{- -*- mode: haskell; coding: utf-8-unix -*-  -}
{-# LANGUAGE BangPatterns, DeriveDataTypeable, FlexibleContexts,
    ScopedTypeVariables, TypeFamilies #-}
-- |
-- Module    : System.Random.MT64
-- Copyright : (c) 2020 Naoyuki MORITA
-- Licence   : MIT
--
-- Maintainer  : naoyuki.morita@gmail.com
-- Stability   : experimental
-- Portability : portable
--
module System.Random.MT64
    (
    -- * Gen: Pseudo-Random Number Generators
      Gen
    , initGenRand64
    , initByArray64

    -- ** Type helpers
    , GenIO
    , GenST

    , asGenIO
    , asGenST

    -- * Variates: uniformly distributed values
    , Variate(..)

    -- * State management
    , save
    , restore
    ) where

import Control.Monad           (liftM, when)
import Control.Monad.Primitive (PrimMonad, PrimState)
import Control.Monad.ST        (ST)
import Data.Bits               ((.&.), (.|.), shiftL, shiftR, xor)
import Data.Int                (Int8, Int16, Int32, Int64)
import Data.Vector.Generic     (Vector)
import Data.Word
import qualified Data.Vector.Generic         as G
import qualified Data.Vector.Unboxed         as I
import qualified Data.Vector.Unboxed.Mutable as M

-- | The class of types for which we can generate uniformly
-- distributed random variates.
class Variate a where
    -- | Generate a single uniformly distributed random variate.  The
    -- range of values produced varies by type:
    uniform :: (PrimMonad m) => Gen (PrimState m) -> m a

instance Variate Int8 where
    uniform = uniform1 fromIntegral
    {-# INLINE uniform #-}

instance Variate Int16 where
    uniform = uniform1 fromIntegral
    {-# INLINE uniform #-}

instance Variate Int32 where
    uniform = uniform1 fromIntegral
    {-# INLINE uniform #-}

instance Variate Int64 where
    uniform = uniform1 fromIntegral
    {-# INLINE uniform #-}

instance Variate Word8 where
    uniform = uniform1 fromIntegral
    {-# INLINE uniform #-}

instance Variate Word16 where
    uniform = uniform1 fromIntegral
    {-# INLINE uniform #-}

instance Variate Word32 where
    uniform = uniform1 fromIntegral
    {-# INLINE uniform #-}

instance Variate Word64 where
    uniform = uniform1 id
    {-# INLINE uniform #-}

instance Variate Bool where
    uniform = uniform1 wordToBool
    {-# INLINE uniform #-}

instance Variate Float where
    uniform = uniform1 wordToFloat
    {-# INLINE uniform #-}

instance Variate Double where
    uniform = uniformDouble
    {-# INLINE uniform #-}

wordToBool :: Word64 -> Bool
wordToBool w = w < 0x8000000000000000
{-# INLINE wordToBool #-}

wordToFloat :: Word64 -> Float
wordToFloat x = fromIntegral y * (1.0/16777216.0)
  where y = x `shiftR` 40
{-# INLINE wordToFloat #-}

newtype Gen s = Gen (M.MVector s Word64)

type GenIO = Gen (PrimState IO)

type GenST s = Gen (PrimState (ST s))

asGenIO :: (GenIO -> IO a) -> (GenIO -> IO a)
asGenIO = id

asGenST :: (GenST s -> ST s a) -> (GenST s -> ST s a)
asGenST = id

nn :: Int
nn = 312
{-# INLINE nn #-}

mm :: Int
mm = 156
{-# INLINE mm #-}

mti_idx :: Int
mti_idx = nn
{-# INLINE mti_idx #-}

matrix_a :: Word64
matrix_a = 0xB5026F5AA96619E9
{-# INLINE matrix_a #-}

um :: Word64
um = 0xFFFFFFFF80000000
{-# INLINE um #-}

lm :: Word64
lm = 0x000000007FFFFFFF
{-# INLINE lm #-}

initGenRand64 :: (PrimMonad m) => Word64 -> m (Gen (PrimState m))
initGenRand64 seed = do
    q <- M.unsafeNew (nn+1)
    M.unsafeWrite q 0 seed
    fill q seed 1
    return (Gen q)
      where fill q pre_mt idx =
              if idx < nn then do
                let mt = 6364136223846793005 * (pre_mt `xor` (pre_mt `shiftR` 62)) + fromIntegral idx
                M.unsafeWrite q idx mt
                fill q mt (idx+1)
              else
                M.unsafeWrite q mti_idx (fromIntegral idx)

initByArray64 :: (PrimMonad m, Vector v Word64) => v Word64 -> m (Gen (PrimState m))
initByArray64 seed = do
    Gen q <- initGenRand64 19650218
    mt0 <- M.unsafeRead q 0
    let k = if nn > l then nn else l
    i <- fill0 q mt0 1 0 k
    mt1 <- M.unsafeRead q (i-1)
    fill1 q mt1 i (nn-1)
    M.unsafeWrite q 0 0x8000000000000000
    return (Gen q)
      where l = G.length seed
            -- first loop
            fill0 _ _      i _ 0 = return i
            fill0 q pre_mt i j k = do
              mt <- M.unsafeRead q i
              let ik = G.unsafeIndex seed j
              let mt' = (mt `xor` ((pre_mt `xor` (pre_mt `shiftR` 62)) * 3935559000370003845)) + ik + fromIntegral j
              M.unsafeWrite q i mt'
              let i' = i+1
              let j' = j+1
              let i'' = if i' >= nn then 1 else i'
              let j'' = if j' >= l  then 0 else j'
              when (i' >= nn) (M.unsafeRead q (nn-1) >>= M.unsafeWrite q 0)
              fill0 q mt' i'' j'' (k-1)
            -- second loop
            fill1 _ _      _ 0 = return ()
            fill1 q pre_mt i k = do
              mt <- M.unsafeRead q i
              let mt' = (mt `xor` ((pre_mt `xor` (pre_mt `shiftR` 62)) * 2862933555777941757)) - fromIntegral i
              M.unsafeWrite q i mt'
              let i' = i+1
              let i'' = if i' >= nn then 1 else i'
              when (i' >= nn) (M.unsafeRead q (nn-1) >>= M.unsafeWrite q 0)
              fill1 q mt' i'' (k-1)


save :: (PrimMonad m) => Gen (PrimState m) -> m (I.Vector Word64)
save (Gen q) = G.freeze q

checkMti :: (PrimMonad m) => M.MVector (PrimState m) Word64 -> m Bool
checkMti q = do mti <- M.unsafeRead q mti_idx
                if mti <= (fromIntegral nn)
                  then return True
                  else return False

restore :: (PrimMonad m) => (I.Vector Word64) -> m (Gen (PrimState m))
restore v
  | G.length v /= (nn+1) = error "Invalid state vector."
  | otherwise            =
    do q <- G.thaw v
       t <- checkMti q
       if t
         then return (Gen q)
         else error "Invalid state vector."


twist :: (PrimMonad m) => M.MVector (PrimState m) Word64 -> Int -> Int -> Int -> m ()
twist q i0 i1 i2 = do
    mt0 <- M.unsafeRead q i0
    mt1 <- M.unsafeRead q i1
    mt2 <- M.unsafeRead q i2
    let x = (mt0 .&. um) .|. (mt1 .&. lm)
    let mag = (x .&. 1) * matrix_a
    let mt' = mt2 `xor` (x `shiftR` 1) `xor` mag
    M.unsafeWrite q i0 mt'
{-# INLINE twist #-}

mixWord64 :: Word64 -> Word64
mixWord64 x0 = x4
  where x1 = x0 `xor` ((x0 `shiftR` 29) .&. 0x5555555555555555)
        x2 = x1 `xor` ((x1 `shiftL` 17) .&. 0x71D67FFFEDA60000)
        x3 = x2 `xor` ((x2 `shiftL` 37) .&. 0xFFF7EEE000000000)
        x4 = x3 `xor`  (x3 `shiftR` 43)
{-# INLINE mixWord64 #-}

uniformWord64 :: (PrimMonad m) => Gen (PrimState m) -> m Word64
uniformWord64 (Gen q) = do
    mti <- fromIntegral `liftM` M.unsafeRead q mti_idx
    when (mti >= nn) $ do
         fill0 0
         fill1 (nn-mm)
         twist q (nn-1) 0 (mm-1)
    let mti' = if (mti >= nn) then 0 else mti
    x <- mixWord64 `liftM` M.unsafeRead q mti'
    M.unsafeWrite q mti_idx (fromIntegral (mti'+1))
    return x
      where fill0 i
              | i >= nn-mm = return ()
              | otherwise  = do
                  twist q i (i+1) (i+mm)
                  fill0 (i+1)
            fill1 i
              | i >= nn-1  = return ()
              | otherwise  = do
                  twist q i (i+1) (i+(mm-nn))
                  fill1 (i+1)
{-# INLINE uniformWord64 #-}

uniform1 :: (PrimMonad m) => (Word64 -> a) -> Gen (PrimState m) -> m a
uniform1 f gen = do
    i <- uniformWord64 gen
    return $! f i
{-# INLINE uniform1 #-}

uniformDouble :: (PrimMonad m) => Gen (PrimState m) -> m Double
uniformDouble gen = do
    w <- uniformWord64 gen
    let w' = w `shiftR` 11
    let v  = fromIntegral w' * (1.0/9007199254740992.0)
    return v
{-# INLINE uniformDouble #-}

-- EOF
