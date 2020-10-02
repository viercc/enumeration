{-# LANGUAGE DeriveFunctor       #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}

-- SPDX-License-Identifier: BSD-3-Clause

-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Enumeration.Invertible
-- Copyright   :  Brent Yorgey
-- Maintainer  :  byorgey@gmail.com
--
-- An /invertible enumeration/ is a bijection between a set of values
-- and the natural numbers (or a finite prefix thereof), represented
-- as a pair of inverse functions, one in each direction.  Hence they
-- support efficient indexing and can be constructed for very large
-- finite sets.  A few examples are shown below.
--
-- Compared to "Data.Enumeration", one can also build invertible
-- enumerations of functions (or other type formers with contravariant
-- arguments); however, invertible enumerations no longer make for
-- valid 'Functor', 'Applicative', or 'Alternative' instances.
--
-- This module exports many of the same names as "Data.Enumeration";
-- the expectation is that you will choose one or the other to import,
-- though of course it is possible to import both if you qualify the
-- imports.
--
-----------------------------------------------------------------------------

module Data.Enumeration.Invertible
  ( -- * Invertible enumerations

    IEnumeration,
    baseEnum, baseCoEnum
  , card, select, locate
  , isFinite
  , enumerate
  
    -- ** Using enumerations

  , Cardinality(..), Index

    -- ** Primitive invertible enumerations
  
  , void
  , unit
  , singleton
  , finite
  , finiteList
  , boundedEnum

  , nat
  , int
  , cw
  , rat

  -- ** Enumeration combinators

  , mapE
  , takeP, dropP
  , zipE
  , infinite
  , (<+>)
  , (><)
  , interleave

  , maybeOf
  , eitherOf
  , listOf
  , finiteSubsetOf
  , finiteEnumerationOf
  , functionOf
  ) where

import           Control.Applicative (Alternative (..))
import           Data.Bits           (shiftL, (.|.))
import           Data.List           (foldl')
import           Data.Maybe          (fromJust)

import           Data.Enumeration    (Cardinality (..), Enumeration, Index)
import qualified Data.Enumeration    as E
import           Data.CoEnumeration    (CoEnumeration)
import qualified Data.CoEnumeration    as C
import           Data.ProEnumeration
import           Data.Void (Void)
import           Data.Functor.Contravariant

------------------------------------------------------------
-- Setup for doctest examples
------------------------------------------------------------

-- $setup
-- >>> :set -XTypeApplications
-- >>> import Control.Arrow ((&&&))
-- >>> :{
--   data Tree = L | B Tree Tree deriving Show
--   treesUpTo :: Int -> IEnumeration Tree
--   treesUpTo 0 = singleton L
--   treesUpTo n = mapE toTree fromTree (unit <+> (t' >< t'))
--     where
--       t' = treesUpTo (n-1)
--   trees :: IEnumeration Tree
--   trees = infinite $ mapE toTree fromTree (unit <+> (trees >< trees))
--   toTree :: Either () (Tree, Tree) -> Tree
--   toTree = either (const L) (uncurry B)
--   fromTree :: Tree -> Either () (Tree, Tree)
--   fromTree L = Left ()
--   fromTree (B l r) = Right (l,r)
-- :}

------------------------------------------------------------
-- Invertible enumerations
------------------------------------------------------------

-- | An invertible enumeration is a bijection between a set of
--   enumerated values and the natural numbers, or a finite prefix of
--   the natural numbers.  An invertible enumeration is represented as
--   a function from natural numbers to values, paired with an inverse
--   function that returns the natural number index of a given value.
--   Enumerations can thus easily be constructed for very large sets,
--   and support efficient indexing and random sampling.
--   
--   Note that 'IEnumeration' cannot be made an instance of 'Functor',
--   'Applicative', or 'Alternative'.  However, it does support the
--   'functionOf' combinator which cannot be supported by
--   "Data.Enumeration".

type IEnumeration a = ProEnumeration a a

-- | Map a pair of inverse functions over an invertible enumeration of
--   @a@ values to turn it into an invertible enumeration of @b@
--   values.  Because invertible enumerations contain a /bijection/ to
--   the natural numbers, we really do need both directions of a
--   bijection between @a@ and @b@ in order to map.  This is why
--   'IEnumeration' cannot be an instance of 'Functor'.
{-# DEPRECATED mapE "use dimap instead" #-}
mapE :: (a -> b) -> (b -> a) -> IEnumeration a -> IEnumeration b
mapE f g = dimap g f

------------------------------------------------------------
-- Constructing Enumerations
------------------------------------------------------------

-- | The empty enumeration, with cardinality zero and no elements.
--
-- >>> card void
-- Finite 0
--
-- >>> enumerate void
-- []
void :: IEnumeration Void
void = Data.ProEnumeration.empty

{-# DEPRECATED finite "use Data.ProEnumeration.modulo instead" #-}
-- | A finite prefix of the natural numbers.
--
--   'locate' on out-of-bounds values are
--   forcibly made
--   to be in bounds by taking modulo @n@.
--
-- >>> card (finite 5)
-- Finite 5
-- >>> card (finite 1234567890987654321)
-- Finite 1234567890987654321
--
-- >>> enumerate (finite 5)
-- [0,1,2,3,4]
-- 
-- >>> enumerate (finite 0)
-- []
--
-- >>> locate (finite 5) 2
-- 2
finite :: Integer -> IEnumeration Integer
finite = modulo


-- | Construct an enumeration from the elements of a /finite/ list.
--   The elements of the list must all be distinct.
--   
--   The type of 'finiteList' is quite changed from Data.Enumeration.'E.fromList'.
--   It constructs enumeration and its inverse of @Maybe a@ elements,
--   instead of just @a@,
--   to include the failure case @Nothing@.
--
-- >>> enumerate (finiteList [2,3,8,1])   -- Nothing is enumerated first
-- [Nothing,Just 2,Just 3,Just 8,Just 1]
-- >>> select (finiteList [2,3,8,1]) 3
-- Just 8
-- >>> locate (finiteList [2,3,8,1]) (Just 8)
-- 3
finiteList :: Eq a => [a] -> IEnumeration (Maybe a)
finiteList as = mkProEnumeration findIndexIn' (E.maybeOf (E.finiteList as))
  where
    findIndexIn' = contramap (maybe (Left ()) Right) $
      C.overlayC C.unit (C.findIndexIn as)

-- | Fairly interleave a set of /infinite/ enumerations.
--
--   For a finite set of infinite enumerations, a round-robin
--   interleaving is used. That is, if we think of an enumeration of
--   enumerations as a 2D matrix read off row-by-row, this corresponds
--   to taking the transpose of a matrix with finitely many infinite
--   rows, turning it into one with infinitely many finite rows.  For
--   an infinite set of infinite enumerations, /i.e./ an infinite 2D
--   matrix, the resulting enumeration reads off the matrix by
--   'Data.Enumeration.diagonal's.
--
--   Note that the type of this function is slightly different than
--   its counterpart in "Data.Enumeration": each enumerated value in
--   the output is tagged with an index indicating which input
--   enumeration it came from.  This is required to make the result
--   invertible, and is analogous to the way the output values of
--   '<+>' are tagged with 'Left' or 'Right'; in fact, 'interleave'
--   can be thought of as an iterated version of '<+>', but with a
--   more efficient implementation.

interleave :: IEnumeration (IEnumeration a) -> IEnumeration (Index, a)
interleave e = unsafeMkProEnumeration Infinite sel loc
  where
    sel k =
      let (i,j) = case card e of
            Finite n -> k `divMod` n
            Infinite -> E.diagonal k
      in  (j, select (select e j) i)
    loc (j,a) =
      let i = locate (select e j) a
      in  case card e of
            Finite n -> i*n + j
            Infinite -> C.undiagonal (i,j)


-- | Zip two enumerations in parallel, producing the pair of
--   elements at each index.  The resulting enumeration is truncated
--   to the cardinality of the smaller of the two arguments.
--
--   Note that defining @zipWithE@ as in "Data.Enumeration" is not
--   possible since there would be no way to invert it in general.
--   However, one can use 'zipE' in combination with 'mapE' to achieve
--   a similar result.
--
-- >>> enumerate $ zipE nat (boundedEnum @Bool)
-- [(0,False),(1,True)]
--
-- >>> cs = zipE (mapE fromInteger toInteger $ clamped 1 10) (dropP 35 (boundedEnum @Char))
-- >>> cs' = mapE (uncurry replicate) (length &&& head) cs
-- >>> enumerate cs'
-- ["#","$$","%%%","&&&&","'''''","((((((",")))))))","********","+++++++++",",,,,,,,,,,"]
-- >>> locate cs' "********"
-- 7

zipE :: IEnumeration a -> IEnumeration b -> IEnumeration (a,b)
zipE ea eb = mkProEnumeration pre (E.zipE (baseEnum ea) (baseEnum eb))
  where
    pre | card ea <= card eb = contramap fst (baseCoEnum ea)
        | otherwise          = contramap snd (baseCoEnum eb)

-- | @finiteEnumerationOf n a@ creates an enumeration of all sequences
--   of exactly n items taken from the enumeration @a@.
--
-- >>> map E.enumerate . enumerate $ finiteEnumerationOf 2 (finite 3)
-- [[0,0],[0,1],[0,2],[1,0],[1,1],[1,2],[2,0],[2,1],[2,2]]
-- >>> map E.enumerate . take 10 . enumerate $ finiteEnumerationOf 3 nat
-- [[0,0,0],[0,0,1],[1,0,0],[0,1,0],[1,0,1],[2,0,0],[0,0,2],[1,1,0],[2,0,1],[3,0,0]]
finiteEnumerationOf :: Int -> IEnumeration a -> IEnumeration (Enumeration a)
finiteEnumerationOf k as = dimap fromE toE $ finiteFunctionOf k' as
  where k' = toInteger k
        fromE = E.select
        toE = E.mkEnumeration (Finite k')

------------------------------------------------------------
-- Building standard data types
------------------------------------------------------------

-- | @functionOf a b@ creates an enumeration of all functions taking
--   values from the enumeration @a@ and returning values from the
--   enumeration @b@.  As a precondition, @a@ must be finite;
--   otherwise @functionOf@ throws an error. There are two exceptions:
--   first, if @b@ has cardinality 1, we get an enumeration of exactly
--   one function which constantly returns the one element of @b@,
--   even if @a@ is infinite.  Second, if @b@ has cardinality 0, we
--   get a singleton enumeration if @a@ also has cardinality 0, and an
--   empty enumeration otherwise (even if @a@ is infinite).
--
-- >>> bbs = functionOf (boundedEnum @Bool) (boundedEnum @Bool)
-- >>> card bbs
-- Finite 4
-- >>> map (select bbs 2) [False, True]
-- [True,False]
-- >>> locate bbs not
-- 2
--
-- >>> locate (functionOf bbs (boundedEnum @Bool)) (\f -> f True)
-- 5
--
-- >>> n2u = functionOf nat unit
-- >>> card n2u
-- Finite 1
-- >>> (select n2u 0) 57
-- ()
-- >>> n2o = functionOf nat void
-- >>> card n2o
-- Finite 0
-- >>> o2o = functionOf void void
-- >>> card o2o
-- Finite 1
functionOf :: IEnumeration a -> IEnumeration b -> IEnumeration (a -> b)
functionOf as bs = dimap id run $ proenumerationOf as bs
