-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Singletons.Prelude
-- Copyright   :  (C) 2013 Richard Eisenberg
-- License     :  BSD-style (see LICENSE)
-- Maintainer  :  Richard Eisenberg (eir@cis.upenn.edu)
-- Stability   :  experimental
-- Portability :  non-portable
--
-- Mimics the Haskell Prelude, but with singleton types. Includes the basic
-- singleton definitions. Note: This is currently very incomplete!
--
-- Because many of these definitions are produced by Template Haskell, it is
-- not possible to create proper Haddock documentation. Also, please excuse
-- the apparent repeated variable names. This is due to an interaction between
-- Template Haskell and Haddock.
--
----------------------------------------------------------------------------

{-# LANGUAGE CPP #-}
module Data.Singletons.Prelude (
  -- * Basic singleton definitions
  module Data.Singletons,

  Sing(SFalse, STrue, SNil, SCons, SJust, SNothing, SLeft, SRight, SLT, SEQ, SGT,
       STuple0, STuple2, STuple3, STuple4, STuple5, STuple6, STuple7),
  -- | Though Haddock doesn't show it, the 'Sing' instance above includes
  -- the following instances
  --
  -- > data instance Sing (a :: Bool) where
  -- >   SFalse :: Sing False
  -- >   STrue  :: Sing True
  -- >
  -- > data instance Sing (a :: [k]) where
  -- >   SNil  :: Sing '[]
  -- >   SCons :: Sing (h :: k) -> Sing (t :: [k]) -> Sing (h ': t)
  -- >
  -- > data instance Sing (a :: Maybe k) where
  -- >   SNothing :: Sing Nothing
  -- >   SJust    :: Sing (a :: k) -> Sing (Just a)
  -- >
  -- > data instance Sing (a :: Either x y) where
  -- >   SLeft  :: Sing (a :: x) -> Sing (Left a)
  -- >   SRight :: Sing (b :: y) -> Sing (Right b)
  -- >
  -- > data instance Sing (a :: Ordering) where
  -- >   SLT :: Sing LT
  -- >   SEQ :: Sing EQ
  -- >   SGT :: Sing GT
  -- >
  -- > data instance Sing (a :: ()) where
  -- >   STuple0 :: Sing '()
  -- >
  -- > data instance Sing (z :: (a, b)) where
  -- >   STuple2 :: Sing a -> Sing b -> Sing '(a, b)
  -- >
  -- > data instance Sing (z :: (a, b, c)) where
  -- >   STuple3 :: Sing a -> Sing b -> Sing c -> Sing '(a, b, c)
  -- >
  -- > data instance Sing (z :: (a, b, c, d)) where
  -- >   STuple4 :: Sing a -> Sing b -> Sing c -> Sing d -> Sing '(a, b, c, d)
  -- >
  -- > data instance Sing (z :: (a, b, c, d, e)) where
  -- >   STuple5 :: Sing a -> Sing b -> Sing c -> Sing d -> Sing e -> Sing '(a, b, c, d, e)
  -- >
  -- > data instance Sing (z :: (a, b, c, d, e, f)) where
  -- >   STuple6 :: Sing a -> Sing b -> Sing c -> Sing d -> Sing e -> Sing f
  -- >           -> Sing '(a, b, c, d, e, f)
  -- >
  -- > data instance Sing (z :: (a, b, c, d, e, f, g)) where
  -- >   STuple7 :: Sing a -> Sing b -> Sing c -> Sing d -> Sing e -> Sing f
  -- >           -> Sing g -> Sing '(a, b, c, d, e, f, g)

  -- * Singleton type synonyms

  -- | These synonyms are all kind-restricted synonyms of 'Sing'.
  -- For example 'SBool' requires an argument of kind 'Bool'.
  SBool, SList, SMaybe, SEither, SOrdering,
  STuple0, STuple2, STuple3, STuple4, STuple5, STuple6, STuple7,

  -- * Functions working with 'Bool'
  If, sIf, Not, sNot, (:&&), (:||), (%:&&), (%:||), Otherwise, sOtherwise,

  -- * Functions working with lists
  Head, sHead, Tail, sTail, (:++), (%:++), Reverse, sReverse, Map, sMap,

  -- * Error reporting
  Error, ErrorSym0, sError,

  -- * Singleton equality
  module Data.Singletons.Eq,

  -- * Other datatypes
  Maybe_, sMaybe_,
  Either_, sEither_,
  Fst, sFst, Snd, sSnd, Curry, sCurry, Uncurry, sUncurry,

  -- * Other functions
  either_, -- reimplementation of either to be used with singletons library

  -- * Defunctionalization symbols
  TrueSym0, FalseSym0,
  (:$), (:$$),
  ConsSym0, ConsSym1, NilSym0,
  NothingSym0, JustSym0,
  LeftSym0, RightSym0,
  Tuple0Sym0,
  Tuple2Sym0, Tuple2Sym1,
  Tuple3Sym0, Tuple3Sym1, Tuple3Sym2,
  Tuple4Sym0, Tuple4Sym1, Tuple4Sym2, Tuple4Sym3,
  Tuple5Sym0, Tuple5Sym1, Tuple5Sym2, Tuple5Sym3, Tuple5Sym4,
  Tuple6Sym0, Tuple6Sym1, Tuple6Sym2, Tuple6Sym3, Tuple6Sym4, Tuple6Sym5,
  Tuple7Sym0, Tuple7Sym1, Tuple7Sym2, Tuple7Sym3, Tuple7Sym4, Tuple7Sym5, Tuple7Sym6,

  NotSym0, (:&&$), (:&&$$), (:||$), (:||$$), OtherwiseSym0,

  HeadSym0, TailSym0, (:++$), (:++$$), ReverseSym0, MapSym0, MapSym1,

  Maybe_Sym0, Maybe_Sym1, Maybe_Sym2,
  Either_Sym0, Either_Sym1, Either_Sym2,
  FstSym0, SndSym0, CurrySym0, CurrySym1, CurrySym2, UncurrySym0, UncurrySym1
  ) where

import Data.Singletons
import Data.Singletons.Bool
import Data.Singletons.List
import Data.Singletons.Maybe
import Data.Singletons.Either
import Data.Singletons.Tuple
import Data.Singletons.Eq
import Data.Singletons.Instances
import Data.Singletons.TypeLits