{-# LANGUAGE CPP, TypeOperators, DataKinds, PolyKinds, TypeFamilies,
             TemplateHaskell, GADTs, UndecidableInstances, RankNTypes #-}

#if __GLASGOW_HASKELL__ < 707
{-# OPTIONS_GHC -fno-warn-name-shadowing #-}
#endif

-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Singletons.List
-- Copyright   :  (C) 2013 Richard Eisenberg
-- License     :  BSD-style (see LICENSE)
-- Maintainer  :  Richard Eisenberg (eir@cis.upenn.edu)
-- Stability   :  experimental
-- Portability :  non-portable
--
-- Defines functions and datatypes relating to the singleton for '[]',
-- including a singletons version of a few of the definitions in @Data.List@.
--
-- Because many of these definitions are produced by Template Haskell,
-- it is not possible to create proper Haddock documentation. Please look
-- up the corresponding operation in @Data.List@. Also, please excuse
-- the apparent repeated variable names. This is due to an interaction
-- between Template Haskell and Haddock.
--
----------------------------------------------------------------------------

module Data.Singletons.List (
  -- * The singleton for lists
  Sing(SNil, SCons),
  -- | Though Haddock doesn't show it, the 'Sing' instance above declares
  -- constructors
  --
  -- > SNil  :: Sing '[]
  -- > SCons :: Sing (h :: k) -> Sing (t :: [k]) -> Sing (h ': t)

  SList,
  -- | 'SList' is a kind-restricted synonym for 'Sing': @type SList (a :: [k]) = Sing a@

  (:++), (%:++),
  Head, Tail, sHead, sTail,
  Map, sMap,
  Reverse, sReverse,

  -- * Defunctionalization symbols
  (:$), (:$$),
  ConsSym0, ConsSym1, NilSym0,

  (:++$$), (:++$),
  HeadSym0, TailSym0,
  MapSym0, MapSym1,
  ReverseSym0, Reverse_auxSym0, Reverse_auxSym1
  ) where

import Data.Singletons
import Data.Singletons.Instances
import Data.Singletons.Singletons
import Data.Singletons.TypeLits

$(singletonsOnly [d|
  (++) :: [a] -> [a] -> [a]
  [] ++ a = a
  (h:t) ++ a = h:(t ++ a)

  head :: [a] -> a
  head (a : _) = a
  head []      = error "Data.Singletons.List.head: empty list"

  tail :: [a] -> [a]
  tail (_ : t) = t
  tail []      = error "Data.Singletons.List.tail: empty list"

  map :: (a -> b) -> [a] -> [b]
  map _ [] = []
  map f (x:xs) = f x : map f xs

  reverse :: [a] -> [a]
  reverse list = reverse_aux [] list

  reverse_aux :: [a] -> [a] -> [a]
  reverse_aux acc []      = acc
  reverse_aux acc (h : t) = reverse_aux (h : acc) t
  |])

type ConsSym0 = (:$)
type ConsSym1 = (:$$)
type NilSym0  = '[]