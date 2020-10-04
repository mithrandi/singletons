{- Data/Singletons/TH/Single/Type.hs

(c) Richard Eisenberg 2013
rae@cs.brynmawr.edu

Singletonizes types.
-}

module Data.Singletons.TH.Single.Type where

import Language.Haskell.TH.Desugar
import Language.Haskell.TH.Desugar.OSet (OSet)
import Language.Haskell.TH.Syntax
import Data.Singletons.TH.Names
import Data.Singletons.TH.Options
import Data.Singletons.TH.Promote.Type
import Data.Singletons.TH.Single.Monad
import Data.Singletons.TH.Util
import Control.Monad
import Data.Foldable
import Data.Function
import Data.List (deleteFirstsBy)

singType :: OSet Name      -- the set of bound kind variables in this scope
                           -- see Note [Explicitly binding kind variables]
                           -- in Data.Singletons.TH.Promote.Monad
         -> DType          -- the promoted version of the thing classified by...
         -> DType          -- ... this type
         -> SgM ( DType    -- the singletonized type
                , Int      -- the number of arguments
                , [Name]   -- the names of the tyvars used in the sing'd type
                , DCxt     -- the context of the singletonized type
                , [DKind]  -- the kinds of the argument types
                , DKind )  -- the kind of the result type
singType bound_kvs prom ty = do
  (orig_tvbs, cxt, args, res) <- unravelVanillaDType ty
  let num_args = length args
  cxt' <- mapM singPred_NC cxt
  arg_names <- replicateM num_args (qNewName "t")
  prom_args <- mapM promoteType_NC args
  prom_res  <- promoteType_NC res
  let args' = map (\n -> singFamily `DAppT` (DVarT n)) arg_names
      res'  = singFamily `DAppT` (foldl apply prom (map DVarT arg_names) `DSigT` prom_res)
                -- Make sure to include an explicit `prom_res` kind annotation.
                -- See Note [Preserve the order of type variables during singling],
                -- wrinkle 2.
      kvbs     = singTypeKVBs orig_tvbs prom_args cxt' prom_res bound_kvs
      all_tvbs = kvbs ++ zipWith (`DKindedTV` SpecifiedSpec) arg_names prom_args
      ty'      = ravelVanillaDType all_tvbs cxt' args' res'
  return (ty', num_args, arg_names, cxt, prom_args, prom_res)

-- Compute the kind variable binders to use in the singled version of a type
-- signature. This has two main call sites: singType and D.S.TH.Single.Data.singCtor.
--
-- This implements the advice documented in
-- Note [Preserve the order of type variables during singling], wrinkle 1.
singTypeKVBs ::
     [DTyVarBndrSpec] -- ^ The bound type variables from the original type signature.
  -> [DType]          -- ^ The argument types of the signature (promoted).
  -> DCxt             -- ^ The context of the signature (singled).
  -> DType            -- ^ The result type of the signature (promoted).
  -> OSet Name        -- ^ The type variables previously bound in the current scope.
  -> [DTyVarBndrSpec] -- ^ The kind variables for the singled type signature.
singTypeKVBs orig_tvbs prom_args sing_ctxt prom_res bound_tvbs
  | null orig_tvbs
  -- There are no explicitly `forall`ed type variable binders, so we must
  -- infer them ourselves.
  = changeDTVFlags SpecifiedSpec $
    deleteFirstsBy
      ((==) `on` extractTvbName)
      (toposortTyVarsOf $ prom_args ++ sing_ctxt ++ [prom_res])
      (map (`DPlainTV` ()) $ toList bound_tvbs)
      -- Make sure to subtract out the bound variables currently in scope,
      -- lest we accidentally shadow them in this type signature.
      -- See Note [Explicitly binding kind variables] in D.S.TH.Promote.Monad.
  | otherwise
  -- There is an explicit `forall`, so this case is easy.
  = orig_tvbs

-- Single a DPred, checking that it is a vanilla type in the process.
-- See [Vanilla-type validity checking during promotion]
-- in Data.Singletons.TH.Promote.Type.
singPred :: DPred -> SgM DPred
singPred p = do
  checkVanillaDType p
  singPred_NC p

-- Single a DPred. Does not check if the argument is a vanilla type.
-- See [Vanilla-type validity checking during promotion]
-- in Data.Singletons.TH.Promote.Type.
singPred_NC :: DPred -> SgM DPred
singPred_NC = singPredRec []

-- The workhorse for singPred_NC.
singPredRec :: [DTypeArg] -> DPred -> SgM DPred
singPredRec _cxt (DForallT {}) =
  fail "Singling of quantified constraints not yet supported"
singPredRec _cxt (DConstrainedT {}) =
  fail "Singling of quantified constraints not yet supported"
singPredRec ctx (DAppT pr ty) = singPredRec (DTANormal ty : ctx) pr
singPredRec ctx (DAppKindT pr ki) = singPredRec (DTyArg ki : ctx) pr
singPredRec _ctx (DSigT _pr _ki) =
  fail "Singling of constraints with explicit kinds not yet supported"
singPredRec _ctx (DVarT _n) =
  fail "Singling of contraint variables not yet supported"
singPredRec ctx (DConT n)
  | n == equalityName
  = fail "Singling of type equality constraints not yet supported"
  | otherwise = do
    opts <- getOptions
    kis <- mapM promoteTypeArg_NC ctx
    let sName = singledClassName opts n
    return $ applyDType (DConT sName) kis
singPredRec _ctx DWildCardT = return DWildCardT  -- it just might work
singPredRec _ctx DArrowT =
  fail "(->) spotted at head of a constraint"
singPredRec _ctx (DLitT {}) =
  fail "Type-level literal spotted at head of a constraint"

{-
Note [Preserve the order of type variables during singling]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
singletons-th does its best to preseve the order in which users write type
variables in type signatures for functions and data constructors. They are
"preserved" in the sense that if one writes `foo @T1 @T2`, one should be
able to write out `sFoo @T1 @T2` by hand and have the same order of visible
type applications still work. Accomplishing this is surprisingly nontrivial,
so this Note documents the various wrinkles one must iron out to get this
working.

-----
-- Wrinkle 1: Dealing with the presence (and absence) of `forall`
-----

If we single a function that has an explicit `forall`, such as this example:

  const2 :: forall b a. a -> b -> a
  const2 x _ = x

Then our job is easy, as the exact order of type variables has already been
spelled out in advance. We single this to:

  sConst2 :: forall b a (x :: a) (y :: b). Sing x -> Sing y -> Sing (Const2 x y :: a)
  sConst2 = ...

What happens if there is no explicit `forall`, as in this example?

  data V a

  absurd :: V a -> b
  absurd v = case v of {}

This time, the order of type variables vis-à-vis TypeApplications is determined
by their left-to-right order of appearance in the type signature. It's tempting
to think that since there is no explicit `forall` in the original type
signature, we could get away without an explicit `forall` in the singled type
signature. That is, one could write:

  sAbsurd :: Sing (v :: V a) -> Sing (Absurd :: b)

This would have the right type variable order, but unfortunately, this approach
does not play well with singletons-th's style of code generation. Consider the code
that would be generated for the body of sAbsurd:

  sAbsurd :: Sing (v :: V a) -> Sing (Absurd :: b)
  sAbsurd (sV :: Sing v) = id @(Case v v :: b) (case sV of {})

Note the use of the type `Case v v :: b` in the right-hand side of sAbsurd.
However, because `b` was not bound by a top-level `forall`, it won't be in
scope here, resulting in an error!

(Why do we generate the code `id @(Case v v :: b)` in the first place? See
Note [The id hack; or, how singletons-th learned to stop worrying and avoid kind generalization]
in D.S.TH.Single.)

The simplest approach is to just always generate singled type signatures with
explicit `forall`s. In the event that the original type signature lacks an
explicit `forall`, we infer the correct type variable ordering ourselves and
synthesize a `forall` with that order. The `singTypeKVBs` function implements
this logic.

-----
-- Wrinkle 2: Where to put explicit kind annotations
-----

Type variable binders are only part of the story—we must also determine what
the body of the type signature will be singled to. As a general rule, if the
original type signature is of the form:

  f :: forall a_1 ... a_m. (C_1, ..., C_n)
    => T_1 -> ... -> T_p -> R

Then the singled type signature will be:

  sF :: forall a_1 ... a_m (x_1 :: PT_1) ... (x_p :: PT_p). (SC_1, ..., SC_n)
     => Sing x1 -> ... -> Sing x_p -> Sing (F x1 ... x_p :: PR)

Where:

* F is the promoted version of the function f, PT_i is the promoted version of
  the type T_i, and PR is the promoted version of the type R.
* x_i is a fresh type variable of kind PT_i.
* SC_i is the singled version of the constraint SC_i.

The `singType` function is responsible for this.

Note that we need only write `Sing x_1 -> ... -> Sing x_p`, and not
`Sing (x_1 :: PT_1) -> ... Sing (x_p :: PT_p)`. This is simply because we
always use explicit `forall`s in singled type signatures, and therefore always
explicitly bind `(x_1 :: PT_1) ... (x_p :: PT_p)`, which fully determine the
kinds of `x_1 ... x_p`. It wouldn't be wrong to add extra kind annotations to
`Sing x_1 -> ... -> Sing x_p`, just redundant.

On the other hand, the explicit `:: PR` kind annotation in the result type
`Sing (F x1 ... x_p :: PR)` is mandatory. Omitting this annotation can result
in singled type signatures with the wrong semantics. For instance, consider
this function:

  nuthin :: forall a. Maybe a
  nuthin = Nothing

Consider what would happen if nuthin were singled like this:

  sNuthin :: forall a. Sing Nuthin

This is not what we want at all, since the `a` has no connection to the
Nuthin in the result type. It's as if we had written this:

  sNuthin :: forall {t} a. Sing (Nuthin :: Maybe t)

If we instead generate `forall a. Sing (Nuthin :: Maybe a)`, then this issue
is handily avoided.

A similar template is used for data constructors. If a data constructor is of
the form:

  MkD :: forall a_1 ... a_m. (C_1, ..., C_n)
      => T_1 -> ... -> T_p -> D

Then the singled data constructor type will be:

  SMkD :: forall a_1 ... a_m (x_1 :: PT_1) ... (x_p :: PT_p). (SC_1, ..., SC_n)
       => Sing x1 -> ... -> Sing x_p -> SD (MkD @a_1 ... @a_m x1 ... x_p)

There are two differences in the way this is singled when compared to function
type signatures, and both of these differences pertain to the result type:

1. Rather than using Sing in the result type, the singled version of the data
   type name is used instead. This is important, as GADT constructors do not
   permit return types that are headed by a type family.
2. Rather than using an explicit `:: PR` kind annotation in the result type,
   visible kind application is used instead. This accomplishes the same end
   result as using an explicit kind annotation—namely, disambiguating all of
   the type variables involved—but in a cleaner fashion.

The `D.S.TH.Single.Data.singCtor` function is responsible for this.

Why do we do things differently for data constructor types than we do for
other types? That is, why do we not use the `singCtor` template in `singType`
as well? There are two reasons why this template would be ill suited for
`singType`:

1. Data constructor type signatures always have a result type that is headed
   by a data constructor (e.g., D), so it is always possible to come up with
   a singled counterpart to the data constructor name (e.g., SD) instead of
   using `Sing` in the singled return type. This is not always the case for
   functions in general. For example, consider `id :: a -> a`, whose return
   type is simply a type variable. Here, we have no choice but to use `Sing` in
   the singled return type.
2. A data constructor and its promoted counterpart will always quantify their
   type variables in the exact same order, so using visible kind application
   in the way described above will always succeed. This property does not hold
   for functions in general, however. As explained in
   Note [Promoted class methods and kind variable ordering] in D.S.TH.Promote,
   if you promote the following class:

    class C (b :: Type) where
      m :: forall a. a -> b -> a

   You will get the following:

    class PC (b :: Type) where
      type M (x :: a) (y :: b) :: a

   The order of type variables in the types of `m` and `M` is different:
   `m` quantifies `b` first, while `M` quantifies `a` first. As a result, a
   naïve attempt at singling `m` like this would fail:

     class SC (b :: Type) where
       sM :: forall a (x_1 :: a) (x_2 :: b).
             Sing x_1 -> Sing x_2 -> Sing (M @b @a x_1 x2)

   As a result, we don't bother with visible kind application in `singType`.
   One could imagine carving out a special case in `singType` for promoted
   class methods, but when I tried doing this, I found that the amount of
   effort it required didn't justify the result.
-}
