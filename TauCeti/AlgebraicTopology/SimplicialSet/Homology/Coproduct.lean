/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Basic
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
public import Mathlib.CategoryTheory.Limits.MonoCoprod
public import Mathlib.CategoryTheory.Limits.Preserves.SigmaConst

/-!
# The simplicial chain complex preserves colimits

In degree `n` the chain complex of a simplicial set `X` with coefficients in an object `R` is the
coproduct of copies of `R` indexed by the `n`-simplices of `X`.  Evaluating a simplicial set in a
fixed degree preserves colimits, because colimits of presheaves are computed pointwise, and
forming a coproduct of copies of `R` preserves colimits; hence so does `X ↦ X.chainComplex R`.

The case of a coproduct is chain-level additivity: the chain complex of a disjoint union of
simplicial sets is the coproduct of the chain complexes of the summands.
The chain map induced by a monomorphism of simplicial sets is also a monomorphism.

## Sources

The argument assembles three Mathlib constructions.  The simplicial chain complex
`SSet.chainComplexFunctor` and its degreewise cofan `SSet.isColimitChainComplexXCofan`
are due to Joël Riou and Andrew Yang in `Mathlib/AlgebraicTopology/SimplicialSet/Homology/Basic`;
the coproduct-of-copies functor `CategoryTheory.Limits.sigmaConst` and its colimit preservation
are due to Joël Riou in `Mathlib/CategoryTheory/Limits/Preserves/SigmaConst`, as is the reduction
of colimit preservation to the degreewise statement,
`HomologicalComplex.preservesColimitsOfShape_of_eval`.
-/

public section

noncomputable section

open CategoryTheory Limits

open scoped Simplicial

universe w v u v' u'

namespace TauCeti

variable (C : Type u) [Category.{v} C] [HasCoproducts.{w} C] [Preadditive C] (R : C)

variable {J : Type u'} [Category.{v'} J] [HasColimitsOfShape J (Type w)]

/-- The simplicial chain complex with coefficients in `R` preserves every shape of colimit that
the category of `w`-small types has: in each degree it is the composite of evaluation, which
preserves colimits of presheaves, with `sigmaConst.obj R`. -/
instance : PreservesColimitsOfShape J ((SSet.chainComplexFunctor.{w} C).obj R) :=
  HomologicalComplex.preservesColimitsOfShape_of_eval _ fun n ↦ by
    have : PreservesColimitsOfShape J
        ((evaluation SimplexCategoryᵒᵖ (Type w)).obj (Opposite.op ⦋n⦌) ⋙ sigmaConst.obj R) :=
      comp_preservesColimitsOfShape _ _
    -- The two functors named below are the same functor.  `SSet.chainComplexFunctor C` is
    -- `X ↦ X ⋙ sigmaConst.obj R` postcomposed with `alternatingFaceMapComplex`, and degree `n`
    -- of an alternating face map complex is evaluation at `⦋n⦌`, on morphisms as well as on
    -- objects; Mathlib records both halves of that as `rfl`, in `alternatingFaceMapComplex_obj_X`
    -- and `alternatingFaceMapComplex_map_f`.  The comparison therefore has no content beyond the
    -- identity, and no interface lemma can stand in for `Iso.refl` here; the `show` spells out
    -- which two functors are being identified.
    exact preservesColimitsOfShape_of_natIso
      (show (evaluation SimplexCategoryᵒᵖ (Type w)).obj (Opposite.op ⦋n⦌) ⋙ sigmaConst.obj R ≅
        (SSet.chainComplexFunctor.{w} C).obj R ⋙ HomologicalComplex.eval C _ n from Iso.refl _)

end TauCeti

namespace SSet

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Preadditive C]
  {X Y : SSet.{w}} (f : X ⟶ Y) (R : C)

/-- The chain map induced by a monomorphism of simplicial sets is a monomorphism. -/
instance mono_chainComplexMap [Mono f] : Mono (chainComplexMap f R) :=
  HomologicalComplex.mono_of_mono_f _ fun _ ↦
    inferInstanceAs (Mono ((sigmaConst.obj R).map (f.app _)))

end SSet
