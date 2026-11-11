/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Basic
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
The chain map induced by a monomorphism of simplicial sets is also a monomorphism. For two
subcomplexes `S` and `T` of a simplicial set, a chain of `S` whose image is a chain of `T` is a
chain of `S ⊓ T` (`SSet.Subcomplex.exists_comp_chainComplexMap_homOfLE_eq_of_comp_eq`), because in
each degree all three chain objects are coproducts of copies of `R` indexed by simplices.

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

/-- The simplicial chain complex functor `X ↦ X.chainComplex R` preserves colimits of every shape
`J` that the category of `w`-small types has colimits of. -/
instance : PreservesColimitsOfShape J ((SSet.chainComplexFunctor.{w} C).obj R) :=
  HomologicalComplex.preservesColimitsOfShape_of_eval _ fun n ↦
    -- Degree `n` of `X.chainComplex R` is evaluation at `⦋n⦌` followed by `sigmaConst.obj R`,
    -- by definition of `alternatingFaceMapComplex` (`alternatingFaceMapComplex_obj_X` and
    -- `alternatingFaceMapComplex_map_f` are `rfl`); both factors preserve colimits.
    inferInstanceAs (PreservesColimitsOfShape J
      ((evaluation SimplexCategoryᵒᵖ (Type w)).obj (Opposite.op ⦋n⦌) ⋙ sigmaConst.obj R))

end TauCeti

namespace SSet

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Preadditive C]
  {X Y : SSet.{w}} (f : X ⟶ Y) (R : C)

/-- The chain map induced by a monomorphism of simplicial sets is a monomorphism. -/
instance mono_chainComplexMap [Mono f] : Mono (chainComplexMap f R) :=
  HomologicalComplex.mono_of_mono_f _ fun _ ↦
    inferInstanceAs (Mono ((sigmaConst.obj R).map (f.app _)))

namespace Subcomplex

variable {K : SSet.{w}} (S T : K.Subcomplex)

/-- A chain of a subcomplex `S` whose image in the chains of `K` is the image of a chain of a
subcomplex `T` is a chain of `S ⊓ T`. -/
theorem exists_comp_chainComplexMap_homOfLE_eq_of_comp_eq {n : ℕ}
    {g : R ⟶ ((S : SSet).chainComplex R).X n} {h : R ⟶ ((T : SSet).chainComplex R).X n}
    (hgh : g ≫ (chainComplexMap S.ι R).f n = h ≫ (chainComplexMap T.ι R).f n) :
    ∃ g' : R ⟶ ((S ⊓ T).toSSet.chainComplex R).X n,
      g' ≫ (chainComplexMap (homOfLE (inf_le_left : S ⊓ T ≤ S)) R).f n = g := by
  classical
  have : Mono ((chainComplexMap S.ι R).f n) :=
    inferInstanceAs (Mono ((sigmaConst.obj R).map (S.ι.app (Opposite.op ⦋n⦌))))
  -- The projections onto the summands of the simplices of `T`.
  let π : ((S : SSet).chainComplex R).X n ⟶ ((S ⊓ T).toSSet.chainComplex R).X n :=
    Cofan.IsColimit.desc ((S : SSet).isColimitChainComplexXCofan R n) fun σ ↦
      if hσ : σ.1 ∈ T.obj (Opposite.op ⦋n⦌) then
        (S ⊓ T).toSSet.ιChainComplex ⟨σ.1, Set.mem_inter σ.2 hσ⟩
      else 0
  let πK : (K.chainComplex R).X n ⟶ ((T : SSet).chainComplex R).X n :=
    Cofan.IsColimit.desc (K.isColimitChainComplexXCofan R n) fun σ ↦
      if hσ : σ ∈ T.obj (Opposite.op ⦋n⦌) then (T : SSet).ιChainComplex ⟨σ, hσ⟩ else 0
  have hπσ (σ : (S : SSet) _⦋n⦌) : (S : SSet).ιChainComplex σ ≫ π =
      if hσ : σ.1 ∈ T.obj (Opposite.op ⦋n⦌) then
        (S ⊓ T).toSSet.ιChainComplex ⟨σ.1, Set.mem_inter σ.2 hσ⟩
      else 0 :=
    Cofan.IsColimit.fac _ _ σ
  have hπKσ (σ : K _⦋n⦌) : K.ιChainComplex σ ≫ πK =
      if hσ : σ ∈ T.obj (Opposite.op ⦋n⦌) then (T : SSet).ιChainComplex ⟨σ, hσ⟩ else 0 :=
    Cofan.IsColimit.fac _ _ σ
  have hπK : (chainComplexMap T.ι R).f n ≫ πK = 𝟙 _ := by
    ext τ
    rw [← Category.assoc, ι_chainComplexMap_f, hπKσ, Category.comp_id]
    split_ifs with hτ
    · rfl
    · exact (hτ τ.2).elim
  have hπ : π ≫ (chainComplexMap (homOfLE (inf_le_left : S ⊓ T ≤ S)) R).f n ≫
        (chainComplexMap S.ι R).f n =
      (chainComplexMap S.ι R).f n ≫ πK ≫ (chainComplexMap T.ι R).f n := by
    ext σ
    rw [reassoc_of% (hπσ σ), ι_chainComplexMap_f_assoc, reassoc_of% (hπKσ _)]
    split_ifs with h₁ h₂ h₂
    · rw [ι_chainComplexMap_f_assoc, ι_chainComplexMap_f, ι_chainComplexMap_f]
      rfl
    · exact (h₂ h₁).elim
    · exact (h₁ h₂).elim
    · rw [zero_comp, zero_comp]
  refine ⟨g ≫ π, (cancel_mono ((chainComplexMap S.ι R).f n)).1 ?_⟩
  rw [Category.assoc, Category.assoc, hπ, reassoc_of% hgh, reassoc_of% hπK, hgh]

end Subcomplex

end SSet
