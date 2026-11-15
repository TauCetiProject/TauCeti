/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.InnerProductSpace.StarOrder
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms
public import Mathlib.CategoryTheory.ObjectProperty.ClosedUnderIsomorphisms
public import TauCeti.Analysis.InnerProductSpace.Category
public import TauCeti.CategoryTheory.CStar.Functor

/-!
# Complex Hilbert spaces as a C⋆-category

`TauCeti.HilbertCat.{0, v} ℂ` is a C⋆-category under the operator norm on `X →L[ℂ] Y` and the
Hilbert-space adjoint. Its categorical endomorphism C⋆-algebra `End X` identifies canonically via
`HilbertCat.endStarAlgEquiv` with Mathlib's `X →L[ℂ] X`, matching the categorical spectral order on
`End X` with Mathlib's Loewner order (`ContinuousLinearMap.IsPositive`).

Zero objects in `HilbertCat 𝕜` are precisely the subsingleton Hilbert spaces (for which
`‖𝟙 X‖ = 0`), while nontrivial complex Hilbert spaces satisfy `‖𝟙 X‖ = 1`. Restricting to
`HilbertCat.isFiniteDimensional` yields the full C⋆-subcategory of finite-dimensional complex
Hilbert spaces via `CategoryTheory.ObjectProperty.instCStarCategoryFullSubcategory`.

## Main declarations

* `TauCeti.HilbertCat.instCStarCategory`: `CStarCategory (HilbertCat.{0, v} ℂ)`.
* `TauCeti.HilbertCat.endStarAlgEquiv`: `End X ≃⋆ₐ[ℂ] (X →L[ℂ] X)`.
* `TauCeti.HilbertCat.end_le_iff`, `TauCeti.HilbertCat.end_nonneg_iff`: the spectral order on
  `End X` agrees with Mathlib's Loewner order and `ContinuousLinearMap.IsPositive`.
* `TauCeti.HilbertCat.isZero_iff_subsingleton`,
  `TauCeti.HilbertCat.norm_id_eq_zero_iff_subsingleton`,
  `TauCeti.HilbertCat.norm_id_eq_one_iff_nontrivial`: zero-object and identity-norm
  characterizations.
* `TauCeti.HilbertCat.isFiniteDimensional`: isomorphism-closed object property cutting out
  finite-dimensional Hilbert spaces, whose complex full subcategory inherits `CStarCategory`.

## References

* [P. Ghez, R. Lima, J. E. Roberts, *W\*-categories*][ghez1985]
-/

public section

noncomputable section

open CategoryTheory

universe u v

namespace TauCeti.HilbertCat

instance instCStarCategory : CStarCategory (HilbertCat.{0, v} ℂ) where
  homNorm X Y := inferInstanceAs (Norm (X ⟶ Y))
  homMetricSpace X Y := inferInstanceAs (MetricSpace (X ⟶ Y))
  homCompleteSpace X Y := inferInstanceAs (CompleteSpace (X ⟶ Y))
  norm_smul_le c f := norm_smul_le c (f : _ →L[ℂ] _)
  norm_comp_le f g := ContinuousLinearMap.opNorm_comp_le g f
  norm_mul_self_le f := (ContinuousLinearMap.norm_adjoint_comp_self (f : _ →L[ℂ] _)).ge
  exists_comp_dagger_eq {X Y} f := by
    have hpos := ContinuousLinearMap.isPositive_adjoint_comp_self (f : X →L[ℂ] Y)
    obtain ⟨p, hp_sa, -, hp_sq⟩ := CFC.exists_sqrt_of_isSelfAdjoint_of_quasispectrumRestricts
      hpos.isSelfAdjoint hpos.spectrumRestricts
    have hp_adj : ContinuousLinearMap.adjoint p = p :=
      ContinuousLinearMap.star_eq_adjoint p ▸ hp_sa.star_eq
    refine ⟨p, ?_⟩
    simpa [comp_eq_comp, dagger_eq_adjoint, sq, ContinuousLinearMap.mul_def, hp_adj]
      using hp_sq.symm

/-- The categorical endomorphism C⋆-algebra `End X` of a complex Hilbert space `X` is canonically
`⋆`-isomorphic to `X →L[ℂ] X` (both use operator-order multiplication). -/
def endStarAlgEquiv (X : HilbertCat.{0, v} ℂ) : End X ≃⋆ₐ[ℂ] (X →L[ℂ] X) where
  toFun f := f.asHom
  invFun f := End.of f
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  map_star' _ := rfl

/-- Forward evaluation of `HilbertCat.endStarAlgEquiv`. -/
@[simp] theorem endStarAlgEquiv_apply (X : HilbertCat.{0, v} ℂ) (f : End X) :
    endStarAlgEquiv X f = f.asHom := (rfl)

/-- Inverse evaluation of `HilbertCat.endStarAlgEquiv`. -/
@[simp] theorem endStarAlgEquiv_symm_apply (X : HilbertCat.{0, v} ℂ) (f : X →L[ℂ] X) :
    (endStarAlgEquiv X).symm f = End.of f := (rfl)

/-- The spectral order on `End X` agrees with the Loewner partial order on `X →L[ℂ] X`. -/
theorem end_le_iff {X : HilbertCat.{0, v} ℂ} {f g : End X} :
    f ≤ g ↔ ConcreteCategory.hom f.asHom ≤ ConcreteCategory.hom g.asHom :=
  (NonUnitalStarAlgHom.map_le_map_iff (endStarAlgEquiv X) (endStarAlgEquiv X).injective).symm

/-- Nonnegativity in `End X` agrees with `ContinuousLinearMap.IsPositive` on `X →L[ℂ] X`. -/
theorem end_nonneg_iff {X : HilbertCat.{0, v} ℂ} {f : End X} :
    0 ≤ f ↔ (ConcreteCategory.hom f.asHom).IsPositive := by
  rw [end_le_iff, ContinuousLinearMap.le_def]
  simp

section ZeroAndFiniteDimensional

variable {𝕜 : Type u} [RCLike 𝕜]

/-- An object of `HilbertCat 𝕜` is a categorical zero object if and only if its underlying carrier
is subsingleton. -/
theorem isZero_iff_subsingleton {X : HilbertCat.{u, v} 𝕜} :
    Limits.IsZero X ↔ Subsingleton X := by
  rw [Limits.IsZero.iff_id_eq_zero, id_eq_id, ContinuousLinearMap.ext_iff,
    subsingleton_iff_forall_eq 0]
  simp

/-- Any subsingleton Hilbert space bundles to a zero object of `HilbertCat 𝕜`. -/
theorem isZero_of_subsingleton (E : Type v) [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [CompleteSpace E] [Subsingleton E] : Limits.IsZero (of 𝕜 E) :=
  isZero_iff_subsingleton.mpr inferInstance

/-- The identity morphism of `X : HilbertCat ℂ` has norm `0` if and only if `X` is subsingleton. -/
theorem norm_id_eq_zero_iff_subsingleton {X : HilbertCat.{0, v} ℂ} :
    ‖𝟙 X‖ = 0 ↔ Subsingleton X :=
  (norm_id_eq_zero_iff X).trans isZero_iff_subsingleton

/-- The identity morphism of `X : HilbertCat ℂ` has norm `1` if and only if `X` is nontrivial. -/
theorem norm_id_eq_one_iff_nontrivial {X : HilbertCat.{0, v} ℂ} :
    ‖𝟙 X‖ = 1 ↔ Nontrivial X := by
  rw [← not_subsingleton_iff_nontrivial, ← isZero_iff_subsingleton]
  refine ⟨fun h hzero => ?_, norm_id_of_not_isZero⟩
  rw [hzero.norm_id_eq_zero] at h
  exact zero_ne_one h

/-- Object property selecting the finite-dimensional Hilbert spaces in `HilbertCat 𝕜`. For `𝕜 = ℂ`,
`(HilbertCat.isFiniteDimensional (𝕜 := ℂ)).FullSubcategory` inherits `CStarCategory` from
`CategoryTheory.ObjectProperty.instCStarCategoryFullSubcategory`. -/
def isFiniteDimensional : ObjectProperty (HilbertCat.{u, v} 𝕜) :=
  fun X => FiniteDimensional 𝕜 X

/-- Membership in `HilbertCat.isFiniteDimensional` is `FiniteDimensional 𝕜 X`. -/
@[simp] theorem isFiniteDimensional_iff (X : HilbertCat.{u, v} 𝕜) :
    isFiniteDimensional X ↔ FiniteDimensional 𝕜 X := Iff.rfl

instance instIsClosedUnderIsomorphismsIsFiniteDimensional :
    (isFiniteDimensional (𝕜 := 𝕜)).IsClosedUnderIsomorphisms where
  of_iso {X Y} e hX := by
    rw [isFiniteDimensional_iff] at hX ⊢
    exact (LinearEquiv.ofLinearMap (ConcreteCategory.hom e.hom).toLinearMap
      (ConcreteCategory.hom e.inv).toLinearMap
      (LinearMap.ext fun y => DFunLike.congr_fun (congrArg ConcreteCategory.hom e.inv_hom_id) y)
      (LinearMap.ext fun x =>
        DFunLike.congr_fun (congrArg ConcreteCategory.hom e.hom_inv_id) x)).finiteDimensional

end ZeroAndFiniteDimensional

end TauCeti.HilbertCat
