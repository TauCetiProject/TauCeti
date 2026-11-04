/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Diffeomorph
public import TauCeti.Geometry.Manifold.DifferentialForm.Naturality
import TauCeti.Geometry.Manifold.Diffeomorph.Basic

/-!
# Maps tangent to a distribution

Let `D` be a distribution on a manifold `M`, given as a field of subspaces `D x ⊆ T_x M`. A map
`f : N → M` is **isotropic** for `D` (`TauCeti.IsDistributionIsotropicMap J D f`) when it is
tangent to `D`: every tangent image `df_y(T_y N)` lies in `D (f y)`. The source is an arbitrary
charted space and `f` need not be injective, so the predicate applies to embedded and immersed
submanifolds alike, through any parametrization
(`Diffeomorph.isDistributionIsotropicMap_comp_diffeomorph_iff`). For a contact structure `D`
these are the parametrized isotropic submanifolds.

If a one-form `α` vanishes on `D` near `f y`, then an isotropic map pulls `α` back to zero near
`y`, hence also pulls back `dα` to zero at `y`
(`TauCeti.IsDistributionIsotropicMap.mextDeriv_apply_mfderiv_eq_zero`). This is the key step in
showing that the Levi form of a hyperplane field vanishes on the tangent images of an isotropic
map.

## Main declarations

* `TauCeti.IsDistributionIsotropicMap`: maps tangent to a distribution.
* `TauCeti.isDistributionIsotropicMap_iff_range_le`: isotropy as inclusion of the tangent images.
* `Diffeomorph.isDistributionIsotropicMap_diffeomorph_comp_iff`: transport of isotropy by a
  diffeomorphism whose differential carries one distribution onto the other.
* `TauCeti.IsDistributionIsotropicMap.mextDeriv_apply_mfderiv_eq_zero`: an isotropic map pulls
  back the exterior derivative of a local defining form to zero.
-/

public section

noncomputable section

open Set Filter Function Bundle Manifold
open scoped Manifold Topology ContDiff

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  {E' H' N : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} [TopologicalSpace N] [ChartedSpace H' N]
  {D : Π x : M, Submodule ℝ (TangentSpace I x)} {f : N → M}

variable (J D) in
/-- A map `f : N → M` is **isotropic** for a distribution `D` on `M` when it is tangent to `D`:
every tangent image `df_y(T_y N)` lies in `D (f y)`. For a contact structure `D` these are the
parametrized isotropic submanifolds.

The tangent image is taken with `mfderiv`, which is `0` at points where `f` is not differentiable,
so there the condition holds trivially. Isotropy is meaningful for differentiable maps. -/
def IsDistributionIsotropicMap (f : N → M) : Prop :=
  ∀ y, LinearMap.range (mfderiv J I f y).toLinearMap ≤ D (f y)

/-- A map is isotropic exactly when each tangent image lies in the distribution. -/
theorem isDistributionIsotropicMap_iff_range_le :
    IsDistributionIsotropicMap J D f ↔
      ∀ y, LinearMap.range (mfderiv J I f y).toLinearMap ≤ D (f y) :=
  Iff.rfl

/-- The tangent image of an isotropic map lies in the distribution. -/
theorem IsDistributionIsotropicMap.range_le (h : IsDistributionIsotropicMap J D f) (y : N) :
    LinearMap.range (mfderiv J I f y).toLinearMap ≤ D (f y) :=
  isDistributionIsotropicMap_iff_range_le.1 h y

/-- A map is isotropic exactly when it sends every tangent vector into the distribution. -/
theorem isDistributionIsotropicMap_iff :
    IsDistributionIsotropicMap J D f ↔ ∀ y v, mfderiv J I f y v ∈ D (f y) := by
  simp only [isDistributionIsotropicMap_iff_range_le, LinearMap.range_le_iff_comap,
    Submodule.eq_top_iff', Submodule.mem_comap, ContinuousLinearMap.coe_coe]

/-- An isotropic map sends every tangent vector into the distribution. -/
theorem IsDistributionIsotropicMap.mfderiv_mem (h : IsDistributionIsotropicMap J D f) (y : N)
    (v : TangentSpace J y) :
    mfderiv J I f y v ∈ D (f y) :=
  isDistributionIsotropicMap_iff.1 h y v

/-- **Independence of the parametrization.** Precomposing with a diffeomorphism of the source
does not change whether a map is isotropic. -/
theorem _root_.Diffeomorph.isDistributionIsotropicMap_comp_diffeomorph_iff {E'' H'' : Type*}
    [NormedAddCommGroup E''] [NormedSpace ℝ E''] [TopologicalSpace H'']
    {K : ModelWithCorners ℝ E'' H''} {P : Type*} [TopologicalSpace P] [ChartedSpace H'' P]
    {n : ℕ∞ω} (φ : P ≃ₘ^n⟮K, J⟯ N) (hn : n ≠ 0) :
    IsDistributionIsotropicMap K D (f ∘ φ) ↔ IsDistributionIsotropicMap J D f := by
  simp only [isDistributionIsotropicMap_iff_range_le, φ.range_mfderiv_comp_diffeomorph hn,
    Function.comp_apply]
  exact ⟨fun h y ↦ φ.apply_symm_apply y ▸ h (φ.symm y), fun h x ↦ h (φ x)⟩

/-- **Transport by a diffeomorphism of the target.** If the differential of a diffeomorphism `ψ`
carries the distribution `D` onto `D'`, then `ψ ∘ f` is isotropic for `D'` exactly when `f` is
isotropic for `D`. -/
theorem _root_.Diffeomorph.isDistributionIsotropicMap_diffeomorph_comp_iff {E'' H'' : Type*}
    [NormedAddCommGroup E''] [NormedSpace ℝ E''] [TopologicalSpace H'']
    {I' : ModelWithCorners ℝ E'' H''} {M' : Type*} [TopologicalSpace M'] [ChartedSpace H'' M']
    {D' : Π x : M', Submodule ℝ (TangentSpace I' x)} {n : ℕ∞ω} (ψ : M ≃ₘ^n⟮I, I'⟯ M')
    (hn : n ≠ 0) (hψ : ∀ x v, v ∈ D x ↔ mfderiv I I' ψ x v ∈ D' (ψ x)) :
    IsDistributionIsotropicMap J D' (ψ ∘ f) ↔ IsDistributionIsotropicMap J D f := by
  simp only [isDistributionIsotropicMap_iff_range_le, ψ.range_mfderiv_diffeomorph_comp hn,
    Submodule.map_le_iff_le_comap, Function.comp_apply]
  refine forall_congr' fun y ↦ ?_
  have hD : (D' (ψ (f y))).comap
      (ψ.mfderivToContinuousLinearEquiv hn (f y)).toLinearEquiv.toLinearMap = D (f y) := by
    ext v
    rw [Submodule.mem_comap, hψ, ← ψ.mfderivToContinuousLinearEquiv_coe hn, LinearEquiv.coe_coe,
      ContinuousLinearEquiv.coe_toLinearEquiv, ContinuousLinearEquiv.coe_coe]
  rw [hD]

/-! ### Pulling back a local defining form -/

variable [IsManifold I 2 M] [IsManifold J 2 N]

/-- **An isotropic map pulls back the derivative of a local defining form to zero.** Let `α` be a
one-form which is `C¹` at `f y` and whose kernel contains `D` near `f y`. If `f` is isotropic for
`D` and `C²` at `y`, then `dα_(f y)(df u, df v) = 0`: since `f^* α` vanishes near `y`, so does
`f^* dα = d(f^* α)` at `y`. -/
theorem IsDistributionIsotropicMap.mextDeriv_apply_mfderiv_eq_zero
    (h : IsDistributionIsotropicMap J D f) {y : N} (hf : ContMDiffAt J I 2 f y)
    {α : RoughForm I M ℝ 1}
    (hα : ContMDiffAt I (I.prod 𝓘(ℝ, E [⋀^Fin 1]→L[ℝ] ℝ)) 1
      (fun x ↦ TotalSpace.mk' (E [⋀^Fin 1]→L[ℝ] ℝ) x (α x)) (f y))
    (hDα : ∀ᶠ x in 𝓝 (f y), D x ≤ α.ker x) (u v : TangentSpace J y) :
    mextDeriv α (f y) ![mfderiv J I f y u, mfderiv J I f y v] = 0 := by
  -- The pulled-back one-form `f^* α` vanishes near `y`.
  have hzero : ∀ᶠ z in 𝓝 y, mpullback J I f α z = (0 : RoughForm J N ℝ 1) z :=
    (hf.continuousAt.eventually hDα).mono fun z hz ↦
      mpullback_apply_eq_zero_iff_mem_ker.2 fun w ↦ hz (h.mfderiv_mem z w)
  have hd := mpullback_mextDeriv_at hf hα
  rw [mextDeriv_congr_of_eventuallyEq hzero, mextDeriv_zero, Pi.zero_apply] at hd
  have hd' := congrArg (fun φ ↦ φ ![u, v]) hd
  simp only [mpullback_apply, ContinuousAlternatingMap.coe_zero, Pi.zero_apply] at hd'
  rw [← hd']
  exact congrArg (mextDeriv α (f y)) (funext fun i ↦ by fin_cases i <;> simp)

end TauCeti
