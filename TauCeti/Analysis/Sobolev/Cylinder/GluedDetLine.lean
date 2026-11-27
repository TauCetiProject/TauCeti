/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fredholm.DeterminantLine.Gluing
public import TauCeti.Analysis.Sobolev.Cylinder.GluedIndex

/-!
# The determinant line of glued operators on the cylinder

Let `D₁` and `D₂` be first-order operators on the cylinder `ℝ × S¹`, from `W^{1,2}` to `L²`, with
coefficient fields `M₁` and `M₂` whose ends match, and let `D_R` be the operator of the glued
coefficient field along a neck of length `2 R`. Stabilize the pieces by finite-dimensional
`ιᵢ : Sᵢ → L²` so that `Aᵢ (ξ, σ) = Dᵢ ξ + ιᵢ σ` is onto, with kernel `Eᵢ`, and let
`A_R (ξ, σ₁, σ₂) = D_R ξ + j_R (σ₁, σ₂)` be the stabilized glued operator, with kernel `E_R`. For
a right inverse `Q` of `A_R` the corrected pregluing `TauCeti.CylinderSobolev.gluingKerMap` maps
`E₁ × E₂` to `E_R`, bijectively for long necks and bounded `Q`
(`TauCeti.CylinderSobolev.exists_forall_ge_forall_gluingKerMap_bijective`). Through
`ContinuousLinearMap.detLineGluingEquiv` it gives the ordered determinant-line isomorphism of
linear gluing

`det D_R ≃ det D₁ ⊗ det D₂`

(`TauCeti.CylinderSobolev.gluingDetLineEquiv`), where `det D = det (ker D) ⊗ (det (coker D))^*`.
The kernel and cokernel of `D_R` need not split as those of the pieces; the isomorphism is built
from the stabilized kernels, through the exact sequence
`0 → ker D_R → E₁ × E₂ → S₁ × S₂ → coker D_R → 0` of linear gluing.

The gluing map depends on the choice of `Q`, and so does the isomorphism of determinant lines,
but only through a positive factor once the neck is long: for every bound `C`, for long necks
any two right inverses `Q` and `Q'` of norm at most `C` give isomorphisms of determinant lines
which differ by a positive real factor
(`TauCeti.CylinderSobolev.exists_forall_ge_forall_exists_pos_gluingDetLineEquiv_eq_smul`). So the
orientation of `det D_R` that the gluing isomorphism induces from orientations of `det D₁` and
`det D₂` does not depend on the right inverse. The reason is that the gluing map is affine in
`Q` (`TauCeti.CylinderSobolev.gluingKerMap_smul_add_smul`), and the right inverses
`(1 - t) Q' + t Q` of `A_R` keep norm at most `C`, so the gluing maps along this segment stay
bijective, and gluing isomorphisms joined by such a segment give the same orientation
(`ContinuousLinearMap.exists_pos_detLineGluingEquiv_eq_smul_of_forall_bijective`).

## Main definitions

* `TauCeti.CylinderSobolev.gluingDetLineEquiv`: the isomorphism `det D_R ≃ det D₁ ⊗ det D₂` of a
  bijective gluing map.

## Main results

* `TauCeti.CylinderSobolev.gluingKerMap_smul_add_smul`: the gluing map is affine in the right
  inverse.
* `TauCeti.CylinderSobolev.exists_forall_ge_forall_exists_pos_gluingDetLineEquiv_eq_smul`: for
  long necks and bounded right inverses, the isomorphism of determinant lines does not depend on
  the right inverse up to a positive factor.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., Section A.2
  (determinant line bundles) and Chapter 10 (linear gluing, and the orientation of glued moduli
  spaces).
-/

public section

noncomputable section

open Filter MeasureTheory Set Module TensorProduct
open scoped ENNReal

namespace TauCeti.CylinderSobolev

open StripSobolev ContinuousLinearMap

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  {S₁ S₂ : Type*} [NormedAddCommGroup S₁] [NormedSpace ℝ S₁]
  [NormedAddCommGroup S₂] [NormedSpace ℝ S₂]
  {M₁ M₂ : ℝ × ℝ → V × V × V →L[ℝ] W} {ι₁ : S₁ →L[ℝ] Lp W 2 stripMeasure}
  {ι₂ : S₂ →L[ℝ] Lp W 2 stripMeasure}

/-- **The gluing map is affine in the right inverse.** For right inverses `Q` and `Q'` of the
stabilized glued operator `A_R` and `a + b = 1`, the combination `a Q + b Q'` is again a right
inverse, and its gluing map is `a` times the gluing map of `Q` plus `b` times that of `Q'`. -/
theorem gluingKerMap_smul_add_smul {R : ℝ} {Q Q' : Lp W 2 stripMeasure →L[ℝ] H1 V × (S₁ × S₂)}
    (hQ : Function.RightInverse Q (((jetOperator 2 stripMeasure
      (Function.uncurry (gluedCoeff (Function.curry M₁) (Function.curry M₂) R))).comp
        (H1 V).subtypeL).coprod (gluedStabilizer ι₁ ι₂ R)))
    (hQ' : Function.RightInverse Q' (((jetOperator 2 stripMeasure
      (Function.uncurry (gluedCoeff (Function.curry M₁) (Function.curry M₂) R))).comp
        (H1 V).subtypeL).coprod (gluedStabilizer ι₁ ι₂ R)))
    {a b : ℝ} (hab : a + b = 1)
    (hQab : Function.RightInverse (a • Q + b • Q') (((jetOperator 2 stripMeasure
      (Function.uncurry (gluedCoeff (Function.curry M₁) (Function.curry M₂) R))).comp
        (H1 V).subtypeL).coprod (gluedStabilizer ι₁ ι₂ R)))
    (k : (((jetOperator 2 stripMeasure M₁).comp (H1 V).subtypeL).coprod ι₁).ker ×
      (((jetOperator 2 stripMeasure M₂).comp (H1 V).subtypeL).coprod ι₂).ker) :
    gluingKerMap hQab k = a • gluingKerMap hQ k + b • gluingKerMap hQ' k := by
  obtain rfl : b = 1 - a := by linarith
  refine Subtype.ext ?_
  simp only [coe_gluingKerMap_apply, add_apply, FunLike.coe_smul, Pi.smul_apply,
    Submodule.coe_add, Submodule.coe_smul]
  module

variable [FiniteDimensional ℝ S₁] [FiniteDimensional ℝ S₂]
  [FiniteDimensional ℝ ((jetOperator 2 stripMeasure M₁).comp (H1 V).subtypeL).ker]
  [FiniteDimensional ℝ ((jetOperator 2 stripMeasure M₂).comp (H1 V).subtypeL).ker]

/-- **The determinant-line isomorphism of linear gluing on the cylinder.** Let the stabilized
pieces `Aᵢ (ξ, σ) = Dᵢ ξ + ιᵢ σ` be onto, let `Q` be a right inverse of the stabilized glued
operator `A_R`, and let the gluing map `E₁ × E₂ → E_R` of `Q`
(`TauCeti.CylinderSobolev.gluingKerMap`) be bijective, as it is for long necks and bounded `Q`.
This is the isomorphism `det D_R ≃ det D₁ ⊗ det D₂` of `ContinuousLinearMap.detLineGluingEquiv`
for this gluing map (`TauCeti.CylinderSobolev.gluingDetLineEquiv_def`). -/
def gluingDetLineEquiv
    (h₁ : Function.Surjective (((jetOperator 2 stripMeasure M₁).comp (H1 V).subtypeL).coprod ι₁))
    (h₂ : Function.Surjective (((jetOperator 2 stripMeasure M₂).comp (H1 V).subtypeL).coprod ι₂))
    {R : ℝ} {Q : Lp W 2 stripMeasure →L[ℝ] H1 V × (S₁ × S₂)}
    (hQ : Function.RightInverse Q (((jetOperator 2 stripMeasure
      (Function.uncurry (gluedCoeff (Function.curry M₁) (Function.curry M₂) R))).comp
        (H1 V).subtypeL).coprod (gluedStabilizer ι₁ ι₂ R)))
    (hg : Function.Bijective (gluingKerMap hQ)) :
    (((jetOperator 2 stripMeasure
      (Function.uncurry (gluedCoeff (Function.curry M₁) (Function.curry M₂) R))).comp
        (H1 V).subtypeL : H1 V →L[ℝ] Lp W 2 stripMeasure) :
          H1 V →ₗ[ℝ] Lp W 2 stripMeasure).detLine ≃ₗ[ℝ]
      (((jetOperator 2 stripMeasure M₁).comp (H1 V).subtypeL : H1 V →L[ℝ] Lp W 2 stripMeasure) :
        H1 V →ₗ[ℝ] Lp W 2 stripMeasure).detLine ⊗[ℝ]
      (((jetOperator 2 stripMeasure M₂).comp (H1 V).subtypeL : H1 V →L[ℝ] Lp W 2 stripMeasure) :
        H1 V →ₗ[ℝ] Lp W 2 stripMeasure).detLine :=
  detLineGluingEquiv _ (gluedStabilizer ι₁ ι₂ R) hQ.surjective h₁ h₂
    (LinearEquiv.ofBijective (gluingKerMap hQ).toLinearMap hg)

/-- `TauCeti.CylinderSobolev.gluingDetLineEquiv` is `ContinuousLinearMap.detLineGluingEquiv` for
the gluing map of `Q`. -/
theorem gluingDetLineEquiv_def
    (h₁ : Function.Surjective (((jetOperator 2 stripMeasure M₁).comp (H1 V).subtypeL).coprod ι₁))
    (h₂ : Function.Surjective (((jetOperator 2 stripMeasure M₂).comp (H1 V).subtypeL).coprod ι₂))
    {R : ℝ} {Q : Lp W 2 stripMeasure →L[ℝ] H1 V × (S₁ × S₂)}
    (hQ : Function.RightInverse Q (((jetOperator 2 stripMeasure
      (Function.uncurry (gluedCoeff (Function.curry M₁) (Function.curry M₂) R))).comp
        (H1 V).subtypeL).coprod (gluedStabilizer ι₁ ι₂ R)))
    (hg : Function.Bijective (gluingKerMap hQ)) :
    gluingDetLineEquiv h₁ h₂ hQ hg = detLineGluingEquiv _ (gluedStabilizer ι₁ ι₂ R)
      hQ.surjective h₁ h₂ (LinearEquiv.ofBijective (gluingKerMap hQ).toLinearMap hg) :=
  (rfl)

-- Stabilized kernels `(D.coprod ι).ker` are finite-dimensional when `D.ker` and `S` are.
attribute [local instance] finiteDimensional_ker_coprod

variable [CompleteSpace W] in
/-- **The orientation of linear gluing does not depend on the right inverse.** Let `D₁` and `D₂`
be first-order operators on the cylinder with essentially bounded coefficient fields `M₁` and
`M₂` whose ends match, `M₁(s, t) → M(t)` as `s → +∞` and `M₂(s, t) → M(t)` as `s → -∞` uniformly
in `t`. Let `ιᵢ : Sᵢ → L²` be finite-dimensional stabilizers, the sections `ι₁ σ₁` vanishing for
`s > T` and `ι₂ σ₂` for `s < -T`, such that the stabilized operators `Aᵢ (ξ, σ) = Dᵢ ξ + ιᵢ σ`
have bounded right inverses `Qᵢ`, and let `Dᵢ` have finite-dimensional kernels. Then for every
bound `C` and every sufficiently long neck, any two right inverses `Q` and `Q'` of the stabilized
glued operator with `‖Q‖ ≤ C` and `‖Q'‖ ≤ C` give determinant-line isomorphisms
`det D_R ≃ det D₁ ⊗ det D₂` (`TauCeti.CylinderSobolev.gluingDetLineEquiv`) differing by a
positive real factor. -/
theorem exists_forall_ge_forall_exists_pos_gluingDetLineEquiv_eq_smul
    {M : ℝ → V × V × V →L[ℝ] W} (hM₁ : MemLp M₁ ∞ stripMeasure) (hM₂ : MemLp M₂ ∞ stripMeasure)
    (h₁ : TendstoUniformlyOn (Function.curry M₁) M atTop (Icc 0 1))
    (h₂ : TendstoUniformlyOn (Function.curry M₂) M atBot (Icc 0 1)) {T : ℝ}
    (hι₁ : ∀ σ, ∀ᵐ z ∂stripMeasure, T < z.1 → ι₁ σ z = 0)
    (hι₂ : ∀ σ, ∀ᵐ z ∂stripMeasure, z.1 < -T → ι₂ σ z = 0)
    {Q₁ : Lp W 2 stripMeasure →L[ℝ] H1 V × S₁} {Q₂ : Lp W 2 stripMeasure →L[ℝ] H1 V × S₂}
    (hQ₁ : Function.RightInverse Q₁
      (((jetOperator 2 stripMeasure M₁).comp (H1 V).subtypeL).coprod ι₁))
    (hQ₂ : Function.RightInverse Q₂
      (((jetOperator 2 stripMeasure M₂).comp (H1 V).subtypeL).coprod ι₂))
    (C : ℝ) :
    ∃ R₀ : ℝ, ∀ R ≥ R₀, ∀ (Q Q' : Lp W 2 stripMeasure →L[ℝ] H1 V × (S₁ × S₂))
      (hQ : Function.RightInverse Q (((jetOperator 2 stripMeasure
        (Function.uncurry (gluedCoeff (Function.curry M₁) (Function.curry M₂) R))).comp
          (H1 V).subtypeL).coprod (gluedStabilizer ι₁ ι₂ R)))
      (hQ' : Function.RightInverse Q' (((jetOperator 2 stripMeasure
        (Function.uncurry (gluedCoeff (Function.curry M₁) (Function.curry M₂) R))).comp
          (H1 V).subtypeL).coprod (gluedStabilizer ι₁ ι₂ R)))
      (hg : Function.Bijective (gluingKerMap hQ)) (hg' : Function.Bijective (gluingKerMap hQ')),
      ‖Q‖ ≤ C → ‖Q'‖ ≤ C → ∃ c : ℝ, 0 < c ∧ ∀ x,
        gluingDetLineEquiv hQ₁.surjective hQ₂.surjective hQ' hg' x =
          c • gluingDetLineEquiv hQ₁.surjective hQ₂.surjective hQ hg x := by
  obtain ⟨R₀, hR₀⟩ := exists_forall_ge_forall_gluingKerMap_bijective hM₁ hM₂ h₁ h₂ hι₁ hι₂
    (ContinuousLinearMap.ext hQ₁) (ContinuousLinearMap.ext hQ₂) C
  refine ⟨R₀, fun R hR Q Q' hQ hQ' hg hg' hQC hQC' ↦ ?_⟩
  rw [gluingDetLineEquiv_def, gluingDetLineEquiv_def]
  refine exists_pos_detLineGluingEquiv_eq_smul_of_forall_bijective _ (gluedStabilizer ι₁ ι₂ R)
    hQ.surjective hQ₁.surjective hQ₂.surjective
    (LinearEquiv.ofBijective (gluingKerMap hQ).toLinearMap hg)
    (LinearEquiv.ofBijective (gluingKerMap hQ').toLinearMap hg') fun t ht ↦ ?_
  -- Along the segment `Q_t = (1 - t) Q' + t Q` of right inverses of norm at most `C`, the gluing
  -- maps are the corresponding combinations of the gluing maps of `Q'` and `Q`, and they stay
  -- bijective.
  have hQt : Function.RightInverse ((1 - t) • Q' + t • Q) (((jetOperator 2 stripMeasure
      (Function.uncurry (gluedCoeff (Function.curry M₁) (Function.curry M₂) R))).comp
        (H1 V).subtypeL).coprod (gluedStabilizer ι₁ ι₂ R)) := fun y ↦ by
    simp only [add_apply, FunLike.coe_smul, Pi.smul_apply, map_add, map_smul, hQ y, hQ' y]
    module
  have hQtC : ‖(1 - t) • Q' + t • Q‖ ≤ C := by
    have h0 : 0 ≤ 1 - t := sub_nonneg.2 ht.2
    calc ‖(1 - t) • Q' + t • Q‖ ≤ ‖1 - t‖ * ‖Q'‖ + ‖t‖ * ‖Q‖ :=
          (opNorm_add_le _ _).trans (add_le_add (opNorm_smul_le _ _) (opNorm_smul_le _ _))
      _ = (1 - t) * ‖Q'‖ + t * ‖Q‖ := by
          rw [Real.norm_of_nonneg h0, Real.norm_of_nonneg ht.1]
      _ ≤ (1 - t) * C + t * C :=
          add_le_add (mul_le_mul_of_nonneg_left hQC' h0) (mul_le_mul_of_nonneg_left hQC ht.1)
      _ = C := by ring
  convert (hR₀ R hR).2 _ hQt hQtC using 1
  funext k
  simp [gluingKerMap_smul_add_smul hQ' hQ (by ring) hQt k]

end TauCeti.CylinderSobolev
