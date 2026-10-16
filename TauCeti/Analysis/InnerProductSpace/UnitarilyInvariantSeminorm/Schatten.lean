/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm.Frobenius
public import TauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm.Gauge
public import TauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm.OpNorm

import TauCeti.Analysis.OperatorIdeal.ApproximationNumber.EckartYoung

/-!
# The Schatten seminorms

For `1 ≤ p ≤ ∞` and a linear map `A : E →ₗ[𝕜] F` between finite-dimensional inner product spaces,
the **Schatten `p`-seminorm** `‖A‖_p` is the `ℓᵖ` norm of the singular values of `A`:
`‖A‖_p = (∑ᵢ σᵢ(A)ᵖ)^(1/p)` for finite `p`, and `‖A‖_∞ = maxᵢ σᵢ(A)`. The `ℓᵖ` norm on real
tuples is a symmetric gauge (`Seminorm.isSymmetricGauge_piLp`), so the Schatten seminorm is the
unitarily invariant seminorm attached to this gauge by
`TauCeti.UnitarilyInvariantSeminorm.ofIsSymmetricGauge`. In particular its triangle inequality,
`‖A + B‖_p ≤ ‖A‖_p + ‖B‖_p`, comes from the weak majorization `σ(A + B) ≺w σ(A) + σ(B)` and is
part of the seminorm structure.

The Schatten seminorm vanishes only at `0`, dominates the operator norm, is invariant under taking
adjoints, and satisfies the ideal inequalities `‖C A‖_p ≤ ‖C‖ ‖A‖_p` and `‖A C‖_p ≤ ‖A‖_p ‖C‖` for
rectangular factors `C`. Its endpoints are the nuclear seminorm (`p = 1`), the Frobenius seminorm
(`p = 2`) and the operator norm (`p = ∞`).

## Main declarations

* `TauCeti.UnitarilyInvariantSeminorm.schatten`: the Schatten `p`-seminorm.
* `TauCeti.UnitarilyInvariantSeminorm.schatten_apply_of_ne_top`: `‖A‖_p = (∑ᵢ σᵢ(A)ᵖ)^(1/p)` for
  finite `p`.
* `TauCeti.UnitarilyInvariantSeminorm.schatten_apply_eq_zero_iff`: `‖A‖_p = 0 ↔ A = 0`.
* `TauCeti.UnitarilyInvariantSeminorm.opNorm_apply_le_schatten_apply`: `‖A‖ ≤ ‖A‖_p`.
* `TauCeti.UnitarilyInvariantSeminorm.schatten_apply_adjoint`: `‖A†‖_p = ‖A‖_p`.
* `TauCeti.UnitarilyInvariantSeminorm.schatten_comp_le_left`,
  `TauCeti.UnitarilyInvariantSeminorm.schatten_comp_le_right`,
  `TauCeti.UnitarilyInvariantSeminorm.schatten_comp_comp_le`: the ideal inequalities.
* `TauCeti.UnitarilyInvariantSeminorm.schatten_one`, `schatten_two`, `schatten_top`: the
  nuclear, Frobenius and operator-norm endpoints.

## References

* R. Bhatia, *Matrix Analysis*, Graduate Texts in Mathematics 169, Springer, 1997, Section IV.2.
* B. Simon, *Trace Ideals and Their Applications*, second edition, Mathematical Surveys and
  Monographs 120, American Mathematical Society, 2005, Chapter 2.
-/

public section

open Module
open scoped ENNReal

namespace TauCeti.UnitarilyInvariantSeminorm

variable (𝕜 E F : Type*) [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]
  (p : ℝ≥0∞) [Fact (1 ≤ p)]

/-- The **Schatten `p`-seminorm** `‖A‖_p`, the `ℓᵖ` norm of the singular values of `A`, as a
unitarily invariant seminorm: `‖A‖_p = (∑ᵢ σᵢ(A)ᵖ)^(1/p)` for finite `p`
(`TauCeti.UnitarilyInvariantSeminorm.schatten_apply_of_ne_top`) and `‖A‖_∞ = σ₀(A)` is the
operator norm (`TauCeti.UnitarilyInvariantSeminorm.schatten_top`). -/
noncomputable def schatten : UnitarilyInvariantSeminorm 𝕜 E F :=
  ofIsSymmetricGauge (n := finrank 𝕜 E) _ (Seminorm.isSymmetricGauge_piLp p)

variable {𝕜 E F}

/-- The Schatten `p`-seminorm of `A` is the `ℓᵖ` norm of the tuple `(σ₀(A), …, σₙ₋₁(A))` of its
singular values, where `n = dim E`. -/
theorem schatten_apply (A : E →ₗ[𝕜] F) :
    schatten 𝕜 E F p A = ‖WithLp.toLp p fun i : Fin (finrank 𝕜 E) ↦ A.singularValues i‖ := by
  rw [schatten, ofIsSymmetricGauge_apply, Seminorm.comp_apply, coe_normSeminorm,
    LinearEquiv.coe_coe, WithLp.coe_symm_linearEquiv]

/-- For finite `p`, the Schatten `p`-seminorm is `‖A‖_p = (∑ᵢ σᵢ(A)ᵖ)^(1/p)`. -/
theorem schatten_apply_of_ne_top (hp : p ≠ ∞) (A : E →ₗ[𝕜] F) :
    schatten 𝕜 E F p A = (A.singularValues.sum fun _ s ↦ s ^ p.toReal) ^ (1 / p.toReal) := by
  have hp0 : 0 < p.toReal :=
    ENNReal.toReal_pos (one_pos.trans_le Fact.out).ne' hp
  rw [schatten_apply, PiLp.norm_eq_sum hp0]
  congr 1
  simp only [Real.norm_of_nonneg (A.singularValues_nonneg _)]
  exact A.sum_fin_singularValues (· ^ p.toReal) (by simp [hp0.ne'])

/-- The Schatten seminorms dominate the operator norm: `‖A‖ ≤ ‖A‖_p`. -/
theorem opNorm_apply_le_schatten_apply (A : E →ₗ[𝕜] F) :
    opNorm 𝕜 E F A ≤ schatten 𝕜 E F p A := by
  rw [opNorm_apply, A.norm_toContinuousLinearMap_eq_singularValues_zero, schatten_apply]
  rcases (finrank 𝕜 E).eq_zero_or_pos with h | h
  · rw [A.singularValues_of_finrank_le h.le]
    exact norm_nonneg _
  · simpa [Real.norm_of_nonneg (A.singularValues_nonneg 0)] using
      PiLp.norm_apply_le (WithLp.toLp p fun i : Fin (finrank 𝕜 E) ↦ A.singularValues i) ⟨0, h⟩

/-- The Schatten seminorms are norms: `‖A‖_p = 0` only for `A = 0`. -/
@[simp]
theorem schatten_apply_eq_zero_iff {A : E →ₗ[𝕜] F} : schatten 𝕜 E F p A = 0 ↔ A = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ map_zero _⟩
  have h0 := (opNorm_apply_le_schatten_apply p A).trans h.le
  rw [opNorm_apply] at h0
  exact LinearMap.toContinuousLinearMap.map_eq_zero_iff.mp (norm_le_zero_iff.mp h0)

/-! ### Endpoints -/

/-- At `p = 1`, the Schatten seminorm is the nuclear seminorm `∑ᵢ σᵢ(A)`. -/
@[simp]
theorem schatten_one : schatten 𝕜 E F 1 = nuclear 𝕜 E F := by
  ext A
  rw [schatten_apply_of_ne_top 1 ENNReal.one_ne_top, nuclear_apply]
  simp

/-- At `p = 2`, the Schatten seminorm is the Frobenius seminorm `√(∑ᵢ σᵢ(A)²)`. -/
@[simp]
theorem schatten_two : schatten 𝕜 E F 2 = frobenius 𝕜 E F := by
  ext A
  rw [schatten_apply_of_ne_top 2 ENNReal.ofNat_ne_top,
    frobenius_apply_eq_sqrt_sum_sq_singularValues, Real.sqrt_eq_rpow]
  simp

/-- At `p = ∞`, the Schatten seminorm is the operator norm `σ₀(A)`. -/
@[simp]
theorem schatten_top : schatten 𝕜 E F ∞ = opNorm 𝕜 E F := by
  ext A
  refine le_antisymm ?_ (opNorm_apply_le_schatten_apply ∞ A)
  rw [schatten_apply, PiLp.norm_toLp, opNorm_apply,
    A.norm_toContinuousLinearMap_eq_singularValues_zero]
  refine pi_norm_le_iff_of_nonneg (A.singularValues_nonneg 0) |>.mpr fun i ↦ ?_
  rw [Real.norm_of_nonneg (A.singularValues_nonneg _)]
  exact A.singularValues_antitone (Nat.zero_le _)

/-! ### Adjoints and ideal inequalities -/

/-- The adjoint transport of the Schatten `p`-seminorm on `E →ₗ[𝕜] F` is the Schatten
`p`-seminorm on `F →ₗ[𝕜] E`. -/
@[simp]
theorem compAdjoint_schatten : (schatten 𝕜 E F p).compAdjoint = schatten 𝕜 F E p := by
  ext B
  rw [compAdjoint_apply]
  obtain rfl | hp := eq_or_ne p ∞
  · simp only [schatten_top, opNorm_apply,
      LinearMap.norm_toContinuousLinearMap_eq_singularValues_zero, LinearMap.singularValues_adjoint]
  · rw [schatten_apply_of_ne_top p hp, schatten_apply_of_ne_top p hp,
      LinearMap.singularValues_adjoint]

/-- The Schatten seminorms are invariant under taking adjoints: `‖A†‖_p = ‖A‖_p`. -/
@[simp]
theorem schatten_apply_adjoint (A : E →ₗ[𝕜] F) :
    schatten 𝕜 F E p (LinearMap.adjoint A) = schatten 𝕜 E F p A := by
  rw [← compAdjoint_apply, compAdjoint_schatten]

/-- **Ideal inequality, left factor.** If `‖C y‖ ≤ c * ‖y‖` for every `y` (for `c ≥ 0`: if `C` has
operator norm at most `c`), then `‖C A‖_p ≤ c * ‖A‖_p`. The factor `C : F →ₗ[𝕜] G` may change the
target space. -/
theorem schatten_comp_le_left {G : Type*} [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
    [FiniteDimensional 𝕜 G] (C : F →ₗ[𝕜] G) (A : E →ₗ[𝕜] F) {c : ℝ}
    (hC : ∀ y, ‖C y‖ ≤ c * ‖y‖) : schatten 𝕜 E G p (C ∘ₗ A) ≤ c * schatten 𝕜 E F p A := by
  rcases lt_or_ge c 0 with hc | hc
  · -- A negative constant forces `A = 0`.
    have hA : A = 0 := LinearMap.ext fun x ↦ norm_le_zero_iff.mp <|
      nonpos_of_mul_nonneg_right ((norm_nonneg _).trans (hC (A x))) hc
    simp [hA]
  -- Compare the singular values of `C A` with those of `A`, coordinatewise.
  have h := (Seminorm.isSymmetricGauge_piLp (ι := Fin (finrank 𝕜 E)) p).apply_le_of_abs_le
    (x := fun i ↦ (C ∘ₗ A).singularValues i)
    (y := c • fun i : Fin (finrank 𝕜 E) ↦ A.singularValues i) fun i ↦ by
      simp only [Pi.abs_apply, Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_nonneg hc,
        abs_of_nonneg (LinearMap.singularValues_nonneg _ _)]
      exact LinearMap.singularValues_comp_le C A hC i
  simp only [Seminorm.comp_apply, coe_normSeminorm, LinearEquiv.coe_coe,
    WithLp.coe_symm_linearEquiv, WithLp.toLp_smul, norm_smul, Real.norm_of_nonneg hc] at h
  rwa [schatten_apply, schatten_apply]

/-- **Ideal inequality, right factor.** If `0 ≤ c` and `‖C x‖ ≤ c * ‖x‖` for every `x`, then
`‖A C‖_p ≤ c * ‖A‖_p`. The factor `C : G →ₗ[𝕜] E` may change the source space; the sign condition
on `c` cannot be dropped, since for `G = 0` every `c` bounds `C`. -/
theorem schatten_comp_le_right {G : Type*} [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
    [FiniteDimensional 𝕜 G] (A : E →ₗ[𝕜] F) (C : G →ₗ[𝕜] E) {c : ℝ} (hc : 0 ≤ c)
    (hC : ∀ x, ‖C x‖ ≤ c * ‖x‖) : schatten 𝕜 G F p (A ∘ₗ C) ≤ c * schatten 𝕜 E F p A := by
  -- Pass to adjoints, where `C†` is a left factor with the same bound.
  have h := schatten_comp_le_left p (LinearMap.adjoint C) (LinearMap.adjoint A)
    (LinearMap.norm_adjoint_apply_le hc hC)
  rwa [← LinearMap.adjoint_comp, schatten_apply_adjoint, schatten_apply_adjoint] at h

/-- **Two-sided ideal inequality.** If `‖C y‖ ≤ c * ‖y‖` for every `y`, and `0 ≤ d` and
`‖D x‖ ≤ d * ‖x‖` for every `x`, then `‖C A D‖_p ≤ c * d * ‖A‖_p`. -/
theorem schatten_comp_comp_le {G H : Type*} [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
    [FiniteDimensional 𝕜 G] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
    [FiniteDimensional 𝕜 H] (C : F →ₗ[𝕜] G) (A : E →ₗ[𝕜] F) (D : H →ₗ[𝕜] E) {c d : ℝ}
    (hC : ∀ y, ‖C y‖ ≤ c * ‖y‖) (hd : 0 ≤ d) (hD : ∀ x, ‖D x‖ ≤ d * ‖x‖) :
    schatten 𝕜 H G p (C ∘ₗ A ∘ₗ D) ≤ c * d * schatten 𝕜 E F p A := by
  calc schatten 𝕜 H G p (C ∘ₗ A ∘ₗ D) = schatten 𝕜 H G p ((C ∘ₗ A) ∘ₗ D) := by
        rw [LinearMap.comp_assoc]
    _ ≤ d * schatten 𝕜 E G p (C ∘ₗ A) := schatten_comp_le_right p _ D hd hD
    _ ≤ d * (c * schatten 𝕜 E F p A) :=
        mul_le_mul_of_nonneg_left (schatten_comp_le_left p C A hC) hd
    _ = c * d * schatten 𝕜 E F p A := by ring

end TauCeti.UnitarilyInvariantSeminorm
