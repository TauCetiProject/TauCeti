/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Lp.lpHolder
public import Mathlib.Analysis.Normed.Operator.Mul

/-!
# Pointwise multiplication for `lp`

Specialisation of Mathlib's `lp.holderL` to pointwise multiplication
`lp.mulL : ℓ^p(ι, R) →L[𝕜] ℓ^q(ι, R) →L[𝕜] ℓ^r(ι, R)` (`1/r = 1/p + 1/q`) on a non-unital
normed `𝕜`-algebra `R`, with `lp.mulL_apply_apply`, `lp.norm_mulL_le`, and
`lp.norm_mulL_apply_apply_le`.
-/

public section

noncomputable section

open scoped ENNReal NNReal

namespace lp

variable {ι 𝕜 : Type*} [RCLike 𝕜] {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]

variable (𝕜) (R : Type*) [NonUnitalNormedRing R] [NormedSpace 𝕜 R]
  [IsScalarTower 𝕜 R R] [SMulCommClass 𝕜 R R]

/-- Pointwise multiplication `ℓ^p(ι, R) × ℓ^q(ι, R) → ℓ^r(ι, R)` for `1/r = 1/p + 1/q`. -/
def mulL (r : ℝ≥0∞) [Fact (1 ≤ r)] [p.HolderTriple q r] :
    lp (fun _ : ι ↦ R) p →L[𝕜] lp (fun _ : ι ↦ R) q →L[𝕜] lp (fun _ : ι ↦ R) r :=
  holderL r (fun _ : ι ↦ ContinuousLinearMap.mul 𝕜 R) (K := 1) fun _ ↦
    by simpa using ContinuousLinearMap.opNorm_mul_le 𝕜 R

/-- Coordinatewise evaluation of `lp.mulL`. -/
@[simp] theorem mulL_apply_apply (r : ℝ≥0∞) [Fact (1 ≤ r)] [p.HolderTriple q r]
    (a : lp (fun _ : ι ↦ R) p) (b : lp (fun _ : ι ↦ R) q) (i : ι) :
    mulL 𝕜 R r a b i = a i * b i := by
  rw [mulL, holderL, LinearMap.mkContinuous₂_apply, holderₗ_apply_apply_coe,
    ContinuousLinearMap.mul_apply']

/-- Operator norm bound `‖lp.mulL 𝕜 R r‖ ≤ 1`. -/
theorem norm_mulL_le (r : ℝ≥0∞) [Fact (1 ≤ r)] [p.HolderTriple q r] :
    ‖mulL 𝕜 R (ι := ι) (p := p) (q := q) r‖ ≤ 1 :=
  (norm_holderL_le (p := p) (q := q) r (fun _ : ι ↦ ContinuousLinearMap.mul 𝕜 R) (K := 1) fun _ ↦
    by simpa using ContinuousLinearMap.opNorm_mul_le 𝕜 R).trans_eq NNReal.coe_one

/-- Pointwise norm bound `‖lp.mulL 𝕜 R r a b‖ ≤ ‖a‖ * ‖b‖`. -/
theorem norm_mulL_apply_apply_le (r : ℝ≥0∞) [Fact (1 ≤ r)] [p.HolderTriple q r]
    (a : lp (fun _ : ι ↦ R) p) (b : lp (fun _ : ι ↦ R) q) :
    ‖mulL 𝕜 R r a b‖ ≤ ‖a‖ * ‖b‖ := by
  simpa using (mulL 𝕜 R r).le_of_opNorm₂_le_of_le (norm_mulL_le 𝕜 R r) le_rfl le_rfl

end lp
