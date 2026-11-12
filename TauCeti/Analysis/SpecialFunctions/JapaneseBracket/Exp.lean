/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Smooth radial exponential weights

For `b > 0`, the weight `exp(c √(b + ‖z‖²))` is smooth on any real inner product space. The
norm of its derivative is `|c| ‖z‖ / √(b + ‖z‖²)` times the weight, so it is bounded by `|c|`
times the weight, and by an arbitrarily small multiple of the weight on a fixed ball once `b` is
large. The usual choice is `b = 1`.

For `ε > 0`, the bounded weight `E / (1 + ε E)` with `E(z) = exp(c √(1 + ‖z‖²))`
(`TauCeti.boundedExpWeight`) is smooth, bounded by `E` and by `ε⁻¹`, still has logarithmic gradient
at most `|c|`, and increases to `E` as `ε` decreases to `0`. Weighted energy estimates use it to
approximate the unbounded weight `E` from below.
-/

public section

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {b : ℝ}

/-- The regularized radial exponential weight is smooth, of every order. -/
theorem contDiff_exp_mul_sqrt_add_norm_sq (c : ℝ) (hb : 0 < b) {n : WithTop ℕ∞} :
    ContDiff ℝ n (fun z : E ↦ Real.exp (c * √(b + ‖z‖ ^ 2))) := by
  have hq : ContDiff ℝ n (fun z : E ↦ b + ‖z‖ ^ 2) :=
    contDiff_const.add (contDiff_id.norm_sq ℝ)
  exact (contDiff_const.mul (hq.sqrt (fun z ↦ by positivity))).exp

/-- The derivative of the regularized radial exponential weight, as a real functional. -/
theorem fderiv_exp_mul_sqrt_add_norm_sq (c : ℝ) (hb : 0 < b) (z : E) :
    fderiv ℝ (fun t : E ↦ Real.exp (c * √(b + ‖t‖ ^ 2))) z =
      (Real.exp (c * √(b + ‖z‖ ^ 2)) * c / √(b + ‖z‖ ^ 2)) • innerSL ℝ z := by
  have hp : 0 < b + ‖z‖ ^ 2 := by positivity
  have hd :=
    ((((hasStrictFDerivAt_norm_sq z).hasFDerivAt.const_add b).sqrt hp.ne').const_mul c).exp
  rw [hd.fderiv]
  ext v
  simp only [smul_apply, smul_eq_mul, innerSL_apply_apply]
  field_simp
  ring

/-- The exact norm of the derivative of the regularized radial exponential weight: the
logarithmic gradient has norm `|c| ‖z‖ / √(b + ‖z‖²)`. -/
theorem norm_fderiv_exp_mul_sqrt_add_norm_sq (c : ℝ) (hb : 0 < b) (z : E) :
    ‖fderiv ℝ (fun t : E ↦ Real.exp (c * √(b + ‖t‖ ^ 2))) z‖ =
      |c| * Real.exp (c * √(b + ‖z‖ ^ 2)) * (‖z‖ / √(b + ‖z‖ ^ 2)) := by
  rw [fderiv_exp_mul_sqrt_add_norm_sq c hb, norm_smul, innerSL_apply_norm, Real.norm_eq_abs,
    abs_div, abs_mul, abs_of_pos (Real.exp_pos _),
    abs_of_nonneg (Real.sqrt_nonneg _)]
  ring

/-- The logarithmic gradient of the regularized radial exponential weight has norm
at most `|c|`, with no restriction on the sign of `c`. -/
theorem norm_fderiv_exp_mul_sqrt_add_norm_sq_le (c : ℝ) (hb : 0 < b) (z : E) :
    ‖fderiv ℝ (fun t : E ↦ Real.exp (c * √(b + ‖t‖ ^ 2))) z‖ ≤
      |c| * Real.exp (c * √(b + ‖z‖ ^ 2)) := by
  have hp : 0 < b + ‖z‖ ^ 2 := by positivity
  have hq : ‖z‖ / √(b + ‖z‖ ^ 2) ≤ 1 := by
    apply (div_le_one (Real.sqrt_pos.2 hp)).2
    exact (Real.le_sqrt (norm_nonneg z) hp.le).2 (by linarith)
  rw [norm_fderiv_exp_mul_sqrt_add_norm_sq c hb]
  exact mul_le_of_le_one_right (by positivity) hq

section Bounded

variable {F : Type*} [NormedAddCommGroup F]

/-- The bounded approximation `E / (1 + ε E)` of the radial exponential weight
`E(z) = exp(c √(1 + ‖z‖²))`. For `ε > 0` it is bounded by `ε⁻¹`, and it increases to `E` as `ε`
decreases to `0`. -/
noncomputable def boundedExpWeight (c ε : ℝ) (z : F) : ℝ :=
  Real.exp (c * √(1 + ‖z‖ ^ 2)) / (1 + ε * Real.exp (c * √(1 + ‖z‖ ^ 2)))

/-- The defining formula `E / (1 + ε E)` of the bounded weight. -/
theorem boundedExpWeight_def (c ε : ℝ) (z : F) :
    boundedExpWeight c ε z =
      Real.exp (c * √(1 + ‖z‖ ^ 2)) / (1 + ε * Real.exp (c * √(1 + ‖z‖ ^ 2))) :=
  (rfl)

/-- The bounded weight is the composition of `s ↦ s / (1 + ε s)` with the exponential weight. -/
private theorem boundedExpWeight_eq_comp (c ε : ℝ) :
    boundedExpWeight (F := F) c ε =
      (fun s ↦ s / (1 + ε * s)) ∘ fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) :=
  rfl

private theorem one_le_one_add_mul_exp {c ε : ℝ} (hε : 0 ≤ ε) (z : F) :
    1 ≤ 1 + ε * Real.exp (c * √(1 + ‖z‖ ^ 2)) := by
  have := Real.exp_pos (c * √(1 + ‖z‖ ^ 2))
  nlinarith

theorem boundedExpWeight_nonneg {c ε : ℝ} (hε : 0 ≤ ε) (z : F) : 0 ≤ boundedExpWeight c ε z :=
  div_nonneg (Real.exp_pos _).le (zero_le_one.trans (one_le_one_add_mul_exp hε z))

/-- The bounded weight lies below the exponential weight. -/
theorem boundedExpWeight_le {c ε : ℝ} (hε : 0 ≤ ε) (z : F) :
    boundedExpWeight c ε z ≤ Real.exp (c * √(1 + ‖z‖ ^ 2)) :=
  div_le_self (Real.exp_pos _).le (one_le_one_add_mul_exp hε z)

/-- For `ε > 0` the bounded weight is at most `ε⁻¹`. -/
theorem boundedExpWeight_le_inv {c ε : ℝ} (hε : 0 < ε) (z : F) : boundedExpWeight c ε z ≤ ε⁻¹ := by
  rw [boundedExpWeight_def, div_le_iff₀ (zero_lt_one.trans_le (one_le_one_add_mul_exp hε.le z)),
    inv_mul_eq_div, le_div_iff₀ hε]
  nlinarith [Real.exp_pos (c * √(1 + ‖z‖ ^ 2))]

/-- As `ε → 0`, the bounded weight converges to the exponential weight. -/
theorem tendsto_boundedExpWeight (c : ℝ) (z : F) :
    Filter.Tendsto (fun ε ↦ boundedExpWeight c ε z) (nhds 0)
      (nhds (Real.exp (c * √(1 + ‖z‖ ^ 2)))) := by
  have h : Filter.Tendsto (fun ε : ℝ ↦ 1 + ε * Real.exp (c * √(1 + ‖z‖ ^ 2))) (nhds 0)
      (nhds 1) := by
    simpa using ((continuous_id.mul continuous_const).const_add 1).tendsto' 0 _ (by simp)
  have h' := (tendsto_const_nhds (x := Real.exp (c * √(1 + ‖z‖ ^ 2)))).div h one_ne_zero
  rw [div_one] at h'
  exact h'

end Bounded

section InnerProductSpace

variable {c ε : ℝ} (hε : 0 ≤ ε)
include hε

/-- The bounded weight is smooth, of every order. -/
theorem contDiff_boundedExpWeight {n : WithTop ℕ∞} : ContDiff ℝ n (boundedExpWeight (F := E) c ε) :=
  (contDiff_exp_mul_sqrt_add_norm_sq c one_pos).div
    (contDiff_const.add (contDiff_const.mul (contDiff_exp_mul_sqrt_add_norm_sq c one_pos)))
    fun z ↦ (zero_lt_one.trans_le (one_le_one_add_mul_exp hε z)).ne'

/-- The logarithmic gradient of the bounded weight has norm at most `|c|`, as for the
exponential weight itself. -/
theorem norm_fderiv_boundedExpWeight_le (z : E) :
    ‖fderiv ℝ (boundedExpWeight c ε) z‖ ≤ |c| * boundedExpWeight c ε z := by
  set W := fun t : E ↦ Real.exp (c * √(1 + ‖t‖ ^ 2))
  have h1 := one_le_one_add_mul_exp (c := c) hε z
  have hg : HasDerivAt (fun s ↦ s / (1 + ε * s)) (1 / (1 + ε * W z) ^ 2) (W z) := by
    have h := (hasDerivAt_id' (W z)).div (((hasDerivAt_id' (W z)).const_mul ε).const_add 1)
      (zero_lt_one.trans_le h1).ne'
    rwa [show 1 * (1 + ε * W z) - W z * (ε * 1) = 1 by ring] at h
  have hW : HasFDerivAt W (fderiv ℝ W z) z :=
    ((contDiff_exp_mul_sqrt_add_norm_sq (n := 1) c one_pos).differentiable one_ne_zero
      z).hasFDerivAt
  rw [boundedExpWeight_eq_comp, (hg.comp_hasFDerivAt z hW).fderiv, norm_smul,
    Real.norm_of_nonneg (r := 1 / (1 + ε * W z) ^ 2) (by positivity)]
  have hd := norm_fderiv_exp_mul_sqrt_add_norm_sq_le c one_pos z
  have hWz : 0 < W z := Real.exp_pos _
  calc 1 / (1 + ε * W z) ^ 2 * ‖fderiv ℝ W z‖ ≤ 1 / (1 + ε * W z) ^ 2 * (|c| * W z) :=
        mul_le_mul_of_nonneg_left hd (by positivity)
    _ ≤ |c| * (W z / (1 + ε * W z)) := by
        rw [div_eq_mul_inv, div_eq_mul_inv, one_mul]
        have hi : ((1 + ε * W z) ^ 2)⁻¹ ≤ (1 + ε * W z)⁻¹ :=
          inv_anti₀ (by positivity) (by nlinarith)
        nlinarith [abs_nonneg c, mul_le_mul_of_nonneg_left hi (mul_nonneg (abs_nonneg c) hWz.le)]

end InnerProductSpace

end TauCeti
