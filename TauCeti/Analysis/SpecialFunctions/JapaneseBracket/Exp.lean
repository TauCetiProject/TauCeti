/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.Calculus.Deriv.Inv
import TauCeti.Analysis.Real.Sqrt

/-!
# Smooth radial exponential weights

For `b > 0`, the weight `exp(c √(b + ‖z‖²))` is smooth on any real inner product space. The
norm of its derivative is `|c| ‖z‖ / √(b + ‖z‖²)` times the weight, so it is bounded by `|c|`
times the weight, and by an arbitrarily small multiple of the weight on a fixed ball once `b` is
large. The usual choice is `b = 1`, and changing `b` changes the weight by at most a constant
factor. The truncated weights `W / (1 + ε W)`, `ε > 0`, are smooth, lie between `0` and
`min W (1 / ε)`, and have logarithmic gradient at most that of `W`.

The weights `exp(c √(b + ‖z‖²))` and `exp(-c √(b + ‖z‖²))` are reciprocal, so either can be moved
across the `L²` pairing: `|⟪e, f⟫| ≤ ‖exp(-c ρ) e‖₂ ‖exp(c ρ) f‖₂`
(`abs_inner_le_of_memLp_exp_mul_smul`). So if `‖u‖₂² ≤ |⟪e, A⟫|`, where the weight `exp(-c ρ)`
costs at most `q ‖u‖₂` on `e` and the weight `exp(c ρ)` at most `a` on `u`, then
`‖exp(c ρ) u‖₂ ≤ a q ‖exp(c ρ) A‖₂` (`eLpNorm_exp_mul_smul_le_of_sq_le_abs_inner`).
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

omit [InnerProductSpace ℝ E] in
/-- The factor `‖z‖ / √(b + ‖z‖²)` in the logarithmic gradient is at most `1`. -/
theorem norm_div_sqrt_add_norm_sq_le_one (hb : 0 ≤ b) (z : E) : ‖z‖ / √(b + ‖z‖ ^ 2) ≤ 1 := by
  simpa only [abs_div, abs_norm, abs_of_nonneg (Real.sqrt_nonneg _), add_comm] using
    Real.abs_div_sqrt_sq_add_le_one hb ‖z‖

/-- The logarithmic gradient of the regularized radial exponential weight has norm
at most `|c|`, with no restriction on the sign of `c`. -/
theorem norm_fderiv_exp_mul_sqrt_add_norm_sq_le (c : ℝ) (hb : 0 < b) (z : E) :
    ‖fderiv ℝ (fun t : E ↦ Real.exp (c * √(b + ‖t‖ ^ 2))) z‖ ≤
      |c| * Real.exp (c * √(b + ‖z‖ ^ 2)) := by
  rw [norm_fderiv_exp_mul_sqrt_add_norm_sq c hb]
  exact mul_le_of_le_one_right (by positivity) (norm_div_sqrt_add_norm_sq_le_one hb.le z)

/-- A nonnegative weight whose logarithmic gradient is at most that of the radial exponential
weight, `|c| ‖z‖ / √(b + ‖z‖²)`, satisfies `‖dV‖² ≤ c² V²`. -/
theorem norm_fderiv_sq_le_of_norm_fderiv_le {V : E → ℝ} (c : ℝ) (hb : 0 ≤ b) {z : E}
    (hV : 0 ≤ V z) (hdV : ‖fderiv ℝ V z‖ ≤ |c| * (‖z‖ / √(b + ‖z‖ ^ 2)) * V z) :
    ‖fderiv ℝ V z‖ ^ 2 ≤ c ^ 2 * V z ^ 2 := by
  have h := hdV.trans (mul_le_mul_of_nonneg_right
    (mul_le_of_le_one_right (abs_nonneg c) (norm_div_sqrt_add_norm_sq_le_one hb z)) hV)
  simpa only [mul_pow, sq_abs] using pow_le_pow_left₀ (norm_nonneg _) h 2

/-- The truncated radial exponential weight `W / (1 + ε W)`, `W = exp(c √(b + ‖z‖²))`, is smooth
for `ε ≥ 0`, of every order. -/
theorem contDiff_exp_div_one_add_mul_exp (c : ℝ) (hb : 0 < b) {ε : ℝ} (hε : 0 ≤ ε)
    {n : WithTop ℕ∞} :
    ContDiff ℝ n (fun z : E ↦ Real.exp (c * √(b + ‖z‖ ^ 2)) /
      (1 + ε * Real.exp (c * √(b + ‖z‖ ^ 2)))) :=
  have hW := contDiff_exp_mul_sqrt_add_norm_sq (E := E) (n := n) c hb
  hW.div (contDiff_const.add (contDiff_const.mul hW)) fun _ ↦ by positivity

omit [InnerProductSpace ℝ E] in
/-- The truncated radial exponential weight `W / (1 + ε W)`, `ε ≥ 0`, is nonnegative. -/
theorem exp_div_one_add_mul_exp_nonneg (c : ℝ) {ε : ℝ} (hε : 0 ≤ ε) (z : E) :
    0 ≤ Real.exp (c * √(b + ‖z‖ ^ 2)) / (1 + ε * Real.exp (c * √(b + ‖z‖ ^ 2))) := by
  positivity

omit [InnerProductSpace ℝ E] in
/-- The truncated radial exponential weight `W / (1 + ε W)`, `ε ≥ 0`, is at most `W`. -/
theorem exp_div_one_add_mul_exp_le_exp (c : ℝ) {ε : ℝ} (hε : 0 ≤ ε) (z : E) :
    Real.exp (c * √(b + ‖z‖ ^ 2)) / (1 + ε * Real.exp (c * √(b + ‖z‖ ^ 2))) ≤
      Real.exp (c * √(b + ‖z‖ ^ 2)) :=
  div_le_self (Real.exp_pos _).le (le_add_of_nonneg_right (by positivity))

omit [InnerProductSpace ℝ E] in
/-- The truncated radial exponential weight `W / (1 + ε W)`, `ε > 0`, is bounded by `1 / ε`. -/
theorem exp_div_one_add_mul_exp_le_one_div (c : ℝ) {ε : ℝ} (hε : 0 < ε) (z : E) :
    Real.exp (c * √(b + ‖z‖ ^ 2)) / (1 + ε * Real.exp (c * √(b + ‖z‖ ^ 2))) ≤ 1 / ε := by
  rw [div_le_div_iff₀ (by positivity) hε]
  linarith [mul_comm (Real.exp (c * √(b + ‖z‖ ^ 2))) ε]

/-- The truncated radial exponential weight `W / (1 + ε W)`, `W = exp(c √(b + ‖z‖²))`, `ε ≥ 0`,
has logarithmic gradient at most that of `W`, namely `|c| ‖z‖ / √(b + ‖z‖²)`. -/
theorem norm_fderiv_exp_div_one_add_mul_exp_le (c : ℝ) (hb : 0 < b) {ε : ℝ} (hε : 0 ≤ ε)
    (z : E) :
    ‖fderiv ℝ (fun t : E ↦ Real.exp (c * √(b + ‖t‖ ^ 2)) /
        (1 + ε * Real.exp (c * √(b + ‖t‖ ^ 2)))) z‖ ≤
      |c| * (‖z‖ / √(b + ‖z‖ ^ 2)) *
        (Real.exp (c * √(b + ‖z‖ ^ 2)) / (1 + ε * Real.exp (c * √(b + ‖z‖ ^ 2)))) := by
  set W : E → ℝ := fun t ↦ Real.exp (c * √(b + ‖t‖ ^ 2))
  have hW : 0 < W z := Real.exp_pos _
  have hd : 0 < 1 + ε * W z := by positivity
  -- `W / (1 + ε W)` is `W` composed with `s ↦ s / (1 + ε s)`, of derivative `1 / (1 + ε s)²`.
  have hg : HasDerivAt (fun s : ℝ ↦ s / (1 + ε * s)) (1 / (1 + ε * W z) ^ 2) (W z) := by
    have h := (hasDerivAt_id' (W z)).div (((hasDerivAt_id' (W z)).const_mul ε).const_add 1)
      hd.ne'
    convert h using 1
    field_simp
    ring
  have hWd : HasFDerivAt W (fderiv ℝ W z) z :=
    ((contDiff_exp_mul_sqrt_add_norm_sq (n := 1) c hb).differentiable (by simp) z).hasFDerivAt
  have hVd : HasFDerivAt (fun t ↦ W t / (1 + ε * W t))
      ((1 / (1 + ε * W z) ^ 2) • fderiv ℝ W z) z := hg.comp_hasFDerivAt z hWd
  rw [hVd.fderiv, norm_smul, Real.norm_of_nonneg (by positivity),
    norm_fderiv_exp_mul_sqrt_add_norm_sq c hb]
  set d := 1 + ε * W z
  rw [show 1 / d ^ 2 * (|c| * W z * (‖z‖ / √(b + ‖z‖ ^ 2))) =
    |c| * (‖z‖ / √(b + ‖z‖ ^ 2)) * (W z / d) * (1 / d) by field_simp]
  refine mul_le_of_le_one_right (by positivity) ?_
  rw [div_le_one hd]
  nlinarith [mul_nonneg hε hW.le]

omit [InnerProductSpace ℝ E] in
/-- Changing the regularization parameter changes the radial exponential weight by at most the
factor `exp(|c| √|s - t|)`, uniformly in `z`, since the square root is `1/2`-Hölder. -/
theorem exp_mul_sqrt_add_norm_sq_le (c s t : ℝ) (z : E) :
    Real.exp (c * √(s + ‖z‖ ^ 2)) ≤
      Real.exp (|c| * √|s - t|) * Real.exp (c * √(t + ‖z‖ ^ 2)) := by
  rw [← Real.exp_add, Real.exp_le_exp]
  have hd := Real.abs_sqrt_sub_sqrt_le (s + ‖z‖ ^ 2) (t + ‖z‖ ^ 2)
  rw [add_sub_add_right_eq_sub] at hd
  have h := (abs_le.mp ((abs_mul c _).symm ▸
    mul_le_mul_of_nonneg_left hd (abs_nonneg c))).2
  linarith [mul_sub c (√(s + ‖z‖ ^ 2)) (√(t + ‖z‖ ^ 2))]

omit [InnerProductSpace ℝ E] in
/-- The squared form of `exp_mul_sqrt_add_norm_sq_le`, comparing the squared weights that enter
weighted `L²` norms. -/
theorem sq_exp_mul_sqrt_add_norm_sq_le (c s t : ℝ) (z : E) :
    Real.exp (c * √(s + ‖z‖ ^ 2)) ^ 2 ≤
      Real.exp (|c| * √|s - t|) ^ 2 * Real.exp (c * √(t + ‖z‖ ^ 2)) ^ 2 := by
  rw [← mul_pow]
  exact pow_le_pow_left₀ (Real.exp_pos _).le (exp_mul_sqrt_add_norm_sq_le c s t z) 2

section L2

open MeasureTheory
open scoped RealInnerProductSpace NNReal

variable {X F : Type*} [Norm X] [MeasurableSpace X] {μ : Measure X}
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- **Moving an exponential weight across the `L²` pairing.** Let `ρ(z) = √(b + ‖z‖²)` and let
`e`, `f` be `L²` functions such that `exp(-c ρ) e` and `exp(c ρ) f` are square integrable. Then
the `L²` pairing satisfies `|⟪e, f⟫| ≤ ‖exp(-c ρ) e‖₂ ‖exp(c ρ) f‖₂`. -/
theorem abs_inner_le_of_memLp_exp_mul_smul {c : ℝ} {e f : Lp F 2 μ}
    (he : MemLp (fun z ↦ Real.exp (-c * √(b + ‖z‖ ^ 2)) • e z) 2 μ)
    (hf : MemLp (fun z ↦ Real.exp (c * √(b + ‖z‖ ^ 2)) • f z) 2 μ) :
    |⟪e, f⟫| ≤ (eLpNorm (fun z ↦ Real.exp (-c * √(b + ‖z‖ ^ 2)) • e z) 2 μ).toReal *
      (eLpNorm (fun z ↦ Real.exp (c * √(b + ‖z‖ ^ 2)) • f z) 2 μ).toReal := by
  -- Moving the weight across the pairing: `⟪e, f⟫ = ⟪exp(-c ρ) e, exp(c ρ) f⟫` in `L²`.
  have hinner : ⟪e, f⟫ = ⟪he.toLp _, hf.toLp _⟫ := by
    rw [L2.inner_def, L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [he.coeFn_toLp, hf.coeFn_toLp] with z hez hfz
    simp only [hez, hfz, real_inner_smul_left, real_inner_smul_right, ← mul_assoc, ← Real.exp_add,
      ← add_mul, add_neg_cancel, zero_mul, Real.exp_zero, one_mul]
  rw [hinner, ← Lp.norm_toLp _ he, ← Lp.norm_toLp _ hf]
  exact abs_real_inner_le_norm _ _

/-- **A weighted bound from a pairing inequality.** Let `ρ(z) = √(b + ‖z‖²)` and let `u`, `e`, `A`
be `L²` functions with `‖u‖₂² ≤ |⟪e, A⟫|`. Suppose that the weight `exp(c ρ)` costs at most `a` on
`u`, that `exp(-c ρ) e` is square integrable with norm at most `q ‖u‖₂`, and that `exp(c ρ) A` is
square integrable. Then `‖exp(c ρ) u‖₂ ≤ a q ‖exp(c ρ) A‖₂`.

Typically `u` lies in a finite-dimensional space of decaying functions, on which every weight
costs a bounded factor, and the pairing inequality comes from an orthogonality relation. -/
theorem eLpNorm_exp_mul_smul_le_of_sq_le_abs_inner {c : ℝ} {u e A : Lp F 2 μ} {a q : ℝ≥0}
    (hu : eLpNorm (fun z ↦ Real.exp (c * √(b + ‖z‖ ^ 2)) • u z) 2 μ ≤ a * eLpNorm u 2 μ)
    (he : MemLp (fun z ↦ Real.exp (-c * √(b + ‖z‖ ^ 2)) • e z) 2 μ)
    (hqe : eLpNorm (fun z ↦ Real.exp (-c * √(b + ‖z‖ ^ 2)) • e z) 2 μ ≤ q * eLpNorm u 2 μ)
    (hA : MemLp (fun z ↦ Real.exp (c * √(b + ‖z‖ ^ 2)) • A z) 2 μ)
    (hinner : ‖u‖ ^ 2 ≤ |⟪e, A⟫|) :
    eLpNorm (fun z ↦ Real.exp (c * √(b + ‖z‖ ^ 2)) • u z) 2 μ ≤
      (a * q : ℝ≥0) * eLpNorm (fun z ↦ Real.exp (c * √(b + ‖z‖ ^ 2)) • A z) 2 μ := by
  set N := eLpNorm (fun z ↦ Real.exp (c * √(b + ‖z‖ ^ 2)) • A z) 2 μ
  have hq : (eLpNorm (fun z ↦ Real.exp (-c * √(b + ‖z‖ ^ 2)) • e z) 2 μ).toReal ≤ q * ‖u‖ := by
    simpa [Lp.norm_def, ENNReal.toReal_mul] using ENNReal.toReal_mono
      (ENNReal.mul_ne_top ENNReal.coe_ne_top (Lp.eLpNorm_ne_top u)) hqe
  -- From `‖u‖₂² ≤ ‖exp(-c ρ) e‖₂ ‖exp(c ρ) A‖₂ ≤ q ‖u‖₂ N`, `‖u‖₂ ≤ q N`.
  have hP : ‖u‖ ≤ q * N.toReal := by
    have h₁ : ‖u‖ ^ 2 ≤ q * ‖u‖ * N.toReal := hinner.trans
      ((abs_inner_le_of_memLp_exp_mul_smul he hA).trans
        (mul_le_mul_of_nonneg_right hq ENNReal.toReal_nonneg))
    rcases (norm_nonneg u).eq_or_lt with h | h
    · rw [← h]
      positivity
    · nlinarith
  calc _ ≤ a * eLpNorm u 2 μ := hu
    _ = a * ENNReal.ofReal ‖u‖ := by rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top u)]
    _ ≤ a * ENNReal.ofReal (q * N.toReal) := by gcongr
    _ = (a * q : ℝ≥0) * N := by
      rw [ENNReal.ofReal_mul q.coe_nonneg, ENNReal.ofReal_coe_nnreal,
        ENNReal.ofReal_toReal hA.eLpNorm_ne_top, ENNReal.coe_mul, mul_assoc]

end L2

end TauCeti
