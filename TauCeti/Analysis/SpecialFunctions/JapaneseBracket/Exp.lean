/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.Calculus.Deriv.Inv
import TauCeti.Analysis.Real.Sqrt
import TauCeti.MeasureTheory.Function.Lp.Adjoint

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
`‖exp(c ρ) u‖₂ ≤ a q ‖exp(c ρ) A‖₂` (`eLpNorm_exp_mul_smul_le_of_sq_le_abs_inner`). More generally,
if `‖u‖₂² ≤ ∑ᵢ |⟪eᵢ, Aᵢ⟫|` with `‖exp(-c ρ) eᵢ‖₂ ≤ qᵢ ‖u‖₂`, then
`‖exp(c ρ) u‖₂ ≤ a ∑ᵢ qᵢ ‖exp(c ρ) Aᵢ‖₂` (`eLpNorm_exp_mul_smul_le_of_sq_le_sum_abs_inner`). By the
same duality, an operator on `L²` that preserves decay at the rate `-c` has an adjoint that
preserves decay at the rate `c`, with the same constant
(`ContinuousLinearMap.eLpNorm_exp_mul_smul_adjoint_apply_le`).
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

omit [InnerProductSpace ℝ E] in
/-- The regularized radial exponential weight is continuous. -/
theorem continuous_exp_mul_sqrt_add_norm_sq (c : ℝ) :
    Continuous fun z : E ↦ Real.exp (c * √(b + ‖z‖ ^ 2)) :=
  (continuous_const.mul (continuous_const.add (continuous_norm.pow 2)).sqrt).rexp

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
open scoped RealInnerProductSpace NNReal ENNReal

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

/-- **Moving an exponential weight across the `L²` pairing, in `ℝ≥0∞`.** Let `ρ(z) = √(b + ‖z‖²)`.
For `L²` functions `e` and `f`, `|⟪e, f⟫| ≤ ‖exp(-c ρ) e‖₂ ‖exp(c ρ) f‖₂`, where the right side may
be infinite. -/
theorem ofReal_abs_inner_le_eLpNorm_exp_mul_smul_mul (c : ℝ) (e f : Lp F 2 μ) :
    ENNReal.ofReal |⟪e, f⟫| ≤ eLpNorm (fun z ↦ Real.exp (-c * √(b + ‖z‖ ^ 2)) • e z) 2 μ *
      eLpNorm (fun z ↦ Real.exp (c * √(b + ‖z‖ ^ 2)) • f z) 2 μ := by
  set Ne := eLpNorm (fun z ↦ Real.exp (-c * √(b + ‖z‖ ^ 2)) • e z) 2 μ
  set Nf := eLpNorm (fun z ↦ Real.exp (c * √(b + ‖z‖ ^ 2)) • f z) 2 μ
  -- A weighted norm vanishes only for the zero function, since the weight is positive.
  have hzero : ∀ (c' : ℝ) (g : Lp F 2 μ),
      eLpNorm (fun z ↦ Real.exp (c' * √(b + ‖z‖ ^ 2)) • g z) 2 μ = 0 → g = 0 := fun c' g hg ↦
    Lp.eq_zero_iff_ae_eq_zero.2 (((eLpNorm_eq_zero_iff two_ne_zero).1 hg).mono
      fun z hz ↦ (smul_eq_zero.1 hz).resolve_left (Real.exp_pos _).ne')
  rcases eq_or_ne Ne 0 with he | he
  · rw [hzero _ e he, inner_zero_left, abs_zero, ENNReal.ofReal_zero]
    exact zero_le
  rcases eq_or_ne Nf 0 with hf | hf
  · rw [hzero _ f hf, inner_zero_right, abs_zero, ENNReal.ofReal_zero]
    exact zero_le
  rcases eq_or_ne Ne ⊤ with he' | he'
  · rw [he', ENNReal.top_mul hf]
    exact le_top
  rcases eq_or_ne Nf ⊤ with hf' | hf'
  · rw [hf', ENNReal.mul_top he]
    exact le_top
  calc ENNReal.ofReal |⟪e, f⟫| ≤ ENNReal.ofReal (Ne.toReal * Nf.toReal) :=
        ENNReal.ofReal_le_ofReal (abs_inner_le_of_memLp_exp_mul_smul
          (memLp_iff.2 he'.lt_top) (memLp_iff.2 hf'.lt_top))
    _ = Ne * Nf := by
      rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal he',
        ENNReal.ofReal_toReal hf']

/-- **A weighted bound from several pairing inequalities.** Let `ρ(z) = √(b + ‖z‖²)` and let `u`,
`e i`, `A i` be `L²` functions with `‖u‖₂² ≤ ∑ i ∈ s, |⟪e i, A i⟫|`. Suppose that the weight
`exp(c ρ)` costs at most `a` on `u` and that `‖exp(-c ρ) e i‖₂ ≤ q i ‖u‖₂` for every `i ∈ s`. Then
`‖exp(c ρ) u‖₂ ≤ a ∑ i ∈ s, q i ‖exp(c ρ) A i‖₂`, where either side may be infinite. -/
theorem eLpNorm_exp_mul_smul_le_of_sq_le_sum_abs_inner {ι : Type*} {s : Finset ι} {c : ℝ}
    {u : Lp F 2 μ} {e A : ι → Lp F 2 μ} {a : ℝ≥0} {q : ι → ℝ≥0}
    (hu : eLpNorm (fun z ↦ Real.exp (c * √(b + ‖z‖ ^ 2)) • u z) 2 μ ≤ a * eLpNorm u 2 μ)
    (hqe : ∀ i ∈ s, eLpNorm (fun z ↦ Real.exp (-c * √(b + ‖z‖ ^ 2)) • e i z) 2 μ ≤
      q i * eLpNorm u 2 μ)
    (hinner : ‖u‖ ^ 2 ≤ ∑ i ∈ s, |⟪e i, A i⟫|) :
    eLpNorm (fun z ↦ Real.exp (c * √(b + ‖z‖ ^ 2)) • u z) 2 μ ≤
      a * ∑ i ∈ s, q i * eLpNorm (fun z ↦ Real.exp (c * √(b + ‖z‖ ^ 2)) • A i z) 2 μ := by
  set S := ∑ i ∈ s, (q i : ℝ≥0∞) * eLpNorm (fun z ↦ Real.exp (c * √(b + ‖z‖ ^ 2)) • A i z) 2 μ
  set U := eLpNorm u 2 μ
  have hU : U = ENNReal.ofReal ‖u‖ := by
    rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top u)]
  -- From `‖u‖₂² ≤ ∑ ‖exp(-c ρ) e i‖₂ ‖exp(c ρ) A i‖₂ ≤ ‖u‖₂ S`, `‖u‖₂ ≤ S`.
  have h₁ : U * U ≤ U * S := by
    calc U * U = ENNReal.ofReal (‖u‖ ^ 2) := by
          rw [hU, sq, ENNReal.ofReal_mul (norm_nonneg u)]
      _ ≤ ENNReal.ofReal (∑ i ∈ s, |⟪e i, A i⟫|) := ENNReal.ofReal_le_ofReal hinner
      _ = ∑ i ∈ s, ENNReal.ofReal |⟪e i, A i⟫| :=
          ENNReal.ofReal_sum_of_nonneg (f := fun i ↦ |⟪e i, A i⟫|) fun i _ ↦ abs_nonneg _
      _ ≤ ∑ i ∈ s, q i * U * eLpNorm (fun z ↦ Real.exp (c * √(b + ‖z‖ ^ 2)) • A i z) 2 μ :=
          Finset.sum_le_sum fun i hi ↦
            (ofReal_abs_inner_le_eLpNorm_exp_mul_smul_mul (b := b) c (e i) (A i)).trans
              (by gcongr; exact hqe i hi)
      _ = U * S := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ ↦ by ring
  have h₂ : U ≤ S := by
    rcases eq_or_ne U 0 with h | h
    · rw [h]
      exact zero_le
    · exact (ENNReal.mul_le_mul_iff_right h (Lp.eLpNorm_ne_top u)).1 h₁
  exact hu.trans (by gcongr)

/-- **A weighted bound from a pairing inequality.** Let `ρ(z) = √(b + ‖z‖²)` and let `u`, `e`, `A`
be `L²` functions with `‖u‖₂² ≤ |⟪e, A⟫|`. Suppose that the weight `exp(c ρ)` costs at most `a` on
`u` and that `‖exp(-c ρ) e‖₂ ≤ q ‖u‖₂`. Then `‖exp(c ρ) u‖₂ ≤ a q ‖exp(c ρ) A‖₂`, where either
side may be infinite.

Typically `u` lies in a finite-dimensional space of decaying functions, on which every weight
costs a bounded factor, and the pairing inequality comes from an orthogonality relation. -/
theorem eLpNorm_exp_mul_smul_le_of_sq_le_abs_inner {c : ℝ} {u e A : Lp F 2 μ} {a q : ℝ≥0}
    (hu : eLpNorm (fun z ↦ Real.exp (c * √(b + ‖z‖ ^ 2)) • u z) 2 μ ≤ a * eLpNorm u 2 μ)
    (hqe : eLpNorm (fun z ↦ Real.exp (-c * √(b + ‖z‖ ^ 2)) • e z) 2 μ ≤ q * eLpNorm u 2 μ)
    (hinner : ‖u‖ ^ 2 ≤ |⟪e, A⟫|) :
    eLpNorm (fun z ↦ Real.exp (c * √(b + ‖z‖ ^ 2)) • u z) 2 μ ≤
      (a * q : ℝ≥0) * eLpNorm (fun z ↦ Real.exp (c * √(b + ‖z‖ ^ 2)) • A z) 2 μ := by
  simpa [mul_assoc] using eLpNorm_exp_mul_smul_le_of_sq_le_sum_abs_inner (s := Finset.univ)
    (e := fun _ : Unit ↦ e) (A := fun _ ↦ A) (q := fun _ ↦ q) hu (fun _ _ ↦ hqe)
    (by simpa using hinner)

end L2

end TauCeti

namespace ContinuousLinearMap

open MeasureTheory TauCeti
open scoped ENNReal

variable {b : ℝ} {X F : Type*} [NormedAddCommGroup X] [MeasurableSpace X]
  [OpensMeasurableSpace X] {μ : Measure X} [SigmaFinite μ]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-- **Exponentially weighted estimates pass to the adjoint.** Let `ρ(z) = √(b + ‖z‖²)` and let
`T` be a bounded operator on `L²(μ; F)` with `‖exp(-c ρ) T f‖₂ ≤ C ‖exp(-c ρ) f‖₂` for every `f`.
Then its Hilbert space adjoint satisfies `‖exp(c ρ) T† g‖₂ ≤ C ‖exp(c ρ) g‖₂` for every `g`, where
either side may be infinite. -/
theorem eLpNorm_exp_mul_smul_adjoint_apply_le {c : ℝ} {C : ℝ≥0∞} (T : Lp F 2 μ →L[ℝ] Lp F 2 μ)
    (hT : ∀ f, eLpNorm (fun z ↦ Real.exp (-c * √(b + ‖z‖ ^ 2)) • T f z) 2 μ ≤
      C * eLpNorm (fun z ↦ Real.exp (-c * √(b + ‖z‖ ^ 2)) • f z) 2 μ)
    (g : Lp F 2 μ) :
    eLpNorm (fun z ↦ Real.exp (c * √(b + ‖z‖ ^ 2)) • ContinuousLinearMap.adjoint T g z) 2 μ ≤
      C * eLpNorm (fun z ↦ Real.exp (c * √(b + ‖z‖ ^ 2)) • g z) 2 μ := by
  have h := eLpNorm_smul_le_of_eLpNorm_smul_adjoint_le
    (ContinuousLinearMap.adjoint T) (p := 2) (p' := 2) (q := 2) (q' := 2)
    (ae_of_all _ fun z ↦ (Real.exp_pos (c * √(b + ‖z‖ ^ 2))).ne')
    (continuous_exp_mul_sqrt_add_norm_sq (b := b) c).aestronglyMeasurable (C := C) (fun f ↦ ?_) g
  · simpa using h
  · -- `T†† = T`, and `exp(c ρ)⁻¹ = exp(-c ρ)`.
    simpa [ContinuousLinearMap.adjoint_adjoint, ← Real.exp_neg, neg_mul] using hT f

end ContinuousLinearMap
