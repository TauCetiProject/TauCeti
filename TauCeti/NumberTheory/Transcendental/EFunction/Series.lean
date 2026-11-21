/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.OfScalars
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import TauCeti.RingTheory.PowerSeries.Borel
public import TauCeti.RingTheory.PowerSeries.Entire.Eval
public import TauCeti.RingTheory.PowerSeries.Radius
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import TauCeti.Algebra.Order.GroupWithZero.Pow

/-!
# Factorial-divided power series `eFun` under geometric coefficient bounds

Given a complex sequence `a : ℕ → ℂ`, this file defines the factorial-divided complex series

  `eFun a z = ∑' n, aₙ * zⁿ / n!`

corresponding to the formal Borel series `TauCeti.ePowerSeries a = ∑ (aₙ / n!) Xⁿ`, so that
`eFun a z = (ePowerSeries a).evalAt z` (`TauCeti.eFun_eq_evalAt_ePowerSeries`).

In transcendence theory, Siegel's E-functions are entire functions of the form `eFun a` whose
coefficients satisfy algebraic, differential, and arithmetic growth hypotheses. Separating out the
purely analytic consequences of the geometric modulus bound `‖aₙ‖ ≤ C ^ (n + 1)` allows entireness,
Taylor-series representation, termwise complex differentiation, evaluation of sums, differences,
and Hurwitz products, and division by `1 - z` at a zero at `1` (`TauCeti.divOneSubSeq`) to be
applied before establishing full E-function closure or arithmetic bounds.

Whenever `‖aₙ‖ ≤ C ^ (n + 1)` for all `n` (with any real constant `C`, automatically nonnegative
from `n = 0`), `ePowerSeries a` has infinite radius of convergence, `eFun a` is represented by its
Taylor series on `Metric.eball 0 ⊤` (hence analytic and complex-differentiable on all of `ℂ`),
complex differentiation shifts `a` by `1` (`deriv (eFun a) = eFun fun n ↦ a (n + 1)`), and the
Hurwitz convolution evaluates to the pointwise product (`eFun (hurwitzMul a b) z = eFun a z *
eFun b z`). If moreover `eFun a 1 = 0`, dividing `ePowerSeries a` by `1 - X` produces the
normalized quotient sequence `divOneSubSeq a n = n! * ∑ k ≤ n, aₖ / k!`, which inherits a
geometric modulus bound (`TauCeti.norm_divOneSubSeq_le`) and satisfies the analytic identity
`(1 - z) * eFun (divOneSubSeq a) z = eFun a z` (`TauCeti.one_sub_mul_eFun_divOneSubSeq_of_norm_le`).

## Main definitions

* `TauCeti.eFun a`: the analytic sum `z ↦ ∑' n, aₙ * zⁿ / n!`.
* `TauCeti.divOneSubSeq a`: the coefficient sequence `n ↦ n! * ∑ k ≤ n, aₖ / k!` of the quotient
  of `ePowerSeries a` by `1 - X`.

## Main results

* `TauCeti.eFun_eq_evalAt_ePowerSeries`: `eFun a z = (ePowerSeries a).evalAt z`.
* `TauCeti.radius_ePowerSeries_of_norm_le`, `TauCeti.isEntire_ePowerSeries_of_norm_le`,
  `TauCeti.hasFPowerSeriesOnBall_eFun_of_norm_le`, `TauCeti.analyticOnNhd_eFun_of_norm_le`:
  infinite convergence radius and entireness under `‖aₙ‖ ≤ C ^ (n + 1)`.
* `TauCeti.hasDerivAt_eFun_of_norm_le`, `TauCeti.deriv_eFun_of_norm_le`,
  `TauCeti.iteratedDeriv_eFun_of_norm_le`: termwise differentiation shifts `a`.
* `TauCeti.eFun_add_of_norm_le`, `TauCeti.eFun_sub_of_norm_le`,
  `TauCeti.eFun_hurwitzMul_of_norm_le`: `eFun` preserves addition, subtraction, and Hurwitz
  products under geometric coefficient bounds.
* `TauCeti.one_sub_X_mul_ePowerSeries_divOneSubSeq`, `TauCeti.norm_divOneSubSeq_le`,
  `TauCeti.one_sub_mul_eFun_divOneSubSeq_of_norm_le`: formal identity, geometric modulus bound,
  and analytic quotient identity for `divOneSubSeq`.
-/

public section

open Filter
open scoped ENNReal NNReal PowerSeries Topology

namespace TauCeti

/-! ### Basic properties of `eFun` -/

/-- The complex series `z ↦ ∑' n, a n * z ^ n / n!` attached to a sequence `a : ℕ → ℂ`. -/
noncomputable def eFun (a : ℕ → ℂ) (z : ℂ) : ℂ :=
  ∑' n : ℕ, a n * z ^ n / n.factorial

/-- Unfolding `eFun` as an infinite series. -/
theorem eFun_def (a : ℕ → ℂ) (z : ℂ) :
    eFun a z = ∑' n : ℕ, a n * z ^ n / n.factorial :=
  (rfl)

/-- Evaluating `eFun a` at `z` agrees with `PowerSeries.evalAt` on `ePowerSeries a`. -/
theorem eFun_eq_evalAt_ePowerSeries (a : ℕ → ℂ) (z : ℂ) :
    eFun a z = (ePowerSeries a).evalAt z := by
  simp [eFun_def, PowerSeries.evalAt_def, div_mul_eq_mul_div]

/-- Applying `eFun a` at `0` recovers `a 0`. -/
@[simp]
theorem eFun_apply_zero (a : ℕ → ℂ) : eFun a 0 = a 0 := by
  rw [eFun_def, tsum_eq_single 0]
  · simp
  · intro n hn
    simp [zero_pow hn]

/-- The zero sequence sums to `0` at every `z`. -/
@[simp]
theorem eFun_zero (z : ℂ) : eFun 0 z = 0 := by
  simp [eFun_def]

/-- `eFun` on a sequence supported at `n` evaluates to the monomial `c * z ^ n / n!`. -/
theorem eFun_single (n : ℕ) (c z : ℂ) :
    eFun (Pi.single n c) z = c * z ^ n / n.factorial := by
  rw [eFun_def, tsum_eq_single n]
  · simp
  · intro m hmn
    simp [Pi.single_eq_of_ne hmn]

/-- `eFun` on `Pi.single 0 c` is the constant `c`. -/
@[simp]
theorem eFun_single_zero (c z : ℂ) : eFun (Pi.single 0 c) z = c := by
  simp [eFun_single]

/-- `eFun` on `Pi.single 1 c` is the linear function `c * z`. -/
@[simp]
theorem eFun_single_one (c z : ℂ) : eFun (Pi.single 1 c) z = c * z := by
  simp [eFun_single]

/-- The constant-one sequence sums to `Complex.exp`. -/
@[simp]
theorem eFun_const_one (z : ℂ) : eFun (fun _ ↦ 1) z = Complex.exp z := by
  simp [eFun_def, Complex.exp_eq_exp_ℂ, NormedSpace.exp_eq_tsum_div]

/-- `eFun` commutes with negation of sequences. -/
@[simp]
theorem eFun_neg (a : ℕ → ℂ) (z : ℂ) : eFun (-a) z = -eFun a z := by
  simp only [eFun_def, Pi.neg_apply, neg_mul, neg_div, tsum_neg]

/-- `eFun` commutes with complex scalar multiplication. -/
@[simp]
theorem eFun_smul (c : ℂ) (a : ℕ → ℂ) (z : ℂ) : eFun (c • a) z = c * eFun a z := by
  simp only [eFun_def, Pi.smul_apply, smul_eq_mul, mul_assoc, mul_div_assoc, tsum_mul_left]

/-- Rescaling `a n` by `α ^ n` evaluates `eFun a` at `α * z`. -/
theorem eFun_rescale (α : ℂ) (a : ℕ → ℂ) (z : ℂ) :
    eFun (fun n ↦ α ^ n * a n) z = eFun a (α * z) := by
  rw [eFun_def, eFun_def]
  congr 1 with n
  rw [mul_pow]
  ring

/-! ### Convergence and analyticity under geometric coefficient bounds -/

/-- If `‖a n‖ ≤ C ^ (n + 1)` for all `n`, then `∑ ‖a n‖ * R ^ n / n!` converges for every
nonnegative `R`. -/
theorem summable_norm_eFun_term_of_norm_le {a : ℕ → ℂ} {C : ℝ}
    (ha : ∀ n, ‖a n‖ ≤ C ^ (n + 1)) {R : ℝ} (hR : 0 ≤ R) :
    Summable fun n : ℕ ↦ ‖a n‖ * R ^ n / n.factorial := by
  have : 0 ≤ C := by simpa using (norm_nonneg (a 0)).trans (ha 0)
  refine Summable.of_nonneg_of_le (fun _ ↦ by positivity) (fun n ↦ ?_)
    ((Real.summable_pow_div_factorial (C * R)).mul_left C)
  calc ‖a n‖ * R ^ n / n.factorial
      ≤ C ^ (n + 1) * R ^ n / n.factorial := by gcongr; exact ha n
    _ = C * ((C * R) ^ n / n.factorial) := by rw [pow_succ', mul_pow]; ring

/-- Under `‖a n‖ ≤ C ^ (n + 1)`, the series defining `eFun a z` is summable at every `z : ℂ`. -/
theorem summable_eFun_term_of_norm_le {a : ℕ → ℂ} {C : ℝ}
    (ha : ∀ n, ‖a n‖ ≤ C ^ (n + 1)) (z : ℂ) :
    Summable fun n : ℕ ↦ a n * z ^ n / n.factorial := by
  refine Summable.of_norm_bounded (summable_norm_eFun_term_of_norm_le ha (norm_nonneg z))
    fun n ↦ ?_
  simp

/-- Under `‖a n‖ ≤ C ^ (n + 1)`, the series `∑ aₙ zⁿ / n!` converges to `eFun a z`. -/
theorem hasSum_eFun_of_norm_le {a : ℕ → ℂ} {C : ℝ}
    (ha : ∀ n, ‖a n‖ ≤ C ^ (n + 1)) (z : ℂ) :
    HasSum (fun n : ℕ ↦ a n * z ^ n / n.factorial) (eFun a z) :=
  (summable_eFun_term_of_norm_le ha z).hasSum

/-- Under `‖a n‖ ≤ C ^ (n + 1)`, the formal series `ePowerSeries a` has infinite radius of
convergence. -/
theorem radius_ePowerSeries_of_norm_le {a : ℕ → ℂ} {C : ℝ}
    (ha : ∀ n, ‖a n‖ ≤ C ^ (n + 1)) :
    (ePowerSeries a).radius = ⊤ := by
  refine ENNReal.eq_top_of_forall_nnreal_le fun r ↦ ?_
  have hsum := summable_norm_eFun_term_of_norm_le ha r.coe_nonneg
  obtain ⟨B, hB⟩ := hsum.tendsto_atTop_zero.bddAbove_range
  refine PowerSeries.le_radius_of_bound B fun n ↦ ?_
  have hmem : ‖a n‖ * (r : ℝ) ^ n / n.factorial ∈
      Set.range (fun k : ℕ ↦ ‖a k‖ * (r : ℝ) ^ k / k.factorial) := ⟨n, rfl⟩
  simpa [coeff_ePowerSeries, norm_div, div_mul_eq_mul_div] using hB hmem

/-- Under `‖a n‖ ≤ C ^ (n + 1)`, the formal series `ePowerSeries a` is entire. -/
theorem isEntire_ePowerSeries_of_norm_le {a : ℕ → ℂ} {C : ℝ}
    (ha : ∀ n, ‖a n‖ ≤ C ^ (n + 1)) :
    (ePowerSeries a).IsEntire :=
  PowerSeries.radius_eq_top_iff.mp (radius_ePowerSeries_of_norm_le ha)

/-- Under `‖a n‖ ≤ C ^ (n + 1)`, `eFun a` has formal power series
`ofScalars ℂ (fun n ↦ a n / n!)` on the ball of radius `⊤` around `0`. -/
theorem hasFPowerSeriesOnBall_eFun_of_norm_le {a : ℕ → ℂ} {C : ℝ}
    (ha : ∀ n, ‖a n‖ ≤ C ^ (n + 1)) :
    HasFPowerSeriesOnBall (eFun a)
      (FormalMultilinearSeries.ofScalars ℂ fun n ↦ a n / n.factorial) 0 ⊤ := by
  set p := FormalMultilinearSeries.ofScalars ℂ fun n ↦ a n / n.factorial
  have hrad : p.radius = ⊤ := by
    simpa [p, coeff_ePowerSeries] using
      (PowerSeries.radius_eq_radius_ofScalars ℂ (ePowerSeries a)).symm.trans
        (radius_ePowerSeries_of_norm_le ha)
  have hp := p.hasFPowerSeriesOnBall (hrad ▸ ENNReal.zero_lt_top)
  rw [hrad] at hp
  have hsum : p.sum = eFun a := by
    ext z
    rw [FormalMultilinearSeries.sum, eFun_def]
    refine tsum_congr fun n ↦ ?_
    simp only [p, FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul]
    ring
  rwa [hsum] at hp

/-- Under `‖a n‖ ≤ C ^ (n + 1)`, `eFun a` is analytic on all of `ℂ`. -/
theorem analyticOnNhd_eFun_of_norm_le {a : ℕ → ℂ} {C : ℝ}
    (ha : ∀ n, ‖a n‖ ≤ C ^ (n + 1)) :
    AnalyticOnNhd ℂ (eFun a) Set.univ := by
  simpa using (hasFPowerSeriesOnBall_eFun_of_norm_le ha).analyticOnNhd

/-- Under `‖a n‖ ≤ C ^ (n + 1)`, `eFun a` is complex-differentiable everywhere. -/
theorem differentiable_eFun_of_norm_le {a : ℕ → ℂ} {C : ℝ}
    (ha : ∀ n, ‖a n‖ ≤ C ^ (n + 1)) :
    Differentiable ℂ (eFun a) :=
  differentiableOn_univ.mp (analyticOnNhd_eFun_of_norm_le ha).differentiableOn

/-- Under `‖a n‖ ≤ C ^ (n + 1)`, `eFun a` has complex derivative `eFun (fun n ↦ a (n + 1)) z` at
every `z : ℂ`. -/
theorem hasDerivAt_eFun_of_norm_le {a : ℕ → ℂ} {C : ℝ}
    (ha : ∀ n, ‖a n‖ ≤ C ^ (n + 1)) (z : ℂ) :
    HasDerivAt (eFun a) (eFun (fun n ↦ a (n + 1)) z) z := by
  have hC : 0 ≤ C := by simpa using (norm_nonneg (a 0)).trans (ha 0)
  set R : ℝ := ‖z‖ + 1
  have hR : 0 < R := by positivity
  let g : ℕ → ℂ → ℂ := fun n w ↦ a n * w ^ n / n.factorial
  let g' : ℕ → ℂ → ℂ := fun n w ↦
    if n = 0 then 0 else a n * w ^ (n - 1) / (n - 1).factorial
  let u : ℕ → ℝ := fun n ↦
    if n = 0 then 0 else ‖a n‖ * R ^ (n - 1) / (n - 1).factorial
  have hu_shift : Summable fun n : ℕ ↦ u (n + 1) := by
    simpa [u] using summable_norm_eFun_term_of_norm_le
      (fun n ↦ (ha (n + 1)).trans (pow_le_max_one_pow_pow hC (k := 2) (by omega))) hR.le
  have hu : Summable u := (summable_nat_add_iff 1).mp hu_shift
  have hg : ∀ n w, w ∈ Metric.ball (0 : ℂ) R → HasDerivAt (g n) (g' n w) w := by
    intro n w _
    cases n with
    | zero => simpa [g, g'] using hasDerivAt_const w (a 0)
    | succ n =>
      have hd := (((hasDerivAt_pow (n + 1) w).const_mul (a (n + 1))).div_const
        ((n + 1).factorial : ℂ))
      have hsimp : a (n + 1) * ((n + 1 : ℂ) * w ^ n) / (n + 1).factorial = g' (n + 1) w := by
        simp only [g', Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel, Nat.factorial_succ,
          Nat.cast_mul]
        rw [← div_div, mul_left_comm (a (n + 1)), Nat.cast_add, Nat.cast_one,
          mul_div_cancel_left₀ _ (by exact_mod_cast Nat.succ_ne_zero n)]
      simpa [Nat.add_sub_cancel, hsimp] using hd
  have hg' : ∀ n w, w ∈ Metric.ball (0 : ℂ) R → ‖g' n w‖ ≤ u n := by
    intro n w hw
    cases n with
    | zero => simp [g', u]
    | succ n =>
      have hwR : ‖w‖ ≤ R := (mem_ball_zero_iff.mp hw).le
      simp only [g', u, Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel, norm_div, norm_mul,
        norm_pow, Complex.norm_natCast]
      gcongr
  have hzR : z ∈ Metric.ball (0 : ℂ) R := mem_ball_zero_iff.mpr (lt_add_one ‖z‖)
  have htsum : HasDerivAt (eFun a) (∑' n, g' n z) z :=
    hasDerivAt_tsum_of_isPreconnected hu Metric.isOpen_ball (convex_ball 0 R).isPreconnected
      hg hg' (Metric.mem_ball_self hR) (summable_eFun_term_of_norm_le ha 0) hzR
  have hsum_succ : Summable fun n : ℕ ↦ g' (n + 1) z :=
    Summable.of_norm_bounded hu_shift fun n ↦ hg' (n + 1) z hzR
  have hsum_g' : (∑' n, g' n z) = eFun (fun n ↦ a (n + 1)) z := by
    rw [((summable_nat_add_iff 1).mp hsum_succ).tsum_eq_zero_add]
    simp [g', eFun_def]
  rwa [hsum_g'] at htsum

/-- Under `‖a n‖ ≤ C ^ (n + 1)`, `deriv (eFun a) = eFun fun n ↦ a (n + 1)`. -/
theorem deriv_eFun_of_norm_le {a : ℕ → ℂ} {C : ℝ}
    (ha : ∀ n, ‖a n‖ ≤ C ^ (n + 1)) :
    deriv (eFun a) = eFun fun n ↦ a (n + 1) := by
  ext z
  exact (hasDerivAt_eFun_of_norm_le ha z).deriv

/-- Under `‖a n‖ ≤ C ^ (n + 1)`, the `m`-th iterated derivative of `eFun a` shifts `a` by `m`. -/
theorem iteratedDeriv_eFun_of_norm_le {a : ℕ → ℂ} {C : ℝ}
    (ha : ∀ n, ‖a n‖ ≤ C ^ (n + 1)) (m : ℕ) :
    iteratedDeriv m (eFun a) = eFun fun n ↦ a (n + m) := by
  induction m generalizing a C with
  | zero =>
    ext z
    simp
  | succ m ih =>
    have hC : 0 ≤ C := by simpa using (norm_nonneg (a 0)).trans (ha 0)
    rw [iteratedDeriv_succ', deriv_eFun_of_norm_le ha,
      ih fun n ↦ (ha (n + 1)).trans (pow_le_max_one_pow_pow hC (k := 2) (by omega))]
    simp_rw [Nat.add_assoc]

/-- Under geometric bounds, `eFun` preserves addition. -/
theorem eFun_add_of_norm_le {a b : ℕ → ℂ} {C₁ C₂ : ℝ}
    (ha : ∀ n, ‖a n‖ ≤ C₁ ^ (n + 1)) (hb : ∀ n, ‖b n‖ ≤ C₂ ^ (n + 1)) (z : ℂ) :
    eFun (a + b) z = eFun a z + eFun b z := by
  simp only [eFun_eq_evalAt_ePowerSeries, ePowerSeries_add]
  exact (isEntire_ePowerSeries_of_norm_le ha).evalAt_add (isEntire_ePowerSeries_of_norm_le hb) z

/-- Under geometric bounds, `eFun` preserves subtraction. -/
theorem eFun_sub_of_norm_le {a b : ℕ → ℂ} {C₁ C₂ : ℝ}
    (ha : ∀ n, ‖a n‖ ≤ C₁ ^ (n + 1)) (hb : ∀ n, ‖b n‖ ≤ C₂ ^ (n + 1)) (z : ℂ) :
    eFun (a - b) z = eFun a z - eFun b z := by
  simp only [eFun_eq_evalAt_ePowerSeries, ePowerSeries_sub]
  exact (isEntire_ePowerSeries_of_norm_le ha).evalAt_sub (isEntire_ePowerSeries_of_norm_le hb) z

/-- **Hurwitz product evaluates to analytic product.** Under geometric coefficient bounds,
`eFun (hurwitzMul a b) z = eFun a z * eFun b z` for every `z : ℂ`. -/
theorem eFun_hurwitzMul_of_norm_le {a b : ℕ → ℂ} {C₁ C₂ : ℝ}
    (ha : ∀ n, ‖a n‖ ≤ C₁ ^ (n + 1)) (hb : ∀ n, ‖b n‖ ≤ C₂ ^ (n + 1)) (z : ℂ) :
    eFun (hurwitzMul a b) z = eFun a z * eFun b z := by
  simp only [eFun_eq_evalAt_ePowerSeries, ePowerSeries_hurwitzMul]
  exact (isEntire_ePowerSeries_of_norm_le ha).evalAt_mul (isEntire_ePowerSeries_of_norm_le hb) z

/-! ### Division by `1 - z` at a zero at `1` -/

/-- Given `a : ℕ → ℂ`, the normalized coefficient sequence
`divOneSubSeq a n = n! * ∑ k ∈ Finset.range (n + 1), a k / k!` of `(1 - X)⁻¹ * ePowerSeries a`. -/
noncomputable def divOneSubSeq (a : ℕ → ℂ) (n : ℕ) : ℂ :=
  n.factorial * ∑ k ∈ Finset.range (n + 1), a k / k.factorial

/-- Unfolding `divOneSubSeq`. -/
theorem divOneSubSeq_def (a : ℕ → ℂ) (n : ℕ) :
    divOneSubSeq a n = n.factorial * ∑ k ∈ Finset.range (n + 1), a k / k.factorial :=
  (rfl)

/-- Applying `divOneSubSeq a` at `0` gives `a 0`. -/
@[simp]
theorem divOneSubSeq_apply_zero (a : ℕ → ℂ) : divOneSubSeq a 0 = a 0 := by
  simp [divOneSubSeq_def]

/-- `divOneSubSeq` maps the zero sequence to `0`. -/
@[simp]
theorem divOneSubSeq_zero : divOneSubSeq 0 = 0 := by
  ext n
  simp [divOneSubSeq_def]

/-- Step recurrence for `divOneSubSeq`:
`divOneSubSeq a (n + 1) = (n + 1) * divOneSubSeq a n + a (n + 1)`. -/
theorem divOneSubSeq_succ (a : ℕ → ℂ) (n : ℕ) :
    divOneSubSeq a (n + 1) = (n + 1) * divOneSubSeq a n + a (n + 1) := by
  have hnf : ((n + 1).factorial : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (n + 1))
  rw [divOneSubSeq_def, divOneSubSeq_def, Finset.sum_range_succ, mul_add,
    mul_div_cancel₀ _ hnf, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
    mul_assoc]

/-- Applying a ring endomorphism `σ : ℂ →+* ℂ` commutes with `divOneSubSeq` at each index. -/
theorem map_divOneSubSeq (σ : ℂ →+* ℂ) (a : ℕ → ℂ) (n : ℕ) :
    σ (divOneSubSeq a n) = divOneSubSeq (σ ∘ a) n := by
  simp [divOneSubSeq_def]

/-- Post-composing with a ring endomorphism `σ : ℂ →+* ℂ` commutes with `divOneSubSeq`. -/
theorem comp_divOneSubSeq (σ : ℂ →+* ℂ) (a : ℕ → ℂ) :
    σ ∘ divOneSubSeq a = divOneSubSeq (σ ∘ a) :=
  funext (map_divOneSubSeq σ a)

/-- Formal identity `(1 - X) * ePowerSeries (divOneSubSeq a) = ePowerSeries a`. -/
@[simp]
theorem one_sub_X_mul_ePowerSeries_divOneSubSeq (a : ℕ → ℂ) :
    (1 - PowerSeries.X) * ePowerSeries (divOneSubSeq a) = ePowerSeries a := by
  have hcoeff (n : ℕ) :
      PowerSeries.coeff n (ePowerSeries (divOneSubSeq a)) =
        ∑ k ∈ Finset.range (n + 1), a k / k.factorial := by
    rw [coeff_ePowerSeries, divOneSubSeq_def,
      mul_div_cancel_left₀ _ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n))]
  ext n
  cases n with
  | zero => simp [sub_mul]
  | succ n =>
    rw [sub_mul, one_mul, map_sub, PowerSeries.coeff_succ_X_mul, hcoeff, hcoeff,
      Finset.sum_range_succ, add_sub_cancel_left, coeff_ePowerSeries]

/-- If `‖a n‖ ≤ C ^ (n + 1)` for all `n` and `eFun a 1 = 0`, then `divOneSubSeq a` satisfies the
geometric modulus bound `‖divOneSubSeq a n‖ ≤ (max 1 C ^ 2 * Real.exp C) ^ (n + 1)`. -/
theorem norm_divOneSubSeq_le {a : ℕ → ℂ} {C : ℝ}
    (ha : ∀ n, ‖a n‖ ≤ C ^ (n + 1)) (hz : eFun a 1 = 0) (n : ℕ) :
    ‖divOneSubSeq a n‖ ≤ (max 1 C ^ 2 * Real.exp C) ^ (n + 1) := by
  have hC : 0 ≤ C := by simpa using (norm_nonneg (a 0)).trans (ha 0)
  have hsum1 : Summable fun k : ℕ ↦ a k / k.factorial := by
    simpa using summable_eFun_term_of_norm_le ha 1
  have hz0 : (∑' k : ℕ, a k / k.factorial) = 0 := by simpa [eFun_def] using hz
  have hsplit := hsum1.sum_add_tsum_nat_add (n + 1)
  rw [hz0] at hsplit
  have htail := eq_neg_of_add_eq_zero_left hsplit
  have hterm_le (m : ℕ) :
      ‖(n.factorial : ℂ) * (a (m + (n + 1)) / (m + (n + 1)).factorial)‖ ≤
        C ^ (n + 2) * (C ^ m / m.factorial) := by
    have hfac_le : n.factorial * m.factorial ≤ (m + (n + 1)).factorial :=
      calc n.factorial * m.factorial
          ≤ (n + 1).factorial * m.factorial :=
            Nat.mul_le_mul_right _ (Nat.factorial_le (Nat.le_succ n))
        _ = 1 * (m.factorial * (n + 1).factorial) := by ring
        _ ≤ (m + (n + 1)).choose (n + 1) * (m.factorial * (n + 1).factorial) :=
            Nat.mul_le_mul_right _ (Nat.choose_pos (Nat.le_add_left (n + 1) m))
        _ = (m + (n + 1)).factorial := by
            rw [← mul_assoc, Nat.add_choose_mul_factorial_mul_factorial]
    have hexp : m + (n + 1) + 1 = (n + 2) + m := by omega
    have hnf : (n.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
    have hmf : (m.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m)
    rw [norm_mul, norm_div, Complex.norm_natCast, Complex.norm_natCast]
    calc (n.factorial : ℝ) * (‖a (m + (n + 1))‖ / (m + (n + 1)).factorial)
        ≤ (n.factorial : ℝ) * (C ^ (m + (n + 1) + 1) / (n.factorial * m.factorial)) := by
          gcongr
          · exact ha _
          · exact_mod_cast hfac_le
      _ = C ^ (n + 2) * (C ^ m / m.factorial) := by
          rw [hexp, pow_add]
          field_simp
  have hdom : Summable fun m : ℕ ↦ C ^ (n + 2) * (C ^ m / m.factorial) :=
    (Real.summable_pow_div_factorial C).mul_left (C ^ (n + 2))
  have hsub : Summable fun m : ℕ ↦
      ‖(n.factorial : ℂ) * (a (m + (n + 1)) / (m + (n + 1)).factorial)‖ :=
    Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) hterm_le hdom
  have hnorm_tail : ‖divOneSubSeq a n‖ ≤ C ^ (n + 2) * Real.exp C := by
    rw [divOneSubSeq_def, htail, mul_neg, norm_neg, ← tsum_mul_left]
    exact (norm_tsum_le_tsum_norm hsub).trans ((Summable.tsum_le_tsum hterm_le hsub hdom).trans
      (by rw [tsum_mul_left, Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]))
  refine hnorm_tail.trans ?_
  rw [mul_pow]
  exact mul_le_mul (pow_le_max_one_pow_pow hC (by omega))
    (le_self_pow₀ (Real.one_le_exp hC) (Nat.succ_ne_zero n))
    (Real.exp_pos C).le (by positivity)

/-- Under `‖a n‖ ≤ C ^ (n + 1)` and `eFun a 1 = 0`, the quotient sequence `divOneSubSeq a`
satisfies `(1 - z) * eFun (divOneSubSeq a) z = eFun a z` for all `z : ℂ`. -/
theorem one_sub_mul_eFun_divOneSubSeq_of_norm_le {a : ℕ → ℂ} {C : ℝ}
    (ha : ∀ n, ‖a n‖ ≤ C ^ (n + 1)) (hz : eFun a 1 = 0) (z : ℂ) :
    (1 - z) * eFun (divOneSubSeq a) z = eFun a z := by
  have hb := isEntire_ePowerSeries_of_norm_le (norm_divOneSubSeq_le ha hz)
  have h1X : (1 - PowerSeries.X : ℂ⟦X⟧).IsEntire :=
    PowerSeries.isEntire_one.sub PowerSeries.isEntire_X
  have heval1X : (1 - PowerSeries.X : ℂ⟦X⟧).evalAt z = 1 - z := by
    simpa using PowerSeries.isEntire_one.evalAt_sub (R := ℂ) PowerSeries.isEntire_X z
  rw [eFun_eq_evalAt_ePowerSeries, eFun_eq_evalAt_ePowerSeries, ← heval1X,
    ← h1X.evalAt_mul hb z, one_sub_X_mul_ePowerSeries_divOneSubSeq]

end TauCeti
