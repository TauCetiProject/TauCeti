/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.OfScalars
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import TauCeti.RingTheory.PowerSeries.DFinite.Borel
public import TauCeti.RingTheory.PowerSeries.Radius
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-!
# Factorial-divided power series `eFun` under geometric coefficient bounds

Given a complex sequence `a : ℕ → ℂ`, this file defines the factorial-divided complex series

  `eFun a z = ∑' n, aₙ * zⁿ / n!`

corresponding to the formal Borel series `TauCeti.ePowerSeries a = ∑ (aₙ / n!) Xⁿ`.

Whenever `‖aₙ‖ ≤ C ^ (n + 1)` for all `n` (with any real constant `C`, automatically nonnegative
from `n = 0`), `ePowerSeries a` has infinite radius of convergence, `eFun a` is represented by its
Taylor series on `Metric.eball 0 ⊤` (hence analytic and complex-differentiable on all of `ℂ`),
complex differentiation shifts `a` by `1` (`deriv (eFun a) = eFun fun n ↦ a (n + 1)`), and the
Hurwitz convolution evaluates to the pointwise product (`eFun (hurwitzMul a b) z = eFun a z *
eFun b z`).

## Main definitions

* `TauCeti.eFun a`: the analytic sum `z ↦ ∑' n, aₙ * zⁿ / n!`.

## Main results

* `TauCeti.radius_ePowerSeries_of_norm_le`, `TauCeti.hasFPowerSeriesOnBall_eFun_of_norm_le`,
  `TauCeti.analyticOnNhd_eFun_of_norm_le`: infinite convergence radius and entireness under
  `‖aₙ‖ ≤ C ^ (n + 1)`.
* `TauCeti.hasDerivAt_eFun_of_norm_le`, `TauCeti.deriv_eFun_of_norm_le`,
  `TauCeti.iteratedDeriv_eFun_of_norm_le`: termwise differentiation shifts `a`.
* `TauCeti.eFun_hurwitzMul_of_norm_le`: Hurwitz convolution corresponds to pointwise multiplication
  of `eFun`.
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

/-- Evaluating `eFun a` at `0` recovers `a 0`. -/
@[simp]
theorem eFun_eval_zero (a : ℕ → ℂ) : eFun a 0 = a 0 := by
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

/-- `eFun` on `Pi.single 1 1` is the identity `z`. -/
@[simp]
theorem eFun_single_one (z : ℂ) : eFun (Pi.single 1 1) z = z := by
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
    rw [← PowerSeries.radius_eq_radius_of_norm_eq (f := ePowerSeries a) p
      (fun n ↦ by simp [p, coeff_ePowerSeries])]
    exact radius_ePowerSeries_of_norm_le ha
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

private theorem shift_norm_le {a : ℕ → ℂ} {C : ℝ} (ha : ∀ n, ‖a n‖ ≤ C ^ (n + 1)) (n : ℕ) :
    ‖a (n + 1)‖ ≤ (max 1 C ^ 2) ^ (n + 1) := by
  have hC : 0 ≤ C := by simpa using (norm_nonneg (a 0)).trans (ha 0)
  refine (ha (n + 1)).trans ?_
  calc C ^ (n + 2)
      ≤ max 1 C ^ (n + 2) := pow_le_pow_left₀ hC (le_max_right 1 C) (n + 2)
    _ ≤ max 1 C ^ (2 * (n + 1)) := pow_le_pow_right₀ (le_max_left 1 C) (by omega)
    _ = (max 1 C ^ 2) ^ (n + 1) := by rw [pow_mul]

/-- Under `‖a n‖ ≤ C ^ (n + 1)`, `eFun a` has complex derivative `eFun (fun n ↦ a (n + 1)) z` at
every `z : ℂ`. -/
theorem hasDerivAt_eFun_of_norm_le {a : ℕ → ℂ} {C : ℝ}
    (ha : ∀ n, ‖a n‖ ≤ C ^ (n + 1)) (z : ℂ) :
    HasDerivAt (eFun a) (eFun (fun n ↦ a (n + 1)) z) z := by
  set R : ℝ := ‖z‖ + 1
  have hR : 0 < R := by positivity
  let g : ℕ → ℂ → ℂ := fun n w ↦ a n * w ^ n / n.factorial
  let g' : ℕ → ℂ → ℂ := fun n w ↦
    if n = 0 then 0 else a n * w ^ (n - 1) / (n - 1).factorial
  let u : ℕ → ℝ := fun n ↦
    if n = 0 then 0 else ‖a n‖ * R ^ (n - 1) / (n - 1).factorial
  have hu_shift : Summable fun n : ℕ ↦ u (n + 1) := by
    simpa [u] using summable_norm_eFun_term_of_norm_le (shift_norm_le ha) hR.le
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
    rw [iteratedDeriv_succ', deriv_eFun_of_norm_le ha, ih (shift_norm_le ha)]
    simp_rw [Nat.add_assoc]

/-- Under geometric bounds, `eFun` preserves addition. -/
theorem eFun_add_of_norm_le {a b : ℕ → ℂ} {C₁ C₂ : ℝ}
    (ha : ∀ n, ‖a n‖ ≤ C₁ ^ (n + 1)) (hb : ∀ n, ‖b n‖ ≤ C₂ ^ (n + 1)) (z : ℂ) :
    eFun (a + b) z = eFun a z + eFun b z := by
  rw [eFun_def, eFun_def, eFun_def,
    ← (summable_eFun_term_of_norm_le ha z).tsum_add (summable_eFun_term_of_norm_le hb z)]
  refine tsum_congr fun n ↦ ?_
  simp [add_mul, add_div]

/-- **Hurwitz product evaluates to analytic product.** Under geometric coefficient bounds,
`eFun (hurwitzMul a b) z = eFun a z * eFun b z` for every `z : ℂ`. -/
theorem eFun_hurwitzMul_of_norm_le {a b : ℕ → ℂ} {C₁ C₂ : ℝ}
    (ha : ∀ n, ‖a n‖ ≤ C₁ ^ (n + 1)) (hb : ∀ n, ‖b n‖ ≤ C₂ ^ (n + 1)) (z : ℂ) :
    eFun (hurwitzMul a b) z = eFun a z * eFun b z := by
  have hna : Summable fun n : ℕ ↦ ‖a n * z ^ n / n.factorial‖ := by
    simpa using summable_norm_eFun_term_of_norm_le ha (norm_nonneg z)
  have hnb : Summable fun n : ℕ ↦ ‖b n * z ^ n / n.factorial‖ := by
    simpa using summable_norm_eFun_term_of_norm_le hb (norm_nonneg z)
  rw [eFun_def, eFun_def, eFun_def,
    tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hna hnb]
  refine tsum_congr fun n ↦ ?_
  rw [hurwitzMul_eq_sum_antidiagonal, Finset.sum_mul, div_eq_mul_inv, Finset.sum_mul]
  refine Finset.sum_congr rfl fun ij hij ↦ ?_
  have hsum := Finset.mem_antidiagonal.mp hij
  have hi : (ij.1.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hj : (ij.2.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hn : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hchoose : (n.choose ij.1 : ℂ) * ij.1.factorial * ij.2.factorial = n.factorial := by
    have hij2 : n - ij.1 = ij.2 := by omega
    exact_mod_cast hij2 ▸ Nat.choose_mul_factorial_mul_factorial (by omega : ij.1 ≤ n)
  rw [← div_eq_mul_inv, nsmul_eq_mul, div_mul_div_comm, ← hsum, pow_add,
    div_eq_div_iff (by rw [hsum]; exact hn) (mul_ne_zero hi hj)]
  calc ((ij.1 + ij.2).choose ij.1 : ℂ) * (a ij.1 * b ij.2) * (z ^ ij.1 * z ^ ij.2) *
          (ij.1.factorial * ij.2.factorial)
      = a ij.1 * z ^ ij.1 * (b ij.2 * z ^ ij.2) *
          ((n.choose ij.1 : ℂ) * ij.1.factorial * ij.2.factorial) := by
        rw [hsum]
        ring
    _ = a ij.1 * z ^ ij.1 * (b ij.2 * z ^ ij.2) * (ij.1 + ij.2).factorial := by
        rw [hchoose, hsum]

end TauCeti
