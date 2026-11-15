/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.BernoulliPolynomials
public import TauCeti.Analysis.Complex.CauchyIntegralPolydisc
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# The Bernoulli generating kernel and uniform Taylor remainder bounds

The Mellin integrand of the Hurwitz zeta function involves the generating kernel

`K(c, z) = z * exp (-c * z) / (1 - exp (-z))`

extended across its removable singularity at `z = 0` by `K(c, 0) = 1`. Writing the denominator as
`dslope (fun w ↦ -exp (-w)) 0 z` gives a total expression without case splits that is jointly
analytic on `ℂ × ball 0 (2π)`, since the nonzero zeros of `1 - exp (-z)` lie on `2πiℤ \ {0}` at
distance at least `2π` from the origin.

On `ball 0 (2π)` the kernel satisfies `K(c, z) * (exp z - 1) = z * exp ((1 - c) * z)`. Comparing
iterated `z`-derivatives at `0` with Mathlib's Bernoulli polynomial recurrence
`Polynomial.sum_bernoulli` and reflection identity `Polynomial.bernoulli_comp_one_sub_X` identifies
the `k`-th Taylor coefficient of `z ↦ K(c, z)` at `z = 0` as
`(-1) ^ k * B_k(c) / k!`.

Integrating the exact geometric remainder identity on the circle `C(0, 2)` expresses the `M`-th
Taylor remainder on `ball 0 2` in factored form `z ^ (M + 1) * Q_M(c, z)` where `Q_M` is jointly
analytic on `ℂ × ball 0 2` by `TauCeti.analyticOnNhd_circleIntegral`. Joint analyticity of `Q_M`
yields uniform `O(|z| ^ (M + 1))` bounds on `closedBall 0 1` (and hence `O(t ^ (M + 1))` on
`t ∈ [0, 1]`) over compact parameter sets `K ⊆ ℂ` for the remainder and all of its iterated
`c`-derivatives.

## Main definitions and results

* `TauCeti.hurwitzBernoulliKernel`: the analytic extension of `z * exp (-c * z) / (1 - exp (-z))`
  across `z = 0`, defined via `dslope`.
* `TauCeti.hurwitzBernoulliCoeff`: the Taylor coefficient `(-1) ^ k * B_k(c) / k!`.
* `TauCeti.analyticOnNhd_hurwitzBernoulliKernel`: joint analyticity on `ℂ × ball 0 (2π)`.
* `TauCeti.iteratedDeriv_hurwitzBernoulliKernel_zero`: identification of the `k`-th `z`-derivative
  at `0` with `(-1) ^ k * B_k(c)`.
* `TauCeti.hurwitzBernoulliRemainderQuot`, `TauCeti.hurwitzBernoulliKernel_sub_sum_eq`: exact
  jointly analytic Cauchy remainder quotient `Q_M(c, z)` on `ℂ × ball 0 2`.
* `IsCompact.exists_norm_iteratedDeriv_hurwitzBernoulliKernel_sub_sum_le`,
  `IsCompact.exists_norm_iteratedDeriv_hurwitzBernoulliKernel_sub_sum_ofReal_le`: uniform compact
  bounds on all iterated `c`-derivatives of the `M`-th Taylor remainder.

## References

* T. M. Apostol, *Introduction to Analytic Number Theory*, Springer (1976), §12.11.
* J. C. Lagarias and W.-C. W. Li, *The Lerch zeta function II. Analytic continuation*, Forum Math.
  24 (2012), 49–84, §9.
* NIST Digital Library of Mathematical Functions, §§24.2, 25.11, <https://dlmf.nist.gov/24.2>.
-/

public section

open Complex Filter Metric Real Set Topology
open scoped BigOperators

namespace TauCeti

/-- The Bernoulli generating kernel `z * exp (-c * z) / (1 - exp (-z))`, extended analytically
across `z = 0` by dividing `exp (-c * z)` by the difference quotient
`dslope (fun w ↦ -exp (-w)) 0 z`. -/
noncomputable def hurwitzBernoulliKernel (c z : ℂ) : ℂ :=
  Complex.exp (-c * z) / dslope (fun w : ℂ ↦ -Complex.exp (-w)) 0 z

/-- Unfolding lemma for `hurwitzBernoulliKernel`. -/
theorem hurwitzBernoulliKernel_def (c z : ℂ) :
    hurwitzBernoulliKernel c z =
      Complex.exp (-c * z) / dslope (fun w : ℂ ↦ -Complex.exp (-w)) 0 z := (rfl)

/-- The `k`-th Taylor coefficient `(-1) ^ k * B_k(c) / k!` of `z ↦ hurwitzBernoulliKernel c z` at
`z = 0`, where `B_k` is Mathlib's `Polynomial.bernoulli k` (with `B_1(X) = X - 1 / 2`). -/
noncomputable def hurwitzBernoulliCoeff (k : ℕ) (c : ℂ) : ℂ :=
  (-1 : ℂ) ^ k * Polynomial.aeval c (Polynomial.bernoulli k) / k.factorial

/-- Unfolding lemma for `hurwitzBernoulliCoeff`. -/
theorem hurwitzBernoulliCoeff_def (k : ℕ) (c : ℂ) :
    hurwitzBernoulliCoeff k c =
      (-1 : ℂ) ^ k * Polynomial.aeval c (Polynomial.bernoulli k) / k.factorial := (rfl)

/-- Presentation of `hurwitzBernoulliCoeff k c` via `Polynomial.eval` of the mapped rational
Bernoulli polynomial. -/
theorem hurwitzBernoulliCoeff_eq_eval_map (k : ℕ) (c : ℂ) :
    hurwitzBernoulliCoeff k c =
      (-1 : ℂ) ^ k * ((Polynomial.bernoulli k).map (algebraMap ℚ ℂ)).eval c / k.factorial := by
  rw [hurwitzBernoulliCoeff_def, Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map]

/-- The `0`-th Bernoulli Taylor coefficient is identically `1`. -/
@[simp]
theorem hurwitzBernoulliCoeff_zero (c : ℂ) : hurwitzBernoulliCoeff 0 c = 1 := by
  simp [hurwitzBernoulliCoeff_def]

/-- The `1`-st Bernoulli Taylor coefficient is `1 / 2 - c`. -/
theorem hurwitzBernoulliCoeff_one (c : ℂ) : hurwitzBernoulliCoeff 1 c = 1 / 2 - c := by
  simp [hurwitzBernoulliCoeff_def, Polynomial.bernoulli_one]

/-- The `2`-nd Bernoulli Taylor coefficient is `(c ^ 2 - c + 1 / 6) / 2`. -/
theorem hurwitzBernoulliCoeff_two (c : ℂ) :
    hurwitzBernoulliCoeff 2 c = (c ^ 2 - c + 1 / 6) / 2 := by
  rw [hurwitzBernoulliCoeff_def]
  simp only [Polynomial.bernoulli, Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    map_add, Polynomial.aeval_monomial, eq_ratCast, Rat.cast_mul, Rat.cast_natCast]
  rw [_root_.bernoulli_zero, _root_.bernoulli_one,
    bernoulli_eq_bernoulli'_of_ne_one (by decide : 2 ≠ 1), bernoulli'_two]
  norm_num
  ring

/-- Each Bernoulli Taylor coefficient `c ↦ hurwitzBernoulliCoeff k c` is an entire polynomial in
`c`. -/
@[fun_prop]
theorem differentiable_hurwitzBernoulliCoeff (k : ℕ) :
    Differentiable ℂ (hurwitzBernoulliCoeff k) := by
  rw [funext (hurwitzBernoulliCoeff_def k)]
  exact (((Polynomial.bernoulli k).differentiable_aeval (𝕜 := ℂ)).const_mul _).div_const _

/-- Each Bernoulli Taylor coefficient `hurwitzBernoulliCoeff k` is analytic at every `c : ℂ`. -/
@[fun_prop]
theorem analyticAt_hurwitzBernoulliCoeff (k : ℕ) (c : ℂ) :
    AnalyticAt ℂ (hurwitzBernoulliCoeff k) c :=
  (differentiable_hurwitzBernoulliCoeff k).analyticAt c

/-! ### Analyticity and values of `hurwitzBernoulliKernel` -/

/-- The denominator `dslope (fun w ↦ -exp (-w)) 0` equals `1` at `0`. -/
theorem dslope_neg_cexp_neg_zero :
    dslope (fun w : ℂ ↦ -Complex.exp (-w)) 0 0 = 1 := by
  rw [dslope_same]
  have hd : HasDerivAt (fun w : ℂ ↦ -Complex.exp (-w)) 1 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).neg.cexp).fun_neg
  exact hd.deriv

/-- Away from `0`, `dslope (fun w ↦ -exp (-w)) 0 z = (1 - exp (-z)) / z`. -/
theorem dslope_neg_cexp_neg_of_ne_zero {z : ℂ} (hz : z ≠ 0) :
    dslope (fun w : ℂ ↦ -Complex.exp (-w)) 0 z = (1 - Complex.exp (-z)) / z := by
  rw [dslope_of_ne _ hz, slope_def_field]
  simp [sub_eq_add_neg, add_comm]

/-- On the open disc `ball 0 (2π)`, the difference quotient `dslope (fun w ↦ -exp (-w)) 0` has no
zeros. -/
theorem dslope_neg_cexp_neg_ne_zero_of_mem_ball {z : ℂ}
    (hz : z ∈ Metric.ball (0 : ℂ) (2 * Real.pi)) :
    dslope (fun w : ℂ ↦ -Complex.exp (-w)) 0 z ≠ 0 := by
  rcases eq_or_ne z 0 with rfl | hz0
  · rw [dslope_neg_cexp_neg_zero]
    exact one_ne_zero
  · rw [dslope_neg_cexp_neg_of_ne_zero hz0, div_ne_zero_iff]
    refine ⟨sub_ne_zero.mpr fun hexp ↦ ?_, hz0⟩
    obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp hexp.symm
    have hn0 : n ≠ 0 := by
      rintro rfl
      simp only [Int.cast_zero, zero_mul, neg_eq_zero] at hn
      exact hz0 hn
    have h1 : (1 : ℝ) ≤ |(n : ℝ)| := by
      exact_mod_cast Int.one_le_abs hn0
    have hnorm : 2 * Real.pi ≤ ‖z‖ := by
      have hnz : ‖-z‖ = |(n : ℝ)| * (2 * Real.pi) := by
        rw [hn, norm_mul, norm_mul, norm_intCast, Complex.norm_I, mul_one, norm_mul,
          Complex.norm_two, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
      rw [norm_neg] at hnz
      nlinarith [Real.two_pi_pos]
    exact (mem_ball_zero_iff.mp hz).not_ge hnorm

/-- Removable value `hurwitzBernoulliKernel c 0 = 1` at `z = 0`. -/
@[simp]
theorem hurwitzBernoulliKernel_zero (c : ℂ) : hurwitzBernoulliKernel c 0 = 1 := by
  rw [hurwitzBernoulliKernel_def, dslope_neg_cexp_neg_zero]
  simp

/-- Away from `z = 0`, `hurwitzBernoulliKernel c z = z * exp (-c * z) / (1 - exp (-z))`. -/
theorem hurwitzBernoulliKernel_of_ne_zero (c : ℂ) {z : ℂ} (hz : z ≠ 0) :
    hurwitzBernoulliKernel c z = z * Complex.exp (-c * z) / (1 - Complex.exp (-z)) := by
  rw [hurwitzBernoulliKernel_def, dslope_neg_cexp_neg_of_ne_zero hz, div_div_eq_mul_div, mul_comm]

/-- The Bernoulli generating kernel `(c, z) ↦ hurwitzBernoulliKernel c z` is jointly analytic on
`ℂ × ball 0 (2π)`. -/
theorem analyticOnNhd_hurwitzBernoulliKernel :
    AnalyticOnNhd ℂ (fun p : ℂ × ℂ ↦ hurwitzBernoulliKernel p.1 p.2)
      (Set.univ ×ˢ Metric.ball (0 : ℂ) (2 * Real.pi)) := by
  intro p hp
  have hnum : AnalyticAt ℂ (fun q : ℂ × ℂ ↦ Complex.exp (-q.1 * q.2)) p :=
    (analyticAt_fst.neg.mul analyticAt_snd).cexp
  have hden_1d : AnalyticAt ℂ (dslope (fun w : ℂ ↦ -Complex.exp (-w)) 0) p.2 :=
    (analyticAt_id.neg.cexp.neg).dslope 0
  have hden : AnalyticAt ℂ (fun q : ℂ × ℂ ↦ dslope (fun w : ℂ ↦ -Complex.exp (-w)) 0 q.2) p :=
    hden_1d.comp analyticAt_snd
  exact hnum.div hden (dslope_neg_cexp_neg_ne_zero_of_mem_ball hp.2)

/-- For every fixed parameter `c : ℂ`, `hurwitzBernoulliKernel c` is analytic on `ball 0 (2π)`. -/
theorem analyticOnNhd_hurwitzBernoulliKernel_right (c : ℂ) :
    AnalyticOnNhd ℂ (hurwitzBernoulliKernel c) (Metric.ball (0 : ℂ) (2 * Real.pi)) := by
  intro z hz
  exact (analyticOnNhd_hurwitzBernoulliKernel (c, z) ⟨mem_univ c, hz⟩).comp
    (analyticAt_const.prod analyticAt_id)

/-- For every fixed `c : ℂ`, `hurwitzBernoulliKernel c` is complex differentiable on
`closedBall 0 2` (since `2 < 2π`). -/
theorem differentiableOn_hurwitzBernoulliKernel_closedBall_two (c : ℂ) :
    DifferentiableOn ℂ (hurwitzBernoulliKernel c) (Metric.closedBall (0 : ℂ) 2) := by
  have hsub : Metric.closedBall (0 : ℂ) 2 ⊆ Metric.ball (0 : ℂ) (2 * Real.pi) :=
    Metric.closedBall_subset_ball (by linarith [Real.pi_gt_three])
  exact (analyticOnNhd_hurwitzBernoulliKernel_right c).differentiableOn.mono hsub

/-! ### Generating identity and Taylor coefficients at `z = 0` -/

/-- On `ball 0 (2π)`, the kernel satisfies the exponential generating relation
`hurwitzBernoulliKernel c z * (exp z - 1) = z * exp ((1 - c) * z)`. -/
theorem hurwitzBernoulliKernel_mul_exp_sub_one (c : ℂ) {z : ℂ}
    (hz : z ∈ Metric.ball (0 : ℂ) (2 * Real.pi)) :
    hurwitzBernoulliKernel c z * (Complex.exp z - 1) = z * Complex.exp ((1 - c) * z) := by
  rcases eq_or_ne z 0 with rfl | hz0
  · simp
  · have hden : 1 - Complex.exp (-z) ≠ 0 := by
      have hd := dslope_neg_cexp_neg_ne_zero_of_mem_ball hz
      rw [dslope_neg_cexp_neg_of_ne_zero hz0] at hd
      exact (div_ne_zero_iff.mp hd).1
    have hexp : Complex.exp z - 1 = Complex.exp z * (1 - Complex.exp (-z)) := by
      rw [mul_sub, mul_one, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
    rw [hurwitzBernoulliKernel_of_ne_zero c hz0, hexp]
    have hcancel :
        z * Complex.exp (-c * z) / (1 - Complex.exp (-z)) *
          (Complex.exp z * (1 - Complex.exp (-z))) =
        z * Complex.exp (-c * z) * Complex.exp z := by
      field_simp [hden]
    rw [hcancel]
    calc z * Complex.exp (-c * z) * Complex.exp z
        = z * (Complex.exp (-c * z) * Complex.exp z) := by ring
      _ = z * Complex.exp (-c * z + z) := by rw [← Complex.exp_add]
      _ = z * Complex.exp ((1 - c) * z) := by ring_nf

private theorem iteratedDeriv_hurwitzBernoulliKernel_mul_exp_sub_one_zero (n : ℕ) (c : ℂ) :
    iteratedDeriv (n + 1)
        (fun z : ℂ ↦ hurwitzBernoulliKernel c z * (Complex.exp z - 1)) 0 =
      ∑ k ∈ Finset.range (n + 1),
        ((n + 1).choose k : ℂ) * iteratedDeriv k (hurwitzBernoulliKernel c) 0 := by
  have hK_cd : ContDiffAt ℂ (n + 1) (hurwitzBernoulliKernel c) 0 :=
    (analyticOnNhd_hurwitzBernoulliKernel_right c 0
      (Metric.mem_ball_self Real.two_pi_pos)).contDiffAt
  have hexp_sub_cd : ContDiffAt ℂ (n + 1) (fun z : ℂ ↦ Complex.exp z - 1) 0 :=
    Complex.contDiff_exp.contDiffAt.sub contDiffAt_const
  have hexp_sub_deriv (m : ℕ) (hm : 1 ≤ m) :
      iteratedDeriv m (fun z : ℂ ↦ Complex.exp z - 1) 0 = 1 := by
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le' hm
    have hd : deriv (fun z : ℂ ↦ Complex.exp z - 1) = Complex.exp := by
      ext z
      simp
    rw [iteratedDeriv_succ', hd, iteratedDeriv_eq_iterate, Complex.iter_deriv_exp,
      Complex.exp_zero]
  rw [iteratedDeriv_fun_mul hK_cd hexp_sub_cd, Finset.sum_range_succ]
  simp only [Nat.sub_self, iteratedDeriv_zero, Complex.exp_zero, sub_self, mul_zero, add_zero]
  refine Finset.sum_congr rfl fun k hk ↦ ?_
  rw [Finset.mem_range] at hk
  rw [hexp_sub_deriv (n + 1 - k) (by omega), mul_one]

/-- The `k`-th `z`-derivative of `hurwitzBernoulliKernel c` at `0` is `(-1) ^ k * B_k(c)`. -/
theorem iteratedDeriv_hurwitzBernoulliKernel_zero (k : ℕ) (c : ℂ) :
    iteratedDeriv k (hurwitzBernoulliKernel c) 0 =
      (-1 : ℂ) ^ k * Polynomial.aeval c (Polynomial.bernoulli k) := by
  have hrefl (m : ℕ) :
      (-1 : ℂ) ^ m * Polynomial.aeval c (Polynomial.bernoulli m) =
        Polynomial.aeval (1 - c) (Polynomial.bernoulli m) := by
    have h := congrArg (Polynomial.aeval c) (Polynomial.bernoulli_comp_one_sub_X m)
    simpa [Polynomial.aeval_comp] using h.symm
  rw [hrefl]
  induction k using Nat.strong_induction_on with
  | ind n ih =>
    have hev : (fun z : ℂ ↦ hurwitzBernoulliKernel c z * (Complex.exp z - 1)) =ᶠ[𝓝 0]
        (fun z : ℂ ↦ z * Complex.exp ((1 - c) * z)) := by
      filter_upwards [Metric.ball_mem_nhds (0 : ℂ) Real.two_pi_pos] with z hz
      exact hurwitzBernoulliKernel_mul_exp_sub_one c hz
    have hderiv_eq := hev.iteratedDeriv_eq (n + 1)
    have hrhs : iteratedDeriv (n + 1) (fun z : ℂ ↦ z * Complex.exp ((1 - c) * z)) 0 =
        ((n + 1 : ℕ) : ℂ) * (1 - c) ^ n := by
      have hid_cd : ContDiffAt ℂ (n + 1) (fun z : ℂ ↦ z) 0 := contDiffAt_id
      have hcexp_cd : ContDiffAt ℂ (n + 1) (fun z : ℂ ↦ Complex.exp ((1 - c) * z)) 0 :=
        (contDiff_const.mul contDiff_id).cexp.contDiffAt
      rw [iteratedDeriv_fun_mul hid_cd hcexp_cd]
      have hsum : ∑ k ∈ Finset.range (n + 2),
          ((n + 1).choose k : ℂ) * iteratedDeriv k (fun z : ℂ ↦ z) 0 *
            iteratedDeriv (n + 1 - k) (fun z : ℂ ↦ Complex.exp ((1 - c) * z)) 0 =
          ((n + 1).choose 1 : ℂ) * iteratedDeriv 1 (fun z : ℂ ↦ z) 0 *
            iteratedDeriv (n + 1 - 1) (fun z : ℂ ↦ Complex.exp ((1 - c) * z)) 0 := by
        refine Finset.sum_eq_single 1 (fun k _ hk1 ↦ ?_) (fun h1 ↦ False.elim (h1 (by simp)))
        rcases k with _ | _ | k
        · simp
        · exact False.elim (hk1 rfl)
        · have hk2 : k + 2 = (k + 1) + 1 := rfl
          have hd2 : iteratedDeriv (k + 2) (fun z : ℂ ↦ z) 0 = 0 := by
            rw [hk2, iteratedDeriv_succ', deriv_id'', iteratedDeriv_const]
            simp
          rw [hd2, mul_zero, zero_mul]
      rw [hsum, Nat.choose_one_right, iteratedDeriv_one, deriv_id'', Nat.add_sub_cancel,
        iteratedDeriv_cexp_const_mul]
      simp
    rw [iteratedDeriv_hurwitzBernoulliKernel_mul_exp_sub_one_zero, hrhs] at hderiv_eq
    have hbern := congrArg (Polynomial.aeval (1 - c)) (Polynomial.sum_bernoulli n)
    simp only [map_sum, Polynomial.aeval_monomial, Algebra.smul_def, map_mul, AlgHom.commutes,
      eq_ratCast, Rat.cast_add, Rat.cast_natCast, Rat.cast_one] at hbern
    have hn_cast : ((n : ℂ) + 1) = ((n + 1 : ℕ) : ℂ) := by push_cast; ring
    rw [hn_cast] at hbern
    have hdiff := hderiv_eq.trans hbern.symm
    rw [Finset.sum_range_succ, Finset.sum_range_succ] at hdiff
    have hprev : ∑ k ∈ Finset.range n,
        ((n + 1).choose k : ℂ) * iteratedDeriv k (hurwitzBernoulliKernel c) 0 =
        ∑ k ∈ Finset.range n,
          ((n + 1).choose k : ℂ) * Polynomial.aeval (1 - c) (Polynomial.bernoulli k) :=
      Finset.sum_congr rfl fun k hk ↦ by rw [ih k (Finset.mem_range.mp hk)]
    rw [hprev, add_right_inj, Nat.choose_succ_self_right] at hdiff
    exact mul_left_cancel₀ (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)) hdiff

/-- Dividing `iteratedDeriv k (hurwitzBernoulliKernel c) 0` by `k!` recovers
`hurwitzBernoulliCoeff k c`. -/
theorem iteratedDeriv_hurwitzBernoulliKernel_zero_div_factorial (k : ℕ) (c : ℂ) :
    iteratedDeriv k (hurwitzBernoulliKernel c) 0 / k.factorial = hurwitzBernoulliCoeff k c := by
  rw [iteratedDeriv_hurwitzBernoulliKernel_zero, hurwitzBernoulliCoeff_def]

/-! ### Exact Cauchy Taylor remainder quotient and uniform compact bounds -/

/-- The factored Cauchy Taylor remainder quotient of order `M` on `ℂ × ball 0 2`, defined by
integrating `(ζ ^ (M + 1) * (ζ - z))⁻¹ * hurwitzBernoulliKernel c ζ` around `C(0, 2)`. -/
noncomputable def hurwitzBernoulliRemainderQuot (M : ℕ) (p : ℂ × ℂ) : ℂ :=
  (2 * Real.pi * I : ℂ)⁻¹ •
    ∮ ζ in C(0, 2), (ζ ^ (M + 1) * (ζ - p.2))⁻¹ • hurwitzBernoulliKernel p.1 ζ

/-- Unfolding lemma for `hurwitzBernoulliRemainderQuot`. -/
theorem hurwitzBernoulliRemainderQuot_def (M : ℕ) (p : ℂ × ℂ) :
    hurwitzBernoulliRemainderQuot M p =
      (2 * Real.pi * I : ℂ)⁻¹ •
        ∮ ζ in C(0, 2), (ζ ^ (M + 1) * (ζ - p.2))⁻¹ • hurwitzBernoulliKernel p.1 ζ := (rfl)

/-- The Taylor remainder quotient `hurwitzBernoulliRemainderQuot M` is jointly analytic on
`ℂ × ball 0 2`. -/
theorem analyticOnNhd_hurwitzBernoulliRemainderQuot (M : ℕ) :
    AnalyticOnNhd ℂ (hurwitzBernoulliRemainderQuot M)
      (Set.univ ×ˢ Metric.ball (0 : ℂ) 2) := by
  refine AnalyticOnNhd.const_smul (c := (2 * Real.pi * I : ℂ)⁻¹) ?_
  refine analyticOnNhd_circleIntegral (c := 0) (R := 2)
    (f := fun q : (ℂ × ℂ) × ℂ ↦ (q.2 ^ (M + 1) * (q.2 - q.1.2))⁻¹ •
      hurwitzBernoulliKernel q.1.1 q.2) ?_
  intro q hq
  have hζ_norm : ‖q.2‖ = 2 := by
    simpa [abs_of_pos (two_pos : (0 : ℝ) < 2)] using mem_sphere_zero_iff_norm.mp hq.2
  have hζ_ne : q.2 ≠ 0 := norm_ne_zero_iff.mp (by linarith)
  have hz_lt : ‖q.1.2‖ < 2 := mem_ball_zero_iff.mp hq.1.2
  have hsub_ne : q.2 - q.1.2 ≠ 0 := by
    intro h
    rw [sub_eq_zero.mp h] at hζ_norm
    linarith
  have hζ_ball : q.2 ∈ Metric.ball (0 : ℂ) (2 * Real.pi) := by
    rw [mem_ball_zero_iff, hζ_norm]
    linarith [Real.pi_gt_three]
  have hden : AnalyticAt ℂ (fun x : (ℂ × ℂ) × ℂ ↦ x.2 ^ (M + 1) * (x.2 - x.1.2)) q :=
    (analyticAt_snd.pow (M + 1)).mul (analyticAt_snd.sub (analyticAt_snd.comp analyticAt_fst))
  have hproj : AnalyticAt ℂ (fun x : (ℂ × ℂ) × ℂ ↦ (x.1.1, x.2)) q :=
    (analyticAt_fst.comp analyticAt_fst).prod analyticAt_snd
  have hK : AnalyticAt ℂ (fun x : (ℂ × ℂ) × ℂ ↦ hurwitzBernoulliKernel x.1.1 x.2) q :=
    AnalyticAt.comp (f := fun x : (ℂ × ℂ) × ℂ ↦ (x.1.1, x.2))
      (analyticOnNhd_hurwitzBernoulliKernel (q.1.1, q.2) ⟨mem_univ _, hζ_ball⟩) hproj
  exact (hden.inv (mul_ne_zero (pow_ne_zero _ hζ_ne) hsub_ne)).smul hK

private theorem hurwitzBernoulliCoeff_mul_pow_eq_circleIntegral (k : ℕ) (c z : ℂ) :
    hurwitzBernoulliCoeff k c * z ^ k =
      (2 * Real.pi * I : ℂ)⁻¹ *
        ∮ ζ in C(0, 2), (z ^ k / ζ ^ (k + 1)) * hurwitzBernoulliKernel c ζ := by
  have hd := differentiableOn_hurwitzBernoulliKernel_closedBall_two c
  have h2pi : (2 * Real.pi * I : ℂ) ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) I_ne_zero
  have hk := hd.circleIntegral_one_div_sub_center_pow_smul (two_pos : (0 : ℝ) < 2) k
  simp only [sub_zero, smul_eq_mul] at hk
  have hpull : (∮ ζ in C(0, 2), (z ^ k / ζ ^ (k + 1)) * hurwitzBernoulliKernel c ζ) =
      z ^ k * ∮ ζ in C(0, 2), (1 / ζ ^ (k + 1)) * hurwitzBernoulliKernel c ζ := by
    rw [← circleIntegral.integral_const_mul]
    exact circleIntegral.integral_congr (by positivity) fun _ _ ↦ by ring
  rw [hpull, hk, ← iteratedDeriv_hurwitzBernoulliKernel_zero_div_factorial]
  have hfac : (k.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
  field_simp [h2pi, hfac]

/-- Exact Taylor remainder factorization on `ball 0 2`: subtracting the `M`-th Bernoulli polynomial
Taylor partial sum from `hurwitzBernoulliKernel c z` leaves
`z ^ (M + 1) * hurwitzBernoulliRemainderQuot M (c, z)`. -/
theorem hurwitzBernoulliKernel_sub_sum_eq (M : ℕ) (c : ℂ) {z : ℂ}
    (hz : z ∈ Metric.ball (0 : ℂ) 2) :
    hurwitzBernoulliKernel c z -
        ∑ k ∈ Finset.range (M + 1), hurwitzBernoulliCoeff k c * z ^ k =
      z ^ (M + 1) * hurwitzBernoulliRemainderQuot M (c, z) := by
  have hd := differentiableOn_hurwitzBernoulliKernel_closedBall_two c
  have hcont_sphere : ContinuousOn (hurwitzBernoulliKernel c) (Metric.sphere (0 : ℂ) 2) :=
    hd.continuousOn.mono sphere_subset_closedBall
  have hcauchy : hurwitzBernoulliKernel c z =
      (2 * Real.pi * I : ℂ)⁻¹ *
        ∮ ζ in C(0, 2), (ζ - z)⁻¹ * hurwitzBernoulliKernel c ζ := by
    have h := (hd.mono closure_ball_subset_closedBall).diffContOnCl
      |>.two_pi_i_inv_smul_circleIntegral_sub_inv_smul hz
    simpa only [smul_eq_mul] using h.symm
  have hint_main : CircleIntegrable
      (fun ζ : ℂ ↦ (ζ - z)⁻¹ * hurwitzBernoulliKernel c ζ) 0 2 := by
    refine ContinuousOn.circleIntegrable (by positivity) ?_
    refine (ContinuousOn.inv₀ (continuousOn_id.sub continuousOn_const) fun ζ hζ hsub ↦ ?_).mul
      hcont_sphere
    have hζ_norm : ‖ζ‖ = 2 := mem_sphere_zero_iff_norm.mp hζ
    have hsub' : ζ - z = 0 := hsub
    rw [sub_eq_zero.mp hsub'] at hζ_norm
    linarith [mem_ball_zero_iff.mp hz]
  have hint_term (k : ℕ) : CircleIntegrable
      (fun ζ : ℂ ↦ (z ^ k / ζ ^ (k + 1)) * hurwitzBernoulliKernel c ζ) 0 2 := by
    refine ContinuousOn.circleIntegrable (by positivity) ?_
    refine (continuousOn_const.div (continuousOn_id.pow (k + 1)) fun ζ hζ ↦ ?_).mul hcont_sphere
    have hζ_norm : ‖ζ‖ = 2 := mem_sphere_zero_iff_norm.mp hζ
    have hζ_ne : ζ ≠ 0 := norm_ne_zero_iff.mp (by linarith)
    exact pow_ne_zero (k + 1) hζ_ne
  have hsum_eq : (∑ k ∈ Finset.range (M + 1), hurwitzBernoulliCoeff k c * z ^ k) =
      (2 * Real.pi * I : ℂ)⁻¹ *
        ∮ ζ in C(0, 2), (∑ k ∈ Finset.range (M + 1),
          (z ^ k / ζ ^ (k + 1)) * hurwitzBernoulliKernel c ζ) := by
    simp_rw [hurwitzBernoulliCoeff_mul_pow_eq_circleIntegral, ← Finset.mul_sum,
      ← circleIntegral.integral_fun_sum (fun k _ ↦ hint_term k)]
  rw [hcauchy, hsum_eq, ← mul_sub,
    ← circleIntegral.integral_sub hint_main (CircleIntegrable.fun_sum _ fun k _ ↦ hint_term k),
    hurwitzBernoulliRemainderQuot_def]
  simp only [smul_eq_mul]
  conv_rhs =>
    rw [← mul_assoc, mul_comm (z ^ (M + 1)), mul_assoc, ← circleIntegral.integral_const_mul]
  refine congrArg ((2 * Real.pi * I : ℂ)⁻¹ * ·)
    (circleIntegral.integral_congr (two_pos : (0 : ℝ) < 2).le fun ζ hζ ↦ ?_)
  have hζ_norm : ‖ζ‖ = 2 := mem_sphere_zero_iff_norm.mp hζ
  have hζ_ne : ζ ≠ 0 := norm_ne_zero_iff.mp (by linarith)
  have hsub_ne : ζ - z ≠ 0 := fun h ↦ by
    rw [sub_eq_zero.mp h] at hζ_norm; linarith [mem_ball_zero_iff.mp hz]
  have hgeom : (ζ - z)⁻¹ - ∑ k ∈ Finset.range (M + 1), z ^ k / ζ ^ (k + 1) =
      z ^ (M + 1) / (ζ ^ (M + 1) * (ζ - z)) := by
    clear hsum_eq
    induction M with
    | zero => rw [Finset.sum_range_one]; simp only [pow_zero]; field_simp [hζ_ne, hsub_ne]; ring
    | succ m ihm =>
      rw [Finset.sum_range_succ, sub_add_eq_sub_sub, ihm]
      simp only [pow_succ]; field_simp [hζ_ne, hsub_ne]; ring
  rw [← Finset.sum_mul, ← sub_mul, hgeom, div_eq_mul_inv, mul_assoc]

/-- Stepping `M` to `M + 1` in `hurwitzBernoulliRemainderQuot` extracts the `(M + 1)`-st Bernoulli
Taylor coefficient on `ball 0 2`. -/
theorem hurwitzBernoulliRemainderQuot_eq_add_mul (M : ℕ) (c : ℂ) {z : ℂ}
    (hz : z ∈ Metric.ball (0 : ℂ) 2) :
    hurwitzBernoulliRemainderQuot M (c, z) =
      hurwitzBernoulliCoeff (M + 1) c + z * hurwitzBernoulliRemainderQuot (M + 1) (c, z) := by
  -- Both sides are analytic in `z` on `ball 0 2`, so it suffices to check `z ≠ 0` by continuity,
  -- or cancel `z ^ (M + 1)` away from `0` and pass to the limit at `0`.
  let lhs : ℂ → ℂ := fun w ↦ hurwitzBernoulliRemainderQuot M (c, w)
  let rhs : ℂ → ℂ := fun w ↦
    hurwitzBernoulliCoeff (M + 1) c + w * hurwitzBernoulliRemainderQuot (M + 1) (c, w)
  have h_eq_ne {w : ℂ} (hw : w ∈ Metric.ball (0 : ℂ) 2) (hw0 : w ≠ 0) : lhs w = rhs w := by
    have hM := hurwitzBernoulliKernel_sub_sum_eq M c hw
    have hM1 := hurwitzBernoulliKernel_sub_sum_eq (M + 1) c hw
    rw [Finset.sum_range_succ, sub_add_eq_sub_sub, hM, pow_succ] at hM1
    have hmul : w ^ (M + 1) * lhs w = w ^ (M + 1) * rhs w := by
      dsimp only [lhs, rhs]
      linear_combination hM1
    exact mul_left_cancel₀ (pow_ne_zero (M + 1) hw0) hmul
  rcases ne_or_eq z 0 with hz0 | rfl
  · exact h_eq_ne hz hz0
  · have hlhs_cont : ContinuousAt lhs 0 :=
      ((analyticOnNhd_hurwitzBernoulliRemainderQuot M (c, 0)
        ⟨mem_univ c, Metric.mem_ball_self two_pos⟩).comp
        (analyticAt_const.prod analyticAt_id)).continuousAt
    have hrhs_cont : ContinuousAt rhs 0 :=
      continuousAt_const.add <| continuousAt_id.mul
        ((analyticOnNhd_hurwitzBernoulliRemainderQuot (M + 1) (c, 0)
          ⟨mem_univ c, Metric.mem_ball_self two_pos⟩).comp
          (analyticAt_const.prod analyticAt_id)).continuousAt
    have hev : lhs =ᶠ[𝓝[≠] (0 : ℂ)] rhs := by
      filter_upwards [nhdsWithin_le_nhds (Metric.ball_mem_nhds (0 : ℂ) two_pos),
        self_mem_nhdsWithin] with w hw hw0
      exact h_eq_ne hw hw0
    exact tendsto_nhds_unique (hlhs_cont.tendsto.mono_left nhdsWithin_le_nhds)
      ((hrhs_cont.tendsto.mono_left nhdsWithin_le_nhds).congr' hev.symm)

/-- Every iterated `c`-derivative of `hurwitzBernoulliRemainderQuot M` is jointly analytic on
`ℂ × ball 0 2`. -/
theorem analyticOnNhd_iteratedDeriv_hurwitzBernoulliRemainderQuot (M r : ℕ) :
    AnalyticOnNhd ℂ
      (fun p : ℂ × ℂ ↦ iteratedDeriv r (fun c' ↦ hurwitzBernoulliRemainderQuot M (c', p.2)) p.1)
      (Set.univ ×ˢ Metric.ball (0 : ℂ) 2) := by
  induction r with
  | zero =>
    simpa only [iteratedDeriv_zero] using analyticOnNhd_hurwitzBernoulliRemainderQuot M
  | succ r ihr =>
    let g : ℂ × ℂ → ℂ :=
      fun p ↦ iteratedDeriv r (fun c' ↦ hurwitzBernoulliRemainderQuot M (c', p.2)) p.1
    have hU_open : IsOpen (Set.univ ×ˢ Metric.ball (0 : ℂ) 2) :=
      (isOpen_univ (X := ℂ)).prod Metric.isOpen_ball
    intro p hp
    have han : AnalyticAt ℂ (fun q : ℂ × ℂ ↦ fderiv ℂ g q ((1 : ℂ), (0 : ℂ))) p :=
      ((ContinuousLinearMap.apply ℂ ℂ ((1 : ℂ), (0 : ℂ))).analyticAt _).comp (ihr p hp).fderiv
    refine han.congr ?_
    filter_upwards [hU_open.mem_nhds hp] with q hq
    rw [iteratedDeriv_succ]
    have hd := ((ihr (q.1, q.2) ⟨mem_univ _, hq.2⟩).differentiableAt.hasFDerivAt.comp
      (𝕜 := ℂ) q.1 (hasFDerivAt_prodMk_left (𝕜 := ℂ) q.1 q.2)).hasDerivAt.deriv
    simpa [Function.comp_def, g] using hd.symm

/-- On any compact parameter set `K ⊆ ℂ` and the closed unit disc `closedBall 0 1`, every fixed
`c`-derivative of the `M`-th Bernoulli Taylor remainder is bounded by `C * ‖z‖ ^ (M + 1)`. -/
theorem _root_.IsCompact.exists_norm_iteratedDeriv_hurwitzBernoulliKernel_sub_sum_le
    {K : Set ℂ} (hK : IsCompact K) (M r : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ c ∈ K, ∀ z ∈ Metric.closedBall (0 : ℂ) 1,
      ‖iteratedDeriv r
          (fun c' ↦ hurwitzBernoulliKernel c' z -
            ∑ k ∈ Finset.range (M + 1), hurwitzBernoulliCoeff k c' * z ^ k) c‖ ≤
        C * ‖z‖ ^ (M + 1) := by
  have hsub : K ×ˢ Metric.closedBall (0 : ℂ) 1 ⊆ Set.univ ×ˢ Metric.ball (0 : ℂ) 2 :=
    prod_mono (subset_univ K) (Metric.closedBall_subset_ball one_lt_two)
  have hcont : ContinuousOn
      (fun p : ℂ × ℂ ↦ iteratedDeriv r (fun c' ↦ hurwitzBernoulliRemainderQuot M (c', p.2)) p.1)
      (K ×ˢ Metric.closedBall (0 : ℂ) 1) :=
    (analyticOnNhd_iteratedDeriv_hurwitzBernoulliRemainderQuot M r).continuousOn.mono hsub
  obtain ⟨B, hB⟩ := (hK.prod (isCompact_closedBall (0 : ℂ) 1)).exists_bound_of_continuousOn hcont
  refine ⟨max B 0, le_max_right B 0, fun c hc z hz ↦ ?_⟩
  have hz_ball : z ∈ Metric.ball (0 : ℂ) 2 :=
    Metric.closedBall_subset_ball one_lt_two hz
  have hfun : (fun c' ↦ hurwitzBernoulliKernel c' z -
      ∑ k ∈ Finset.range (M + 1), hurwitzBernoulliCoeff k c' * z ^ k) =
      fun c' ↦ z ^ (M + 1) * hurwitzBernoulliRemainderQuot M (c', z) :=
    funext fun c' ↦ hurwitzBernoulliKernel_sub_sum_eq M c' hz_ball
  rw [hfun, iteratedDeriv_const_mul_field, norm_mul, norm_pow, mul_comm]
  exact mul_le_mul_of_nonneg_right ((hB (c, z) ⟨hc, hz⟩).trans (le_max_left B 0)) (by positivity)

/-- Real-interval specialization of
`IsCompact.exists_norm_iteratedDeriv_hurwitzBernoulliKernel_sub_sum_le`: for compact `K ⊆ ℂ`,
`t ∈ [0, 1]`, and any `c`-derivative order `r`, the `M`-th Taylor remainder is bounded by
`C * t ^ (M + 1)`. -/
theorem _root_.IsCompact.exists_norm_iteratedDeriv_hurwitzBernoulliKernel_sub_sum_ofReal_le
    {K : Set ℂ} (hK : IsCompact K) (M r : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ c ∈ K, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖iteratedDeriv r
          (fun c' ↦ hurwitzBernoulliKernel c' t -
            ∑ k ∈ Finset.range (M + 1), hurwitzBernoulliCoeff k c' * (t : ℂ) ^ k) c‖ ≤
        C * t ^ (M + 1) := by
  obtain ⟨C, hC0, hC⟩ := hK.exists_norm_iteratedDeriv_hurwitzBernoulliKernel_sub_sum_le M r
  refine ⟨C, hC0, fun c hc t ht ↦ ?_⟩
  have ht_ball : (t : ℂ) ∈ Metric.closedBall (0 : ℂ) 1 := by
    rw [mem_closedBall_zero_iff, Complex.norm_real, Real.norm_of_nonneg ht.1]
    exact ht.2
  simpa [Complex.norm_real, Real.norm_of_nonneg ht.1] using hC c hc (t : ℂ) ht_ball

end TauCeti
