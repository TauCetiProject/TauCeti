/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LSeries.Dirichlet
public import TauCeti.Analysis.Meromorphic.Divisor

/-!
# Meromorphy and poles of the completed Riemann zeta function

Mathlib's `completedRiemannZeta` is `Λ(s) = Λ₀(s) - 1/s - 1/(1 - s)` with `Λ₀` entire
(`completedRiemannZeta_eq`, `differentiable_completedZeta₀`). This file reads off the
consequences in the language of meromorphic functions: `Λ` is meromorphic on `ℂ`, analytic away
from `0` and `1`, and has a simple pole, of order exactly `-1`, at each of `0` and `1`. Since
`ζ(s) = Λ(s) / Γ_ℝ(s)` for `s ≠ 0` and `1 / Γ_ℝ` is entire, the Riemann zeta function itself is
meromorphic on `ℂ` too; this is what lets a factorization through `ζ` serve as a meromorphic
continuation.

## Main results

* `TauCeti.meromorphic_completedRiemannZeta`
* `TauCeti.analyticAt_completedRiemannZeta`
* `TauCeti.meromorphicOrderAt_completedRiemannZeta_zero`,
  `TauCeti.meromorphicOrderAt_completedRiemannZeta_one`
* `TauCeti.meromorphic_riemannZeta`: the uncompleted function `riemannZeta` is meromorphic on `ℂ`
  as well.
* `TauCeti.meromorphicOrderAt_completedRiemannZeta_neg_two_mul_nat_add_one`: `Λ` is regular and
  nonzero at the trivial zeros `-2(n + 1)` of `riemannZeta`, where `Γ_ℝ` has its poles.
* `TauCeti.zero_lt_divisor_completedRiemannZeta_iff`: the points of positive divisor of `Λ` are
  exactly the zeros of `riemannZeta` excluded neither by `RiemannHypothesis` as trivial zeros nor
  as the pole `1`.
-/

public section

open Complex Filter Topology Set

namespace TauCeti

/-- Mathlib's completed Riemann zeta function is meromorphic on `ℂ`. -/
theorem meromorphic_completedRiemannZeta : Meromorphic completedRiemannZeta := by
  intro z
  have h₀ : AnalyticAt ℂ completedRiemannZeta₀ z := differentiable_completedZeta₀.analyticAt z
  rw [funext completedRiemannZeta_eq]
  fun_prop

/-- Mathlib's completed Riemann zeta function is analytic away from `0` and `1`. -/
theorem analyticAt_completedRiemannZeta {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) :
    AnalyticAt ℂ completedRiemannZeta s := by
  have h₀ : AnalyticAt ℂ completedRiemannZeta₀ s := differentiable_completedZeta₀.analyticAt s
  have h1' : 1 - s ≠ 0 := sub_ne_zero.2 h1.symm
  rw [funext completedRiemannZeta_eq]
  fun_prop (disch := assumption)

/-- The completed Riemann zeta function has a simple pole at `0`. -/
theorem meromorphicOrderAt_completedRiemannZeta_zero :
    meromorphicOrderAt completedRiemannZeta 0 = (-1 : ℤ) := by
  have h₀ : AnalyticAt ℂ completedRiemannZeta₀ 0 := differentiable_completedZeta₀.analyticAt 0
  have h1 : (1 : ℂ) - 0 ≠ 0 := by norm_num
  refine (meromorphicOrderAt_eq_int_iff (meromorphic_completedRiemannZeta 0)).2
    ⟨fun z ↦ z * completedRiemannZeta₀ z - 1 - z / (1 - z), by fun_prop (disch := assumption),
      by simp, ?_⟩
  filter_upwards [self_mem_nhdsWithin, eventually_ne_nhdsWithin (zero_ne_one (α := ℂ))]
    with z (hz : z ≠ 0) hz1
  have hz1' : 1 - z ≠ 0 := sub_ne_zero.2 (Ne.symm hz1)
  rw [completedRiemannZeta_eq, sub_zero, zpow_neg_one, smul_eq_mul]
  field_simp

/-- The completed Riemann zeta function has a simple pole at `1`. -/
theorem meromorphicOrderAt_completedRiemannZeta_one :
    meromorphicOrderAt completedRiemannZeta 1 = (-1 : ℤ) := by
  -- Transport the pole at `0` along the functional equation `completedRiemannZeta_one_sub`.
  have h := meromorphicOrderAt_comp_of_deriv_ne_zero (f := completedRiemannZeta)
    (g := fun z : ℂ ↦ 1 - z) (x := 1) (by fun_prop) (by simp)
  rw [sub_self, meromorphicOrderAt_completedRiemannZeta_zero] at h
  rw [← h]
  congr 1
  exact funext fun z ↦ (completedRiemannZeta_one_sub z).symm

/-- Mathlib's Riemann zeta function is meromorphic on `ℂ`. Away from `1` it is analytic
(`analyticOn_riemannZeta`); its pole at `1` is that of `completedRiemannZeta`. -/
theorem meromorphic_riemannZeta : Meromorphic riemannZeta := by
  intro z
  rcases eq_or_ne z 1 with rfl | hz
  · refine ((meromorphic_completedRiemannZeta 1).mul
      (Complex.differentiable_Gammaℝ_inv.analyticAt 1).meromorphicAt).congr ?_
    filter_upwards [nhdsWithin_le_nhds (eventually_ne_nhds one_ne_zero)] with s hs
    rw [riemannZeta_def_of_ne_zero hs, div_eq_mul_inv, Pi.mul_apply]
  · exact (analyticOn_riemannZeta z hz).meromorphicAt

/-- The completed Riemann zeta function does not vanish on the half-plane `1 < re s`. -/
theorem completedRiemannZeta_ne_zero_of_one_lt_re {s : ℂ} (hs : 1 < s.re) :
    completedRiemannZeta s ≠ 0 := by
  have hs0 : s ≠ 0 := by
    rintro rfl
    norm_num at hs
  intro h
  apply riemannZeta_ne_zero_of_one_lt_re hs
  rw [riemannZeta_def_of_ne_zero hs0, h, zero_div]

/-- The completed Riemann zeta function does not vanish at the trivial zeros of `riemannZeta`. -/
theorem completedRiemannZeta_neg_two_mul_nat_add_one_ne_zero (n : ℕ) :
    completedRiemannZeta (-2 * (n + 1)) ≠ 0 := by
  rw [← completedRiemannZeta_one_sub]
  apply completedRiemannZeta_ne_zero_of_one_lt_re
  simp only [sub_re, one_re, mul_re, neg_re, re_ofNat, add_re, natCast_re, neg_im, im_ofNat,
    add_im, natCast_im, one_im]
  linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]

/-- The completed Riemann zeta function is regular and nonzero at the trivial zeros of
`riemannZeta`: there the zero of `riemannZeta` comes from the pole of `Γ_ℝ`. -/
theorem meromorphicOrderAt_completedRiemannZeta_neg_two_mul_nat_add_one (n : ℕ) :
    meromorphicOrderAt completedRiemannZeta (-2 * (n + 1)) = 0 := by
  have h0 : (-2 * (n + 1) : ℂ) ≠ 0 := by
    have : (n : ℂ) + 1 ≠ 0 := by exact_mod_cast n.succ_ne_zero
    simpa using this
  have h1 : (-2 * (n + 1) : ℂ) ≠ 1 := by
    intro h
    have := congrArg re h
    simp only [mul_re, neg_re, re_ofNat, add_re, natCast_re, one_re, neg_im, im_ofNat, add_im,
      natCast_im, one_im] at this
    linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
  rw [(analyticAt_completedRiemannZeta h0 h1).meromorphicOrderAt_eq,
    analyticOrderAt_eq_zero.2 (Or.inr (completedRiemannZeta_neg_two_mul_nat_add_one_ne_zero n))]
  rfl

/-- The completed Riemann zeta function does not vanish identically near any point. -/
theorem meromorphicOrderAt_completedRiemannZeta_ne_top (s : ℂ) :
    meromorphicOrderAt completedRiemannZeta s ≠ ⊤ := by
  have h2 : meromorphicOrderAt completedRiemannZeta 2 ≠ ⊤ := by
    rw [(analyticAt_completedRiemannZeta two_ne_zero (by norm_num)).meromorphicOrderAt_eq,
      analyticOrderAt_eq_zero.2 (Or.inr (completedRiemannZeta_ne_zero_of_one_lt_re (by norm_num)))]
    simp
  exact (meromorphicOn_univ.2 meromorphic_completedRiemannZeta)
    |>.meromorphicOrderAt_ne_top_of_isPreconnected isPreconnected_univ (mem_univ 2) (mem_univ s) h2

/-- The divisor of the completed Riemann zeta function is `-1` at its pole `0`. -/
theorem divisor_completedRiemannZeta_zero :
    MeromorphicOn.divisor completedRiemannZeta univ 0 = -1 := by
  rw [(meromorphicOn_univ.2 meromorphic_completedRiemannZeta).divisor_apply (mem_univ 0),
    meromorphicOrderAt_completedRiemannZeta_zero]
  rfl

/-- The divisor of the completed Riemann zeta function is `-1` at its pole `1`. -/
theorem divisor_completedRiemannZeta_one :
    MeromorphicOn.divisor completedRiemannZeta univ 1 = -1 := by
  rw [(meromorphicOn_univ.2 meromorphic_completedRiemannZeta).divisor_apply (mem_univ 1),
    meromorphicOrderAt_completedRiemannZeta_one]
  rfl

/-- The completed Riemann zeta function has a zero of positive multiplicity exactly at the zeros
of `riemannZeta` which are neither trivial zeros `-2(n + 1)` nor the junk value at the pole `1`,
the hypotheses under which `RiemannHypothesis` constrains a zero. -/
theorem zero_lt_divisor_completedRiemannZeta_iff {s : ℂ} :
    0 < MeromorphicOn.divisor completedRiemannZeta univ s ↔
      riemannZeta s = 0 ∧ (¬∃ n : ℕ, s = -2 * (n + 1)) ∧ s ≠ 1 := by
  rcases eq_or_ne s 0 with rfl | hs0
  · simp [divisor_completedRiemannZeta_zero, riemannZeta_zero]
  rcases eq_or_ne s 1 with rfl | hs1
  · simp [divisor_completedRiemannZeta_one]
  rw [(meromorphicOn_univ.2 meromorphic_completedRiemannZeta).zero_lt_divisor_iff_of_analyticAt
    (analyticAt_completedRiemannZeta hs0 hs1) (mem_univ s)
    (meromorphicOrderAt_completedRiemannZeta_ne_top s),
    riemannZeta_def_of_ne_zero hs0, div_eq_zero_iff]
  constructor
  · intro h
    refine ⟨Or.inl h, ?_, hs1⟩
    rintro ⟨n, rfl⟩
    exact completedRiemannZeta_neg_two_mul_nat_add_one_ne_zero n h
  · rintro ⟨h | h, htriv, -⟩
    · exact h
    · obtain ⟨n, rfl⟩ := Gammaℝ_eq_zero_iff.1 h
      cases n with
      | zero => simp at hs0
      | succ m => exact absurd ⟨m, by push_cast; ring⟩ htriv

end TauCeti
