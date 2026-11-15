/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Hadamard.OrderOne
import Mathlib.Analysis.Calculus.Deriv.Star
import TauCeti.Analysis.Complex.GrowthOrder.Zero.Summability
import TauCeti.NumberTheory.LFunctions.Zeros.Divisor

/-!
# Real-part cancellation in Hadamard expansions under functional symmetry

Entire completions `f` of L-functions have growth order at most `1`, satisfy `f 0 ≠ 0` after pole
clearing, have zeros whose real parts are bounded above (`Re ρ ≤ B`, classically `Re ρ ≤ 1` from
Euler-product nonvanishing), and obey a critical-line functional-conjugation identity
`f (1 - z) = c * conj (f (conj z))` obtained by combining the functional equation relating
`f (1 - z)` to the dual completion with conjugate symmetry of the dual. Writing the symmetry in
this combined `1 - conj` form covers both self-dual completions (such as `zetaEntireCompletion`,
with `c = 1`) and non-self-dual completions (such as primitive complex Dirichlet characters, with
`c` equal to the root number).

In the generic order-at-most-one Hadamard expansion
`logDeriv f s = logDeriv f 0 + ∑' ρ, m_ρ * (1 / (s - ρ) + 1 / ρ)`, the linear coefficient
`logDeriv f 0` is an a priori unknown global constant. The hypotheses here eliminate its real part
so that downstream zero-free region and real-zero arguments see a pure zero sum:
* `f 0 ≠ 0` ensures `0` is not a zero of `f` (so `E₁(ρ⁻¹ * s)` and `1 / ρ` are nonsingular at every
  zero) and, via `f (1 - z) = c * conj (f (conj z))`, forces `c ≠ 0` and `f 1 ≠ 0`.
* Combining `Re ρ ≤ B` with `1 - conj` zero symmetry confines all zeros to `1 - B ≤ Re ρ ≤ B`, so
  `∑' ρ, m_ρ * Re (1 / ρ)` and `∑' ρ, m_ρ * Re (1 / (s - ρ))` converge separately
  (`TauCeti.OrderLE.summable_divisor_toNat_mul_re_one_div_of_re_le`,
  `TauCeti.OrderLE.summable_divisor_toNat_mul_re_one_div_sub_of_re_le`).
* Differentiating `f (1 - z) = c * conj (f (conj z))` gives
  `logDeriv f (1 - conj z) = -conj (logDeriv f z)`, hence `Re (logDeriv f 1) = -Re (logDeriv f 0)`,
  while permuting the zeros by `ρ ↦ 1 - conj ρ` (`TauCeti.divisorSupportOneSubConj`) identifies
  `∑' ρ, m_ρ * Re (1 / (1 - ρ))` with `∑' ρ, m_ρ * Re (1 / ρ)`. Evaluating the real-part expansion
  at `s = 1` yields `Re (logDeriv f 0) = -∑' ρ, m_ρ * Re (1 / ρ)` and cancels the constant term
  from `Re (logDeriv f s)` at every non-zero `s`.

## Main results

* `TauCeti.logDeriv_one_sub_conj_nhds_of_ne_zero`,
  `TauCeti.logDeriv_one_sub_conj_nhds`, `TauCeti.logDeriv_one_sub_conj`: local germ and
  global reflection identities `logDeriv f (1 - conj z) = -conj (logDeriv f z)` under
  `f (1 - conj w) = u * conj (f w)`.
* `TauCeti.OrderLE.summable_divisor_toNat_mul_re_one_div_of_re_le`,
  `TauCeti.OrderLE.summable_divisor_toNat_mul_re_one_div_sub_of_re_le`: separate summability of
  `m_ρ * Re (1 / ρ)` and `m_ρ * Re (1 / (s - ρ))` from a one-sided bound `Re ρ ≤ B` and
  `f (1 - z) = c * conj (f (conj z))`.
* `TauCeti.OrderLE.re_logDeriv_zero_eq_neg_tsum`:
  `Re (logDeriv f 0) = -∑' ρ, m_ρ * Re (1 / ρ)` for an entire `f` of order at most `1` with
  `f 0 ≠ 0`, `Re ρ ≤ B` on zeros, and `f (1 - z) = c * conj (f (conj z))`.
* `TauCeti.OrderLE.re_logDeriv_eq_tsum`,
  `TauCeti.OrderLE.sum_divisor_toNat_mul_re_one_div_sub_le_re_logDeriv`: the constant-free
  expansion `Re (logDeriv f s) = ∑' ρ, m_ρ * Re (1 / (s - ρ))` away from the zeros of `f`, and
  its finite retained-zero subsum lower bound when `Re ρ ≤ Re s` on zeros.

## References

* H. Davenport, *Multiplicative Number Theory*, 3rd ed., GTM 74, Chapters 11–12.
* H. L. Montgomery and R. C. Vaughan, *Multiplicative Number Theory I*, Cambridge University
  Press, 2007, §§10.2 and 11.1.
-/

public section

open Complex ComplexConjugate Filter Set Topology
open scoped BigOperators

namespace TauCeti

/-- **Local logarithmic-derivative symmetry across the critical line, for a nonzero multiplier.**
If `(fun w ↦ f (1 - conj w)) =ᶠ[𝓝 z] fun w ↦ u * conj (f w)` and `u ≠ 0`, then
`logDeriv f (1 - conj z) = -conj (logDeriv f z)`, with no differentiability assumption on `f`. -/
theorem logDeriv_one_sub_conj_nhds_of_ne_zero {f : ℂ → ℂ} {u z : ℂ}
    (hfe : (fun w : ℂ ↦ f (1 - conj w)) =ᶠ[𝓝 z] fun w : ℂ ↦ u * conj (f w)) (hu : u ≠ 0) :
    logDeriv f (1 - conj z) = -conj (logDeriv f z) := by
  have hconj : Tendsto conj (𝓝 (conj z)) (𝓝 z) := by
    simpa using Complex.continuous_conj.tendsto (conj z)
  have hEq : (fun w : ℂ ↦ f (1 - w)) =ᶠ[𝓝 (conj z)] fun w : ℂ ↦ u * (conj ∘ f ∘ conj) w := by
    filter_upwards [hconj.eventually hfe] with w hw
    simpa [Function.comp_def] using hw
  have hcongr : logDeriv (fun w : ℂ ↦ f (1 - w)) (conj z) =
      logDeriv (fun w : ℂ ↦ u * (conj ∘ f ∘ conj) w) (conj z) := by
    rw [logDeriv_apply, logDeriv_apply, hEq.deriv_eq, hEq.eq_of_nhds]
  have hlhs : logDeriv (fun w : ℂ ↦ f (1 - w)) (conj z) = -logDeriv f (1 - conj z) := by
    rw [logDeriv_apply, logDeriv_apply, deriv_comp_const_sub, neg_div]
  have hrhs : logDeriv (fun w : ℂ ↦ u * (conj ∘ f ∘ conj) w) (conj z) = conj (logDeriv f z) := by
    rw [logDeriv_const_mul _ _ hu, logDeriv_apply, logDeriv_apply, deriv_conj_conj]
    simp
  exact neg_eq_iff_eq_neg.mp (by rw [← hlhs, hcongr, hrhs])

/-- **Local logarithmic-derivative symmetry across the critical line.** If
`(fun w ↦ f (1 - conj w)) =ᶠ[𝓝 z] fun w ↦ u * conj (f w)` and the same germ identity holds at
`1 - conj z`, then `logDeriv f (1 - conj z) = -conj (logDeriv f z)` (including the degenerate case
`u = 0`). -/
theorem logDeriv_one_sub_conj_nhds {f : ℂ → ℂ} {u z : ℂ}
    (hfe : (fun w : ℂ ↦ f (1 - conj w)) =ᶠ[𝓝 z] fun w : ℂ ↦ u * conj (f w))
    (hfe' : (fun w : ℂ ↦ f (1 - conj w)) =ᶠ[𝓝 (1 - conj z)] fun w : ℂ ↦ u * conj (f w)) :
    logDeriv f (1 - conj z) = -conj (logDeriv f z) := by
  rcases eq_or_ne u 0 with rfl | hu
  · have h1 : f (1 - conj z) = 0 := by simpa using hfe.eq_of_nhds
    have h2 : f z = 0 := by simpa [sub_sub_cancel] using hfe'.eq_of_nhds
    simp [logDeriv_apply, h1, h2]
  · exact logDeriv_one_sub_conj_nhds_of_ne_zero hfe hu

/-- Under a whole-plane functional-conjugation symmetry `f (1 - z) = u * conj (f (conj z))`, the
logarithmic derivative satisfies `logDeriv f (1 - conj z) = -conj (logDeriv f z)`. -/
theorem logDeriv_one_sub_conj {f : ℂ → ℂ} {u : ℂ}
    (hfe : ∀ z : ℂ, f (1 - z) = u * conj (f (conj z))) (z : ℂ) :
    logDeriv f (1 - conj z) = -conj (logDeriv f z) :=
  logDeriv_one_sub_conj_nhds
    (Eventually.of_forall fun w ↦ by simpa using hfe (conj w))
    (Eventually.of_forall fun w ↦ by simpa using hfe (conj w))

namespace OrderLE

/-- Under `f (1 - z) = c * conj (f (conj z))`, an upper bound `ρ.re ≤ B` on the real parts of all
zeros also yields `1 - ρ.re ≤ B`, hence `|ρ.re| ≤ max B |1 - B|`. -/
private theorem abs_re_le_of_re_le {f : ℂ → ℂ} {B : ℝ} (hre : ∀ ρ : ℂ, f ρ = 0 → ρ.re ≤ B)
    {c : ℂ} (hfe : ∀ z : ℂ, f (1 - z) = c * conj (f (conj z)))
    (ρ : ℂ) (hρ : f ρ = 0) : |ρ.re| ≤ max B |1 - B| := by
  have hsym : f (1 - conj ρ) = 0 := by
    have := hfe (conj ρ)
    simpa [hρ] using this
  have h1 := hre (1 - conj ρ) hsym
  simp only [sub_re, one_re, conj_re] at h1
  have hlow : -max B |1 - B| ≤ 1 - B := by
    have := neg_abs_le (1 - B)
    linarith [le_max_right B |1 - B|]
  exact abs_le.mpr ⟨by linarith, (hre ρ hρ).trans (le_max_left _ _)⟩

/-- Under `f (1 - z) = c * conj (f (conj z))` and a one-sided bound `Re ρ ≤ B` on all zeros of an
entire function `f` of order less than two, the real-part series `ρ ↦ m_ρ * Re (1 / ρ)` is
summable on the divisor support. -/
theorem summable_divisor_toNat_mul_re_one_div_of_re_le {f : ℂ → ℂ} {A : ℝ} (h : OrderLE f A)
    (hf : Differentiable ℂ f) (hA : A < 2) {B : ℝ} (hre : ∀ ρ : ℂ, f ρ = 0 → ρ.re ≤ B)
    {c : ℂ} (hfe : ∀ z : ℂ, f (1 - z) = c * conj (f (conj z))) :
    Summable (fun ρ : (MeromorphicOn.divisor f Set.univ).support ↦
      ((MeromorphicOn.divisor f Set.univ ρ).toNat : ℝ) * (1 / (ρ : ℂ)).re) :=
  h.summable_divisor_toNat_mul_re_one_div hf hA (abs_re_le_of_re_le hre hfe)

/-- Under `f (1 - z) = c * conj (f (conj z))` and a one-sided bound `Re ρ ≤ B` on all zeros of an
entire function `f` of order less than two, the real-part series `ρ ↦ m_ρ * Re (1 / (s - ρ))` is
summable on the divisor support for every `s : ℂ`. -/
theorem summable_divisor_toNat_mul_re_one_div_sub_of_re_le {f : ℂ → ℂ} {A : ℝ} (h : OrderLE f A)
    (hf : Differentiable ℂ f) (hA : A < 2) {B : ℝ} (hre : ∀ ρ : ℂ, f ρ = 0 → ρ.re ≤ B)
    {c : ℂ} (hfe : ∀ z : ℂ, f (1 - z) = c * conj (f (conj z))) (s : ℂ) :
    Summable (fun ρ : (MeromorphicOn.divisor f Set.univ).support ↦
      ((MeromorphicOn.divisor f Set.univ ρ).toNat : ℝ) * (1 / (s - ρ)).re) :=
  h.summable_divisor_toNat_mul_re_one_div_sub hf hA (abs_re_le_of_re_le hre hfe) s

/-- **Real-part formula for the Hadamard linear constant.** Let `f` be entire of growth order at
most `1` with `f 0 ≠ 0`, all zeros satisfying `Re ρ ≤ B`, and `f (1 - z) = c * conj (f (conj z))`
for a constant `c`. Then `Re (logDeriv f 0) = -∑' ρ, m_ρ * Re (1 / ρ)`. -/
theorem re_logDeriv_zero_eq_neg_tsum {f : ℂ → ℂ}
    (h : OrderLE f 1) (hf : Differentiable ℂ f) (hf0 : f 0 ≠ 0)
    {B : ℝ} (hre : ∀ ρ : ℂ, f ρ = 0 → ρ.re ≤ B)
    {c : ℂ} (hfe : ∀ z : ℂ, f (1 - z) = c * conj (f (conj z))) :
    (logDeriv f 0).re = -∑' ρ : (MeromorphicOn.divisor f Set.univ).support,
      ((MeromorphicOn.divisor f Set.univ ρ).toNat : ℝ) * (1 / (ρ : ℂ)).re := by
  have hc : c ≠ 0 := by
    rintro rfl
    have h0 := hfe 1
    simp only [sub_self, zero_mul] at h0
    exact hf0 h0
  have hf1 : f 1 ≠ 0 := by
    have h1 := hfe 0
    rw [sub_zero, map_zero] at h1
    rw [h1]
    exact mul_ne_zero hc (star_ne_zero.mpr hf0)
  have hlog1 : (logDeriv f 1).re = -(logDeriv f 0).re := by
    have h0 := congrArg re (logDeriv_one_sub_conj hfe 0)
    simpa using h0
  have hd : ∀ z : ℂ, MeromorphicOn.divisor f Set.univ (1 - conj z) =
      MeromorphicOn.divisor f Set.univ z :=
    divisor_one_sub_conj fun z ↦ Eventually.of_forall hfe
  let d := MeromorphicOn.divisor f Set.univ
  have hperm : (∑' ρ : d.support, ((d ρ).toNat : ℝ) * (1 / (1 - (ρ : ℂ))).re) =
      ∑' ρ : d.support, ((d ρ).toNat : ℝ) * (1 / (ρ : ℂ)).re := by
    symm
    rw [← (divisorSupportOneSubConj hd).tsum_eq]
    refine tsum_congr fun ρ ↦ ?_
    simp only [d, coe_divisorSupportOneSubConj_apply, hd]
    congr 1
    rw [← conj_re]
    simp
  have hexp1 := h.re_logDeriv_eq_add_tsum_add_tsum hf hf0 (abs_re_le_of_re_le hre hfe) hf1
  rw [hperm, hlog1] at hexp1
  linarith

/-- **Cancelled real-part expansion of the logarithmic derivative.** Under the hypotheses of
`OrderLE.re_logDeriv_zero_eq_neg_tsum`, for every `s` with `f s ≠ 0` one has
`Re (logDeriv f s) = ∑' ρ, m_ρ * Re (1 / (s - ρ))`, with no additive constant. -/
theorem re_logDeriv_eq_tsum {f : ℂ → ℂ}
    (h : OrderLE f 1) (hf : Differentiable ℂ f) (hf0 : f 0 ≠ 0)
    {B : ℝ} (hre : ∀ ρ : ℂ, f ρ = 0 → ρ.re ≤ B)
    {c : ℂ} (hfe : ∀ z : ℂ, f (1 - z) = c * conj (f (conj z)))
    {s : ℂ} (hs : f s ≠ 0) :
    (logDeriv f s).re = ∑' ρ : (MeromorphicOn.divisor f Set.univ).support,
      ((MeromorphicOn.divisor f Set.univ ρ).toNat : ℝ) * (1 / (s - ρ)).re := by
  rw [h.re_logDeriv_eq_add_tsum_add_tsum hf hf0 (abs_re_le_of_re_le hre hfe) hs,
    h.re_logDeriv_zero_eq_neg_tsum hf hf0 hre hfe]
  ring

/-- **Retained-zero finite-subsum bound.** Under the hypotheses of `OrderLE.re_logDeriv_eq_tsum`,
at any `s` with `f s ≠ 0` to the right of all zeros of `f` (`∀ ρ, f ρ = 0 → ρ.re ≤ s.re`), every
finite subsum `∑ ρ ∈ S, m_ρ * Re (1 / (s - ρ))` is at most `Re (logDeriv f s)`. -/
theorem sum_divisor_toNat_mul_re_one_div_sub_le_re_logDeriv {f : ℂ → ℂ}
    (h : OrderLE f 1) (hf : Differentiable ℂ f) (hf0 : f 0 ≠ 0)
    {c : ℂ} (hfe : ∀ z : ℂ, f (1 - z) = c * conj (f (conj z)))
    {s : ℂ} (hs : f s ≠ 0) (hle : ∀ ρ : ℂ, f ρ = 0 → ρ.re ≤ s.re) (S : Finset ℂ) :
    ∑ ρ ∈ S, ((MeromorphicOn.divisor f Set.univ ρ).toNat : ℝ) * (1 / (s - ρ)).re ≤
      (logDeriv f s).re := by
  rw [h.re_logDeriv_eq_tsum hf hf0 hle hfe hs]
  exact sum_divisor_toNat_mul_re_one_div_sub_le_tsum
    (h.summable_divisor_toNat_mul_re_one_div_sub_of_re_le hf (by norm_num) hle hfe s) S
    fun ρ _ hρ ↦ hle ρ ((hf.analyticAt ρ).apply_eq_zero_of_divisor_ne_zero hρ.ne')

end OrderLE

end TauCeti
