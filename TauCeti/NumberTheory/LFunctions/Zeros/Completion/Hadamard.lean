/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.CanonicalProduct.Hadamard
import Mathlib.Analysis.Calculus.Deriv.Star
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
* `f 0 ≠ 0` ensures `0` is not a zero of `f` (so `E₁(s / ρ)` and `1 / ρ` are nonsingular at every
  zero) and, via `f (1 - z) = c * conj (f (conj z))`, forces `c ≠ 0` and `f 1 ≠ 0`.
* Combining `Re ρ ≤ B` with `1 - conj` zero symmetry confines all zeros to `1 - B ≤ Re ρ ≤ B`, so
  `∑' ρ, m_ρ * Re (1 / ρ)` and `∑' ρ, m_ρ * Re (1 / (s - ρ))` converge separately
  (`TauCeti.OrderLE.summable_divisor_toNat_mul_re_one_div`,
  `TauCeti.OrderLE.summable_divisor_toNat_mul_re_one_div_sub`).
* Differentiating `f (1 - z) = c * conj (f (conj z))` gives
  `logDeriv f (1 - conj z) = -conj (logDeriv f z)`, hence `Re (logDeriv f 1) = -Re (logDeriv f 0)`,
  while permuting the zeros by `ρ ↦ 1 - conj ρ` (`TauCeti.divisorSupportOneSubConj`) identifies
  `∑' ρ, m_ρ * Re (1 / (1 - ρ))` with `∑' ρ, m_ρ * Re (1 / ρ)`. Evaluating the real-part expansion
  at `s = 1` yields `Re (logDeriv f 0) = -∑' ρ, m_ρ * Re (1 / ρ)` and cancels the constant term
  from `Re (logDeriv f s)` at every non-zero `s`.

## Main results

* `TauCeti.logDeriv_one_sub_conj_of_isOpen_of_ne_zero`,
  `TauCeti.logDeriv_one_sub_conj_of_isOpen`, `TauCeti.logDeriv_one_sub_conj`: local open-set and
  global reflection identities `logDeriv f (1 - conj z) = -conj (logDeriv f z)` under
  `f (1 - conj z) = u * conj (f z)`.
* `TauCeti.OrderLE.re_logDeriv_zero_eq_neg_tsum`:
  `Re (logDeriv f 0) = -∑' ρ, m_ρ * Re (1 / ρ)` for an entire `f` of order at most `1` with
  `f 0 ≠ 0`, `Re ρ ≤ B` on zeros, and `f (1 - z) = c * conj (f (conj z))`.
* `TauCeti.OrderLE.re_logDeriv_eq_tsum`: the constant-free expansion
  `Re (logDeriv f s) = ∑' ρ, m_ρ * Re (1 / (s - ρ))` away from the zeros of `f`.

## References

* H. Davenport, *Multiplicative Number Theory*, 3rd ed., GTM 74, Chapters 11–12.
* H. L. Montgomery and R. C. Vaughan, *Multiplicative Number Theory I*, Cambridge University
  Press, 2007, §§10.2 and 11.1.
-/

public section

open Complex ComplexConjugate Filter Set Topology

namespace TauCeti

/-- **Local logarithmic-derivative symmetry across the critical line, for a nonzero multiplier.**
If `f (1 - conj z) = u * conj (f z)` on an open set `Ω` and `u ≠ 0`, then
`logDeriv f (1 - conj z) = -conj (logDeriv f z)` at every `z ∈ Ω`, with no symmetry assumption on
`Ω` or differentiability assumption on `f`. -/
theorem logDeriv_one_sub_conj_of_isOpen_of_ne_zero {Ω : Set ℂ} {f : ℂ → ℂ} {u : ℂ} (hu : u ≠ 0)
    (hΩopen : IsOpen Ω) (hfe : ∀ z ∈ Ω, f (1 - conj z) = u * conj (f z)) {z : ℂ} (hz : z ∈ Ω) :
    logDeriv f (1 - conj z) = -conj (logDeriv f z) := by
  have hΩ' : IsOpen {w : ℂ | conj w ∈ Ω} := hΩopen.preimage Complex.continuous_conj
  have hEq : (fun w : ℂ ↦ f (1 - w)) =ᶠ[𝓝 (conj z)] fun w : ℂ ↦ u * (conj ∘ f ∘ conj) w := by
    filter_upwards [hΩ'.mem_nhds (by simpa using hz)] with w hw
    simpa [Function.comp_def] using hfe (conj w) hw
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
`f (1 - conj z) = u * conj (f z)` on an open set `Ω`, then
`logDeriv f (1 - conj z) = -conj (logDeriv f z)` at every `z ∈ Ω` with `1 - conj z ∈ Ω` (including
the degenerate case `u = 0`). -/
theorem logDeriv_one_sub_conj_of_isOpen {Ω : Set ℂ} {f : ℂ → ℂ} {u : ℂ} (hΩopen : IsOpen Ω)
    (hfe : ∀ z ∈ Ω, f (1 - conj z) = u * conj (f z)) {z : ℂ} (hz : z ∈ Ω)
    (hz' : 1 - conj z ∈ Ω) :
    logDeriv f (1 - conj z) = -conj (logDeriv f z) := by
  rcases eq_or_ne u 0 with rfl | hu
  · have h1 : f (1 - conj z) = 0 := by simpa using hfe z hz
    have h2 : f z = 0 := by simpa [sub_sub_cancel] using hfe (1 - conj z) hz'
    simp [logDeriv_apply, h1, h2]
  · exact logDeriv_one_sub_conj_of_isOpen_of_ne_zero hu hΩopen hfe hz

/-- Under a whole-plane functional-conjugation symmetry `f (1 - z) = u * conj (f (conj z))`, the
logarithmic derivative satisfies `logDeriv f (1 - conj z) = -conj (logDeriv f z)`. -/
theorem logDeriv_one_sub_conj {f : ℂ → ℂ} {u : ℂ}
    (hfe : ∀ z : ℂ, f (1 - z) = u * conj (f (conj z))) (z : ℂ) :
    logDeriv f (1 - conj z) = -conj (logDeriv f z) :=
  logDeriv_one_sub_conj_of_isOpen isOpen_univ (fun w _ ↦ by simpa using hfe (conj w))
    (mem_univ z) (mem_univ _)

namespace OrderLE

/-- Under `f (1 - z) = c * conj (f (conj z))`, an upper bound `ρ.re ≤ B` on the real parts of all
zeros also yields `1 - ρ.re ≤ B`, hence `|ρ.re| ≤ B`. -/
private theorem abs_re_le_of_re_le {f : ℂ → ℂ} {B : ℝ} (hre : ∀ ρ : ℂ, f ρ = 0 → ρ.re ≤ B)
    {c : ℂ} (hfe : ∀ z : ℂ, f (1 - z) = c * conj (f (conj z)))
    (ρ : ℂ) (hρ : f ρ = 0) : |ρ.re| ≤ B := by
  have hsym : f (1 - conj ρ) = 0 := by
    have := hfe (conj ρ)
    simpa [hρ] using this
  have h1 := hre (1 - conj ρ) hsym
  simp only [sub_re, one_re, conj_re] at h1
  exact abs_le.mpr ⟨by linarith, hre ρ hρ⟩

/-- Splits `Re (logDeriv f s)` into `Re (logDeriv f 0)`, `∑' ρ, m_ρ * Re (1 / (s - ρ))`, and
`∑' ρ, m_ρ * Re (1 / ρ)` when all zeros have bounded real part. -/
private theorem re_logDeriv_eq_add_tsum_add_tsum {f : ℂ → ℂ}
    (h : OrderLE f 1) (hf : Differentiable ℂ f) (hf0 : f 0 ≠ 0)
    {B : ℝ} (habs : ∀ ρ : ℂ, f ρ = 0 → |ρ.re| ≤ B) {s : ℂ} (hs : f s ≠ 0) :
    (logDeriv f s).re = (logDeriv f 0).re +
      (∑' ρ : (MeromorphicOn.divisor f Set.univ).support,
        ((MeromorphicOn.divisor f Set.univ ρ).toNat : ℝ) * (1 / (s - ρ)).re) +
      (∑' ρ : (MeromorphicOn.divisor f Set.univ).support,
        ((MeromorphicOn.divisor f Set.univ ρ).toNat : ℝ) * (1 / (ρ : ℂ)).re) := by
  have hc := (h.summable_norm_natCast_divisor_mul_one_div_sub_add_one_div hf s).of_norm
  have hsub := h.summable_divisor_toNat_mul_re_one_div_sub hf habs s
  have hinv := h.summable_divisor_toNat_mul_re_one_div hf habs
  have htsum_re : (∑' ρ : (MeromorphicOn.divisor f Set.univ).support,
      ((MeromorphicOn.divisor f Set.univ ρ).toNat : ℂ) * (1 / (s - ρ) + 1 / ρ)).re =
      ∑' ρ : (MeromorphicOn.divisor f Set.univ).support,
        (((MeromorphicOn.divisor f Set.univ ρ).toNat : ℝ) * (1 / (s - ρ)).re +
          ((MeromorphicOn.divisor f Set.univ ρ).toNat : ℝ) * (1 / (ρ : ℂ)).re) := by
    rw [← Complex.reCLM_apply, ContinuousLinearMap.map_tsum Complex.reCLM hc]
    refine tsum_congr fun ρ ↦ ?_
    rw [Complex.reCLM_apply, mul_re, natCast_re, natCast_im, zero_mul, sub_zero, add_re, mul_add]
  rw [h.logDeriv_eq_add_tsum hf hf0 hs, add_re, htsum_re, Summable.tsum_add hsub hinv, add_assoc]

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

end OrderLE

end TauCeti
