/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Hadamard.OrderOne

import TauCeti.Analysis.Calculus.LogDeriv.Symmetry
import TauCeti.Analysis.Complex.Basic
import TauCeti.Analysis.Meromorphic.Conj

/-!
# Real-part cancellation in Hadamard expansions under functional symmetry

For an entire function `f : ℂ → ℂ` of growth order at most `1` with `f 0 ≠ 0`, the generic Hadamard
partial-fraction expansion
`logDeriv f s = logDeriv f 0 + ∑' ρ, m_ρ * (1 / (s - ρ) + 1 / ρ)` contains the a priori unknown
linear coefficient `logDeriv f 0`. When `f` obeys a functional-conjugation symmetry
`f (a - z) = c * conj (f (conj z))` (as occurs for completed L-functions, with `a = 1` or more
generally `a = w + 1` and `c` a root number up to sign, in particular `c = ±1` in the self-dual
case) and `ρ ↦ m_ρ * Re (1 / ρ)` is summable on the divisor support (in particular whenever the
zeros of `f` satisfy a one-sided bound `Re ρ ≤ B`), the real part of `logDeriv f 0` cancels
completely:

* `f 0 ≠ 0` ensures `0` is not a zero of `f` (so `E₁(ρ⁻¹ * s)` and `1 / ρ` are nonsingular at every
  zero) and, via `f (a - z) = c * conj (f (conj z))`, forces `c ≠ 0` and `f a ≠ 0`.
* Combining `Re ρ ≤ B` with `a - conj` zero symmetry confines all zeros to
  `|Re ρ| ≤ max B |Re a - B|` (`TauCeti.abs_re_le_max_of_re_le_of_sub_conj`), so
  `∑' ρ, m_ρ * Re (1 / ρ)` and `∑' ρ, m_ρ * Re (1 / (s - ρ))` converge separately
  (`TauCeti.OrderLE.summable_divisor_toNat_mul_re_one_div_of_re_le`,
  `TauCeti.OrderLE.summable_divisor_toNat_mul_re_one_div_sub_of_re_le`).
* Differentiating `f (a - z) = c * conj (f (conj z))` gives
  `logDeriv f (a - conj z) = -conj (logDeriv f z)`, hence `Re (logDeriv f a) = -Re (logDeriv f 0)`,
  while permuting the divisor support by `ρ ↦ a - conj ρ` (`TauCeti.divisor_sub_conj`) identifies
  `∑' ρ, m_ρ * Re (1 / (a - ρ))` with `∑' ρ, m_ρ * Re (1 / ρ)`. Evaluating the real-part expansion
  at `s = a` yields `Re (logDeriv f 0) = -∑' ρ, m_ρ * Re (1 / ρ)` and cancels the constant term
  from `Re (logDeriv f s)` at every `s` with `f s ≠ 0`.

## Main results

* `TauCeti.OrderLE.summable_divisor_toNat_mul_re_one_div_of_re_le`,
  `TauCeti.OrderLE.summable_divisor_toNat_mul_re_one_div_sub_of_re_le`: separate summability of
  `m_ρ * Re (1 / ρ)` and `m_ρ * Re (1 / (s - ρ))` from a one-sided bound `Re ρ ≤ B` and
  `f (a - z) = c * conj (f (conj z))`.
* `TauCeti.OrderLE.re_logDeriv_zero_eq_neg_tsum`:
  `Re (logDeriv f 0) = -∑' ρ, m_ρ * Re (1 / ρ)` for an entire `f` of order at most `1` with
  `f 0 ≠ 0`, `m_ρ * Re (1 / ρ)` summable on the divisor support, and
  `f (a - z) = c * conj (f (conj z))`.
* `TauCeti.OrderLE.re_logDeriv_eq_tsum`,
  `TauCeti.OrderLE.sum_divisor_toNat_mul_re_one_div_sub_le_re_logDeriv`,
  `TauCeti.OrderLE.re_logDeriv_nonneg`: the constant-free expansion
  `Re (logDeriv f s) = ∑' ρ, m_ρ * Re (1 / (s - ρ))` away from the zeros of `f`, its finite
  retained-zero subsum lower bound when `Re ρ ≤ Re s` on zeros outside `S`, and nonnegativity of
  `Re (logDeriv f s)` to the right of all zeros.

## References

* H. Davenport, *Multiplicative Number Theory*, 3rd ed., GTM 74, Chapters 11–12.
* H. L. Montgomery and R. C. Vaughan, *Multiplicative Number Theory I*, Cambridge University
  Press, 2007, §§10.2 and 11.1.
-/

public section

open Complex ComplexConjugate Filter Set Topology
open scoped BigOperators

namespace TauCeti.OrderLE

/-- Under `f (a - z) = c * conj (f (conj z))` and a one-sided bound `Re ρ ≤ B` on all zeros of an
entire function `f` of order less than two, the real-part series `ρ ↦ m_ρ * Re (1 / ρ)` is
summable on the divisor support. -/
theorem summable_divisor_toNat_mul_re_one_div_of_re_le {f : ℂ → ℂ} {A : ℝ} (h : OrderLE f A)
    (hf : Differentiable ℂ f) (hA : A < 2) {B : ℝ} (hre : ∀ ρ : ℂ, f ρ = 0 → ρ.re ≤ B)
    {a c : ℂ} (hfe : ∀ z : ℂ, f (a - z) = c * conj (f (conj z))) :
    Summable (fun ρ : (MeromorphicOn.divisor f Set.univ).support ↦
      ((MeromorphicOn.divisor f Set.univ ρ).toNat : ℝ) * (1 / (ρ : ℂ)).re) :=
  h.summable_divisor_toNat_mul_re_one_div hf hA
    fun _ hρ ↦ abs_re_le_max_of_re_le_of_sub_conj hre hfe hρ

/-- Under `f (a - z) = c * conj (f (conj z))` and a one-sided bound `Re ρ ≤ B` on all zeros of an
entire function `f` of order less than two, the real-part series `ρ ↦ m_ρ * Re (1 / (s - ρ))` is
summable on the divisor support for every `s : ℂ`. -/
theorem summable_divisor_toNat_mul_re_one_div_sub_of_re_le {f : ℂ → ℂ} {A : ℝ} (h : OrderLE f A)
    (hf : Differentiable ℂ f) (hA : A < 2) {B : ℝ} (hre : ∀ ρ : ℂ, f ρ = 0 → ρ.re ≤ B)
    {a c : ℂ} (hfe : ∀ z : ℂ, f (a - z) = c * conj (f (conj z))) (s : ℂ) :
    Summable (fun ρ : (MeromorphicOn.divisor f Set.univ).support ↦
      ((MeromorphicOn.divisor f Set.univ ρ).toNat : ℝ) * (1 / (s - ρ)).re) :=
  h.summable_divisor_toNat_mul_re_one_div_sub hf hA
    (fun _ hρ ↦ abs_re_le_max_of_re_le_of_sub_conj hre hfe hρ) s

/-- **Real-part formula for the Hadamard linear constant.** Let `f` be entire of growth order at
most `1` with `f 0 ≠ 0`, `ρ ↦ m_ρ * Re (1 / ρ)` summable on its divisor support, and
`f (a - z) = c * conj (f (conj z))` for constants `a, c`. Then
`Re (logDeriv f 0) = -∑' ρ, m_ρ * Re (1 / ρ)`. -/
theorem re_logDeriv_zero_eq_neg_tsum {f : ℂ → ℂ}
    (h : OrderLE f 1) (hf : Differentiable ℂ f) (hf0 : f 0 ≠ 0)
    (hinv : Summable (fun ρ : (MeromorphicOn.divisor f Set.univ).support ↦
      ((MeromorphicOn.divisor f Set.univ ρ).toNat : ℝ) * (1 / (ρ : ℂ)).re))
    {a c : ℂ} (hfe : ∀ z : ℂ, f (a - z) = c * conj (f (conj z))) :
    (logDeriv f 0).re = -∑' ρ : (MeromorphicOn.divisor f Set.univ).support,
      ((MeromorphicOn.divisor f Set.univ ρ).toNat : ℝ) * (1 / (ρ : ℂ)).re := by
  have hc : c ≠ 0 := by
    rintro rfl
    have h0 := hfe a
    simp only [sub_self, zero_mul] at h0
    exact hf0 h0
  have hfa : f a ≠ 0 := by
    have h1 := hfe 0
    rw [sub_zero, map_zero] at h1
    rw [h1]
    exact mul_ne_zero hc (star_ne_zero.mpr hf0)
  have hloga : (logDeriv f a).re = -(logDeriv f 0).re := by
    have h0 := congrArg re (logDeriv_sub_conj hfe 0)
    simpa using h0
  have hd : ∀ z : ℂ, MeromorphicOn.divisor f Set.univ (a - conj z) =
      MeromorphicOn.divisor f Set.univ z :=
    fun _ ↦ divisor_sub_conj (by simp) (Eventually.of_forall hfe) (Eventually.of_forall hfe)
  let d := MeromorphicOn.divisor f Set.univ
  let e : Equiv.Perm d.support :=
    (Complex.conjCLE.toEquiv.trans (Equiv.subLeft a)).subtypeEquiv fun z ↦ by
      simp [Function.mem_support, d, hd z]
  have hperm : (∑' ρ : d.support, ((d ρ).toNat : ℝ) * (1 / (a - (ρ : ℂ))).re) =
      ∑' ρ : d.support, ((d ρ).toNat : ℝ) * (1 / (ρ : ℂ)).re := by
    rw [← e.tsum_eq]
    refine tsum_congr fun ρ ↦ ?_
    have he : (e ρ : ℂ) = a - conj (ρ : ℂ) := rfl
    simp only [he, d, hd, sub_sub_cancel]
    congr 1
    rw [← conj_re]
    simp
  have hexpa := h.re_logDeriv_eq_add_tsum_add_tsum hf hf0 hinv hfa
  rw [hperm, hloga] at hexpa
  linarith

/-- **Cancelled real-part expansion of the logarithmic derivative.** Let `f` be entire of growth
order at most `1` with `f 0 ≠ 0`, `ρ ↦ m_ρ * Re (1 / ρ)` summable on its divisor support, and
`f (a - z) = c * conj (f (conj z))`. Then for every `s` with `f s ≠ 0` one has
`Re (logDeriv f s) = ∑' ρ, m_ρ * Re (1 / (s - ρ))`, with no additive constant. -/
theorem re_logDeriv_eq_tsum {f : ℂ → ℂ}
    (h : OrderLE f 1) (hf : Differentiable ℂ f) (hf0 : f 0 ≠ 0)
    (hinv : Summable (fun ρ : (MeromorphicOn.divisor f Set.univ).support ↦
      ((MeromorphicOn.divisor f Set.univ ρ).toNat : ℝ) * (1 / (ρ : ℂ)).re))
    {a c : ℂ} (hfe : ∀ z : ℂ, f (a - z) = c * conj (f (conj z)))
    {s : ℂ} (hs : f s ≠ 0) :
    (logDeriv f s).re = ∑' ρ : (MeromorphicOn.divisor f Set.univ).support,
      ((MeromorphicOn.divisor f Set.univ ρ).toNat : ℝ) * (1 / (s - ρ)).re := by
  rw [h.re_logDeriv_eq_add_tsum_add_tsum hf hf0 hinv hs,
    h.re_logDeriv_zero_eq_neg_tsum hf hf0 hinv hfe]
  ring

/-- **Retained-zero finite-subsum bound.** Let `f` be entire of growth order at most `1` with
`f 0 ≠ 0` and `f (a - z) = c * conj (f (conj z))`. At any `s` with `f s ≠ 0` such that every zero
`ρ` of `f` outside `S : Finset ℂ` satisfies `ρ.re ≤ s.re`, the finite subsum
`∑ ρ ∈ S, m_ρ * Re (1 / (s - ρ))` is at most `Re (logDeriv f s)`. -/
theorem sum_divisor_toNat_mul_re_one_div_sub_le_re_logDeriv {f : ℂ → ℂ}
    (h : OrderLE f 1) (hf : Differentiable ℂ f) (hf0 : f 0 ≠ 0)
    {a c : ℂ} (hfe : ∀ z : ℂ, f (a - z) = c * conj (f (conj z)))
    {s : ℂ} (hs : f s ≠ 0) (S : Finset ℂ) (hle : ∀ ρ ∉ S, f ρ = 0 → ρ.re ≤ s.re) :
    ∑ ρ ∈ S, ((MeromorphicOn.divisor f Set.univ ρ).toNat : ℝ) * (1 / (s - ρ)).re ≤
      (logDeriv f s).re := by
  have hB : ∀ ρ : ℂ, f ρ = 0 →
      ρ.re ≤ (insert s S).sup' (Finset.insert_nonempty s S) Complex.re := by
    intro ρ hρ
    by_cases hρS : ρ ∈ S
    · exact Finset.le_sup' Complex.re (Finset.mem_insert_of_mem hρS)
    · exact (hle ρ hρS hρ).trans (Finset.le_sup' Complex.re (Finset.mem_insert_self s S))
  have hinv := h.summable_divisor_toNat_mul_re_one_div_of_re_le hf (by norm_num) hB hfe
  rw [h.re_logDeriv_eq_tsum hf hf0 hinv hfe hs]
  exact sum_divisor_toNat_mul_re_one_div_sub_le_tsum
    ((h.summable_divisor_toNat_mul_re_one_div_sub_iff hf (by norm_num) s).mpr hinv) S
    fun ρ hρS hρ ↦ hle ρ hρS ((hf.analyticAt ρ).apply_eq_zero_of_divisor_ne_zero hρ.ne')

/-- **Nonnegativity of `Re (logDeriv f s)` to the right of all zeros.** Let `f` be entire of growth
order at most `1` with `f 0 ≠ 0` and `f (a - z) = c * conj (f (conj z))`. At any `s` with
`f s ≠ 0` such that every zero `ρ` of `f` satisfies `ρ.re ≤ s.re`, one has
`0 ≤ Re (logDeriv f s)`. -/
theorem re_logDeriv_nonneg {f : ℂ → ℂ}
    (h : OrderLE f 1) (hf : Differentiable ℂ f) (hf0 : f 0 ≠ 0)
    {a c : ℂ} (hfe : ∀ z : ℂ, f (a - z) = c * conj (f (conj z)))
    {s : ℂ} (hs : f s ≠ 0) (hle : ∀ ρ : ℂ, f ρ = 0 → ρ.re ≤ s.re) :
    0 ≤ (logDeriv f s).re := by
  simpa using h.sum_divisor_toNat_mul_re_one_div_sub_le_re_logDeriv hf hf0 hfe hs ∅
    fun ρ _ hρ ↦ hle ρ hρ

end TauCeti.OrderLE
