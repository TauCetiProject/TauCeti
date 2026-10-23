/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Data.Finset.Max

import Mathlib.Analysis.Calculus.LocalExtr.Rolle

/-!
# Rolle's theorem for finitely many zeros

Rolle's theorem places a zero of `f'` strictly between any two zeros of a continuous function
`f : ℝ → ℝ`. Applied to consecutive points of a finite set `Z` of zeros of `f`, it gives a set of
`#Z - 1` zeros of `f'` separating the points of `Z` (`TauCeti.exists_finset_deriv_eq_zero`).
Iterating along a sequence of functions, each the derivative of the previous one, a finite set of
zeros of `f` has at most `k` more points than some finite set of zeros of the `k`-th function
(`TauCeti.exists_card_le_card_add_of_hasDerivAt`).

This is how one counts the real zeros of a function by repeatedly differentiating it, as in the
zero estimate for real exponential polynomials `∑ pₖ(x) exp(γₖ x)`.

## Main results

* `TauCeti.exists_finset_deriv_eq_zero`: a nonempty finite set `Z` of zeros of a continuous `f`
  is separated by a set of `#Z - 1` zeros of `deriv f`.
* `TauCeti.exists_card_le_card_add_of_hasDerivAt`: if `F (n + 1)` is the derivative of `F n` for
  `n < k`, a finite set `Z` of zeros of `F 0` gives a finite set `Z'` of zeros of `F k` with
  `#Z ≤ #Z' + k`.

## References

* J.-H. Evertse, *Diophantine Approximation*, lecture notes (2019), ch. 4, §4.4, Exercise 4.5.
-/

public section

open Finset

namespace TauCeti

/-- **Rolle's theorem for finitely many zeros.** If a continuous function `f : ℝ → ℝ` vanishes on
a nonempty finite set `Z`, then `deriv f` vanishes on a finite set `Z'` with one point fewer that
separates the points of `Z`: every point of `Z'` lies strictly between two points of `Z`, and
strictly between any two points of `Z` lies a point of `Z'`. -/
theorem exists_finset_deriv_eq_zero {f : ℝ → ℝ} (hf : Continuous f) {Z : Finset ℝ}
    (hZ : Z.Nonempty) (hfZ : ∀ x ∈ Z, f x = 0) :
    ∃ Z' : Finset ℝ, #Z' + 1 = #Z ∧ (∀ z ∈ Z', deriv f z = 0) ∧
      (∀ z ∈ Z', ∃ x ∈ Z, ∃ y ∈ Z, x < z ∧ z < y) ∧
      ∀ x ∈ Z, ∀ y ∈ Z, x < y → ∃ z ∈ Z', x < z ∧ z < y := by
  induction Z using Finset.induction_on_max with
  | empty => exact absurd hZ Finset.not_nonempty_empty
  | insert m Z hm ih =>
    have hmZ : m ∉ Z := fun h ↦ lt_irrefl m (hm m h)
    rcases Z.eq_empty_or_nonempty with rfl | hZ₀
    · refine ⟨∅, by simp, by simp, by simp, ?_⟩
      simp only [insert_empty, mem_singleton]
      rintro x rfl y rfl h
      exact absurd h (lt_irrefl _)
    obtain ⟨Z', hcard, hderiv, hbetween, hsep⟩ :=
      ih hZ₀ fun x hx ↦ hfZ x (mem_insert_of_mem hx)
    -- A zero `c` of `deriv f` between the largest point `m₀` of `Z` and the new point `m`.
    have hm₀Z := Z.max'_mem hZ₀
    obtain ⟨c, ⟨hc₀, hc⟩, hdc⟩ := exists_deriv_eq_zero (hm _ hm₀Z) hf.continuousOn
      ((hfZ _ (mem_insert_of_mem hm₀Z)).trans (hfZ m (mem_insert_self m Z)).symm)
    have hcZ' : c ∉ Z' := fun hc' ↦ by
      obtain ⟨-, -, y, hy, -, hcy⟩ := hbetween c hc'
      exact lt_asymm hc₀ (hcy.trans_le (Z.le_max' y hy))
    refine ⟨insert c Z', ?_, ?_, ?_, ?_⟩
    · rw [card_insert_of_notMem hcZ', card_insert_of_notMem hmZ, hcard]
    · simpa [hdc] using hderiv
    · simp only [mem_insert, forall_eq_or_imp]
      refine ⟨⟨_, Or.inr hm₀Z, m, Or.inl rfl, hc₀, hc⟩, fun z hz ↦ ?_⟩
      obtain ⟨x, hx, y, hy, hxz, hzy⟩ := hbetween z hz
      exact ⟨x, Or.inr hx, y, Or.inr hy, hxz, hzy⟩
    · simp only [mem_insert]
      rintro x (rfl | hx) y (rfl | hy) hxy
      · exact absurd hxy (lt_irrefl _)
      · exact absurd (hm y hy) (lt_asymm hxy)
      · exact ⟨c, Or.inl rfl, (Z.le_max' x hx).trans_lt hc₀, hc⟩
      · obtain ⟨z, hz, hxz, hzy⟩ := hsep x hx y hy hxy
        exact ⟨z, Or.inr hz, hxz, hzy⟩

/-- **Iterated Rolle's theorem.** Let `F (n + 1)` be the derivative of `F n` for every `n < k`.
Then every finite set `Z` of zeros of `F 0` has at most `k` more points than some finite set of
zeros of `F k`. -/
theorem exists_card_le_card_add_of_hasDerivAt {F : ℕ → ℝ → ℝ} {k : ℕ}
    (hF : ∀ n < k, ∀ x, HasDerivAt (F n) (F (n + 1) x) x) {Z : Finset ℝ}
    (hZ : ∀ x ∈ Z, F 0 x = 0) :
    ∃ Z' : Finset ℝ, (∀ x ∈ Z', F k x = 0) ∧ #Z ≤ #Z' + k := by
  induction k with
  | zero => exact ⟨Z, hZ, le_rfl⟩
  | succ k ih =>
    obtain ⟨Z', hZ', hcard⟩ := ih fun n hn ↦ hF n (hn.trans k.lt_succ_self)
    rcases Z'.eq_empty_or_nonempty with rfl | hne
    · exact ⟨∅, by simp, by simp only [card_empty, zero_add] at hcard; omega⟩
    have hk := hF k k.lt_succ_self
    obtain ⟨Z'', hcard', hderiv, -, -⟩ := exists_finset_deriv_eq_zero
      (continuous_iff_continuousAt.2 fun x ↦ (hk x).continuousAt) hne hZ'
    refine ⟨Z'', fun x hx ↦ (hk x).deriv ▸ hderiv x hx, ?_⟩
    omega

end TauCeti
