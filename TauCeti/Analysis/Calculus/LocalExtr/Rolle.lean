/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Data.Finset.Max

import Mathlib.Analysis.Calculus.LocalExtr.Rolle
import TauCeti.Analysis.Calculus.TangentCone.Basic

/-!
# Rolle's theorem for finitely many zeros

Rolle's theorem places a zero of `f'` strictly between any two zeros of a function `f : ℝ → ℝ`
continuous between them. Applied to consecutive points of a finite set `Z` of zeros of `f`, it
gives a set of `#Z - 1` zeros of `f'` separating the points of `Z`
(`TauCeti.exists_finset_deriv_eq_zero`).
Iterating along a sequence of functions, each the derivative of the previous one, a finite set of
zeros of `f` has at most `k` more points than some finite set of zeros of the `k`-th function
(`TauCeti.exists_card_le_card_add_of_hasDerivAt`).

This is how one counts the real zeros of a function by repeatedly differentiating it, as in the
zero estimate for real exponential polynomials `∑ pₖ(x) exp(γₖ x)`.

## Main results

* `TauCeti.exists_finset_deriv_eq_zero`: a nonempty finite set `Z` of zeros of `f`, continuous on
  `[min Z, max Z]`, is separated by a set of `#Z - 1` zeros of `deriv f`.
* `TauCeti.exists_card_le_card_add_of_hasDerivAt`: if `F (n + 1)` is the derivative of `F n` for
  `n < k`, a finite set `Z` of zeros of `F 0` gives a finite set `Z'` of zeros of `F k` with
  `#Z ≤ #Z' + k`.
* `Set.OrdConnected.exists_card_le_card_add_of_continuousOn_of_deriv_eq`: the same count on an
  order-connected set, assuming each `F n` for `n < k` is continuous on the set and
  `deriv (F n) x = F (n + 1) x` only in the interior.
* `ContDiffOn.exists_iteratedDerivWithin_eq_zero_of_lt_card`: the `k`-th derivative within
  an order-connected set has a zero there if the function is `C^k` on the set and has more
  than `k` zeros there.

## References

* J.-H. Evertse, *Diophantine Approximation*, lecture notes (2019), ch. 4, §4.4, Exercise 4.5.
-/

public section

open Finset

namespace TauCeti

/-- **Rolle's theorem for finitely many zeros.** If a function `f : ℝ → ℝ`, continuous between
the smallest and largest points of a nonempty finite set `Z`, vanishes on `Z`, then `deriv f`
vanishes on a finite set `Z'` with one point fewer that separates the points of `Z`: every point of
`Z'` lies strictly between two points of `Z`, and strictly between any two points of `Z` lies a
point of `Z'`. -/
theorem exists_finset_deriv_eq_zero {f : ℝ → ℝ} {Z : Finset ℝ} (hZ : Z.Nonempty)
    (hf : ContinuousOn f (Set.Icc (Z.min' hZ) (Z.max' hZ))) (hfZ : ∀ x ∈ Z, f x = 0) :
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
    have hm₀Z := Z.max'_mem hZ₀
    obtain ⟨Z', hcard, hderiv, hbetween, hsep⟩ := ih hZ₀
      (hf.mono (Set.Icc_subset_Icc (min'_le _ _ (mem_insert_of_mem (Z.min'_mem hZ₀)))
        (le_max' _ _ (mem_insert_of_mem hm₀Z))))
      fun x hx ↦ hfZ x (mem_insert_of_mem hx)
    -- A zero `c` of `deriv f` between the largest point `m₀` of `Z` and the new point `m`.
    obtain ⟨c, ⟨hc₀, hc⟩, hdc⟩ := exists_deriv_eq_zero (hm _ hm₀Z)
      (hf.mono (Set.Icc_subset_Icc (min'_le _ _ (mem_insert_of_mem hm₀Z))
        (le_max' _ _ (mem_insert_self m Z))))
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

/-- On an order-connected set `s`, suppose `F n` is continuous and `F (n + 1)` agrees with its
Lean derivative `deriv (F n)` in the interior for each `n < k`. A finite set `Z` of zeros of
`F 0` in `s` then has at most `k` more points than some finite set of zeros of `F k` in `s`.
When `k > 0`, all the resulting zeros lie in the interior of `s`. -/
theorem _root_.Set.OrdConnected.exists_card_le_card_add_of_continuousOn_of_deriv_eq {s : Set ℝ}
    (hs : s.OrdConnected) {F : ℕ → ℝ → ℝ} {k : ℕ}
    (hF : ∀ n < k, ContinuousOn (F n) s)
    (hD : ∀ n < k, ∀ x ∈ interior s, deriv (F n) x = F (n + 1) x)
    {Z : Finset ℝ} (hZs : ↑Z ⊆ s) (hZ : ∀ x ∈ Z, F 0 x = 0) :
    ∃ Z' : Finset ℝ, ↑Z' ⊆ s ∧ (∀ x ∈ Z', F k x = 0) ∧ #Z ≤ #Z' + k ∧
      (0 < k → ↑Z' ⊆ interior s) := by
  induction k with
  | zero => exact ⟨Z, hZs, hZ, le_rfl, by simp⟩
  | succ k ih =>
    obtain ⟨Z', hZ's, hZ', hcard, -⟩ := ih
      (fun n hn ↦ hF n (hn.trans k.lt_succ_self)) (fun n hn ↦ hD n (hn.trans k.lt_succ_self))
    rcases Z'.eq_empty_or_nonempty with rfl | hne
    · exact ⟨∅, by simp, by simp, by simp only [card_empty, zero_add] at hcard ⊢; omega, by simp⟩
    have hinterval := hs.out (hZ's (Z'.min'_mem hne)) (hZ's (Z'.max'_mem hne))
    obtain ⟨Z'', hcard', hderiv, hbetween, -⟩ := exists_finset_deriv_eq_zero hne
      ((hF k k.lt_succ_self).mono hinterval) hZ'
    have hZ''s : ↑Z'' ⊆ interior s := by
      intro z hz
      obtain ⟨x, hx, y, hy, hxz, hzy⟩ := hbetween z hz
      exact interior_maximal (Set.Ioo_subset_Icc_self.trans (hs.out (hZ's hx) (hZ's hy)))
        isOpen_Ioo ⟨hxz, hzy⟩
    refine ⟨Z'', hZ''s.trans interior_subset, fun x hx ↦ ?_, by omega, fun _ ↦ hZ''s⟩
    rw [← hD k k.lt_succ_self x (hZ''s hx), hderiv x hx]

/-- **Iterated Rolle's theorem.** Let `F (n + 1)` be the derivative of `F n` for every `n < k`.
Then every finite set `Z` of zeros of `F 0` has at most `k` more points than some finite set of
zeros of `F k`. -/
theorem exists_card_le_card_add_of_hasDerivAt {F : ℕ → ℝ → ℝ} {k : ℕ}
    (hF : ∀ n < k, ∀ x, HasDerivAt (F n) (F (n + 1) x) x) {Z : Finset ℝ}
    (hZ : ∀ x ∈ Z, F 0 x = 0) :
    ∃ Z' : Finset ℝ, (∀ x ∈ Z', F k x = 0) ∧ #Z ≤ #Z' + k := by
  obtain ⟨Z', -, hZ', hcard, -⟩ :=
    Set.ordConnected_univ.exists_card_le_card_add_of_continuousOn_of_deriv_eq
    (F := F) (k := k) (fun n hn x _ ↦ (hF n hn x).continuousAt.continuousWithinAt)
    (fun n hn x _ ↦ (hF n hn x).deriv) (Z := Z) (Set.subset_univ _) hZ
  exact ⟨Z', hZ', hcard⟩

/-- A `C^k` function with more than `k` distinct zeros on an order-connected set has a zero of
its `k`-th derivative within that set. For `k > 0`, the zero lies in the interior. -/
theorem _root_.ContDiffOn.exists_iteratedDerivWithin_eq_zero_of_lt_card {s : Set ℝ}
    {f : ℝ → ℝ} {k : ℕ} (hf : ContDiffOn ℝ k f s) (hs : s.OrdConnected)
    {Z : Finset ℝ} (hZs : ↑Z ⊆ s) (hZ : ∀ x ∈ Z, f x = 0) (hk : k < #Z) :
    ∃ x ∈ s, iteratedDerivWithin k f s x = 0 ∧ (0 < k → x ∈ interior s) := by
  by_cases hk₀ : k = 0
  · obtain ⟨x, hx⟩ := card_pos.mp ((Nat.zero_le k).trans_lt hk)
    exact ⟨x, hZs hx, by simpa only [hk₀, iteratedDerivWithin_zero] using hZ x hx, by simp [hk₀]⟩
  have htwo : (↑Z : Set ℝ).Nontrivial := one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨a, ha, b, hb, hab⟩ := htwo.mono hZs
  have hu := hs.isPreconnected.uniqueDiffOn ha hb hab
  obtain ⟨Z', hZ's, hZ', hcard, hinterior⟩ := hs.exists_card_le_card_add_of_continuousOn_of_deriv_eq
    (F := fun n ↦ iteratedDerivWithin n f s) (k := k)
    (fun n hn ↦ hf.continuousOn_iteratedDerivWithin (by exact_mod_cast hn.le) hu)
    (fun n _ x hx ↦ by
      rw [iteratedDerivWithin_succ, derivWithin_of_mem_nhds (mem_interior_iff_mem_nhds.mp hx)])
    hZs (by simpa only [iteratedDerivWithin_zero] using hZ)
  have hne : Z'.Nonempty := card_pos.mp (by omega)
  obtain ⟨x, hx⟩ := hne
  exact ⟨x, hZ's hx, hZ' x hx, fun hk ↦ hinterior hk hx⟩

end TauCeti
