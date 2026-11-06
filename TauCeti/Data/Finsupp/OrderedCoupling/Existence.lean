/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Finsupp.Order
public import Mathlib.Order.Preorder.Chain
import Mathlib.Data.Finset.Max

/-!
# Existence of staircase couplings

Two nonnegative finitely supported functions on linear orders with equal total mass admit
nonnegative joint weights supported on a chain in the coordinatewise product order. This is
the barycentric existence argument for the staircase triangulation of a product of simplices.
The index orders are arbitrary, and the coefficients may lie in an ordered additive group
or a monoid with truncated subtraction, such as `ℕ` or `ℝ≥0`. Normalization to mass one is
unnecessary.

## References

* C. P. Rourke, B. J. Sanderson, *Introduction to Piecewise-Linear Topology*, Chapter 2
  (triangulating products of polyhedra).
-/

public section

namespace Finsupp

open Finset

variable {α β R : Type*} [LinearOrder α] [LinearOrder β]
  [AddCommMonoid R] [LinearOrder R] [IsOrderedCancelAddMonoid R]
  [Sub R] [OrderedSub R] [ExistsAddOfLE R]

/-- A nonnegative finitely supported function of total mass zero vanishes. -/
theorem eq_zero_of_sum_eq_zero_of_nonneg {ι M : Type*} [AddCommMonoid M] [LinearOrder M]
    [IsOrderedCancelAddMonoid M] {f : ι →₀ M} (hf : 0 ≤ f)
    (h : f.sum (fun _ r => r) = 0) : f = 0 := by
  by_contra hne
  exact (ne_of_gt (f.sum_pos (g := fun _ r => r) (fun i hi => lt_of_le_of_ne (hf i)
    (mem_support_iff.mp hi).symm) hne)) h

/-- Subtracting the smaller of the weights at `a` and `b` from both marginals leaves nonnegative
residuals with smaller supports, and equal masses. -/
theorem exists_residual_marginals (f : α →₀ R) (g : β →₀ R) (hf : 0 ≤ f) (hg : 0 ≤ g)
    (hmass : f.sum (fun _ r => r) = g.sum (fun _ r => r)) {a : α} {b : β}
    (ha : a ∈ f.support) (hb : b ∈ g.support) :
    ∃ (c : R) (f' : α →₀ R) (g' : β →₀ R), 0 ≤ c ∧ 0 ≤ f' ∧ 0 ≤ g' ∧
      f'.support ⊆ f.support ∧ g'.support ⊆ g.support ∧
      f'.support.card + g'.support.card < f.support.card + g.support.card ∧
      f'.sum (fun _ r => r) = g'.sum (fun _ r => r) ∧
      single a c + f' = f ∧ single b c + g' = g := by
  classical
  let c := min (f a) (g b)
  let f' := f.update a (f a - c)
  let g' := g.update b (g b - c)
  have hf' : 0 ≤ f' := by
    intro i
    by_cases hi : i = a
    · subst i
      simpa [f'] using (le_tsub_iff_right (min_le_left (f a) (g b))).mpr (by simp)
    · simpa [f', update_apply, hi] using hf i
  have hg' : 0 ≤ g' := by
    intro i
    by_cases hi : i = b
    · subst i
      simpa [g'] using (le_tsub_iff_right (min_le_right (f a) (g b))).mpr (by simp)
    · simpa [g', update_apply, hi] using hg i
  have hfs : f'.support ⊆ f.support := by
    simpa [ha] using support_update_subset f a (b := f a - c)
  have hgs : g'.support ⊆ g.support := by
    simpa [hb] using support_update_subset g b (b := g b - c)
  have hcard : f'.support.card + g'.support.card < f.support.card + g.support.card := by
    have hfcard := card_le_card hfs
    have hgcard := card_le_card hgs
    rcases le_total (f a) (g b) with hle | hle
    · have hna : a ∉ f'.support := by
        simp [f', c, min_eq_left hle, tsub_eq_of_eq_add (zero_add (f a)).symm]
      have hlt := card_lt_card (Finset.ssubset_iff_subset_ne.mpr
        ⟨hfs, fun h => hna (h.symm ▸ ha)⟩)
      omega
    · have hnb : b ∉ g'.support := by
        simp [g', c, min_eq_right hle, tsub_eq_of_eq_add (zero_add (g b)).symm]
      have hlt := card_lt_card (Finset.ssubset_iff_subset_ne.mpr
        ⟨hgs, fun h => hnb (h.symm ▸ hb)⟩)
      omega
  have hfr : single a c + f' = f := by
    ext i
    by_cases hi : i = a
    · subst i; simp [f', c]
    · simp [f', hi]
  have hgr : single b c + g' = g := by
    ext i
    by_cases hi : i = b
    · subst i; simp [g', c]
    · simp [g', hi]
  refine ⟨c, f', g', le_min (hf a) (hg b), hf', hg', hfs, hgs, hcard, ?_, hfr, hgr⟩
  rw [← hfr, ← hgr] at hmass
  simpa [sum_add_index] using hmass

omit [Sub R] [OrderedSub R] [ExistsAddOfLE R] in
/-- Adding the least pair `(a, b)` with weight `c` to a staircase coupling of the residual
marginals gives a staircase coupling of the original marginals. -/
theorem exists_nonneg_isChain_mapDomain_of_residual {f f' : α →₀ R} {g g' : β →₀ R}
    {a : α} {b : β} {c : R} (hc : 0 ≤ c) (hfr : single a c + f' = f) (hgr : single b c + g' = g)
    (ha : ∀ x ∈ f.support, a ≤ x) (hb : ∀ y ∈ g.support, b ≤ y)
    (hfs : f'.support ⊆ f.support) (hgs : g'.support ⊆ g.support)
    {w : (α × β) →₀ R} (hw : 0 ≤ w) (hchain : IsChain (· ≤ ·) (w.support : Set (α × β)))
    (hwf : mapDomain Prod.fst w = f') (hwg : mapDomain Prod.snd w = g') :
    ∃ w : (α × β) →₀ R, 0 ≤ w ∧ IsChain (· ≤ ·) (w.support : Set (α × β)) ∧
      mapDomain Prod.fst w = f ∧ mapDomain Prod.snd w = g := by
  classical
  have hws : w.support ⊆ f.support.product g.support := by
    intro p hp
    have hpf : p.1 ∈ f'.support := by
      rw [← hwf, support_mapDomain_of_nonneg hw]
      exact mem_image_of_mem Prod.fst hp
    have hpg : p.2 ∈ g'.support := by
      rw [← hwg, support_mapDomain_of_nonneg hw]
      exact mem_image_of_mem Prod.snd hp
    exact mem_product.mpr ⟨hfs hpf, hgs hpg⟩
  refine ⟨single (a, b) c + w, add_nonneg (single_nonneg.mpr hc) hw, ?_, ?_, ?_⟩
  · have hsub : ((single (a, b) c + w).support : Set (α × β)) ⊆
        insert (a, b) (w.support : Set (α × β)) := by
      intro p hp
      rcases mem_union.mp (support_add hp) with hp | hp
      · exact Or.inl (by simpa using support_single_subset hp)
      · exact Or.inr hp
    apply (hchain.insert ?_).mono hsub
    intro p hp _
    have hp' := mem_product.mp (hws hp)
    exact Or.inl ⟨ha _ hp'.1, hb _ hp'.2⟩
  · simpa [mapDomain_add, hwf] using hfr
  · simpa [mapDomain_add, hwg] using hgr

/-- Nonnegative finite weights of equal total mass have a nonnegative coupling supported
on a staircase. The two `mapDomain` equations specify its marginals. -/
theorem exists_nonneg_isChain_mapDomain (f : α →₀ R) (g : β →₀ R)
    (hf : 0 ≤ f) (hg : 0 ≤ g) (hmass : f.sum (fun _ r => r) = g.sum (fun _ r => r)) :
    ∃ w : (α × β) →₀ R, 0 ≤ w ∧ IsChain (· ≤ ·) (w.support : Set (α × β)) ∧
      mapDomain Prod.fst w = f ∧ mapDomain Prod.snd w = g := by
  classical
  -- Match the least remaining indices, removing the smaller weight. At least one support
  -- shrinks at each step, so induction on the sum of the support cardinalities terminates.
  have aux : ∀ n : ℕ, ∀ (f : α →₀ R) (g : β →₀ R),
      f.support.card + g.support.card = n → 0 ≤ f → 0 ≤ g →
      f.sum (fun _ r => r) = g.sum (fun _ r => r) →
      ∃ w : (α × β) →₀ R, 0 ≤ w ∧ IsChain (· ≤ ·) (w.support : Set (α × β)) ∧
        mapDomain Prod.fst w = f ∧ mapDomain Prod.snd w = g := by
    intro n
    induction n using Nat.strong_induction_on with
    | ind n ih =>
      intro f g hn hf hg hmass
      -- Zero mass forces both nonnegative marginals to vanish.
      by_cases hf0 : f = 0
      · have hg0 : g = 0 := eq_zero_of_sum_eq_zero_of_nonneg hg (by simp [← hmass, hf0])
        subst f; subst g
        exact ⟨0, le_rfl, by simp, by simp, by simp⟩
      have hg0 : g ≠ 0 := fun hg0 =>
        hf0 (eq_zero_of_sum_eq_zero_of_nonneg hf (by simp [hmass, hg0]))
      obtain ⟨c, f', g', hc, hf', hg', hfs, hgs, hcard, hmass', hfr, hgr⟩ :=
        exists_residual_marginals f g hf hg hmass
          (min'_mem _ (support_nonempty_iff.mpr hf0)) (min'_mem _ (support_nonempty_iff.mpr hg0))
      obtain ⟨w, hw, hchain, hwf, hwg⟩ := ih _ (hn ▸ hcard) f' g' rfl hf' hg' hmass'
      exact exists_nonneg_isChain_mapDomain_of_residual hc hfr hgr
        (fun _ hx => min'_le _ _ hx) (fun _ hy => min'_le _ _ hy) hfs hgs hw hchain hwf hwg
  exact aux _ f g rfl hf hg hmass

end Finsupp
