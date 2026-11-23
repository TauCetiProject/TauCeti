/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.Set.Finite.Lemmas
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Order.Interval.Set.Basic

/-!
# Greedy covers of sets without long growth chains

Let `f : α → α` be a map on a linear order. A *growth chain* of `m + 1` points in a set `s` is a
sequence `a 0, …, a m` of points of `s` with `f (a i) ≤ a (i + 1)` for every `i < m`; the points
need not be distinct. If `s` is finite and contains no growth chain of `m + 1` points, then `s` is
covered by at most `m` blocks `Set.Ico t (f t)` with `t ∈ s`. The cover is the greedy one: start
at the least point `t` of `s`, discard the block `[t, f t)`, and repeat on the rest of `s`. The
starting points form a growth chain, so the procedure stops after at most `m` steps.

This is how a gap principle becomes a count in Diophantine approximation: a gap principle rules
out long chains of solutions, or of levels in the parametric Subspace Theorem, that grow at a fixed
rate, and the greedy cover then places them all in boundedly many windows `[t, ρ t)` of
logarithmic height, as in the counting arguments of Bombieri–Gubler, *Heights in Diophantine
Geometry*, §6.5 and §7.5.

A set of real numbers need not have a least point. Its infimum serves as the starting point
instead, at the price of a slightly longer window: in a conditionally complete ordered field, a
set bounded below by a positive number with no chain of `m + 1` points growing at rate `ρ` is
covered by at most `m` windows `[t, ρ' t)` for any `ρ' > ρ`, with every `t` above the lower
bound. The abstract form, `Set.exists_finset_card_le_of_not_exists_chain`, takes as hypothesis
exactly what one step of the greedy procedure needs: an approximate least point of every nonempty
subset.

## Main results

* `Set.exists_finset_card_le_of_not_exists_chain`: the greedy cover, for any choice of approximate
  least points.
* `Finset.exists_subset_card_le_of_not_exists_chain`: a finite set without a growth chain of
  `m + 1` points is covered by the blocks `[t, f t)` of at most `m` of its own points.
* `Finset.card_le_mul_of_not_exists_chain`: if moreover each such block holds at most `B` points,
  the set has at most `m * B` points.
* `Set.exists_forall_mem_Ico_of_not_exists_chain`: the cover by windows `[t, ρ' t)` in a
  conditionally complete ordered field.
-/

public section

namespace Set

variable {α : Type*} [LinearOrder α]

/-- **The greedy cover.** Let `s` be a set in a linear order and `f g : α → α`. Suppose every
nonempty subset `u` of `s` has an approximate least point: a lower bound `t` of `u` satisfying `P`,
together with a point `a ∈ u` with `f a ≤ g t`. If `s` holds no sequence of `m + 1` points with
`f (a i) ≤ a (i + 1)`, then `s` is covered by the windows `[t, g t)` of at most `m` points `t`
satisfying `P`. -/
theorem exists_finset_card_le_of_not_exists_chain {s : Set α} {f g : α → α} {P : α → Prop}
    {m : ℕ} (hstep : ∀ u ⊆ s, u.Nonempty → ∃ t, P t ∧ t ∈ lowerBounds u ∧ ∃ a ∈ u, f a ≤ g t)
    (hchain : ¬∃ a : Fin (m + 1) → α, (∀ i, a i ∈ s) ∧ ∀ i : Fin m, f (a i.castSucc) ≤ a i.succ) :
    ∃ T : Finset α, T.card ≤ m ∧ (∀ t ∈ T, P t) ∧ ∀ x ∈ s, ∃ t ∈ T, x ∈ Ico t (g t) := by
  classical
  induction m generalizing s with
  | zero =>
    exact ⟨∅, by simp, by simp, fun x hx ↦
      (hchain ⟨fun _ ↦ x, fun _ ↦ hx, fun i ↦ i.elim0⟩).elim⟩
  | succ m ih =>
    rcases s.eq_empty_or_nonempty with rfl | hne
    · exact ⟨∅, by simp, by simp, by simp⟩
    obtain ⟨t, hPt, ht, a, has, hfa⟩ := hstep s subset_rfl hne
    -- Discard the window `[t, g t)` and cover the rest of `s` by induction; a chain in the rest
    -- would extend to a longer chain in `s` starting at `a`.
    obtain ⟨T, hTcard, hTP, hT⟩ := ih (s := {x ∈ s | g t ≤ x})
      (fun u hu hne ↦ hstep u (hu.trans (sep_subset _ _)) hne) fun ⟨c, hcs, hc⟩ ↦
        hchain ⟨Fin.cons a c, Fin.cases has fun i ↦ (hcs i).1, Fin.cases
          (by simpa using hfa.trans (hcs 0).2) fun j ↦ by simpa [← Fin.succ_castSucc] using hc j⟩
    refine ⟨insert t T, (Finset.card_insert_le _ _).trans (by omega),
      Finset.forall_mem_insert _ _ _ |>.2 ⟨hPt, hTP⟩, fun x hx ↦ ?_⟩
    by_cases hgx : g t ≤ x
    · obtain ⟨t', ht', hx'⟩ := hT x ⟨hx, hgx⟩
      exact ⟨t', Finset.mem_insert_of_mem ht', hx'⟩
    · exact ⟨t, Finset.mem_insert_self _ _, ht hx, not_le.1 hgx⟩

end Set

namespace Finset

variable {α : Type*} [LinearOrder α]

/-- **The greedy cover of a finite set.** A finite set `s` holding no sequence of `m + 1` points
with `f (a i) ≤ a (i + 1)` is covered by the blocks `[t, f t)` of at most `m` of its own points. -/
theorem exists_subset_card_le_of_not_exists_chain {s : Finset α} {f : α → α} {m : ℕ}
    (hchain : ¬∃ a : Fin (m + 1) → α, (∀ i, a i ∈ s) ∧ ∀ i : Fin m, f (a i.castSucc) ≤ a i.succ) :
    ∃ T ⊆ s, T.card ≤ m ∧ ∀ x ∈ s, ∃ t ∈ T, x ∈ Set.Ico t (f t) := by
  obtain ⟨T, hTcard, hTs, hT⟩ := Set.exists_finset_card_le_of_not_exists_chain
    (s := (s : Set α)) (g := f) (P := (· ∈ s)) (fun u hu hne ↦ by
      obtain ⟨a, ha, hmin⟩ := Set.exists_min_image u id (s.finite_toSet.subset hu) hne
      exact ⟨a, hu ha, hmin, a, ha, le_rfl⟩) (by simpa only [mem_coe] using hchain)
  exact ⟨T, hTs, hTcard, by simpa only [mem_coe] using hT⟩

/-- **Counting with the greedy cover.** A finite set `s` holding no sequence of `m + 1` points with
`f (a i) ≤ a (i + 1)`, and whose block `[t, f t)` starting at each of its points `t` holds at most
`B` of its points, has at most `m * B` points. -/
theorem card_le_mul_of_not_exists_chain {s : Finset α} {f : α → α} {m B : ℕ}
    (hblock : ∀ t ∈ s, {x ∈ s | x ∈ Set.Ico t (f t)}.card ≤ B)
    (hchain : ¬∃ a : Fin (m + 1) → α, (∀ i, a i ∈ s) ∧ ∀ i : Fin m, f (a i.castSucc) ≤ a i.succ) :
    s.card ≤ m * B := by
  classical
  obtain ⟨T, hTs, hTcard, hT⟩ := exists_subset_card_le_of_not_exists_chain hchain
  calc s.card ≤ (T.biUnion fun t ↦ {x ∈ s | x ∈ Set.Ico t (f t)}).card :=
        card_le_card fun x hx ↦ by
          obtain ⟨t, ht, hxt⟩ := hT x hx
          exact mem_biUnion.2 ⟨t, ht, mem_filter.2 ⟨hx, hxt⟩⟩
    _ ≤ T.card * B := card_biUnion_le_card_mul _ _ _ fun t ht ↦ hblock t (hTs ht)
    _ ≤ m * B := Nat.mul_le_mul_right B hTcard

end Finset

namespace Set

variable {𝕜 : Type*} [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

/-- **The greedy cover by windows.** In a conditionally complete ordered field, let `s` be a set
bounded below by `b > 0` holding no sequence of `m + 1` points with `ρ * a i ≤ a (i + 1)`. Then
for every `ρ' > ρ` the set `s` is covered by at most `m` windows `[t, ρ' t)` with `b ≤ t`.

The window is longer than the growth rate because the starting points are infima of parts of
`s`, which need not belong to `s`. -/
theorem exists_forall_mem_Ico_of_not_exists_chain {s : Set 𝕜} {b ρ ρ' : 𝕜} {m : ℕ} (hb : 0 < b)
    (hs : s ⊆ Ici b) (hρ : ρ < ρ')
    (hchain : ¬∃ a : Fin (m + 1) → 𝕜, (∀ i, a i ∈ s) ∧ ∀ i : Fin m, ρ * a i.castSucc ≤ a i.succ) :
    ∃ T : Finset 𝕜, T.card ≤ m ∧ (∀ t ∈ T, b ≤ t) ∧ ∀ x ∈ s, ∃ t ∈ T, x ∈ Ico t (ρ' * t) := by
  refine exists_finset_card_le_of_not_exists_chain (f := (ρ * ·)) (P := (b ≤ ·))
    (fun u hu hne ↦ ?_) hchain
  have hbdd : BddBelow u := ⟨b, fun x hx ↦ hs (hu hx)⟩
  have hbt : b ≤ sInf u := le_csInf hne fun x hx ↦ hs (hu hx)
  have ht : 0 < sInf u := hb.trans_le hbt
  refine ⟨sInf u, hbt, fun x hx ↦ csInf_le hbdd hx, ?_⟩
  rcases le_or_gt ρ 0 with hρ0 | hρ0
  · obtain ⟨a, ha⟩ := hne
    exact ⟨a, ha, (mul_le_mul_of_nonpos_left (csInf_le hbdd ha) hρ0).trans
      (mul_le_mul_of_nonneg_right hρ.le ht.le)⟩
  · obtain ⟨a, ha, hat⟩ := exists_lt_of_csInf_lt hne
      ((lt_div_iff₀' hρ0).2 (mul_lt_mul_of_pos_right hρ ht) : sInf u < ρ' * sInf u / ρ)
    exact ⟨a, ha, ((lt_div_iff₀' hρ0).1 hat).le⟩

end Set
