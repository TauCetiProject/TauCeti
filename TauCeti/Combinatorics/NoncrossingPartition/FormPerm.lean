/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.NoncrossingPartition.Kreweras
public import TauCeti.Order.Partition.FormPerm
import TauCeti.Order.Partition.Finpartition

/-!
# The permutation model of noncrossing partitions and the Kreweras complement

A finite partition `P` of a finite set `s` in a linear order has the permutation
`Finpartition.formPerm P`, which cycles every part in increasing order. The partition of `s` into
one part gives the cycle `γ` through all of `s` in increasing order, which on `Fin n` is
`finRotate n`, that is `i ↦ i + 1` modulo `n`.

This file proves that for a noncrossing partition `P` the permutation of the Kreweras complement
`K(P)` is `P.formPerm⁻¹ * γ`, where, as for all permutations, the right factor acts first. In
other words, the bar after `x` is followed in its part of `K(P)` by the bar after the point of `P`
that precedes the successor `γ x` of `x` in increasing cyclic order. Combined with
`#P.parts + #K(P).parts = n + 1`, this shows that a noncrossing partition of `Fin n`, `n ≥ 1`,
satisfies the geodesic condition: the permutation `p` of `P` and `p⁻¹ * γ` have `n + 1` cycles in
total, fixed points included. The converse, that every permutation satisfying the geodesic
condition comes from a noncrossing partition, is in
`TauCeti/Combinatorics/NoncrossingPartition/Geodesic.lean`.

## Main results

* `Finpartition.IsNoncrossing.formPerm_kreweras`: for noncrossing `P`, the permutation of the
  Kreweras complement is `P.formPerm⁻¹ * (⊤ : Finpartition s).formPerm`.
* `TauCeti.NoncrossingPartition.formPerm_kreweras`: on `NC(n)`,
  `p_{K(π)} = p_π⁻¹ * finRotate n`.
* `TauCeti.NoncrossingPartition.orbitCount_formPerm_add_orbitCount_inv_mul_finRotate`: for
  `π ∈ NC(n)` with `n ≠ 0`, the permutations `p_π` and `p_π⁻¹ * finRotate n` have `n + 1` cycles
  in total.

## References

* P. Biane, *Some properties of crossings and partitions*, Discrete Math. 175 (1997), 41–53.
* A. Nica, R. Speicher, *Lectures on the Combinatorics of Free Probability*, Lecture 23.
-/

public section

open Equiv Finset

namespace Finpartition

variable {α : Type*} [LinearOrder α] {s : Finset α} {P : Finpartition s}

/-- For a noncrossing partition `P` of `s`, let `y` be the point of `s` after `x` in increasing
cyclic order and `k` the point of the part of `y` before `y`. Then `Set.uIoc x k ∩ s` is a union
of parts of `P`, so the bars after `x` and `k` lie in a common part of `K(P)`. -/
private theorem IsNoncrossing.mem_uIoc_of_mem_part (hP : P.IsNoncrossing) {x y k : α}
    (hys : y ∈ s) (hks : k ∈ s) (hyk : P.part y = P.part k)
    (hylt : x < y → ∀ w ∈ s, x < w → y ≤ w) (hyle : y ≤ x → ∀ w ∈ s, y ≤ w ∧ w ≤ x)
    (hklt : k < y → ∀ w ∈ P.part k, k < w → y ≤ w)
    (hkle : y ≤ k → ∀ w ∈ P.part k, y ≤ w ∧ w ≤ k)
    {a b : α} (hb : b ∈ P.part a) (ha : a ∈ Set.uIoc x k) : b ∈ Set.uIoc x k := by
  have has : a ∈ s := P.part_nonempty.1 ⟨b, hb⟩
  have hbs : b ∈ s := P.part_subset a hb
  have hba : P.part b = P.part a := (P.mem_part_iff_part_eq_part hbs has).1 hb
  rw [Set.mem_uIoc] at ha ⊢
  rcases lt_or_ge x y with hxy | hyx
  · rcases lt_or_ge k y with hky | hyk'
    · -- `k < y`: then `k ≤ x`, and `a` lies in `(k, x]`, between `k` and `y`.
      have hkx : k ≤ x := not_lt.1 fun hxk => absurd (hylt hxy k hks hxk) (not_le.2 hky)
      obtain ⟨hka, hax⟩ : k < a ∧ a ≤ x :=
        ha.resolve_left fun h => absurd (h.1.trans_le h.2) hkx.not_gt
      have hay : a < y := hax.trans_lt hxy
      have hne : P.part a ≠ P.part k := fun h =>
        absurd (hklt hky a (h ▸ P.mem_part has) hka) (not_le.2 hay)
      refine Or.inr ⟨?_, ?_⟩
      · by_contra hbk
        rcases (not_lt.1 hbk).lt_or_eq with hbk | rfl
        · exact hne (hba.symm.trans (hP.part_eq_part hbs hks hba hyk.symm hbk hka hay))
        · exact hne hba.symm
      · by_contra hxb
        have hyb := hylt hxy b hbs (not_le.1 hxb)
        rcases hyb.lt_or_eq with hyb | rfl
        · exact hne (hP.part_eq_part hks has hyk.symm hba.symm hka hay hyb).symm
        · exact hne (hba.symm.trans hyk)
    · -- `y ≤ k`: `y` and `k` are the first and last points of their part, and `a ∈ (x, k]`.
      have hxk : x < k := hxy.trans_le hyk'
      obtain ⟨hxa, hak'⟩ : x < a ∧ a ≤ k :=
        ha.resolve_right fun h => absurd (h.1.trans_le h.2) hxk.not_gt
      by_cases hsame : P.part a = P.part k
      · obtain ⟨hyb, hbk⟩ := hkle hyk' b (hsame ▸ hb)
        exact Or.inl ⟨hxy.trans_le hyb, hbk⟩
      have hya : y < a := (hylt hxy a has hxa).lt_of_ne fun h => hsame (h ▸ hyk)
      have hak'' : a < k := hak'.lt_of_ne fun h => hsame (h ▸ rfl)
      refine Or.inl ⟨?_, ?_⟩
      · by_contra hbx
        have hby : b < y := (not_lt.1 hbx).trans_lt hxy
        exact hsame (hba.symm.trans ((hP.part_eq_part hbs hys hba hyk hby hya hak'').trans hyk))
      · by_contra hkb
        exact hsame ((hP.part_eq_part hys has hyk hba.symm hya hak'' (not_le.1 hkb)).symm.trans hyk)
  · -- `y ≤ x`: `x` and `y` are the last and first points of `s`, and `a ∈ (k, x]`.
    have hyk' : y ≤ k := (hyle hyx k hks).1
    have hkx : k ≤ x := (hyle hyx k hks).2
    obtain ⟨hka, hax⟩ : k < a ∧ a ≤ x :=
      ha.resolve_left fun h => absurd (h.1.trans_le h.2) hkx.not_gt
    have hne : P.part a ≠ P.part k := fun h =>
      absurd (hkle hyk' a (h ▸ P.mem_part has)).2 (not_le.2 hka)
    refine Or.inr ⟨?_, (hyle hyx b hbs).2⟩
    by_contra hbk
    rcases (not_lt.1 hbk).lt_or_eq with hbk | rfl
    · rcases (hyle hyx b hbs).1.lt_or_eq with hyb | rfl
      · exact hne (hba.symm.trans ((hP.part_eq_part hys hbs hyk hba hyb hbk hka).symm.trans hyk))
      · exact hne (hba.symm.trans hyk)
    · exact hne hba.symm

/-- **The permutation of the Kreweras complement.** For a noncrossing partition `P` of a finite
set `s` in a linear order, the permutation of its Kreweras complement is `p⁻¹ * γ`, where `p` is
the permutation of `P` and `γ` is the cycle through the points of `s` in increasing order. -/
theorem IsNoncrossing.formPerm_kreweras (hP : P.IsNoncrossing) :
    P.kreweras.formPerm = P.formPerm⁻¹ * (⊤ : Finpartition s).formPerm := by
  ext x
  rw [Perm.mul_apply]
  by_cases hx : x ∈ s
  swap
  · rw [formPerm_apply_of_notMem _ hx, formPerm_apply_of_notMem _ hx, eq_comm,
      Perm.inv_eq_iff_eq, formPerm_apply_of_notMem _ hx]
  -- `y` is the point of `s` after `x` in increasing cyclic order.
  set y := (⊤ : Finpartition s).formPerm x
  obtain ⟨hys, hylt, hyle⟩ := ((⊤ : Finpartition s).formPerm_apply_eq_iff hx).1 rfl
  rw [part_top hx] at hys hylt hyle
  -- `k` is the point of the part of `y` before `y`.
  set k := P.formPerm⁻¹ y
  have hk : P.formPerm k = y := by simp [k]
  have hks : k ∈ s := P.formPerm_apply_mem_iff.1 (hk ▸ hys)
  obtain ⟨hyk, hklt, hkle⟩ := (P.formPerm_apply_eq_iff hks).1 hk
  have hyk : P.part y = P.part k := (P.mem_part_iff_part_eq_part hys hks).1 hyk
  have hky : k ∈ P.part y := hyk ▸ P.mem_part hks
  have hyk' : y ∈ P.part k := hyk ▸ P.mem_part hys
  have hclosed {a b : α} (hb : b ∈ P.part a) (ha : a ∈ Set.uIoc x k) : b ∈ Set.uIoc x k :=
    hP.mem_uIoc_of_mem_part hys hks hyk hylt hyle hklt hkle hb ha
  refine (P.kreweras.formPerm_apply_eq_iff hx).2 ⟨mem_part_kreweras_iff.2 ⟨hx, hks,
    fun a b hb ha => hclosed hb ha⟩, fun hxk w hw hxw => ?_, fun hkx w hw => ?_⟩
  all_goals
    obtain ⟨-, hws, hw⟩ := mem_part_kreweras_iff.1 hw
  · -- A bar `w` after `x` in the part of `x` in `K(P)` has `y ∈ (x, w]`, hence also `k`.
    by_contra hwk
    rcases lt_or_ge x y with hxy | hyx
    · have := hw y k hky (Set.mem_uIoc.2 (Or.inl ⟨hxy, hylt hxy w hws hxw⟩))
      rw [Set.mem_uIoc] at this
      rcases this with h | h
      · exact hwk h.2
      · exact absurd (h.1.trans_le h.2) hxw.not_gt
    · exact absurd (hyle hyx k hks).2 hxk.not_ge
  · refine ⟨?_, ?_⟩
    · -- A bar `w` before `k` would have `k ∈ (w, x]`, hence also `y`, in the same part.
      by_contra hwk
      have hwx : w < x := (not_le.1 hwk).trans_le hkx
      have := hw k y hyk' (Set.mem_uIoc.2 (Or.inr ⟨not_le.1 hwk, hkx⟩))
      rw [Set.mem_uIoc] at this
      rcases this with h | ⟨hwy, hyx⟩
      · exact absurd (h.1.trans_le h.2) hwx.not_gt
      · exact absurd (hyle hyx w hws).1 hwy.not_ge
    · -- A bar `w` after `x` would have `y ∈ (x, w]`, hence also `k`.
      by_contra hwx
      rcases lt_or_ge x y with hxy | hyx
      · have := hw y k hky (Set.mem_uIoc.2 (Or.inl ⟨hxy, hylt hxy w hws (not_le.1 hwx)⟩))
        rw [Set.mem_uIoc] at this
        rcases this with h | h
        · exact absurd h.1 hkx.not_gt
        · exact absurd (h.1.trans_le h.2) (not_le.1 hwx).not_gt
      · exact hwx (hyle hyx w hws).2

end Finpartition

namespace TauCeti.NoncrossingPartition

variable {n : ℕ}

/-- **The permutation of the Kreweras complement on `NC(n)`.** For a noncrossing partition `π` of
`Fin n`, `p_{K(π)} = p_π⁻¹ * γ`, where `p_σ` cycles each part of `σ` in increasing order and
`γ = finRotate n` is the rotation `i ↦ i + 1` modulo `n`. -/
theorem formPerm_kreweras (π : NoncrossingPartition (univ : Finset (Fin n))) :
    (kreweras π : Finpartition (univ : Finset (Fin n))).formPerm =
      (π : Finpartition (univ : Finset (Fin n))).formPerm⁻¹ * finRotate n := by
  rw [coe_kreweras, π.2.formPerm_kreweras, Finpartition.formPerm_top_eq_finRotate]

/-- **The geodesic condition for noncrossing partitions.** For a noncrossing partition `π` of
`Fin n` with `n ≠ 0`, the permutations `p_π` and `p_π⁻¹ * finRotate n` have `n + 1` cycles in
total, fixed points included. -/
theorem orbitCount_formPerm_add_orbitCount_inv_mul_finRotate (hn : n ≠ 0)
    (π : NoncrossingPartition (univ : Finset (Fin n))) :
    orbitCount (π : Finpartition (univ : Finset (Fin n))).formPerm +
        orbitCount ((π : Finpartition (univ : Finset (Fin n))).formPerm⁻¹ * finRotate n) =
      n + 1 := by
  rw [← formPerm_kreweras, Finpartition.orbitCount_formPerm, Finpartition.orbitCount_formPerm,
    card_parts_add_card_parts_kreweras π (univ_nonempty_iff.2 ⟨⟨0, Nat.pos_of_ne_zero hn⟩⟩),
    card_univ, Fintype.card_fin]

end TauCeti.NoncrossingPartition
