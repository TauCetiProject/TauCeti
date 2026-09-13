/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Index
import Mathlib.Tactic.Group
import Mathlib.Tactic.NthRewrite

/-!
# A subgroup of index two inverted by one outside element

Let `N` be a subgroup of index two in a group `G`, and suppose a single element `s` outside `N`
conjugates `N` by inversion, `s * x * s⁻¹ = x⁻¹`. Conjugation by `s` then reverses products while
being an automorphism, so `N` is abelian, and every other element outside `N` is `s * n` with
`n ∈ N`, whose conjugation action is the same as that of `s`: the inversion hypothesis on one
outside element is already the inversion hypothesis on all of them.

This is the shape of a dihedral group over its rotations and of a dicyclic group over its cyclic
subgroup, and three further elementary consequences of it are recorded here: all the elements
outside `N` have one and the same square, that common square squares to one, and -- for a finite
`G` -- the elements outside `N` are exactly as many as those inside.

## Main statements

* `TauCeti.isMulCommutative_of_conj_eq_inv`: **a subgroup inverted by conjugation is abelian.**
* `TauCeti.conj_eq_inv_of_notMem_of_index_two`: **one inverting element outside a subgroup of index
  two makes every element outside it invert.**
* `TauCeti.sq_eq_sq_of_notMem_of_index_two`: the elements outside such a subgroup all have the same
  square, and `TauCeti.sq_sq_eq_one_of_conj_eq_inv`: that square squares to one.
* `TauCeti.card_filter_notMem_eq_card_of_index_two`: the complement of a subgroup of index two in a
  finite group has as many elements as the subgroup.
-/

public section

namespace TauCeti

variable {G : Type*} [Group G] {N : Subgroup G}

/-- **A subgroup conjugated by inversion is abelian.**  If `s * x * s⁻¹ = x⁻¹` for every `x ∈ N`,
then `N` is commutative.  Neither `s ∉ N` nor any hypothesis on the index of `N` is needed. -/
theorem isMulCommutative_of_conj_eq_inv {s : G} (hinv : ∀ x ∈ N, s * x * s⁻¹ = x⁻¹) :
    IsMulCommutative N :=
  IsMulCommutative.of_comm fun y z => Subtype.ext <| by
    have h : (z : G)⁻¹ * (y : G)⁻¹ = (y : G)⁻¹ * (z : G)⁻¹ :=
      calc (z : G)⁻¹ * (y : G)⁻¹ = ((y : G) * z)⁻¹ := (mul_inv_rev _ _).symm
        _ = s * ((y : G) * z) * s⁻¹ := (hinv _ (N.mul_mem y.2 z.2)).symm
        _ = s * y * s⁻¹ * (s * z * s⁻¹) := by group
        _ = (y : G)⁻¹ * (z : G)⁻¹ := by rw [hinv y y.2, hinv z z.2]
    simpa using congrArg Inv.inv h

/-- **One inverting element outside a subgroup of index two makes every element outside it
invert.**  If some `s ∉ N` satisfies `s * x * s⁻¹ = x⁻¹` for every `x ∈ N`, then so does every
`t ∉ N`; the inversion hypothesis may therefore be checked on a single outside element. -/
theorem conj_eq_inv_of_notMem_of_index_two (hindex : N.index = 2) {s : G} (hs : s ∉ N)
    (hinv : ∀ x ∈ N, s * x * s⁻¹ = x⁻¹) {t : G} (ht : t ∉ N) {x : G} (hx : x ∈ N) :
    t * x * t⁻¹ = x⁻¹ := by
  have hcomm : ∀ y ∈ N, ∀ z ∈ N, y * z = z * y := fun y hy z hz => by
    simpa using congrArg Subtype.val
      (isMulCommutative_iff.mp (isMulCommutative_of_conj_eq_inv hinv) ⟨y, hy⟩ ⟨z, hz⟩)
  have hsinv : s⁻¹ ∉ N := fun h => hs (by simpa using N.inv_mem h)
  obtain ⟨n, hn, rfl⟩ : ∃ n, n ∈ N ∧ t = s * n :=
    ⟨s⁻¹ * t, by rw [Subgroup.mul_mem_iff_of_index_two hindex]; exact iff_of_false hsinv ht,
      by group⟩
  calc s * n * x * (s * n)⁻¹ = s * (n * x * n⁻¹) * s⁻¹ := by group
    _ = s * x * s⁻¹ := by rw [hcomm n hn x hx, mul_inv_cancel_right]
    _ = x⁻¹ := hinv x hx

/-- **All the elements outside an inverted subgroup of index two have the same square**, namely
the square of the chosen inverting element `s`.  That square lies in `N` by
`Subgroup.sq_mem_of_index_two`. -/
theorem sq_eq_sq_of_notMem_of_index_two (hindex : N.index = 2) {s : G} (hs : s ∉ N)
    (hinv : ∀ x ∈ N, s * x * s⁻¹ = x⁻¹) {g : G} (hg : g ∉ N) : g ^ 2 = s ^ 2 := by
  have hsinv : s⁻¹ ∉ N := fun h => hs (by simpa using N.inv_mem h)
  obtain ⟨n, hn, rfl⟩ : ∃ n, n ∈ N ∧ g = s * n :=
    ⟨s⁻¹ * g, by rw [Subgroup.mul_mem_iff_of_index_two hindex]; exact iff_of_false hsinv hg,
      by group⟩
  have hconj : s⁻¹ * n * s = n⁻¹ := by
    simpa using conj_eq_inv_of_notMem_of_index_two hindex hs hinv hsinv hn
  have hns : n * s = s * n⁻¹ := by rw [← hconj]; group
  rw [pow_two, pow_two]
  calc s * n * (s * n) = s * (n * s) * n := by group
    _ = s * (s * n⁻¹) * n := by rw [hns]
    _ = s * s := by group

/-- **The common square of the elements outside an inverted subgroup squares to one:**
`(s ^ 2) ^ 2 = 1`. Only membership of `s ^ 2` in `N` is needed, which
`Subgroup.sq_mem_of_index_two` supplies when `N` has index two. -/
theorem sq_sq_eq_one_of_conj_eq_inv {s : G} (hsq : s ^ 2 ∈ N)
    (hinv : ∀ x ∈ N, s * x * s⁻¹ = x⁻¹) : (s ^ 2) ^ 2 = 1 := by
  have hfix : s ^ 2 = (s ^ 2)⁻¹ := by
    rw [← hinv (s ^ 2) hsq]
    group
  rw [pow_two]
  nth_rewrite 2 [hfix]
  exact mul_inv_cancel _

/-- **The complement of a subgroup of index two has as many elements as the subgroup:** in a
finite group, both halves of `G` have `Nat.card N` elements. -/
theorem card_filter_notMem_eq_card_of_index_two [Fintype G] [DecidablePred (· ∈ N)]
    (hindex : N.index = 2) : (Finset.univ.filter (fun x : G => x ∉ N)).card = Nat.card N := by
  have hsplit := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset G))
    (p := fun x : G => x ∈ N)
  have hmem : (Finset.univ.filter (fun x : G => x ∈ N)).card = Nat.card N := by
    simp [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hcard : (Finset.univ : Finset G).card = Nat.card N * 2 := by
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card, ← Subgroup.card_mul_index N, hindex]
  omega

end TauCeti
