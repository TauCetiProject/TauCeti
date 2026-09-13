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
subgroup, and two further elementary consequences of it are recorded here: all the elements
outside `N` have one and the same square, and that common square is an involution.

## Main statements

* `TauCeti.conj_eq_inv_of_notMem_of_index_two`: **one inverting element outside a subgroup of index
  two makes every element outside it invert.**
* `TauCeti.sq_eq_sq_of_notMem_of_index_two`: the elements outside such a subgroup all have the same
  square, and `TauCeti.sq_sq_eq_one_of_conj_eq_inv`: that square is an involution.
-/

public section

namespace TauCeti

variable {G : Type*} [Group G] {N : Subgroup G}

/-- **One inverting element outside a subgroup of index two makes every element outside it
invert.**  If some `s ∉ N` satisfies `s * x * s⁻¹ = x⁻¹` for every `x ∈ N`, then so does every
`t ∉ N`; the inversion hypothesis may therefore be checked on a single outside element. -/
theorem conj_eq_inv_of_notMem_of_index_two (hindex : N.index = 2) {s : G} (hs : s ∉ N)
    (hinv : ∀ x ∈ N, s * x * s⁻¹ = x⁻¹) {t : G} (ht : t ∉ N) {x : G} (hx : x ∈ N) :
    t * x * t⁻¹ = x⁻¹ := by
  have hcomm : ∀ y ∈ N, ∀ z ∈ N, y * z = z * y := fun y hy z hz => by
    have h : z⁻¹ * y⁻¹ = y⁻¹ * z⁻¹ :=
      calc z⁻¹ * y⁻¹ = (y * z)⁻¹ := (mul_inv_rev y z).symm
        _ = s * (y * z) * s⁻¹ := (hinv _ (N.mul_mem hy hz)).symm
        _ = s * y * s⁻¹ * (s * z * s⁻¹) := by group
        _ = y⁻¹ * z⁻¹ := by rw [hinv y hy, hinv z hz]
    simpa using congrArg Inv.inv h
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

/-- **The common square of the elements outside an inverted subgroup is an involution:**
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

end TauCeti
