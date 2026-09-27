/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.QuotientGroup.Basic
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

The file also records the coset structure of an arbitrary subgroup of index two, which needs no
inverting element: `G ⧸ N` consists of the trivial coset and the coset of any `s ∉ N`, so a finite
sum over `G ⧸ N` has exactly those two terms.

## Main statements

* `TauCeti.isMulCommutative_of_conj_eq_inv`: **a subgroup inverted by conjugation is abelian.**
* `TauCeti.sq_eq_one_of_mem_of_conj_eq_inv`: if the inverting element lies in the subgroup, the
  subgroup has exponent two, and `TauCeti.monoidHom_sq_eq_one_of_mem_of_conj_eq_inv`: every
  homomorphism from it to a commutative monoid squares to one.
* `TauCeti.conj_eq_inv_of_notMem_of_index_two`: **one inverting element outside a subgroup of index
  two makes every element outside it invert.**
* `TauCeti.sq_eq_sq_of_notMem_of_index_two`: the elements outside such a subgroup all have the same
  square, and `TauCeti.sq_sq_eq_one_of_conj_eq_inv`: that square squares to one.
* `TauCeti.card_filter_notMem_eq_card_of_index_two`: the complement of a subgroup of index two in a
  finite group has as many elements as the subgroup.
* `TauCeti.eq_mk_one_or_eq_mk_of_index_two`: **a subgroup of index two has exactly two cosets**,
  the trivial one and that of any outside element, and
  `TauCeti.sum_quotient_eq_add_of_index_two`: a finite sum over them is the sum of two terms.
* `TauCeti.smul_mk_one_of_notMem_of_index_two` and `TauCeti.smul_mk_of_notMem_of_index_two`: an
  element outside a subgroup of index two exchanges the two cosets.
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

/-- **A subgroup inverted by conjugation by one of its own elements has exponent two.**  If an
element `s ∈ N` satisfies `s * x * s⁻¹ = x⁻¹` for every `x ∈ N`, then `x ^ 2 = 1` for every
`x ∈ N`. -/
theorem sq_eq_one_of_mem_of_conj_eq_inv {s : G} (hs : s ∈ N)
    (hinv : ∀ x ∈ N, s * x * s⁻¹ = x⁻¹) {x : G} (hx : x ∈ N) : x ^ 2 = 1 := by
  -- `N` is abelian, so conjugation by `s ∈ N` fixes `x`, which is therefore its own inverse.
  have hcomm : s * x = x * s := by
    simpa using congrArg Subtype.val
      (isMulCommutative_iff.mp (isMulCommutative_of_conj_eq_inv hinv) ⟨s, hs⟩ ⟨x, hx⟩)
  have h := hinv x hx
  rw [hcomm, mul_inv_cancel_right] at h
  rw [pow_two]
  nth_rewrite 2 [h]
  exact mul_inv_cancel x

/-- **A homomorphism to a commutative monoid squares to one on a subgroup inverted by one of its
own elements**, that subgroup having exponent two (`TauCeti.sq_eq_one_of_mem_of_conj_eq_inv`).
Read contrapositively, a single `ψ` with `ψ ^ 2 ≠ 1` places every element inverting `N` outside
`N`. -/
theorem monoidHom_sq_eq_one_of_mem_of_conj_eq_inv {M : Type*} [CommMonoid M] {s : G}
    (hs : s ∈ N) (hinv : ∀ x ∈ N, s * x * s⁻¹ = x⁻¹) (ψ : N →* M) : ψ ^ 2 = 1 := by
  ext x
  have hx : x ^ 2 = 1 := Subtype.ext (by simpa using sq_eq_one_of_mem_of_conj_eq_inv hs hinv x.2)
  rw [MonoidHom.pow_apply, ← map_pow, hx, map_one, MonoidHom.one_apply]

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

/-! ### The two cosets of a subgroup of index two -/

/-- The coset of an element outside `N` is not the trivial coset. No hypothesis on the index is
needed. -/
theorem mk_ne_mk_one_of_notMem {s : G} (hs : s ∉ N) :
    (QuotientGroup.mk s : G ⧸ N) ≠ QuotientGroup.mk 1 := fun h =>
  hs (by simpa using QuotientGroup.eq.1 h)

/-- **A subgroup of index two has exactly two cosets**: the trivial coset and the coset of any
element `s` outside it. -/
theorem eq_mk_one_or_eq_mk_of_index_two (hindex : N.index = 2) {s : G} (hs : s ∉ N)
    (u : G ⧸ N) : u = QuotientGroup.mk 1 ∨ u = QuotientGroup.mk s := by
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective u
  by_cases hb : b ∈ N
  · exact Or.inl (QuotientGroup.eq.2 (by simpa using hb))
  · exact Or.inr (QuotientGroup.eq.2 ((Subgroup.mul_mem_iff_of_index_two hindex).2
      (iff_of_false (mt N.inv_mem_iff.1 hb) hs)))

/-- **A finite sum over the cosets of a subgroup of index two has two terms**, one at the trivial
coset and one at the coset of any element `s` outside the subgroup. -/
theorem sum_quotient_eq_add_of_index_two [Fintype (G ⧸ N)] {M : Type*} [AddCommMonoid M]
    (hindex : N.index = 2) {s : G} (hs : s ∉ N) (f : G ⧸ N → M) :
    ∑ u : G ⧸ N, f u = f (QuotientGroup.mk 1) + f (QuotientGroup.mk s) :=
  Fintype.sum_eq_add _ _ (mk_ne_mk_one_of_notMem hs).symm fun u hu =>
    ((eq_mk_one_or_eq_mk_of_index_two hindex hs u).elim hu.1 hu.2).elim

/-- An element outside a subgroup of index two carries the trivial coset to the coset of any
other element outside it. -/
theorem smul_mk_one_of_notMem_of_index_two (hindex : N.index = 2) {s γ : G} (hs : s ∉ N)
    (hγ : γ ∉ N) : γ • (QuotientGroup.mk 1 : G ⧸ N) = QuotientGroup.mk s := by
  rw [MulAction.Quotient.smul_mk, smul_eq_mul, mul_one, QuotientGroup.eq]
  exact (Subgroup.mul_mem_iff_of_index_two hindex).2 (iff_of_false (mt N.inv_mem_iff.1 hγ) hs)

/-- An element outside a subgroup of index two carries the coset of any element outside it to the
trivial coset. -/
theorem smul_mk_of_notMem_of_index_two (hindex : N.index = 2) {s γ : G} (hs : s ∉ N)
    (hγ : γ ∉ N) : γ • (QuotientGroup.mk s : G ⧸ N) = QuotientGroup.mk 1 := by
  rw [MulAction.Quotient.smul_mk, smul_eq_mul, QuotientGroup.eq, mul_one, inv_mem_iff]
  exact (Subgroup.mul_mem_iff_of_index_two hindex).2 (iff_of_false hγ hs)

end TauCeti
