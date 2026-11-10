/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.Group.Action.Sigma
public import Mathlib.Algebra.Group.Action.Sum
public import Mathlib.Data.Set.Card
import Mathlib.Logic.Equiv.Sigma

/-!
# Burnside's lemma on a product of two `G`-sets

A point of a product `G`-set `X × Y` is fixed by `g` exactly when both of its components are, so
Mathlib's Burnside lemma `MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group`, applied to
`X × Y`, reads

`∑ g : G, |X^g| * |Y^g| = |(X × Y) / G| * |G|`.

This is the shape in which Burnside's lemma computes the pairing of two permutation characters.
For disjoint unions, the analogous counting rules add the fixed-point counts, including for an
indexed family of sets on which the action leaves the index fixed.

## Main statements

* `TauCeti.fixedBy_prod`: the fixed points of `g` on `X × Y` are the product of its fixed points
  on `X` and on `Y`.
* `TauCeti.card_fixedBy_prod`: the corresponding count.
* `TauCeti.card_fixedBy_sum` and `TauCeti.card_fixedBy_sigma`: fixed-point counts on
  disjoint unions.
* `TauCeti.sum_card_fixedBy_mul_card_fixedBy_eq_card_orbits_mul_card_group`: Burnside's lemma
  on `X × Y`.

## Implementation notes

Counts are phrased with `Nat.card`, with `Set.ncard` simp forms for disjoint unions.
Mathlib's Burnside lemma is stated with `Fintype.card` and
carries `Fintype` instances for each fixed-point set, which are supplied here from `Finite X` and
`Finite Y` rather than assumed.
-/

public section

open MulAction

namespace TauCeti

variable {G : Type*} (X Y : Type*)

section Monoid

variable [Monoid G] [MulAction G X] [MulAction G Y]

/-- A point of a product `G`-set is fixed exactly when both of its components are. -/
@[simp]
theorem fixedBy_prod (g : G) : fixedBy (X × Y) g = fixedBy X g ×ˢ fixedBy Y g := by
  ext p
  simp [mem_fixedBy, Prod.ext_iff, Set.mem_prod]

/-- The fixed points of `g` on a product `G`-set are counted by the product of the two
fixed-point counts. -/
theorem card_fixedBy_prod (g : G) :
    Nat.card (fixedBy (X × Y) g) = Nat.card (fixedBy X g) * Nat.card (fixedBy Y g) := by
  rw [fixedBy_prod, Nat.card_congr (Equiv.Set.prod _ _), Nat.card_prod]

variable {X Y}

/-- The fixed points on a disjoint union are counted by the sum of the fixed-point counts,
provided both fixed-point sets are finite. -/
theorem card_fixedBy_sum (g : G) [Finite (fixedBy X g)] [Finite (fixedBy Y g)] :
    Nat.card (fixedBy (X ⊕ Y) g) = Nat.card (fixedBy X g) + Nat.card (fixedBy Y g) := by
  rw [← Nat.card_sum]
  exact Nat.card_congr <| Equiv.subtypeSum.trans <| .sumCongr
    (.subtypeEquivRight fun _ ↦ by simp [mem_fixedBy])
    (.subtypeEquivRight fun _ ↦ by simp [mem_fixedBy])

/-- The fixed-point count on a disjoint union, in simp normal form. -/
@[simp]
theorem ncard_fixedBy_sum (g : G) [Finite (fixedBy X g)] [Finite (fixedBy Y g)] :
    (fixedBy (X ⊕ Y) g).ncard = (fixedBy X g).ncard + (fixedBy Y g).ncard := by
  simpa only [Nat.card_coe_set_eq] using card_fixedBy_sum g

/-- For the fiberwise action on an indexed disjoint union, fixed-point counts add over the
indices, provided each fixed-point set is finite. The monoid fixes the index of each point. -/
theorem card_fixedBy_sigma {ι : Type*} (X : ι → Type*) [∀ i, MulAction G (X i)]
    (g : G) [∀ i, Finite (fixedBy (X i) g)] :
    Nat.card (fixedBy (Σ i, X i) g) = ∑ᶠ i, Nat.card (fixedBy (X i) g) := by
  have hset : fixedBy (Σ i, X i) g = Set.univ.sigma (fun i ↦ fixedBy (X i) g) := by
    ext ⟨i, x⟩
    simp [mem_fixedBy]
  have hcard : Nat.card (fixedBy (Σ i, X i) g) = Nat.card (Σ i, fixedBy (X i) g) := by
    rw [hset]
    exact Nat.card_congr <| (Equiv.Set.sigma _ _).trans <|
      .sigmaCongrLeft (β := fun i ↦ fixedBy (X i) g) (Equiv.Set.univ ι)
  rw [hcard]
  by_cases hs : (Function.support fun i ↦ Nat.card (fixedBy (X i) g)).Finite
  · have := hs.fintype
    have hempty : ∀ i ∉ hs.toFinset, IsEmpty (fixedBy (X i) g) := fun i hi ↦
      (Nat.card_eq_zero.mp (Function.notMem_support.mp (hs.mem_toFinset.not.mp hi))).resolve_right
        (not_infinite_iff_finite.mpr inferInstance)
    rw [finsum_eq_sum_of_support_subset _ (s := hs.toFinset) (by simp), ← Finset.sum_coe_sort,
      ← Nat.card_sigma]
    refine (Nat.card_congr (Equiv.ofBijective
      (fun p : Σ i : hs.toFinset, fixedBy (X i) g ↦ (⟨p.1.1, p.2⟩ : Σ i, fixedBy (X i) g))
      ⟨?_, ?_⟩)).symm
    · rintro ⟨⟨i, hi⟩, x⟩ ⟨⟨j, hj⟩, y⟩ h
      simp only [Sigma.mk.inj_iff] at h
      obtain ⟨rfl, h⟩ := h
      simp_all
    · rintro ⟨i, x⟩
      by_cases hi : i ∈ hs.toFinset
      · exact ⟨⟨⟨i, hi⟩, x⟩, rfl⟩
      · exact (hempty i hi).elim x
  · rw [finsum_of_infinite_support hs]
    have : Infinite (Function.support fun i ↦ Nat.card (fixedBy (X i) g)) :=
      Set.infinite_coe_iff.mpr hs
    have hne : ∀ i : Function.support fun i ↦ Nat.card (fixedBy (X i) g),
        Nonempty (fixedBy (X i) g) := fun i ↦
      (Nat.card_pos_iff.mp (Nat.pos_of_ne_zero i.2)).1
    have : Infinite (Σ i, fixedBy (X i) g) :=
      Infinite.of_injective (fun i : Function.support fun i ↦ Nat.card (fixedBy (X i) g) ↦
        (⟨i.1, (hne i).some⟩ : Σ i, fixedBy (X i) g))
        fun i j h ↦ Subtype.ext (congrArg Sigma.fst h)
    exact Nat.card_eq_zero_of_infinite

/-- The fixed-point count on a fiberwise indexed disjoint union, in simp normal form. -/
@[simp]
theorem ncard_fixedBy_sigma {ι : Type*} (X : ι → Type*) [∀ i, MulAction G (X i)]
    (g : G) [∀ i, Finite (fixedBy (X i) g)] :
    (fixedBy (Σ i, X i) g).ncard = ∑ᶠ i, (fixedBy (X i) g).ncard := by
  simpa only [Nat.card_coe_set_eq] using card_fixedBy_sigma X g

end Monoid

variable [Group G] [MulAction G X] [MulAction G Y]

/-- **Burnside's lemma on a product.** For a finite group `G` acting on two finite sets `X` and
`Y`, the sum over `g : G` of the product of the two fixed-point counts is the number of orbits of
`G` on `X × Y`, times the order of `G`. -/
theorem sum_card_fixedBy_mul_card_fixedBy_eq_card_orbits_mul_card_group
    [Fintype G] [Finite X] [Finite Y] :
    ∑ g : G, Nat.card (fixedBy X g) * Nat.card (fixedBy Y g) =
      Nat.card (orbitRel.Quotient G (X × Y)) * Nat.card G := by
  classical
  have := Fintype.ofFinite (X × Y)
  have := Fintype.ofFinite (orbitRel.Quotient G (X × Y))
  simpa only [← Nat.card_eq_fintype_card, card_fixedBy_prod] using
    sum_card_fixedBy_eq_card_orbits_mul_card_group G (X × Y)

end TauCeti
