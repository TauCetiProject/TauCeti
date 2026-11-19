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
public import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Nat.Cast.Field
import Mathlib.GroupTheory.GroupAction.FixedPoints
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.GroupTheory.Coset.Card
import Mathlib.GroupTheory.GroupAction.CardCommute
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import TauCeti.SetTheory.Cardinal.Finite

/-!
# Burnside's lemma on products, and for constant fixed-point counts

A point of a product `G`-set `X × Y` is fixed by `g` exactly when both of its components are, so
Mathlib's Burnside lemma `MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group`, applied to
`X × Y`, reads

`∑ g : G, |X^g| * |Y^g| = |(X × Y) / G| * |G|`.

This is the shape in which Burnside's lemma computes the pairing of two permutation characters.
For disjoint unions, the analogous counting rules add the fixed-point counts, including for an
indexed family of sets on which the action leaves the index fixed.

When every nonidentity element of a finite group `G` fixes the same number `k` of points of a
finite `G`-set `X`, Burnside's lemma together with the class formula `|X| = ∑ |G| / mⱼ` gives

`∑ⱼ (1 - 1 / mⱼ) = k * (1 - 1 / |G|)`,

the sum running over the orbits and `mⱼ` being the order of the stabilizer of a point of the
`j`-th orbit. For `k = 2` this is the equation that classifies the finite groups of rotations of
three-space through their action on poles.

## Main statements

* `TauCeti.fixedBy_prod`: the fixed points of `g` on `X × Y` are the product of its fixed points
  on `X` and on `Y`.
* `TauCeti.card_fixedBy_prod`: the corresponding count.
* `TauCeti.card_fixedBy_sum` and `TauCeti.card_fixedBy_sigma`: fixed-point counts on
  disjoint unions.
* `TauCeti.sum_card_fixedBy_mul_card_fixedBy_eq_card_orbits_mul_card_group`: Burnside's lemma
  on `X × Y`.
* `TauCeti.sum_one_sub_one_div_card_stabilizer_eq`: the orbit equation
  `∑ⱼ (1 - 1 / mⱼ) = k * (1 - 1 / |G|)` when every nonidentity element fixes `k` points.

## Implementation notes

Counts are phrased with `Nat.card`, with `Set.ncard` simp forms for disjoint unions.
Mathlib's Burnside lemma is stated with `Fintype.card` and
carries `Fintype` instances for each fixed-point set, which are supplied here from `Finite X` and
`Finite Y` rather than assumed.

## References

* M. Artin, *Algebra*, second edition, Pearson, 2011, Section 6.12, for the orbit equation.
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
  rw [hcard, Nat.card_sigma_eq_finsum]

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

variable {X}

/-- **The orbit equation for a constant fixed-point count.** If every nonidentity element of a
finite group `G` fixes exactly `k` points of a finite `G`-set `X`, then summing `1 - 1 / mⱼ` over
the orbits, where `mⱼ` is the order of the stabilizer of a point of the `j`-th orbit, gives
`k * (1 - 1 / |G|)`. -/
theorem sum_one_sub_one_div_card_stabilizer_eq [Finite G] [Finite X]
    [Fintype (orbitRel.Quotient G X)] {k : ℕ}
    (hk : ∀ g : G, g ≠ 1 → Nat.card (fixedBy X g) = k) :
    ∑ ω : orbitRel.Quotient G X, (1 - 1 / (Nat.card (stabilizer G ω.out) : ℚ)) =
      k * (1 - 1 / Nat.card G) := by
  classical
  have := Fintype.ofFinite G
  have := Fintype.ofFinite X
  have hN : (Nat.card G : ℚ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  -- Burnside's lemma, with the identity fixing every point: `|X| + (|G| - 1) k = s |G|`.
  have hburnside : (Nat.card X : ℚ) + (Nat.card G - 1) * k =
      Fintype.card (orbitRel.Quotient G X) * Nat.card G := by
    have h := sum_card_fixedBy_eq_card_orbits_mul_card_group G X
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ 1)] at h
    have hsum : ∑ g ∈ Finset.univ.erase (1 : G), Fintype.card (fixedBy X g) =
        (Nat.card G - 1) * k := by
      rw [Finset.sum_congr rfl fun g hg ↦ by
        rw [← Nat.card_eq_fintype_card, hk g (Finset.ne_of_mem_erase hg)]]
      simp [Finset.card_erase_of_mem, Nat.card_eq_fintype_card]
    have h1 : Fintype.card (fixedBy X (1 : G)) = Nat.card X := by
      rw [← Nat.card_eq_fintype_card, fixedBy_one_eq_univ, Nat.card_univ]
    rw [hsum, h1, ← Nat.card_eq_fintype_card (α := G)] at h
    have hG : 1 ≤ Nat.card G := Nat.card_pos
    rw [← Nat.cast_inj (R := ℚ)] at h
    push_cast [hG] at h
    exact h
  -- The class formula, with orbit sizes `|G| / mⱼ`.
  have hclass : (Nat.card X : ℚ) = ∑ ω : orbitRel.Quotient G X,
      (Nat.card G : ℚ) / Nat.card (stabilizer G ω.out) := by
    have h := card_eq_sum_card_group_div_card_stabilizer G X
    simp only [← Nat.card_eq_fintype_card] at h
    rw [h, Nat.cast_sum]
    refine Finset.sum_congr rfl fun ω _ ↦ ?_
    rw [Nat.cast_div (Subgroup.card_subgroup_dvd_card _) (by exact_mod_cast Nat.card_pos.ne')]
  -- Hence `∑ⱼ (1 - 1 / mⱼ) = s - |X| / |G|`, and Burnside's lemma evaluates this.
  have hinv (ω : orbitRel.Quotient G X) : 1 / (Nat.card (stabilizer G ω.out) : ℚ) =
      (Nat.card G : ℚ) / Nat.card (stabilizer G ω.out) / Nat.card G := by
    field_simp
  simp_rw [Finset.sum_sub_distrib, hinv, ← Finset.sum_div, ← hclass, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, mul_one]
  field_simp
  linear_combination -hburnside

end TauCeti
