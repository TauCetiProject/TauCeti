/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.SeparableDegree
public import TauCeti.RingTheory.Invariant.Basic
public import TauCeti.RingTheory.LocalRing.FixedPoints.Basic
public import TauCeti.RingTheory.LocalRing.RamificationGroup.Basic
public import TauCeti.RingTheory.LocalRing.RingHom.Subalgebra
import TauCeti.GroupTheory.Index.Basic
import TauCeti.NumberTheory.RamificationInertia.SeparableDegree

/-!
# Ramification groups and separable residue degrees

Let a finite group `G` act faithfully on the local ring `B` by `A`-algebra automorphisms, with
invariants the local ring `A`. Every element of `G` stabilizes the maximal ideal of `B`, so the
orbit-stabilizer count for the inertia group gives `#G = #G_0 · f_s(B/A)`, where `G_0` is the
ramification group of index `0` and `f_s` is the separable degree of the residue extension.

Applying this to `G` and to a subgroup `H`, acting on `B` with invariants the fixed ring `B^H`,
the index `[G : G_0 H]` is the separable degree of the residue extension of `B^H` over `A`. For a
finite Galois extension `M/K` of complete discretely valued fields, with `G = Gal(M/K)` acting on
the integer ring of `M` and `H = Gal(M/L)`, this is the separable residue degree of `L/K`.

## Main results

* `TauCeti.IsLocalRing.natCard_eq_natCard_ramificationGroup_zero_mul_finSepDegree`:
  `#G = #G_0 · f_s(B/A)`.
* `TauCeti.IsLocalRing.index_ramificationGroup_zero_sup_eq_finSepDegree`: `[G : G_0 H]` is the
  separable residue degree of `B^H` over `A`.

## References

* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter I, §7, Proposition 20, and Chapter IV, §1.
-/

public section

open IsLocalRing

open scoped Pointwise

namespace TauCeti.IsLocalRing

variable {A B : Type*} [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B] [Algebra A B]
  [IsLocalHom (algebraMap A B)]
  {G : Type*} [Group G] [Finite G] [MulSemiringAction G B] [SMulCommClass G A B]
  [Algebra.IsInvariant A B G] [FaithfulSMul G B]

variable (A G) in
attribute [local instance] Ideal.Quotient.field in
/-- `#G = #G_0 · f_s`, with `G_0` the ramification group of index `0` and `f_s` the separable
degree of the residue extension of `B` over `A`: every element of `G` stabilizes the maximal ideal
of `B`, and `G_0` is its inertia group. -/
theorem natCard_eq_natCard_ramificationGroup_zero_mul_finSepDegree :
    Nat.card G = Nat.card (ramificationGroup G B 0) *
      Field.finSepDegree (ResidueField A) (ResidueField B) := by
  have : IsGaloisGroup G A B := ⟨inferInstance, inferInstance, inferInstance⟩
  have h := Ideal.card_stabilizer_eq_card_inertia_mul_finSepDegree (G := G) (maximalIdeal A)
    (maximalIdeal B)
  have htop : MulAction.stabilizer G (maximalIdeal B) = ⊤ :=
    eq_top_iff.2 fun σ _ ↦ smul_maximalIdeal σ
  rw [htop, Subgroup.card_top] at h
  rw [h, ramificationGroup_zero_eq_inertia]
  -- The residue field of a local ring is its quotient by the maximal ideal.
  rfl

variable (A) in
/-- **The index `[G : G_0 H]` is the separable residue degree.** Let a finite group `G` act
faithfully on the local ring `B` by `A`-algebra automorphisms, with invariants the local ring
`A`, and let `H` be a subgroup. Then `[G : G_0 H]` is the separable degree of the residue
extension of the fixed ring `B^H` over `A`. For `G = Gal(M/K)` and `H = Gal(M/L)` this is the
separable residue degree of `L/K`. -/
theorem index_ramificationGroup_zero_sup_eq_finSepDegree (H : Subgroup G) :
    (ramificationGroup G B 0 ⊔ H).index =
      Field.finSepDegree (ResidueField A) (ResidueField (FixedPoints.subalgebra A B H)) := by
  -- `#G = #G_0 · f_s(B/A)` and `#H = #H_0 · f_s(B/B^H)`.
  have hG := natCard_eq_natCard_ramificationGroup_zero_mul_finSepDegree A G (B := B)
  have hH := natCard_eq_natCard_ramificationGroup_zero_mul_finSepDegree
    (FixedPoints.subalgebra A B H) H (B := B)
  -- The separable degree is multiplicative in the residue tower of `A ⊆ B^H ⊆ B`.
  have := Algebra.IsInvariant.isIntegral (FixedPoints.subalgebra A B H) B H
  have : Algebra.IsIntegral B (ResidueField B) :=
    .of_surjective (Algebra.ofId B (ResidueField B)) residue_surjective
  have : Algebra.IsIntegral (FixedPoints.subalgebra A B H) (ResidueField B) := .trans B
  have : IsScalarTower (FixedPoints.subalgebra A B H) (ResidueField (FixedPoints.subalgebra A B H))
      (ResidueField B) :=
    -- Both maps into `ResidueField B` are the residue map of `B` after `B^H → B`, by definition.
    .of_algebraMap_eq fun _ ↦ rfl
  have : Algebra.IsIntegral (ResidueField (FixedPoints.subalgebra A B H)) (ResidueField B) :=
    .tower_top (FixedPoints.subalgebra A B H)
  have hmul := Field.finSepDegree_mul_finSepDegree_of_isAlgebraic (ResidueField A)
    (ResidueField (FixedPoints.subalgebra A B H)) (ResidueField B)
  -- Compare with the product formula `[G : G_0 H] · #G_0 · #H = #G · #H_0`.
  have hP := Subgroup.index_sup_mul_card_mul_card (N := ramificationGroup G B 0) (H := H)
    Subgroup.le_normalizer_of_normal
  rw [subgroupOf_ramificationGroup] at hP
  have hf : Field.finSepDegree (ResidueField (FixedPoints.subalgebra A B H)) (ResidueField B) ≠ 0 :=
    fun h ↦ (Nat.card_pos (α := H)).ne' (by rw [hH, h, mul_zero])
  rw [hG, hH, ← hmul] at hP
  have hG0 : Nat.card (ramificationGroup G B 0) ≠ 0 := Nat.card_pos.ne'
  have hH0 : Nat.card (ramificationGroup H B 0) ≠ 0 := Nat.card_pos.ne'
  refine mul_right_cancel₀ (mul_ne_zero (mul_ne_zero hG0 hH0) hf) ?_
  linear_combination hP

end TauCeti.IsLocalRing
