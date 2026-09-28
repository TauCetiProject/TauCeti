/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Perm.List
public import TauCeti.GroupTheory.Perm.MultipleTransitivity
public import TauCeti.GroupTheory.Perm.Recognition
public import TauCeti.GroupTheory.TriangleGroup.Basic

/-!
# Polyhedral permutation representations of triangle groups

The spherical triangle groups with signatures `(2, 3, 3)`, `(2, 3, 4)`, and `(2, 3, 5)`
have concrete permutation representations whose images are respectively the tetrahedral,
octahedral, and icosahedral rotation groups. This file constructs those representations and
identifies their images with `A₄`, `S₄`, and `A₅`.

These maps provide explicit finite quotients of the three spherical triangle groups, of orders
`12`, `24`, and `60`. Their image cardinalities give the lower bounds which, together with matching
coset-enumeration upper bounds, identify the triangle groups themselves with the corresponding
polyhedral rotation groups.

## Main definitions

* `TauCeti.TriangleGroup.tetrahedralRep`: the `(2, 3, 3)` representation with image `A₄`.
* `TauCeti.TriangleGroup.octahedralRep`: the `(2, 3, 4)` representation with image `S₄`.
* `TauCeti.TriangleGroup.icosahedralRep`: the `(2, 3, 5)` representation with image `A₅`.

## References

* E. Girondo and G. González-Diez, *Introduction to Compact Riemann Surfaces and Dessins
  d'Enfants*, Remark 2.30.
-/

public section

namespace TauCeti

open Equiv Equiv.Perm MulAction

namespace TriangleGroup

/-! ### The tetrahedral representation -/

/-- The tetrahedral permutation representation of `Δ(2, 3, 3)` on its four vertices.

The first generator is the double transposition `(0 1)(2 3)` and the second is the
three-cycle `(0 1 2)`. -/
def tetrahedralRep : TriangleGroup 2 3 3 →* Perm (Fin 4) :=
  lift (swap 0 1 * swap 2 3) ([0, 1, 2] : List (Fin 4)).formPerm
    (([0, 1, 2] : List (Fin 4)).formPerm * (swap 0 1 * swap 2 3))⁻¹
    (by decide) (by decide) (by decide) (by group)

@[simp]
theorem tetrahedralRep_x :
    tetrahedralRep (x 2 3 3) = swap 0 1 * swap 2 3 :=
  lift_x ..

@[simp]
theorem tetrahedralRep_y :
    tetrahedralRep (y 2 3 3) = ([0, 1, 2] : List (Fin 4)).formPerm :=
  lift_y ..

@[simp]
theorem tetrahedralRep_z :
    tetrahedralRep (z 2 3 3) = ([0, 3, 2] : List (Fin 4)).formPerm := by
  rw [tetrahedralRep, lift_z]
  decide

private theorem isPretransitive_tetrahedralGenerators :
    IsPretransitive
      (Subgroup.closure
        {swap 0 1 * swap 2 3, ([0, 1, 2] : List (Fin 4)).formPerm})
      (Fin 4) := by
  let a : Perm (Fin 4) := swap 0 1 * swap 2 3
  let b : Perm (Fin 4) := ([0, 1, 2] : List (Fin 4)).formPerm
  let G : Subgroup (Perm (Fin 4)) := Subgroup.closure {a, b}
  have ha : a ∈ G := Subgroup.subset_closure (Set.mem_insert a {b})
  have hb : b ∈ G := Subgroup.subset_closure (Set.mem_insert_of_mem a rfl)
  have horbit : orbit G (0 : Fin 4) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro i
    rw [mem_orbit_iff]
    fin_cases i
    · exact ⟨1, rfl⟩
    · exact ⟨⟨a, ha⟩, by simp only [Subgroup.smul_def, Perm.smul_def]; apply Fin.ext; decide⟩
    · exact ⟨⟨b ^ 2, G.pow_mem hb 2⟩,
        by simp only [Subgroup.smul_def, Perm.smul_def]; apply Fin.ext; decide⟩
    · exact ⟨⟨a * b ^ 2, G.mul_mem ha (G.pow_mem hb 2)⟩,
        by simp only [Subgroup.smul_def, Perm.smul_def]; apply Fin.ext; decide⟩
  exact (isPretransitive_iff_orbit_eq_univ 0).mpr horbit

/-- The image of the tetrahedral representation is the alternating group `A₄`. -/
@[simp]
theorem range_tetrahedralRep :
    tetrahedralRep.range = alternatingGroup (Fin 4) := by
  rw [range_eq_closure, tetrahedralRep_x, tetrahedralRep_y]
  let a : Perm (Fin 4) := swap 0 1 * swap 2 3
  let b : Perm (Fin 4) := ([0, 1, 2] : List (Fin 4)).formPerm
  let G : Subgroup (Perm (Fin 4)) := Subgroup.closure {a, b}
  have ha : a ∈ G := Subgroup.subset_closure (Set.mem_insert a {b})
  have hb : b ∈ G := Subgroup.subset_closure (Set.mem_insert_of_mem a rfl)
  have haEven : a ∈ alternatingGroup (Fin 4) :=
    Perm.mul_mem_alternatingGroup_of_isSwap
      (Perm.swap_isSwap_iff.mpr (by decide)) (Perm.swap_isSwap_iff.mpr (by decide))
  have hbSupport : b.support.card = 3 := by
    simp only [b]
    rw [List.support_formPerm_of_nodup _ (by decide) (by decide)]
    decide
  have hbThree : b.IsThreeCycle := card_support_eq_three_iff.mp hbSupport
  have htrans : IsPretransitive G (Fin 4) := isPretransitive_tetrahedralGenerators
  let _ : IsPretransitive G (Fin 4) := htrans
  have hprimitive : IsPreprimitive G (Fin 4) :=
    isPreprimitive_of_isCycle_mem_of_card_support_add_one_eq_card G hbThree.isCycle hb (by
      rw [hbThree.card_support]
      simp)
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro g (rfl | rfl)
    · exact haEven
    · exact Perm.mem_alternatingGroup.mpr hbThree.sign
  · exact alternatingGroup_le_of_isPreprimitive_of_isThreeCycle_mem
      hprimitive hbThree hb

/-- The tetrahedral image has order `12`. -/
theorem natCard_range_tetrahedralRep : Nat.card tetrahedralRep.range = 12 := by
  rw [range_tetrahedralRep, nat_card_alternatingGroup, Nat.card_fin]
  norm_num [Nat.factorial]

/-! ### The octahedral representation -/

/-- The octahedral permutation representation of `Δ(2, 3, 4)` on the four body diagonals.

The first generator is the transposition `(0 1)` and the second is the three-cycle `(1 2 3)`. -/
def octahedralRep : TriangleGroup 2 3 4 →* Perm (Fin 4) :=
  lift (swap 0 1) ([1, 2, 3] : List (Fin 4)).formPerm
    (([1, 2, 3] : List (Fin 4)).formPerm * swap 0 1)⁻¹
    (by decide) (by decide) (by decide) (by group)

@[simp]
theorem octahedralRep_x : octahedralRep (x 2 3 4) = swap 0 1 :=
  lift_x ..

@[simp]
theorem octahedralRep_y :
    octahedralRep (y 2 3 4) = ([1, 2, 3] : List (Fin 4)).formPerm :=
  lift_y ..

@[simp]
theorem octahedralRep_z :
    octahedralRep (z 2 3 4) = ([0, 1, 3, 2] : List (Fin 4)).formPerm := by
  rw [octahedralRep, lift_z]
  decide

private theorem isPretransitive_octahedralGenerators :
    IsPretransitive
      (Subgroup.closure {swap 0 1, ([1, 2, 3] : List (Fin 4)).formPerm})
      (Fin 4) := by
  let a : Perm (Fin 4) := swap 0 1
  let b : Perm (Fin 4) := ([1, 2, 3] : List (Fin 4)).formPerm
  let g : Perm (Fin 4) := b * a
  let G : Subgroup (Perm (Fin 4)) := Subgroup.closure {a, b}
  have ha : a ∈ G := Subgroup.subset_closure (Set.mem_insert a {b})
  have hb : b ∈ G := Subgroup.subset_closure (Set.mem_insert_of_mem a rfl)
  have hg : g ∈ G := G.mul_mem hb ha
  have hg_eq : g = ([0, 2, 3, 1] : List (Fin 4)).formPerm := by
    ext i
    fin_cases i <;> decide
  have hgCycle : g.IsCycle := by
    rw [hg_eq]
    exact List.isCycle_formPerm (by decide) (by decide)
  have hgSupport : g.support = Finset.univ := by
    rw [hg_eq, List.support_formPerm_of_nodup _ (by decide) (by decide)]
    decide
  exact isPretransitive_of_isCycle_mem_of_support_eq_univ hgCycle hg hgSupport

/-- The image of the octahedral representation is the full symmetric group `S₄`. -/
@[simp]
theorem range_octahedralRep : octahedralRep.range = ⊤ := by
  rw [range_eq_closure, octahedralRep_x, octahedralRep_y]
  let a : Perm (Fin 4) := swap 0 1
  let b : Perm (Fin 4) := ([1, 2, 3] : List (Fin 4)).formPerm
  let G : Subgroup (Perm (Fin 4)) := Subgroup.closure {a, b}
  have ha : a ∈ G := Subgroup.subset_closure (Set.mem_insert a {b})
  have hb : b ∈ G := Subgroup.subset_closure (Set.mem_insert_of_mem a rfl)
  have hbSupport : b.support.card = 3 := by
    simp only [b]
    rw [List.support_formPerm_of_nodup _ (by decide) (by decide)]
    decide
  have hbThree : b.IsThreeCycle := card_support_eq_three_iff.mp hbSupport
  have htrans : IsPretransitive G (Fin 4) := isPretransitive_octahedralGenerators
  let _ : IsPretransitive G (Fin 4) := htrans
  have hprimitive : IsPreprimitive G (Fin 4) :=
    isPreprimitive_of_isCycle_mem_of_card_support_add_one_eq_card G hbThree.isCycle hb (by
      rw [hbThree.card_support]
      simp)
  exact subgroup_eq_top_of_isPreprimitive_of_isSwap_mem
    hprimitive a (Perm.swap_isSwap_iff.mpr (by decide)) ha

/-- The octahedral image has order `24`. -/
theorem natCard_range_octahedralRep : Nat.card octahedralRep.range = 24 := by
  rw [range_octahedralRep, Subgroup.card_top, Nat.card_perm, Nat.card_fin]
  norm_num [Nat.factorial]

/-! ### The icosahedral representation -/

/-- The icosahedral permutation representation of `Δ(2, 3, 5)` on five inscribed cubes.

The first generator is the double transposition `(0 1)(2 3)` and the second is the
three-cycle `(0 4 2)`. -/
def icosahedralRep : TriangleGroup 2 3 5 →* Perm (Fin 5) :=
  lift (swap 0 1 * swap 2 3) ([0, 4, 2] : List (Fin 5)).formPerm
    (([0, 4, 2] : List (Fin 5)).formPerm * (swap 0 1 * swap 2 3))⁻¹
    (by decide) (by decide) (by decide) (by group)

@[simp]
theorem icosahedralRep_x :
    icosahedralRep (x 2 3 5) = swap 0 1 * swap 2 3 :=
  lift_x ..

@[simp]
theorem icosahedralRep_y :
    icosahedralRep (y 2 3 5) = ([0, 4, 2] : List (Fin 5)).formPerm :=
  lift_y ..

@[simp]
theorem icosahedralRep_z :
    icosahedralRep (z 2 3 5) = ([0, 3, 2, 4, 1] : List (Fin 5)).formPerm := by
  rw [icosahedralRep, lift_z]
  decide

private theorem isPretransitive_icosahedralGenerators :
    IsPretransitive
      (Subgroup.closure
        {swap 0 1 * swap 2 3, ([0, 4, 2] : List (Fin 5)).formPerm})
      (Fin 5) := by
  let a : Perm (Fin 5) := swap 0 1 * swap 2 3
  let b : Perm (Fin 5) := ([0, 4, 2] : List (Fin 5)).formPerm
  let g : Perm (Fin 5) := b * a
  let G : Subgroup (Perm (Fin 5)) := Subgroup.closure {a, b}
  have ha : a ∈ G := Subgroup.subset_closure (Set.mem_insert a {b})
  have hb : b ∈ G := Subgroup.subset_closure (Set.mem_insert_of_mem a rfl)
  have hg : g ∈ G := G.mul_mem hb ha
  have hg_eq : g = ([0, 1, 4, 2, 3] : List (Fin 5)).formPerm := by
    ext i
    fin_cases i <;> decide
  have hgCycle : g.IsCycle := by
    rw [hg_eq]
    exact List.isCycle_formPerm (by decide) (by decide)
  have hgSupport : g.support = Finset.univ := by
    rw [hg_eq, List.support_formPerm_of_nodup _ (by decide) (by decide)]
    decide
  exact isPretransitive_of_isCycle_mem_of_support_eq_univ hgCycle hg hgSupport

/-- The image of the icosahedral representation is the alternating group `A₅`. -/
@[simp]
theorem range_icosahedralRep :
    icosahedralRep.range = alternatingGroup (Fin 5) := by
  rw [range_eq_closure, icosahedralRep_x, icosahedralRep_y]
  let a : Perm (Fin 5) := swap 0 1 * swap 2 3
  let b : Perm (Fin 5) := ([0, 4, 2] : List (Fin 5)).formPerm
  let G : Subgroup (Perm (Fin 5)) := Subgroup.closure {a, b}
  have hb : b ∈ G := Subgroup.subset_closure (Set.mem_insert_of_mem a rfl)
  have haEven : a ∈ alternatingGroup (Fin 5) :=
    Perm.mul_mem_alternatingGroup_of_isSwap
      (Perm.swap_isSwap_iff.mpr (by decide)) (Perm.swap_isSwap_iff.mpr (by decide))
  have hbSupport : b.support.card = 3 := by
    simp only [b]
    rw [List.support_formPerm_of_nodup _ (by decide) (by decide)]
    decide
  have hbThree : b.IsThreeCycle := card_support_eq_three_iff.mp hbSupport
  have htrans : IsPretransitive G (Fin 5) := isPretransitive_icosahedralGenerators
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro g (rfl | rfl)
    · exact haEven
    · exact Perm.mem_alternatingGroup.mpr hbThree.sign
  · exact alternatingGroup_le_of_isPretransitive_of_orderOf_eq_three
      (by decide) htrans hbThree.orderOf hb

/-- The icosahedral image has order `60`. -/
theorem natCard_range_icosahedralRep : Nat.card icosahedralRep.range = 60 := by
  rw [range_icosahedralRep, nat_card_alternatingGroup, Nat.card_fin]
  norm_num [Nat.factorial]

end TriangleGroup

end TauCeti
