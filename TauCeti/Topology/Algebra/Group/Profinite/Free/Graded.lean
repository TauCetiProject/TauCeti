/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import TauCeti.Topology.Algebra.Group.LowerCentralSeries.Graded.Basic
public import TauCeti.Topology.Algebra.Group.Profinite.Free.ProP

/-!
# A nonzero bracket in the free pro-2 group

The classes of the two canonical generators of `freeProP 2 (Fin 2)` have a nonzero bracket.
To detect it, send the generators to a rotation and a reflection in the dihedral group of
order eight. Their commutator is nontrivial, while the second lower `2`-series term of the
dihedral group is trivial.

The degree-zero power-defect formula then shows that the `2`-power operator on this free
pro-`2` group is not additive.

## Main results

* `TauCeti.gradedBracket_freeProP_two_ne_zero`: the bracket of the two generator classes is nonzero.
* `TauCeti.gradedPow_add_freeProP_two_ne`: the power operator fails additivity on those classes.
* `TauCeti.gradedPow_freeProP_two_not_additive`: the power operator is not additive in degree zero.
-/

public section

namespace TauCeti

open Subgroup DihedralGroup
open scoped commutatorElement

private theorem pLowerCentralSeries_dihedral_four_two
    [TopologicalSpace (DihedralGroup 4)] [DiscreteTopology (DihedralGroup 4)] :
    pLowerCentralSeries 2 (DihedralGroup 4) 2 = ⊥ := by
  have hsquare : ∀ x : DihedralGroup 4, x ^ 2 ∈ center (DihedralGroup 4) := by
    simp only [mem_center_iff]
    decide
  have hcomm : ∀ x y : DihedralGroup 4, ⁅x, y⁆ ∈ center (DihedralGroup 4) := by
    simp only [mem_center_iff]
    decide
  have hfirst : pLowerCentralSeries 2 (DihedralGroup 4) 1 ≤ center (DihedralGroup 4) := by
    rw [pLowerCentralSeries_succ, pLowerCentralSeries_zero]
    exact (pLowerCentralStep_le_iff (isClosed_discrete _)).mpr
      ⟨fun x _ ↦ hsquare x, commutator_le.mpr fun x _ y _ ↦ hcomm x y⟩
  have hcenter : pLowerCentralStep 2 (center (DihedralGroup 4)) ≤ ⊥ := by
    refine (pLowerCentralStep_le_iff (isClosed_discrete _)).mpr ⟨?_, ?_⟩
    · simp only [mem_center_iff, mem_bot]
      decide
    · exact (commutator_center_left ⊤).le
  apply eq_bot_iff.mpr
  rw [pLowerCentralSeries_succ]
  exact (pLowerCentralStep_mono hfirst).trans hcenter

/-- In the free pro-`2` group of rank two, the bracket of the two canonical generator
classes is nonzero in degree one. -/
theorem gradedBracket_freeProP_two_ne_zero
    (x y : gradedPiece 2 (freeProP 2 (Fin 2)) 0)
    (hx : x = gradedMk 2 _ 0 ⟨freeProP.of (p := 2) (0 : Fin 2), by simp⟩)
    (hy : y = gradedMk 2 _ 0 ⟨freeProP.of (p := 2) (1 : Fin 2), by simp⟩) :
    gradedBracket 2 (freeProP 2 (Fin 2)) 0 0 x y ≠ 0 := by
  let : TopologicalSpace (DihedralGroup 4) := ⊥
  let : DiscreteTopology (DihedralGroup 4) := ⟨rfl⟩
  have hD : IsProP 2 (DihedralGroup 4) :=
    (IsPGroup.of_card (n := 3) (DihedralGroup.nat_card (n := 4))).isProP
  let generators : Fin 2 → DihedralGroup 4 := fun i ↦ if i = 0 then r 1 else sr 0
  let f := freeProP.lift hD generators
  have hf0 : f (freeProP.of (p := 2) (0 : Fin 2)) = r 1 := by simp [f, generators]
  have hf1 : f (freeProP.of (p := 2) (1 : Fin 2)) = sr 0 := by simp [f, generators]
  subst x y
  rw [gradedBracket_gradedMk, ne_eq, gradedMk_eq_zero_iff]
  intro h
  have hm := f.toMonoidHom.map_pLowerCentralSeries_le f.continuous 2
    (mem_map_of_mem f.toMonoidHom h)
  have hne : ⁅(r 1 : DihedralGroup 4), (sr 0 : DihedralGroup 4)⁆ ≠ 1 := by decide
  rw [pLowerCentralSeries_dihedral_four_two, mem_bot, coe_mk, coe_mk, coe_mk,
    map_commutatorElement, ContinuousMonoidHom.coe_toMonoidHom, MonoidHom.coe_ofClass, hf0,
    hf1] at hm
  exact hne hm

/-- The `2`-power operator fails additivity on the two canonical generator classes of
the free pro-`2` group of rank two. -/
theorem gradedPow_add_freeProP_two_ne
    (x y : gradedPiece 2 (freeProP 2 (Fin 2)) 0)
    (hx : x = gradedMk 2 _ 0 ⟨freeProP.of (p := 2) (0 : Fin 2), by simp⟩)
    (hy : y = gradedMk 2 _ 0 ⟨freeProP.of (p := 2) (1 : Fin 2), by simp⟩) :
    gradedPow 2 (freeProP 2 (Fin 2)) 0 (x + y) ≠
      gradedPow 2 (freeProP 2 (Fin 2)) 0 x + gradedPow 2 (freeProP 2 (Fin 2)) 0 y := by
  intro h
  apply gradedBracket_freeProP_two_ne_zero x y hx hy
  rw [gradedPow_add_zero_of_two rfl] at h
  exact add_left_cancel (h.trans (add_zero _).symm)

/-- The degree-zero `2`-power operator of the free pro-`2` group of rank two is not additive. -/
theorem gradedPow_freeProP_two_not_additive :
    ¬ ∀ x y : gradedPiece 2 (freeProP 2 (Fin 2)) 0,
      gradedPow 2 (freeProP 2 (Fin 2)) 0 (x + y) =
        gradedPow 2 (freeProP 2 (Fin 2)) 0 x + gradedPow 2 (freeProP 2 (Fin 2)) 0 y := by
  intro h
  exact gradedPow_add_freeProP_two_ne _ _ rfl rfl (h _ _)

end TauCeti
