/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Coxeter.Length
public import Mathlib.GroupTheory.SpecificGroups.Dihedral
import TauCeti.GroupTheory.Coxeter.Geometric.Basic
import TauCeti.GroupTheory.Coxeter.Length
import TauCeti.GroupTheory.SpecificGroups.Dihedral.Basic

/-!
# Rank-one and rank-two Coxeter groups

A Coxeter system on `[Unique B]` is isomorphic to `Multiplicative (ZMod 2)` via length parity
(`CoxeterSystem.uniqueEquivZModTwo`). A Coxeter system on `Fin 2` with matrix `M` is isomorphic to
`DihedralGroup (M 0 1)` (`CoxeterSystem.finTwoEquivDihedralGroup`,
`CoxeterMatrix.finTwoGroupEquivDihedralGroup`), covering both finite dihedral groups (`0 < M 0 1`)
and the infinite dihedral group `DihedralGroup 0` (`M 0 1 = 0`).
-/

public section

namespace CoxeterSystem

section Unique

variable {B W : Type*} [Unique B] [Group W] {M : CoxeterMatrix B} (cs : CoxeterSystem M W)

/-- **A rank-one Coxeter system is isomorphic to `Multiplicative (ZMod 2)` via length parity.** -/
noncomputable def uniqueEquivZModTwo : W ≃* Multiplicative (ZMod 2) :=
  MulEquiv.ofBijective cs.lengthParity ⟨(injective_iff_map_eq_one _).mpr fun w hw ↦ by
    have h2 : w = 1 ∨ w = cs.simple default :=
      cs.simple_induction_left (p := fun u ↦ u = 1 ∨ u = cs.simple default) w (Or.inl rfl)
        fun u i h ↦ by
          rw [Subsingleton.elim i default]
          exact h.symm.imp (fun h' ↦ by rw [h', cs.simple_mul_simple_self])
            (fun h' ↦ by rw [h', mul_one])
    exact h2.resolve_right fun h ↦ by
      rw [h, cs.lengthParity_simple] at hw
      exact (by decide : Multiplicative.ofAdd (1 : ZMod 2) ≠ 1) hw,
    fun x ↦ by
      have h2 : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
      rcases h2 (Multiplicative.toAdd x) with h | h
      · exact ⟨1, by rw [map_one]; exact Multiplicative.toAdd.injective h.symm⟩
      · exact ⟨cs.simple default,
          by rw [cs.lengthParity_simple]; exact Multiplicative.toAdd.injective h.symm⟩⟩

/-- `uniqueEquivZModTwo` sends the simple reflection to `Multiplicative.ofAdd 1`. -/
@[simp] theorem uniqueEquivZModTwo_simple (i : B) :
    cs.uniqueEquivZModTwo (cs.simple i) = Multiplicative.ofAdd 1 := cs.lengthParity_simple i

include cs in
/-- **A rank-one Coxeter group has cardinality `2`.** -/
theorem natCard_eq_two : Nat.card W = 2 := by
  rw [Nat.card_congr cs.uniqueEquivZModTwo.toEquiv, Nat.card_congr Multiplicative.toAdd,
    Nat.card_zmod]

end Unique

section FinTwo

variable {W : Type*} [Group W] {M : CoxeterMatrix (Fin 2)} (cs : CoxeterSystem M W)

/-- **Any Coxeter system on `Fin 2` is isomorphic to `DihedralGroup (M 0 1)`.**
When `M 0 1 = 0`, `DihedralGroup 0` is the infinite dihedral group. -/
noncomputable def finTwoEquivDihedralGroup : W ≃* DihedralGroup (M 0 1) :=
  (TauCeti.dihedralGroupMulEquiv (cs.simple_mul_simple_self 0) (cs.simple_mul_simple_self 1)
    (cs.simple_ne_one 0) (cs.simple_ne_one 1) (cs.orderOf_simple_mul_simple 0 1) <| by
      have hrange : Set.range cs.simple = {cs.simple 0, cs.simple 1} := by
        ext x; simp [Fin.exists_fin_two, eq_comm]
      rw [← hrange, cs.subgroupClosure_range_simple]).symm

@[simp] theorem finTwoEquivDihedralGroup_simple_zero :
    cs.finTwoEquivDihedralGroup (cs.simple 0) = DihedralGroup.sr 0 := by
  rw [finTwoEquivDihedralGroup, MulEquiv.symm_apply_eq, TauCeti.dihedralGroupMulEquiv_apply,
    TauCeti.dihedralHom_sr, ZMod.cast_zero, zpow_zero, mul_one]
@[simp] theorem finTwoEquivDihedralGroup_simple_one :
    cs.finTwoEquivDihedralGroup (cs.simple 1) = DihedralGroup.sr 1 := by
  rw [finTwoEquivDihedralGroup, MulEquiv.symm_apply_eq, TauCeti.dihedralGroupMulEquiv_apply,
    TauCeti.dihedralHom_sr]
  have hone : (cs.simple 0 * cs.simple 1) ^ (ZMod.cast (1 : ZMod (M 0 1)) : ℤ) =
      cs.simple 0 * cs.simple 1 := by
    conv_rhs => rw [← zpow_one (cs.simple 0 * cs.simple 1)]
    rw [zpow_eq_zpow_iff_modEq, cs.orderOf_simple_mul_simple 0 1,
      ← ZMod.intCast_eq_intCast_iff, ZMod.intCast_zmod_cast, Int.cast_one]
  rw [hone, ← mul_assoc, cs.simple_mul_simple_self, one_mul]

include cs in
/-- **A rank-two Coxeter group on `Fin 2` has cardinality `2 * M 0 1`.**
In the infinite dihedral case `M 0 1 = 0`, `Nat.card W` is `0` (as for any infinite type). -/
theorem natCard_eq_two_mul : Nat.card W = 2 * M 0 1 := by
  rw [Nat.card_congr cs.finTwoEquivDihedralGroup.toEquiv, DihedralGroup.nat_card]

end FinTwo

end CoxeterSystem

namespace CoxeterMatrix

/-- **A rank-two presented Coxeter group `M.Group` is isomorphic to `DihedralGroup (M 0 1)`.**
When `M 0 1 = 0`, `DihedralGroup 0` is the infinite dihedral group. -/
noncomputable def finTwoGroupEquivDihedralGroup (M : CoxeterMatrix (Fin 2)) :
    M.Group ≃* DihedralGroup (M 0 1) := M.toCoxeterSystem.finTwoEquivDihedralGroup
@[simp] theorem finTwoGroupEquivDihedralGroup_simple_zero (M : CoxeterMatrix (Fin 2)) :
    M.finTwoGroupEquivDihedralGroup (M.simple 0) = DihedralGroup.sr 0 :=
  M.toCoxeterSystem.finTwoEquivDihedralGroup_simple_zero
@[simp] theorem finTwoGroupEquivDihedralGroup_simple_one (M : CoxeterMatrix (Fin 2)) :
    M.finTwoGroupEquivDihedralGroup (M.simple 1) = DihedralGroup.sr 1 :=
  M.toCoxeterSystem.finTwoEquivDihedralGroup_simple_one

end CoxeterMatrix
