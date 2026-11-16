/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Coxeter.Length
public import Mathlib.GroupTheory.SpecificGroups.Dihedral

/-!
# Rank-one and rank-two Coxeter groups

A Coxeter system on `[Unique B]` is isomorphic to `Multiplicative (ZMod 2)` via length parity
(`CoxeterSystem.uniqueEquivZModTwo`). A Coxeter system on `Fin 2` with matrix `M` is isomorphic to
`DihedralGroup (M 0 1)` (`CoxeterMatrix.finTwoGroupEquivDihedralGroup`,
`CoxeterSystem.finTwoEquivDihedralGroup`), covering both finite dihedral groups (`0 < M 0 1`) and
the infinite dihedral group `DihedralGroup 0` (`M 0 1 = 0`).
-/

public section

namespace CoxeterMatrix

private def finTwoSrFun (n : ℕ) (i : Fin 2) : DihedralGroup n :=
  if i = 0 then .sr 0 else .sr 1

private theorem isLiftable_finTwoSrFun (M : CoxeterMatrix (Fin 2)) :
    M.IsLiftable (finTwoSrFun (M 0 1)) := by
  have h10 : (1 : Fin 2) ≠ 0 := by decide
  refine Fin.forall_fin_two.mpr ⟨Fin.forall_fin_two.mpr ⟨by simp [finTwoSrFun],
    by simp [finTwoSrFun, h10]⟩, Fin.forall_fin_two.mpr ⟨?_, by simp [finTwoSrFun]⟩⟩
  rw [M.symmetric 1 0]
  have hinv : finTwoSrFun (M 0 1) 1 * finTwoSrFun (M 0 1) 0 = (DihedralGroup.r 1)⁻¹ := by
    simp [finTwoSrFun, h10]
  rw [hinv, inv_pow, DihedralGroup.r_one_pow_n, inv_one]

private def finTwoToDihedralGroup (M : CoxeterMatrix (Fin 2)) :
    M.Group →* DihedralGroup (M 0 1) :=
  M.toCoxeterSystem.lift ⟨finTwoSrFun (M 0 1), isLiftable_finTwoSrFun M⟩

private theorem exists_zpow_or_mul_zpow {W : Type*} [Group W] {M : CoxeterMatrix (Fin 2)}
    (cs : CoxeterSystem M W) (w : W) :
    ∃ z : ℤ, w = (cs.simple 0 * cs.simple 1) ^ z ∨
      w = cs.simple 0 * (cs.simple 0 * cs.simple 1) ^ z := by
  induction w using cs.simple_induction_left with
  | one => exact ⟨0, Or.inl (by simp)⟩
  | mul_simple_left w i ih =>
    rcases ih with ⟨z, rfl | rfl⟩ <;> rcases Fin.exists_fin_two.mp ⟨i, rfl⟩ with rfl | rfl
    · exact ⟨z, Or.inr rfl⟩
    · refine ⟨1 + z, Or.inr ?_⟩
      rw [zpow_add, zpow_one, ← mul_assoc, cs.simple_mul_simple_cancel_left]
    · exact ⟨z, Or.inl (cs.simple_mul_simple_cancel_left 0)⟩
    · refine ⟨-1 + z, Or.inl ?_⟩
      have hinv : (cs.simple 0 * cs.simple 1)⁻¹ = cs.simple 1 * cs.simple 0 := by
        rw [mul_inv_rev, cs.inv_simple, cs.inv_simple]
      rw [zpow_add, zpow_neg_one, hinv, mul_assoc]

private theorem finTwoToDihedralGroup_bijective (M : CoxeterMatrix (Fin 2)) :
    Function.Bijective M.finTwoToDihedralGroup := by
  let cs := M.toCoxeterSystem
  have hs0 : M.finTwoToDihedralGroup (cs.simple 0) = .sr 0 := cs.lift_apply_simple _ 0
  have hs1 : M.finTwoToDihedralGroup (cs.simple 1) = .sr 1 := cs.lift_apply_simple _ 1
  have hrot (z : ℤ) : M.finTwoToDihedralGroup ((cs.simple 0 * cs.simple 1) ^ z) = .r z := by
    simp [map_zpow, hs0, hs1]
  refine ⟨(injective_iff_map_eq_one _).mpr fun w hw ↦ ?_, fun x ↦ ?_⟩
  · obtain ⟨z, rfl | rfl⟩ := exists_zpow_or_mul_zpow cs w
    · have hz0 : (z : ZMod (M 0 1)) = 0 :=
        DihedralGroup.r.inj ((hrot z).symm.trans (hw.trans DihedralGroup.one_def))
      obtain ⟨q, rfl⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd z (M 0 1)).mp hz0
      rw [zpow_mul, zpow_natCast, cs.simple_mul_simple_pow, one_zpow]
    · rw [map_mul, hs0, hrot, DihedralGroup.sr_mul_r, zero_add] at hw
      cases hw
  · rcases x with i | i <;> obtain ⟨z, rfl⟩ := ZMod.intCast_surjective i
    · exact ⟨(cs.simple 0 * cs.simple 1) ^ z, hrot z⟩
    · exact ⟨cs.simple 0 * (cs.simple 0 * cs.simple 1) ^ z, by simp [hs0, hrot]⟩

/-- **A rank-two presented Coxeter group `M.Group` is isomorphic to `DihedralGroup (M 0 1)`.**
When `M 0 1 = 0`, `DihedralGroup 0` is the infinite dihedral group. -/
noncomputable def finTwoGroupEquivDihedralGroup (M : CoxeterMatrix (Fin 2)) :
    M.Group ≃* DihedralGroup (M 0 1) :=
  MulEquiv.ofBijective M.finTwoToDihedralGroup (finTwoToDihedralGroup_bijective M)

@[simp]
theorem finTwoGroupEquivDihedralGroup_simple_zero (M : CoxeterMatrix (Fin 2)) :
    M.finTwoGroupEquivDihedralGroup (M.simple 0) = DihedralGroup.sr 0 :=
  M.toCoxeterSystem.lift_apply_simple _ 0

@[simp]
theorem finTwoGroupEquivDihedralGroup_simple_one (M : CoxeterMatrix (Fin 2)) :
    M.finTwoGroupEquivDihedralGroup (M.simple 1) = DihedralGroup.sr 1 :=
  M.toCoxeterSystem.lift_apply_simple _ 1

end CoxeterMatrix

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

include cs in
theorem natCard_of_unique : Nat.card W = 2 := by
  rw [Nat.card_congr cs.uniqueEquivZModTwo.toEquiv, Nat.card_congr Multiplicative.toAdd,
    Nat.card_zmod]

end Unique

section FinTwo

variable {W : Type*} [Group W] {M : CoxeterMatrix (Fin 2)} (cs : CoxeterSystem M W)

/-- **Any Coxeter system on `Fin 2` is isomorphic to `DihedralGroup (M 0 1)`.** -/
noncomputable def finTwoEquivDihedralGroup : W ≃* DihedralGroup (M 0 1) :=
  cs.mulEquiv.trans M.finTwoGroupEquivDihedralGroup

@[simp]
theorem finTwoEquivDihedralGroup_simple_zero :
    cs.finTwoEquivDihedralGroup (cs.simple 0) = DihedralGroup.sr 0 := by
  simp [finTwoEquivDihedralGroup]

@[simp]
theorem finTwoEquivDihedralGroup_simple_one :
    cs.finTwoEquivDihedralGroup (cs.simple 1) = DihedralGroup.sr 1 := by
  simp [finTwoEquivDihedralGroup]

include cs in
theorem natCard_of_fin_two : Nat.card W = 2 * M 0 1 := by
  rw [Nat.card_congr cs.finTwoEquivDihedralGroup.toEquiv, DihedralGroup.nat_card]

end FinTwo

end CoxeterSystem
