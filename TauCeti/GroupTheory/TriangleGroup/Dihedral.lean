/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.TriangleGroup.Basic
public import TauCeti.GroupTheory.SpecificGroups.Dihedral.Basic

/-!
# Dihedral spherical triangle groups

For `m` with `2 ≤ m`, `equivDihedral` identifies the spherical triangle group with
signature `(2, 2, m)` with `DihedralGroup m`.  The reflection generators `x` and `y`
correspond to `DihedralGroup.sr 1` and `DihedralGroup.sr 0`, respectively, and their product
corresponds to the rotation `DihedralGroup.r 1`.
-/

public section

noncomputable section

namespace TauCeti

namespace TriangleGroup

/-- The map from the `(2, 2, m)` presentation to `DihedralGroup m` used to establish the
order of the product of the two reflection generators. -/
private def toDihedral (m : ℕ) : TriangleGroup 2 2 m →* DihedralGroup m :=
  lift (DihedralGroup.sr 1) (DihedralGroup.sr 0) (DihedralGroup.r (-1 : ZMod m))
    (by rw [pow_two, DihedralGroup.sr_mul_self])
    (by rw [pow_two, DihedralGroup.sr_mul_self])
    (by
      have h : DihedralGroup.r (-1 : ZMod m) = (DihedralGroup.r 1)⁻¹ :=
        (DihedralGroup.inv_r 1).symm
      rw [h, inv_pow, DihedralGroup.r_one_pow_n, inv_one])
    (by
      rw [mul_assoc, DihedralGroup.sr_mul_sr]
      rw [DihedralGroup.r_mul_r]
      have hz : (-1 : ZMod m) + (1 - 0) = 0 := by
        simpa only [sub_eq_add_neg, neg_zero, add_zero] using
          (neg_add_cancel (1 : ZMod m))
      rw [hz, DihedralGroup.r_zero])

@[simp]
private theorem toDihedral_x (m : ℕ) :
    toDihedral m (x 2 2 m) = DihedralGroup.sr 1 := by
  simp [toDihedral]

@[simp]
private theorem toDihedral_y (m : ℕ) :
    toDihedral m (y 2 2 m) = DihedralGroup.sr 0 := by
  simp [toDihedral]

@[simp]
private theorem toDihedral_z (m : ℕ) :
    toDihedral m (z 2 2 m) = DihedralGroup.r (-1 : ZMod m) := by
  simp [toDihedral]

private theorem toDihedral_y_mul_x (m : ℕ) :
    toDihedral m (y 2 2 m * x 2 2 m) = DihedralGroup.r 1 := by
  simp [toDihedral, DihedralGroup.sr_mul_sr]

/-- The two distinguished involutions are nonidentity. -/
private theorem x_ne_one_two_two : x 2 2 m ≠ 1 := by
  intro h
  apply dihedralSr_ne_one
  simpa only [toDihedral_x, map_one] using congrArg (toDihedral m) h

private theorem y_ne_one_two_two : y 2 2 m ≠ 1 := by
  intro h
  apply dihedralSr_ne_one
  simpa only [toDihedral_y, map_one] using congrArg (toDihedral m) h

/-- The product of the two distinguished involutions has exact order `m`. -/
private theorem orderOf_y_mul_x_two_two (m : ℕ) (hm : 2 ≤ m) :
    orderOf (y 2 2 m * x 2 2 m) = m := by
  have hm0 : 0 < m := lt_of_lt_of_le (by decide) hm
  have hmap : orderOf (toDihedral m (y 2 2 m * x 2 2 m)) = m := by
    rw [toDihedral_y_mul_x]
    exact DihedralGroup.orderOf_r_one
  have h₁ : orderOf (toDihedral m (y 2 2 m * x 2 2 m)) ∣
      orderOf (y 2 2 m * x 2 2 m) :=
    orderOf_map_dvd _ _
  have h₂ : orderOf (y 2 2 m * x 2 2 m) ∣ m :=
    orderOf_dvd_of_pow_eq_one (y_mul_x_pow 2 2 m)
  have h₁' := h₁
  rw [hmap] at h₁'
  apply Nat.le_antisymm
  · exact Nat.le_of_dvd hm0 h₂
  · exact Nat.le_of_dvd (Nat.pos_of_dvd_of_pos h₂ hm0) h₁'

private theorem cast_one_of_two_le (m : ℕ) (hm : 2 ≤ m) :
    (ZMod.cast (1 : ZMod m) : ℤ) = 1 := by
  have hnz : NeZero m := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hm)⟩
  have hf : Fact (1 < m) := ⟨lt_of_lt_of_le (by decide) hm⟩
  have hv := @ZMod.cast_eq_val m ℤ (inferInstance) hnz (1 : ZMod m)
  have hw := @ZMod.val_one m hf
  rw [hv, hw]
  rfl

/-- The isomorphism from `DihedralGroup m` to the `(2, 2, m)` triangle group. -/
private noncomputable def dihedralEquiv (m : ℕ) (hm : 2 ≤ m) :
    DihedralGroup m ≃* TriangleGroup 2 2 m :=
  TauCeti.dihedralGroupMulEquiv (G := TriangleGroup 2 2 m) (n := m)
    (s := y 2 2 m) (t := x 2 2 m)
    (by simpa only [pow_two] using y_pow 2 2 m)
    (by simpa only [pow_two] using x_pow 2 2 m)
    y_ne_one_two_two x_ne_one_two_two
    (orderOf_y_mul_x_two_two m hm) (by
      have hset : ({y 2 2 m, x 2 2 m} : Set (TriangleGroup 2 2 m)) =
          {x 2 2 m, y 2 2 m} := by
        ext g
        simp [or_comm]
      rw [hset]
      exact closure_x_y 2 2 m)

/-- The spherical signature `(2, 2, m)` is the dihedral group of order `2m`. -/
noncomputable def equivDihedral (m : ℕ) (hm : 2 ≤ m) :
    TriangleGroup 2 2 m ≃* DihedralGroup m :=
  (dihedralEquiv m hm).symm

/-- The inverse equivalence sends `DihedralGroup.sr 0` to the generator `y`. -/
@[simp]
theorem equivDihedral_symm_sr_zero (m : ℕ) (hm : 2 ≤ m) :
    (equivDihedral m hm).symm (DihedralGroup.sr 0) = y 2 2 m := by
  unfold equivDihedral
  simp [dihedralEquiv, TauCeti.dihedralGroupMulEquiv_apply]

/-- The inverse equivalence sends `DihedralGroup.sr 1` to the generator `x`. -/
@[simp]
theorem equivDihedral_symm_sr_one (m : ℕ) (hm : 2 ≤ m) :
    (equivDihedral m hm).symm (DihedralGroup.sr 1) = x 2 2 m := by
  unfold equivDihedral
  simp only [MulEquiv.symm_symm, dihedralEquiv,
    TauCeti.dihedralGroupMulEquiv_apply, TauCeti.dihedralHom_sr]
  rw [cast_one_of_two_le m hm]
  simp only [zpow_one]
  calc
    y 2 2 m * (y 2 2 m * x 2 2 m) = (y 2 2 m * y 2 2 m) * x 2 2 m := by ac_rfl
    _ = x 2 2 m := by
      rw [← pow_two, y_pow 2 2 m, one_mul]

/-- `equivDihedral` sends the generator `x` to the reflection `DihedralGroup.sr 1`. -/
@[simp]
theorem equivDihedral_x (m : ℕ) (hm : 2 ≤ m) :
    equivDihedral m hm (x 2 2 m) = DihedralGroup.sr 1 := by
  unfold equivDihedral
  rw [← equivDihedral_symm_sr_one m hm]
  exact MulEquiv.symm_apply_apply (dihedralEquiv m hm) _

/-- `equivDihedral` sends the generator `y` to the reflection `DihedralGroup.sr 0`. -/
@[simp]
theorem equivDihedral_y (m : ℕ) (hm : 2 ≤ m) :
    equivDihedral m hm (y 2 2 m) = DihedralGroup.sr 0 := by
  unfold equivDihedral
  rw [← equivDihedral_symm_sr_zero m hm]
  exact MulEquiv.symm_apply_apply (dihedralEquiv m hm) _

/-- `equivDihedral` sends the product `y * x` to the rotation `DihedralGroup.r 1`. -/
@[simp]
theorem equivDihedral_y_mul_x (m : ℕ) (hm : 2 ≤ m) :
    equivDihedral m hm (y 2 2 m * x 2 2 m) = DihedralGroup.r 1 := by
  rw [map_mul, equivDihedral_y, equivDihedral_x]
  simp [DihedralGroup.sr_mul_sr]

/-- `equivDihedral` sends the generator `z` to the inverse one-step rotation. -/
@[simp]
theorem equivDihedral_z (m : ℕ) (hm : 2 ≤ m) :
    equivDihedral m hm (z 2 2 m) = DihedralGroup.r (-1 : ZMod m) := by
  rw [z_eq, map_inv, equivDihedral_y_mul_x]
  exact DihedralGroup.inv_r (n := m) 1

/-- The inverse equivalence sends `DihedralGroup.r 1` to the product `y * x`. -/
@[simp]
theorem equivDihedral_symm_r_one (m : ℕ) (hm : 2 ≤ m) :
    (equivDihedral m hm).symm (DihedralGroup.r 1) = y 2 2 m * x 2 2 m := by
  apply (equivDihedral m hm).injective
  rw [MulEquiv.apply_symm_apply, equivDihedral_y_mul_x]

/-- The dihedral triangle group has cardinality `2m`. -/
@[simp]
theorem natCard_two_two (m : ℕ) (hm : 2 ≤ m) :
    Nat.card (TriangleGroup 2 2 m) = 2 * m := by
  calc
    Nat.card (TriangleGroup 2 2 m) = Nat.card (DihedralGroup m) :=
      Nat.card_congr (equivDihedral m hm).toEquiv
    _ = 2 * m := DihedralGroup.nat_card

end TriangleGroup

end TauCeti
