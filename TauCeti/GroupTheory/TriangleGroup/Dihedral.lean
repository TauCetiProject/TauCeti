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

`equivDihedral` identifies the triangle group with signature `(2, 2, m)` with
`DihedralGroup m`, for every `m`.  The reflection generators `x` and `y` correspond to
`DihedralGroup.sr 1` and `DihedralGroup.sr 0`, respectively, and their product corresponds to
the rotation `DihedralGroup.r 1`. For `2 ≤ m` this is the dihedral row of the spherical
triangle-group classification: a finite group of order `2m`
(`TauCeti.TriangleGroup.finite_two_two`). The degenerate signatures are covered as well:
`(2, 2, 0)` is the infinite dihedral group `DihedralGroup 0`, and `(2, 2, 1)` is the group of
order two.

## References

* H. S. M. Coxeter, W. O. J. Moser, *Generators and Relations for Discrete Groups*, Springer,
  §6.4 (the group `Δ(2, 2, m)` is the dihedral group of order `2m`).
* W. Magnus, *Noneuclidean Tesselations and Their Groups*, Academic Press (1974).

These sources treat the spherical case `2 ≤ m`. The identification for `m = 0` and `m = 1` is
not taken from them: it is checked directly from the presentation, as the same map on
generators.
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

/-- The product of the two distinguished involutions has exact order `m`: its image in
`DihedralGroup m` is the rotation `r 1`, of order `m`, and `(y * x) ^ m = 1`. For `m = 0` both
sides read `0`, the product having infinite order. -/
private theorem orderOf_y_mul_x_two_two (m : ℕ) :
    orderOf (y 2 2 m * x 2 2 m) = m := by
  have hmap : orderOf (toDihedral m (y 2 2 m * x 2 2 m)) = m := by
    rw [toDihedral_y_mul_x]
    exact DihedralGroup.orderOf_r_one
  have h₁ : orderOf (toDihedral m (y 2 2 m * x 2 2 m)) ∣ orderOf (y 2 2 m * x 2 2 m) :=
    orderOf_map_dvd _ _
  rw [hmap] at h₁
  exact Nat.dvd_antisymm (orderOf_dvd_of_pow_eq_one (y_mul_x_pow 2 2 m)) h₁

/-- Multiplying `y` by the `(1 : ZMod m)`-th power of `y * x` gives `x`. For `m ≠ 1` the exponent
is `1` and this is `y * y * x = x`; for `m = 1` the exponent is `0` and `x = y`, as `y * x = 1`. -/
private theorem y_mul_y_mul_x_zpow_cast_one (m : ℕ) :
    y 2 2 m * (y 2 2 m * x 2 2 m) ^ (ZMod.cast (1 : ZMod m) : ℤ) = x 2 2 m := by
  have hyy : y 2 2 m * y 2 2 m = 1 := by simpa only [pow_two] using y_pow 2 2 m
  rcases m with - | - | m
  · simp [← mul_assoc, hyy]
  · have hyx : y 2 2 1 * x 2 2 1 = 1 := by simpa only [pow_one] using y_mul_x_pow 2 2 1
    have hxy : x 2 2 1 = y 2 2 1 := mul_left_cancel (hyx.trans hyy.symm)
    simp [Subsingleton.elim (1 : ZMod 1) 0, hxy]
  · have : Fact (1 < m + 2) := ⟨by omega⟩
    simp [ZMod.cast_eq_val, ZMod.val_one, ← mul_assoc, hyy]

/-- The isomorphism from `DihedralGroup m` to the `(2, 2, m)` triangle group. -/
private noncomputable def dihedralEquiv (m : ℕ) :
    DihedralGroup m ≃* TriangleGroup 2 2 m :=
  TauCeti.dihedralGroupMulEquiv (G := TriangleGroup 2 2 m) (n := m)
    (s := y 2 2 m) (t := x 2 2 m)
    (by simpa only [pow_two] using y_pow 2 2 m)
    (by simpa only [pow_two] using x_pow 2 2 m)
    y_ne_one_two_two x_ne_one_two_two
    (orderOf_y_mul_x_two_two m) (by
      have hset : ({y 2 2 m, x 2 2 m} : Set (TriangleGroup 2 2 m)) =
          {x 2 2 m, y 2 2 m} := by
        ext g
        simp [or_comm]
      rw [hset]
      exact closure_x_y 2 2 m)

/-- **The signature `(2, 2, m)` is the dihedral group `DihedralGroup m`**, for every `m`: the
spherical dihedral row of order `2m` when `2 ≤ m`, the infinite dihedral group when `m = 0`, and
the group of order two when `m = 1`. -/
noncomputable def equivDihedral (m : ℕ) :
    TriangleGroup 2 2 m ≃* DihedralGroup m :=
  (dihedralEquiv m).symm

/-- The inverse equivalence sends `DihedralGroup.sr 0` to the generator `y`. -/
@[simp]
theorem equivDihedral_symm_sr_zero (m : ℕ) :
    (equivDihedral m).symm (DihedralGroup.sr 0) = y 2 2 m := by
  unfold equivDihedral
  simp [dihedralEquiv, TauCeti.dihedralGroupMulEquiv_apply]

/-- The inverse equivalence sends `DihedralGroup.sr 1` to the generator `x`. -/
@[simp]
theorem equivDihedral_symm_sr_one (m : ℕ) :
    (equivDihedral m).symm (DihedralGroup.sr 1) = x 2 2 m := by
  unfold equivDihedral
  simp only [MulEquiv.symm_symm, dihedralEquiv,
    TauCeti.dihedralGroupMulEquiv_apply, TauCeti.dihedralHom_sr]
  exact y_mul_y_mul_x_zpow_cast_one m

/-- `equivDihedral` sends the generator `x` to the reflection `DihedralGroup.sr 1`. -/
@[simp]
theorem equivDihedral_x (m : ℕ) :
    equivDihedral m (x 2 2 m) = DihedralGroup.sr 1 := by
  unfold equivDihedral
  rw [← equivDihedral_symm_sr_one m]
  exact MulEquiv.symm_apply_apply (dihedralEquiv m) _

/-- `equivDihedral` sends the generator `y` to the reflection `DihedralGroup.sr 0`. -/
@[simp]
theorem equivDihedral_y (m : ℕ) :
    equivDihedral m (y 2 2 m) = DihedralGroup.sr 0 := by
  unfold equivDihedral
  rw [← equivDihedral_symm_sr_zero m]
  exact MulEquiv.symm_apply_apply (dihedralEquiv m) _

/-- `equivDihedral` sends the product `y * x` to the rotation `DihedralGroup.r 1`. -/
@[simp]
theorem equivDihedral_y_mul_x (m : ℕ) :
    equivDihedral m (y 2 2 m * x 2 2 m) = DihedralGroup.r 1 := by
  rw [map_mul, equivDihedral_y, equivDihedral_x]
  simp [DihedralGroup.sr_mul_sr]

/-- `equivDihedral` sends the generator `z` to the inverse one-step rotation. -/
@[simp]
theorem equivDihedral_z (m : ℕ) :
    equivDihedral m (z 2 2 m) = DihedralGroup.r (-1 : ZMod m) := by
  rw [z_eq, map_inv, equivDihedral_y_mul_x]
  exact DihedralGroup.inv_r (n := m) 1

/-- The inverse equivalence sends `DihedralGroup.r 1` to the product `y * x`. -/
@[simp]
theorem equivDihedral_symm_r_one (m : ℕ) :
    (equivDihedral m).symm (DihedralGroup.r 1) = y 2 2 m * x 2 2 m := by
  apply (equivDihedral m).injective
  rw [MulEquiv.apply_symm_apply, equivDihedral_y_mul_x]

/-- The dihedral triangle group has cardinality `2m`; for `m = 0` both sides are `0`, the group
being infinite. -/
@[simp]
theorem natCard_two_two (m : ℕ) :
    Nat.card (TriangleGroup 2 2 m) = 2 * m := by
  calc
    Nat.card (TriangleGroup 2 2 m) = Nat.card (DihedralGroup m) :=
      Nat.card_congr (equivDihedral m).toEquiv
    _ = 2 * m := DihedralGroup.nat_card

/-- The dihedral spherical row: a signature `(2, 2, m)` with `m ≠ 0` gives a finite triangle
group, the dihedral group of order `2m`. -/
theorem finite_two_two (m : ℕ) (hm : m ≠ 0) : Finite (TriangleGroup 2 2 m) := by
  have hcard : 0 < Nat.card (TriangleGroup 2 2 m) := by
    rw [natCard_two_two m]
    omega
  exact Nat.card_pos_iff.mp hcard |>.2

end TriangleGroup

end TauCeti
