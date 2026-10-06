/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.GroupWithZero.Units.Fintype
public import Mathlib.Algebra.Ring.Int.Units
public import Mathlib.LinearAlgebra.Determinant
public import TauCeti.LinearAlgebra.IntegralLattice.Isometry.Basic

/-!
# The isometry group of an integral lattice

The self-isometries of an integral lattice `L` form a group `O(L) = Isometry L L` under
composition, with `f * g` the isometry `g` followed by `f`, as for `LinearEquiv.automorphismGroup`.
Restricting a self-isometry to the carrier is a group homomorphism into the automorphism group of
the carrier, and composing with the determinant gives the **determinant** of a self-isometry, a
unit of `ℤ`, hence `±1`. Its kernel is the **special isometry group** `SO(L)`, a subgroup of
index at most two. Negation is a self-isometry of every lattice, the element `-1` of `O(L)`, and
its determinant is `(-1) ^ rank L`; so `SO(L)` is a proper subgroup in odd rank.

## Main definitions

* The `Group` instance on `Isometry L L`: composition, identity and inversion of self-isometries.
* `TauCeti.IntegralLattice.Isometry.carrierEquivHom`: restriction to the carrier as a group
  homomorphism `O(L) →* (L ≃ₗ[ℤ] L)`.
* `TauCeti.IntegralLattice.Isometry.det`: the determinant `O(L) →* ℤˣ`.
* `TauCeti.IntegralLattice.specialOrthogonalGroup`: the subgroup `SO(L)` of determinant one.
* `TauCeti.IntegralLattice.Isometry.neg`: negation, the element `-1` of `O(L)`.

## Main results

* `TauCeti.IntegralLattice.Isometry.carrierEquivHom_injective`: a self-isometry is determined by
  its restriction to the carrier.
* `TauCeti.IntegralLattice.index_specialOrthogonalGroup_le_two`: `SO(L)` has index at most two.
* `TauCeti.IntegralLattice.Isometry.det_neg`: the determinant of negation is `(-1) ^ rank L`.

## References

* W. Ebeling, *Lattices and Codes*, Chapter 1
* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, Chapter 3, §4
-/

public section

namespace TauCeti

namespace IntegralLattice

variable {V : Type*} [AddCommGroup V] [Module ℚ V] {L : IntegralLattice V}

namespace Isometry

/-- The self-isometries of an integral lattice form a group under composition: `f * g` is `g`
followed by `f`, the identity is `refl` and the inverse is `symm`, as for
`LinearEquiv.automorphismGroup`. -/
instance : Group (Isometry L L) where
  mul f g := g.trans f
  one := refl L
  inv f := f.symm
  mul_assoc a b c := (trans_assoc c b a).symm
  one_mul f := trans_refl f
  mul_one f := refl_trans f
  inv_mul_cancel f := self_trans_symm f

theorem one_def : (1 : Isometry L L) = refl L := (rfl)

theorem mul_def (f g : Isometry L L) : f * g = g.trans f := (rfl)

theorem inv_def (f : Isometry L L) : f⁻¹ = f.symm := (rfl)

@[simp]
theorem one_apply (x : V) : (1 : Isometry L L) x = x := refl_apply L x

@[simp]
theorem mul_apply (f g : Isometry L L) (x : V) : (f * g) x = f (g x) := trans_apply g f x

@[simp]
theorem inv_apply (f : Isometry L L) (x : V) : f⁻¹ x = f.symm x := (rfl)

/-- Restriction of a self-isometry to the carrier, as a group homomorphism from `O(L)` to the
automorphism group of the carrier. -/
def carrierEquivHom (L : IntegralLattice V) : Isometry L L →* (L ≃ₗ[ℤ] L) where
  toFun e := e.carrierEquiv
  map_one' := carrierEquiv_refl L
  map_mul' f g := by rw [mul_def, carrierEquiv_trans, LinearEquiv.mul_eq_trans]

@[simp]
theorem carrierEquivHom_apply (e : Isometry L L) : carrierEquivHom L e = e.carrierEquiv := (rfl)

/-- A self-isometry is determined by its restriction to the carrier. -/
theorem carrierEquivHom_injective (L : IntegralLattice V) :
    Function.Injective (carrierEquivHom L) :=
  carrierEquiv_injective

/-- The determinant of a self-isometry of an integral lattice: the determinant of its restriction
to the carrier, a unit of `ℤ`. -/
noncomputable def det (L : IntegralLattice V) : Isometry L L →* ℤˣ :=
  LinearEquiv.det.comp (carrierEquivHom L)

theorem det_apply (e : Isometry L L) : det L e = LinearEquiv.det e.carrierEquiv := (rfl)

@[simp]
theorem coe_det (e : Isometry L L) :
    (det L e : ℤ) = LinearMap.det (e.carrierEquiv : L →ₗ[ℤ] L) :=
  LinearEquiv.coe_det e.carrierEquiv

/-- The determinant of a self-isometry is `1` or `-1`. -/
theorem det_eq_one_or_neg_one (e : Isometry L L) : det L e = 1 ∨ det L e = -1 :=
  Int.units_eq_one_or (det L e)

/-- Negation is a self-isometry of every integral lattice: the element `-1` of `O(L)`. -/
def neg (L : IntegralLattice V) : Isometry L L where
  toIsometryEquiv :=
    { toLinearEquiv := LinearEquiv.neg ℚ
      map_app' x y := by simp }
  map_carrier := by
    have h : ((LinearEquiv.neg ℚ : V ≃ₗ[ℚ] V).restrictScalars ℤ).toLinearMap =
        -(LinearMap.id : V →ₗ[ℤ] V) := by
      ext x
      simp
    rw [h, Submodule.map_neg, Submodule.map_id]

@[simp]
theorem neg_apply (L : IntegralLattice V) (x : V) : neg L x = -x := (rfl)

/-- Negation restricts to negation of the carrier. -/
@[simp]
theorem carrierEquiv_neg (L : IntegralLattice V) : (neg L).carrierEquiv = LinearEquiv.neg ℤ := by
  ext x
  simp

/-- Negation is an involution of `O(L)`. -/
@[simp]
theorem neg_mul_neg (L : IntegralLattice V) : neg L * neg L = 1 := by
  ext x
  simp

/-- The determinant of negation is `(-1) ^ rank L`. -/
@[simp]
theorem det_neg (L : IntegralLattice V) : det L (neg L) = (-1) ^ Module.finrank ℤ L := by
  apply Units.ext
  rw [coe_det, carrierEquiv_neg, Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one]
  have h : ((LinearEquiv.neg ℤ : L ≃ₗ[ℤ] L) : L →ₗ[ℤ] L) = (-1 : ℤ) • LinearMap.id := by
    ext x
    simp
  rw [h, LinearMap.det_smul, LinearMap.det_id, mul_one]

end Isometry

/-- The special isometry group `SO(L)`: the subgroup of the isometry group `O(L) = Isometry L L`
of self-isometries of determinant one. -/
noncomputable def specialOrthogonalGroup (L : IntegralLattice V) : Subgroup (Isometry L L) :=
  (Isometry.det L).ker

@[simp]
theorem mem_specialOrthogonalGroup_iff {e : Isometry L L} :
    e ∈ specialOrthogonalGroup L ↔ Isometry.det L e = 1 :=
  MonoidHom.mem_ker

/-- `SO(L)` has index at most two in `O(L)`, the determinant taking values in `ℤˣ = {±1}`. -/
theorem index_specialOrthogonalGroup_le_two (L : IntegralLattice V) :
    (specialOrthogonalGroup L).index ≤ 2 := by
  rw [specialOrthogonalGroup, Subgroup.index_ker]
  calc Nat.card (Isometry.det L).range ≤ Nat.card ℤˣ := Nat.card_le_card_of_injective _
        Subtype.val_injective
    _ = 2 := Nat.card_eq_fintype_card.trans Fintype.card_units_int

/-- Negation lies in `SO(L)` exactly when the rank of `L` is even. -/
theorem neg_mem_specialOrthogonalGroup_iff (L : IntegralLattice V) :
    Isometry.neg L ∈ specialOrthogonalGroup L ↔ Even (Module.finrank ℤ L) := by
  rw [mem_specialOrthogonalGroup_iff, Isometry.det_neg, neg_one_pow_eq_one_iff_even]
  exact fun h ↦ by simpa using congrArg Units.val h

end IntegralLattice

end TauCeti
