/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.E7.Minuscule.Frobenius
public import TauCeti.FieldTheory.Finite.SepClosedSubfield

/-!
# Frobenius-fixed points of the full-weight type-E7 minuscule carrier

The full-weight type-`E₇` minuscule carrier is an explicit integral subgroup scheme of
`GL₅₆`, and `TauCeti.E7Minuscule.frobenius p k A` acts on its points by raising every matrix
entry to its `p ^ k`-th power. This file identifies its fixed subgroup with the carrier's points
over the Frobenius-fixed subring:

```text
G(A^(F = 1)) ≃* G(A)^F.
```

The equivalence is the functorial point map along the inclusion of the fixed subring into `A`.
Both directions are described on matrices and entrywise. Consequently, the fixed subgroup is
finite whenever the fixed subring is finite; in particular it is finite over a field of
characteristic `p` for every nonzero Frobenius exponent.

This is an identification for the explicit minuscule carrier. It does not assert that the carrier
is the simply connected reductive group of type `E₇`, nor does it assert perfectness or simplicity
of the fixed group.

## Main declarations

* `TauCeti.E7Minuscule.pointsMulEquivFixedSubgroupFrobenius`: the multiplicative equivalence from
  points over the fixed subring to Frobenius-fixed points.
* `TauCeti.E7Minuscule.coe_pointsMulEquivFixedSubgroupFrobenius_eq_pointsMap`: the equivalence is
  the point map induced by the inclusion of the fixed subring.
* `TauCeti.E7Minuscule.finite_fixedSubgroup_frobenius_of_charP`: Frobenius-fixed points over a
  field of characteristic `p` are finite for a nonzero exponent.

## References

* R. W. Carter, *Finite Groups of Lie Type: Conjugacy Classes and Complex Characters*, §1.17.
* J. C. Jantzen, *Representations of Algebraic Groups*, II.1.

The construction specializes
`TauCeti.GeneralLinear.frobeniusFixedMulEquivOfCoeEq`, which gives the same equivalence for any
matrix carrier presented by a Hopf ideal and an entrywise Frobenius. Its statement shapes follow
`TauCeti.Algebra.Lie.Symplectic.StandardCarrier.FixedPoints` and
`TauCeti.Algebra.Lie.Orthogonal.TypeD.SpinCarrier.FixedPoints`.
-/

public section

namespace TauCeti.E7Minuscule

universe v

noncomputable section

variable (p k : ℕ)
variable (A : Type v) [CommRing A] [ExpChar A p]

/-! ## The fixed points as points over the fixed subring -/

/-- **The Frobenius-fixed points of the full-weight type-`E₇` minuscule carrier are its points
over the Frobenius-fixed subring.** For `p` prime, `0 < k`, and `A` an algebraic closure of
`ZMod p`, this is the group isomorphism `G(𝔽_(p^k)) ≃* G(A)^F` for the explicit carrier. -/
def pointsMulEquivFixedSubgroupFrobenius :
    points ↥(frobeniusFixedSubring A p k) ≃*
      ↥(fixedSubgroup (frobenius p k A)) :=
  GeneralLinear.frobeniusFixedMulEquivOfCoeEq 56 p k definingIdeal A
    (frobenius p k A) (points_def A) (points_def ↥(frobeniusFixedSubring A p k))
    (coe_frobenius p k A)

/-- The fixed-point equivalence includes the matrix entries of a carrier point over the
Frobenius-fixed subring into the value ring. -/
theorem coe_pointsMulEquivFixedSubgroupFrobenius
    (g : points ↥(frobeniusFixedSubring A p k)) :
    ((pointsMulEquivFixedSubgroupFrobenius p k A g : points A) :
        Matrix.GeneralLinearGroup (Fin 56) A) =
      Matrix.GeneralLinearGroup.map (frobeniusFixedSubring A p k).subtype g :=
  GeneralLinear.coe_frobeniusFixedMulEquivOfCoeEq 56 p k definingIdeal A
    (frobenius p k A) (points_def A) (points_def ↥(frobeniusFixedSubring A p k))
    (coe_frobenius p k A) g

/-- Entrywise, the fixed-point equivalence applies the inclusion of the Frobenius-fixed subring. -/
theorem coe_pointsMulEquivFixedSubgroupFrobenius_apply
    (g : points ↥(frobeniusFixedSubring A p k)) (i j : Fin 56) :
    ((((pointsMulEquivFixedSubgroupFrobenius p k A g : points A) :
          Matrix.GeneralLinearGroup (Fin 56) A) :
        Matrix (Fin 56) (Fin 56) A) i j) =
      ((((g : Matrix.GeneralLinearGroup (Fin 56) ↥(frobeniusFixedSubring A p k)) :
          Matrix (Fin 56) (Fin 56) ↥(frobeniusFixedSubring A p k)) i j :
        ↥(frobeniusFixedSubring A p k)) : A) := by
  rw [coe_pointsMulEquivFixedSubgroupFrobenius, Matrix.GeneralLinearGroup.map_apply,
    Subring.coe_subtype]

/-- The fixed-point equivalence is the functorial carrier-point map along the inclusion of the
Frobenius-fixed subring. -/
@[simp]
theorem coe_pointsMulEquivFixedSubgroupFrobenius_eq_pointsMap
    (g : points ↥(frobeniusFixedSubring A p k)) :
    (pointsMulEquivFixedSubgroupFrobenius p k A g : points A) =
      pointsMap (frobeniusFixedSubring A p k).subtype g :=
  Subtype.ext (by rw [coe_pointsMulEquivFixedSubgroupFrobenius, coe_pointsMap])

/-- Including the matrix underlying the inverse image of a Frobenius-fixed point returns the
original matrix. -/
@[simp]
theorem coe_pointsMulEquivFixedSubgroupFrobenius_symm_apply
    (x : ↥(fixedSubgroup (frobenius p k A))) :
    Matrix.GeneralLinearGroup.map (frobeniusFixedSubring A p k).subtype
        ((pointsMulEquivFixedSubgroupFrobenius p k A).symm x) =
      ((x : points A) : Matrix.GeneralLinearGroup (Fin 56) A) :=
  GeneralLinear.coe_frobeniusFixedMulEquivOfCoeEq_symm_apply 56 p k definingIdeal A
    (frobenius p k A) (points_def A) (points_def ↥(frobeniusFixedSubring A p k))
    (coe_frobenius p k A) x

/-- Entrywise, the inverse equivalence reads a Frobenius-fixed matrix over the fixed subring
without changing its entries. -/
@[simp]
theorem coe_pointsMulEquivFixedSubgroupFrobenius_symm_apply_apply
    (x : ↥(fixedSubgroup (frobenius p k A))) (i j : Fin 56) :
    (((((pointsMulEquivFixedSubgroupFrobenius p k A).symm x :
            Matrix.GeneralLinearGroup (Fin 56) ↥(frobeniusFixedSubring A p k)) :
          Matrix (Fin 56) (Fin 56) ↥(frobeniusFixedSubring A p k)) i j :
        ↥(frobeniusFixedSubring A p k)) : A) =
      ((((x : points A) : Matrix.GeneralLinearGroup (Fin 56) A) :
        Matrix (Fin 56) (Fin 56) A) i j) := by
  rw [← coe_pointsMulEquivFixedSubgroupFrobenius_symm_apply,
    Matrix.GeneralLinearGroup.map_apply, Subring.coe_subtype]

/-- Mapping the inverse image of a Frobenius-fixed point back along the fixed-subring inclusion
returns the carrier point one started from. -/
@[simp]
theorem pointsMap_pointsMulEquivFixedSubgroupFrobenius_symm_apply
    (x : ↥(fixedSubgroup (frobenius p k A))) :
    pointsMap (frobeniusFixedSubring A p k).subtype
        ((pointsMulEquivFixedSubgroupFrobenius p k A).symm x) = (x : points A) := by
  rw [← coe_pointsMulEquivFixedSubgroupFrobenius_eq_pointsMap, MulEquiv.apply_symm_apply]

/-! ## Finiteness -/

/-- The Frobenius-fixed points of the full-weight type-`E₇` minuscule carrier form a finite group
whenever the Frobenius-fixed subring is finite. -/
theorem finite_fixedSubgroup_frobenius [Finite ↥(frobeniusFixedSubring A p k)] :
    Finite ↥(fixedSubgroup (frobenius p k A)) :=
  .of_equiv _ (pointsMulEquivFixedSubgroupFrobenius p k A).toEquiv

/-- The Frobenius-fixed points of the full-weight type-`E₇` minuscule carrier over a field of
characteristic `p` form a finite group for every nonzero Frobenius exponent. -/
theorem finite_fixedSubgroup_frobenius_of_charP (K : Type v) [Field K]
    [Fact p.Prime] [CharP K p] (hk : k ≠ 0) :
    Finite ↥(fixedSubgroup (frobenius p k K)) :=
  have := finite_frobeniusFixedSubring K p k hk
  finite_fixedSubgroup_frobenius p k K

end

end TauCeti.E7Minuscule
