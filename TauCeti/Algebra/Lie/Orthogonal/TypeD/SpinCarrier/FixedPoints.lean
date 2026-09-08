/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Orthogonal.TypeD.SpinCarrier.Frobenius
public import TauCeti.FieldTheory.Finite.SepClosedSubfield

/-!
# Frobenius-fixed points of the full-weight type-D spin carrier

For `4 ≤ n`, `TauCeti.TypeDSpinCarrier.frobenius n hn p k A` is the `p ^ k`-power
Frobenius endomorphism of the full-weight type-`Dₙ` spin carrier over a commutative ring `A` of
exponential characteristic `p`. This file identifies its fixed-point group with the carrier's
points over the Frobenius-fixed subring:

```text
G(A^F) ≃* G(A)^F.
```

The underlying map applies the inclusion `A^F → A` to every matrix entry. Its inverse reads the
entries of a fixed point in `A^F`. Consequently the fixed-point group is finite whenever `A^F` is
finite; in particular this holds over a field of characteristic `p` for every nonzero Frobenius
exponent.

The construction uses `TauCeti.GeneralLinear.frobeniusFixedMulEquivOfCoeEq`, which transports the
fixed-point equivalence for the matrix points cut out by a Hopf ideal. The type-`D` carrier supplies
only its Hopf-ideal presentation and the fact that its Frobenius acts entrywise. Thus no fixed-point
descent is repeated here.

## Main declarations

* `TauCeti.TypeDSpinCarrier.pointsMulEquivFixedSubgroupFrobenius`: the fixed-point group
  equivalence.
* `TauCeti.TypeDSpinCarrier.coe_pointsMulEquivFixedSubgroupFrobenius_eq_pointsMap`: the forward
  map is the functorial map on carrier points induced by `A^F → A`.
* `TauCeti.TypeDSpinCarrier.pointsMap_pointsMulEquivFixedSubgroupFrobenius_symm_apply`: the inverse
  map recovers a fixed point after applying that inclusion.
* `TauCeti.TypeDSpinCarrier.finite_fixedSubgroup_frobenius_of_charP`: the fixed-point group over a
  field of characteristic `p` is finite for every nonzero exponent.

## References

* R. W. Carter, *Finite Groups of Lie Type: Conjugacy Classes and Complex Characters*, §1.17.
* J. C. Jantzen, *Representations of Algebraic Groups*, II.1.

The statement and interface parallel the fixed-point descriptions for the full-weight type-`A`
and type-`C` carriers.
-/

public section

namespace TauCeti.TypeDSpinCarrier

universe v

variable (n : ℕ) (hn : 4 ≤ n) (p k : ℕ)

noncomputable section

variable (A : Type v) [CommRing A] [ExpChar A p]

/-! ## The fixed points as points over the fixed subring -/

/-- **The Frobenius-fixed points of the full-weight type-`Dₙ` spin carrier are its points over
the Frobenius-fixed subring.** For `p` prime, `0 < k`, and `A` an algebraic closure of `ZMod p`,
this is the group isomorphism `G(𝔽_(p^k)) ≃* G(A)^F`.

The equivalence is the generic fixed-point equivalence for the matrix points cut out by
`TauCeti.TypeDSpinCarrier.definingIdeal n hn`, transported to the named carrier points using
`TauCeti.TypeDSpinCarrier.points_def`. -/
def pointsMulEquivFixedSubgroupFrobenius :
    points n hn ↥(frobeniusFixedSubring A p k) ≃*
      ↥(fixedSubgroup (frobenius n hn p k A)) :=
  GeneralLinear.frobeniusFixedMulEquivOfCoeEq (dimension n) p k (definingIdeal n hn) A
    (frobenius n hn p k A) (points_def n hn A)
    (points_def n hn ↥(frobeniusFixedSubring A p k)) (coe_frobenius n hn p k A)

/-- The fixed-point equivalence includes the matrix entries of a point over the Frobenius-fixed
subring into the value ring. -/
theorem coe_pointsMulEquivFixedSubgroupFrobenius
    (g : points n hn ↥(frobeniusFixedSubring A p k)) :
    ((pointsMulEquivFixedSubgroupFrobenius n hn p k A g : points n hn A) :
        Matrix.GeneralLinearGroup (Fin (dimension n)) A) =
      Matrix.GeneralLinearGroup.map (frobeniusFixedSubring A p k).subtype g :=
  GeneralLinear.coe_frobeniusFixedMulEquivOfCoeEq (dimension n) p k (definingIdeal n hn) A
    (frobenius n hn p k A) (points_def n hn A)
    (points_def n hn ↥(frobeniusFixedSubring A p k)) (coe_frobenius n hn p k A) g

/-- Entrywise, the fixed-point equivalence applies the inclusion of the Frobenius-fixed subring. -/
theorem coe_pointsMulEquivFixedSubgroupFrobenius_apply
    (g : points n hn ↥(frobeniusFixedSubring A p k)) (r c : Fin (dimension n)) :
    ((((pointsMulEquivFixedSubgroupFrobenius n hn p k A g : points n hn A) :
          Matrix.GeneralLinearGroup (Fin (dimension n)) A) :
        Matrix (Fin (dimension n)) (Fin (dimension n)) A) r c) =
      ((((g : Matrix.GeneralLinearGroup (Fin (dimension n))
            ↥(frobeniusFixedSubring A p k)) :
          Matrix (Fin (dimension n)) (Fin (dimension n))
            ↥(frobeniusFixedSubring A p k)) r c : ↥(frobeniusFixedSubring A p k)) : A) := by
  rw [coe_pointsMulEquivFixedSubgroupFrobenius, Matrix.GeneralLinearGroup.map_apply,
    Subring.coe_subtype]

/-- The fixed-point equivalence is the functorial point map along the inclusion of the
Frobenius-fixed subring. -/
@[simp]
theorem coe_pointsMulEquivFixedSubgroupFrobenius_eq_pointsMap
    (g : points n hn ↥(frobeniusFixedSubring A p k)) :
    (pointsMulEquivFixedSubgroupFrobenius n hn p k A g : points n hn A) =
      pointsMap n hn (frobeniusFixedSubring A p k).subtype g :=
  Subtype.ext (by rw [coe_pointsMulEquivFixedSubgroupFrobenius, coe_pointsMap])

/-- Including the matrix underlying the inverse image of a Frobenius-fixed point returns the
original matrix. -/
@[simp]
theorem coe_pointsMulEquivFixedSubgroupFrobenius_symm_apply
    (x : ↥(fixedSubgroup (frobenius n hn p k A))) :
    Matrix.GeneralLinearGroup.map (frobeniusFixedSubring A p k).subtype
        ((pointsMulEquivFixedSubgroupFrobenius n hn p k A).symm x) =
      ((x : points n hn A) : Matrix.GeneralLinearGroup (Fin (dimension n)) A) :=
  GeneralLinear.coe_frobeniusFixedMulEquivOfCoeEq_symm_apply (dimension n) p k
    (definingIdeal n hn) A (frobenius n hn p k A) (points_def n hn A)
    (points_def n hn ↥(frobeniusFixedSubring A p k)) (coe_frobenius n hn p k A) x

/-- Entrywise, the inverse equivalence reads a Frobenius-fixed matrix over the fixed subring
without changing its entries. -/
@[simp]
theorem coe_pointsMulEquivFixedSubgroupFrobenius_symm_apply_apply
    (x : ↥(fixedSubgroup (frobenius n hn p k A))) (r c : Fin (dimension n)) :
    (((((pointsMulEquivFixedSubgroupFrobenius n hn p k A).symm x :
            Matrix.GeneralLinearGroup (Fin (dimension n)) ↥(frobeniusFixedSubring A p k)) :
          Matrix (Fin (dimension n)) (Fin (dimension n)) ↥(frobeniusFixedSubring A p k)) r c :
        ↥(frobeniusFixedSubring A p k)) : A) =
      ((((x : points n hn A) : Matrix.GeneralLinearGroup (Fin (dimension n)) A) :
        Matrix (Fin (dimension n)) (Fin (dimension n)) A) r c) := by
  rw [← coe_pointsMulEquivFixedSubgroupFrobenius_symm_apply,
    Matrix.GeneralLinearGroup.map_apply, Subring.coe_subtype]

/-- The inverse equivalence, followed by the functorial point map from the fixed subring, returns
the Frobenius-fixed carrier point. -/
@[simp]
theorem pointsMap_pointsMulEquivFixedSubgroupFrobenius_symm_apply
    (x : ↥(fixedSubgroup (frobenius n hn p k A))) :
    pointsMap n hn (frobeniusFixedSubring A p k).subtype
        ((pointsMulEquivFixedSubgroupFrobenius n hn p k A).symm x) = (x : points n hn A) := by
  rw [← coe_pointsMulEquivFixedSubgroupFrobenius_eq_pointsMap, MulEquiv.apply_symm_apply]

/-! ## Finiteness -/

/-- The Frobenius-fixed points of the full-weight type-`Dₙ` spin carrier form a finite group
whenever the Frobenius-fixed subring is finite. -/
theorem finite_fixedSubgroup_frobenius [Finite ↥(frobeniusFixedSubring A p k)] :
    Finite ↥(fixedSubgroup (frobenius n hn p k A)) :=
  .of_equiv _ (pointsMulEquivFixedSubgroupFrobenius n hn p k A).toEquiv

/-- The Frobenius-fixed points of the full-weight type-`Dₙ` spin carrier over a field of
characteristic `p` form a finite group for every nonzero Frobenius exponent. -/
theorem finite_fixedSubgroup_frobenius_of_charP (K : Type v) [Field K]
    [Fact p.Prime] [CharP K p] (hk : k ≠ 0) :
    Finite ↥(fixedSubgroup (frobenius n hn p k K)) :=
  have := finite_frobeniusFixedSubring K p k hk
  finite_fixedSubgroup_frobenius n hn p k K

end

end TauCeti.TypeDSpinCarrier
