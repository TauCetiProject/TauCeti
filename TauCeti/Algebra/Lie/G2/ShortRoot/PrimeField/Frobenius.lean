/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.G2.ShortRoot.PrimeField.PointsFunctor
public import TauCeti.FieldTheory.Finite.Frobenius
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Frobenius

/-!
# Frobenius on the short-root type-G2 prime-field carrier

This file defines the Frobenius endomorphisms of the carrier's matrix-valued points. The
finite-field Frobenius algebra homomorphism exists for every `ZMod 3`-algebra, including the zero
ring, so the coefficient formula and all functor laws need no separate characteristic hypothesis.

Over an algebraic closure of `𝔽₃`, and for `0 < m`, the points fixed by the `3 ^ m`-power
Frobenius are those with entries in the field of `3 ^ m` elements, which is how a group of type
`G₂` over a finite field is cut out of the carrier. The twisted groups of the same diagram need
one further ingredient, the length-exchanging special isogeny of characteristic three, whose
square is the `3`-power Frobenius defined here.

## Main declarations

* `PrimeField.frobenius` is the point map induced by an iterate of the finite-field Frobenius.
* `PrimeField.coe_frobenius_apply` is its entrywise `3 ^ m`-power formula.
* `PrimeField.frobenius_zero`, `PrimeField.frobenius_add`, and `PrimeField.frobenius_pow` are the
  iteration laws inherited from point functoriality.
* `PrimeField.frobenius_rootSubgroupPoints` and `PrimeField.frobenius_weightTorusPoints` describe
  the action on the pinned generators.
* `PrimeField.frobenius_eq_self_iff` and `PrimeField.map_subtype_fixedSubgroup_frobenius_eq` say
  which points it fixes, and identify the fixed subgroup with the carrier's points over the
  Frobenius-fixed subalgebra. No finiteness of either side is asserted.

## References

* R. W. Carter, *Finite Groups of Lie Type: Conjugacy Classes and Complex Characters*, §1.17.
* R. W. Carter, *Simple Groups of Lie Type*, §§4.4 and 11.3.
* J. C. Jantzen, *Representations of Algebraic Groups*, II.1.
-/

/- Formal source: the declaration order, statements and proof plan follow the type-`F₄` sibling
`TauCeti.Algebra.Lie.F4.ShortRoot.PrimeField.Frobenius`, of which this is the seven-dimensional
characteristic-three instance. -/

public section

open scoped Matrix

namespace TauCeti.G2ShortRoot

universe v

namespace PrimeField

/-- **The `3 ^ m`-power Frobenius endomorphism of the carrier over `𝔽₃`**, the map on points
induced by the iterated Frobenius of the value algebra.

For `m` positive this is the `3 ^ m`-power Frobenius of the carrier's points; at `m = 0` it is the
identity. -/
noncomputable def frobenius (m : ℕ) (A : Type v) [CommRing A] [Algebra (ZMod 3) A] :
    points A →* points A := pointsMap ((FiniteField.frobeniusAlgHom (ZMod 3) A) ^ m)

/-- The Frobenius endomorphism of the carrier over `𝔽₃` maps matrices entrywise by the finite-field
Frobenius algebra homomorphism. -/
theorem coe_frobenius (m : ℕ) (A : Type v) [CommRing A] [Algebra (ZMod 3) A]
    (g : points A) :
    (frobenius m A g : _root_.Matrix.GeneralLinearGroup (Fin 7) A) =
      _root_.Matrix.GeneralLinearGroup.map
        (((FiniteField.frobeniusAlgHom (ZMod 3) A) ^ m : A →ₐ[ZMod 3] A) : A →+* A) g := by
  simpa only [frobenius] using
    coe_pointsMap ((FiniteField.frobeniusAlgHom (ZMod 3) A) ^ m) g

/-- Entrywise, the Frobenius endomorphism of the carrier over `𝔽₃` raises each matrix coefficient
to its `3 ^ m`-th power. -/
@[simp]
theorem coe_frobenius_apply (m : ℕ) (A : Type v) [CommRing A] [Algebra (ZMod 3) A]
    (g : points A) (i j : Fin 7) :
    ((frobenius m A g : _root_.Matrix.GeneralLinearGroup (Fin 7) A) :
        Matrix (Fin 7) (Fin 7) A) i j =
      ((g : _root_.Matrix.GeneralLinearGroup (Fin 7) A) :
        Matrix (Fin 7) (Fin 7) A) i j ^ 3 ^ m := by
  rw [coe_frobenius, _root_.Matrix.GeneralLinearGroup.map_apply]
  simpa using TauCeti.FiniteField.frobeniusAlgHom_pow_apply (ZMod 3) A m
    (((g : _root_.Matrix.GeneralLinearGroup (Fin 7) A) :
      Matrix (Fin 7) (Fin 7) A) i j)

/-- The zeroth Frobenius iterate is the identity on the carrier's point group. -/
@[simp]
theorem frobenius_zero (A : Type v) [CommRing A] [Algebra (ZMod 3) A] :
    frobenius 0 A = MonoidHom.id _ := by
  have h : (1 : A →ₐ[ZMod 3] A) = AlgHom.id (ZMod 3) A := by ext; rfl
  rw [frobenius, pow_zero, h, pointsMap_id]

/-- Frobenius iterates add under composition on the carrier's point group. -/
theorem frobenius_add (m k : ℕ) (A : Type v) [CommRing A] [Algebra (ZMod 3) A] :
    frobenius (m + k) A = (frobenius m A).comp (frobenius k A) := by
  let F := FiniteField.frobeniusAlgHom (ZMod 3) A
  have hcomp : F ^ m * F ^ k = (F ^ m).comp (F ^ k) := rfl
  rw [frobenius, frobenius, frobenius, pow_add, hcomp, pointsMap_comp]

/-- **Frobenius exponents multiply under taking powers**: the `m`-th power of the `3 ^ k`-power
Frobenius of the carrier, in the endomorphism monoid of its points, is its `3 ^ (k * m)`-power
Frobenius. -/
theorem frobenius_pow (k m : ℕ) (A : Type v) [CommRing A] [Algebra (ZMod 3) A] :
    (show Monoid.End _ from frobenius k A) ^ m = frobenius (k * m) A := by
  induction m with
  | zero => rw [pow_zero, Nat.mul_zero, frobenius_zero]; rfl
  | succ m ih => rw [pow_succ, ih, Nat.mul_succ, frobenius_add (k * m) k A]; rfl

/-- **Frobenius raises the parameter of every numbered simple root subgroup to its `3 ^ m`-th
power.** -/
@[simp]
theorem frobenius_rootSubgroupPoints (m : ℕ) (A : Type v) [CommRing A] [Algebra (ZMod 3) A]
    (k : Fin 2 ⊕ Fin 2) (u : Multiplicative A) :
    frobenius m A (rootSubgroupPoints k A u) =
      rootSubgroupPoints k A (Multiplicative.ofAdd (Multiplicative.toAdd u ^ 3 ^ m)) := by
  rw [frobenius, pointsMap_rootSubgroupPoints]
  congr 2
  simpa using TauCeti.FiniteField.frobeniusAlgHom_pow_apply
    (ZMod 3) A m (Multiplicative.toAdd u)

/-- **Frobenius raises every coordinate of the pinned split weight torus to its `3 ^ m`-th
power.** -/
@[simp]
theorem frobenius_weightTorusPoints (m : ℕ) (A : Type v) [CommRing A] [Algebra (ZMod 3) A]
    (s : Fin 2 → Aˣ) :
    frobenius m A (weightTorusPoints A s) = weightTorusPoints A (s ^ 3 ^ m) := by
  rw [frobenius, pointsMap_weightTorusPoints]
  congr 1
  funext i
  apply Units.ext
  simpa using TauCeti.FiniteField.frobeniusAlgHom_pow_apply (ZMod 3) A m (s i)

/-- **A point of the carrier over `𝔽₃` is fixed by the `3 ^ m`-power Frobenius exactly when all of
its matrix entries lie in the Frobenius-fixed subalgebra.** -/
@[simp]
theorem frobenius_eq_self_iff (m : ℕ) (A : Type v) [CommRing A] [Algebra (ZMod 3) A]
    (g : points A) :
    frobenius m A g = g ↔
      ∀ i j, ((g : _root_.Matrix.GeneralLinearGroup (Fin 7) A) :
          Matrix (Fin 7) (Fin 7) A) i j ∈
        TauCeti.FiniteField.frobeniusFixedSubalgebra (ZMod 3) A m := by
  rw [← SetLike.coe_eq_coe, coe_frobenius, TauCeti.FiniteField.frobeniusFixedSubalgebra_def,
    _root_.Matrix.GeneralLinearGroup.map_eq_self_iff_mem_equalizer]

/-- **The Frobenius-fixed points of the carrier over `𝔽₃` are its points over the Frobenius-fixed
subalgebra.** For `A` an algebraic closure of `𝔽₃` and `0 < m` that subalgebra is the field of
`3 ^ m` elements, but no finiteness of either side is asserted here. -/
theorem map_subtype_fixedSubgroup_frobenius_eq (m : ℕ) (A : Type v) [CommRing A]
    [Algebra (ZMod 3) A] :
    (fixedSubgroup (frobenius m A)).map (points A).subtype =
      (points ↥(TauCeti.FiniteField.frobeniusFixedSubalgebra (ZMod 3) A m)).map
        (_root_.Matrix.GeneralLinearGroup.map
          ((TauCeti.FiniteField.frobeniusFixedSubalgebra (ZMod 3) A m).val :
            ↥(TauCeti.FiniteField.frobeniusFixedSubalgebra (ZMod 3) A m) →+* A)) := by
  rw [TauCeti.map_subtype_fixedSubgroup_of_coe_eq (frobenius m A) _ (coe_frobenius m A),
    points_eq_hopfIdealPointsSubgroup
      ↥(TauCeti.FiniteField.frobeniusFixedSubalgebra (ZMod 3) A m),
    TauCeti.GeneralLinear.map_hopfIdealPointsSubgroup_subalgebra 7 definingIdeal _,
    points_eq_hopfIdealPointsSubgroup A, TauCeti.FiniteField.frobeniusFixedSubalgebra_def,
    _root_.Matrix.GeneralLinearGroup.range_map_val_equalizer]

end PrimeField

end TauCeti.G2ShortRoot
