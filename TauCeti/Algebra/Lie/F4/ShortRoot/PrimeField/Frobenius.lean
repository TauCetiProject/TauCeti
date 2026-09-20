/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.F4.ShortRoot.PrimeField.PointsFunctor
public import TauCeti.FieldTheory.Finite.Frobenius
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Frobenius

/-!
# Frobenius on the short-root type-F4 prime-field carrier

This file defines the Frobenius endomorphisms of the carrier's matrix-valued points. The
finite-field Frobenius algebra homomorphism exists for every `ZMod 2`-algebra, including the zero
ring, so the coefficient formula and all functor laws need no separate characteristic hypothesis.

## Main declarations

* `PrimeField.frobenius` is the point map induced by an iterate of the finite-field Frobenius.
* `PrimeField.coe_frobenius_apply` is its entrywise `2 ^ m`-power formula.
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
* The corresponding integral short-root construction in
  `TauCeti.Algebra.Lie.F4.ShortRoot.Frobenius`.
-/

public section

open scoped Matrix

namespace TauCeti.F4ShortRoot

universe v

namespace PrimeField

/-- **The `2 ^ m`-power Frobenius endomorphism of the carrier over `𝔽₂`**, the map on points
induced by the iterated Frobenius of the value algebra.

For `m` positive this is the `2 ^ m`-power Frobenius of the carrier's points; at `m = 0` it is the
identity. -/
noncomputable def frobenius (m : ℕ) (A : Type v) [CommRing A] [Algebra (ZMod 2) A] :
    points A →* points A := pointsMap ((FiniteField.frobeniusAlgHom (ZMod 2) A) ^ m)

/-- The Frobenius endomorphism of the carrier over `𝔽₂` maps matrices entrywise by the finite-field
Frobenius algebra homomorphism. -/
theorem coe_frobenius (m : ℕ) (A : Type v) [CommRing A] [Algebra (ZMod 2) A]
    (g : points A) :
    (frobenius m A g : _root_.Matrix.GeneralLinearGroup (Fin 26) A) =
      _root_.Matrix.GeneralLinearGroup.map
        (((FiniteField.frobeniusAlgHom (ZMod 2) A) ^ m : A →ₐ[ZMod 2] A) : A →+* A) g := by
  simpa only [frobenius] using
    coe_pointsMap ((FiniteField.frobeniusAlgHom (ZMod 2) A) ^ m) g

/-- Entrywise, the Frobenius endomorphism of the carrier over `𝔽₂` raises each matrix coefficient
to its `2 ^ m`-th power. -/
@[simp]
theorem coe_frobenius_apply (m : ℕ) (A : Type v) [CommRing A] [Algebra (ZMod 2) A]
    (g : points A) (i j : Fin 26) :
    ((frobenius m A g : _root_.Matrix.GeneralLinearGroup (Fin 26) A) :
        Matrix (Fin 26) (Fin 26) A) i j =
      ((g : _root_.Matrix.GeneralLinearGroup (Fin 26) A) :
        Matrix (Fin 26) (Fin 26) A) i j ^ 2 ^ m := by
  rw [coe_frobenius, _root_.Matrix.GeneralLinearGroup.map_apply]
  simpa using TauCeti.FiniteField.frobeniusAlgHom_pow_apply (ZMod 2) A m
    (((g : _root_.Matrix.GeneralLinearGroup (Fin 26) A) :
      Matrix (Fin 26) (Fin 26) A) i j)

/-- The zeroth Frobenius iterate is the identity on the carrier's point group. -/
@[simp]
theorem frobenius_zero (A : Type v) [CommRing A] [Algebra (ZMod 2) A] :
    frobenius 0 A = MonoidHom.id _ := by
  have h : (1 : A →ₐ[ZMod 2] A) = AlgHom.id (ZMod 2) A := by ext; rfl
  rw [frobenius, pow_zero, h, pointsMap_id]

/-- Frobenius iterates add under composition on the carrier's point group. -/
theorem frobenius_add (m k : ℕ) (A : Type v) [CommRing A] [Algebra (ZMod 2) A] :
    frobenius (m + k) A = (frobenius m A).comp (frobenius k A) := by
  let F := FiniteField.frobeniusAlgHom (ZMod 2) A
  have hcomp : F ^ m * F ^ k = (F ^ m).comp (F ^ k) := rfl
  rw [frobenius, frobenius, frobenius, pow_add, hcomp, pointsMap_comp]

/-- **Frobenius exponents multiply under taking powers**: the `m`-th power of the `2 ^ k`-power
Frobenius of the carrier, in the endomorphism monoid of its points, is its `2 ^ (k * m)`-power
Frobenius. -/
theorem frobenius_pow (k m : ℕ) (A : Type v) [CommRing A] [Algebra (ZMod 2) A] :
    (show Monoid.End _ from frobenius k A) ^ m = frobenius (k * m) A := by
  induction m with
  | zero => rw [pow_zero, Nat.mul_zero, frobenius_zero]; rfl
  | succ m ih => rw [pow_succ, ih, Nat.mul_succ, frobenius_add (k * m) k A]; rfl

/-- **Frobenius raises the parameter of every numbered simple root subgroup to its `2 ^ m`-th
power.** -/
@[simp]
theorem frobenius_rootSubgroupPoints (m : ℕ) (A : Type v) [CommRing A] [Algebra (ZMod 2) A]
    (k : Fin 4 ⊕ Fin 4) (u : Multiplicative A) :
    frobenius m A (rootSubgroupPoints k A u) =
      rootSubgroupPoints k A (Multiplicative.ofAdd (Multiplicative.toAdd u ^ 2 ^ m)) := by
  rw [frobenius, pointsMap_rootSubgroupPoints]
  congr 2
  simpa using TauCeti.FiniteField.frobeniusAlgHom_pow_apply
    (ZMod 2) A m (Multiplicative.toAdd u)

/-- **Frobenius raises every coordinate of the pinned split weight torus to its `2 ^ m`-th
power.** -/
@[simp]
theorem frobenius_weightTorusPoints (m : ℕ) (A : Type v) [CommRing A] [Algebra (ZMod 2) A]
    (s : Fin 4 → Aˣ) :
    frobenius m A (weightTorusPoints A s) = weightTorusPoints A (s ^ 2 ^ m) := by
  rw [frobenius, pointsMap_weightTorusPoints]
  congr 1
  funext i
  apply Units.ext
  simpa using TauCeti.FiniteField.frobeniusAlgHom_pow_apply (ZMod 2) A m (s i)

/-- **A point of the carrier over `𝔽₂` is fixed by the `2 ^ m`-power Frobenius exactly when all of
its matrix entries lie in the Frobenius-fixed subalgebra.** -/
@[simp]
theorem frobenius_eq_self_iff (m : ℕ) (A : Type v) [CommRing A] [Algebra (ZMod 2) A]
    (g : points A) :
    frobenius m A g = g ↔
      ∀ i j, ((g : _root_.Matrix.GeneralLinearGroup (Fin 26) A) :
          Matrix (Fin 26) (Fin 26) A) i j ∈
        TauCeti.FiniteField.frobeniusFixedSubalgebra (ZMod 2) A m := by
  rw [← SetLike.coe_eq_coe, coe_frobenius, TauCeti.FiniteField.frobeniusFixedSubalgebra_def,
    _root_.Matrix.GeneralLinearGroup.map_eq_self_iff_mem_equalizer]

/-- **The Frobenius-fixed points of the carrier over `𝔽₂` are its points over the Frobenius-fixed
subalgebra.** For `A` an algebraic closure of `𝔽₂` and `0 < m` that subalgebra is the field of
`2 ^ m` elements, but no finiteness of either side is asserted here. -/
theorem map_subtype_fixedSubgroup_frobenius_eq (m : ℕ) (A : Type v) [CommRing A]
    [Algebra (ZMod 2) A] :
    (fixedSubgroup (frobenius m A)).map (points A).subtype =
      (points ↥(TauCeti.FiniteField.frobeniusFixedSubalgebra (ZMod 2) A m)).map
        (_root_.Matrix.GeneralLinearGroup.map
          ((TauCeti.FiniteField.frobeniusFixedSubalgebra (ZMod 2) A m).val :
            ↥(TauCeti.FiniteField.frobeniusFixedSubalgebra (ZMod 2) A m) →+* A)) := by
  rw [TauCeti.map_subtype_fixedSubgroup_of_coe_eq (frobenius m A) _ (coe_frobenius m A),
    points_eq_hopfIdealPointsSubgroup
      ↥(TauCeti.FiniteField.frobeniusFixedSubalgebra (ZMod 2) A m),
    TauCeti.GeneralLinear.map_hopfIdealPointsSubgroup_subalgebra 26 definingIdeal _,
    points_eq_hopfIdealPointsSubgroup A, TauCeti.FiniteField.frobeniusFixedSubalgebra_def,
    _root_.Matrix.GeneralLinearGroup.range_map_val_equalizer]

end PrimeField

end TauCeti.F4ShortRoot
