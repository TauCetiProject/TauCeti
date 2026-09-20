/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Frobenius.GeneralLinear
public import TauCeti.Algebra.CharP.Frobenius.Basic
public import TauCeti.Algebra.Lie.Orthogonal.TypeB.SpinCarrier.PointsFunctor

/-!
# Frobenius on the full-weight type-B spin carrier

`TauCeti.TypeBSpinCarrier.groupScheme n` is the explicit full-weight Chevalley carrier of
type `Bₙ₊₁`, cut out inside `GL_(2^(n+1))` over `ℤ` by the split spin representation and its
exterior coordinate lattice. For a commutative value ring `A` of exponential characteristic
`p`, this file equips its point group `TauCeti.TypeBSpinCarrier.points n A` with the `p ^ k`-power
Frobenius endomorphism.

The endomorphism raises every matrix entry to its `p ^ k`-th power. In particular it satisfies the
pinned root-subgroup equation

```text
F (x_i(u)) = x_i(u ^ (p ^ k))
```

for every Bourbaki-numbered raising or lowering generator, and it raises every coordinate of the
split spin weight torus by the same exponent. Its fixed points are exactly the points of the same
carrier over the Frobenius-fixed subring of `A`.

The construction uses the carrier's functorial point map at the iterated Frobenius of the value
ring. Nothing asserts that the carrier is reductive, that it is the spin group scheme, or that any
fixed-point group is finite or simple.

## Main declarations

* `TauCeti.TypeBSpinCarrier.frobenius`: the `p ^ k`-power Frobenius endomorphism of the
  type-`Bₙ₊₁` spin carrier's point group.
* `TauCeti.TypeBSpinCarrier.frobenius_rootSubgroupPoints` and
  `TauCeti.TypeBSpinCarrier.frobenius_weightTorusPoints`: the equations on the numbered root
  subgroups and split weight torus.
* `TauCeti.TypeBSpinCarrier.frobenius_zero`, `TauCeti.TypeBSpinCarrier.frobenius_add` and
  `TauCeti.TypeBSpinCarrier.frobenius_pow`: the iteration laws.
* `TauCeti.TypeBSpinCarrier.frobenius_eq_self_iff`: the coefficientwise fixed-point criterion.
* `TauCeti.TypeBSpinCarrier.map_subtype_fixedSubgroup_frobenius_eq`: the fixed points are the
  carrier's points over the Frobenius-fixed subring.

## References

* R. W. Carter, *Finite Groups of Lie Type: Conjugacy Classes and Complex Characters*, §1.17.
* J. C. Jantzen, *Representations of Algebraic Groups*, II.1.

The organization follows the carrier specializations
`TauCeti.Algebra.Lie.E6.Minuscule.Frobenius` and
`TauCeti.Algebra.Lie.Orthogonal.TypeD.SpinCarrier.Frobenius`.
-/

public section

namespace TauCeti.TypeBSpinCarrier

universe v

noncomputable section

variable (n p k : ℕ) (A : Type v) [CommRing A] [ExpChar A p]

/-- **The `p ^ k`-power Frobenius endomorphism of the full-weight type-`Bₙ₊₁` spin carrier.**

For `p` prime, `0 < k`, and `A` an algebraic closure of `ZMod p`, this is intended to supply the
Frobenius component in a future construction of the `Bₙ₊₁(p ^ k)` Steinberg map. -/
def frobenius : points n A →* points n A :=
  (pointsPresentation n A).map (pointsPresentation n A) (iterateFrobenius A p k)

/-- The Frobenius endomorphism of the type-`Bₙ₊₁` spin carrier acts by entrywise Frobenius.

This is not a `simp` lemma because `coe_frobenius_apply` is the coefficient-level normal form. -/
theorem coe_frobenius (g : points n A) :
    (frobenius n p k A g : _root_.Matrix.GeneralLinearGroup (Fin (dimension n)) A) =
      _root_.Matrix.GeneralLinearGroup.map (iterateFrobenius A p k) g := by
  rw [frobenius, GeneralLinear.IntegralPointsPresentation.coe_map]

/-- Entrywise, the Frobenius endomorphism raises each matrix coefficient to its `p ^ k`-th
power. -/
@[simp]
theorem coe_frobenius_apply (g : points n A) (r c : Fin (dimension n)) :
    ((frobenius n p k A g : _root_.Matrix.GeneralLinearGroup (Fin (dimension n)) A) :
        _root_.Matrix (Fin (dimension n)) (Fin (dimension n)) A) r c =
      ((g : _root_.Matrix.GeneralLinearGroup (Fin (dimension n)) A) :
        _root_.Matrix (Fin (dimension n)) (Fin (dimension n)) A) r c ^ p ^ k := by
  rw [coe_frobenius, _root_.Matrix.GeneralLinearGroup.map_apply, iterateFrobenius_def]

/-- **Frobenius raises the parameter of a numbered type-`Bₙ₊₁` root subgroup to its
`p ^ k`-th power** on both the raising and lowering generators. -/
@[simp]
theorem frobenius_rootSubgroupPoints
    (i : Fin (n + 1) ⊕ Fin (n + 1)) (u : Multiplicative A) :
    frobenius n p k A (rootSubgroupPoints n i A u) =
      rootSubgroupPoints n i A
        (Multiplicative.ofAdd (Multiplicative.toAdd u ^ p ^ k)) := by
  rw [frobenius, map_rootSubgroupPoints]
  exact Subtype.ext (by rw [iterateFrobenius_def])

/-- **Frobenius raises every coordinate of the split spin weight torus to its `p ^ k`-th
power.** -/
@[simp]
theorem frobenius_weightTorusPoints (s : Fin (n + 1) → Aˣ) :
    frobenius n p k A (weightTorusPoints n A s) =
      weightTorusPoints n A (s ^ p ^ k) := by
  rw [frobenius, map_weightTorusPoints, map_iterateFrobenius_units_eq_pow]

/-- The zeroth Frobenius iterate is the identity on the type-`Bₙ₊₁` spin carrier's point
group. -/
@[simp]
theorem frobenius_zero : frobenius n p 0 A = MonoidHom.id _ := by
  rw [frobenius, iterateFrobenius_zero, GeneralLinear.IntegralPointsPresentation.map_id]

/-- Frobenius iterates add under composition on the type-`Bₙ₊₁` spin carrier's point group. -/
theorem frobenius_add (m : ℕ) :
    frobenius n p (k + m) A = (frobenius n p k A).comp (frobenius n p m A) := by
  rw [frobenius, frobenius, frobenius, iterateFrobenius_add,
    GeneralLinear.IntegralPointsPresentation.map_comp (Q := pointsPresentation n A)]

/-- **Frobenius exponents multiply under taking powers**: the `m`-th power of the `p ^ k`-power
Frobenius of the type-`B_(n+1)` spin carrier's point group, in the endomorphism monoid of its
points, is its `p ^ (k * m)`-power
Frobenius. -/
-- `Monoid.End` is definitionally a bundled `MonoidHom`; the `show` picks its composition monoid
-- structure before the power is elaborated.
theorem frobenius_pow (m : ℕ) :
    (show Monoid.End _ from frobenius n p k A) ^ m = frobenius n p (k * m) A := by
  induction m with
  | zero => rw [pow_zero, Nat.mul_zero, frobenius_zero]; rfl
  | succ m ih => rw [pow_succ, ih, Nat.mul_succ, frobenius_add n p (k * m) A k]; rfl

/-- A type-`Bₙ₊₁` spin-carrier point is fixed by Frobenius exactly when all of its matrix
entries lie in the Frobenius-fixed subring. -/
@[simp]
theorem frobenius_eq_self_iff (g : points n A) :
    frobenius n p k A g = g ↔
      ∀ r c, ((g : _root_.Matrix.GeneralLinearGroup (Fin (dimension n)) A) :
          _root_.Matrix (Fin (dimension n)) (Fin (dimension n)) A) r c ∈
        frobeniusFixedSubring A p k := by
  rw [← SetLike.coe_eq_coe, coe_frobenius,
    _root_.Matrix.GeneralLinearGroup.map_iterateFrobenius_eq_self_iff]

/-- **The Frobenius-fixed points of the full-weight type-`Bₙ₊₁` spin carrier are its points
over the Frobenius-fixed subring.** Interpreting this as a statement about a finite group of
type `Bₙ₊₁` will require the future identification of this carrier with the corresponding
spin group scheme. -/
theorem map_subtype_fixedSubgroup_frobenius_eq :
    (fixedSubgroup (frobenius n p k A)).map (points n A).subtype =
      (points n ↥(frobeniusFixedSubring A p k)).map
        (_root_.Matrix.GeneralLinearGroup.map (frobeniusFixedSubring A p k).subtype) := by
  rw [TauCeti.map_subtype_fixedSubgroup_of_coe_eq (frobenius n p k A) _
      (coe_frobenius n p k A),
    points_def n A, points_def n ↥(frobeniusFixedSubring A p k),
    TauCeti.GeneralLinear.map_hopfIdealPointsSubgroup_frobeniusFixedSubring]

end

end TauCeti.TypeBSpinCarrier
