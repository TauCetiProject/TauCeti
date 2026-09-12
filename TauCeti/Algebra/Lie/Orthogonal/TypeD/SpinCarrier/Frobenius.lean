/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Frobenius.GeneralLinear
public import TauCeti.Algebra.Lie.Orthogonal.TypeD.SpinCarrier.PointsFunctor
import TauCeti.Algebra.CharP.Frobenius.Basic

/-!
# Frobenius on the full-weight type-D spin carrier

`TauCeti.TypeDSpinCarrier.groupScheme n hn` is the explicit full-weight Chevalley carrier of type
`Dₙ`, cut out inside `GL_(2^n)` over `ℤ` by the split spin representation and its exterior
coordinate lattice. For a commutative value ring `A` of exponential characteristic `p`, this file
equips its point group `TauCeti.TypeDSpinCarrier.points n hn A` with the `p ^ k`-power Frobenius
endomorphism.

The endomorphism raises every matrix entry to its `p ^ k`-th power. In particular it satisfies the
pinned root-subgroup equation

```text
F (x_i(u)) = x_i(u ^ (p ^ k))
```

for every Bourbaki-numbered raising or lowering generator, and it raises every coordinate of the
split spin weight torus by the same exponent. Its fixed points are exactly the points of the same
carrier over the Frobenius-fixed subring of `A`.

The construction is the carrier's functorial point map at the iterated Frobenius of the value
ring. Nothing asserts that the carrier is reductive, that it is the spin group scheme, or that
any fixed-point group is finite or simple.

## Main definitions

* `TauCeti.TypeDSpinCarrier.frobenius`: the `p ^ k`-power Frobenius endomorphism of the type-`Dₙ`
  spin carrier's point group.

## Main results

* `TauCeti.TypeDSpinCarrier.coe_frobenius` and `TauCeti.TypeDSpinCarrier.coe_frobenius_apply`: the
  endomorphism acts by entrywise Frobenius.
* `TauCeti.TypeDSpinCarrier.frobenius_eq_pointsMap`: it is the functorial point map induced by the
  iterated Frobenius endomorphism of the value ring.
* `TauCeti.TypeDSpinCarrier.frobenius_rootSubgroupPoints` and
  `TauCeti.TypeDSpinCarrier.frobenius_weightTorusPoints`: the equations on the pinned generating
  root subgroups and split spin weight torus.
* `TauCeti.TypeDSpinCarrier.frobenius_zero` and `TauCeti.TypeDSpinCarrier.frobenius_add`: the
  iteration laws.
* `TauCeti.TypeDSpinCarrier.frobenius_eq_self_iff` and
  `TauCeti.TypeDSpinCarrier.map_subtype_fixedSubgroup_frobenius_eq`: a point is fixed exactly when
  its entries lie in the Frobenius-fixed subring, so the fixed points are the points of the same
  carrier over that subring.

## References

* R. W. Carter, *Finite Groups of Lie Type: Conjugacy Classes and Complex Characters*, §1.17.
* J. C. Jantzen, *Representations of Algebraic Groups*, II.1.

The organization follows the sibling carrier specialization
`TauCeti.Algebra.Lie.Orthogonal.TypeB.SpinCarrier.Frobenius`.
-/

public section

namespace TauCeti.TypeDSpinCarrier

open TauCeti.UniversalEnvelopingAlgebra

universe v

noncomputable section

variable (n : ℕ) (hn : 4 ≤ n) (p k : ℕ) (A : Type v) [CommRing A] [ExpChar A p]

/-- **The `p ^ k`-power Frobenius endomorphism of the full-weight type-`Dₙ` spin carrier.**

For `p` prime, `0 < k`, and `A` an algebraic closure of `ZMod p`, this is the Frobenius component
intended for a future construction of the `Dₙ(p ^ k)`, `²Dₙ(p ^ k)` and `³D₄(p ^ k)` Steinberg
maps. -/
def frobenius : points n hn A →* points n hn A :=
  pointsMap n hn (iterateFrobenius A p k)

/-- The Frobenius endomorphism of the type-`Dₙ` spin carrier acts by entrywise Frobenius.

This is not a `simp` lemma because `coe_frobenius_apply` is the canonical coefficient-level normal
form. -/
theorem coe_frobenius (g : points n hn A) :
    (frobenius n hn p k A g : _root_.Matrix.GeneralLinearGroup (Fin (dimension n)) A) =
      _root_.Matrix.GeneralLinearGroup.map (iterateFrobenius A p k) g := by
  rw [frobenius, coe_pointsMap]

/-- **The carrier Frobenius is the functorial map on points** induced by the iterated Frobenius
endomorphism of the value ring. -/
theorem frobenius_eq_pointsMap :
    frobenius n hn p k A = pointsMap n hn (iterateFrobenius A p k) := by
  rw [frobenius]

/-- Entrywise, the Frobenius endomorphism raises each matrix coefficient to its `p ^ k`-th
power. -/
@[simp]
theorem coe_frobenius_apply (g : points n hn A) (r c : Fin (dimension n)) :
    ((frobenius n hn p k A g : _root_.Matrix.GeneralLinearGroup (Fin (dimension n)) A) :
        _root_.Matrix (Fin (dimension n)) (Fin (dimension n)) A) r c =
      ((g : _root_.Matrix.GeneralLinearGroup (Fin (dimension n)) A) :
        _root_.Matrix (Fin (dimension n)) (Fin (dimension n)) A) r c ^ p ^ k := by
  rw [coe_frobenius, _root_.Matrix.GeneralLinearGroup.map_apply, iterateFrobenius_def]

/-- **Frobenius raises the parameter of a numbered type-`Dₙ` root subgroup to its `p ^ k`-th
power**, that is, `F (x_i(u)) = x_i(u ^ (p ^ k))` on both the raising and the lowering
generators. -/
@[simp]
theorem frobenius_rootSubgroupPoints (i : Fin n ⊕ Fin n) (u : Multiplicative A) :
    frobenius n hn p k A (rootSubgroupPoints n hn i A u) =
      rootSubgroupPoints n hn i A
        (Multiplicative.ofAdd (Multiplicative.toAdd u ^ p ^ k)) := by
  rw [frobenius, pointsMap_rootSubgroupPoints]
  exact Subtype.ext (by rw [iterateFrobenius_def])

/-- **Frobenius raises every coordinate of the pinned split spin weight torus to its `p ^ k`-th
power.** -/
@[simp]
theorem frobenius_weightTorusPoints (s : Fin n → Aˣ) :
    frobenius n hn p k A (weightTorusPoints n hn A s) =
      weightTorusPoints n hn A (s ^ p ^ k) := by
  rw [frobenius, pointsMap_weightTorusPoints, map_iterateFrobenius_units_eq_pow]

/-- The zeroth Frobenius iterate is the identity on the type-`Dₙ` spin carrier's point group. -/
@[simp]
theorem frobenius_zero : frobenius n hn p 0 A = MonoidHom.id _ := by
  rw [frobenius, iterateFrobenius_zero, pointsMap_id]

/-- Frobenius iterates add under composition on the type-`Dₙ` spin carrier's point group. -/
theorem frobenius_add (m : ℕ) :
    frobenius n hn p (k + m) A = (frobenius n hn p k A).comp (frobenius n hn p m A) := by
  rw [frobenius, frobenius, frobenius, iterateFrobenius_add, pointsMap_comp]

/-- A type-`Dₙ` spin carrier point is fixed by Frobenius exactly when all of its matrix entries lie
in the Frobenius-fixed subring. -/
@[simp]
theorem frobenius_eq_self_iff (g : points n hn A) :
    frobenius n hn p k A g = g ↔
      ∀ r c, ((g : _root_.Matrix.GeneralLinearGroup (Fin (dimension n)) A) :
          _root_.Matrix (Fin (dimension n)) (Fin (dimension n)) A) r c ∈
        frobeniusFixedSubring A p k := by
  rw [← SetLike.coe_eq_coe, coe_frobenius,
    _root_.Matrix.GeneralLinearGroup.map_iterateFrobenius_eq_self_iff]

/-- **The Frobenius-fixed points of the full-weight type-`Dₙ` spin carrier are its points over the
Frobenius-fixed subring.** For `p` prime, `0 < k`, `A` an algebraic closure of `ZMod p` and
`q = p ^ k` this reads the fixed group of the untwisted `Dₙ(q)` Steinberg map as the carrier's
`𝔽_q`-points; no finiteness of either side is asserted. -/
theorem map_subtype_fixedSubgroup_frobenius_eq :
    (fixedSubgroup (frobenius n hn p k A)).map (points n hn A).subtype =
      (points n hn ↥(frobeniusFixedSubring A p k)).map
        (_root_.Matrix.GeneralLinearGroup.map (frobeniusFixedSubring A p k).subtype) := by
  rw [TauCeti.map_subtype_fixedSubgroup_of_coe_eq (frobenius n hn p k A) _
      (coe_frobenius n hn p k A),
    points_def n hn A, points_def n hn ↥(frobeniusFixedSubring A p k),
    TauCeti.GeneralLinear.map_hopfIdealPointsSubgroup_frobeniusFixedSubring]

end

end TauCeti.TypeDSpinCarrier
