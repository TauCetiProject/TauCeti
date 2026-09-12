/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Frobenius.GeneralLinear
public import TauCeti.Algebra.CharP.Frobenius.Basic
public import TauCeti.Algebra.Lie.Symplectic.StandardCarrier.PointsFunctor

/-!
# Frobenius on the full-weight type-C carrier

`TauCeti.SpStd.groupScheme n` is the explicit full-weight Chevalley carrier of type `C_(n+1)`,
built from the standard representation of `sp_(2n+2)` and its coordinate integral lattice. For a
commutative value ring `A` of exponential characteristic `p`, this file equips its point group
`TauCeti.SpStd.points n A` with the `p ^ k`-power Frobenius endomorphism.

The endomorphism raises every matrix entry to its `p ^ k`-th power. In particular it satisfies the
pinned root-subgroup equation

```text
F(x_i(u)) = x_i(u ^ (p ^ k))
```

for every Bourbaki-numbered raising or lowering generator, and it raises every coordinate of the
split weight torus by the same exponent. Its fixed points are exactly the points of the same
carrier over the Frobenius-fixed subring.

The construction is the carrier's functorial point map at the iterated Frobenius of the value
ring. Nothing asserts that the carrier is reductive, that it is the symplectic group scheme, or
that any fixed-point group is finite or simple.

## Main definitions

* `TauCeti.SpStd.frobenius`: the `p ^ k`-power Frobenius endomorphism of the type-`C_(n+1)` point
  group.

## Main results

* `TauCeti.SpStd.coe_frobenius` and `TauCeti.SpStd.coe_frobenius_apply`: the endomorphism acts by
  entrywise Frobenius.
* `TauCeti.SpStd.frobenius_eq_pointsMap`: Frobenius is the functorial point map induced by the
  iterated Frobenius endomorphism of the value ring.
* `TauCeti.SpStd.frobenius_rootSubgroupPoints` and `TauCeti.SpStd.frobenius_weightTorusPoints`: the
  equations on the pinned generating root subgroups and split torus.
* `TauCeti.SpStd.frobenius_zero` and `TauCeti.SpStd.frobenius_add`: the iteration laws.
* `TauCeti.SpStd.map_subtype_fixedSubgroup_frobenius_eq`: the Frobenius-fixed points are the points
  over the Frobenius-fixed subring.

## References

* R. W. Carter, *Finite Groups of Lie Type: Conjugacy Classes and Complex Characters*, §1.17.
* J. C. Jantzen, *Representations of Algebraic Groups*, II.1.

The organization follows the sibling carrier specialization
`TauCeti.Algebra.Lie.Orthogonal.TypeB.SpinCarrier.Frobenius`.

This advances the "points over an algebraically closed field" and "Chevalley--Demazure
construction" targets in Layer 9 of `TauCetiRoadmap/ReductiveGroups/README.md`, whose first named
case is the `q`-power Frobenius. Its consumer is milestone L1 of
`TauCetiRoadmap/CFSGStatement/README.md`, whose Steinberg map for the untwisted family `C_n(q)` is
`Frob_q` on the points of the pinned type-`C` ambient group over an algebraic closure of `ZMod p`.
The type-`A` counterpart is
`TauCeti/Algebra/Lie/SpecialLinear/StandardCarrier/Frobenius.lean`.
-/

public section

open WithConv

namespace TauCeti.SpStd

universe v

noncomputable section

variable (n p k : ℕ) (A : Type v) [CommRing A] [ExpChar A p]

/-- **The `p ^ k`-power Frobenius endomorphism of the full-weight type-`C_(n+1)` carrier.**

For `p` prime, `0 < k`, and `A` an algebraic closure of `ZMod p`, this is the Frobenius component
intended for a future construction of the `C_(n+1)(p ^ k)` Steinberg map. -/
def frobenius : points n A →* points n A :=
  pointsMap n (iterateFrobenius A p k)

/-- The Frobenius endomorphism of the type-`C_(n+1)` carrier acts by entrywise Frobenius.

This is not a `simp` lemma because `coe_frobenius_apply` is the canonical coefficient-level
normal form. -/
theorem coe_frobenius (g : points n A) :
    (frobenius n p k A g : _root_.Matrix.GeneralLinearGroup (Fin ((n + 1) + (n + 1))) A) =
      _root_.Matrix.GeneralLinearGroup.map (iterateFrobenius A p k) g := by
  rw [frobenius, coe_pointsMap]

/-- The carrier Frobenius is the functorial map on points induced by the iterated Frobenius
endomorphism of the value ring. -/
theorem frobenius_eq_pointsMap :
    frobenius n p k A = pointsMap n (iterateFrobenius A p k) := by
  rw [frobenius]

/-- Entrywise, the Frobenius endomorphism raises each matrix coefficient to its
`p ^ k`-th power. -/
@[simp]
theorem coe_frobenius_apply (g : points n A) (i j : Fin ((n + 1) + (n + 1))) :
    ((frobenius n p k A g : _root_.Matrix.GeneralLinearGroup (Fin ((n + 1) + (n + 1))) A) :
        _root_.Matrix (Fin ((n + 1) + (n + 1))) (Fin ((n + 1) + (n + 1))) A) i j =
      ((g : _root_.Matrix.GeneralLinearGroup (Fin ((n + 1) + (n + 1))) A) :
        _root_.Matrix (Fin ((n + 1) + (n + 1))) (Fin ((n + 1) + (n + 1))) A) i j ^ p ^ k := by
  rw [coe_frobenius, Matrix.GeneralLinearGroup.map_apply, iterateFrobenius_def]

/-- **Frobenius raises the parameter of a numbered type-`C_(n+1)` root subgroup to its
`p ^ k`-th power.** -/
@[simp]
theorem frobenius_rootSubgroupPoints (i : Fin (n + 1) ⊕ Fin (n + 1)) (u : Multiplicative A) :
    frobenius n p k A (rootSubgroupPoints n i A u) =
      rootSubgroupPoints n i A
        (Multiplicative.ofAdd (Multiplicative.toAdd u ^ p ^ k)) := by
  rw [frobenius, pointsMap_rootSubgroupPoints]
  exact Subtype.ext (by rw [iterateFrobenius_def])

/-- **Frobenius raises every coordinate of the pinned split torus to its `p ^ k`-th power.** -/
@[simp]
theorem frobenius_weightTorusPoints (s : Fin (n + 1) → Aˣ) :
    frobenius n p k A (weightTorusPoints n A s) = weightTorusPoints n A (s ^ p ^ k) := by
  rw [frobenius, pointsMap_weightTorusPoints, map_iterateFrobenius_units_eq_pow]

/-- The zeroth Frobenius iterate is the identity on the type-`C_(n+1)` point group. -/
@[simp]
theorem frobenius_zero : frobenius n p 0 A = MonoidHom.id _ := by
  rw [frobenius, iterateFrobenius_zero, pointsMap_id]

/-- Frobenius iterates add under composition on the type-`C_(n+1)` point group. -/
theorem frobenius_add (m : ℕ) :
    frobenius n p (k + m) A = (frobenius n p k A).comp (frobenius n p m A) := by
  rw [frobenius, frobenius, frobenius, iterateFrobenius_add, pointsMap_comp]

/-- A type-`C_(n+1)` carrier point is fixed by Frobenius exactly when all of its matrix entries lie
in the Frobenius-fixed subring. -/
@[simp]
theorem frobenius_eq_self_iff (g : points n A) :
    frobenius n p k A g = g ↔
      ∀ i j, ((g : _root_.Matrix.GeneralLinearGroup (Fin ((n + 1) + (n + 1))) A) :
          _root_.Matrix (Fin ((n + 1) + (n + 1))) (Fin ((n + 1) + (n + 1))) A) i j ∈
        frobeniusFixedSubring A p k := by
  rw [← SetLike.coe_eq_coe, coe_frobenius,
    Matrix.GeneralLinearGroup.map_iterateFrobenius_eq_self_iff]

/-- **The Frobenius-fixed points of the full-weight type-`C_(n+1)` carrier are its points over the
Frobenius-fixed subring.** -/
theorem map_subtype_fixedSubgroup_frobenius_eq :
    (fixedSubgroup (frobenius n p k A)).map (points n A).subtype =
      (points n ↥(frobeniusFixedSubring A p k)).map
        (_root_.Matrix.GeneralLinearGroup.map (frobeniusFixedSubring A p k).subtype) := by
  rw [TauCeti.map_subtype_fixedSubgroup_of_coe_eq (frobenius n p k A) _
      (coe_frobenius n p k A),
    points_def n A, points_def n ↥(frobeniusFixedSubring A p k),
    TauCeti.GeneralLinear.map_hopfIdealPointsSubgroup_frobeniusFixedSubring]

end

end TauCeti.SpStd
