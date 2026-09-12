/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.SpecialLinear.StandardCarrier.PointsFunctor
public import TauCeti.Algebra.AlgebraicGroup.Frobenius.GeneralLinear

/-!
# Frobenius on the full-weight type-A carrier

`TauCeti.SlStd.groupScheme r` is the explicit full-weight Chevalley carrier of type `A_r` built
from the standard representation of `sl_{r+1}` and its coordinate integral lattice. For a
commutative value ring `A` of exponential characteristic `p`, this file equips its point group
`TauCeti.SlStd.points r A` with the `p ^ k`-power Frobenius endomorphism.

The endomorphism raises every matrix entry to its `p ^ k`-th power. In particular it satisfies the
pinned root-subgroup equation

```text
F(x_i(u)) = x_i(u ^ (p ^ k))
```

for every Bourbaki-numbered raising or lowering generator, and it raises every coordinate of the
split weight torus by the same exponent. Its fixed points are exactly the points of the same
carrier over the Frobenius-fixed subring.

The construction is the carrier's functorial point map at the iterated Frobenius of the value
ring. Nothing here asserts that the carrier is reductive, or that any fixed-point group is finite
or simple.

## Main definitions

* `TauCeti.SlStd.frobenius`: the `p ^ k`-power Frobenius endomorphism of the type-`A_r` point group.

## Main results

* `TauCeti.SlStd.coe_frobenius` and `TauCeti.SlStd.coe_frobenius_apply`: the endomorphism acts by
  entrywise Frobenius.
* `TauCeti.SlStd.frobenius_eq_pointsMap`: it is the functorial point map induced by the iterated
  Frobenius endomorphism of the value ring.
* `TauCeti.SlStd.frobenius_rootSubgroupPoints` and `TauCeti.SlStd.frobenius_weightTorusPoints`: the
  equations on the pinned generating root subgroups and split torus.
* `TauCeti.SlStd.frobenius_zero` and `TauCeti.SlStd.frobenius_add`: the iteration laws.
* `TauCeti.SlStd.map_subtype_fixedSubgroup_frobenius_eq`: the Frobenius-fixed points are the points
  over the Frobenius-fixed subring.

## References

* R. W. Carter, *Finite Groups of Lie Type: Conjugacy Classes and Complex Characters*, §1.17.
* J. C. Jantzen, *Representations of Algebraic Groups*, II.1.

The organization follows the sibling carrier specialization
`TauCeti.Algebra.Lie.Orthogonal.TypeB.SpinCarrier.Frobenius`.

This advances the "points over an algebraically closed field" and "Chevalley--Demazure
construction" targets in Layer 9 of `TauCetiRoadmap/ReductiveGroups/README.md`. Its consumer is
milestone L1 of `TauCetiRoadmap/CFSGStatement/README.md`: this is the Frobenius component intended
for a future construction of the `A_r(p ^ k)` Steinberg map over an algebraic closure of `ZMod p`.
-/

public section

open WithConv

namespace TauCeti.SlStd

universe v

noncomputable section

variable (r p k : ℕ) (A : Type v) [CommRing A] [ExpChar A p]

/-- **The `p ^ k`-power Frobenius endomorphism of the full-weight type-`A_r` carrier.**

For `p` prime, `0 < k`, and `A` an algebraic closure of `ZMod p`, this is the Frobenius component
intended for a future construction of the `A_r(p ^ k)` Steinberg map. -/
def frobenius : points r A →* points r A :=
  pointsMap r (iterateFrobenius A p k)

/-- The Frobenius endomorphism of the type-`A_r` carrier acts by entrywise Frobenius.

This is not a `simp` lemma because `coe_frobenius_apply` is the canonical coefficient-level
normal form. -/
theorem coe_frobenius (g : points r A) :
    (frobenius r p k A g : Matrix.GeneralLinearGroup (Fin (r + 1)) A) =
      Matrix.GeneralLinearGroup.map (iterateFrobenius A p k) g := by
  rw [frobenius, coe_pointsMap]

/-- **The carrier Frobenius is the functorial map on points** induced by the iterated Frobenius
endomorphism of the value ring. -/
theorem frobenius_eq_pointsMap :
    frobenius r p k A = pointsMap r (iterateFrobenius A p k) := by
  rw [frobenius]

/-- Entrywise, the Frobenius endomorphism raises each matrix coefficient to its
`p ^ k`-th power. -/
@[simp]
theorem coe_frobenius_apply (g : points r A) (i j : Fin (r + 1)) :
    ((frobenius r p k A g : Matrix.GeneralLinearGroup (Fin (r + 1)) A) :
        Matrix (Fin (r + 1)) (Fin (r + 1)) A) i j =
      ((g : Matrix.GeneralLinearGroup (Fin (r + 1)) A) :
        Matrix (Fin (r + 1)) (Fin (r + 1)) A) i j ^ p ^ k := by
  rw [coe_frobenius, Matrix.GeneralLinearGroup.map_apply, iterateFrobenius_def]

/-- **Frobenius raises the parameter of a numbered type-`A_r` root subgroup to its
`p ^ k`-th power.** -/
@[simp]
theorem frobenius_rootSubgroupPoints (i : Fin r ⊕ Fin r) (u : Multiplicative A) :
    frobenius r p k A (rootSubgroupPoints r i A u) =
      rootSubgroupPoints r i A
        (Multiplicative.ofAdd (Multiplicative.toAdd u ^ p ^ k)) := by
  rw [frobenius, pointsMap_rootSubgroupPoints]
  exact Subtype.ext (by rw [iterateFrobenius_def])

/-- **Frobenius raises every coordinate of the pinned split torus to its `p ^ k`-th power.** -/
@[simp]
theorem frobenius_weightTorusPoints (s : Fin r → Aˣ) :
    frobenius r p k A (weightTorusPoints r A s) = weightTorusPoints r A (s ^ p ^ k) := by
  have hs : (fun i => Units.map (iterateFrobenius A p k : A →* A) (s i)) = s ^ p ^ k := by
    funext i
    exact Units.ext (by
      rw [Units.coe_map, MonoidHom.coe_coe, iterateFrobenius_def, Pi.pow_apply,
        Units.val_pow_eq_pow_val])
  rw [frobenius, pointsMap_weightTorusPoints, hs]

/-- The zeroth Frobenius iterate is the identity on the type-`A_r` point group. -/
@[simp]
theorem frobenius_zero : frobenius r p 0 A = MonoidHom.id _ := by
  rw [frobenius, iterateFrobenius_zero, pointsMap_id]

/-- Frobenius iterates add under composition on the type-`A_r` point group. -/
theorem frobenius_add (m : ℕ) :
    frobenius r p (k + m) A = (frobenius r p k A).comp (frobenius r p m A) := by
  rw [frobenius, frobenius, frobenius, iterateFrobenius_add, pointsMap_comp]

/-- A type-`A_r` carrier point is fixed by Frobenius exactly when all of its matrix entries lie in
the Frobenius-fixed subring. -/
@[simp]
theorem frobenius_eq_self_iff (g : points r A) :
    frobenius r p k A g = g ↔
      ∀ i j, ((g : Matrix.GeneralLinearGroup (Fin (r + 1)) A) :
          Matrix (Fin (r + 1)) (Fin (r + 1)) A) i j ∈ frobeniusFixedSubring A p k := by
  rw [← SetLike.coe_eq_coe, coe_frobenius,
    Matrix.GeneralLinearGroup.map_iterateFrobenius_eq_self_iff]

/-- **The Frobenius-fixed points of the full-weight type-`A_r` carrier are its points over the
Frobenius-fixed subring.** -/
theorem map_subtype_fixedSubgroup_frobenius_eq :
    (fixedSubgroup (frobenius r p k A)).map (points r A).subtype =
      (points r ↥(frobeniusFixedSubring A p k)).map
        (Matrix.GeneralLinearGroup.map (frobeniusFixedSubring A p k).subtype) := by
  rw [TauCeti.map_subtype_fixedSubgroup_of_coe_eq (frobenius r p k A) _
      (coe_frobenius r p k A),
    points_def r A, points_def r ↥(frobeniusFixedSubring A p k),
    TauCeti.GeneralLinear.map_hopfIdealPointsSubgroup_frobeniusFixedSubring]

end

end TauCeti.SlStd
