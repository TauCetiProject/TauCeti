/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Frobenius.GeneralLinear
public import TauCeti.Algebra.CharP.Frobenius.Basic
public import TauCeti.Algebra.Lie.G2.ShortRoot.PointsFunctor

/-!
# The Frobenius of the short-root type-G2 carrier

`TauCeti.G2ShortRoot.groupScheme` is the short-root type-`G₂` Chevalley carrier over `ℤ`, the
Kostant toral closure built from the seven-dimensional representation and its admissible
lattice, and `TauCeti.G2ShortRoot.points A` realizes its `A`-valued points as a subgroup of
`GL₇(A)`. Over a commutative ring `A` of exponential characteristic `p`, entrywise `p ^ k`-th
powers are a homomorphism of value rings, so the carrier's functoriality turns them into a group
endomorphism of its points.

This file names that endomorphism `TauCeti.G2ShortRoot.frobenius` and records its characteristic
equations:

```text
F (g)ᵢⱼ = gᵢⱼ ^ (p ^ k),
F (xᵢ(u)) = xᵢ(u ^ (p ^ k)),
F (t(s)) = t(s ^ (p ^ k)).
```

The zeroth iterate is the identity, exponents add under composition and multiply under taking
powers in the endomorphism monoid, and the fixed points are the points of the same carrier over
the Frobenius-fixed subring of `A`.

Nothing here asserts reductivity, maximality of the weight torus, an identification of the
carrier with the pinned simply connected group scheme of type `G₂`, or any finiteness or
simplicity statement.

## Main declarations

* `TauCeti.G2ShortRoot.frobenius`: the `p ^ k`-power Frobenius on the carrier's points.
* `TauCeti.G2ShortRoot.coe_frobenius` and `coe_frobenius_apply`: its matrix and entrywise
  actions.
* `TauCeti.G2ShortRoot.frobenius_rootSubgroupPoints`: its action on every numbered simple-root
  subgroup.
* `TauCeti.G2ShortRoot.frobenius_weightTorusPoints`: its action on the split weight torus.
* `TauCeti.G2ShortRoot.frobenius_zero`, `frobenius_add` and `frobenius_pow`: its iteration laws.
* `TauCeti.G2ShortRoot.frobenius_eq_self_iff` and
  `TauCeti.G2ShortRoot.map_subtype_fixedSubgroup_frobenius_eq`: which points it fixes, and the
  identification of the fixed subgroup with the points over the Frobenius-fixed subring.

## References

* R. W. Carter, *Finite Groups of Lie Type: Conjugacy Classes and Complex Characters*, §1.17.
* R. W. Carter, *Simple Groups of Lie Type*, §§4.4 and 11.3.
* J. C. Jantzen, *Representations of Algebraic Groups*, II.1.
-/

public section

namespace TauCeti.G2ShortRoot

universe v

noncomputable section

variable (p k : ℕ) (A : Type v) [CommRing A] [ExpChar A p]

/-- **The `p ^ k`-power Frobenius endomorphism of the short-root type-`G₂` carrier**, the
functorial map on points induced by the iterated Frobenius endomorphism of the value ring.

For `p` prime, `0 < k` and `A` an algebraic closure of `ZMod p`, this is the `q`-power Frobenius
of the carrier's points for `q = p ^ k`. -/
def frobenius : points A →* points A :=
  pointsMap (iterateFrobenius A p k)

/-- The Frobenius endomorphism of the carrier acts by entrywise Frobenius.

This is not a `simp` lemma because `coe_frobenius_apply` is the canonical coefficient-level
normal form. -/
theorem coe_frobenius (g : points A) :
    (frobenius p k A g : _root_.Matrix.GeneralLinearGroup (Fin 7) A) =
      _root_.Matrix.GeneralLinearGroup.map (iterateFrobenius A p k) g := by
  rw [frobenius, coe_pointsMap]

/-- Entrywise, the Frobenius endomorphism raises each matrix coefficient to its `p ^ k`-th
power. -/
@[simp]
theorem coe_frobenius_apply (g : points A) (i j : Fin 7) :
    ((frobenius p k A g : _root_.Matrix.GeneralLinearGroup (Fin 7) A) :
        _root_.Matrix (Fin 7) (Fin 7) A) i j =
      ((g : _root_.Matrix.GeneralLinearGroup (Fin 7) A) :
        _root_.Matrix (Fin 7) (Fin 7) A) i j ^ p ^ k := by
  rw [coe_frobenius, _root_.Matrix.GeneralLinearGroup.map_apply, iterateFrobenius_def]

/-- **Frobenius raises the parameter of every numbered simple-root subgroup to its `p ^ k`-th
power**, on both the raising and the lowering generators. -/
@[simp]
theorem frobenius_rootSubgroupPoints (i : Fin 2 ⊕ Fin 2) (u : Multiplicative A) :
    frobenius p k A (rootSubgroupPoints i A u) =
      rootSubgroupPoints i A
        (Multiplicative.ofAdd (Multiplicative.toAdd u ^ p ^ k)) := by
  rw [frobenius, pointsMap_rootSubgroupPoints]
  exact Subtype.ext (by rw [iterateFrobenius_def])

/-- **Frobenius raises every coordinate of the pinned split weight torus to its `p ^ k`-th
power.** -/
@[simp]
theorem frobenius_weightTorusPoints (s : Fin 2 → Aˣ) :
    frobenius p k A (weightTorusPoints A s) = weightTorusPoints A (s ^ p ^ k) := by
  rw [frobenius, pointsMap_weightTorusPoints, map_iterateFrobenius_units_eq_pow]

/-- The zeroth Frobenius iterate is the identity on the carrier's point group. -/
@[simp]
theorem frobenius_zero : frobenius p 0 A = MonoidHom.id _ := by
  rw [frobenius, iterateFrobenius_zero, pointsMap_id]

/-- Frobenius iterates add under composition on the carrier's point group. -/
theorem frobenius_add (m : ℕ) :
    frobenius p (k + m) A = (frobenius p k A).comp (frobenius p m A) := by
  rw [frobenius, frobenius, frobenius, iterateFrobenius_add, pointsMap_comp]

/-- **Frobenius exponents multiply under taking powers**: the `m`-th power of the `p ^ k`-power
Frobenius of the carrier, in the endomorphism monoid of its points, is its `p ^ (k * m)`-power
Frobenius. -/
-- `Monoid.End` is definitionally a bundled `MonoidHom`; the `show` picks its composition monoid
-- structure before the power is elaborated.
theorem frobenius_pow (m : ℕ) :
    (show Monoid.End _ from frobenius p k A) ^ m = frobenius p (k * m) A := by
  induction m with
  | zero => rw [pow_zero, Nat.mul_zero, frobenius_zero]; rfl
  | succ m ih => rw [pow_succ, ih, Nat.mul_succ, frobenius_add p (k * m) A k]; rfl

/-- A carrier point is fixed by Frobenius exactly when all of its matrix entries lie in the
Frobenius-fixed subring. -/
@[simp]
theorem frobenius_eq_self_iff (g : points A) :
    frobenius p k A g = g ↔
      ∀ i j, ((g : _root_.Matrix.GeneralLinearGroup (Fin 7) A) :
        _root_.Matrix (Fin 7) (Fin 7) A) i j ∈ frobeniusFixedSubring A p k := by
  rw [← SetLike.coe_eq_coe, coe_frobenius,
    _root_.Matrix.GeneralLinearGroup.map_iterateFrobenius_eq_self_iff]

/-- **The Frobenius-fixed points of the short-root type-`G₂` carrier are its points over the
Frobenius-fixed subring.** No finiteness of either side is asserted. -/
theorem map_subtype_fixedSubgroup_frobenius_eq :
    (fixedSubgroup (frobenius p k A)).map (points A).subtype =
      (points ↥(frobeniusFixedSubring A p k)).map
        (_root_.Matrix.GeneralLinearGroup.map (frobeniusFixedSubring A p k).subtype) := by
  rw [TauCeti.map_subtype_fixedSubgroup_of_coe_eq (frobenius p k A) _
      (coe_frobenius p k A), points_def A, points_def ↥(frobeniusFixedSubring A p k),
    TauCeti.GeneralLinear.map_hopfIdealPointsSubgroup_frobeniusFixedSubring]

end

end TauCeti.G2ShortRoot
