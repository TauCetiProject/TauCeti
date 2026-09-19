/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Frobenius.GeneralLinear
import Mathlib.Algebra.Group.AddChar
public import TauCeti.Algebra.CharP.Frobenius.Basic
public import TauCeti.Algebra.Lie.D4.Tripled.PointsFunctor
import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Scheme.ToralClosure.Frobenius

/-!
# The Frobenius of the tripled type-D4 carrier

The tripled type-`D₄` carrier is the explicit Kostant toral closure over `ℤ` built from the
`24`-dimensional representation `V(ϖ₁) ⊕ V(ϖ₃) ⊕ V(ϖ₄)` and its admissible full-weight lattice.
Over a commutative ring `A` of exponential characteristic `p`, entrywise `p ^ k`-th powers
preserve its defining Hopf ideal and therefore give a group endomorphism of its `A`-valued points.

This file names that endomorphism `TauCeti.D4Tripled.frobenius` and records its characteristic
equations:

```text
F (g)ᵢⱼ = gᵢⱼ ^ (p ^ k),
F (xᵢ(u)) = xᵢ(u ^ (p ^ k)),
F (t(s)) = t(s ^ (p ^ k)).
```

The zeroth iterate is the identity, exponents add under composition and multiply under powers.
The fixed points are the points of the same carrier over the Frobenius-fixed subring. No
reductivity, finiteness, or simplicity statement is involved; no triality automorphism of the
carrier is constructed here, so no Steinberg map is formed, and the carrier is not identified
with the pinned simply connected group scheme of type `D₄`.

## Main declarations

* `TauCeti.D4Tripled.frobenius`: the `p ^ k`-power Frobenius on the carrier's points.
* `TauCeti.D4Tripled.frobenius_eq_pointsMap`: it is the map on points induced by the iterated
  Frobenius of the value ring.
* `TauCeti.D4Tripled.coe_frobenius` and `coe_frobenius_apply`: its matrix and entrywise actions.
* `TauCeti.D4Tripled.frobenius_rootSubgroupPoints`: its action on every numbered simple-root
  subgroup.
* `TauCeti.D4Tripled.frobenius_weightTorusPoints`: its action on the split weight torus.
* `TauCeti.D4Tripled.frobenius_zero`, `frobenius_add` and `frobenius_pow`: its iteration laws.
* `TauCeti.D4Tripled.frobenius_eq_self_iff` and
  `TauCeti.D4Tripled.map_subtype_fixedSubgroup_frobenius_eq`: which points it fixes, and the
  identification of the fixed subgroup with the points over the Frobenius-fixed subring.

## References

* R. W. Carter, *Finite Groups of Lie Type: Conjugacy Classes and Complex Characters*, §1.17.
* R. W. Carter, *Simple Groups of Lie Type*, §12.2, for the triality-twisted family.
* J. C. Jantzen, *Representations of Algebraic Groups*, II.1.
* The entrywise Frobenius of the points cut out by a Hopf ideal in a general linear group is
  `TauCeti.Algebra.AlgebraicGroup.Frobenius.GeneralLinear`, and its action on a weight-torus
  matrix is
  `TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Scheme.ToralClosure.Frobenius`.
-/

-- Adapted from `TauCeti.Algebra.Lie.E6.DoubledMinuscule.Frobenius`.

public section

namespace TauCeti.D4Tripled

universe v

noncomputable section

variable (p k : ℕ) (A : Type v) [CommRing A] [ExpChar A p]

/-- **The `p ^ k`-power Frobenius endomorphism of the tripled type-`D₄` carrier**, the functorial
map on points induced by the iterated Frobenius endomorphism of the value ring. -/
def frobenius : points A →* points A :=
  pointsMap (iterateFrobenius A p k)

/-- The Frobenius endomorphism of the tripled carrier is the map on points induced by the iterated
Frobenius of the value ring. This is its unfolding lemma, through which the naturality of a
symmetry of the carrier, such as triality, yields its commutation with the Frobenius. -/
theorem frobenius_eq_pointsMap : frobenius p k A = pointsMap (iterateFrobenius A p k) :=
  (rfl)

/-- The Frobenius endomorphism of the tripled carrier acts by entrywise Frobenius. -/
theorem coe_frobenius (g : points A) :
    (frobenius p k A g : _root_.Matrix.GeneralLinearGroup (Fin 24) A) =
      _root_.Matrix.GeneralLinearGroup.map (iterateFrobenius A p k) g := by
  rw [frobenius, coe_pointsMap]

/-- Entrywise, the Frobenius endomorphism raises each matrix coefficient to its `p ^ k`-th
power. -/
@[simp]
theorem coe_frobenius_apply (g : points A) (i j : Fin 24) :
    ((frobenius p k A g : _root_.Matrix.GeneralLinearGroup (Fin 24) A) :
        _root_.Matrix (Fin 24) (Fin 24) A) i j =
      ((g : _root_.Matrix.GeneralLinearGroup (Fin 24) A) :
        _root_.Matrix (Fin 24) (Fin 24) A) i j ^ p ^ k := by
  rw [coe_frobenius, _root_.Matrix.GeneralLinearGroup.map_apply, iterateFrobenius_def]

/-- **Frobenius raises the parameter of every numbered tripled type-`D₄` simple-root subgroup to
its `p ^ k`-th power.** -/
@[simp]
theorem frobenius_rootSubgroupPoints (i : Fin 4 ⊕ Fin 4) (u : Multiplicative A) :
    frobenius p k A (rootSubgroupPoints i A u) =
      rootSubgroupPoints i A
        (Multiplicative.ofAdd (Multiplicative.toAdd u ^ p ^ k)) := by
  rw [frobenius, pointsMap_rootSubgroupPoints]
  exact Subtype.ext (by rw [iterateFrobenius_def])

/-- **Frobenius raises every coordinate of the pinned split weight torus to its `p ^ k`-th
power.** -/
@[simp]
theorem frobenius_weightTorusPoints (s : Fin 4 → Aˣ) :
    frobenius p k A (weightTorusPoints A s) = weightTorusPoints A (s ^ p ^ k) :=
  Subtype.ext (by
    rw [coe_frobenius, coe_weightTorusPoints,
      UniversalEnvelopingAlgebra.map_iterateFrobenius_kostantTorusMatrix, coe_weightTorusPoints])

/-- The zeroth Frobenius iterate is the identity on the tripled carrier's point group. -/
@[simp]
theorem frobenius_zero : frobenius p 0 A = MonoidHom.id _ := by
  rw [frobenius, iterateFrobenius_zero, pointsMap_id]

/-- Frobenius iterates add under composition on the tripled carrier's point group. -/
theorem frobenius_add (m : ℕ) :
    frobenius p (k + m) A = (frobenius p k A).comp (frobenius p m A) := by
  rw [frobenius, frobenius, frobenius, iterateFrobenius_add, pointsMap_comp]

/-- **Frobenius exponents multiply under taking powers**: the `m`-th power of the `p ^ k`-power
Frobenius of the tripled carrier, in the endomorphism monoid of its points, is its
`p ^ (k * m)`-power Frobenius. -/
-- `Monoid.End` is definitionally a bundled `MonoidHom`; the `show` picks its composition monoid
-- structure before the power is elaborated.
theorem frobenius_pow (m : ℕ) :
    (show Monoid.End _ from frobenius p k A) ^ m = frobenius p (k * m) A := by
  let ψ : AddChar ℕ (Monoid.End (points A)) :=
    { toFun := fun j => frobenius p j A
      map_zero_eq_one' := frobenius_zero p A
      map_add_eq_mul' := fun a b => frobenius_add p a A b }
  have hpow := AddChar.map_nsmul_eq_pow ψ m k
  -- Expose the function supplied to `AddChar.mk` and the natural-number scalar action.
  change frobenius p (m * k) A =
    (show Monoid.End _ from frobenius p k A) ^ m at hpow
  rw [Nat.mul_comm] at hpow
  exact hpow.symm

/-- A tripled carrier point is fixed by Frobenius exactly when all of its matrix entries lie in
the Frobenius-fixed subring. -/
@[simp]
theorem frobenius_eq_self_iff (g : points A) :
    frobenius p k A g = g ↔
      ∀ i j, ((g : _root_.Matrix.GeneralLinearGroup (Fin 24) A) :
        _root_.Matrix (Fin 24) (Fin 24) A) i j ∈ frobeniusFixedSubring A p k := by
  rw [← SetLike.coe_eq_coe, coe_frobenius,
    _root_.Matrix.GeneralLinearGroup.map_iterateFrobenius_eq_self_iff]

/-- **The Frobenius-fixed points of the tripled carrier are its points over the Frobenius-fixed
subring.** -/
theorem map_subtype_fixedSubgroup_frobenius_eq :
    (fixedSubgroup (frobenius p k A)).map (points A).subtype =
      (points ↥(frobeniusFixedSubring A p k)).map
        (_root_.Matrix.GeneralLinearGroup.map (frobeniusFixedSubring A p k).subtype) := by
  rw [TauCeti.map_subtype_fixedSubgroup_of_coe_eq (frobenius p k A) _
      (coe_frobenius p k A), points_def A, points_def ↥(frobeniusFixedSubring A p k),
    TauCeti.GeneralLinear.map_hopfIdealPointsSubgroup_frobeniusFixedSubring]

end

end TauCeti.D4Tripled
