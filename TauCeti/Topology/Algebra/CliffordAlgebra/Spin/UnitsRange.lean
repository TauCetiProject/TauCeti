/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.CliffordAlgebra.Spin.Basic
import TauCeti.Topology.Algebra.ContinuousMonoidHom.Basic
import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.Basic
import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.Kernel

/-!
# The Spin group in Clifford units and its range-carrier projection

For any quadratic form `Q` over a topological commutative ring `R`, the canonical inclusion
`spinGroup.toUnits` into the units of `CliffordAlgebra Q` is a topological embedding without any
compactness or Hausdorff assumption: its composition with `Units.val` is the subtype inclusion of
`spinGroup Q`, while its inverse field is Clifford conjugation `star`, which is continuous for the
Clifford module topology. Consequently `spinGroup Q` is topologically isomorphic to its range
`MonoidHom.range (spinGroup.toUnits (Q := Q))`.

On a finite coordinate space `n → R` with its module topology, continuous Clifford multiplication,
and `2` invertible, transporting `spinToSpecialOrthogonal Q` across this equivalence and
`QuadraticMap.specialOrthogonalContinuousMulEquivRange` produces a continuous homomorphism
`CliffordAlgebra.spinToSpecialOrthogonalUnitsRange` between the Spin range in `(CliffordAlgebra Q)ˣ`
and the special-orthogonal range in `GL(n, R)`. Over a topological field in which `2` is
invertible, its kernel on any nondegenerate form consists of the central units `1` and `-1` (and
reduces to `{1}` when `n` is empty).

## Main definitions and results

* `CliffordAlgebra.isEmbedding_spinGroup_toUnits` and
  `CliffordAlgebra.spinGroupContinuousMulEquivUnitsRange`: `spinGroup.toUnits` is a topological
  embedding and identifies `spinGroup Q` with its range in `(CliffordAlgebra Q)ˣ`.
* `CliffordAlgebra.spinToSpecialOrthogonalUnitsRange`: the continuous Spin projection between the
  unit-group range carriers of `Spin(Q)` and `SO(Q)` in coordinates.
* `CliffordAlgebra.spinToSpecialOrthogonalUnitsRange_eq_one_iff`: kernel characterization for a
  nondegenerate coordinate form over a topological field of characteristic not `2`.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, Section 2.
-/

public section

namespace CliffordAlgebra

noncomputable section

universe u v

section UnitsEmbedding

variable {R : Type u} [CommRing R] [TopologicalSpace R]
  {V : Type v} [AddCommGroup V] [Module R V]

/-- The canonical inclusion of a Spin group into the units of its Clifford algebra is a topological
embedding for the canonical Clifford module topology, without compactness or separation
hypotheses. -/
theorem isEmbedding_spinGroup_toUnits (Q : QuadraticForm R V) :
    Topology.IsEmbedding (spinGroup.toUnits (Q := Q)) := by
  have hcont : Continuous (spinGroup.toUnits (Q := Q)) :=
    Units.continuous_iff.mpr ⟨continuous_subtype_val, continuous_subtype_val.star⟩
  exact Topology.IsEmbedding.of_comp hcont Units.continuous_val Topology.IsEmbedding.subtypeVal

private def spinGroupToUnitsContinuousMonoidHom (Q : QuadraticForm R V) :
    spinGroup Q →ₜ* (CliffordAlgebra Q)ˣ :=
  ⟨spinGroup.toUnits, (isEmbedding_spinGroup_toUnits Q).continuous⟩

/-- A Spin group is topologically isomorphic to its range in the units of its Clifford algebra. -/
def spinGroupContinuousMulEquivUnitsRange (Q : QuadraticForm R V) :
    spinGroup Q ≃ₜ* MonoidHom.range (spinGroup.toUnits (Q := Q)) :=
  (spinGroupToUnitsContinuousMonoidHom Q).equivRangeOfIsEmbedding
    (isEmbedding_spinGroup_toUnits Q)

/-- The topological equivalence with the unit range sends a Spin element to its canonical unit. -/
@[simp]
theorem spinGroupContinuousMulEquivUnitsRange_apply
    (Q : QuadraticForm R V) (x : spinGroup Q) :
    spinGroupContinuousMulEquivUnitsRange Q x = ⟨spinGroup.toUnits x, ⟨x, rfl⟩⟩ :=
  (spinGroupToUnitsContinuousMonoidHom Q).equivRangeOfIsEmbedding_apply
    (isEmbedding_spinGroup_toUnits Q) x

/-- The inverse topological equivalence sends a canonical unit representative back to its Spin
element. -/
@[simp]
theorem spinGroupContinuousMulEquivUnitsRange_symm_apply
    (Q : QuadraticForm R V) (x : spinGroup Q) :
    (spinGroupContinuousMulEquivUnitsRange Q).symm ⟨spinGroup.toUnits x, ⟨x, rfl⟩⟩ = x := by
  rw [← spinGroupContinuousMulEquivUnitsRange_apply]
  exact (spinGroupContinuousMulEquivUnitsRange Q).symm_apply_apply x

/-- Reconstructing a Spin element from the unit range preserves its underlying Clifford-algebra
value. -/
@[simp]
theorem coe_spinGroupContinuousMulEquivUnitsRange_symm_apply
    (Q : QuadraticForm R V) (u : MonoidHom.range (spinGroup.toUnits (Q := Q))) :
    (((spinGroupContinuousMulEquivUnitsRange Q).symm u : spinGroup Q) : CliffordAlgebra Q) =
      ((u : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) := by
  obtain ⟨_, x, rfl⟩ := u
  rw [spinGroupContinuousMulEquivUnitsRange_symm_apply, spinGroup.val_toUnits_apply]

end UnitsEmbedding

section CoordinateProjection

variable {R : Type u} [CommRing R] [TopologicalSpace R] [Invertible (2 : R)]
  {n : Type v} [Fintype n] [DecidableEq n]

/-- The Spin projection on a finite coordinate space, transported to the unit-group range carriers
of `Spin(Q)` in `(CliffordAlgebra Q)ˣ` and `SO(Q)` in `GL(n, R)`. -/
def spinToSpecialOrthogonalUnitsRange (Q : QuadraticForm R (n → R))
    [IsModuleTopology R (n → R)] [ContinuousMul (CliffordAlgebra Q)] :
    MonoidHom.range (spinGroup.toUnits (Q := Q)) →ₜ*
      MonoidHom.range Q.specialOrthogonalToGeneralLinear where
  toMonoidHom :=
    Q.specialOrthogonalToGeneralLinear.rangeRestrict.comp
      ((spinToSpecialOrthogonal Q).comp
        (spinGroupContinuousMulEquivUnitsRange Q).symm.toMonoidHom)
  continuous_toFun := by
    refine (Q.specialOrthogonalContinuousMulEquivRange.continuous.comp
      ((continuous_spinToSpecialOrthogonal_pi Q).comp
        (spinGroupContinuousMulEquivUnitsRange Q).symm.continuous)).congr fun x ↦ ?_
    exact Q.specialOrthogonalContinuousMulEquivRange_apply _

/-- Evaluating the range-carrier Spin projection applies `spinToSpecialOrthogonal Q` to the
corresponding Spin element and embeds the result in `GL(n, R)`. -/
@[simp]
theorem spinToSpecialOrthogonalUnitsRange_apply (Q : QuadraticForm R (n → R))
    [IsModuleTopology R (n → R)] [ContinuousMul (CliffordAlgebra Q)]
    (x : MonoidHom.range (spinGroup.toUnits (Q := Q))) :
    spinToSpecialOrthogonalUnitsRange Q x =
      Q.specialOrthogonalContinuousMulEquivRange
        (spinToSpecialOrthogonal Q ((spinGroupContinuousMulEquivUnitsRange Q).symm x)) :=
  (Q.specialOrthogonalContinuousMulEquivRange_apply _).symm

/-- On the canonical unit representative of `x : spinGroup Q`, the range-carrier projection agrees
with `spinToSpecialOrthogonal Q` followed by the `GL(n, R)` range equivalence. -/
theorem spinToSpecialOrthogonalUnitsRange_apply_toUnits (Q : QuadraticForm R (n → R))
    [IsModuleTopology R (n → R)] [ContinuousMul (CliffordAlgebra Q)] (x : spinGroup Q) :
    spinToSpecialOrthogonalUnitsRange Q ⟨spinGroup.toUnits x, ⟨x, rfl⟩⟩ =
      Q.specialOrthogonalContinuousMulEquivRange (spinToSpecialOrthogonal Q x) := by
  rw [spinToSpecialOrthogonalUnitsRange_apply, spinGroupContinuousMulEquivUnitsRange_symm_apply]

end CoordinateProjection

section Kernel

variable {K : Type u} [Field K] [TopologicalSpace K] [Invertible (2 : K)]
  {n : Type v} [Fintype n] [DecidableEq n]

/-- For a nondegenerate quadratic form on `n → K` over a topological field in which `2` is
invertible, an element of the Spin unit range maps to `1` in the `SO(Q)` matrix-unit range if and
only if it is `1` or `-1` in `(CliffordAlgebra Q)ˣ`. -/
theorem spinToSpecialOrthogonalUnitsRange_eq_one_iff (Q : QuadraticForm K (n → K))
    [IsModuleTopology K (n → K)] [ContinuousMul (CliffordAlgebra Q)]
    (hQ : Q.Nondegenerate) (x : MonoidHom.range (spinGroup.toUnits (Q := Q))) :
    spinToSpecialOrthogonalUnitsRange Q x = 1 ↔
      (x : (CliffordAlgebra Q)ˣ) = 1 ∨ (x : (CliffordAlgebra Q)ˣ) = -1 := by
  rcases subsingleton_or_nontrivial (n → K) with _ | _
  · have : Subsingleton (MonoidHom.range (spinGroup.toUnits (Q := Q))) :=
      (Set.subsingleton_coe _).mpr (MonoidHom.subsingleton_coe_range _)
    obtain rfl : x = 1 := Subsingleton.elim _ _
    simp
  · obtain ⟨_, y, rfl⟩ := x
    rw [spinToSpecialOrthogonalUnitsRange_apply_toUnits,
      map_eq_one_iff _ Q.specialOrthogonalContinuousMulEquivRange.injective,
      ← MonoidHom.mem_ker, mem_ker_spinToSpecialOrthogonal_iff Q hQ]
    simp only [Subtype.ext_iff (a1 := y), Units.ext_iff, spinGroup.val_toUnits_apply,
      spinGroup.coe_negOne, OneMemClass.coe_one, Units.val_one, Units.val_neg]

end Kernel

end

end CliffordAlgebra
