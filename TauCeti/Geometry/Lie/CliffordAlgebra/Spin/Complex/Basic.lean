/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.BaseChange
public import TauCeti.Geometry.Lie.Subgroup.Differential
public import TauCeti.Topology.Algebra.CliffordAlgebra.Spin.LieAlgebra

/-!
# The smooth complex Spin carrier and its quadratic Lie coordinates

For a nondegenerate quadratic form on a complex coordinate space, the range of the native Spin
group in Clifford units is a closed real Lie subgroup. It carries its subspace
topology in the units. Its Lie algebra is the underlying real Lie algebra of the complex quadratic
Clifford elements. These coordinates allow Clifford actions to be compared with their real
differentials while retaining the complex scalar structure of the algebraic action.

The construction follows the compact real carrier in
`TauCeti.Geometry.Lie.CliffordAlgebra.Spin.Projection`, using the complex exponential-line
characterization in `TauCeti.Topology.Algebra.CliffordAlgebra.Spin.LieAlgebra`.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, Sections 2 and 5.
-/

public section

open Manifold
open scoped ContDiff Manifold

noncomputable section

namespace TauCeti.CliffordAlgebra

open _root_.CliffordAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing

variable {n : ℕ} {Q : QuadraticForm ℂ (Fin n → ℂ)}

local notation "SpinUnitsRange" => MonoidHom.range (spinGroup.toUnits (Q := Q))

local notation "SpinLieModel" =>
  LieSubalgebra.toSubmodule (TauCeti.Lie.lieSubalgebraOfSubgroup
    (I := 𝓘(ℝ, CliffordAlgebra Q)) SpinUnitsRange)

/-- The closed-subgroup smooth structure on the complex Spin range, modeled on its ambient
one-parameter-subgroup Lie algebra. It uses the existing subspace topology. -/
def complexSpinEmbeddedLieSubgroupData (hQ : Q.Nondegenerate) :
    TauCeti.Lie.EmbeddedLieSubgroupData 𝓘(ℝ, CliffordAlgebra Q) SpinUnitsRange SpinLieModel :=
  Classical.choice (by
    apply TauCeti.Lie.nonempty_embeddedLieSubgroupData_lieSubalgebraOfSubgroup_of_isClosed
    simpa only [MonoidHom.coe_range] using isClosed_range_spinGroup_toUnits Q hQ)

/-- The canonical model of the complex Spin range is finite-dimensional over the reals. -/
instance complexSpinLieModelFiniteDimensional : FiniteDimensional ℝ SpinLieModel := by
  let _ : FiniteDimensional ℝ
      (LeftInvariantDerivation 𝓘(ℝ, CliffordAlgebra Q) (CliffordAlgebra Q)ˣ) :=
    finiteDimensional_leftInvariantDerivation BoundarylessManifold.isInteriorPoint
  exact FiniteDimensional.finiteDimensional_submodule _

/-- The charted-space structure on the complex Spin range selected by Cartan's theorem. -/
instance complexSpinUnitsRangeChartedSpace [Fact Q.Nondegenerate] :
    ChartedSpace SpinLieModel SpinUnitsRange :=
  (complexSpinEmbeddedLieSubgroupData (Fact.out : Q.Nondegenerate)).chartedSpace

/-- The real Lie-group structure on the complex Spin range selected by Cartan's theorem. -/
instance complexSpinUnitsRangeLieGroup [Fact Q.Nondegenerate] :
    LieGroup 𝓘(ℝ, SpinLieModel) ∞ SpinUnitsRange :=
  (complexSpinEmbeddedLieSubgroupData (Fact.out : Q.Nondegenerate)).lieGroup

private def complexSpinAmbientCoordinateLieEquiv (hQ : Q.Nondegenerate) :
    TauCeti.Lie.lieSubalgebraOfSubgroup (I := 𝓘(ℝ, CliffordAlgebra Q)) SpinUnitsRange ≃ₗ⁅ℝ⁆
      RestrictScalars ℝ ℂ (quadraticLieSubalgebra Q) :=
  { LinearEquiv.ofSubmodules
    (TauCeti.Lie.unitsLieAlgebraLieEquiv (R := CliffordAlgebra Q)).toLinearEquiv
    _ ((quadraticLieSubalgebra Q).toSubmodule.restrictScalars ℝ) (by
      ext x
      simp only [Submodule.mem_map_equiv, Submodule.restrictScalars_mem]
      exact
unitsLieAlgebraLieEquiv_symm_mem_lieSubalgebraOfSubgroup_iff_mem_quadraticLieSubalgebra_complex
          Q hQ x) with
    map_lie' := fun {x y} ↦ Subtype.ext
      ((TauCeti.Lie.unitsLieAlgebraLieEquiv (R := CliffordAlgebra Q)).map_lie x y) }

private theorem coe_complexSpinAmbientCoordinateLieEquiv_apply (hQ : Q.Nondegenerate)
    (x : TauCeti.Lie.lieSubalgebraOfSubgroup (I := 𝓘(ℝ, CliffordAlgebra Q)) SpinUnitsRange) :
    (RestrictScalars.addEquiv ℝ ℂ (quadraticLieSubalgebra Q)
      (complexSpinAmbientCoordinateLieEquiv hQ x) : CliffordAlgebra Q) =
      TauCeti.Lie.unitsLieAlgebraLieEquiv x := by
  -- Both the restriction of the equivalence and the scalar-restriction accessor retain
  -- the ambient units-coordinate function.
  unfold complexSpinAmbientCoordinateLieEquiv
  rfl

/-- The real Lie algebra of complex Spin in the complex quadratic Clifford coordinates.
`RestrictScalars` keeps the complex quadratic carrier and regards it as a real Lie algebra. -/
def complexSpinLieEquivQuadratic [Fact Q.Nondegenerate] :
    LeftInvariantDerivation 𝓘(ℝ, SpinLieModel) SpinUnitsRange ≃ₗ⁅ℝ⁆
      RestrictScalars ℝ ℂ (quadraticLieSubalgebra Q) :=
  (complexSpinEmbeddedLieSubgroupData (Fact.out : Q.Nondegenerate))
    |>.lieEquivLieSubalgebraOfSubgroup.trans
      (complexSpinAmbientCoordinateLieEquiv (Fact.out : Q.Nondegenerate))

/-- Quadratic coordinates are the ambient units coordinates of the differential of inclusion. -/
@[simp↓ high]
theorem unitsLieAlgebraLieEquiv_lieMapSubtypeVal_eq_coe_complexSpinLieEquivQuadratic
    [Fact Q.Nondegenerate]
    (X : LeftInvariantDerivation 𝓘(ℝ, SpinLieModel) SpinUnitsRange) :
      TauCeti.Lie.unitsLieAlgebraLieEquiv
          ((complexSpinEmbeddedLieSubgroupData (Fact.out : Q.Nondegenerate)).lieMapSubtypeVal X) =
        ((RestrictScalars.addEquiv ℝ ℂ (quadraticLieSubalgebra Q)
          (complexSpinLieEquivQuadratic (Q := Q) X)) : CliffordAlgebra Q) := by
  have h := congrArg
    (fun Y : LeftInvariantDerivation 𝓘(ℝ, CliffordAlgebra Q) (CliffordAlgebra Q)ˣ ↦
      TauCeti.Lie.unitsLieAlgebraLieEquiv Y)
    ((complexSpinEmbeddedLieSubgroupData (Fact.out : Q.Nondegenerate))
      |>.lieEquivLieSubalgebraOfSubgroup_apply X)
  simpa only [complexSpinLieEquivQuadratic, LieEquiv.trans_apply,
    coe_complexSpinAmbientCoordinateLieEquiv_apply] using h.symm

end TauCeti.CliffordAlgebra
