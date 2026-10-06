/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.AutomaticSmoothness
public import TauCeti.Geometry.Lie.Subgroup.Differential
public import TauCeti.Geometry.Lie.Subgroup.SpecialOrthogonal
public import TauCeti.Topology.Algebra.CliffordAlgebra.Spin.LieAlgebra
public import TauCeti.Topology.Algebra.CliffordAlgebra.Spin.Real.Projection

/-!
# The Lie map of the real Spin projection

The compact real Spin group and its special-orthogonal target are realized as closed subgroups of
the units of a Clifford algebra and a matrix algebra. This file equips those two range carriers
with the Lie-group structures supplied by the closed-subgroup theorem and applies the Lie functor
to the existing continuous projection between them.

The abstract Lie algebras of the two carriers are then put in concrete coordinates. On the Spin
side, the canonical units coordinates identify the subgroup Lie algebra with the quadratic
Clifford elements. On the special-orthogonal side, they identify it with the skew-symmetric
matrices. Transporting the differential of the projection through these equivalences produces a
Lie homomorphism from quadratic Clifford elements to skew-symmetric matrices.

## Main definitions

* `TauCeti.CliffordAlgebra.realCliffordSpinEmbeddedLieSubgroupData` and
  `realCliffordSpecialOrthogonalEmbeddedLieSubgroupData` select the closed-subgroup Lie structures.
* `TauCeti.CliffordAlgebra.realCliffordSpinLieEquivQuadratic` identifies the source Lie algebra
  with the quadratic Lie subalgebra.
* `TauCeti.CliffordAlgebra.realCliffordSpecialOrthogonalLieEquivSo` identifies the target Lie
  algebra with real skew-symmetric matrices.
* `TauCeti.CliffordAlgebra.realCliffordSpinToSpecialOrthogonalSmoothRange` is the smooth carrier
  projection, and `realCliffordSpinToSpecialOrthogonalRangeLieMap` is its differential.
* `TauCeti.CliffordAlgebra.realCliffordSpinToSpecialOrthogonalCoordinateLieHom` is that
  differential in quadratic-Clifford and skew-matrix coordinates.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, Section 2.
* A. Kirillov Jr., *An Introduction to Lie Groups and Lie Algebras* (2008), Chapter 3.
-/

public section

open Manifold
open scoped ContDiff Manifold Matrix.Norms.Operator

noncomputable section

namespace TauCeti.CliffordAlgebra

open _root_.CliffordAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing

attribute [local instance] Matrix.linftyOpTopologicalSpace

local notation "SpinUnitsRange(" n ")" =>
  MonoidHom.range (spinGroup.toUnits (Q := realCliffordForm n 0))

local notation "SpecialOrthogonalUnitsRange(" n ")" =>
  MonoidHom.range (QuadraticMap.specialOrthogonalToGeneralLinear
    (realCliffordForm n 0 : QuadraticForm ℝ (Fin n → ℝ)))

local notation "SpinLieModel(" n ")" =>
  LieSubalgebra.toSubmodule (TauCeti.Lie.lieSubalgebraOfSubgroup
    (I := 𝓘(ℝ, CliffordAlgebra (realCliffordForm n 0))) (SpinUnitsRange(n)))

local notation "SpecialOrthogonalLieModel(" n ")" =>
  LieSubalgebra.toSubmodule (TauCeti.Lie.lieSubalgebraOfSubgroup
    (I := 𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ))
    (SpecialOrthogonalUnitsRange(n)))

/-- The closed-subgroup Lie structure on the range of the compact real Spin group in the
Clifford units. Its model is the ambient one-parameter-subgroup Lie algebra of that range. -/
noncomputable def realCliffordSpinEmbeddedLieSubgroupData (n : ℕ) :
    TauCeti.Lie.EmbeddedLieSubgroupData
      𝓘(ℝ, CliffordAlgebra (realCliffordForm n 0))
      (SpinUnitsRange(n)) (SpinLieModel(n)) :=
  Classical.choice (by
    apply TauCeti.Lie.nonempty_embeddedLieSubgroupData_lieSubalgebraOfSubgroup_of_isClosed
    simpa only [MonoidHom.coe_range] using
      isClosed_range_spinGroup_toUnits (realCliffordForm n 0)
        (nondegenerate_realCliffordForm n 0))

/-- The closed-subgroup Lie structure on the range of the positive-definite real special
orthogonal group in the matrix units. Its model is the ambient one-parameter-subgroup Lie algebra
of that range. -/
noncomputable def realCliffordSpecialOrthogonalEmbeddedLieSubgroupData (n : ℕ) :
    TauCeti.Lie.EmbeddedLieSubgroupData
      𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ)
      (SpecialOrthogonalUnitsRange(n)) (SpecialOrthogonalLieModel(n)) :=
  Classical.choice (by
    apply TauCeti.Lie.nonempty_embeddedLieSubgroupData_lieSubalgebraOfSubgroup_of_isClosed
    rw [MonoidHom.coe_range]
    exact QuadraticMap.isClosed_range_specialOrthogonalToGeneralLinear_realCliffordForm n)

private noncomputable def spinAmbientCoordinateLieEquiv (n : ℕ) :
    TauCeti.Lie.lieSubalgebraOfSubgroup
        (I := 𝓘(ℝ, CliffordAlgebra (realCliffordForm n 0))) (SpinUnitsRange(n)) ≃ₗ⁅ℝ⁆
      quadraticLieSubalgebra (realCliffordForm n 0) := by
  apply LieEquiv.ofSubalgebras _ _
    (TauCeti.Lie.unitsLieAlgebraLieEquiv
      (R := CliffordAlgebra (realCliffordForm n 0)))
  ext x
  simp only [Submodule.mem_map_equiv, LieSubalgebra.mem_map_submodule]
  exact
    unitsLieAlgebraLieEquiv_symm_mem_lieSubalgebraOfSubgroup_iff_mem_quadraticLieSubalgebra
      n 0 x

private theorem coe_spinAmbientCoordinateLieEquiv_apply
    (n : ℕ) (x : TauCeti.Lie.lieSubalgebraOfSubgroup
      (I := 𝓘(ℝ, CliffordAlgebra (realCliffordForm n 0))) (SpinUnitsRange(n))) :
    ((spinAmbientCoordinateLieEquiv n x : quadraticLieSubalgebra (realCliffordForm n 0)) :
      CliffordAlgebra (realCliffordForm n 0)) =
      TauCeti.Lie.unitsLieAlgebraLieEquiv x := by
  unfold spinAmbientCoordinateLieEquiv
  rfl

private noncomputable def specialOrthogonalAmbientCoordinateLieEquiv (n : ℕ) :
    TauCeti.Lie.lieSubalgebraOfSubgroup
        (I := 𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ)) (SpecialOrthogonalUnitsRange(n)) ≃ₗ⁅ℝ⁆
      LieAlgebra.Orthogonal.so (Fin n) ℝ := by
  apply LieEquiv.ofSubalgebras _ _
    (TauCeti.Lie.unitsLieAlgebraLieEquiv (R := Matrix (Fin n) (Fin n) ℝ))
  ext x
  simp only [Submodule.mem_map_equiv, LieSubalgebra.mem_map_submodule]
  exact
    TauCeti.Lie.unitsLieAlgebraLieEquiv_symm_mem_realCliffordForm_lieSubalgebra_iff_mem_so n x

private theorem coe_specialOrthogonalAmbientCoordinateLieEquiv_apply
    (n : ℕ) (x : TauCeti.Lie.lieSubalgebraOfSubgroup
      (I := 𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ)) (SpecialOrthogonalUnitsRange(n))) :
    ((specialOrthogonalAmbientCoordinateLieEquiv n x :
        LieAlgebra.Orthogonal.so (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ) =
      TauCeti.Lie.unitsLieAlgebraLieEquiv x := by
  unfold specialOrthogonalAmbientCoordinateLieEquiv
  rfl

/-- The closed real Spin carrier's canonical model is finite-dimensional. -/
noncomputable instance realCliffordSpinLieModelFiniteDimensional (n : ℕ) :
    FiniteDimensional ℝ (SpinLieModel(n)) := by
  let _ : FiniteDimensional ℝ
      (LeftInvariantDerivation 𝓘(ℝ, CliffordAlgebra (realCliffordForm n 0))
        (CliffordAlgebra (realCliffordForm n 0))ˣ) :=
    finiteDimensional_leftInvariantDerivation
      (ContMDiffMul.isInteriorPoint
        (I := 𝓘(ℝ, CliffordAlgebra (realCliffordForm n 0))) (n := ∞) (by simp) 1)
  exact FiniteDimensional.finiteDimensional_submodule _

/-- The closed real special-orthogonal carrier's canonical model is finite-dimensional. -/
noncomputable instance realCliffordSpecialOrthogonalLieModelFiniteDimensional (n : ℕ) :
    FiniteDimensional ℝ (SpecialOrthogonalLieModel(n)) := by
  let _ : FiniteDimensional ℝ
      (LeftInvariantDerivation 𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ)
        (Matrix (Fin n) (Fin n) ℝ)ˣ) :=
    finiteDimensional_leftInvariantDerivation
      (ContMDiffMul.isInteriorPoint
        (I := 𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ)) (n := ∞) (by simp) 1)
  exact FiniteDimensional.finiteDimensional_submodule _

/-- The charted-space structure on the closed real Spin carrier selected by Cartan's theorem. -/
noncomputable instance realCliffordSpinUnitsRangeChartedSpace (n : ℕ) :
    ChartedSpace (SpinLieModel(n)) (SpinUnitsRange(n)) :=
  (realCliffordSpinEmbeddedLieSubgroupData n).chartedSpace

/-- The Lie-group structure on the closed real Spin carrier selected by Cartan's theorem. -/
noncomputable instance realCliffordSpinUnitsRangeLieGroup (n : ℕ) :
    LieGroup 𝓘(ℝ, SpinLieModel(n)) ∞ (SpinUnitsRange(n)) :=
  (realCliffordSpinEmbeddedLieSubgroupData n).lieGroup

/-- The charted-space structure on the closed real special-orthogonal carrier selected by
Cartan's theorem. -/
noncomputable instance realCliffordSpecialOrthogonalUnitsRangeChartedSpace (n : ℕ) :
    ChartedSpace (SpecialOrthogonalLieModel(n)) (SpecialOrthogonalUnitsRange(n)) :=
  (realCliffordSpecialOrthogonalEmbeddedLieSubgroupData n).chartedSpace

/-- The Lie-group structure on the closed real special-orthogonal carrier selected by Cartan's
theorem. -/
noncomputable instance realCliffordSpecialOrthogonalUnitsRangeLieGroup (n : ℕ) :
    LieGroup 𝓘(ℝ, SpecialOrthogonalLieModel(n)) ∞ (SpecialOrthogonalUnitsRange(n)) :=
  (realCliffordSpecialOrthogonalEmbeddedLieSubgroupData n).lieGroup

/-- The Lie algebra of the compact real Spin carrier, in quadratic Clifford coordinates. -/
noncomputable def realCliffordSpinLieEquivQuadratic (n : ℕ) :
    LeftInvariantDerivation 𝓘(ℝ, SpinLieModel(n)) (SpinUnitsRange(n)) ≃ₗ⁅ℝ⁆
      quadraticLieSubalgebra (realCliffordForm n 0) :=
  (realCliffordSpinEmbeddedLieSubgroupData n).lieEquivLieSubalgebraOfSubgroup.trans
    (spinAmbientCoordinateLieEquiv n)

/-- In ambient Clifford coordinates, the source Lie equivalence is the units Lie equivalence
applied after differentiating the subgroup inclusion. -/
theorem coe_realCliffordSpinLieEquivQuadratic_apply
    (n : ℕ) (X : LeftInvariantDerivation 𝓘(ℝ, SpinLieModel(n)) (SpinUnitsRange(n))) :
    ((realCliffordSpinLieEquivQuadratic n X :
        quadraticLieSubalgebra (realCliffordForm n 0)) :
      CliffordAlgebra (realCliffordForm n 0)) =
      TauCeti.Lie.unitsLieAlgebraLieEquiv
        ((realCliffordSpinEmbeddedLieSubgroupData n).lieMapSubtypeVal X) := by
  have h := congrArg
    (fun Y : LeftInvariantDerivation
      𝓘(ℝ, CliffordAlgebra (realCliffordForm n 0))
      (CliffordAlgebra (realCliffordForm n 0))ˣ ↦
        TauCeti.Lie.unitsLieAlgebraLieEquiv Y)
    ((realCliffordSpinEmbeddedLieSubgroupData n)
      |>.lieEquivLieSubalgebraOfSubgroup_apply X)
  simp only [realCliffordSpinLieEquivQuadratic, LieEquiv.trans_apply,
    coe_spinAmbientCoordinateLieEquiv_apply]
  exact h

/-- The units coordinates of the differentiated Spin-carrier inclusion normalize to the concrete
quadratic coordinates. -/
@[simp↓ high]
theorem unitsLieAlgebraLieEquiv_lieMapSubtypeVal_eq_coe_realCliffordSpinLieEquivQuadratic
    (n : ℕ) (X : LeftInvariantDerivation 𝓘(ℝ, SpinLieModel(n)) (SpinUnitsRange(n))) :
    TauCeti.Lie.unitsLieAlgebraLieEquiv
        ((realCliffordSpinEmbeddedLieSubgroupData n).lieMapSubtypeVal X) =
      ((realCliffordSpinLieEquivQuadratic n X :
          quadraticLieSubalgebra (realCliffordForm n 0)) :
        CliffordAlgebra (realCliffordForm n 0)) :=
  (coe_realCliffordSpinLieEquivQuadratic_apply n X).symm

/-- The Lie algebra of the positive-definite real special-orthogonal carrier, in
skew-symmetric-matrix coordinates. -/
noncomputable def realCliffordSpecialOrthogonalLieEquivSo (n : ℕ) :
    LeftInvariantDerivation 𝓘(ℝ, SpecialOrthogonalLieModel(n))
        (SpecialOrthogonalUnitsRange(n)) ≃ₗ⁅ℝ⁆
      LieAlgebra.Orthogonal.so (Fin n) ℝ :=
  (realCliffordSpecialOrthogonalEmbeddedLieSubgroupData n)
    |>.lieEquivLieSubalgebraOfSubgroup.trans (specialOrthogonalAmbientCoordinateLieEquiv n)

/-- In ambient matrix coordinates, the target Lie equivalence is the units Lie equivalence
applied after differentiating the subgroup inclusion. -/
theorem coe_realCliffordSpecialOrthogonalLieEquivSo_apply
    (n : ℕ) (X : LeftInvariantDerivation 𝓘(ℝ, SpecialOrthogonalLieModel(n))
      (SpecialOrthogonalUnitsRange(n))) :
    ((realCliffordSpecialOrthogonalLieEquivSo n X :
        LieAlgebra.Orthogonal.so (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ) =
      TauCeti.Lie.unitsLieAlgebraLieEquiv
        ((realCliffordSpecialOrthogonalEmbeddedLieSubgroupData n).lieMapSubtypeVal X) := by
  have h := congrArg
    (fun Y : LeftInvariantDerivation 𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ)
      (Matrix (Fin n) (Fin n) ℝ)ˣ ↦ TauCeti.Lie.unitsLieAlgebraLieEquiv Y)
    ((realCliffordSpecialOrthogonalEmbeddedLieSubgroupData n)
      |>.lieEquivLieSubalgebraOfSubgroup_apply X)
  simp only [realCliffordSpecialOrthogonalLieEquivSo, LieEquiv.trans_apply,
    coe_specialOrthogonalAmbientCoordinateLieEquiv_apply]
  exact h

/-- The units coordinates of the differentiated special-orthogonal-carrier inclusion normalize to
the concrete skew-matrix coordinates. -/
@[simp↓ high]
theorem
    unitsLieAlgebraLieEquiv_lieMapSubtypeVal_eq_coe_realCliffordSpecialOrthogonalLieEquivSo
    (n : ℕ) (X : LeftInvariantDerivation 𝓘(ℝ, SpecialOrthogonalLieModel(n))
      (SpecialOrthogonalUnitsRange(n))) :
    TauCeti.Lie.unitsLieAlgebraLieEquiv
        ((realCliffordSpecialOrthogonalEmbeddedLieSubgroupData n).lieMapSubtypeVal X) =
      ((realCliffordSpecialOrthogonalLieEquivSo n X :
          LieAlgebra.Orthogonal.so (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ) :=
  (coe_realCliffordSpecialOrthogonalLieEquivSo_apply n X).symm

/-- The continuous projection between the closed real Spin and special-orthogonal carriers,
regarded as a smooth homomorphism by automatic smoothness. -/
noncomputable def realCliffordSpinToSpecialOrthogonalSmoothRange (n : ℕ) :
    ContMDiffMonoidMorphism 𝓘(ℝ, SpinLieModel(n))
      𝓘(ℝ, SpecialOrthogonalLieModel(n)) ∞
      (SpinUnitsRange(n)) (SpecialOrthogonalUnitsRange(n)) :=
  -- The type annotation fixes the target carrier before synthesis chooses its selected chart.
  (show SpinUnitsRange(n) →ₜ* SpecialOrthogonalUnitsRange(n) from
    realCliffordSpinToSpecialOrthogonalRange n).toContMDiffMonoidMorphism _ _

/-- The smooth carrier projection has the same underlying map as the continuous projection. -/
@[simp]
theorem realCliffordSpinToSpecialOrthogonalSmoothRange_apply (n : ℕ) (x : SpinUnitsRange(n)) :
    realCliffordSpinToSpecialOrthogonalSmoothRange n x =
      realCliffordSpinToSpecialOrthogonalRange n x :=
  by
    rw [realCliffordSpinToSpecialOrthogonalSmoothRange]
    exact congrFun
      (ContinuousMonoidHom.coe_toContMDiffMonoidMorphism
        (I := 𝓘(ℝ, SpinLieModel(n))) (I' := 𝓘(ℝ, SpecialOrthogonalLieModel(n)))
        (show SpinUnitsRange(n) →ₜ* SpecialOrthogonalUnitsRange(n) from
          realCliffordSpinToSpecialOrthogonalRange n)) x

/-- The abstract Lie map of the smooth projection between the two closed range carriers. -/
noncomputable def realCliffordSpinToSpecialOrthogonalRangeLieMap (n : ℕ) :
    LeftInvariantDerivation 𝓘(ℝ, SpinLieModel(n)) (SpinUnitsRange(n)) →ₗ⁅ℝ⁆
      LeftInvariantDerivation 𝓘(ℝ, SpecialOrthogonalLieModel(n))
        (SpecialOrthogonalUnitsRange(n)) :=
  lieMap (realCliffordSpinToSpecialOrthogonalSmoothRange n)

/-- The abstract range map is the Lie functor applied to the smooth carrier projection. -/
theorem realCliffordSpinToSpecialOrthogonalRangeLieMap_eq_lieMap (n : ℕ) :
    realCliffordSpinToSpecialOrthogonalRangeLieMap n =
      lieMap (realCliffordSpinToSpecialOrthogonalSmoothRange n) :=
  by
    simp only [realCliffordSpinToSpecialOrthogonalRangeLieMap]

/-- The differential of the compact real Spin projection in quadratic-Clifford source
coordinates and skew-symmetric-matrix target coordinates. -/
noncomputable def realCliffordSpinToSpecialOrthogonalCoordinateLieHom (n : ℕ) :
    quadraticLieSubalgebra (realCliffordForm n 0) →ₗ⁅ℝ⁆
      LieAlgebra.Orthogonal.so (Fin n) ℝ :=
  (realCliffordSpecialOrthogonalLieEquivSo n).toLieHom.comp
    ((realCliffordSpinToSpecialOrthogonalRangeLieMap n).comp
      (realCliffordSpinLieEquivQuadratic n).symm.toLieHom)

/-- The coordinate Lie map is the abstract differential conjugated by the source and target
coordinate equivalences. -/
@[simp]
theorem realCliffordSpinToSpecialOrthogonalCoordinateLieHom_apply (n : ℕ)
    (x : quadraticLieSubalgebra (realCliffordForm n 0)) :
    realCliffordSpinToSpecialOrthogonalCoordinateLieHom n x =
      realCliffordSpecialOrthogonalLieEquivSo n
        (realCliffordSpinToSpecialOrthogonalRangeLieMap n
          ((realCliffordSpinLieEquivQuadratic n).symm x)) := by
  simp only [realCliffordSpinToSpecialOrthogonalCoordinateLieHom, LieHom.comp_apply,
    LieEquiv.coe_toLieHom]

end TauCeti.CliffordAlgebra
