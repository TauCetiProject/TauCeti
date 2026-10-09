/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.AutomaticSmoothness
public import TauCeti.Geometry.Lie.ContinuousFunctor
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
* `TauCeti.CliffordAlgebra.isQuotientMap_realCliffordSpinToSpecialOrthogonalSmoothRange` records
  the quotient property of the smooth carrier projection.
* `TauCeti.CliffordAlgebra.lieMap_lift_realCliffordSpinToSpecialOrthogonalSmoothRange_comp`
  identifies the differential of a homomorphism descended through that projection.

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

/-- The smooth projection between the closed real Spin and special-orthogonal carriers, regarded
as a continuous homomorphism, is a quotient map. -/
theorem isQuotientMap_realCliffordSpinToSpecialOrthogonalSmoothRange (n : ℕ) :
    Topology.IsQuotientMap
      (show SpinUnitsRange(n) →ₜ* SpecialOrthogonalUnitsRange(n) from
        realCliffordSpinToSpecialOrthogonalSmoothRange n) := by
  let p : SpinUnitsRange(n) →ₜ* SpecialOrthogonalUnitsRange(n) :=
    realCliffordSpinToSpecialOrthogonalSmoothRange n
  -- The coercion in the statement inserts a let-bound continuous map; name that exact map so the
  -- compact-to-Hausdorff quotient theorem uses the selected Lie-group topologies.
  change Topology.IsQuotientMap p
  let _ : CompactSpace (SpinUnitsRange(n)) :=
    Homeomorph.compactSpace
      (realCliffordSpinContinuousMulEquivUnitsRange n).toHomeomorph
  apply Topology.IsQuotientMap.of_surjective_continuous
  · intro y
    obtain ⟨x, hx⟩ := realCliffordSpinToSpecialOrthogonalRange_surjective n y
    refine ⟨x, ?_⟩
    -- Expose the smooth morphism below its continuous coercion so its application theorem matches.
    change realCliffordSpinToSpecialOrthogonalSmoothRange n x = y
    rw [realCliffordSpinToSpecialOrthogonalSmoothRange_apply]
    exact hx
  · exact p.continuous

/-- The supplied differential of the compact real Spin projection is its continuous Lie map. -/
theorem realCliffordSpinToSpecialOrthogonalRangeLieMap_eq_continuousLieMap (n : ℕ) :
    realCliffordSpinToSpecialOrthogonalRangeLieMap n =
      ContinuousMonoidHom.lieMap
        (I := 𝓘(ℝ, SpinLieModel(n)))
        (I' := 𝓘(ℝ, SpecialOrthogonalLieModel(n)))
        (show SpinUnitsRange(n) →ₜ* SpecialOrthogonalUnitsRange(n) from
          realCliffordSpinToSpecialOrthogonalSmoothRange n) := by
  let p : SpinUnitsRange(n) →ₜ* SpecialOrthogonalUnitsRange(n) :=
    realCliffordSpinToSpecialOrthogonalSmoothRange n
  -- The two APIs bundle the same function through different opaque morphism structures; expose
  -- their selected smooth and continuous presentations before using the public defining equation.
  change _root_.lieMap (realCliffordSpinToSpecialOrthogonalSmoothRange n) =
    ContinuousMonoidHom.lieMap p
  rw [ContinuousMonoidHom.lieMap_eq_lieMap_toContMDiffMonoidMorphism]
  apply congrArg _root_.lieMap
  apply DFunLike.coe_injective
  rw [ContinuousMonoidHom.coe_toContMDiffMonoidMorphism]
  rfl

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [FiniteDimensional ℝ E] [LieGroup I ∞ G]

/-- Descending a continuous homomorphism through the compact real Spin projection preserves its
Lie map after composition with the projection differential. -/
theorem lieMap_lift_realCliffordSpinToSpecialOrthogonalSmoothRange_comp
    (n : ℕ) (f : SpinUnitsRange(n) →ₜ* G)
    (hf : ((show SpinUnitsRange(n) →ₜ* SpecialOrthogonalUnitsRange(n) from
        realCliffordSpinToSpecialOrthogonalSmoothRange n) :
          SpinUnitsRange(n) →* SpecialOrthogonalUnitsRange(n)).ker ≤
      (f : SpinUnitsRange(n) →* G).ker) :
    (ContinuousMonoidHom.lieMap
        (I := 𝓘(ℝ, SpecialOrthogonalLieModel(n))) (I' := I)
        (ContinuousMonoidHom.liftOfIsQuotientMap
          (show SpinUnitsRange(n) →ₜ* SpecialOrthogonalUnitsRange(n) from
            realCliffordSpinToSpecialOrthogonalSmoothRange n)
          (isQuotientMap_realCliffordSpinToSpecialOrthogonalSmoothRange n)
          f hf)).comp
      (realCliffordSpinToSpecialOrthogonalRangeLieMap n) =
    ContinuousMonoidHom.lieMap (I := 𝓘(ℝ, SpinLieModel(n))) (I' := I) f := by
  let p : SpinUnitsRange(n) →ₜ* SpecialOrthogonalUnitsRange(n) :=
    realCliffordSpinToSpecialOrthogonalSmoothRange n
  let hp : Topology.IsQuotientMap p :=
    isQuotientMap_realCliffordSpinToSpecialOrthogonalSmoothRange n
  let g : SpecialOrthogonalUnitsRange(n) →ₜ* G :=
    ContinuousMonoidHom.liftOfIsQuotientMap p hp f hf
  have hprojection : realCliffordSpinToSpecialOrthogonalRangeLieMap n =
      ContinuousMonoidHom.lieMap
        (I := 𝓘(ℝ, SpinLieModel(n)))
        (I' := 𝓘(ℝ, SpecialOrthogonalLieModel(n))) p :=
    realCliffordSpinToSpecialOrthogonalRangeLieMap_eq_continuousLieMap n
  have hdescent := ContinuousMonoidHom.lieMap_liftOfIsQuotientMap_comp
    (I := 𝓘(ℝ, SpinLieModel(n)))
    (I' := 𝓘(ℝ, SpecialOrthogonalLieModel(n))) (I'' := I)
    p hp f hf
  -- The displayed lift retains its quotient and kernel proofs; expose the proof-irrelevant
  -- let-bound presentation so `hdescent` and the projection bridge have the same middle map.
  change (ContinuousMonoidHom.lieMap
      (I := 𝓘(ℝ, SpecialOrthogonalLieModel(n))) (I' := I) g).comp
      (realCliffordSpinToSpecialOrthogonalRangeLieMap n) = _
  exact congrArg
    (fun L ↦ (ContinuousMonoidHom.lieMap
      (I := 𝓘(ℝ, SpecialOrthogonalLieModel(n))) (I' := I) g).comp L)
    hprojection |>.trans hdescent

end TauCeti.CliffordAlgebra
