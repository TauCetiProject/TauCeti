/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Instances.UnitsOfNormedAlgebra
public import TauCeti.Analysis.Matrix.Normed
public import TauCeti.Geometry.Lie.AutomaticSmoothness
public import TauCeti.Geometry.Lie.Subgroup.CompactSymplectic
public import TauCeti.Geometry.Lie.Subgroup.Embedded
public import TauCeti.Geometry.Lie.Subgroup.Units
public import TauCeti.Topology.Algebra.Matrix.Realify
import TauCeti.Analysis.Matrix.Exponential.Realify
import TauCeti.Geometry.Lie.Exponential.OneParameter

/-!
# Realification as an embedding of Lie groups

Realification `Matrix.GeneralLinearGroup.realify n 𝕜 : GL n 𝕜 →* GL (n ⊕ n) ℝ`, for `𝕜 = ℝ` or `ℂ`,
is a closed embedding of topological groups, so its image `C = (realify n 𝕜).range` is a closed
subgroup of the real Lie group `GL (n ⊕ n) ℝ`. By the closed-subgroup theorem it is an embedded
Lie subgroup, a real Lie group modelled on its Lie algebra. This file computes that Lie algebra and
identifies the resulting Lie group with `GL n 𝕜`, and likewise identifies `U(n)` with the compact
group `Sp(2n, ℝ) ∩ O(2n)` of orthogonal symplectic matrices.

* **The Lie algebra.** In the canonical matrix coordinates of the general linear Lie algebra, the
  Lie algebra of `C` is the set of realified matrices `X.realify`, `X : Matrix n n 𝕜`
  (`TauCeti.Lie.unitsLieAlgebraLieEquiv_symm_mem_lieSubalgebraOfSubgroup_range_realify_iff`).
  Realification commutes with the exponential (`Matrix.exp_realify`), so the exponential line of
  `X.realify` stays in `C`; conversely the velocity at `0` of an exponential line inside `C` lies in
  the closed subspace of realified matrices. For `𝕜 = ℂ` the realified matrices are those
  commuting with the canonical complex structure `J` (`Matrix.commute_J_iff_exists_realify_eq`),
  so the Lie algebra of the realified `GL(n, ℂ)` is the commutant of `J` (`TauCeti.Lie.
  unitsLieAlgebraLieEquiv_symm_mem_lieSubalgebraOfSubgroup_range_realify_iff_commute`).
* **The Lie groups.** `TauCeti.Lie.realifyRangeChartedSpace` and `TauCeti.Lie.realifyRangeLieGroup`
  are the closed-subgroup charts and Lie group structure of `C`. Realification is then a
  diffeomorphism of Lie groups from `GL n 𝕜` onto `C`
  (`Matrix.GeneralLinearGroup.realifyDiffeomorph`): it is the topological group isomorphism
  `Matrix.GeneralLinearGroup.realifyEquivRange`, which is smooth in both directions by automatic
  smoothness of continuous homomorphisms of Lie groups
  (`TauCeti.Lie.contMDiff_of_continuous_monoidHom`). In the same way the topological group
  isomorphism `Matrix.unitaryGroupEquivSymplecticInfOrthogonal` gives a diffeomorphism of Lie
  groups from the unitary subgroup of `GL n ℂ` onto `Sp(2n, ℝ) ∩ O(2n)`, both with their
  closed-subgroup structures (`Matrix.unitarySubgroupDiffeomorphSymplecticInfOrthogonal`).

The general linear Lie groups carry the topology of the `L∞` operator norm. To state or use these
results, `open scoped Matrix.Norms.Operator` and enable
`attribute [local instance] Matrix.linftyOpTopologicalSpace`; that topology is the entrywise one
(`Matrix.linftyOpTopologicalSpace_eq`).

## Main declarations

* `TauCeti.Lie.unitsLieAlgebraLieEquiv_symm_mem_lieSubalgebraOfSubgroup_range_realify_iff`: the
  Lie algebra of the realified `GL n 𝕜` is the realified matrices.
* `TauCeti.Lie.unitsLieAlgebraLieEquiv_symm_mem_lieSubalgebraOfSubgroup_range_realify_iff_commute`:
  the Lie algebra of the realified `GL(n, ℂ)` is the commutant of `J`.
* `TauCeti.Lie.realifyRangeEmbeddedData`: the closed-subgroup data of the realified `GL n 𝕜`, with
  `TauCeti.Lie.isEmbeddedLieSubgroup_range_realify`.
* `TauCeti.Lie.realifyRangeChartedSpace`, `TauCeti.Lie.realifyRangeLieGroup`: its charts and real
  Lie group structure.
* `Matrix.GeneralLinearGroup.realifyDiffeomorph`: realification as a diffeomorphism of Lie groups
  from `GL n 𝕜` onto its image.
* `Matrix.unitarySubgroupDiffeomorphSymplecticInfOrthogonal`: realification as a diffeomorphism of
  Lie groups from `U(n)` onto `Sp(2n, ℝ) ∩ O(2n)`.

## References

* B. C. Hall, *Lie Groups, Lie Algebras, and Representations*, second edition, Graduate Texts in
  Mathematics 222, Springer, 2015, Section 3.3 (the Lie algebra of a matrix Lie group).
* D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, third edition, Oxford University
  Press, 2017, Section 2.2 (complex linear maps as the real maps commuting with `J`, and
  `U(n) = Sp(2n) ∩ O(2n)`).
-/

public section

open Manifold Matrix
open scoped ContDiff Manifold Matrix.Norms.Operator

noncomputable section

namespace TauCeti.Lie

attribute [local instance 100] LieRing.ofAssociativeRing

-- Select the matrix topology underlying the operator norm used for the general linear Lie group.
attribute [local instance] Matrix.linftyOpTopologicalSpace

variable {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [RCLike 𝕜]

/-- **The Lie algebra of the realified `GL n 𝕜` is the realified matrices.** In the canonical
matrix coordinates of the general linear Lie algebra of `GL (n ⊕ n) ℝ`, a matrix belongs to the
Lie algebra of the image of realification exactly when it is the realification of a matrix. -/
-- Normalize membership before the Lie equivalence simplifies to its linear equivalence.
@[simp↓]
theorem unitsLieAlgebraLieEquiv_symm_mem_lieSubalgebraOfSubgroup_range_realify_iff
    (A : Matrix (n ⊕ n) (n ⊕ n) ℝ) :
    (unitsLieAlgebraLieEquiv (R := Matrix (n ⊕ n) (n ⊕ n) ℝ)).symm A ∈
        lieSubalgebraOfSubgroup (GeneralLinearGroup.realify n 𝕜).range ↔
      ∃ B : Matrix n n 𝕜, B.realify = A := by
  rw [unitsLieAlgebraLieEquiv_symm_mem_lieSubalgebraOfSubgroup_iff
    (GeneralLinearGroup.isClosed_range_realify n 𝕜)]
  refine ⟨fun h ↦ ?_, ?_⟩
  · -- The realified matrices form a closed subspace containing the whole exponential line.
    have hA : A ∈ LinearMap.range (realifyLinearMap n n 𝕜) :=
      TauCeti.mem_of_forall_exp_smul_mem (Submodule.isClosed_of_finiteDimensional _) fun t ↦ by
        obtain ⟨B, hB⟩ := h t
        exact ⟨B, by rw [realifyLinearMap_apply, ← GeneralLinearGroup.coe_realify, hB,
          TauCeti.expUnit_coe]⟩
    obtain ⟨B, rfl⟩ := hA
    exact ⟨B, (realifyLinearMap_apply B).symm⟩
  · rintro ⟨B, rfl⟩ t
    refine ⟨(Matrix.isUnit_exp (t • B)).unit, Units.ext ?_⟩
    rw [GeneralLinearGroup.coe_realify, IsUnit.unit_spec, TauCeti.expUnit_coe, ← realify_smul]
    exact (exp_realify (t • B)).symm

/-- **The Lie algebra of the realified `GL(n, ℂ)` is the commutant of `J`.** In the canonical
matrix coordinates of the general linear Lie algebra of `GL (n ⊕ n) ℝ`, a matrix belongs to the
Lie algebra of the realified `GL(n, ℂ)` exactly when it commutes with the canonical complex
structure `J`. -/
theorem unitsLieAlgebraLieEquiv_symm_mem_lieSubalgebraOfSubgroup_range_realify_iff_commute
    (A : Matrix (n ⊕ n) (n ⊕ n) ℝ) :
    (unitsLieAlgebraLieEquiv (R := Matrix (n ⊕ n) (n ⊕ n) ℝ)).symm A ∈
        lieSubalgebraOfSubgroup (GeneralLinearGroup.realify n ℂ).range ↔
      Commute (J n ℝ) A := by
  rw [unitsLieAlgebraLieEquiv_symm_mem_lieSubalgebraOfSubgroup_range_realify_iff,
    commute_J_iff_exists_realify_eq]

variable (n 𝕜)

/-- The model of the realified `GL n 𝕜`: its Lie algebra as a closed subgroup of `GL (n ⊕ n) ℝ`. -/
abbrev RealifyRangeModel :=
  (lieSubalgebraOfSubgroup (I := 𝓘(ℝ, Matrix (n ⊕ n) (n ⊕ n) ℝ))
    (GeneralLinearGroup.realify n 𝕜).range).toSubmodule

/-- The closed-subgroup data of the realified `GL n 𝕜` inside `GL (n ⊕ n) ℝ`. -/
def realifyRangeEmbeddedData :
    EmbeddedLieSubgroupData 𝓘(ℝ, Matrix (n ⊕ n) (n ⊕ n) ℝ)
      (GeneralLinearGroup.realify n 𝕜).range (RealifyRangeModel n 𝕜) :=
  EmbeddedLieSubgroupData.ofIsClosed (GeneralLinearGroup.isClosed_range_realify n 𝕜)

/-- **The realified `GL n 𝕜` is an embedded Lie subgroup of `GL (n ⊕ n) ℝ`.** -/
theorem isEmbeddedLieSubgroup_range_realify :
    IsEmbeddedLieSubgroup (I := 𝓘(ℝ, Matrix (n ⊕ n) (n ⊕ n) ℝ))
      (GeneralLinearGroup.realify n 𝕜).range :=
  isEmbeddedLieSubgroup_of_isClosed (GeneralLinearGroup.isClosed_range_realify n 𝕜)

/-- The closed-subgroup charts of the realified `GL n 𝕜`. -/
instance realifyRangeChartedSpace :
    ChartedSpace (RealifyRangeModel n 𝕜) (GeneralLinearGroup.realify n 𝕜).range :=
  (realifyRangeEmbeddedData n 𝕜).chartedSpace

/-- The real Lie group structure of the realified `GL n 𝕜` in its closed-subgroup charts. -/
instance realifyRangeLieGroup :
    LieGroup 𝓘(ℝ, RealifyRangeModel n 𝕜) ∞ (GeneralLinearGroup.realify n 𝕜).range :=
  (realifyRangeEmbeddedData n 𝕜).lieGroup

end TauCeti.Lie

namespace Matrix.GeneralLinearGroup

open TauCeti.Lie

-- Select the matrix topology underlying the operator norm used for the general linear Lie groups.
attribute [local instance] Matrix.linftyOpTopologicalSpace

variable (n 𝕜 : Type*) [Fintype n] [DecidableEq n] [RCLike 𝕜]

/-- **Realification is a diffeomorphism of Lie groups** from `GL n 𝕜` onto its image in
`GL (n ⊕ n) ℝ`, with the closed-subgroup structure of the image. It is the topological group
isomorphism `Matrix.GeneralLinearGroup.realifyEquivRange`, smooth in both directions because
continuous homomorphisms of Lie groups are smooth. -/
def realifyDiffeomorph :
    GL n 𝕜 ≃ₘ⟮𝓘(ℝ, Matrix n n 𝕜), 𝓘(ℝ, RealifyRangeModel n 𝕜)⟯ (realify n 𝕜).range where
  toEquiv := (realifyEquivRange n 𝕜).toEquiv
  -- The continuity statements of `realifyEquivRange` are for the entrywise topologies, which
  -- are definitionally the operator-norm topologies selected above
  -- (`Matrix.linftyOpTopologicalSpace_eq`).
  contMDiff_toFun :=
    contMDiff_of_continuous_monoidHom (realifyEquivRange n 𝕜) (realifyEquivRange n 𝕜).continuous
  contMDiff_invFun := contMDiff_of_continuous_monoidHom (realifyEquivRange n 𝕜).symm
    (realifyEquivRange n 𝕜).symm.continuous

@[simp]
theorem realifyDiffeomorph_apply (A : GL n 𝕜) :
    realifyDiffeomorph n 𝕜 A = realifyEquivRange n 𝕜 A :=
  (rfl)

@[simp]
theorem realifyDiffeomorph_symm_apply (M : (realify n 𝕜).range) :
    (realifyDiffeomorph n 𝕜).symm M = (realifyEquivRange n 𝕜).symm M :=
  (rfl)

end Matrix.GeneralLinearGroup

namespace Matrix

open TauCeti TauCeti.Lie

variable (n : Type*) [Fintype n] [DecidableEq n]

/-- Realification as a group isomorphism from the unitary subgroup of `GL n ℂ` onto the orthogonal
symplectic matrices `Sp(2n, ℝ) ∩ O(2n)`. -/
private def unitarySubgroupMulEquivSymplecticInfOrthogonal :
    unitarySubgroup (GL n ℂ) ≃* ↥(GLSymplectic n ℝ ⊓ unitarySubgroup (GL (n ⊕ n) ℝ)) :=
  unitarySubgroupUnitsEquiv.trans unitaryGroupEquivSymplecticInfOrthogonal.toMulEquiv

private theorem coe_unitarySubgroupMulEquivSymplecticInfOrthogonal_apply
    (U : unitarySubgroup (GL n ℂ)) :
    ((unitarySubgroupMulEquivSymplecticInfOrthogonal n U : GL (n ⊕ n) ℝ) :
        Matrix (n ⊕ n) (n ⊕ n) ℝ) = ((U : GL n ℂ) : Matrix n n ℂ).realify := by
  rw [unitarySubgroupMulEquivSymplecticInfOrthogonal, MulEquiv.trans_apply]
  -- `toMulEquiv` applies as the continuous group isomorphism itself.
  refine (congrArg Units.val (unitaryGroupEquivSymplecticInfOrthogonal_apply (n := n)
    (unitarySubgroupUnitsEquiv U))).trans ?_
  rw [GeneralLinearGroup.coe_realify, Unitary.val_toUnits_apply,
    unitarySubgroupUnitsEquiv_apply_coe]

-- The continuity statements are for the entrywise topologies of `GL n ℂ` and `GL (n ⊕ n) ℝ`, in
-- which `Matrix.unitaryGroupEquivSymplecticInfOrthogonal` is stated.
private theorem continuous_unitarySubgroupMulEquivSymplecticInfOrthogonal :
    Continuous (unitarySubgroupMulEquivSymplecticInfOrthogonal n) := by
  have h := (map_continuous (unitaryGroupEquivSymplecticInfOrthogonal (n := n))).comp
    (unitarySubgroupUnitsHomeomorph (Matrix n n ℂ)).continuous
  rwa [show ⇑(unitarySubgroupUnitsHomeomorph (Matrix n n ℂ)) = unitarySubgroupUnitsEquiv from
    funext unitarySubgroupUnitsHomeomorph_apply] at h

private theorem continuous_unitarySubgroupMulEquivSymplecticInfOrthogonal_symm :
    Continuous (unitarySubgroupMulEquivSymplecticInfOrthogonal n).symm := by
  have h := (unitarySubgroupUnitsHomeomorph (Matrix n n ℂ)).symm.continuous.comp
    (map_continuous (unitaryGroupEquivSymplecticInfOrthogonal (n := n)).symm)
  rwa [show ⇑(unitarySubgroupUnitsHomeomorph (Matrix n n ℂ)).symm =
    unitarySubgroupUnitsEquiv.symm from funext unitarySubgroupUnitsHomeomorph_symm_apply] at h

-- Select the matrix topologies underlying the operator norms used for the general linear Lie
-- groups, which are definitionally the entrywise topologies (`Matrix.linftyOpTopologicalSpace_eq`).
attribute [local instance] Matrix.linftyOpTopologicalSpace

/-- **Realification is a diffeomorphism of Lie groups from `U(n)` onto `Sp(2n, ℝ) ∩ O(2n)`**, the
unitary subgroup of `GL n ℂ` and the orthogonal symplectic matrices carrying their closed-subgroup
structures. On the underlying unitary matrices it is the topological group isomorphism
`Matrix.unitaryGroupEquivSymplecticInfOrthogonal`. -/
def unitarySubgroupDiffeomorphSymplecticInfOrthogonal :
    unitarySubgroup (GL n ℂ) ≃ₘ⟮𝓘(ℝ, (lieSubalgebraOfSubgroup (I := 𝓘(ℝ, Matrix n n ℂ))
        (unitarySubgroup (GL n ℂ))).toSubmodule), 𝓘(ℝ, CompactSymplecticModel n ℝ)⟯
      ↥(GLSymplectic n ℝ ⊓ unitarySubgroup (GL (n ⊕ n) ℝ)) where
  toEquiv := (unitarySubgroupMulEquivSymplecticInfOrthogonal n).toEquiv
  contMDiff_toFun := contMDiff_of_continuous_monoidHom
    (unitarySubgroupMulEquivSymplecticInfOrthogonal n)
    (continuous_unitarySubgroupMulEquivSymplecticInfOrthogonal n)
  contMDiff_invFun := contMDiff_of_continuous_monoidHom
    (unitarySubgroupMulEquivSymplecticInfOrthogonal n).symm
    (continuous_unitarySubgroupMulEquivSymplecticInfOrthogonal_symm n)

/-- The diffeomorphism `U(n) ≃ Sp(2n, ℝ) ∩ O(2n)` realifies the unitary matrix. -/
@[simp]
theorem coe_unitarySubgroupDiffeomorphSymplecticInfOrthogonal_apply
    (U : unitarySubgroup (GL n ℂ)) :
    ((unitarySubgroupDiffeomorphSymplecticInfOrthogonal n U : GL (n ⊕ n) ℝ) :
        Matrix (n ⊕ n) (n ⊕ n) ℝ) = ((U : GL n ℂ) : Matrix n n ℂ).realify :=
  coe_unitarySubgroupMulEquivSymplecticInfOrthogonal_apply n U

/-- The inverse diffeomorphism `Sp(2n, ℝ) ∩ O(2n) ≃ U(n)` returns the unitary matrix whose
realification is the given orthogonal symplectic matrix. -/
@[simp]
theorem realify_coe_unitarySubgroupDiffeomorphSymplecticInfOrthogonal_symm_apply
    (M : ↥(GLSymplectic n ℝ ⊓ unitarySubgroup (GL (n ⊕ n) ℝ))) :
    ((((unitarySubgroupDiffeomorphSymplecticInfOrthogonal n).symm M :
        unitarySubgroup (GL n ℂ)) : GL n ℂ) : Matrix n n ℂ).realify =
      ((M : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ) := by
  rw [← coe_unitarySubgroupDiffeomorphSymplecticInfOrthogonal_apply, Diffeomorph.apply_symm_apply]

end Matrix
