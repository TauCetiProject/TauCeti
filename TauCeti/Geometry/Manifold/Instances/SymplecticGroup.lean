/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Subalgebra.RestrictScalars
public import TauCeti.Geometry.Lie.Subgroup.Differential
public import TauCeti.Geometry.Lie.Subgroup.Symplectic
public import TauCeti.Geometry.Manifold.Immersion.LocalDiffeomorph
import TauCeti.Geometry.Manifold.Algebra.LieGroup
public import TauCeti.Geometry.Manifold.PullbackGroupoid

/-!
# The native symplectic Lie group

The canonical multiplicative equivalence between `Matrix.symplecticGroup` and the closed
subgroup `TauCeti.GLSymplectic` identifies their subspace topologies. Pulling back the
closed-subgroup charts gives a real Lie group structure on the original matrix carrier.
The inclusion into the units is a smooth embedding, and its differential gives the
Lie-algebra equivalence to `LieAlgebra.Symplectic.sp` with scalars restricted to `ℝ`.

For matrix-valued results, use `open scoped Matrix.Norms.Operator` and
`attribute [local instance] Matrix.linftyOpTopologicalSpace`, as for the special linear group.
The topology of this operator norm agrees with the entrywise topology.

## Main results

* `TauCeti.Lie.symplecticGroupChartedSpace` and `TauCeti.Lie.symplecticGroup_lieGroup` give
  the native charts and smooth group structure.
* `TauCeti.Lie.isSmoothEmbedding_ofSymplecticGroup` proves that the original matrix-to-units
  map is a smooth embedding.
* `TauCeti.Lie.symplecticGroupLieAlgebraEquiv` identifies the native Lie algebra with the
  symplectic matrix Lie algebra.
* `TauCeti.Lie.restrictScalarsIncl_symplecticGroupLieAlgebraEquiv_apply` identifies the
  equivalence with the differential of the inclusion in matrix coordinates.

## References

* Brian C. Hall, *Lie Groups, Lie Algebras, and Representations*, 2nd ed., Springer GTM 222
  (2015), §1.2.4 and Proposition 3.25.
* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013),
  Theorem 20.12.
-/

public noncomputable section

open Matrix
open scoped Matrix Manifold ContDiff

namespace TauCeti.Lie

open scoped Matrix.Norms.Operator

attribute [local instance] Matrix.linftyOpTopologicalSpace
attribute [local instance 100] LieRing.ofAssociativeRing

variable {l : Type*} [Fintype l] [DecidableEq l] {𝕜 : Type*} [RCLike 𝕜]

/-- The model is the canonical Lie subalgebra of the symplectic subgroup of the units. -/
abbrev SymplecticGroupModel (l : Type*) [Fintype l] [DecidableEq l]
    (𝕜 : Type*) [RCLike 𝕜] :=
  (lieSubalgebraOfSubgroup (I := 𝓘(ℝ, Matrix (l ⊕ l) (l ⊕ l) 𝕜))
    (GLSymplectic l 𝕜 : Subgroup (Matrix (l ⊕ l) (l ⊕ l) 𝕜)ˣ)).toSubmodule

/-- The embedded Lie subgroup data on the symplectic subgroup of matrix units. -/
def symplecticEmbeddedData (l : Type*) [Fintype l] [DecidableEq l]
    (𝕜 : Type*) [RCLike 𝕜] :
    EmbeddedLieSubgroupData 𝓘(ℝ, Matrix (l ⊕ l) (l ⊕ l) 𝕜)
      (GLSymplectic l 𝕜) (SymplecticGroupModel l 𝕜) :=
  EmbeddedLieSubgroupData.ofIsClosed (isClosed_GLSymplectic l 𝕜)

/-- The closed-subgroup charts on the symplectic subgroup of matrix units. -/
local instance closedSymplecticChartedSpace (l : Type*) [Fintype l] [DecidableEq l]
    (𝕜 : Type*) [RCLike 𝕜] : ChartedSpace (SymplecticGroupModel l 𝕜) (GLSymplectic l 𝕜) :=
  (symplecticEmbeddedData l 𝕜).chartedSpace

/-- The Lie-group structure on the symplectic subgroup in the closed-subgroup charts. -/
local instance closedSymplecticLieGroup (l : Type*) [Fintype l] [DecidableEq l]
    (𝕜 : Type*) [RCLike 𝕜] : LieGroup 𝓘(ℝ, SymplecticGroupModel l 𝕜) ∞ (GLSymplectic l 𝕜) :=
  (symplecticEmbeddedData l 𝕜).lieGroup

/-- The closed-subgroup charts pulled back to Mathlib's symplectic matrices. -/
@[instance_reducible]
instance symplecticGroupChartedSpace (l : Type*) [Fintype l] [DecidableEq l]
    (𝕜 : Type*) [RCLike 𝕜] : ChartedSpace (SymplecticGroupModel l 𝕜) (Matrix.symplecticGroup l 𝕜) :=
  (GLSymplectic.symplecticGroupContinuousMulEquiv l 𝕜).toHomeomorph.pullbackChartedSpace
    (cM := closedSymplecticChartedSpace l 𝕜)

/-- Mathlib's matrix symplectic group is a smooth manifold for its subspace topology. -/
instance symplecticGroup_isManifold (l : Type*) [Fintype l] [DecidableEq l]
    (𝕜 : Type*) [RCLike 𝕜] :
    IsManifold 𝓘(ℝ, SymplecticGroupModel l 𝕜) ∞ (Matrix.symplecticGroup l 𝕜) :=
  (GLSymplectic.symplecticGroupContinuousMulEquiv l 𝕜).toHomeomorph.pullback_isManifold
    (cM := closedSymplecticChartedSpace l 𝕜)
    (manifoldM := (closedSymplecticLieGroup l 𝕜).toContMDiffMul.toIsManifold)
    𝓘(ℝ, SymplecticGroupModel l 𝕜) ∞

-- Keep the selected closed-subgroup charts explicit when specializing the generic pullback.
private def symplecticDiffeomorph (l : Type*) [Fintype l] [DecidableEq l]
    (𝕜 : Type*) [RCLike 𝕜] :
    Matrix.symplecticGroup l 𝕜 ≃ₘ^∞⟮𝓘(ℝ, SymplecticGroupModel l 𝕜),
      𝓘(ℝ, SymplecticGroupModel l 𝕜)⟯ GLSymplectic l 𝕜 :=
  (GLSymplectic.symplecticGroupContinuousMulEquiv l 𝕜).toHomeomorph.pullbackDiffeomorph
    (cM := closedSymplecticChartedSpace l 𝕜) 𝓘(ℝ, SymplecticGroupModel l 𝕜) ∞

private theorem symplecticDiffeomorph_coe (l : Type*) [Fintype l] [DecidableEq l]
    (𝕜 : Type*) [RCLike 𝕜] :
    ⇑(symplecticDiffeomorph l 𝕜) = GLSymplectic.symplecticGroupContinuousMulEquiv l 𝕜 := by
  unfold symplecticDiffeomorph
  exact (GLSymplectic.symplecticGroupContinuousMulEquiv l 𝕜).toHomeomorph.coe_pullbackDiffeomorph
    (cM := closedSymplecticChartedSpace l 𝕜) 𝓘(ℝ, SymplecticGroupModel l 𝕜) ∞

/-- Mathlib's matrix symplectic group is a Lie group for its original subspace topology. -/
instance symplecticGroup_lieGroup (l : Type*) [Fintype l] [DecidableEq l]
    (𝕜 : Type*) [RCLike 𝕜] :
    LieGroup 𝓘(ℝ, SymplecticGroupModel l 𝕜) ∞ (Matrix.symplecticGroup l 𝕜) :=
  (GLSymplectic.symplecticGroupContinuousMulEquiv l 𝕜).lieGroup_pullbackChartedSpace
    (cB := closedSymplecticChartedSpace l 𝕜) (lieB := closedSymplecticLieGroup l 𝕜)
    (I := 𝓘(ℝ, SymplecticGroupModel l 𝕜)) (n := ∞)

/-- In the transported charts the actual matrix-to-units map is a smooth embedding. -/
theorem isSmoothEmbedding_ofSymplecticGroup (l : Type*) [Fintype l] [DecidableEq l]
    (𝕜 : Type*) [RCLike 𝕜] :
    Manifold.IsSmoothEmbedding 𝓘(ℝ, SymplecticGroupModel l 𝕜)
      𝓘(ℝ, Matrix (l ⊕ l) (l ⊕ l) 𝕜) ∞ (GLSymplectic.ofSymplecticGroup l 𝕜) := by
  have h := TauCeti.isSmoothEmbedding_comp_isLocalDiffeomorph
    (g := symplecticDiffeomorph l 𝕜) (f := fun x : GLSymplectic l 𝕜 ↦ (x : GL (l ⊕ l) 𝕜))
    (symplecticDiffeomorph l 𝕜).isLocalDiffeomorph
    (symplecticDiffeomorph l 𝕜).toHomeomorph.isEmbedding
    (symplecticEmbeddedData l 𝕜).isSmoothEmbedding_subtypeVal
  have he : (fun x : GLSymplectic l 𝕜 ↦ (x : GL (l ⊕ l) 𝕜)) ∘
      (symplecticDiffeomorph l 𝕜) = GLSymplectic.ofSymplecticGroup l 𝕜 := by
    funext x
    rw [Function.comp_apply, symplecticDiffeomorph_coe]
    exact GLSymplectic.coe_symplecticGroupContinuousMulEquiv l 𝕜 x
  exact he ▸ h

private def symplecticGroupToClosedCarrier (l : Type*) [Fintype l] [DecidableEq l]
    (𝕜 : Type*) [RCLike 𝕜] :
    ContMDiffMonoidMorphism 𝓘(ℝ, SymplecticGroupModel l 𝕜)
      𝓘(ℝ, SymplecticGroupModel l 𝕜) ∞ (Matrix.symplecticGroup l 𝕜) (GLSymplectic l 𝕜) where
  toMonoidHom := (GLSymplectic.symplecticGroupContinuousMulEquiv l 𝕜).toMulEquiv.toMonoidHom
  contMDiff_toFun := by
    -- Expose the equivalence underlying the monoid-hom coercion for the pullback theorem.
    change ContMDiff 𝓘(ℝ, SymplecticGroupModel l 𝕜) 𝓘(ℝ, SymplecticGroupModel l 𝕜) ∞
      (⇑(GLSymplectic.symplecticGroupContinuousMulEquiv l 𝕜))
    rw [← symplecticDiffeomorph_coe]
    exact (symplecticDiffeomorph l 𝕜).contMDiff

private theorem coe_symplecticGroupToClosedCarrier (l : Type*) [Fintype l] [DecidableEq l]
    (𝕜 : Type*) [RCLike 𝕜] :
    ⇑(symplecticGroupToClosedCarrier l 𝕜) =
      (GLSymplectic.symplecticGroupContinuousMulEquiv l 𝕜) := by
  -- The smooth homomorphism and continuous equivalence retain the same function through
  -- their monoid-hom projections.
  unfold symplecticGroupToClosedCarrier
  rfl

/-- The canonical embedding into the general linear group as a smooth group homomorphism. -/
def symplecticGroupToGLSmoothHom (l : Type*) [Fintype l] [DecidableEq l]
    (𝕜 : Type*) [RCLike 𝕜] :
    ContMDiffMonoidMorphism 𝓘(ℝ, SymplecticGroupModel l 𝕜)
      𝓘(ℝ, Matrix (l ⊕ l) (l ⊕ l) 𝕜) ∞ (Matrix.symplecticGroup l 𝕜) (GL (l ⊕ l) 𝕜) :=
  (symplecticEmbeddedData l 𝕜).subtypeVal.comp (symplecticGroupToClosedCarrier l 𝕜)

/-- The smooth homomorphism has the original matrix-to-units map as its underlying map. -/
@[simp]
theorem symplecticGroupToGLSmoothHom_apply (l : Type*) [Fintype l] [DecidableEq l]
    (𝕜 : Type*) [RCLike 𝕜] (x : Matrix.symplecticGroup l 𝕜) :
    symplecticGroupToGLSmoothHom l 𝕜 x = GLSymplectic.ofSymplecticGroup l 𝕜 x := by
  rw [symplecticGroupToGLSmoothHom]
  -- Express evaluation as a composition on the selected carrier charts to use `comp_apply`.
  change ((symplecticEmbeddedData l 𝕜).subtypeVal.comp
    (symplecticGroupToClosedCarrier l 𝕜)) x = _
  rw [ContMDiffMonoidMorphism.coe_comp, Function.comp_apply,
    EmbeddedLieSubgroupData.subtypeVal_apply]
  rw [coe_symplecticGroupToClosedCarrier]
  exact GLSymplectic.coe_symplecticGroupContinuousMulEquiv l 𝕜 x

private def symplecticNativeToCarrierLieEquiv (l : Type*) [Fintype l] [DecidableEq l]
    (𝕜 : Type*) [RCLike 𝕜] :
    LeftInvariantDerivation 𝓘(ℝ, SymplecticGroupModel l 𝕜) (Matrix.symplecticGroup l 𝕜)
      ≃ₗ⁅ℝ⁆ LeftInvariantDerivation 𝓘(ℝ, SymplecticGroupModel l 𝕜) (GLSymplectic l 𝕜) := by
  let f := symplecticGroupToClosedCarrier l 𝕜
  have hf : IsLocalDiffeomorphAt 𝓘(ℝ, SymplecticGroupModel l 𝕜)
      𝓘(ℝ, SymplecticGroupModel l 𝕜) ∞ f 1 := by
    dsimp only [f]
    rw [coe_symplecticGroupToClosedCarrier, ← symplecticDiffeomorph_coe]
    exact (symplecticDiffeomorph l 𝕜).isLocalDiffeomorph 1
  exact lieEquivOfIsLocalDiffeomorphAt f hf

private theorem symplecticNativeToCarrierLieEquiv_apply (l : Type*) [Fintype l] [DecidableEq l]
    (𝕜 : Type*) [RCLike 𝕜]
    (D : LeftInvariantDerivation 𝓘(ℝ, SymplecticGroupModel l 𝕜) (Matrix.symplecticGroup l 𝕜)) :
    symplecticNativeToCarrierLieEquiv l 𝕜 D = lieMap (symplecticGroupToClosedCarrier l 𝕜) D := by
  unfold symplecticNativeToCarrierLieEquiv
  exact lieEquivOfIsLocalDiffeomorphAt_apply _ _ D

private def symplecticLieSubalgebraToSp (l : Type*) [Fintype l] [DecidableEq l]
    (𝕜 : Type*) [RCLike 𝕜] :
    lieSubalgebraOfSubgroup (I := 𝓘(ℝ, Matrix (l ⊕ l) (l ⊕ l) 𝕜))
        (GLSymplectic l 𝕜) ≃ₗ⁅ℝ⁆ RestrictScalars ℝ 𝕜 (LieAlgebra.Symplectic.sp l 𝕜) :=
  { LinearEquiv.ofSubmodules
      (unitsLieAlgebraLieEquiv (R := Matrix (l ⊕ l) (l ⊕ l) 𝕜)).toLinearEquiv
      _ ((LieAlgebra.Symplectic.sp l 𝕜).toSubmodule.restrictScalars ℝ) (by
        ext A
        simp only [Submodule.mem_map_equiv, Submodule.restrictScalars_mem]
        exact unitsLieAlgebraLieEquiv_symm_mem_lieSubalgebraOfSubgroup_iff_mem_sp A) with
    map_smul' := fun r X ↦ by
      -- The restricted action uses `algebraMap`, and the submodule inherits the real action.
      apply (RestrictScalars.addEquiv ℝ 𝕜 (LieAlgebra.Symplectic.sp l 𝕜)).injective
      apply Subtype.ext
      change unitsLieAlgebraLieEquiv
          (r • (X : LeftInvariantDerivation 𝓘(ℝ, Matrix (l ⊕ l) (l ⊕ l) 𝕜)
            (GL (l ⊕ l) 𝕜))) =
        algebraMap ℝ 𝕜 r • unitsLieAlgebraLieEquiv
          (X : LeftInvariantDerivation 𝓘(ℝ, Matrix (l ⊕ l) (l ⊕ l) 𝕜) (GL (l ⊕ l) 𝕜))
      rw [map_smul, algebraMap_smul]
    map_lie' := fun {x y} ↦ Subtype.ext
      ((unitsLieAlgebraLieEquiv (R := Matrix (l ⊕ l) (l ⊕ l) 𝕜)).map_lie x y) }

private theorem restrictScalarsIncl_symplecticLieSubalgebraToSp_apply
    (l : Type*) [Fintype l] [DecidableEq l] (𝕜 : Type*) [RCLike 𝕜]
    (X : lieSubalgebraOfSubgroup (I := 𝓘(ℝ, Matrix (l ⊕ l) (l ⊕ l) 𝕜))
      (GLSymplectic l 𝕜)) :
    (LieAlgebra.Symplectic.sp l 𝕜).restrictScalarsIncl ℝ
      (symplecticLieSubalgebraToSp l 𝕜 X) =
      unitsLieAlgebraLieEquiv
        (X : LeftInvariantDerivation 𝓘(ℝ, Matrix (l ⊕ l) (l ⊕ l) 𝕜) (GL (l ⊕ l) 𝕜)) := by
  rw [LieSubalgebra.restrictScalarsIncl_apply]
  -- The restricted equivalence and scalar-restriction accessor retain the ambient
  -- units-coordinate function. The scalar-linearity field supplies its proof.
  unfold symplecticLieSubalgebraToSp
  rfl

/-- The Lie algebra of Mathlib's matrix symplectic group is its symplectic
matrix Lie algebra viewed over the real scalars. -/
def symplecticGroupLieAlgebraEquiv (l : Type*) [Fintype l] [DecidableEq l]
    (𝕜 : Type*) [RCLike 𝕜] :
    LeftInvariantDerivation 𝓘(ℝ, SymplecticGroupModel l 𝕜) (Matrix.symplecticGroup l 𝕜)
      ≃ₗ⁅ℝ⁆ RestrictScalars ℝ 𝕜 (LieAlgebra.Symplectic.sp l 𝕜) :=
  (symplecticNativeToCarrierLieEquiv l 𝕜).trans
    ((symplecticEmbeddedData l 𝕜).lieEquivLieSubalgebraOfSubgroup.trans
      (symplecticLieSubalgebraToSp l 𝕜))

/-- In matrix coordinates the native Lie algebra equivalence is the differential of the
canonical matrix-to-units map. -/
@[simp↓]
theorem restrictScalarsIncl_symplecticGroupLieAlgebraEquiv_apply
    (l : Type*) [Fintype l] [DecidableEq l]
    (𝕜 : Type*) [RCLike 𝕜]
    (D : LeftInvariantDerivation 𝓘(ℝ, SymplecticGroupModel l 𝕜) (Matrix.symplecticGroup l 𝕜)) :
    (LieAlgebra.Symplectic.sp l 𝕜).restrictScalarsIncl ℝ
      (symplecticGroupLieAlgebraEquiv l 𝕜 D) =
    (unitsLieAlgebraLieEquiv (R := Matrix (l ⊕ l) (l ⊕ l) 𝕜))
      (lieMap (symplecticGroupToGLSmoothHom l 𝕜) D) := by
  simp only [symplecticGroupLieAlgebraEquiv, LieEquiv.trans_apply,
    restrictScalarsIncl_symplecticLieSubalgebraToSp_apply,
    EmbeddedLieSubgroupData.lieEquivLieSubalgebraOfSubgroup_apply,
    EmbeddedLieSubgroupData.lieMapSubtypeVal_apply, symplecticNativeToCarrierLieEquiv_apply,
    symplecticGroupToGLSmoothHom, lieMap_comp, LieHom.comp_apply]

end TauCeti.Lie
