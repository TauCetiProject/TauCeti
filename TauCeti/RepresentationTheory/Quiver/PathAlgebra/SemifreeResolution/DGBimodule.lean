/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DG.Bimodule.Cone
public import TauCeti.Algebra.Homology.DG.Bimodule.TensorProduct.Unit
public import TauCeti.RepresentationTheory.Quiver.PathAlgebra.SemifreeResolution.Actions
import TauCeti.RepresentationTheory.Quiver.PathAlgebra.SemifreeResolution.Grading
import TauCeti.RingTheory.GradedAlgebra.TensorProduct

/-!
# The augmented DG bimodule resolution of a DG path algebra

For a finite-vertex quiver and a DG path algebra whose differential kills the vertex
idempotents, the standard arrow and vertex tensor terms are DG bimodules for the original
outer actions and the arrow-weight grading. This lifts the scalar cone
`PathAlgebra.standardResolution` and its augmentation. Their boundary
is a DG bimodule map. Its cone augments to the diagonal bimodule by multiplication, and
this augmentation is a quasi-isomorphism. The construction applies to the uncompleted
two-dimensional Ginzburg algebra, where the suspended generator has degree `-1` for a
doubled arrow and `-2` for an added loop.

## References

* B. Keller, *Deformed Calabi--Yau completions*, Section 6.
* Junyang Liu and Zhengfang Wang, *A-infinity deformations of zigzag algebras via Ginzburg
  dg algebras*, Proposition 3.2 ([arXiv:2301.06757](https://arxiv.org/abs/2301.06757)).
-/

public section

open CategoryTheory MulOpposite
open scoped TensorProduct

namespace TauCeti.PathAlgebra

open TauCeti.Algebra.TensorProduct

universe u v w

variable {k : Type w} [CommRing k] {Q : Type u} [Quiver.{v} Q] [Fintype Q]
  {wt : ∀ {i j : Q}, (i ⟶ j) → ℤ} {d : pathAlgebra k Q →ₗ[k] pathAlgebra k Q}
  (hd : IsDGAlgebra (gradeBy k wt) d) (hdε : ∀ i, d (vertexIdempotent k i) = 0)

local notation "𝒜" => pathAlgebra k Q
local notation "ℰ" => 𝒜 ⊗[k] 𝒜ᵐᵒᵖ
local notation "Γ" => InternalGrading.ofDecomposition (gradeBy k wt)
local notation "G" => InternalGrading.mk (gradeBy k wt) (isInternal_gradeBy k wt)
local notation "Ξ" => InternalGrading.tensorProduct (G) (InternalGrading.opposite (G))

section RestrictedActions

/-- Restrict the enveloping action along the left tensor factor. -/
noncomputable local instance (priority := high) (M : Type*) [AddCommGroup M] [Module ℰ M] :
    Module 𝒜 M :=
  moduleLeft (k := k) (B := 𝒜ᵐᵒᵖ) M

/-- Restrict the enveloping action along the right tensor factor. -/
noncomputable local instance (priority := high) (M : Type*) [AddCommGroup M] [Module ℰ M] :
    Module 𝒜ᵐᵒᵖ M :=
  moduleRight (k := k) (A := 𝒜) M

local instance (priority := high) (M : Type*) [AddCommGroup M] [Module ℰ M] [Module k M]
    [IsScalarTower k ℰ M] : IsScalarTower k 𝒜 M :=
  moduleLeftIsScalarTower (k := k) (B := 𝒜ᵐᵒᵖ) M

local instance (priority := high) (M : Type*) [AddCommGroup M] [Module ℰ M] [Module k M]
    [IsScalarTower k ℰ M] : IsScalarTower k 𝒜ᵐᵒᵖ M :=
  moduleRightIsScalarTower (k := k) (A := 𝒜) M

local instance (priority := high) (M : Type*) [AddCommGroup M] [Module ℰ M] :
    SMulCommClass 𝒜 𝒜ᵐᵒᵖ M :=
  moduleSMulCommClass (k := k) (A := 𝒜) (B := 𝒜ᵐᵒᵖ) M

local notation "V" => InternalGrading.piece (vertexTensorGrading k Q wt)
local notation "U" => InternalGrading.piece (arrowTensorGrading k Q wt)

/-- The vertex term uses the same restricted left action in its grading and DG structure. -/
noncomputable local instance vertexTensorSMulLeft : SMul 𝒜 (vertexTensorBimodule k Q) :=
  (moduleLeft (k := k) (B := 𝒜ᵐᵒᵖ) (vertexTensorBimodule k Q)).toSMul

local instance : SetLike.GradedSMul (Ξ).piece V :=
  (vertexTensorBimodule k Q).subtype.gradedSMul_of_mem_iff (Ξ).piece V (Ξ).piece
    (mem_vertexTensorGrading_piece_iff k Q wt)

local instance : SetLike.GradedSMul (gradeBy k wt) V :=
  (G).gradedSMul_moduleLeft (G).opposite V

local instance : SetLike.GradedSMul (Γ).opposite.piece V := by
  rw [(G).ofDecomposition_piece_eq]
  exact (G).gradedSMul_moduleRight (G).opposite V

include hdε

/-- The vertex tensor term as a DG bimodule over the path algebra. -/
@[expose, implicit_reducible]
noncomputable def vertexTensorDGBimodule : DGBimoduleCat hd hd :=
  DGBimoduleCat.of (M := vertexTensorBimodule k Q) (hA := hd) (hB := hd) (ℳ := V)
    (dM := vertexTensorBimoduleDifferential wt d)
    (by
      apply IsDGBimodule.of_leibniz_tmul_smul (M := vertexTensorBimodule k Q)
        (hA := hd) (hB := hd) (dM := vertexTensorBimoduleDifferential wt d)
        (vertexTensorGrading k Q wt) (smul_moduleLeft_smul_moduleRight (k := k) _)
        (isHomogeneous_vertexTensorBimoduleDifferential k Q wt d hd hdε)
        (vertexTensorBimoduleDifferential_vertexTensorBimoduleDifferential hd hdε)
      intro p q a ha z hz b
      exact vertexTensorBimoduleDifferential_tmul_smul hd hdε ha hz b)

variable [DecidableEq Q] [∀ i j : Q, DecidableEq (i ⟶ j)]

local instance : SetLike.GradedSMul (Ξ).piece U :=
  (arrowTensorDifferential k Q).gradedSMul_of_mem_iff (Ξ).piece U V (by
    intro q x
    rw [mem_arrowTensorGrading_piece_iff, mem_vertexTensorGrading_piece_iff])

local instance : SetLike.GradedSMul (gradeBy k wt) U :=
  (G).gradedSMul_moduleLeft (G).opposite U

local instance : SetLike.GradedSMul (Γ).opposite.piece U := by
  rw [(G).ofDecomposition_piece_eq]
  exact (G).gradedSMul_moduleRight (G).opposite U

/-- The arrow tensor term as a DG bimodule over the path algebra. -/
@[expose, implicit_reducible]
noncomputable def arrowTensorDGBimodule : DGBimoduleCat hd hd :=
  DGBimoduleCat.of (M := arrowTensorBimodule k Q) (hA := hd) (hB := hd) (ℳ := U)
    (dM := arrowTensorBimoduleDifferential wt d)
    (by
      apply IsDGBimodule.of_leibniz_tmul_smul (M := arrowTensorBimodule k Q)
        (hA := hd) (hB := hd) (dM := arrowTensorBimoduleDifferential wt d)
        (arrowTensorGrading k Q wt) (smul_moduleLeft_smul_moduleRight (k := k) _)
        (isHomogeneous_arrowTensorBimoduleDifferential k Q wt d hd hdε)
        (arrowTensorBimoduleDifferential_arrowTensorBimoduleDifferential hd hdε)
      intro p q a ha z hz b
      exact arrowTensorBimoduleDifferential_tmul_smul hd hdε ha hz b)

end RestrictedActions

/-- The DG vertex term has the original total-weight grading. -/
@[simp]
theorem mem_vertexTensorDGBimodule_grading_iff {q : ℤ}
    {z : vertexTensorDGBimodule hd hdε} :
    z ∈ (vertexTensorDGBimodule hd hdε).grading q ↔
      z ∈ (vertexTensorGrading k Q wt).piece q :=
  (Iff.rfl)

/-- The DG vertex term has the original path-algebra resolution differential. -/
@[simp]
theorem vertexTensorDGBimodule_differential_apply (z : vertexTensorDGBimodule hd hdε) :
    (vertexTensorDGBimodule hd hdε).differential z = vertexTensorBimoduleDifferential wt d z :=
  (rfl)

/-- The left action on the DG vertex term comes from the first tensor factor. -/
@[simp]
theorem vertexTensorDGBimodule_smul_left (a : 𝒜) (z : vertexTensorDGBimodule hd hdε) :
    (a • z : vertexTensorDGBimodule hd hdε) =
      @SMul.smul ℰ ↑(vertexTensorBimodule k Q) _ (a ⊗ₜ[k] (1 : 𝒜ᵐᵒᵖ)) z :=
  (rfl)

/-- The right action on the DG vertex term comes from the second tensor factor. -/
@[simp]
theorem vertexTensorDGBimodule_smul_right (b : 𝒜ᵐᵒᵖ) (z : vertexTensorDGBimodule hd hdε) :
    (b • z : vertexTensorDGBimodule hd hdε) =
      @SMul.smul ℰ ↑(vertexTensorBimodule k Q) _ ((1 : 𝒜) ⊗ₜ[k] b) z :=
  (rfl)

variable [DecidableEq Q] [∀ i j : Q, DecidableEq (i ⟶ j)]

/-- The DG arrow term has the original total-weight grading. -/
@[simp]
theorem mem_arrowTensorDGBimodule_grading_iff {q : ℤ}
    {z : arrowTensorDGBimodule hd hdε} :
    z ∈ (arrowTensorDGBimodule hd hdε).grading q ↔
      z ∈ (arrowTensorGrading k Q wt).piece q :=
  (Iff.rfl)

/-- The DG arrow term has the original path-algebra resolution differential. -/
@[simp]
theorem arrowTensorDGBimodule_differential_apply (z : arrowTensorDGBimodule hd hdε) :
    (arrowTensorDGBimodule hd hdε).differential z = arrowTensorBimoduleDifferential wt d z :=
  (rfl)

/-- The left action on the DG arrow term comes from the first tensor factor. -/
@[simp]
theorem arrowTensorDGBimodule_smul_left (a : 𝒜) (z : arrowTensorDGBimodule hd hdε) :
    (a • z : arrowTensorDGBimodule hd hdε) =
      @SMul.smul ℰ (arrowTensorBimodule k Q) _ (a ⊗ₜ[k] (1 : 𝒜ᵐᵒᵖ)) z :=
  (rfl)

/-- The right action on the DG arrow term comes from the second tensor factor. -/
@[simp]
theorem arrowTensorDGBimodule_smul_right (b : 𝒜ᵐᵒᵖ) (z : arrowTensorDGBimodule hd hdε) :
    (b • z : arrowTensorDGBimodule hd hdε) =
      @SMul.smul ℰ (arrowTensorBimodule k Q) _ ((1 : 𝒜) ⊗ₜ[k] b) z :=
  (rfl)

/-- The boundary of the small resolution as a morphism of DG bimodules. -/
noncomputable def arrowTensorDGBimoduleBoundary :
    arrowTensorDGBimodule hd hdε ⟶ vertexTensorDGBimodule hd hdε := by
  letI := (arrowTensorDGBimodule hd hdε).moduleOp
  letI := (vertexTensorDGBimodule hd hdε).moduleOp
  let f := arrowTensorDifferential k Q
  let f' : arrowTensorDGBimodule hd hdε →ₗ[𝒜ᵐᵒᵖ] vertexTensorDGBimodule hd hdε :=
    { toFun := f
      map_add' := f.map_add
      map_smul' := fun b z ↦ f.map_smul_moduleRight b z }
  have hf' (z : arrowTensorDGBimodule hd hdε) : f' z = f z := rfl
  refine ⟨⟨f', ?_, ?_⟩, (mem_dgBimoduleHomSubmodule _ _ _).mpr ?_⟩
  · intro q z hz
    simpa only [hf', f, add_zero, mem_vertexTensorDGBimodule_grading_iff] using
      (isHomogeneous_arrowTensorDifferential k Q wt).map_mem
        ((mem_arrowTensorDGBimodule_grading_iff hd hdε).mp hz)
  · intro z
    simpa only [hf', f, vertexTensorDGBimodule_differential_apply,
      arrowTensorDGBimodule_differential_apply] using
      (arrowTensorDifferential_arrowTensorBimoduleDifferential hd hdε z).symm
  · intro a z
    simp only [DGRightModuleHom.coe_mk, hf']
    exact f.map_smul_moduleLeft a z

@[simp]
theorem arrowTensorDGBimoduleBoundary_apply (z : arrowTensorDGBimodule hd hdε) :
    arrowTensorDGBimoduleBoundary hd hdε z = arrowTensorDifferential k Q z := by
  rfl

omit [DecidableEq Q] [∀ i j : Q, DecidableEq (i ⟶ j)] in
/-- The multiplication of the vertex term as a morphism to the diagonal bimodule. -/
noncomputable def vertexTensorDGBimoduleMul :
    vertexTensorDGBimodule hd hdε ⟶ DGBimoduleCat.tensorUnit.{0} hd := by
  let f := (Bimodule.of (AlgHom.id k 𝒜)).symm.toLinearMap ∘ₗ (vertexTensorMul k Q).restrictScalars k
  have hf (a b : 𝒜) (z : vertexTensorBimodule k Q) :
      f ((a ⊗ₜ[k] op b) • z) = a * f z * b := by
    apply (Bimodule.of (AlgHom.id k 𝒜)).injective
    simp only [f, LinearMap.comp_apply, LinearMap.restrictScalars_apply,
      LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
    rw [(vertexTensorMul k Q).map_smul (a ⊗ₜ[k] op b) z]
    simpa only [AlgHom.id_apply, unop_op, LinearEquiv.apply_symm_apply] using
      Bimodule.smul_of (AlgHom.id k 𝒜) a (op b)
        ((Bimodule.of (AlgHom.id k 𝒜)).symm (vertexTensorMul k Q z))
  letI := (vertexTensorDGBimodule hd hdε).moduleOp
  letI := (DGBimoduleCat.tensorUnit.{0} hd).moduleOp
  let e := DGBimoduleCat.tensorUnitEquiv.{0} hd
  let f' : vertexTensorDGBimodule hd hdε →ₗ[𝒜ᵐᵒᵖ] DGBimoduleCat.tensorUnit.{0} hd :=
    { toFun := fun z ↦ e (f z)
      map_add' := fun x y ↦ by rw [f.map_add, e.map_add]
      map_smul' := by
        intro b z
        obtain ⟨b, rfl⟩ := MulOpposite.op_surjective b
        rw [RingHom.id_apply, ← one_smul 𝒜 (op b • e (f z))]
        rw [DGBimoduleCat.tensorUnitEquiv_smul]
        refine (congrArg (e ∘ f) (vertexTensorDGBimodule_smul_right hd hdε (op b) z)).trans ?_
        exact (congrArg e (hf 1 b z)).trans (congrArg e (by rw [one_mul])) }
  have hf' (z : vertexTensorDGBimodule hd hdε) : f' z = e (f z) := rfl
  have hdown (z : vertexTensorDGBimodule hd hdε) : (f' z).down = f z := by
    rw [← DGBimoduleCat.tensorUnitEquiv_symm_apply, hf']
    exact e.symm_apply_apply _
  have hleft (a : 𝒜) (z : vertexTensorDGBimodule hd hdε) : f' (a • z) = a • f' z := by
    apply ULift.ext
    rw [DGBimoduleCat.tensorUnit_smul_down, hdown, hdown]
    have h := hf a 1 z
    rw [op_one, mul_one] at h
    exact (congrArg f (vertexTensorDGBimodule_smul_left hd hdε a z)).trans h
  refine ⟨⟨f', ?_, ?_⟩, (mem_dgBimoduleHomSubmodule _ _ _).mpr hleft⟩
  · intro q z hz
    rw [DGBimoduleCat.mem_tensorUnit_grading_iff, hdown]
    simpa only [f, LinearMap.comp_apply, LinearMap.restrictScalars_apply, LinearEquiv.coe_coe,
      add_zero, InternalGrading.mem_map_piece_iff] using
      (isHomogeneous_vertexTensorMul k Q wt).map_mem hz
  · intro z
    apply ULift.ext
    rw [DGBimoduleCat.tensorUnit_differential_apply, ULift.down_up, hdown, hdown]
    simpa only [f, LinearMap.comp_apply, LinearMap.restrictScalars_apply, LinearEquiv.coe_coe,
      LinearEquiv.symm_apply_apply, vertexTensorDGBimodule_differential_apply] using
      congrArg (Bimodule.of (AlgHom.id k 𝒜)).symm
        (vertexTensorMul_vertexTensorBimoduleDifferential hd hdε z).symm

omit [DecidableEq Q] [∀ i j : Q, DecidableEq (i ⟶ j)] in
/-- Under the diagonal bimodule's carrier equivalence, the vertex-term map is the original
path-algebra multiplication map. -/
@[simp]
theorem vertexTensorDGBimoduleMul_down (z : vertexTensorDGBimodule hd hdε) :
    (vertexTensorDGBimoduleMul hd hdε z).down =
      (Bimodule.of (AlgHom.id k 𝒜)).symm (vertexTensorMul k Q z) := by
  rw [← DGBimoduleCat.tensorUnitEquiv_symm_apply]
  exact LinearEquiv.symm_apply_apply (DGBimoduleCat.tensorUnitEquiv.{0} hd) _

/-- Multiplication kills the image of the boundary, so it induces the cone augmentation. -/
@[reassoc (attr := simp)]
theorem arrowTensorDGBimoduleBoundary_comp_vertexTensorDGBimoduleMul :
    arrowTensorDGBimoduleBoundary hd hdε ≫ vertexTensorDGBimoduleMul hd hdε = 0 := by
  ext z
  apply (DGBimoduleCat.tensorUnitEquiv.{0} hd).symm.injective
  rw [DGBimoduleCat.comp_apply, DGBimoduleCat.tensorUnitEquiv_symm_apply,
    vertexTensorDGBimoduleMul_down,
    arrowTensorDGBimoduleBoundary_apply, vertexTensorMul_arrowTensorDifferential,
    DGBimoduleCat.zero_apply, map_zero, map_zero]

/-- The small resolution of the diagonal DG bimodule. Its terms are the vertex tensors and
the suspended arrow tensors, with the standard boundary in the cone differential. -/
@[expose, implicit_reducible]
noncomputable def standardDGBimoduleResolution : DGBimoduleCat hd hd :=
  DGBimoduleCat.cone (arrowTensorDGBimoduleBoundary hd hdε)

/-- The resolution is the cone of the packaged arrow-to-vertex boundary. -/
theorem standardDGBimoduleResolution_eq_cone :
    standardDGBimoduleResolution hd hdε =
      DGBimoduleCat.cone (arrowTensorDGBimoduleBoundary hd hdε) :=
  (rfl)

/-- The differential of a suspended universal derivative has arrow component
`-∂(d x)` and vertex component the boundary of `∂ x`. -/
theorem standardDGBimoduleResolution_differential_shiftEquiv_symm_arrowTensorDerivation (x : 𝒜) :
    (standardDGBimoduleResolution hd hdε).differential
        (((arrowTensorDGBimodule hd hdε).shiftEquiv 1).symm (arrowTensorDerivation k Q x), 0) =
      (-((arrowTensorDGBimodule hd hdε).shiftEquiv 1).symm (arrowTensorDerivation k Q (d x)),
        arrowTensorDifferential k Q (arrowTensorDerivation k Q x)) := by
  -- Read the resolution differential on its cone carrier.
  change (DGBimoduleCat.cone (arrowTensorDGBimoduleBoundary hd hdε)).differential _ = _
  rw [DGBimoduleCat.cone_differential_apply]
  simp only [LinearEquiv.apply_symm_apply, map_zero, add_zero, arrowTensorDGBimoduleBoundary_apply]
  apply Prod.ext
  · apply ((arrowTensorDGBimodule hd hdε).shiftEquiv 1).injective
    simp only [DGBimoduleCat.shiftEquiv_one_differential, LinearEquiv.apply_symm_apply, map_neg,
      arrowTensorDGBimodule_differential_apply]
    exact congrArg Neg.neg (arrowTensorBimoduleDifferential_arrowTensorDerivation hd hdε x)
  · rfl

/-- The resolution augmentation is multiplication on the vertex term. -/
noncomputable def standardDGBimoduleResolutionAugmentation :
    standardDGBimoduleResolution hd hdε ⟶ DGBimoduleCat.tensorUnit.{0} hd :=
  DGBimoduleCat.coneDesc (arrowTensorDGBimoduleBoundary hd hdε)
    (vertexTensorDGBimoduleMul hd hdε)
    (arrowTensorDGBimoduleBoundary_comp_vertexTensorDGBimoduleMul hd hdε)

@[simp]
theorem standardDGBimoduleResolutionAugmentation_apply (z : standardDGBimoduleResolution hd hdε) :
    standardDGBimoduleResolutionAugmentation hd hdε z = vertexTensorDGBimoduleMul hd hdε z.2 := by
  exact DGBimoduleCat.coneDesc_apply _ _ _ z

/-- The small DG bimodule resolution augments to the diagonal by a quasi-isomorphism. -/
theorem isQuasiIso_forgetToRightModuleCat_map_standardDGBimoduleResolutionAugmentation :
    DGRightModuleCat.IsQuasiIso
      (DGBimoduleCat.forgetToRightModuleCat.map
        (standardDGBimoduleResolutionAugmentation hd hdε)) := by
  let e := (Bimodule.of (AlgHom.id k 𝒜)).symm.trans (DGBimoduleCat.tensorUnitEquiv.{0} hd)
  have hmul : (vertexTensorDGBimoduleMul hd hdε : vertexTensorDGBimodule hd hdε → _) =
      e ∘ vertexTensorMul k Q := by
    funext z
    apply ULift.ext
    simp only [vertexTensorDGBimoduleMul_down, Function.comp_apply, e, LinearEquiv.trans_apply,
      DGBimoduleCat.tensorUnitEquiv_apply, ULift.down_up]
  have hboundary : (arrowTensorDGBimoduleBoundary hd hdε : arrowTensorDGBimodule hd hdε → _) =
      arrowTensorDifferential k Q := funext (arrowTensorDGBimoduleBoundary_apply hd hdε)
  apply DGBimoduleCat.isQuasiIso_forgetToRightModuleCat_map_coneDesc
  · rw [hboundary]
    exact arrowTensorDifferential_injective
  · rw [hmul]
    exact e.surjective.comp vertexTensorMul_surjective
  · rw [hboundary, hmul]
    exact (LinearEquiv.postcomp_exact_iff_exact (e := e)
      (f := (arrowTensorDifferential k Q).restrictScalars k)
      (g := (vertexTensorMul k Q).restrictScalars k)).mpr
      exact_arrowTensorDifferential_vertexTensorMul

end TauCeti.PathAlgebra
