/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DG.Bimodule.Cone
public import TauCeti.Algebra.Homology.DG.Bimodule.TensorProduct.Unit
public import TauCeti.RepresentationTheory.Quiver.PathAlgebra.SemifreeResolution.Actions
import TauCeti.RepresentationTheory.Quiver.PathAlgebra.SemifreeResolution.Complex
import TauCeti.RingTheory.GradedAlgebra.TensorProduct

/-!
# The augmented DG bimodule resolution of a DG path algebra

For a finite-vertex quiver, the standard arrow and vertex tensor terms of a DG path algebra
are DG bimodules for the original outer actions and the arrow-weight grading. Their boundary
is a DG bimodule map. Its cone augments to the diagonal bimodule by multiplication, and
this augmentation is a quasi-isomorphism. The construction applies to the uncompleted
two-dimensional Ginzburg algebra, where the suspended generator has degree `-1` for a
doubled arrow and `-2` for an added loop.

## References

* B. Keller, *Deformed Calabi--Yau completions*, Section 6.
* J. Liu and Z. Wang, *A-infinity deformations of zigzag algebras via Ginzburg dg algebras*,
  Proposition 3.2, for the use of the small resolution in computing Hochschild cohomology.
-/

public section

open CategoryTheory MulOpposite
open scoped TensorProduct

namespace TauCeti.PathAlgebra

open TauCeti.Algebra.TensorProduct

universe u v w

variable {k : Type w} [CommRing k] {Q : Type u} [Quiver.{v} Q] [Finite Q]
  {wt : ∀ {i j : Q}, (i ⟶ j) → ℤ} {d : pathAlgebra k Q →ₗ[k] pathAlgebra k Q}
  (hd : IsDGAlgebra (gradeBy k wt) d) (hdε : ∀ i, d (vertexIdempotent k i) = 0)

local notation "𝒜" => pathAlgebra k Q
local notation "ℰ" => 𝒜 ⊗[k] 𝒜ᵐᵒᵖ
local notation "Γ" => InternalGrading.ofDecomposition (gradeBy k wt)
local notation "G" => InternalGrading.mk (gradeBy k wt) (isInternal_gradeBy k wt)
local notation "Ξ" => InternalGrading.tensorProduct (G) (InternalGrading.opposite (G))

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

private theorem tmul_one_smul_mem_tensorPiece {p q : ℤ} {a : 𝒜} {x : ℰ}
    (ha : a ∈ gradeBy k wt p) (hx : x ∈ (Ξ).piece q) :
    (a ⊗ₜ[k] (1 : 𝒜ᵐᵒᵖ)) * x ∈ (Ξ).piece (p + q) := by
  have : SetLike.GradedMul (G).piece := inferInstance
  have : SetLike.GradedMul (G).opposite.piece := inferInstance
  have h1 : (1 : 𝒜ᵐᵒᵖ) ∈ (G).opposite.piece 0 := by
    rw [InternalGrading.mem_opposite_piece_iff, unop_one]
    exact SetLike.one_mem_graded _
  have h := (G).tmul_mem_tensorProduct (G).opposite ha h1
  simpa only [add_zero] using SetLike.mul_mem_graded h hx

private theorem one_tmul_smul_mem_tensorPiece {p q : ℤ} {b : 𝒜ᵐᵒᵖ} {x : ℰ}
    (hb : b ∈ (Γ).opposite.piece p) (hx : x ∈ (Ξ).piece q) :
    ((1 : 𝒜) ⊗ₜ[k] b) * x ∈ (Ξ).piece (p + q) := by
  have : SetLike.GradedMul (G).piece := inferInstance
  have : SetLike.GradedMul (G).opposite.piece := inferInstance
  have h1 : (1 : 𝒜) ∈ (G).piece 0 := SetLike.one_mem_graded _
  have hΓ : (Γ) = (G) :=
    InternalGrading.ext fun _ ↦ congrFun (InternalGrading.ofDecomposition_piece _) _
  rw [hΓ] at hb
  simpa only [zero_add] using
    SetLike.mul_mem_graded ((G).tmul_mem_tensorProduct (G).opposite h1 hb) hx

private theorem isDGBimodule_of_tensorLeibniz {M : Type*} [AddCommGroup M] [Module k M]
    [Module ℰ M] [IsScalarTower k ℰ M]
    {𝒢 : InternalGrading k M ℤ} {D : M →ₗ[k] M}
    [SetLike.GradedSMul (gradeBy k wt) 𝒢.piece]
    [SetLike.GradedSMul (Γ).opposite.piece 𝒢.piece]
    (hD : LinearMap.IsHomogeneous D 𝒢.piece 𝒢.piece 1) (hD₂ : ∀ x, D (D x) = 0)
    (hLeibniz : ∀ {p q : ℤ} {a : 𝒜}, a ∈ gradeBy k wt p →
      ∀ {z : M}, z ∈ 𝒢.piece q → ∀ (b : 𝒜),
      D ((a ⊗ₜ[k] op b) • z) =
        (d a ⊗ₜ[k] op b) • z +
          negOnePowCast k p • ((a ⊗ₜ[k] op b) • D z) +
          negOnePowCast k (p + q) • ((a ⊗ₜ[k] op (d b)) • z)) :
    IsDGBimodule hd hd 𝒢.piece D where
  isHomogeneous := hD
  sq_zero := hD₂
  leibniz := by
    intro p a ha z
    -- Both sides are additive in the module element, so test on its homogeneous summands.
    generalize he : DirectSum.decompose 𝒢.piece z = x
    rw [← (DirectSum.decompose 𝒢.piece).symm_apply_apply z, he]
    clear he z
    induction x using DirectSum.induction_on with
    | zero => simp
    | add x y hx hy =>
      simp only [DirectSum.decompose_symm_add, map_add, smul_add, hx, hy]
      abel
    | of q x =>
      rw [DirectSum.decompose_symm_of]
      have h := hLeibniz ha x.property 1
      rw [op_one, hd.map_one_eq_zero, op_zero, TensorProduct.tmul_zero, zero_smul ℰ (x : M),
        smul_zero, add_zero] at h
      simpa only [smul_moduleLeft, negOnePow_smul_eq_negOnePowCast_smul (R := k)] using h
  leibniz_right := by
    intro q z hz b
    have h := hLeibniz (SetLike.one_mem_graded (gradeBy k wt)) hz b
    rw [hd.map_one_eq_zero, TensorProduct.zero_tmul, zero_smul ℰ z, zero_add] at h
    simpa only [smul_moduleRight, negOnePowCast_zero, one_smul, zero_add,
      negOnePow_smul_eq_negOnePowCast_smul (R := k)] using h

variable [Fintype Q]

local notation "V" => InternalGrading.piece (vertexTensorGrading k Q wt)
local notation "U" => InternalGrading.piece (arrowTensorGrading k Q wt)

/-- The vertex term uses the same restricted left action in its grading and DG structure. -/
noncomputable local instance vertexTensorSMulLeft : SMul 𝒜 (vertexTensorBimodule k Q) :=
  (moduleLeft (k := k) (B := 𝒜ᵐᵒᵖ) (vertexTensorBimodule k Q)).toSMul

local instance : SetLike.GradedSMul (gradeBy k wt) V where
  smul_mem := by
    intro p q a z ha hz
    rw [mem_vertexTensorGrading_piece_iff] at hz ⊢
    -- The left action on vertex tensors is multiplication by the first-factor inclusion.
    change (a ⊗ₜ[k] (1 : 𝒜ᵐᵒᵖ)) * (z : ℰ) ∈ (Ξ).piece (p + q)
    exact tmul_one_smul_mem_tensorPiece ha hz

local instance : SetLike.GradedSMul (Γ).opposite.piece V where
  smul_mem := by
    intro p q b z hb hz
    rw [mem_vertexTensorGrading_piece_iff] at hz ⊢
    simpa only [smul_moduleRight, Submodule.coe_smul, smul_eq_mul, vadd_eq_add] using
      one_tmul_smul_mem_tensorPiece hb hz

include hdε

/-- The vertex tensor term as a DG bimodule over the path algebra. -/
noncomputable abbrev vertexTensorDGBimodule : DGBimoduleCat hd hd :=
  DGBimoduleCat.of (M := vertexTensorBimodule k Q) (hA := hd) (hB := hd) (ℳ := V)
    (dM := vertexTensorBimoduleDifferential wt d)
    (by
      exact isDGBimodule_of_tensorLeibniz hd (M := vertexTensorBimodule k Q)
        (𝒢 := vertexTensorGrading k Q wt) (D := vertexTensorBimoduleDifferential wt d)
        (isHomogeneous_vertexTensorBimoduleDifferential k Q wt d hd hdε)
        (vertexTensorBimoduleDifferential_vertexTensorBimoduleDifferential hd hdε)
        (fun {_ _ _} ha {_} hz b ↦ vertexTensorBimoduleDifferential_tmul_smul hd hdε ha hz b))

variable [DecidableEq Q] [∀ i j : Q, DecidableEq (i ⟶ j)]

local instance : SetLike.GradedSMul (gradeBy k wt) U where
  smul_mem := by
    intro p q a z ha hz
    rw [mem_arrowTensorGrading_piece_iff] at hz ⊢
    simpa only [smul_moduleLeft, map_smul, Submodule.coe_smul, smul_eq_mul, vadd_eq_add] using
      tmul_one_smul_mem_tensorPiece ha hz

local instance : SetLike.GradedSMul (Γ).opposite.piece U where
  smul_mem := by
    intro p q b z hb hz
    rw [mem_arrowTensorGrading_piece_iff] at hz ⊢
    simpa only [smul_moduleRight, map_smul, Submodule.coe_smul, smul_eq_mul, vadd_eq_add] using
      one_tmul_smul_mem_tensorPiece hb hz

/-- The arrow tensor term as a DG bimodule, with the differential twisted by the
universal derivation of the arrow differentials. -/
noncomputable abbrev arrowTensorDGBimodule : DGBimoduleCat hd hd :=
  DGBimoduleCat.of (M := arrowTensorBimodule k Q) (hA := hd) (hB := hd) (ℳ := U)
    (dM := arrowTensorBimoduleDifferential wt d)
    (by
      exact isDGBimodule_of_tensorLeibniz hd (M := arrowTensorBimodule k Q)
        (𝒢 := arrowTensorGrading k Q wt) (D := arrowTensorBimoduleDifferential wt d)
        (isHomogeneous_arrowTensorBimoduleDifferential k Q wt d hd hdε)
        (arrowTensorBimoduleDifferential_arrowTensorBimoduleDifferential hd hdε)
        (fun {_ _ _} ha {_} hz b ↦ arrowTensorBimoduleDifferential_tmul_smul hd hdε ha hz b))

/-- The boundary of the small resolution as a morphism of DG bimodules. -/
noncomputable def arrowTensorDGBimoduleBoundary :
    arrowTensorDGBimodule hd hdε ⟶ vertexTensorDGBimodule hd hdε := by
  letI := (arrowTensorDGBimodule hd hdε).moduleOp
  letI := (vertexTensorDGBimodule hd hdε).moduleOp
  let f := arrowTensorDifferential k Q
  let f' : arrowTensorDGBimodule hd hdε →ₗ[𝒜ᵐᵒᵖ] vertexTensorDGBimodule hd hdε :=
    { toFun := f
      map_add' := f.map_add
      map_smul' := fun b z ↦ f.map_smul ((1 : 𝒜) ⊗ₜ[k] b) z }
  refine ⟨⟨f', ?_, ?_⟩, (mem_dgBimoduleHomSubmodule _ _ _).mpr ?_⟩
  · intro q z hz
    -- The packaged map has the original boundary as its underlying function.
    change f z ∈ V q
    simpa only [f, add_zero] using (isHomogeneous_arrowTensorDifferential k Q wt).map_mem hz
  · exact fun z ↦ (arrowTensorDifferential_arrowTensorBimoduleDifferential hd hdε z).symm
  · exact fun a z ↦ f.map_smul (a ⊗ₜ[k] (1 : 𝒜ᵐᵒᵖ)) z

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
        -- The source action is through the right tensor factor.
        change e (f (((1 : 𝒜) ⊗ₜ[k] op b) • z)) = e (1 * f z * b)
        simpa only [one_mul] using congrArg e (hf 1 b z) }
  have hdown (z : vertexTensorDGBimodule hd hdε) : (f' z).down = f z := by
    -- Evaluation of the packaged map lands in the lifted diagonal.
    change (DGBimoduleCat.tensorUnitEquiv.{0} hd (f z)).down = f z
    rw [DGBimoduleCat.tensorUnitEquiv_apply, ULift.down_up]
  refine ⟨⟨f', ?_, ?_⟩, (mem_dgBimoduleHomSubmodule _ _ _).mpr ?_⟩
  · intro q z hz
    rw [DGBimoduleCat.mem_tensorUnit_grading_iff, hdown]
    simpa only [f, LinearMap.comp_apply, LinearMap.restrictScalars_apply, LinearEquiv.coe_coe,
      add_zero, InternalGrading.mem_map_piece_iff] using
      (isHomogeneous_vertexTensorMul k Q wt).map_mem hz
  · intro z
    apply ULift.ext
    rw [DGBimoduleCat.tensorUnit_differential_apply, ULift.down_up, hdown, hdown]
    simpa only [f, LinearMap.comp_apply, LinearMap.restrictScalars_apply, LinearEquiv.coe_coe,
      LinearEquiv.symm_apply_apply] using congrArg (Bimodule.of (AlgHom.id k 𝒜)).symm
        (vertexTensorMul_vertexTensorBimoduleDifferential hd hdε z).symm
  · intro a z
    apply ULift.ext
    -- Read the target action on the algebra underlying the diagonal bimodule.
    change (f' (a • z)).down = (a • f' z).down
    rw [DGBimoduleCat.tensorUnit_smul_down, hdown, hdown]
    -- The source action is through the left tensor factor.
    change f ((a ⊗ₜ[k] (1 : 𝒜ᵐᵒᵖ)) • z) = a * f z
    simpa only [op_one, mul_one] using hf a 1 z

omit [DecidableEq Q] [∀ i j : Q, DecidableEq (i ⟶ j)] in
/-- Under the diagonal bimodule's carrier equivalence, the augmentation is the original
path-algebra multiplication map. -/
theorem vertexTensorDGBimoduleMul_apply (z : vertexTensorDGBimodule hd hdε) :
    (DGBimoduleCat.tensorUnitEquiv.{0} hd).symm (vertexTensorDGBimoduleMul hd hdε z) =
      (Bimodule.of (AlgHom.id k 𝒜)).symm (vertexTensorMul k Q z) := by
  exact LinearEquiv.symm_apply_apply (DGBimoduleCat.tensorUnitEquiv.{0} hd) _

@[reassoc (attr := simp)]
theorem arrowTensorDGBimoduleBoundary_comp_vertexTensorDGBimoduleMul :
    arrowTensorDGBimoduleBoundary hd hdε ≫ vertexTensorDGBimoduleMul hd hdε = 0 := by
  ext z
  apply (DGBimoduleCat.tensorUnitEquiv.{0} hd).symm.injective
  rw [DGBimoduleCat.comp_apply, vertexTensorDGBimoduleMul_apply,
    arrowTensorDGBimoduleBoundary_apply, vertexTensorMul_arrowTensorDifferential,
    DGBimoduleCat.zero_apply, map_zero, map_zero]

/-- The small resolution of the diagonal DG bimodule. Its terms are the vertex tensors and
the suspended arrow tensors, with the standard boundary in the cone differential. -/
noncomputable abbrev dgBimoduleResolution : DGBimoduleCat hd hd :=
  DGBimoduleCat.mappingCone (arrowTensorDGBimoduleBoundary hd hdε)

/-- The differential of a suspended universal derivative has arrow component
`-∂(d x)` and vertex component the boundary of `∂ x`. For a Ginzburg loop this
uses the universal derivative of its preprojective relator. -/
theorem dgBimoduleResolution_differential_suspendedDerivation (x : 𝒜) :
    let e := (arrowTensorDGBimodule hd hdε).shiftEquiv 1
    (dgBimoduleResolution hd hdε).differential
        (e.symm (arrowTensorDerivation k Q x), 0) =
      (-e.symm (arrowTensorDerivation k Q (d x)),
        arrowTensorDifferential k Q (arrowTensorDerivation k Q x)) := by
  intro e
  calc
    _ = ((arrowTensorDGBimodule hd hdε |>.shift 1).differential
          (e.symm (arrowTensorDerivation k Q x)),
        arrowTensorDGBimoduleBoundary hd hdε (e (e.symm (arrowTensorDerivation k Q x))) +
          (vertexTensorDGBimodule hd hdε).differential 0) :=
      DGBimoduleCat.mappingCone_differential_apply (arrowTensorDGBimoduleBoundary hd hdε) _
    _ = _ := by
      rw [LinearEquiv.apply_symm_apply, map_zero, add_zero, arrowTensorDGBimoduleBoundary_apply]
      apply Prod.ext
      · apply e.injective
        calc
          _ = (1 : ℤ).negOnePow • (arrowTensorDGBimodule hd hdε).differential
              (e (e.symm (arrowTensorDerivation k Q x))) :=
            DGBimoduleCat.shiftEquiv_differential (arrowTensorDGBimodule hd hdε) 1 _
          _ = _ := by
            simp only [LinearEquiv.apply_symm_apply, Int.negOnePow_one, Units.neg_smul,
              one_smul, map_neg]
            exact congrArg Neg.neg (arrowTensorBimoduleDifferential_arrowTensorDerivation hd hdε x)
      · rfl

/-- The resolution augmentation is multiplication on the vertex term. -/
noncomputable def dgBimoduleResolutionAugmentation :
    dgBimoduleResolution hd hdε ⟶ DGBimoduleCat.tensorUnit.{0} hd :=
  DGBimoduleCat.mappingConeDesc (arrowTensorDGBimoduleBoundary hd hdε)
    (vertexTensorDGBimoduleMul hd hdε)
    (arrowTensorDGBimoduleBoundary_comp_vertexTensorDGBimoduleMul hd hdε)

@[simp]
theorem dgBimoduleResolutionAugmentation_apply (z : dgBimoduleResolution hd hdε) :
    dgBimoduleResolutionAugmentation hd hdε z = vertexTensorDGBimoduleMul hd hdε z.2 := by
  exact DGBimoduleCat.mappingConeDesc_apply _ _ _ z

/-- The small DG bimodule resolution augments to the diagonal by a quasi-isomorphism. -/
theorem isQuasiIso_dgBimoduleResolutionAugmentation :
    DGRightModuleCat.IsQuasiIso
      (DGBimoduleCat.forgetToRightModuleCat.map (dgBimoduleResolutionAugmentation hd hdε)) := by
  apply DGBimoduleCat.isQuasiIso_mappingConeDesc
  · intro x y hxy
    rw [arrowTensorDGBimoduleBoundary_apply, arrowTensorDGBimoduleBoundary_apply] at hxy
    exact arrowTensorDifferential_injective hxy
  · intro a
    obtain ⟨z, hz⟩ := vertexTensorMul_surjective (k := k) (Q := Q)
      (Bimodule.of (AlgHom.id k 𝒜) ((DGBimoduleCat.tensorUnitEquiv.{0} hd).symm a))
    refine ⟨z, (DGBimoduleCat.tensorUnitEquiv.{0} hd).symm.injective ?_⟩
    rw [vertexTensorDGBimoduleMul_apply, hz, LinearEquiv.symm_apply_apply]
  · intro z
    have hm : vertexTensorDGBimoduleMul hd hdε z = 0 ↔ vertexTensorMul k Q z = 0 := by
      rw [← LinearEquiv.map_eq_zero_iff (DGBimoduleCat.tensorUnitEquiv.{0} hd).symm,
        vertexTensorDGBimoduleMul_apply, LinearEquiv.map_eq_zero_iff]
    rw [hm, exact_arrowTensorDifferential_vertexTensorMul]
    constructor
    · rintro ⟨x, hx⟩
      exact ⟨x, (arrowTensorDGBimoduleBoundary_apply hd hdε x).trans hx⟩
    · rintro ⟨x, hx⟩
      exact ⟨x, (arrowTensorDGBimoduleBoundary_apply hd hdε x).symm.trans hx⟩

end TauCeti.PathAlgebra
