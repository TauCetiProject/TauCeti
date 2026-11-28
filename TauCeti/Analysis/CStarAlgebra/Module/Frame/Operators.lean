/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Module.Frame.Basic
public import TauCeti.Analysis.CStarAlgebra.Module.Matrix

/-!
# Analysis and synthesis operators for finite frames

For a finite family `x : ι → E` in a Hilbert C⋆-module over a (possibly non-unital) C⋆-algebra
`A`, this file defines the adjointable synthesis and analysis operators between the standard module
`A^ι = C⋆ᵐᵒᵈ(A, ι → A)` and `E`:

* `TauCeti.AdjointableMap.synthesis A x`: `a ↦ ∑ i, a i • x i`, from `C⋆ᵐᵒᵈ(A, ι → A)` to `E`.
* `TauCeti.AdjointableMap.analysis A x`: `z ↦ (⟪x i, z⟫_A)_i`, the adjoint of synthesis.

Over arbitrary (possibly non-unital) C⋆-algebras `A`, `x` is a Parseval frame iff synthesis after
analysis is `id_E`, iff the analysis operator preserves the `A`-valued inner product; moreover any
module admitting a finite Parseval frame is automatically complete
(`CStarModule.IsParsevalFrame.completeSpace`), and for right Hilbert `A`-modules `x` is a Parseval
frame iff its Gram matrix is a star projection and its synthesis operator is surjective.

Over a unital C⋆-algebra `A`, `TauCeti.CStarModule.opSynthesisLinearMap` and
`TauCeti.CStarModule.opAnalysisLinearMap` express these operators as right `A`-linear maps between
`E` and `C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A)`, where `opAnalysisLinearMap A x ∘ opSynthesisLinearMap A x` is
`CStarMatrix.mulVecLinearMap (CStarMatrix.gram A x)`.

## Main declarations

* `TauCeti.AdjointableMap.synthesis`, `TauCeti.AdjointableMap.analysis`,
  `TauCeti.AdjointableMap.adjoint_synthesis`, `TauCeti.AdjointableMap.adjoint_analysis`
* `TauCeti.AdjointableMap.isParsevalFrame_iff_synthesis_comp_analysis_eq_id`,
  `TauCeti.AdjointableMap.isParsevalFrame_iff_inner_analysis_analysis`
* `CStarModule.IsParsevalFrame.isStarProjection_analysis_comp_synthesis`,
  `CStarModule.IsParsevalFrame.completeSpace`,
  `TauCeti.CStarModule.isParsevalFrame_iff_isStarProjection_gram_and_synthesis_surjective`
* `TauCeti.CStarModule.piOpEquiv`, `TauCeti.CStarModule.opSynthesisLinearMap`,
  `TauCeti.CStarModule.opAnalysisLinearMap`
-/

public section

open CStarModule MulOpposite WithCStarModule
open CStarMatrix (mulVecCLM mulVecLinearMap)

namespace TauCeti.AdjointableMap

variable {A E ι : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul A E] [CStarModule A E] [Fintype ι]

/-! ### Synthesis and analysis operators -/

section Operators

variable (A) in
/-- The bounded complex-linear map `a ↦ ∑ i, a i • x i` underlying `synthesis A x`. -/
private noncomputable def synthesisCLM (x : ι → E) : C⋆ᵐᵒᵈ(A, ι → A) →L[ℂ] E :=
  LinearMap.mkContinuous
    { toFun a := ∑ i, a i • x i
      map_add' a b := by simp [CStarModule.add_smul, Finset.sum_add_distrib]
      map_smul' c a := by
        simp [Finset.smul_sum, (CStarModule.isScalarTower A E).smul_assoc] }
    (∑ i, ‖x i‖) fun a ↦ by
      refine (norm_sum_le _ _).trans ?_
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum fun i _ ↦ (CStarModule.norm_smul_le _ _).trans ?_
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_left (norm_apply_le_norm a i) (norm_nonneg _)

variable (A) in
/-- The bounded complex-linear map `z ↦ (⟪x i, z⟫_A)_i` underlying `analysis A x`. -/
private noncomputable def analysisCLM (x : ι → E) : E →L[ℂ] C⋆ᵐᵒᵈ(A, ι → A) :=
  LinearMap.mkContinuous
    { toFun z := (WithCStarModule.equiv A (ι → A)).symm fun i ↦ inner A (x i) z
      map_add' z w := by ext i; simp [CStarModule.inner_add_right]
      map_smul' c z := by ext i; simp [inner_smul_right_complex] }
    (∑ i, ‖x i‖) fun z ↦ by
      refine (pi_norm_le_sum_norm _).trans ?_
      rw [Finset.sum_mul]
      exact Finset.sum_le_sum fun i _ ↦ CStarModule.norm_inner_le E

variable (A) in
/-- The synthesis operator `a ↦ ∑ i, a i • x i` of a finite family `x : ι → E`, from the standard
module `A^ι = C⋆ᵐᵒᵈ(A, ι → A)` to `E`. Its adjoint is the analysis operator `analysis A x`. For
right Hilbert `B`-modules (`A = Bᵐᵒᵖ`) it is `a ↦ ∑ i, x i a i`. -/
noncomputable def synthesis (x : ι → E) : AdjointableMap A C⋆ᵐᵒᵈ(A, ι → A) E where
  toContinuousLinearMap := synthesisCLM A x
  adjoint' := analysisCLM A x
  inner_map_eq' a z := by
    simp [synthesisCLM, analysisCLM, pi_inner, WithCStarModule.inner_def, inner_sum_left,
      inner_op_smul_left]

variable (A) in
/-- The analysis operator `z ↦ (⟪x i, z⟫_A)_i` of a finite family `x : ι → E`, from `E` to the
standard module `A^ι = C⋆ᵐᵒᵈ(A, ι → A)`: the adjoint of the synthesis operator. -/
noncomputable def analysis (x : ι → E) : AdjointableMap A E C⋆ᵐᵒᵈ(A, ι → A) :=
  (synthesis A x).adjoint

@[simp]
theorem synthesis_apply (x : ι → E) (a : C⋆ᵐᵒᵈ(A, ι → A)) :
    synthesis A x a = ∑ i, a i • x i :=
  (rfl)

@[simp]
theorem analysis_apply (x : ι → E) (z : E) (i : ι) : analysis A x z i = inner A (x i) z := by
  simp [analysis, synthesis, analysisCLM]

@[simp]
theorem adjoint_synthesis (x : ι → E) : (synthesis A x).adjoint = analysis A x :=
  (rfl)

@[simp]
theorem adjoint_analysis (x : ι → E) : (analysis A x).adjoint = synthesis A x :=
  adjoint_adjoint _

/-- The synthesis operator sends the `i`-th coordinate vector with entry `a` to `a • x i`. -/
theorem synthesis_single [DecidableEq ι] (x : ι → E) (i : ι) (a : A) :
    synthesis A x ((WithCStarModule.equiv A (ι → A)).symm (Pi.single i a)) = a • x i := by
  rw [synthesis_apply, Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    simp [Pi.single_eq_of_ne hj, (CStarModule.smulWithZero A E).zero_smul]
  · simp

/-- Analysis after synthesis has entries `∑ j, a j * ⟪x i, x j⟫_A`. -/
theorem analysis_synthesis_apply (x : ι → E) (a : C⋆ᵐᵒᵈ(A, ι → A)) (i : ι) :
    analysis A x (synthesis A x a) i = ∑ j, a j * inner A (x i) (x j) := by
  simp [inner_sum_right, inner_op_smul_right]

/-- For a right Hilbert `B`-module, analysis after synthesis is left multiplication by the Gram
matrix: its `i`-th entry is `∑ j, ⟨x i, x j⟩_B a j`. -/
theorem unop_analysis_synthesis_apply {B E₁ : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B]
    [StarOrderedRing B] [NormedAddCommGroup E₁] [NormedSpace ℂ E₁] [SMul Bᵐᵒᵖ E₁]
    [CStarModule Bᵐᵒᵖ E₁] (x : ι → E₁) (a : C⋆ᵐᵒᵈ(Bᵐᵒᵖ, ι → Bᵐᵒᵖ)) (i : ι) :
    unop (analysis Bᵐᵒᵖ x (synthesis Bᵐᵒᵖ x a) i) =
      ∑ j, CStarMatrix.gram B x i j * unop (a j) := by
  simp [Finset.unop_sum, inner_sum_right, inner_op_smul_right]

private theorem unop_analysis_synthesis_eq_mulVecCLM {B E₁ : Type*} [NonUnitalCStarAlgebra B]
    [PartialOrder B] [StarOrderedRing B] [NormedAddCommGroup E₁] [NormedSpace ℂ E₁]
    [SMul Bᵐᵒᵖ E₁] [CStarModule Bᵐᵒᵖ E₁] (x : ι → E₁) (a : C⋆ᵐᵒᵈ(Bᵐᵒᵖ, ι → Bᵐᵒᵖ)) (i : ι) :
    unop (analysis Bᵐᵒᵖ x (synthesis Bᵐᵒᵖ x a) i) =
      CStarMatrix.mulVecCLM (CStarMatrix.gram B x)
        ((WithCStarModule.equiv Bᵐᵒᵖ (ι → B)).symm fun j ↦ unop (a j)) i := by
  rw [unop_analysis_synthesis_apply, CStarMatrix.mulVecCLM_apply_apply]
  simp

end Operators

/-! ### Parseval frames -/

section Parseval

/-- A family is a Parseval frame exactly when synthesis after analysis is the identity. -/
theorem isParsevalFrame_iff_synthesis_comp_analysis_eq_id {x : ι → E} :
    IsParsevalFrame A x ↔ (synthesis A x).comp (analysis A x) = .id A E := by
  simp [isParsevalFrame_iff, AdjointableMap.ext_iff]

/-- A family is a Parseval frame exactly when its analysis operator preserves the `A`-valued inner
product: `∑ i, ⟪x i, w⟫_A * star ⟪x i, z⟫_A = ⟪z, w⟫_A` for all `z, w`. For right Hilbert
`B`-modules this is `∑ i, ⟨z, x i⟩_B ⟨x i, w⟩_B = ⟨z, w⟩_B`. -/
theorem isParsevalFrame_iff_inner_analysis_analysis {x : ι → E} :
    IsParsevalFrame A x ↔
      ∀ z w : E, inner A (analysis A x z) (analysis A x w) = inner A z w := by
  rw [isParsevalFrame_iff_synthesis_comp_analysis_eq_id, ← adjoint_analysis,
    adjoint_comp_self_eq_id_iff_inner_map_map]

end Parseval

end TauCeti.AdjointableMap

namespace CStarModule.IsParsevalFrame

open TauCeti TauCeti.AdjointableMap

variable {A E ι : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul A E] [CStarModule A E] [Fintype ι]
  {x : ι → E}

/-- For a Parseval frame, synthesis after analysis is the identity. -/
theorem synthesis_comp_analysis_eq_id (hx : IsParsevalFrame A x) :
    (synthesis A x).comp (analysis A x) = .id A E :=
  isParsevalFrame_iff_synthesis_comp_analysis_eq_id.mp hx

/-- The analysis operator of a Parseval frame preserves the `A`-valued inner product. -/
theorem inner_analysis_analysis (hx : IsParsevalFrame A x) (z w : E) :
    inner A (analysis A x z) (analysis A x w) = inner A z w :=
  isParsevalFrame_iff_inner_analysis_analysis.mp hx z w

/-- The analysis operator of a Parseval frame is isometric. -/
theorem norm_analysis_apply (hx : IsParsevalFrame A x) (z : E) : ‖analysis A x z‖ = ‖z‖ :=
  norm_map_of_adjoint_comp_self_eq_id
    (by rw [adjoint_analysis]; exact hx.synthesis_comp_analysis_eq_id) z

/-- For a Parseval frame, analysis after synthesis is a projection on the standard module
`A^ι = C⋆ᵐᵒᵈ(A, ι → A)`. -/
theorem isStarProjection_analysis_comp_synthesis (hx : IsParsevalFrame A x) :
    IsStarProjection ((analysis A x).comp (synthesis A x)) := by
  rw [← adjoint_analysis]
  refine isStarProjection_self_comp_adjoint_of_adjoint_comp_self_eq_id ?_
  rw [adjoint_analysis]
  exact hx.synthesis_comp_analysis_eq_id

end CStarModule.IsParsevalFrame

namespace TauCeti.CStarModule

open TauCeti

section NonUnital

/-- Over any (possibly non-unital) C⋆-algebra `A`, every Hilbert C⋆-module admitting a finite
Parseval frame is automatically complete. -/
theorem _root_.CStarModule.IsParsevalFrame.completeSpace {A ι E : Type*} [Fintype ι]
    [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    [SeminormedAddCommGroup E] [NormedSpace ℂ E] [SMul A E] [CStarModule A E]
    {x : ι → E} (hx : IsParsevalFrame A x) : CompleteSpace E := by
  let : NormedAddCommGroup E := normedAddCommGroupOfCStarModule A E
  let f : E →ₗᵢ[ℂ] C⋆ᵐᵒᵈ(A, ι → A) :=
    (AdjointableMap.analysis A x).toContinuousLinearMap.toLinearMap.isometryOfInnerCStarModule
      fun z ↦ hx.inner_analysis_analysis z z
  exact f.isometry.isUniformInducing.completeSpace
    (Function.LeftInverse.isClosed_range (fun z ↦ by simpa [f] using hx.sum_inner_smul z)
      (AdjointableMap.synthesis A x).continuous f.continuous).isComplete

/-- Over any C⋆-algebra (possibly non-unital), a finite family `x` in a right Hilbert `A`-module
is a Parseval frame iff its Gram matrix is a star projection and its synthesis operator is
surjective. -/
theorem isParsevalFrame_iff_isStarProjection_gram_and_synthesis_surjective {A ι E : Type*}
    [Fintype ι] [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    [SeminormedAddCommGroup E] [NormedSpace ℂ E] [SMul Aᵐᵒᵖ E] [CStarModule Aᵐᵒᵖ E]
    {x : ι → E} :
    IsParsevalFrame Aᵐᵒᵖ x ↔
      IsStarProjection (CStarMatrix.gram A x) ∧
        let : NormedAddCommGroup E := normedAddCommGroupOfCStarModule Aᵐᵒᵖ E
        Function.Surjective (AdjointableMap.synthesis Aᵐᵒᵖ x) := by
  let : NormedAddCommGroup E := normedAddCommGroupOfCStarModule Aᵐᵒᵖ E
  refine ⟨fun hx ↦ ⟨CStarMatrix.isStarProjection_gram hx, fun z ↦
    ⟨AdjointableMap.analysis Aᵐᵒᵖ x z, by simpa using hx.sum_inner_smul z⟩⟩,
    fun ⟨hp, hsurj⟩ ↦ isParsevalFrame_iff.mpr fun z ↦ ?_⟩
  obtain ⟨v, rfl⟩ := hsurj z
  set w := AdjointableMap.analysis Aᵐᵒᵖ x (AdjointableMap.synthesis Aᵐᵒᵖ x v) - v
  have haw : AdjointableMap.analysis Aᵐᵒᵖ x (AdjointableMap.synthesis Aᵐᵒᵖ x w) = 0 := by
    let v' : C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A) := (WithCStarModule.equiv Aᵐᵒᵖ (ι → A)).symm fun j ↦ unop (v j)
    have hw' : ((WithCStarModule.equiv Aᵐᵒᵖ (ι → A)).symm fun j ↦ unop (w j)) =
        CStarMatrix.mulVecCLM (CStarMatrix.gram A x) v' - v' := by
      ext j
      simp [w, v']
    ext i
    apply unop_injective
    rw [AdjointableMap.unop_analysis_synthesis_eq_mulVecCLM, hw', map_sub,
      CStarMatrix.mulVecCLM_mulVecCLM, hp.isIdempotentElem.eq, sub_self]
    simp
  have hΦw : AdjointableMap.synthesis Aᵐᵒᵖ x w = 0 :=
    (_root_.CStarModule.inner_self (A := Aᵐᵒᵖ)).mp <| by
      rw [← (AdjointableMap.synthesis Aᵐᵒᵖ x).adjoint_inner_right,
        AdjointableMap.adjoint_synthesis, haw]
      simp
  rw [map_sub, sub_eq_zero] at hΦw
  simpa only [AdjointableMap.synthesis_apply, AdjointableMap.analysis_apply] using hΦw

end NonUnital

/-! ### Right-module coordinate operators -/

section OpLinear

/-- Right `A`-linear identification between `C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A)` and
`C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → Aᵐᵒᵖ)`. -/
def piOpEquiv (A ι : Type*) [Ring A] :
    C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A) ≃ₗ[Aᵐᵒᵖ] C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → Aᵐᵒᵖ) :=
  (TauCeti.WithCStarModule.piOpLinearEquiv A ι).trans
    (_root_.WithCStarModule.linearEquiv Aᵐᵒᵖ Aᵐᵒᵖ (ι → Aᵐᵒᵖ)).symm

@[simp]
theorem piOpEquiv_apply {A ι : Type*} [Ring A] (v : C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A)) (i : ι) :
    piOpEquiv A ι v i = op (v i) := by
  simp [piOpEquiv]

@[simp]
theorem piOpEquiv_symm_apply {A ι : Type*} [Ring A] (v : C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → Aᵐᵒᵖ)) (i : ι) :
    (piOpEquiv A ι).symm v i = unop (v i) := by
  simp [piOpEquiv]

/-- `piOpEquiv A ι` preserves the `Aᵐᵒᵖ`-valued inner product. -/
theorem inner_piOpEquiv {A ι : Type*} [Fintype ι] [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] (v w : C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A)) :
    inner Aᵐᵒᵖ (piOpEquiv A ι v) (piOpEquiv A ι w) = inner Aᵐᵒᵖ v w := by
  simp [WithCStarModule.pi_inner, CStarModule.inner_op_op]

variable {A ι E : Type*} [Fintype ι] [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [Module Aᵐᵒᵖ E] [CStarModule Aᵐᵒᵖ E]

variable (A) in
/-- Right `A`-linear synthesis map `v ↦ ∑ i, op (v i) • x i` from `C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A)` to `E`. -/
noncomputable def opSynthesisLinearMap (x : ι → E) : C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A) →ₗ[Aᵐᵒᵖ] E :=
  (AdjointableMap.synthesis Aᵐᵒᵖ x).toCoeffLinearMap.comp (piOpEquiv A ι).toLinearMap

@[simp]
theorem opSynthesisLinearMap_apply (x : ι → E) (v : C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A)) :
    opSynthesisLinearMap A x v = ∑ i, op (v i) • x i := by
  simp [opSynthesisLinearMap]

variable (A) in
/-- Right `A`-linear analysis map `z ↦ (⟨x i, z⟩_A)_i` from `E` to `C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A)`. -/
noncomputable def opAnalysisLinearMap (x : ι → E) : E →ₗ[Aᵐᵒᵖ] C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A) :=
  (piOpEquiv A ι).symm.toLinearMap.comp (AdjointableMap.analysis Aᵐᵒᵖ x).toCoeffLinearMap

@[simp]
theorem opAnalysisLinearMap_apply_apply (x : ι → E) (z : E) (i : ι) :
    opAnalysisLinearMap A x z i = unop (inner Aᵐᵒᵖ (x i) z) := by
  simp [opAnalysisLinearMap]

/-- For a Parseval frame `x`, `opSynthesisLinearMap A x` is a left inverse to
`opAnalysisLinearMap A x`. -/
theorem opSynthesisLinearMap_opAnalysisLinearMap {x : ι → E} (hx : IsParsevalFrame Aᵐᵒᵖ x)
    (z : E) : opSynthesisLinearMap A x (opAnalysisLinearMap A x z) = z := by
  simpa [opSynthesisLinearMap, opAnalysisLinearMap] using
    congrArg (fun S : AdjointableMap Aᵐᵒᵖ E E ↦ S z) hx.synthesis_comp_analysis_eq_id

/-- Composing `opAnalysisLinearMap A x` after `opSynthesisLinearMap A x` gives left multiplication
by the Gram matrix `CStarMatrix.gram A x`. -/
theorem opAnalysisLinearMap_comp_opSynthesisLinearMap (x : ι → E) :
    (opAnalysisLinearMap A x).comp (opSynthesisLinearMap A x) =
      mulVecLinearMap (CStarMatrix.gram A x) := by
  ext v i
  simp [opSynthesisLinearMap, opAnalysisLinearMap]

/-- Pointwise evaluation of `opAnalysisLinearMap A x` after `opSynthesisLinearMap A x` as
`mulVecLinearMap (CStarMatrix.gram A x)`. -/
theorem opAnalysisLinearMap_opSynthesisLinearMap (x : ι → E) (v : C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A)) :
    opAnalysisLinearMap A x (opSynthesisLinearMap A x v) =
      mulVecLinearMap (CStarMatrix.gram A x) v :=
  LinearMap.congr_fun (opAnalysisLinearMap_comp_opSynthesisLinearMap x) v

/-- For a Parseval frame `x`, the range of `opAnalysisLinearMap A x` equals the range of
`mulVecLinearMap (CStarMatrix.gram A x)`. -/
theorem range_opAnalysisLinearMap {x : ι → E} (hx : IsParsevalFrame Aᵐᵒᵖ x) :
    LinearMap.range (opAnalysisLinearMap A x) =
      LinearMap.range (mulVecLinearMap (CStarMatrix.gram A x)) := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨z, rfl⟩
    exact ⟨opAnalysisLinearMap A x z, by
      rw [← opAnalysisLinearMap_opSynthesisLinearMap, opSynthesisLinearMap_opAnalysisLinearMap hx]⟩
  · rw [← opAnalysisLinearMap_comp_opSynthesisLinearMap]
    exact LinearMap.range_comp_le_range _ _

/-- For a Parseval frame `x`, `opAnalysisLinearMap A x` preserves the `Aᵐᵒᵖ`-valued inner
product. -/
theorem inner_opAnalysisLinearMap {x : ι → E} (hx : IsParsevalFrame Aᵐᵒᵖ x) (y z : E) :
    inner Aᵐᵒᵖ (opAnalysisLinearMap A x y) (opAnalysisLinearMap A x z) = inner Aᵐᵒᵖ y z := by
  calc inner Aᵐᵒᵖ (opAnalysisLinearMap A x y) (opAnalysisLinearMap A x z)
      = inner Aᵐᵒᵖ (piOpEquiv A ι (opAnalysisLinearMap A x y))
          (piOpEquiv A ι (opAnalysisLinearMap A x z)) := (inner_piOpEquiv _ _).symm
    _ = inner Aᵐᵒᵖ (AdjointableMap.analysis Aᵐᵒᵖ x y) (AdjointableMap.analysis Aᵐᵒᵖ x z) := by
          simp [opAnalysisLinearMap]
    _ = inner Aᵐᵒᵖ y z := hx.inner_analysis_analysis y z

variable (A) in
/-- `opSynthesisLinearMap A x` and `opAnalysisLinearMap A x` form a module adjoint pair. -/
theorem isAdjointPair_opSynthesisLinearMap_opAnalysisLinearMap (x : ι → E) :
    LinearMap.IsAdjointPair (innerₛₗ (A := Aᵐᵒᵖ) (E := C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A))).flip
      (innerₛₗ (A := Aᵐᵒᵖ) (E := E)).flip
      (opSynthesisLinearMap A x) (opAnalysisLinearMap A x) := by
  rw [isAdjointPair_inner_iff]; intro v z
  calc inner Aᵐᵒᵖ (opSynthesisLinearMap A x v) z
      = inner Aᵐᵒᵖ (AdjointableMap.synthesis Aᵐᵒᵖ x (piOpEquiv A ι v)) z := by
          simp [opSynthesisLinearMap]
    _ = inner Aᵐᵒᵖ (piOpEquiv A ι v) (AdjointableMap.analysis Aᵐᵒᵖ x z) :=
        ((AdjointableMap.synthesis Aᵐᵒᵖ x).adjoint_inner_right _ _).symm
    _ = inner Aᵐᵒᵖ (piOpEquiv A ι v) (piOpEquiv A ι (opAnalysisLinearMap A x z)) := by
        simp [opAnalysisLinearMap]
    _ = inner Aᵐᵒᵖ v (opAnalysisLinearMap A x z) := inner_piOpEquiv _ _

variable (A) in
/-- `opAnalysisLinearMap A x` and `opSynthesisLinearMap A x` form a module adjoint pair. -/
theorem isAdjointPair_opAnalysisLinearMap_opSynthesisLinearMap (x : ι → E) :
    LinearMap.IsAdjointPair (innerₛₗ (A := Aᵐᵒᵖ) (E := E)).flip
      (innerₛₗ (A := Aᵐᵒᵖ) (E := C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A))).flip
      (opAnalysisLinearMap A x) (opSynthesisLinearMap A x) :=
  (isAdjointPair_opSynthesisLinearMap_opAnalysisLinearMap A x).symm_cstarModule

end OpLinear

end TauCeti.CStarModule
