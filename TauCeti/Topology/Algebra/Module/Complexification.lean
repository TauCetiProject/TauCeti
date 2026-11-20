/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import TauCeti.Topology.Algebra.Module.Spaces.CompactConvergenceCLM
import Mathlib.Topology.Algebra.Module.Star
public import TauCeti.Analysis.Normed.Module.Complexification
public import TauCeti.LinearAlgebra.Complex.Conjugation
public import TauCeti.LinearAlgebra.TotallyReal.Complex
import TauCeti.LinearAlgebra.Complex.RealForm

/-!
# The complexification topology on `ℂ ⊗[ℝ] W`

For a real vector space `W`, `ℂ ⊗[ℝ] W` splits via `TauCeti.realPart` and `TauCeti.imaginaryPart`,
while on a real seminormed space `X`, `TauCeti.Complexification X` carries the Taylor seminorm
(`TauCeti.Complexification.instSeminormedAddCommGroup`) and is real-linearly homeomorphic to
`X × X` via `TauCeti.Complexification.equivProd`. This file equips `ℂ ⊗[ℝ] W` with the product
topology induced along `(realPart W, imaginaryPart W)` (`TauCeti.complexificationTopology`, scoped
in `TauCeti.Complexification`, with mixin `TauCeti.IsComplexificationTopology`). Over
finite-dimensional Hausdorff real topological vector spaces, every Hausdorff topological `ℝ`-module
topology on `ℂ ⊗[ℝ] W` satisfies `IsComplexificationTopology W`
(`TauCeti.IsComplexificationTopology.of_finiteDimensional`). We also provide
`TauCeti.complexificationEquivProd`, `TauCeti.tensorContinuousLinearEquivComplexification`,
`TauCeti.tmulConjCLE`, `TauCeti.tmulConjCLM`, `ContinuousLinearMap.baseChangeComplex`,
`ContinuousLinearEquiv.baseChangeComplex`, and the continuous complex-linear extension
`ContinuousLinearMap.liftBaseChangeComplex`. For the native compact-convergence duals,
`TauCeti.complexificationCompactDualEquiv` identifies the complexification of the real dual with
the complex dual of the complexification, continuously in both directions. It intertwines
`TauCeti.tmulConj` on the coefficient tensor with
`TauCeti.compactDualConjCLE`; `TauCeti.compactDualRealPointsCLE` identifies the real dual with
the real points (`TauCeti.realPoints`) of that conjugation. These comparisons are natural under
real continuous-linear precomposition and need
no norm, finite-dimensionality or completeness hypothesis on the source. For a finite-dimensional
source with maximal totally real image, we also provide the continuous complex-linear equivalence
`ContinuousLinearMap.complexificationEquivOfIsMaximalTotallyReal`.
The intrinsic `TauCeti.homComplexificationLinearEquiv` compares complexification of real
continuous Hom with complex Hom between complexifications, without bundle frames or norms.

## References

* G. A. Muñoz, Y. Sarantopoulos, A. Tonge, *Complexifications of real Banach spaces,
  polynomials and multilinear maps*, Studia Math. 134 (1999), 1–33.
* D. Huybrechts, *Complex Geometry: An Introduction*, Springer (2005), §1.2.
-/

public section

noncomputable section

open scoped TensorProduct

namespace TauCeti

/-! ### The complexification topology on `ℂ ⊗[ℝ] W` -/

section Topology

/-- The product topology on `ℂ ⊗[ℝ] W` induced from `W × W` along
`u ↦ (realPart W u, imaginaryPart W u)`. Registered as an instance in the
`TauCeti.Complexification` scope to avoid diamonds with inner-product tensor norms on `ℂ ⊗[ℝ] W`. -/
@[instance_reducible]
def complexificationTopology (W : Type*) [AddCommGroup W] [Module ℝ W] [TopologicalSpace W] :
    TopologicalSpace (ℂ ⊗[ℝ] W) :=
  TopologicalSpace.induced (fun u ↦ (realPart W u, imaginaryPart W u)) instTopologicalSpaceProd

scoped[TauCeti.Complexification] attribute [instance] TauCeti.complexificationTopology

/-- Mixin asserting that the topology on `ℂ ⊗[ℝ] W` is induced from `W × W` by the real and
imaginary part projections `(realPart W, imaginaryPart W)`. -/
class IsComplexificationTopology (W : Type*) [AddCommGroup W] [Module ℝ W]
    [TopologicalSpace W] [τ : TopologicalSpace (ℂ ⊗[ℝ] W)] : Prop where
  /-- Prefer `TauCeti.eq_complexificationTopology` over this field. -/
  eq_complexificationTopology' : τ = complexificationTopology W

/-- Under `IsComplexificationTopology W`, the topology on `ℂ ⊗[ℝ] W` equals
`complexificationTopology W`. -/
theorem eq_complexificationTopology (W : Type*) [AddCommGroup W] [Module ℝ W]
    [TopologicalSpace W] [τ : TopologicalSpace (ℂ ⊗[ℝ] W)] [IsComplexificationTopology W] :
    τ = complexificationTopology W :=
  IsComplexificationTopology.eq_complexificationTopology' (W := W)

/-- Low-priority instance recognizing `complexificationTopology W` as an
`IsComplexificationTopology W`, matching `IsModuleTopology`. -/
instance (priority := low) instIsComplexificationTopology {W : Type*} [AddCommGroup W] [Module ℝ W]
    [TopologicalSpace W] : letI := complexificationTopology W; IsComplexificationTopology W :=
  letI := complexificationTopology W; ⟨rfl⟩

section InducedAPI

variable (W : Type*) [AddCommGroup W] [Module ℝ W] [TopologicalSpace W]
  [TopologicalSpace (ℂ ⊗[ℝ] W)] [IsComplexificationTopology W]

/-- The real/imaginary coordinate map `ℂ ⊗[ℝ] W → W × W` is inducing. -/
theorem isInducing_realPart_prod_imaginaryPart :
    Topology.IsInducing (fun u : ℂ ⊗[ℝ] W ↦ (realPart W u, imaginaryPart W u)) :=
  ⟨eq_complexificationTopology W⟩

/-- The real/imaginary coordinate map `ℂ ⊗[ℝ] W → W × W` is a topological embedding. -/
theorem isEmbedding_realPart_prod_imaginaryPart :
    Topology.IsEmbedding (fun u : ℂ ⊗[ℝ] W ↦ (realPart W u, imaginaryPart W u)) :=
  { isInducing_realPart_prod_imaginaryPart W with
    injective := fun _ _ h ↦ complexification_ext (congrArg Prod.fst h) (congrArg Prod.snd h) }

variable {W} in
/-- Continuity into `ℂ ⊗[ℝ] W` is continuity of the real and imaginary parts. -/
theorem continuous_complexification_iff {X : Type*} [TopologicalSpace X] {f : X → ℂ ⊗[ℝ] W} :
    Continuous f ↔
      Continuous (fun x ↦ realPart W (f x)) ∧ Continuous (fun x ↦ imaginaryPart W (f x)) := by
  rw [(isInducing_realPart_prod_imaginaryPart W).continuous_iff, Function.comp_def,
    continuous_prodMk]

/-- The real continuous linear equivalence `ℂ ⊗[ℝ] W ≃L[ℝ] W × W` given by
`(realPart, imaginaryPart)` and its inverse `(v, w) ↦ 1 ⊗ₜ v + I ⊗ₜ w`. -/
def complexificationEquivProd : ℂ ⊗[ℝ] W ≃L[ℝ] W × W where
  toLinearEquiv := complexificationLinearEquivProd W
  continuous_toFun := (isInducing_realPart_prod_imaginaryPart W).continuous.congr
    fun _ ↦ (complexificationLinearEquivProd_apply _).symm
  continuous_invFun := continuous_complexification_iff.mpr
    ⟨by simpa [complexificationLinearEquivProd_symm_apply] using continuous_fst,
      by simpa [complexificationLinearEquivProd_symm_apply] using continuous_snd⟩

/-- `realPart W` as a continuous `ℝ`-linear map `ℂ ⊗[ℝ] W →L[ℝ] W`. -/
def realPartCLM : ℂ ⊗[ℝ] W →L[ℝ] W :=
  (ContinuousLinearMap.fst ℝ W W).comp (complexificationEquivProd W).toContinuousLinearMap

/-- `imaginaryPart W` as a continuous `ℝ`-linear map `ℂ ⊗[ℝ] W →L[ℝ] W`. -/
def imaginaryPartCLM : ℂ ⊗[ℝ] W →L[ℝ] W :=
  (ContinuousLinearMap.snd ℝ W W).comp (complexificationEquivProd W).toContinuousLinearMap

/-- The real inclusion `w ↦ 1 ⊗ₜ[ℝ] w` as a continuous `ℝ`-linear map `W →L[ℝ] ℂ ⊗[ℝ] W`. -/
def oneTmulCLM : W →L[ℝ] ℂ ⊗[ℝ] W :=
  (complexificationEquivProd W).symm.toContinuousLinearMap.comp (ContinuousLinearMap.inl ℝ W W)

/-- The imaginary inclusion `w ↦ I ⊗ₜ[ℝ] w` as a continuous `ℝ`-linear map `W →L[ℝ] ℂ ⊗[ℝ] W`. -/
def ITmulCLM : W →L[ℝ] ℂ ⊗[ℝ] W :=
  (complexificationEquivProd W).symm.toContinuousLinearMap.comp (ContinuousLinearMap.inr ℝ W W)

variable {W}

@[simp] theorem complexificationEquivProd_apply (u : ℂ ⊗[ℝ] W) :
    complexificationEquivProd W u = (realPart W u, imaginaryPart W u) :=
  complexificationLinearEquivProd_apply u
@[simp] theorem complexificationEquivProd_symm_apply (p : W × W) :
    (complexificationEquivProd W).symm p = 1 ⊗ₜ[ℝ] p.1 + Complex.I ⊗ₜ[ℝ] p.2 :=
  complexificationLinearEquivProd_symm_apply p
@[simp] theorem realPartCLM_apply (u : ℂ ⊗[ℝ] W) : realPartCLM W u = realPart W u := by
  simp [realPartCLM]
@[simp] theorem coe_realPartCLM : (realPartCLM W : ℂ ⊗[ℝ] W →ₗ[ℝ] W) = realPart W := by ext; simp
@[simp] theorem imaginaryPartCLM_apply (u : ℂ ⊗[ℝ] W) :
    imaginaryPartCLM W u = imaginaryPart W u := by simp [imaginaryPartCLM]
@[simp] theorem coe_imaginaryPartCLM :
    (imaginaryPartCLM W : ℂ ⊗[ℝ] W →ₗ[ℝ] W) = imaginaryPart W := by ext; simp
@[simp] theorem oneTmulCLM_apply (w : W) : oneTmulCLM W w = 1 ⊗ₜ[ℝ] w := by simp [oneTmulCLM]
@[simp] theorem ITmulCLM_apply (w : W) : ITmulCLM W w = Complex.I ⊗ₜ[ℝ] w := by simp [ITmulCLM]

variable (W) in
/-- Complex conjugation `tmulConj W` on `ℂ ⊗[ℝ] W` as a continuous conjugate-linear equivalence. -/
def tmulConjCLE [ContinuousNeg W] : ℂ ⊗[ℝ] W ≃L⋆[ℂ] ℂ ⊗[ℝ] W :=
  have hcont : Continuous (tmulConj W) := continuous_complexification_iff.mpr
    ⟨(realPartCLM W).continuous.congr fun _ ↦ by simp,
      (continuous_neg.comp (imaginaryPartCLM W).continuous).congr fun _ ↦ by simp⟩
  { toLinearEquiv := LinearEquiv.ofInvolutive (tmulConj W) (tmulConj_involutive W)
    continuous_toFun := hcont, continuous_invFun := hcont }

variable (W) in
/-- Complex conjugation `tmulConj W` on `ℂ ⊗[ℝ] W` viewed as a continuous `ℝ`-linear map. -/
def tmulConjCLM [ContinuousNeg W] : ℂ ⊗[ℝ] W →L[ℝ] ℂ ⊗[ℝ] W where
  toFun := tmulConj W
  map_add' := map_add (tmulConj W)
  map_smul' _ _ := complexification_ext (by simp) (by simp)
  cont := (tmulConjCLE W).continuous

@[simp] theorem coe_tmulConjCLE [ContinuousNeg W] : ⇑(tmulConjCLE W) = tmulConj W := (rfl)
@[simp] theorem tmulConjCLE_symm [ContinuousNeg W] : (tmulConjCLE W).symm = tmulConjCLE W := by
  ext; rfl
@[simp] theorem tmulConjCLM_apply [ContinuousNeg W] (u : ℂ ⊗[ℝ] W) :
    tmulConjCLM W u = tmulConj W u := (rfl)

instance instT2SpaceComplexification [T2Space W] : T2Space (ℂ ⊗[ℝ] W) :=
  (isEmbedding_realPart_prod_imaginaryPart W).t2Space

instance instIsTopologicalAddGroupComplexification [IsTopologicalAddGroup W] :
    IsTopologicalAddGroup (ℂ ⊗[ℝ] W) := by
  have hind : Topology.IsInducing (complexificationEquivProd W) := by
    simpa [funext (complexificationEquivProd_apply (W := W))] using
      isInducing_realPart_prod_imaginaryPart W
  exact hind.isTopologicalAddGroup (complexificationEquivProd W).toAddEquiv.toAddMonoidHom

instance instContinuousSMulComplexComplexification
    [IsTopologicalAddGroup W] [ContinuousSMul ℝ W] : ContinuousSMul ℂ (ℂ ⊗[ℝ] W) where
  continuous_smul := continuous_complexification_iff.mpr
    ⟨(((Complex.continuous_re.comp continuous_fst).smul
        ((realPartCLM W).continuous.comp continuous_snd)).sub
          ((Complex.continuous_im.comp continuous_fst).smul
            ((imaginaryPartCLM W).continuous.comp continuous_snd))).congr
        fun _ ↦ by simp [realPart_smul],
      (((Complex.continuous_re.comp continuous_fst).smul
        ((imaginaryPartCLM W).continuous.comp continuous_snd)).add
          ((Complex.continuous_im.comp continuous_fst).smul
            ((realPartCLM W).continuous.comp continuous_snd))).congr
        fun _ ↦ by simp [imaginaryPart_smul]⟩

instance instContinuousSMulRealComplexification
    [IsTopologicalAddGroup W] [ContinuousSMul ℝ W] : ContinuousSMul ℝ (ℂ ⊗[ℝ] W) where
  continuous_smul := (continuous_smul (M := ℂ) (X := ℂ ⊗[ℝ] W)).comp <|
    (Complex.continuous_ofReal.comp continuous_fst).prodMk continuous_snd

end InducedAPI

/-- Over a finite-dimensional real Hausdorff topological vector space `W`, *every* Hausdorff
topological `ℝ`-module topology on `ℂ ⊗[ℝ] W` agrees with `complexificationTopology W` (for
instance, the Hilbert-space tensor norm on `ℂ ⊗[ℝ] W`). -/
theorem IsComplexificationTopology.of_finiteDimensional (W : Type*) [AddCommGroup W] [Module ℝ W]
    [TopologicalSpace W] [T2Space W] [IsTopologicalAddGroup W] [ContinuousSMul ℝ W]
    [FiniteDimensional ℝ W] [TopologicalSpace (ℂ ⊗[ℝ] W)] [T2Space (ℂ ⊗[ℝ] W)]
    [IsTopologicalAddGroup (ℂ ⊗[ℝ] W)] [ContinuousSMul ℝ (ℂ ⊗[ℝ] W)] :
    IsComplexificationTopology W := by
  let e := complexificationLinearEquivProd W
  have : FiniteDimensional ℝ (ℂ ⊗[ℝ] W) := e.symm.finiteDimensional
  exact ⟨by simpa [complexificationTopology, e, funext complexificationLinearEquivProd_apply]
    using e.toContinuousLinearEquiv.toHomeomorph.isInducing.eq_induced⟩

/-- On a real seminormed space `X`, `TauCeti.tensorEquivComplexification X` is a continuous
`ℂ`-linear equivalence between `ℂ ⊗[ℝ] X` (with an `IsComplexificationTopology`) and
`TauCeti.Complexification X` (with the Taylor seminorm). -/
def tensorContinuousLinearEquivComplexification (X : Type*) [SeminormedAddCommGroup X]
    [NormedSpace ℝ X] [TopologicalSpace (ℂ ⊗[ℝ] X)] [IsComplexificationTopology X] :
    ℂ ⊗[ℝ] X ≃L[ℂ] Complexification X where
  toLinearEquiv := tensorEquivComplexification X
  continuous_toFun := ((Complexification.equivProd X).symm.continuous.comp
    (complexificationEquivProd X).continuous).congr fun _ ↦ by ext <;> simp
  continuous_invFun := ((complexificationEquivProd X).symm.continuous.comp
    (Complexification.equivProd X).continuous).congr fun _ ↦ by simp

section
variable {X : Type*} [SeminormedAddCommGroup X] [NormedSpace ℝ X]
  [TopologicalSpace (ℂ ⊗[ℝ] X)] [IsComplexificationTopology X]
@[simp] theorem toLinearEquiv_tensorContinuousLinearEquivComplexification :
    (tensorContinuousLinearEquivComplexification X).toLinearEquiv =
      tensorEquivComplexification X := (rfl)
@[simp] theorem tensorContinuousLinearEquivComplexification_apply (u : ℂ ⊗[ℝ] X) :
    tensorContinuousLinearEquivComplexification X u = tensorEquivComplexification X u := (rfl)
@[simp] theorem tensorContinuousLinearEquivComplexification_symm_apply (z : Complexification X) :
    (tensorContinuousLinearEquivComplexification X).symm z =
      (tensorEquivComplexification X).symm z := (rfl)
end

end Topology

end TauCeti

/-! ### Continuous scalar extension of `ℝ`-linear maps and equivalences -/

section BaseChangeComplex

open TauCeti

variable {W W' W'' : Type*} [AddCommGroup W] [Module ℝ W] [TopologicalSpace W]
  [TopologicalSpace (ℂ ⊗[ℝ] W)] [IsComplexificationTopology W] [AddCommGroup W'] [Module ℝ W']
  [TopologicalSpace W'] [TopologicalSpace (ℂ ⊗[ℝ] W')] [IsComplexificationTopology W']
  [AddCommGroup W''] [Module ℝ W''] [TopologicalSpace W''] [TopologicalSpace (ℂ ⊗[ℝ] W'')]
  [IsComplexificationTopology W'']

namespace ContinuousLinearMap

/-- Complex base change `c ⊗ₜ w ↦ c ⊗ₜ f w` of a continuous `ℝ`-linear map `f : W →L[ℝ] W'`, as a
continuous `ℂ`-linear map `ℂ ⊗[ℝ] W →L[ℂ] ℂ ⊗[ℝ] W'`. -/
def baseChangeComplex (f : W →L[ℝ] W') : ℂ ⊗[ℝ] W →L[ℂ] ℂ ⊗[ℝ] W' where
  toLinearMap := f.toLinearMap.baseChange ℂ
  cont := continuous_complexification_iff.mpr
    ⟨(f.continuous.comp (realPartCLM W).continuous).congr fun _ ↦ by simp,
      (f.continuous.comp (imaginaryPartCLM W).continuous).congr fun _ ↦ by simp⟩

@[simp] theorem toLinearMap_baseChangeComplex (f : W →L[ℝ] W') :
    f.baseChangeComplex.toLinearMap = f.toLinearMap.baseChange ℂ := (rfl)
@[simp] theorem baseChangeComplex_tmul (f : W →L[ℝ] W') (c : ℂ) (w : W) :
    f.baseChangeComplex (c ⊗ₜ[ℝ] w) = c ⊗ₜ[ℝ] f w := (rfl)
@[simp] theorem realPart_baseChangeComplex (f : W →L[ℝ] W') (u : ℂ ⊗[ℝ] W) :
    realPart W' (f.baseChangeComplex u) = f (realPart W u) := realPart_baseChange f.toLinearMap u
@[simp] theorem imaginaryPart_baseChangeComplex (f : W →L[ℝ] W') (u : ℂ ⊗[ℝ] W) :
    imaginaryPart W' (f.baseChangeComplex u) = f (imaginaryPart W u) :=
  imaginaryPart_baseChange f.toLinearMap u
/-- Continuous complex base change commutes with `tmulConj`. -/
theorem tmulConj_baseChangeComplex (f : W →L[ℝ] W') (u : ℂ ⊗[ℝ] W) :
    tmulConj W' (f.baseChangeComplex u) = f.baseChangeComplex (tmulConj W u) :=
  tmulConj_baseChange f.toLinearMap u
@[simp] theorem baseChangeComplex_id :
    (ContinuousLinearMap.id ℝ W).baseChangeComplex = ContinuousLinearMap.id ℂ (ℂ ⊗[ℝ] W) :=
  ContinuousLinearMap.coe_injective LinearMap.baseChange_id
@[simp] theorem baseChangeComplex_comp (g : W' →L[ℝ] W'') (f : W →L[ℝ] W') :
    (g.comp f).baseChangeComplex = g.baseChangeComplex.comp f.baseChangeComplex := by
  ext u; induction u with | tmul => rfl | add _ _ hu hv => simp [hu, hv]

end ContinuousLinearMap

namespace ContinuousLinearEquiv

/-- Complex base change `c ⊗ₜ w ↦ c ⊗ₜ e w` of a continuous `ℝ`-linear equivalence `e : W ≃L[ℝ] W'`,
as a continuous `ℂ`-linear equivalence `ℂ ⊗[ℝ] W ≃L[ℂ] ℂ ⊗[ℝ] W'`. -/
def baseChangeComplex (e : W ≃L[ℝ] W') : ℂ ⊗[ℝ] W ≃L[ℂ] ℂ ⊗[ℝ] W' :=
  ofContinuousLinearMap e.toContinuousLinearMap.baseChangeComplex
    e.symm.toContinuousLinearMap.baseChangeComplex
    (ContinuousLinearMap.ext fun u ↦ by
      simpa using DFunLike.congr_fun
        (e.toContinuousLinearMap.baseChangeComplex_comp e.symm.toContinuousLinearMap).symm u)
    (ContinuousLinearMap.ext fun u ↦ by
      simpa using DFunLike.congr_fun
        (e.symm.toContinuousLinearMap.baseChangeComplex_comp e.toContinuousLinearMap).symm u)

@[simp] theorem toContinuousLinearMap_baseChangeComplex (e : W ≃L[ℝ] W') :
    e.baseChangeComplex.toContinuousLinearMap = e.toContinuousLinearMap.baseChangeComplex := (rfl)
@[simp] theorem baseChangeComplex_symm (e : W ≃L[ℝ] W') :
    e.baseChangeComplex.symm = e.symm.baseChangeComplex := (rfl)
@[simp] theorem baseChangeComplex_tmul (e : W ≃L[ℝ] W') (c : ℂ) (w : W) :
    e.baseChangeComplex (c ⊗ₜ[ℝ] w) = c ⊗ₜ[ℝ] e w := (rfl)
@[simp] theorem realPart_baseChangeComplex (e : W ≃L[ℝ] W') (u : ℂ ⊗[ℝ] W) :
    realPart W' (e.baseChangeComplex u) = e (realPart W u) :=
  e.toContinuousLinearMap.realPart_baseChangeComplex u
@[simp] theorem imaginaryPart_baseChangeComplex (e : W ≃L[ℝ] W') (u : ℂ ⊗[ℝ] W) :
    imaginaryPart W' (e.baseChangeComplex u) = e (imaginaryPart W u) :=
  e.toContinuousLinearMap.imaginaryPart_baseChangeComplex u
@[simp] theorem baseChangeComplex_refl :
    (ContinuousLinearEquiv.refl ℝ W).baseChangeComplex =
      ContinuousLinearEquiv.refl ℂ (ℂ ⊗[ℝ] W) := by
  ext u; exact DFunLike.congr_fun ContinuousLinearMap.baseChangeComplex_id u
@[simp] theorem baseChangeComplex_trans (e : W ≃L[ℝ] W') (e' : W' ≃L[ℝ] W'') :
    (e.trans e').baseChangeComplex = e.baseChangeComplex.trans e'.baseChangeComplex := by
  ext u; exact DFunLike.congr_fun
    (e'.toContinuousLinearMap.baseChangeComplex_comp e.toContinuousLinearMap) u

end ContinuousLinearEquiv

end BaseChangeComplex

end

section LiftBaseChangeComplex

open scoped TensorProduct
open TauCeti

namespace ContinuousLinearMap

variable {W V : Type*} [AddCommGroup W] [Module ℝ W] [TopologicalSpace W]
  [TopologicalSpace (ℂ ⊗[ℝ] W)] [IsComplexificationTopology W]
  [AddCommGroup V] [Module ℝ V] [Module ℂ V] [IsScalarTower ℝ ℂ V]
  [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousConstSMul ℂ V]

/-- A continuous real-linear map into a complex module extends canonically to a continuous
complex-linear map on its complexification. No finite-dimensionality is needed. -/
noncomputable def liftBaseChangeComplex (f : W →L[ℝ] V) : ℂ ⊗[ℝ] W →L[ℂ] V where
  toLinearMap := f.toLinearMap.liftBaseChange ℂ
  cont := ((f.continuous.comp (realPartCLM W).continuous).add
    ((f.continuous.comp (imaginaryPartCLM W).continuous).const_smul Complex.I)).congr
      fun u ↦ by
        simpa only [Pi.add_apply, Pi.smul_apply, Function.comp_apply, realPartCLM_apply,
          imaginaryPartCLM_apply, ContinuousLinearMap.coe_coe, LinearMap.toFun_eq_coe] using
          (f.toLinearMap.liftBaseChange_complex_apply u).symm

/-- The extension is exactly the native canonical base-change lift. -/
@[simp]
theorem toLinearMap_liftBaseChangeComplex (f : W →L[ℝ] V) :
    f.liftBaseChangeComplex.toLinearMap = f.toLinearMap.liftBaseChange ℂ := by
  simp only [liftBaseChangeComplex]

/-- The characteristic tensor formula for continuous scalar extension. -/
@[simp]
theorem liftBaseChangeComplex_tmul (f : W →L[ℝ] V) (c : ℂ) (w : W) :
    f.liftBaseChangeComplex (c ⊗ₜ[ℝ] w) = c • f w := by
  simp only [liftBaseChangeComplex, coe_mk', LinearMap.liftBaseChange_tmul,
    ContinuousLinearMap.coe_coe]

/-- A continuous complex-linear extension is determined by its values on the real source. -/
theorem liftBaseChangeComplex_unique (f : W →L[ℝ] V) (g : ℂ ⊗[ℝ] W →L[ℂ] V)
    (hg : ∀ w, g (1 ⊗ₜ[ℝ] w) = f w) : g = f.liftBaseChangeComplex := by
  have h : g.toLinearMap = f.liftBaseChangeComplex.toLinearMap := by
    ext w
    simpa only [TensorProduct.AlgebraTensorModule.curry_apply, TensorProduct.curry_apply,
      LinearMap.restrictScalars_apply, coe_coe,
      liftBaseChangeComplex_tmul, one_smul] using hg w
  ext u
  exact congrArg (fun l ↦ l u) h

/-- The real/imaginary formula for the actual continuous complex-linear extension. -/
theorem liftBaseChangeComplex_apply (f : W →L[ℝ] V) (u : ℂ ⊗[ℝ] W) :
    f.liftBaseChangeComplex u = f (realPart W u) + Complex.I • f (imaginaryPart W u) := by
  exact f.toLinearMap.liftBaseChange_complex_apply u

end ContinuousLinearMap

end LiftBaseChangeComplex

namespace TauCeti

/-! ### Compact-convergence duals of complexifications -/

open scoped TensorProduct CompactConvergenceCLM

noncomputable section CompactDualComplexification

variable (E : Type*) [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [TopologicalSpace (ℂ ⊗[ℝ] E)] [IsComplexificationTopology E]

/-- The two real coefficients define an actual continuous complex-valued map on the real source. -/
private def compactDualCoefficient (u : ℂ ⊗[ℝ] (E →L_c[ℝ] ℝ)) : E →L[ℝ] ℂ :=
  let c := ContinuousLinearMap.toUniformConvergenceCLM (RingHom.id ℝ) ℝ {K : Set E | IsCompact K}
  Complex.ofRealCLM.comp (c.symm (realPart (E →L_c[ℝ] ℝ) u)) +
    Complex.I • Complex.ofRealCLM.comp (c.symm (imaginaryPart (E →L_c[ℝ] ℝ) u))

/-- The actual complex-linear functional obtained by native scalar extension of the coefficients. -/
private def compactDualExtension (u : ℂ ⊗[ℝ] (E →L_c[ℝ] ℝ)) : (ℂ ⊗[ℝ] E) →L_c[ℂ] ℂ :=
  (ContinuousLinearMap.toUniformConvergenceCLM (RingHom.id ℂ) ℂ
    {K : Set (ℂ ⊗[ℝ] E) | IsCompact K}) (compactDualCoefficient E u).liftBaseChangeComplex

/-- Evaluation retains all four real pairings. -/
private theorem compactDualExtension_apply (u : ℂ ⊗[ℝ] (E →L_c[ℝ] ℝ)) (v : ℂ ⊗[ℝ] E) :
    compactDualExtension E u v =
      ((realPart (E →L_c[ℝ] ℝ) u) (realPart E v) - (imaginaryPart (E →L_c[ℝ] ℝ) u) (imaginaryPart
        E v) : ℝ) +
        Complex.I * ((imaginaryPart (E →L_c[ℝ] ℝ) u) (realPart E v) + (realPart (E →L_c[ℝ] ℝ) u)
          (imaginaryPart E v)) := by
  simp only [compactDualExtension, ContinuousLinearMap.toUniformConvergenceCLM_apply,
    ContinuousLinearMap.liftBaseChangeComplex_apply, compactDualCoefficient, add_apply, smul_apply,
    ContinuousLinearMap.comp_apply,
    Complex.ofRealCLM_apply, ContinuousLinearMap.toUniformConvergenceCLM_symm_apply,
    smul_eq_mul]
  apply Complex.ext
  · simp [Complex.mul_re, Complex.mul_im]
    ring
  · simp [Complex.mul_re, Complex.mul_im]

/-- The inverse is the literal tensor made from Re/Im restrictions to the real inclusion. -/
private def compactDualRestriction (A : (ℂ ⊗[ℝ] E) →L_c[ℂ] ℂ) : ℂ ⊗[ℝ] (E →L_c[ℝ] ℝ) :=
  let f := (ContinuousLinearMap.toUniformConvergenceCLM (RingHom.id ℂ) ℂ
    {K : Set (ℂ ⊗[ℝ] E) | IsCompact K}).symm A
  let c := ContinuousLinearMap.toUniformConvergenceCLM (RingHom.id ℝ) ℝ {K : Set E | IsCompact K}
  1 ⊗ₜ[ℝ] c (Complex.reCLM.comp ((f.restrictScalars ℝ).comp (oneTmulCLM E))) +
    Complex.I ⊗ₜ[ℝ] c (Complex.imCLM.comp ((f.restrictScalars ℝ).comp (oneTmulCLM E)))

/-- The real coefficient of restriction is the real part on the original real inclusion. -/
@[simp] private theorem compactDualRestriction_re (A : (ℂ ⊗[ℝ] E) →L_c[ℂ] ℂ) (x : E) :
    realPart (E →L_c[ℝ] ℝ) (compactDualRestriction E A) x = (A (1 ⊗ₜ[ℝ] x)).re := by
  simp [compactDualRestriction, realPart_tmul, ContinuousLinearMap.coe_restrictScalars']
/-- The imaginary coefficient is the imaginary part on the original real inclusion. -/
@[simp] private theorem compactDualRestriction_im (A : (ℂ ⊗[ℝ] E) →L_c[ℂ] ℂ) (x : E) :
    imaginaryPart (E →L_c[ℝ] ℝ) (compactDualRestriction E A) x = (A (1 ⊗ₜ[ℝ] x)).im := by
  simp [compactDualRestriction, imaginaryPart_tmul,
    ContinuousLinearMap.coe_restrictScalars']

/-- The actual complex scalar linearity on the coefficient tensor. -/
private theorem compactDualExtension_smul (z : ℂ) (u : ℂ ⊗[ℝ] (E →L_c[ℝ] ℝ)) :
    compactDualExtension E (z • u) = z • compactDualExtension E u := by
  ext v
  apply Complex.ext <;>
    simp [compactDualExtension_apply, realPart_smul, imaginaryPart_smul,
      Complex.mul_re, Complex.mul_im] <;>
      ring

/-- The extension is additive. -/
private theorem compactDualExtension_add (u v : ℂ ⊗[ℝ] (E →L_c[ℝ] ℝ)) :
    compactDualExtension E (u+v) = compactDualExtension E u + compactDualExtension E v := by
  ext w
  simp [compactDualExtension_apply]
  ring

@[simp] private theorem compactDualRestriction_extension (u : ℂ ⊗[ℝ] (E →L_c[ℝ] ℝ)) :
    compactDualRestriction E (compactDualExtension E u) = u := by
  apply complexification_ext <;> ext x <;> simp [compactDualExtension_apply]

@[simp] private theorem compactDualExtension_restriction (A : (ℂ ⊗[ℝ] E) →L_c[ℂ] ℂ) :
    compactDualExtension E (compactDualRestriction E A) = A := by
  let c := ContinuousLinearMap.toUniformConvergenceCLM (RingHom.id ℂ) ℂ
    {K : Set (ℂ ⊗[ℝ] E) | IsCompact K}
  have h := (compactDualCoefficient E (compactDualRestriction E A)).liftBaseChangeComplex_unique
    (c.symm A) (fun x ↦ by
      simp only [compactDualCoefficient, add_apply,
        ContinuousLinearMap.comp_apply, ContinuousLinearMap.toUniformConvergenceCLM_symm_apply,
        Complex.ofRealCLM_apply, smul_apply, compactDualRestriction_re,
        compactDualRestriction_im, smul_eq_mul]
      simpa only [c, ContinuousLinearMap.toUniformConvergenceCLM_symm_apply,
        mul_comm Complex.I] using (Complex.re_add_im (A (1 ⊗ₜ[ℝ] x))).symm)
  exact (congrArg c h).symm.trans (c.apply_symm_apply A)

variable [TopologicalSpace (ℂ ⊗[ℝ] (E →L_c[ℝ] ℝ))]
  [IsComplexificationTopology (E →L_c[ℝ] ℝ)]

/-- Both real/imaginary restrictions are continuous in the genuine compact topology. -/
private theorem compactDual_continuous_restriction : Continuous (compactDualRestriction E) := by
  apply continuous_complexification_iff.mpr
  have h := ((oneTmulCLM E).precompCompactConvergenceCLM ℂ).continuous.comp
    (UniformConvergenceCLM.isEmbedding_restrictScalars (𝕜 := ℂ) (F := ℂ) ℝ
      {K : Set (ℂ ⊗[ℝ] E) | IsCompact K}).continuous
  constructor
  · refine ((Complex.reCLM.postcompCompactConvergenceCLM E).continuous.comp h).congr ?_
    intro A
    ext x
    simp only [Function.comp_apply, ContinuousLinearMap.postcompCompactConvergenceCLM_apply_apply,
      ContinuousLinearMap.precompCompactConvergenceCLM_apply_apply,
      UniformConvergenceCLM.restrictScalars_apply, Complex.reCLM_apply,
      oneTmulCLM_apply, compactDualRestriction_re]
  · refine ((Complex.imCLM.postcompCompactConvergenceCLM E).continuous.comp h).congr ?_
    intro A
    ext x
    simp only [Function.comp_apply, ContinuousLinearMap.postcompCompactConvergenceCLM_apply_apply,
      ContinuousLinearMap.precompCompactConvergenceCLM_apply_apply,
      UniformConvergenceCLM.restrictScalars_apply, Complex.imCLM_apply,
      oneTmulCLM_apply, compactDualRestriction_im]

/-- Extension is continuous for uniform convergence on every compact set. -/
private theorem compactDual_continuous_extension : Continuous (compactDualExtension E) := by
  have hr := (realPartCLM (E →L_c[ℝ] ℝ)).continuous
  have hi := (imaginaryPartCLM (E →L_c[ℝ] ℝ)).continuous
  let R := (realPartCLM E).precompCompactConvergenceCLM (σ := RingHom.id ℝ)
    (τ := RingHom.id ℝ) (ρ := RingHom.id ℝ) ℝ
  let S := (imaginaryPartCLM E).precompCompactConvergenceCLM (σ := RingHom.id ℝ)
    (τ := RingHom.id ℝ) (ρ := RingHom.id ℝ) ℝ
  let O := Complex.ofRealCLM.postcompCompactConvergenceCLM (σ := RingHom.id ℝ)
    (τ := RingHom.id ℝ) (ρ := RingHom.id ℝ) (ℂ ⊗[ℝ] E)
  have h := ((O.continuous.comp ((R.continuous.comp hr).sub (S.continuous.comp hi))).add
    ((O.continuous.comp ((R.continuous.comp hi).add (S.continuous.comp hr)))
      |>.const_smul Complex.I))
  rw [(UniformConvergenceCLM.isEmbedding_restrictScalars (𝕜 := ℂ) (F := ℂ) ℝ
      {K : Set (ℂ ⊗[ℝ] E) | IsCompact K}).continuous_iff]
  refine h.congr fun u ↦ ?_
  ext v
  simp only [R, S, O, Function.comp_apply, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
    add_apply, sub_apply, smul_apply,
    ContinuousLinearMap.precompCompactConvergenceCLM_apply_apply,
    ContinuousLinearMap.postcompCompactConvergenceCLM_apply_apply,
    UniformConvergenceCLM.restrictScalars_apply, Complex.ofRealCLM_apply,
    realPartCLM_apply, imaginaryPartCLM_apply, compactDualExtension_apply,
    smul_eq_mul, Complex.ofReal_add]

/-- The complexification of the real compact-convergence dual is continuously complex-linearly
isomorphic to the complex compact-convergence dual of the complexification. It sends `c ⊗ f`
to the complex-linear functional determined by `z ⊗ x ↦ c * z * f x`. Its inverse takes the real
and imaginary parts of restriction to `1 ⊗ E` as the two tensor coefficients. Both duals have their
native
compact-convergence topologies, and both complexifications carry any compatible real/imaginary
product topology. No norm, completeness or finite-dimensionality assumption on `E` is needed. -/
def complexificationCompactDualEquiv : (ℂ ⊗[ℝ] (E →L_c[ℝ] ℝ)) ≃L[ℂ]
    ((ℂ ⊗[ℝ] E) →L_c[ℂ] ℂ) where
  toFun := compactDualExtension E
  invFun := compactDualRestriction E
  map_add' := compactDualExtension_add E
  map_smul' := compactDualExtension_smul E
  left_inv := compactDualRestriction_extension E
  right_inv := compactDualExtension_restriction E
  continuous_toFun := compactDual_continuous_extension E
  continuous_invFun := compactDual_continuous_restriction E

/-- The compact-topology dual comparison is the native functional extension. -/
private theorem compactDualEquiv_apply (u : ℂ ⊗[ℝ] (E →L_c[ℝ] ℝ)) :
    complexificationCompactDualEquiv E u = compactDualExtension E u := by rfl

/-- Its inverse is the original real/imaginary restriction tensor. -/
private theorem compactDualEquiv_symm_apply (A : (ℂ ⊗[ℝ] E) →L_c[ℂ] ℂ) :
    (complexificationCompactDualEquiv E).symm A = compactDualRestriction E A := by rfl

/-- The compact-dual comparison evaluates by all four real coordinate pairings. -/
theorem complexificationCompactDualEquiv_apply
    (u : ℂ ⊗[ℝ] (E →L_c[ℝ] ℝ)) (v : ℂ ⊗[ℝ] E) :
    complexificationCompactDualEquiv E u v =
      ((realPart (E →L_c[ℝ] ℝ) u) (realPart E v) -
        (imaginaryPart (E →L_c[ℝ] ℝ) u) (imaginaryPart E v) : ℝ) +
        Complex.I * ((imaginaryPart (E →L_c[ℝ] ℝ) u) (realPart E v) +
          (realPart (E →L_c[ℝ] ℝ) u) (imaginaryPart E v)) :=
  compactDualExtension_apply E u v

/-- The real coefficient of the inverse is restriction followed by real part. -/
@[simp] theorem realPart_complexificationCompactDualEquiv_symm_apply
    (A : (ℂ ⊗[ℝ] E) →L_c[ℂ] ℂ) (x : E) :
    realPart (E →L_c[ℝ] ℝ) ((complexificationCompactDualEquiv E).symm A) x =
      (A (1 ⊗ₜ[ℝ] x)).re := by
  rw [compactDualEquiv_symm_apply, compactDualRestriction_re]

/-- The imaginary coefficient of the inverse is restriction followed by imaginary part. -/
@[simp] theorem imaginaryPart_complexificationCompactDualEquiv_symm_apply
    (A : (ℂ ⊗[ℝ] E) →L_c[ℂ] ℂ) (x : E) :
    imaginaryPart (E →L_c[ℝ] ℝ) ((complexificationCompactDualEquiv E).symm A) x =
      (A (1 ⊗ₜ[ℝ] x)).im := by
  rw [compactDualEquiv_symm_apply, compactDualRestriction_im]

/-- On simple tensors the comparison is the literal scalar-extended pairing. -/
@[simp] theorem complexificationCompactDualEquiv_tmul_tmul (c z : ℂ)
    (f : E →L_c[ℝ] ℝ) (x : E) :
    complexificationCompactDualEquiv E (c ⊗ₜ[ℝ] f) (z ⊗ₜ[ℝ] x) = c * z * f x := by
  apply Complex.ext <;>
    simp [complexificationCompactDualEquiv_apply, realPart_tmul, imaginaryPart_tmul,
      Complex.mul_re, Complex.mul_im] <;> ring

end CompactDualComplexification

noncomputable section CompactDualConjugation

variable (E : Type*) [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [ContinuousNeg E]
  [TopologicalSpace (ℂ ⊗[ℝ] E)] [IsComplexificationTopology E]

/-- Intrinsic conjugation of the native complex compact-convergence dual. -/
def compactDualConjCLE : ((ℂ ⊗[ℝ] E) →L_c[ℂ] ℂ) ≃L⋆[ℂ] ((ℂ ⊗[ℝ] E) →L_c[ℂ] ℂ) :=
  (tmulConjCLE E).compactConvergenceCLMCongrSL (starL ℂ : ℂ ≃L⋆[ℂ] ℂ)

/-- Native conjugation acts by conjugation on both the argument and the value. -/
@[simp] theorem compactDualConjCLE_apply (A : (ℂ ⊗[ℝ] E) →L_c[ℂ] ℂ) (v : ℂ ⊗[ℝ] E) :
    compactDualConjCLE E A v = star (A (tmulConj E v)) := by
  simp [compactDualConjCLE, ContinuousLinearEquiv.compactConvergenceCLMCongrSL_apply]

/-- Applying `compactDualConjCLE E` twice returns the original functional. -/
theorem compactDualConjCLE_involutive : Function.Involutive (compactDualConjCLE E) := by
  intro A
  ext v
  simp

variable [TopologicalSpace (ℂ ⊗[ℝ] (E →L_c[ℝ] ℝ))]
  [IsComplexificationTopology (E →L_c[ℝ] ℝ)]

/-- The dual comparison intertwines the two native conjugations. -/
theorem complexificationCompactDualEquiv_tmulConj (u : ℂ ⊗[ℝ] (E →L_c[ℝ] ℝ)) :
    complexificationCompactDualEquiv E (tmulConj (E →L_c[ℝ] ℝ) u) =
      compactDualConjCLE E (complexificationCompactDualEquiv E u) := by
  ext v
  simp only [compactDualEquiv_apply, compactDualExtension_apply, compactDualConjCLE_apply,
    realPart_tmulConj,
    imaginaryPart_tmulConj]
  apply Complex.ext
  · simp [Complex.mul_re]
  · simp [Complex.mul_im]
    ring

/-- The actual real dual is included by the native complex-linear extension. -/
def compactDualComplexExtension : (E →L_c[ℝ] ℝ) →L[ℝ] ((ℂ ⊗[ℝ] E) →L_c[ℂ] ℂ) :=
  ((complexificationCompactDualEquiv E).toContinuousLinearMap.restrictScalars ℝ).comp
    (oneTmulCLM (E →L_c[ℝ] ℝ))

omit [ContinuousNeg E] in
/-- Real extension evaluates as the original functional on both real coordinates. -/
@[simp] theorem compactDualComplexExtension_apply (f : E →L_c[ℝ] ℝ) (v : ℂ ⊗[ℝ] E) :
    compactDualComplexExtension E f v =
      (f (realPart E v) : ℂ) + Complex.I * f (imaginaryPart E v) := by
  simp [compactDualComplexExtension, compactDualEquiv_apply, compactDualExtension_apply,
    ContinuousLinearMap.coe_restrictScalars']

/-- Real functionals identify with the existing native realPoints submodule of dual conjugation. -/
def compactDualRealPointsCLE : (E →L_c[ℝ] ℝ) ≃L[ℝ]
    TauCeti.realPoints (compactDualConjCLE E).toLinearMap where
  toFun f := ⟨compactDualComplexExtension E f, by
    rw [TauCeti.mem_realPoints]
    ext v
    simp [compactDualComplexExtension_apply, compactDualConjCLE_apply]⟩
  invFun A := realPart (E →L_c[ℝ] ℝ) ((complexificationCompactDualEquiv E).symm A.val)
  left_inv f := by
    apply UniformConvergenceCLM.ext
    intro x
    simp [compactDualComplexExtension, compactDualEquiv_apply, compactDualEquiv_symm_apply]
  right_inv A := by
    apply Subtype.ext
    apply (complexificationCompactDualEquiv E).symm.injective
    have hc : tmulConj (E →L_c[ℝ] ℝ) ((complexificationCompactDualEquiv E).symm A.val) =
        (complexificationCompactDualEquiv E).symm A.val := by
      apply (complexificationCompactDualEquiv E).injective
      rw [complexificationCompactDualEquiv_tmulConj, ContinuousLinearEquiv.apply_symm_apply]
      exact TauCeti.mem_realPoints.mp A.property
    obtain ⟨f, hf⟩ := (tmulConj_eq_self_iff (E →L_c[ℝ] ℝ) _).mp hc
    simp [compactDualComplexExtension, hf]
  map_add' f g := Subtype.ext (map_add (compactDualComplexExtension E) f g)
  map_smul' r f := Subtype.ext (map_smul (compactDualComplexExtension E) r f)
  continuous_toFun := by
    apply Topology.IsInducing.subtypeVal.continuous_iff.mpr
    exact (compactDualComplexExtension E).continuous
  continuous_invFun := ((realPartCLM (E →L_c[ℝ] ℝ)).continuous.comp
    ((complexificationCompactDualEquiv E).symm.continuous.comp
      continuous_subtypeVal)).congr fun A ↦
      realPartCLM_apply ((complexificationCompactDualEquiv E).symm A.val)

/-- The fixed endpoint's inclusion is exactly the native real extension. -/
@[simp] theorem coe_compactDualRealPointsCLE (f : E →L_c[ℝ] ℝ) :
    (compactDualRealPointsCLE E f).val = compactDualComplexExtension E f := by rfl

/-- The native fixed-space inverse is the real coefficient of the inverse dual comparison. -/
theorem compactDualRealPointsCLE_symm_eq_realPart
    (A : TauCeti.realPoints (compactDualConjCLE E).toLinearMap) :
    (compactDualRealPointsCLE E).symm A =
      realPart (E →L_c[ℝ] ℝ) ((complexificationCompactDualEquiv E).symm A.val) := by
  -- The inverse field records exactly this real coefficient, without any change of scalar action.
  rfl

/-- The inverse is real restriction on the actual native real inclusion. -/
@[simp] theorem compactDualRealPointsCLE_symm_apply
    (A : TauCeti.realPoints (compactDualConjCLE E).toLinearMap) (x : E) :
    (compactDualRealPointsCLE E).symm A x = (A.val (1 ⊗ₜ[ℝ] x)).re := by
  rw [compactDualRealPointsCLE_symm_eq_realPart,
    realPart_complexificationCompactDualEquiv_symm_apply]

section Naturality
variable {F : Type*} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
  [ContinuousNeg F]
  [TopologicalSpace (ℂ ⊗[ℝ] F)] [IsComplexificationTopology F]
  [TopologicalSpace (ℂ ⊗[ℝ] (F →L_c[ℝ] ℝ))]
  [IsComplexificationTopology (F →L_c[ℝ] ℝ)]

omit [ContinuousNeg E]
  [ContinuousNeg F] in
/-- Dual extension commutes with actual real continuous-linear precomposition. -/
theorem complexificationCompactDualEquiv_baseChangeComplex_precomp (L : E →L[ℝ] F)
    (u : ℂ ⊗[ℝ] (F →L_c[ℝ] ℝ)) :
    complexificationCompactDualEquiv E ((L.precompCompactConvergenceCLM ℝ).baseChangeComplex u) =
      (L.baseChangeComplex.precompCompactConvergenceCLM ℂ)
        (complexificationCompactDualEquiv F u) := by
  ext v
  simp only [compactDualEquiv_apply, compactDualExtension_apply,
    ContinuousLinearMap.realPart_baseChangeComplex,
    ContinuousLinearMap.imaginaryPart_baseChangeComplex,
    ContinuousLinearMap.precompCompactConvergenceCLM_apply_apply]

omit [ContinuousNeg E]
  [ContinuousNeg F] in
/-- The transpose square is an equality of genuine compact-convergence continuous linear maps. -/
theorem complexificationCompactDualEquiv_comp_baseChangeComplex_precomp (L : E →L[ℝ] F) :
    (complexificationCompactDualEquiv E).toContinuousLinearMap.comp
      (L.precompCompactConvergenceCLM ℝ).baseChangeComplex =
    (L.baseChangeComplex.precompCompactConvergenceCLM ℂ).comp
      (complexificationCompactDualEquiv F).toContinuousLinearMap := by
  ext u v
  exact congrArg (fun A ↦ A v) (complexificationCompactDualEquiv_baseChangeComplex_precomp E L u)

omit [ContinuousNeg E]
  [ContinuousNeg F] in
/-- Real extension is natural for actual real continuous-linear maps. -/
private theorem compactDualComplexExtension_precomp (L : E →L[ℝ] F) (f : F →L_c[ℝ] ℝ) :
    compactDualComplexExtension E (L.precompCompactConvergenceCLM ℝ f) =
      L.baseChangeComplex.precompCompactConvergenceCLM ℂ (compactDualComplexExtension F f) := by
  ext v
  simp only [ContinuousLinearMap.precompCompactConvergenceCLM_apply_apply,
    compactDualComplexExtension_apply, ContinuousLinearMap.realPart_baseChangeComplex,
    ContinuousLinearMap.imaginaryPart_baseChangeComplex]

omit [TopologicalSpace (ℂ ⊗[ℝ] (E →L_c[ℝ] ℝ))]
  [IsComplexificationTopology (E →L_c[ℝ] ℝ)]
  [TopologicalSpace (ℂ ⊗[ℝ] (F →L_c[ℝ] ℝ))]
  [IsComplexificationTopology (F →L_c[ℝ] ℝ)] in
/-- Actual compact-dual transpose commutes with both native conjugations. -/
theorem compactDualConjCLE_precomp (L : E →L[ℝ] F) (A : (ℂ ⊗[ℝ] F) →L_c[ℂ] ℂ) :
    compactDualConjCLE E (L.baseChangeComplex.precompCompactConvergenceCLM ℂ A) =
      L.baseChangeComplex.precompCompactConvergenceCLM ℂ (compactDualConjCLE F A) := by
  ext v
  simp only [compactDualConjCLE_apply, ContinuousLinearMap.precompCompactConvergenceCLM_apply_apply,
    ContinuousLinearMap.tmulConj_baseChangeComplex]

/-- The actual fixed-endpoint inclusions commute with the native compact-dual transpose. -/
theorem compactDualRealPointsCLE_precomp (L : E →L[ℝ] F) (f : F →L_c[ℝ] ℝ) :
    (compactDualRealPointsCLE E (L.precompCompactConvergenceCLM ℝ f)).val =
      L.baseChangeComplex.precompCompactConvergenceCLM ℂ (compactDualRealPointsCLE F f).val :=
  compactDualComplexExtension_precomp E L f

end Naturality

end CompactDualConjugation

end TauCeti

section MaximalTotallyReal

open scoped TensorProduct
open TauCeti

namespace ContinuousLinearMap

variable {W V : Type*} [AddCommGroup W] [Module ℝ W] [TopologicalSpace W]
  [TopologicalSpace (ℂ ⊗[ℝ] W)] [IsComplexificationTopology W]
  [AddCommGroup V] [Module ℝ V] [Module ℂ V] [IsScalarTower ℝ ℂ V]
  [TopologicalSpace V] [IsTopologicalAddGroup V]
  [IsTopologicalAddGroup W] [ContinuousSMul ℝ W] [FiniteDimensional ℝ W]
  [ContinuousSMul ℝ V] [T2Space V]

/-- A continuous injective real-linear map onto a maximal totally real subspace identifies the
complexification of its finite-dimensional source with the ambient complex module, as a
continuous complex-linear equivalence. The source is Hausdorff because it injects continuously
into the Hausdorff target, and the inverse is continuous by finite dimensionality. -/
noncomputable def complexificationEquivOfIsMaximalTotallyReal (f : W →L[ℝ] V)
    (hf : Function.Injective f)
    (hmax : IsMaximalTotallyReal ((LinearMap.lsmul ℂ V Complex.I).restrictScalars ℝ)
      f.toLinearMap.range) :
    (ℂ ⊗[ℝ] W) ≃L[ℂ] V :=
  let := T2Space.of_injective_continuous hf f.continuous
  let : FiniteDimensional ℝ (ℂ ⊗[ℝ] W) :=
    (complexificationLinearEquivProd W).symm.finiteDimensional
  let e := (f.toLinearMap.isBaseChange_complex_of_isMaximalTotallyReal hf hmax).equiv
  let r := (e.restrictScalars ℝ).toContinuousLinearEquiv
  { toLinearEquiv := e
    continuous_toFun := by
      rw [LinearEquiv.toFun_eq_coe]
      exact r.continuous.congr fun u ↦ by
        simp only [r, LinearEquiv.coe_toContinuousLinearEquiv', LinearEquiv.restrictScalars_apply]
    continuous_invFun := by
      rw [LinearEquiv.invFun_eq_symm]
      exact r.symm.continuous.congr fun u ↦ by
        simp only [r, LinearEquiv.coe_toContinuousLinearEquiv_symm',
          LinearEquiv.restrictScalars_symm_apply] }

/-- Forgetting continuity recovers the canonical native algebraic base-change equivalence. -/
@[simp]
theorem complexificationEquivOfIsMaximalTotallyReal_toLinearEquiv (f : W →L[ℝ] V)
    (hf : Function.Injective f)
    (hmax : IsMaximalTotallyReal ((LinearMap.lsmul ℂ V Complex.I).restrictScalars ℝ)
      f.toLinearMap.range) :
    (f.complexificationEquivOfIsMaximalTotallyReal hf hmax).toLinearEquiv =
      (f.toLinearMap.isBaseChange_complex_of_isMaximalTotallyReal hf hmax).equiv := by
  unfold complexificationEquivOfIsMaximalTotallyReal
  rfl

/-- The characteristic action of the equivalence on actual tensors. -/
@[simp]
theorem complexificationEquivOfIsMaximalTotallyReal_tmul (f : W →L[ℝ] V)
    (hf : Function.Injective f)
    (hmax : IsMaximalTotallyReal ((LinearMap.lsmul ℂ V Complex.I).restrictScalars ℝ)
      f.toLinearMap.range) (c : ℂ) (w : W) :
    f.complexificationEquivOfIsMaximalTotallyReal hf hmax (c ⊗ₜ[ℝ] w) = c • f w := by
  rw [← ContinuousLinearEquiv.coe_toLinearEquiv,
    complexificationEquivOfIsMaximalTotallyReal_toLinearEquiv, IsBaseChange.equiv_tmul,
    ContinuousLinearMap.coe_coe]

/-- The equivalence is the canonical continuous complex-linear extension of `f`. -/
theorem complexificationEquivOfIsMaximalTotallyReal_apply [ContinuousConstSMul ℂ V] (f : W →L[ℝ] V)
    (hf : Function.Injective f)
    (hmax : IsMaximalTotallyReal ((LinearMap.lsmul ℂ V Complex.I).restrictScalars ℝ)
      f.toLinearMap.range) (u : ℂ ⊗[ℝ] W) :
    f.complexificationEquivOfIsMaximalTotallyReal hf hmax u = f.liftBaseChangeComplex u :=
  DFunLike.congr_fun (f.liftBaseChangeComplex_unique
    (f.complexificationEquivOfIsMaximalTotallyReal hf hmax).toContinuousLinearMap
    (fun w ↦ by simp)) u

end ContinuousLinearMap

end MaximalTotallyReal

namespace TauCeti

section HomComplexification

noncomputable section

open scoped TensorProduct
variable {W D : Type*} [AddCommGroup W] [Module ℝ W] [TopologicalSpace W]
  [AddCommGroup D] [Module ℝ D] [TopologicalSpace D]
  [IsTopologicalAddGroup D] [ContinuousSMul ℝ D]
  [TopologicalSpace (ℂ ⊗[ℝ] W)] [IsComplexificationTopology W]
  [TopologicalSpace (ℂ ⊗[ℝ] D)] [IsComplexificationTopology D]

private def homComplexificationForward (u : ℂ ⊗[ℝ] (W →L[ℝ] D)) :
    (ℂ ⊗[ℝ] W) →L[ℂ] (ℂ ⊗[ℝ] D) :=
  (realPart _ u).baseChangeComplex + Complex.I • (imaginaryPart _ u).baseChangeComplex

private theorem homComplexificationForward_realPart (u : ℂ ⊗[ℝ] (W →L[ℝ] D))
    (v : ℂ ⊗[ℝ] W) :
    realPart D (homComplexificationForward u v) =
      realPart _ u (realPart W v) - imaginaryPart _ u (imaginaryPart W v) := by
  simp [homComplexificationForward, realPart_smul, sub_eq_add_neg]
private theorem homComplexificationForward_imaginaryPart (u : ℂ ⊗[ℝ] (W →L[ℝ] D))
    (v : ℂ ⊗[ℝ] W) :
    imaginaryPart D (homComplexificationForward u v) =
      imaginaryPart _ u (realPart W v) + realPart _ u (imaginaryPart W v) := by
  simp [homComplexificationForward, imaginaryPart_smul, add_comm]

private def homComplexificationRestriction
    (A : (ℂ ⊗[ℝ] W) →L[ℂ] (ℂ ⊗[ℝ] D)) : ℂ ⊗[ℝ] (W →L[ℝ] D) :=
  1 ⊗ₜ[ℝ] (realPartCLM D).comp ((A.restrictScalars ℝ).comp (oneTmulCLM W)) +
    Complex.I ⊗ₜ[ℝ]
      (imaginaryPartCLM D).comp ((A.restrictScalars ℝ).comp (oneTmulCLM W))

/-- The intrinsic scalar-extension comparison on continuous real Hom. It is complex-linear
on the literal tensor and Hom fibres, with no norms or bundle frames. -/
def homComplexificationLinearEquiv : (ℂ ⊗[ℝ] (W →L[ℝ] D)) ≃ₗ[ℂ]
    ((ℂ ⊗[ℝ] W) →L[ℂ] (ℂ ⊗[ℝ] D)) where
  toFun := homComplexificationForward
  invFun := homComplexificationRestriction
  map_add' u v := by
    ext x
    apply complexification_ext <;>
      simp [homComplexificationForward_realPart, homComplexificationForward_imaginaryPart] <;> abel
  map_smul' c u := by
    ext v
    apply complexification_ext <;>
      simp [homComplexificationForward_realPart, homComplexificationForward_imaginaryPart,
        realPart_smul, imaginaryPart_smul] <;> module
  left_inv u := by
    apply complexification_ext <;> ext v <;>
      simp [homComplexificationRestriction, homComplexificationForward_realPart,
        homComplexificationForward_imaginaryPart]
  right_inv A := by
    apply DFunLike.ext
    intro v
    induction v with
    | tmul c v =>
      have ht : c ⊗ₜ[ℝ] v = c • (1 ⊗ₜ[ℝ] v) := by
        simp only [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [ht, map_smul, map_smul]
      congr 1
      apply complexification_ext <;>
        simp [homComplexificationRestriction, homComplexificationForward_realPart,
          homComplexificationForward_imaginaryPart]
    | add u v hu hv => simp only [map_add, hu, hv]

/-- Application is the sum of the real scalar extension and i times the imaginary one. -/
theorem homComplexificationLinearEquiv_apply (u : ℂ ⊗[ℝ] (W →L[ℝ] D)) :
    homComplexificationLinearEquiv u =
      (realPart _ u).baseChangeComplex + Complex.I • (imaginaryPart _ u).baseChangeComplex := by
  rfl

/-- The inverse is obtained from the real and imaginary parts on included real vectors. -/
theorem homComplexificationLinearEquiv_symm_apply
    (A : (ℂ ⊗[ℝ] W) →L[ℂ] (ℂ ⊗[ℝ] D)) :
    homComplexificationLinearEquiv.symm A =
      1 ⊗ₜ[ℝ] (realPartCLM D).comp ((A.restrictScalars ℝ).comp (oneTmulCLM W)) +
        Complex.I ⊗ₜ[ℝ]
          (imaginaryPartCLM D).comp ((A.restrictScalars ℝ).comp (oneTmulCLM W)) := by rfl

/-- Real part of evaluation of the intrinsic Hom comparison. -/
@[simp] theorem homComplexificationLinearEquiv_apply_realPart
    (u : ℂ ⊗[ℝ] (W →L[ℝ] D)) (v : ℂ ⊗[ℝ] W) :
    realPart D (homComplexificationLinearEquiv u v) =
      realPart _ u (realPart W v) - imaginaryPart _ u (imaginaryPart W v) :=
  homComplexificationForward_realPart u v
/-- Imaginary part of evaluation of the intrinsic Hom comparison. -/
@[simp] theorem homComplexificationLinearEquiv_apply_imaginaryPart
    (u : ℂ ⊗[ℝ] (W →L[ℝ] D)) (v : ℂ ⊗[ℝ] W) :
    imaginaryPart D (homComplexificationLinearEquiv u v) =
      imaginaryPart _ u (realPart W v) + realPart _ u (imaginaryPart W v) :=
  homComplexificationForward_imaginaryPart u v

/-- Pure tensor evaluation of the intrinsic Hom comparison. -/
@[simp] theorem homComplexificationLinearEquiv_tmul_apply_tmul
    (z w : ℂ) (T : W →L[ℝ] D) (v : W) :
    homComplexificationLinearEquiv (z ⊗ₜ[ℝ] T) (w ⊗ₜ[ℝ] v) = (z*w) ⊗ₜ[ℝ] T v := by
  apply complexification_ext <;> simp [Complex.mul_re, Complex.mul_im] <;> module

/-- Conjugation commutes with the intrinsic coefficient comparison. -/
theorem homComplexificationLinearEquiv_conj (u : ℂ ⊗[ℝ] (W →L[ℝ] D)) (v : ℂ ⊗[ℝ] W) :
    homComplexificationLinearEquiv (tmulConj _ u) (tmulConj _ v) =
      tmulConj _ (homComplexificationLinearEquiv u v) := by
  apply complexification_ext <;> simp; abel

/-- The intrinsic comparison is natural under real continuous linear source and target maps. -/
theorem homComplexificationLinearEquiv_naturality
    {W' D' : Type*} [AddCommGroup W'] [Module ℝ W'] [TopologicalSpace W']
    [AddCommGroup D'] [Module ℝ D'] [TopologicalSpace D']
    [IsTopologicalAddGroup D'] [ContinuousSMul ℝ D']
    [TopologicalSpace (ℂ ⊗[ℝ] W')] [IsComplexificationTopology W']
    [TopologicalSpace (ℂ ⊗[ℝ] D')] [IsComplexificationTopology D']
    [TopologicalSpace (ℂ ⊗[ℝ] (W →L[ℝ] D))]
    [IsComplexificationTopology (W →L[ℝ] D)]
    [TopologicalSpace (ℂ ⊗[ℝ] (W' →L[ℝ] D'))]
    [IsComplexificationTopology (W' →L[ℝ] D')]
    (U : W' →L[ℝ] W) (S : D →L[ℝ] D') (u : ℂ ⊗[ℝ] (W →L[ℝ] D))
    (v : ℂ ⊗[ℝ] W') :
    homComplexificationLinearEquiv
      ((S.postcomp W').comp (U.precomp D) |>.baseChangeComplex u) v =
        S.baseChangeComplex (homComplexificationLinearEquiv u (U.baseChangeComplex v)) := by
  induction u with
  | tmul z T =>
    induction v with
    | tmul w v => simp
    | add v w hv hw => simp only [map_add, hv, hw]
  | add u w hu hw => simp only [map_add, add_apply, hu, hw]

open scoped TauCeti.Complexification

/-- The intrinsic Hom comparison intertwines arbitrary real fibre frames with the model
continuous Hom comparison. -/
theorem homComplexificationLinearEquiv_in_frames {F G : Type*}
    [SeminormedAddCommGroup F] [NormedSpace ℝ F]
    [SeminormedAddCommGroup G] [NormedSpace ℝ G]
    [TopologicalSpace (ℂ ⊗[ℝ] (W →L[ℝ] D))]
    [IsComplexificationTopology (W →L[ℝ] D)]
    (e : W ≃L[ℝ] F) (d : D ≃L[ℝ] G)
    (u : ℂ ⊗[ℝ] (W →L[ℝ] D)) :
    (e.baseChangeComplex.trans (tensorContinuousLinearEquivComplexification F)).arrowCongr
      (d.baseChangeComplex.trans (tensorContinuousLinearEquivComplexification G))
        (homComplexificationLinearEquiv u) =
      Complexification.continuousLinearMapEquiv F G
        (((e.arrowCongr d).baseChangeComplex.trans
          (tensorContinuousLinearEquivComplexification (F →L[ℝ] G))) u) := by
  ext v <;> simp [sub_eq_add_neg]

end
end HomComplexification
end TauCeti
