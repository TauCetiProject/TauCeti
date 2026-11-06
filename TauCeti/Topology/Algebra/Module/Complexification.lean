/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import TauCeti.Analysis.Normed.Module.Complexification
public import TauCeti.LinearAlgebra.Complex.Conjugation
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
`TauCeti.tmulConjCLE`, `TauCeti.tmulConjCLM`, `ContinuousLinearMap.baseChangeComplex`, and
`ContinuousLinearEquiv.baseChangeComplex`.

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
  equivOfInverse e.toContinuousLinearMap.baseChangeComplex
    e.symm.toContinuousLinearMap.baseChangeComplex
    (fun u ↦ by
      simpa using DFunLike.congr_fun
        (e.symm.toContinuousLinearMap.baseChangeComplex_comp e.toContinuousLinearMap).symm u)
    (fun u ↦ by
      simpa using DFunLike.congr_fun
        (e.toContinuousLinearMap.baseChangeComplex_comp e.symm.toContinuousLinearMap).symm u)

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
