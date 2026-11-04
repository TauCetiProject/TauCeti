/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.Algebra.Module.Star
public import TauCeti.Analysis.Normed.Module.Complexification
public import TauCeti.LinearAlgebra.Complex.Conjugation
public import TauCeti.Topology.Algebra.Module.ComplexSmulI

/-!
# The complexification topology on `ℂ ⊗[ℝ] W`

For a real vector space `W`, the algebraic complexification `ℂ ⊗[ℝ] W` splits along `1` and `I`
via the real-linear coordinates `TauCeti.realPart W` and `TauCeti.imaginaryPart W` from
`TauCeti.LinearAlgebra.Complex.Conjugation`. On a real seminormed space `X`,
`TauCeti.Analysis.Normed.Module.Complexification` instead works on the coordinate model
`TauCeti.Complexification X` equipped with the Taylor seminorm, whose underlying topology agrees
with the product topology on `X × X` (`TauCeti.Complexification.equivProd`).

This file connects the two carriers and equips `ℂ ⊗[ℝ] W` with the product topology transported
along `u ↦ (realPart W u, imaginaryPart W u)` whenever `W` is a topological `ℝ`-module. Because
`ℂ` and finite-dimensional real inner product spaces also participate in Mathlib's tensor-product
norms (`Mathlib.Analysis.InnerProductSpace.TensorProduct`), the canonical topology
`TauCeti.complexificationTopology W` is registered in the `TauCeti.Complexification` scope rather
than globally, while downstream theorems and bundle constructions take the `Prop`-valued mixin
`TauCeti.IsComplexificationTopology W` asserting that `(realPart W, imaginaryPart W)` is inducing.
In finite dimensions over `ℝ`, every Hausdorff topological `ℝ`-module topology on `ℂ ⊗[ℝ] W`
satisfies `IsComplexificationTopology W`
(`TauCeti.IsComplexificationTopology.of_finiteDimensional`).

## Main definitions

* `TauCeti.Complexification.conj` and `TauCeti.Complexification.conjCLE`: complex conjugation
  `x + i y ↦ x - i y` on the coordinate model `TauCeti.Complexification`.
* `TauCeti.tensorEquivComplexification`: the canonical `ℂ`-linear isomorphism
  `ℂ ⊗[ℝ] W ≃ₗ[ℂ] TauCeti.Complexification W`, upgraded on real seminormed spaces to
  `TauCeti.tensorContinuousLinearEquivComplexification`.
* `TauCeti.complexificationTopology` and `TauCeti.IsComplexificationTopology`: the topology on
  `ℂ ⊗[ℝ] W` induced by `(realPart W, imaginaryPart W)` (scoped in `TauCeti.Complexification`) and
  its `Prop`-valued characterization class.
* `TauCeti.complexificationEquivProd`: the real continuous linear equivalence
  `ℂ ⊗[ℝ] W ≃L[ℝ] W × W`.
* `TauCeti.realPartCLM`, `TauCeti.imaginaryPartCLM`, `TauCeti.oneTmulCLM`, `TauCeti.ITmulCLM`,
  `TauCeti.tmulConjCLE`, and `TauCeti.tmulConjCLM`: continuous (semi)linear decomposition,
  inclusion, and conjugation operators on `ℂ ⊗[ℝ] W`.
* `ContinuousLinearMap.baseChangeComplex`, `ContinuousLinearEquiv.baseChangeComplex`, and
  `ContinuousLinearEquiv.complexify`: scalar extension of continuous `ℝ`-linear maps and
  equivalences.

## References

* G. A. Muñoz, Y. Sarantopoulos, A. Tonge, *Complexifications of real Banach spaces,
  polynomials and multilinear maps*, Studia Math. 134 (1999), 1–33.
* D. Huybrechts, *Complex Geometry: An Introduction*, Springer (2005), §1.2.
-/

public section

noncomputable section

open scoped TensorProduct

namespace TauCeti

namespace Complexification

section Conj

variable (W : Type*) [AddCommGroup W] [Module ℝ W]

/-- Complex conjugation `x + i y ↦ x - i y` on `TauCeti.Complexification W`, as a
`starRingEnd ℂ`-semilinear involution. -/
def conj : Complexification W →ₛₗ[starRingEnd ℂ] Complexification W where
  toFun z := ⟨z.re, -z.im⟩
  map_add' z w := by ext <;> simp; abel
  map_smul' c z := by
    ext <;> simp only [smul_re, smul_im, Complex.conj_re, Complex.conj_im] <;> module

variable {W}

@[simp]
theorem conj_re (z : Complexification W) : (conj W z).re = z.re := (rfl)

@[simp]
theorem conj_im (z : Complexification W) : (conj W z).im = -z.im := (rfl)

@[simp]
theorem conj_conj (z : Complexification W) : conj W (conj W z) = z := by
  ext <;> simp

theorem conj_involutive : Function.Involutive (conj W) :=
  conj_conj

@[simp]
theorem conj_ofReal (w : W) : conj W (ofReal w) = ofReal w := by
  ext <;> simp

end Conj

section NormedConj

variable (X : Type*) [SeminormedAddCommGroup X] [NormedSpace ℝ X]

/-- Complex conjugation on `TauCeti.Complexification X` as a continuous conjugate-linear
equivalence. -/
def conjCLE : Complexification X ≃L⋆[ℂ] Complexification X :=
  have hcont : Continuous (conj X) :=
    ((equivProd X).symm.continuous.comp <|
      (reCLM X).continuous.prodMk (continuous_neg.comp (imCLM X).continuous)).congr
      fun z ↦ by ext <;> simp
  { toLinearEquiv := LinearEquiv.ofInvolutive (conj X) conj_involutive
    continuous_toFun := hcont
    continuous_invFun := hcont }

variable {X}

@[simp]
theorem coe_conjCLE : ⇑(conjCLE X) = conj X := (rfl)

@[simp]
theorem symm_conjCLE : (conjCLE X).symm = conjCLE X := by
  ext z <;> rfl

theorem conj_complexify {Y : Type*} [SeminormedAddCommGroup Y] [NormedSpace ℝ Y]
    (T : X →L[ℝ] Y) (z : Complexification X) :
    conj Y (T.complexify z) = T.complexify (conj X z) := by
  ext <;> simp

end NormedConj

end Complexification

/-! ### Algebraic equivalence between `ℂ ⊗[ℝ] W` and `TauCeti.Complexification W` -/

section TensorEquiv

variable (W : Type*) [AddCommGroup W] [Module ℝ W]

/-- The canonical `ℂ`-linear isomorphism `ℂ ⊗[ℝ] W ≃ₗ[ℂ] TauCeti.Complexification W` sending
`u` to `⟨realPart W u, imaginaryPart W u⟩` and `⟨x, y⟩` to `1 ⊗ₜ x + I ⊗ₜ y`. -/
def tensorEquivComplexification : ℂ ⊗[ℝ] W ≃ₗ[ℂ] Complexification W where
  toFun u := ⟨realPart W u, imaginaryPart W u⟩
  map_add' u v := by ext <;> simp
  map_smul' c u := by
    ext <;> simp [realPart_smul, imaginaryPart_smul, add_comm]
  invFun z := 1 ⊗ₜ[ℝ] z.re + Complex.I ⊗ₜ[ℝ] z.im
  left_inv := one_tmul_realPart_add_I_tmul_imaginaryPart W
  right_inv z := by ext <;> simp

variable {W}

@[simp]
theorem tensorEquivComplexification_re (u : ℂ ⊗[ℝ] W) :
    (tensorEquivComplexification W u).re = realPart W u := (rfl)

@[simp]
theorem tensorEquivComplexification_im (u : ℂ ⊗[ℝ] W) :
    (tensorEquivComplexification W u).im = imaginaryPart W u := (rfl)

@[simp]
theorem tensorEquivComplexification_tmul (c : ℂ) (w : W) :
    tensorEquivComplexification W (c ⊗ₜ[ℝ] w) = c • Complexification.ofReal w := by
  ext <;> simp

@[simp]
theorem tensorEquivComplexification_symm_apply (z : Complexification W) :
    (tensorEquivComplexification W).symm z = 1 ⊗ₜ[ℝ] z.re + Complex.I ⊗ₜ[ℝ] z.im := (rfl)

theorem realPart_tensorEquivComplexification_symm (z : Complexification W) :
    realPart W ((tensorEquivComplexification W).symm z) = z.re := by
  simp

theorem imaginaryPart_tensorEquivComplexification_symm (z : Complexification W) :
    imaginaryPart W ((tensorEquivComplexification W).symm z) = z.im := by
  simp

theorem tensorEquivComplexification_tmulConj (u : ℂ ⊗[ℝ] W) :
    tensorEquivComplexification W (tmulConj W u) =
      Complexification.conj W (tensorEquivComplexification W u) := by
  obtain ⟨v, w, rfl⟩ := exists_one_tmul_add_I_tmul u
  ext <;> simp [TensorProduct.neg_tmul]

@[simp]
theorem realPart_tmulConj (u : ℂ ⊗[ℝ] W) : realPart W (tmulConj W u) = realPart W u := by
  have h := congrArg Complexification.re (tensorEquivComplexification_tmulConj u)
  simpa using h

@[simp]
theorem imaginaryPart_tmulConj (u : ℂ ⊗[ℝ] W) :
    imaginaryPart W (tmulConj W u) = -imaginaryPart W u := by
  have h := congrArg Complexification.im (tensorEquivComplexification_tmulConj u)
  simpa using h

theorem tmulConj_eq_one_tmul_sub_I_tmul (u : ℂ ⊗[ℝ] W) :
    tmulConj W u = 1 ⊗ₜ[ℝ] realPart W u - Complex.I ⊗ₜ[ℝ] imaginaryPart W u := by
  conv_lhs => rw [← one_tmul_realPart_add_I_tmul_imaginaryPart W u]
  rw [map_add, tmulConj_tmul, tmulConj_tmul, map_one, Complex.conj_I, TensorProduct.neg_tmul,
    sub_eq_add_neg]

theorem tensorEquivComplexification_baseChange {X Y : Type*}
    [SeminormedAddCommGroup X] [NormedSpace ℝ X] [SeminormedAddCommGroup Y] [NormedSpace ℝ Y]
    (T : X →L[ℝ] Y) (u : ℂ ⊗[ℝ] X) :
    tensorEquivComplexification Y (T.toLinearMap.baseChange ℂ u) =
      T.complexify (tensorEquivComplexification X u) := by
  induction u with
  | tmul c x =>
    rw [LinearMap.baseChange_tmul, tensorEquivComplexification_tmul,
      tensorEquivComplexification_tmul, map_smul, ContinuousLinearMap.coe_coe,
      ContinuousLinearMap.complexify_ofReal]
  | add u v hu hv => simp [hu, hv]

end TensorEquiv

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

theorem eq_complexificationTopology (W : Type*) [AddCommGroup W] [Module ℝ W]
    [TopologicalSpace W] [τ : TopologicalSpace (ℂ ⊗[ℝ] W)] [IsComplexificationTopology W] :
    τ = complexificationTopology W :=
  IsComplexificationTopology.eq_complexificationTopology' (W := W)

/-- Low-priority instance recognizing `complexificationTopology W` as an
`IsComplexificationTopology W`, matching `IsModuleTopology`. -/
instance (priority := low) instIsComplexificationTopology {W : Type*} [AddCommGroup W] [Module ℝ W]
    [TopologicalSpace W] :
    letI := complexificationTopology W; IsComplexificationTopology W :=
  letI := complexificationTopology W; ⟨rfl⟩

theorem isComplexificationTopology_scoped (W : Type*) [AddCommGroup W] [Module ℝ W]
    [TopologicalSpace W] :
    letI := complexificationTopology W; IsComplexificationTopology W :=
  letI := complexificationTopology W; ⟨rfl⟩

scoped[TauCeti.Complexification] attribute [instance] TauCeti.isComplexificationTopology_scoped

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
  toFun u := (realPart W u, imaginaryPart W u)
  map_add' u v := by ext <;> simp
  map_smul' r u := by ext <;> simp
  invFun p := 1 ⊗ₜ[ℝ] p.1 + Complex.I ⊗ₜ[ℝ] p.2
  left_inv := one_tmul_realPart_add_I_tmul_imaginaryPart W
  right_inv p := by ext <;> simp
  continuous_toFun := (isInducing_realPart_prod_imaginaryPart W).continuous
  continuous_invFun := by
    rw [continuous_complexification_iff]
    exact ⟨by simpa using continuous_fst, by simpa using continuous_snd⟩

@[simp]
theorem complexificationEquivProd_apply {W : Type*} [AddCommGroup W] [Module ℝ W]
    [TopologicalSpace W] [TopologicalSpace (ℂ ⊗[ℝ] W)] [IsComplexificationTopology W]
    (u : ℂ ⊗[ℝ] W) :
    complexificationEquivProd W u = (realPart W u, imaginaryPart W u) := (rfl)

@[simp]
theorem complexificationEquivProd_symm_apply {W : Type*} [AddCommGroup W] [Module ℝ W]
    [TopologicalSpace W] [TopologicalSpace (ℂ ⊗[ℝ] W)] [IsComplexificationTopology W]
    (p : W × W) :
    (complexificationEquivProd W).symm p = 1 ⊗ₜ[ℝ] p.1 + Complex.I ⊗ₜ[ℝ] p.2 := (rfl)

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

section SimpLemmas

variable {W}

@[simp]
theorem coe_realPartCLM : (realPartCLM W : ℂ ⊗[ℝ] W →ₗ[ℝ] W) = realPart W := by
  ext u; rfl

@[simp]
theorem realPartCLM_apply (u : ℂ ⊗[ℝ] W) : realPartCLM W u = realPart W u := (rfl)

@[simp]
theorem coe_imaginaryPartCLM : (imaginaryPartCLM W : ℂ ⊗[ℝ] W →ₗ[ℝ] W) = imaginaryPart W := by
  ext u; rfl

@[simp]
theorem imaginaryPartCLM_apply (u : ℂ ⊗[ℝ] W) : imaginaryPartCLM W u = imaginaryPart W u := (rfl)

@[simp]
theorem oneTmulCLM_apply (w : W) : oneTmulCLM W w = 1 ⊗ₜ[ℝ] w := by
  simp [oneTmulCLM]

@[simp]
theorem ITmulCLM_apply (w : W) : ITmulCLM W w = Complex.I ⊗ₜ[ℝ] w := by
  simp [ITmulCLM]

end SimpLemmas

/-- Complex conjugation `tmulConj W` on `ℂ ⊗[ℝ] W` as a continuous conjugate-linear equivalence. -/
def tmulConjCLE [ContinuousNeg W] : ℂ ⊗[ℝ] W ≃L⋆[ℂ] ℂ ⊗[ℝ] W :=
  have hcont : Continuous (tmulConj W) := by
    rw [continuous_complexification_iff]
    exact ⟨(realPartCLM W).continuous.congr fun _ ↦ by simp,
      (continuous_neg.comp (imaginaryPartCLM W).continuous).congr fun _ ↦ by simp⟩
  { toLinearEquiv := LinearEquiv.ofInvolutive (tmulConj W) (tmulConj_involutive W)
    continuous_toFun := hcont
    continuous_invFun := hcont }

@[simp]
theorem coe_tmulConjCLE {W : Type*} [AddCommGroup W] [Module ℝ W] [TopologicalSpace W]
    [ContinuousNeg W] [TopologicalSpace (ℂ ⊗[ℝ] W)] [IsComplexificationTopology W] :
    ⇑(tmulConjCLE W) = tmulConj W := (rfl)

@[simp]
theorem symm_tmulConjCLE {W : Type*} [AddCommGroup W] [Module ℝ W] [TopologicalSpace W]
    [ContinuousNeg W] [TopologicalSpace (ℂ ⊗[ℝ] W)] [IsComplexificationTopology W] :
    (tmulConjCLE W).symm = tmulConjCLE W := by
  ext u; rfl

/-- Complex conjugation `tmulConj W` on `ℂ ⊗[ℝ] W` viewed as a continuous `ℝ`-linear map. -/
def tmulConjCLM [ContinuousNeg W] : ℂ ⊗[ℝ] W →L[ℝ] ℂ ⊗[ℝ] W where
  toFun := tmulConj W
  map_add' := map_add (tmulConj W)
  map_smul' _ _ := complexification_ext (by simp) (by simp)
  cont := (tmulConjCLE W).continuous

variable {W} in
@[simp]
theorem tmulConjCLM_apply [ContinuousNeg W] (u : ℂ ⊗[ℝ] W) :
    tmulConjCLM W u = tmulConj W u := (rfl)

instance instT2SpaceComplexification [T2Space W] : T2Space (ℂ ⊗[ℝ] W) :=
  (isEmbedding_realPart_prod_imaginaryPart W).t2Space

instance instIsTopologicalAddGroupComplexification [IsTopologicalAddGroup W] :
    IsTopologicalAddGroup (ℂ ⊗[ℝ] W) :=
  (isInducing_realPart_prod_imaginaryPart W).isTopologicalAddGroup
    (complexificationEquivProd W).toAddEquiv.toAddMonoidHom

instance instContinuousSMulComplexComplexification
    [IsTopologicalAddGroup W] [ContinuousSMul ℝ W] :
    ContinuousSMul ℂ (ℂ ⊗[ℝ] W) where
  continuous_smul := by
    rw [continuous_complexification_iff]
    refine ⟨?_, ?_⟩
    · simp only [realPart_smul]
      exact ((Complex.continuous_re.comp continuous_fst).smul
        ((realPartCLM W).continuous.comp continuous_snd)).sub
          ((Complex.continuous_im.comp continuous_fst).smul
            ((imaginaryPartCLM W).continuous.comp continuous_snd))
    · simp only [imaginaryPart_smul]
      exact ((Complex.continuous_re.comp continuous_fst).smul
        ((imaginaryPartCLM W).continuous.comp continuous_snd)).add
          ((Complex.continuous_im.comp continuous_fst).smul
            ((realPartCLM W).continuous.comp continuous_snd))

instance instContinuousSMulRealComplexification
    [IsTopologicalAddGroup W] [ContinuousSMul ℝ W] :
    ContinuousSMul ℝ (ℂ ⊗[ℝ] W) where
  continuous_smul :=
    (continuous_smul (M := ℂ) (X := ℂ ⊗[ℝ] W)).comp <|
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
  let e : ℂ ⊗[ℝ] W ≃ₗ[ℝ] W × W :=
    { toFun u := (realPart W u, imaginaryPart W u)
      map_add' u v := by ext <;> simp
      map_smul' r u := by ext <;> simp
      invFun p := 1 ⊗ₜ[ℝ] p.1 + Complex.I ⊗ₜ[ℝ] p.2
      left_inv := one_tmul_realPart_add_I_tmul_imaginaryPart W
      right_inv p := by ext <;> simp }
  have : FiniteDimensional ℝ (ℂ ⊗[ℝ] W) := e.symm.finiteDimensional
  exact ⟨e.toContinuousLinearEquiv.toHomeomorph.isInducing.eq_induced⟩

/-- On a real seminormed space `X`, `TauCeti.tensorEquivComplexification X` is a continuous
`ℂ`-linear equivalence between `ℂ ⊗[ℝ] X` (with an `IsComplexificationTopology`) and
`TauCeti.Complexification X` (with the Taylor seminorm). -/
def tensorContinuousLinearEquivComplexification (X : Type*)
    [SeminormedAddCommGroup X] [NormedSpace ℝ X]
    [TopologicalSpace (ℂ ⊗[ℝ] X)] [IsComplexificationTopology X] :
    ℂ ⊗[ℝ] X ≃L[ℂ] Complexification X where
  toLinearEquiv := tensorEquivComplexification X
  continuous_toFun :=
    ((Complexification.equivProd X).symm.continuous.comp
      (complexificationEquivProd X).continuous).congr fun u ↦ by ext <;> simp
  continuous_invFun :=
    ((complexificationEquivProd X).symm.continuous.comp
      (Complexification.equivProd X).continuous).congr fun z ↦ by simp

@[simp]
theorem coe_tensorContinuousLinearEquivComplexification {X : Type*}
    [SeminormedAddCommGroup X] [NormedSpace ℝ X]
    [TopologicalSpace (ℂ ⊗[ℝ] X)] [IsComplexificationTopology X] :
    (tensorContinuousLinearEquivComplexification X).toLinearEquiv =
      tensorEquivComplexification X := (rfl)

@[simp]
theorem tensorContinuousLinearEquivComplexification_apply {X : Type*}
    [SeminormedAddCommGroup X] [NormedSpace ℝ X]
    [TopologicalSpace (ℂ ⊗[ℝ] X)] [IsComplexificationTopology X] (u : ℂ ⊗[ℝ] X) :
    tensorContinuousLinearEquivComplexification X u = tensorEquivComplexification X u := (rfl)

@[simp]
theorem tensorContinuousLinearEquivComplexification_symm_apply {X : Type*}
    [SeminormedAddCommGroup X] [NormedSpace ℝ X]
    [TopologicalSpace (ℂ ⊗[ℝ] X)] [IsComplexificationTopology X] (z : Complexification X) :
    (tensorContinuousLinearEquivComplexification X).symm z =
      (tensorEquivComplexification X).symm z := (rfl)

end Topology

end TauCeti

/-! ### Continuous scalar extension of `ℝ`-linear maps and equivalences -/

namespace ContinuousLinearMap

open TauCeti

variable {W W' W'' : Type*}
  [AddCommGroup W] [Module ℝ W] [TopologicalSpace W]
  [TopologicalSpace (ℂ ⊗[ℝ] W)] [IsComplexificationTopology W]
  [AddCommGroup W'] [Module ℝ W'] [TopologicalSpace W']
  [TopologicalSpace (ℂ ⊗[ℝ] W')] [IsComplexificationTopology W']
  [AddCommGroup W''] [Module ℝ W''] [TopologicalSpace W'']
  [TopologicalSpace (ℂ ⊗[ℝ] W'')] [IsComplexificationTopology W'']

/-- Complex base change `c ⊗ₜ w ↦ c ⊗ₜ f w` of a continuous `ℝ`-linear map `f : W →L[ℝ] W'`, as a
continuous `ℂ`-linear map `ℂ ⊗[ℝ] W →L[ℂ] ℂ ⊗[ℝ] W'`. -/
def baseChangeComplex (f : W →L[ℝ] W') : ℂ ⊗[ℝ] W →L[ℂ] ℂ ⊗[ℝ] W' where
  toLinearMap := f.toLinearMap.baseChange ℂ
  cont := by
    rw [continuous_complexification_iff]
    have hre : ∀ u, realPart W' (f.toLinearMap.baseChange ℂ u) = f (realPart W u) := fun u ↦ by
      obtain ⟨v, w, rfl⟩ := exists_one_tmul_add_I_tmul u
      simp
    have him : ∀ u, imaginaryPart W' (f.toLinearMap.baseChange ℂ u) =
        f (imaginaryPart W u) := fun u ↦ by
      obtain ⟨v, w, rfl⟩ := exists_one_tmul_add_I_tmul u
      simp
    exact ⟨(f.continuous.comp (realPartCLM W).continuous).congr fun u ↦ (hre u).symm,
      (f.continuous.comp (imaginaryPartCLM W).continuous).congr fun u ↦ (him u).symm⟩

@[simp]
theorem toLinearMap_baseChangeComplex (f : W →L[ℝ] W') :
    f.baseChangeComplex.toLinearMap = f.toLinearMap.baseChange ℂ := (rfl)

@[simp]
theorem baseChangeComplex_tmul (f : W →L[ℝ] W') (c : ℂ) (w : W) :
    f.baseChangeComplex (c ⊗ₜ[ℝ] w) = c ⊗ₜ[ℝ] f w := (rfl)

@[simp]
theorem realPart_baseChangeComplex (f : W →L[ℝ] W') (u : ℂ ⊗[ℝ] W) :
    realPart W' (f.baseChangeComplex u) = f (realPart W u) := by
  obtain ⟨v, w, rfl⟩ := exists_one_tmul_add_I_tmul u
  simp [map_add]

@[simp]
theorem imaginaryPart_baseChangeComplex (f : W →L[ℝ] W') (u : ℂ ⊗[ℝ] W) :
    imaginaryPart W' (f.baseChangeComplex u) = f (imaginaryPart W u) := by
  obtain ⟨v, w, rfl⟩ := exists_one_tmul_add_I_tmul u
  simp [map_add]

theorem tmulConj_baseChangeComplex (f : W →L[ℝ] W') (u : ℂ ⊗[ℝ] W) :
    tmulConj W' (f.baseChangeComplex u) = f.baseChangeComplex (tmulConj W u) :=
  tmulConj_baseChange f.toLinearMap u

@[simp]
theorem baseChangeComplex_id :
    (ContinuousLinearMap.id ℝ W).baseChangeComplex = ContinuousLinearMap.id ℂ (ℂ ⊗[ℝ] W) := by
  ext u
  exact LinearMap.congr_fun LinearMap.baseChange_id u

@[simp]
theorem baseChangeComplex_comp (g : W' →L[ℝ] W'') (f : W →L[ℝ] W') :
    (g.comp f).baseChangeComplex = g.baseChangeComplex.comp f.baseChangeComplex := by
  ext u
  induction u with
  | tmul c w => rfl
  | add u v hu hv => simp [hu, hv]

end ContinuousLinearMap

namespace ContinuousLinearEquiv

open TauCeti

section TopologicalModule

variable {W W' W'' : Type*}
  [AddCommGroup W] [Module ℝ W] [TopologicalSpace W]
  [TopologicalSpace (ℂ ⊗[ℝ] W)] [IsComplexificationTopology W]
  [AddCommGroup W'] [Module ℝ W'] [TopologicalSpace W']
  [TopologicalSpace (ℂ ⊗[ℝ] W')] [IsComplexificationTopology W']
  [AddCommGroup W''] [Module ℝ W''] [TopologicalSpace W'']
  [TopologicalSpace (ℂ ⊗[ℝ] W'')] [IsComplexificationTopology W'']

/-- Complex base change `c ⊗ₜ w ↦ c ⊗ₜ e w` of a continuous `ℝ`-linear equivalence `e : W ≃L[ℝ] W'`,
as a continuous `ℂ`-linear equivalence `ℂ ⊗[ℝ] W ≃L[ℂ] ℂ ⊗[ℝ] W'`. -/
def baseChangeComplex (e : W ≃L[ℝ] W') : ℂ ⊗[ℝ] W ≃L[ℂ] ℂ ⊗[ℝ] W' :=
  ContinuousLinearEquiv.equivOfInverse
    e.toContinuousLinearMap.baseChangeComplex
    e.symm.toContinuousLinearMap.baseChangeComplex
    (fun u ↦ by
      have h := DFunLike.congr_fun
        (ContinuousLinearMap.baseChangeComplex_comp e.symm.toContinuousLinearMap
          e.toContinuousLinearMap).symm u
      simpa using h)
    (fun u ↦ by
      have h := DFunLike.congr_fun
        (ContinuousLinearMap.baseChangeComplex_comp e.toContinuousLinearMap
          e.symm.toContinuousLinearMap).symm u
      simpa using h)

@[simp]
theorem toContinuousLinearMap_baseChangeComplex (e : W ≃L[ℝ] W') :
    e.baseChangeComplex.toContinuousLinearMap = e.toContinuousLinearMap.baseChangeComplex := (rfl)

@[simp]
theorem symm_baseChangeComplex (e : W ≃L[ℝ] W') :
    e.baseChangeComplex.symm = e.symm.baseChangeComplex := (rfl)

@[simp]
theorem baseChangeComplex_tmul (e : W ≃L[ℝ] W') (c : ℂ) (w : W) :
    e.baseChangeComplex (c ⊗ₜ[ℝ] w) = c ⊗ₜ[ℝ] e w := (rfl)

@[simp]
theorem realPart_baseChangeComplex (e : W ≃L[ℝ] W') (u : ℂ ⊗[ℝ] W) :
    realPart W' (e.baseChangeComplex u) = e (realPart W u) :=
  e.toContinuousLinearMap.realPart_baseChangeComplex u

@[simp]
theorem imaginaryPart_baseChangeComplex (e : W ≃L[ℝ] W') (u : ℂ ⊗[ℝ] W) :
    imaginaryPart W' (e.baseChangeComplex u) = e (imaginaryPart W u) :=
  e.toContinuousLinearMap.imaginaryPart_baseChangeComplex u

@[simp]
theorem baseChangeComplex_refl :
    (ContinuousLinearEquiv.refl ℝ W).baseChangeComplex =
      ContinuousLinearEquiv.refl ℂ (ℂ ⊗[ℝ] W) := by
  ext u
  exact DFunLike.congr_fun ContinuousLinearMap.baseChangeComplex_id u

@[simp]
theorem baseChangeComplex_trans (e : W ≃L[ℝ] W') (e' : W' ≃L[ℝ] W'') :
    (e.trans e').baseChangeComplex = e.baseChangeComplex.trans e'.baseChangeComplex := by
  ext u
  exact DFunLike.congr_fun
    (ContinuousLinearMap.baseChangeComplex_comp e'.toContinuousLinearMap e.toContinuousLinearMap) u

end TopologicalModule

section Seminormed

variable {X Y Z : Type*}
  [SeminormedAddCommGroup X] [NormedSpace ℝ X]
  [SeminormedAddCommGroup Y] [NormedSpace ℝ Y]
  [SeminormedAddCommGroup Z] [NormedSpace ℝ Z]

/-- Complexification of a continuous `ℝ`-linear equivalence between real seminormed spaces, as a
continuous `ℂ`-linear equivalence between their Taylor-seminormed complexifications. -/
def complexify (e : X ≃L[ℝ] Y) : Complexification X ≃L[ℂ] Complexification Y :=
  ContinuousLinearEquiv.equivOfInverse
    e.toContinuousLinearMap.complexify
    e.symm.toContinuousLinearMap.complexify
    (fun z ↦ by
      have h := DFunLike.congr_fun
        (ContinuousLinearMap.complexify_comp e.symm.toContinuousLinearMap
          e.toContinuousLinearMap).symm z
      simpa using h)
    (fun z ↦ by
      have h := DFunLike.congr_fun
        (ContinuousLinearMap.complexify_comp e.toContinuousLinearMap
          e.symm.toContinuousLinearMap).symm z
      simpa using h)

@[simp]
theorem toContinuousLinearMap_complexify (e : X ≃L[ℝ] Y) :
    e.complexify.toContinuousLinearMap = e.toContinuousLinearMap.complexify := (rfl)

@[simp]
theorem symm_complexify (e : X ≃L[ℝ] Y) :
    e.complexify.symm = e.symm.complexify := (rfl)

@[simp]
theorem complexify_apply_re (e : X ≃L[ℝ] Y) (z : Complexification X) :
    (e.complexify z).re = e z.re :=
  e.toContinuousLinearMap.complexify_apply_re z

@[simp]
theorem complexify_apply_im (e : X ≃L[ℝ] Y) (z : Complexification X) :
    (e.complexify z).im = e z.im :=
  e.toContinuousLinearMap.complexify_apply_im z

@[simp]
theorem complexify_refl :
    (ContinuousLinearEquiv.refl ℝ X).complexify =
      ContinuousLinearEquiv.refl ℂ (Complexification X) := by
  ext z <;> simp

@[simp]
theorem complexify_trans (e : X ≃L[ℝ] Y) (e' : Y ≃L[ℝ] Z) :
    (e.trans e').complexify = e.complexify.trans e'.complexify := by
  ext z <;> simp

end Seminormed

end ContinuousLinearEquiv

end
