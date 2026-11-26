/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Laplacian
public import TauCeti.Analysis.Distribution.TestFunction.Divergence
import Mathlib.Analysis.Calculus.FDeriv.Equiv
import TauCeti.Analysis.Calculus.IteratedFDeriv.CompContinuousLinearEquiv
import TauCeti.Analysis.InnerProductSpace.Laplacian.Basic

/-!
# Transport of test functions along continuous linear equivalences

A continuous linear equivalence `e : E ≃L[ℝ] E'` carries a test function `φ` on an open set `V`
of `E` to the test function `φ ∘ e.symm` on any open set `Ω` of `E'` containing `e '' V`. This
transport is continuous for the LF topologies, so precomposing with it transports distributions
along `e`. Its derivative is the derivative of `φ` precomposed with `e.symm`. A test vector field
is transported by also applying `e` to its values, `y ↦ e (φ (e.symm y))`; its divergence is then
the transported divergence of `φ`, because the trace is invariant under conjugation.

These formulas transport the test-field pairings that define distributional derivatives,
variation and perimeter along linear changes of variables, in particular along rotations and
reflections.

## Main declarations

* `ContinuousLinearEquiv.transportSupportedIn`: transport of tests supported in a compact `K` to
  tests supported in `e '' K`, as a continuous `𝕜`-linear map.
* `ContinuousLinearEquiv.transportTestFunction`: transport of test functions along a continuous
  linear equivalence, changing their domain, as a continuous `𝕜`-linear map.
* `ContinuousLinearEquiv.transportTestFunction_apply`: evaluation of a transported test function.
* `ContinuousLinearEquiv.transportTestFunction_trans`,
  `ContinuousLinearEquiv.transportTestFunction_transportTestFunction_symm`: functoriality.
* `ContinuousLinearEquiv.transportTestFunction_postcompCLM`: transport commutes with
  postcomposition by a continuous linear map.
* `ContinuousLinearEquiv.fderiv_transportTestFunction`,
  `ContinuousLinearEquiv.lineDeriv_transportTestFunction`: the Fréchet and line derivatives of a
  transported test function, and `ContinuousLinearEquiv.inner_gradient_transportTestFunction`
  pairs its gradient with a direction.
* `LinearIsometryEquiv.laplacian_transportTestFunction`: the Laplacian of a test function
  transported along a linear isometry equivalence.
* `ContinuousLinearEquiv.divergenceCLM_postcompCLM_transportTestFunction`: the divergence of a
  transported test vector field is the transported divergence.
* `TestFunction.compConj`: a test function on a conjugation-invariant open set of `ℂ` composed
  with complex conjugation, an involution (`TestFunction.compConj_compConj`), with its derivatives
  `TestFunction.fderiv_compConj` and `TestFunction.lineDeriv_compConj` and its Laplacian
  `TestFunction.laplacian_compConj`.

## Implementation notes

Both transports work at every order of smoothness `n`, and are linear over any scalar field `𝕜`
acting on the values compatibly with `ℝ`, such as `ℝ` itself or `ℂ` for complex test functions.
Continuity of `transportTestFunction` is checked on each space of tests supported in a fixed
compact `K ⊆ V`, whose transports are supported in `e '' K` (`transportSupportedIn`); there the
`i`-th derivative of `φ ∘ e.symm` is bounded by `‖e.symm‖ ^ i` times that of `φ`.
-/

public section

noncomputable section

namespace ContinuousLinearEquiv

open Set TestFunction TopologicalSpace
open scoped Distributions Gradient InnerProductSpace

variable {𝕜 E E' F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedSpace 𝕜 F] {V : Opens E} {Ω : Opens E'} {n : ℕ∞}

section SupportedIn

variable [SMulCommClass ℝ 𝕜 F]

variable (𝕜) in
/-- Transport along `e` of tests supported in a compact `K`, which are supported in `e '' K`, as a
continuous `𝕜`-linear map. Its `i`-th seminorm is at most `‖e.symm‖ ^ i` times that of the
original test. -/
def transportSupportedIn (e : E ≃L[ℝ] E') (K : Compacts E) :
    𝓓^{n}_{K}(E, F) →L[𝕜] 𝓓^{n}_{K.map e e.continuous}(E', F) :=
  letI P : 𝓓^{n}_{K}(E, F) →ₗ[𝕜] 𝓓^{n}_{K.map e e.continuous}(E', F) :=
    { toFun φ := ⟨φ ∘ e.symm, φ.contDiff.comp e.symm.contDiff, fun y hy ↦
        Function.notMem_support.1 fun h ↦ hy <| by
          rw [Compacts.coe_map]
          exact ⟨e.symm y, φ.support_subset h, e.apply_symm_apply y⟩⟩
      map_add' φ ψ := ContDiffMapSupportedIn.ext fun _ ↦ rfl
      map_smul' c φ := ContDiffMapSupportedIn.ext fun _ ↦ rfl }
  { toLinearMap := P
    cont := by
      refine WithSeminorms.continuous_of_isBounded (ContDiffMapSupportedIn.withSeminorms ..)
        (ContDiffMapSupportedIn.withSeminorms ..) _ (.of_real fun i ↦ ?_)
      refine ⟨{i}, ‖(e.symm : E' →L[ℝ] E)‖ ^ i, fun φ ↦ ((P φ).seminorm_le_iff 𝕜
        (by positivity) i).2 fun hi y _ ↦ ?_⟩
      rw [Finset.sup_singleton]
      exact (e.symm.norm_iteratedFDeriv_comp_right_le φ y i).trans <| mul_le_mul_of_nonneg_left
        (ContDiffMapSupportedIn.norm_iteratedFDeriv_apply_le_seminorm 𝕜 hi) (by positivity) }

/-- A transported test supported in `K` is evaluated at the inversely transported point. -/
@[simp]
theorem transportSupportedIn_apply (e : E ≃L[ℝ] E') (K : Compacts E) (φ : 𝓓^{n}_{K}(E, F))
    (y : E') : transportSupportedIn 𝕜 e K φ y = φ (e.symm y) :=
  (rfl)

end SupportedIn

variable [Algebra ℝ 𝕜] [IsScalarTower ℝ 𝕜 F]

variable (𝕜) in
/-- Transport test functions on `V` along a continuous linear equivalence `e`, regarding the
result `φ ∘ e.symm` as a test function on an open set `Ω` containing `e '' V`. This is a
continuous `𝕜`-linear map for the LF topologies. -/
def transportTestFunction (e : E ≃L[ℝ] E') (hVO : MapsTo e V Ω) :
    𝓓^{n}(V, F) →L[𝕜] 𝓓^{n}(Ω, F) :=
  letI T (φ : 𝓓^{n}(V, F)) : 𝓓^{n}(Ω, F) :=
    ⟨φ ∘ e.symm, φ.contDiff.comp e.symm.contDiff,
      φ.hasCompactSupport.comp_homeomorph e.symm.toHomeomorph,
      by
        intro y hy
        -- Composition with the homeomorphism underlying `e.symm` is the function `φ ∘ e.symm`,
        -- so its topological support is the preimage of that of `φ`.
        have hy' : e.symm y ∈ tsupport (φ : E → F) := by
          have hycomp : y ∈ tsupport ((φ : E → F) ∘ e.symm.toHomeomorph) := hy
          rwa [tsupport_comp_eq_preimage] at hycomp
        simpa only [ContinuousLinearEquiv.apply_symm_apply] using hVO (φ.tsupport_subset hy')⟩
  TestFunction.limitCLM 𝕜 T
    (fun K hK ↦ ofSupportedInCLM 𝕜 (by
        rw [Compacts.coe_map]
        exact image_subset_iff.2 fun x hx ↦ hVO (hK hx)) ∘L
      transportSupportedIn 𝕜 e K)
    (fun _ _ _ ↦ rfl)

/-- A transported test function is evaluated at the inversely transported point. -/
@[simp]
theorem transportTestFunction_apply (e : E ≃L[ℝ] E') (hVO : MapsTo e V Ω) (φ : 𝓓^{n}(V, F))
    (y : E') : transportTestFunction 𝕜 e hVO φ y = φ (e.symm y) :=
  (rfl)

/-- Transporting along a composite of continuous linear equivalences is transporting along each
in turn. -/
theorem transportTestFunction_trans {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace ℝ E'']
    {W : Opens E''} (e₁ : E ≃L[ℝ] E') (e₂ : E' ≃L[ℝ] E'') (h₁ : MapsTo e₁ V Ω)
    (h₂ : MapsTo e₂ Ω W) (h : MapsTo (e₁.trans e₂) V W) (φ : 𝓓^{n}(V, F)) :
    (e₁.trans e₂).transportTestFunction 𝕜 h φ =
      e₂.transportTestFunction 𝕜 h₂ (e₁.transportTestFunction 𝕜 h₁ φ) := by
  ext y
  simp

/-- Transporting along `e.symm` and then along `e` gives back the original test function. -/
@[simp]
theorem transportTestFunction_transportTestFunction_symm (e : E ≃L[ℝ] E') (hVO : MapsTo e V Ω)
    (hOV : MapsTo e.symm Ω V) (φ : 𝓓^{n}(Ω, F)) :
    e.transportTestFunction 𝕜 hVO (e.symm.transportTestFunction 𝕜 hOV φ) = φ := by
  ext y
  simp

/-- Transport commutes with postcomposition by a continuous linear map. -/
theorem transportTestFunction_postcompCLM {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedSpace 𝕜 G] [IsScalarTower ℝ 𝕜 G] (e : E ≃L[ℝ] E') (hVO : MapsTo e V Ω) (L : F →L[𝕜] G)
    (φ : 𝓓^{n}(V, F)) :
    e.transportTestFunction 𝕜 hVO (postcompCLM L φ) =
      postcompCLM L (e.transportTestFunction 𝕜 hVO φ) := by
  ext y
  simp

/-- The Fréchet derivative of a transported test function is the transported derivative,
precomposed with `e.symm`. -/
@[simp]
theorem fderiv_transportTestFunction (e : E ≃L[ℝ] E') (hVO : MapsTo e V Ω) (φ : 𝓓^{n}(V, F))
    (y : E') :
    fderiv ℝ (transportTestFunction 𝕜 e hVO φ : E' → F) y =
      (fderiv ℝ (φ : E → F) (e.symm y)).comp (e.symm : E' →L[ℝ] E) :=
  e.symm.comp_right_fderiv

/-- Pairing the gradient of a transported test function with a direction pulls both the
point and the direction back along the inverse equivalence. -/
theorem inner_gradient_transportTestFunction
    {H H' : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [NormedAddCommGroup H'] [InnerProductSpace ℝ H'] [CompleteSpace H']
    {U : Opens H} {W : Opens H'} (e : H ≃L[ℝ] H') (hUW : MapsTo e U W)
    (φ : 𝓓^{n}(U, ℝ)) (y v : H') :
    ⟪v, ∇ (e.transportTestFunction ℝ hUW φ : H' → ℝ) y⟫_ℝ =
      ⟪e.symm v, ∇ (φ : H → ℝ) (e.symm y)⟫_ℝ := by
  simp [inner_gradient_right]

/-- The line derivative of a transported test function at `y` in the direction `v` is that of the
original test function at `e.symm y` in the direction `e.symm v`. -/
@[simp]
theorem lineDeriv_transportTestFunction (e : E ≃L[ℝ] E') (hVO : MapsTo e V Ω)
    (φ : 𝓓^{n}(V, F)) (y v : E') :
    lineDeriv ℝ (transportTestFunction 𝕜 e hVO φ : E' → F) y v =
      lineDeriv ℝ (φ : E → F) (e.symm y) (e.symm v) := by
  simp only [lineDeriv, transportTestFunction_apply, map_add, map_smul]

/-- The divergence of a transported test vector field `y ↦ e (φ (e.symm y))` is the transported
divergence of `φ`. -/
@[simp]
theorem divergenceCLM_postcompCLM_transportTestFunction [FiniteDimensional ℝ E]
    [FiniteDimensional ℝ E'] (e : E ≃L[ℝ] E') (hVO : MapsTo e V Ω) (φ : 𝓓(V, E)) :
    divergenceCLM (postcompCLM (e : E →L[ℝ] E') (transportTestFunction ℝ e hVO φ)) =
      transportTestFunction ℝ e hVO (divergenceCLM φ) := by
  ext y
  rw [divergenceCLM_apply, transportTestFunction_apply, divergenceCLM_apply,
    ← LinearMap.trace_conj' _ e.toLinearEquiv]
  congr 1
  ext v
  simp [e.comp_fderiv, LinearEquiv.conj_apply]

end ContinuousLinearEquiv

namespace LinearIsometryEquiv

open Set TestFunction TopologicalSpace InnerProductSpace
open scoped Distributions Laplacian

variable {E E' F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup E'] [InnerProductSpace ℝ E'] [FiniteDimensional ℝ E']
  [NormedAddCommGroup F] [NormedSpace ℝ F] {V : Opens E} {Ω : Opens E'} {n : ℕ∞}

/-- The Laplacian of a test function transported along a linear isometry equivalence `e` is the
transported Laplacian: at `y` it is the Laplacian of the original test function at `e.symm y`. -/
@[simp]
theorem laplacian_transportTestFunction (e : E ≃ₗᵢ[ℝ] E')
    (hVO : MapsTo (e.toContinuousLinearEquiv : E → E') V Ω) (φ : 𝓓^{n}(V, F)) (y : E') :
    Δ (e.toContinuousLinearEquiv.transportTestFunction ℝ hVO φ : E' → F) y =
      Δ (φ : E → F) (e.symm y) := by
  have h : (e.toContinuousLinearEquiv.transportTestFunction ℝ hVO φ : E' → F) =
      (φ : E → F) ∘ e.symm := by
    ext z
    simp
  rw [h, TauCeti.laplacian_comp_linearIsometryEquiv_right, Function.comp_apply]

end LinearIsometryEquiv

namespace TestFunction

open Complex InnerProductSpace Set TopologicalSpace
open scoped ComplexConjugate Distributions Laplacian

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {Ω : Opens ℂ} {n : ℕ∞}

private theorem mapsTo_conjLIE (hΩ : MapsTo (starRingEnd ℂ) Ω Ω) :
    MapsTo (conjLIE.toContinuousLinearEquiv : ℂ → ℂ) Ω Ω := fun z hz ↦ by
  rw [LinearIsometryEquiv.coe_toContinuousLinearEquiv, conjLIE_apply]
  exact hΩ hz

/-- Precompose test functions on a conjugation-invariant open set `Ω ⊆ ℂ` with complex
conjugation, `φ ↦ φ ∘ conj`: the transport along `conj`, which is its own inverse. -/
def compConj (hΩ : MapsTo (starRingEnd ℂ) Ω Ω) : 𝓓^{n}(Ω, F) →L[ℝ] 𝓓^{n}(Ω, F) :=
  conjLIE.toContinuousLinearEquiv.transportTestFunction ℝ (mapsTo_conjLIE hΩ)

/-- The test function `φ ∘ conj` is evaluated at the conjugate point. -/
@[simp]
theorem compConj_apply (hΩ : MapsTo (starRingEnd ℂ) Ω Ω) (φ : 𝓓^{n}(Ω, F)) (z : ℂ) :
    compConj hΩ φ z = φ (conj z) := by
  rw [compConj, ContinuousLinearEquiv.transportTestFunction_apply,
    ← LinearIsometryEquiv.toContinuousLinearEquiv_symm, conjLIE_symm,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv, conjLIE_apply]

/-- Conjugating twice gives back the original test function. -/
@[simp]
theorem compConj_compConj (hΩ : MapsTo (starRingEnd ℂ) Ω Ω) (φ : 𝓓^{n}(Ω, F)) :
    compConj hΩ (compConj hΩ φ) = φ := by
  ext z
  simp

/-- Precomposition with `conj` commutes with postcomposition by a continuous linear map. -/
theorem compConj_postcompCLM {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (hΩ : MapsTo (starRingEnd ℂ) Ω Ω) (L : F →L[ℝ] G) (φ : 𝓓^{n}(Ω, F)) :
    compConj hΩ (postcompCLM L φ) = postcompCLM L (compConj hΩ φ) :=
  ContinuousLinearEquiv.transportTestFunction_postcompCLM _ _ L φ

/-- The derivative of `φ ∘ conj` at `z` is that of `φ` at `conj z`, precomposed with `conj`. -/
@[simp]
theorem fderiv_compConj (hΩ : MapsTo (starRingEnd ℂ) Ω Ω) (φ : 𝓓^{n}(Ω, F)) (z : ℂ) :
    fderiv ℝ (compConj hΩ φ : ℂ → F) z =
      (fderiv ℝ (φ : ℂ → F) (conj z)).comp (conjCLE : ℂ →L[ℝ] ℂ) := by
  ext v
  simp only [compConj, ContinuousLinearEquiv.fderiv_transportTestFunction,
    ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_symm_toContinuousLinearEquiv, conjLIE_symm, conjLIE_apply,
    conjCLE_apply]

/-- The derivative of `φ ∘ conj` at `z` in the direction `v` is that of `φ` at `conj z` in the
direction `conj v`. -/
theorem fderiv_compConj_apply (hΩ : MapsTo (starRingEnd ℂ) Ω Ω) (φ : 𝓓^{n}(Ω, F)) (z v : ℂ) :
    fderiv ℝ (compConj hΩ φ : ℂ → F) z v = fderiv ℝ (φ : ℂ → F) (conj z) (conj v) := by
  rw [fderiv_compConj, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    conjCLE_apply]

/-- The line derivative of `φ ∘ conj` at `z` in the direction `v` is that of `φ` at `conj z` in
the direction `conj v`. -/
@[simp]
theorem lineDeriv_compConj (hΩ : MapsTo (starRingEnd ℂ) Ω Ω) (φ : 𝓓^{n}(Ω, F)) (z v : ℂ) :
    lineDeriv ℝ (compConj hΩ φ : ℂ → F) z v = lineDeriv ℝ (φ : ℂ → F) (conj z) (conj v) := by
  rw [compConj, ContinuousLinearEquiv.lineDeriv_transportTestFunction,
    LinearIsometryEquiv.coe_symm_toContinuousLinearEquiv, conjLIE_symm, conjLIE_apply,
    conjLIE_apply]

/-- The Laplacian of `φ ∘ conj` at `z` is that of `φ` at `conj z`. -/
@[simp]
theorem laplacian_compConj (hΩ : MapsTo (starRingEnd ℂ) Ω Ω) (φ : 𝓓^{n}(Ω, F)) (z : ℂ) :
    Δ (compConj hΩ φ : ℂ → F) z = Δ (φ : ℂ → F) (conj z) := by
  rw [compConj, LinearIsometryEquiv.laplacian_transportTestFunction, conjLIE_symm, conjLIE_apply]

end TestFunction
