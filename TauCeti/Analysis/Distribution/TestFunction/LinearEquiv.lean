/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.TestFunction.Divergence
import Mathlib.Analysis.Calculus.FDeriv.Equiv
import TauCeti.Analysis.Calculus.IteratedFDeriv.CompContinuousLinearEquiv

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
  tests supported in `e '' K`, as a continuous linear map.
* `ContinuousLinearEquiv.transportTestFunction`: transport of test functions along a continuous
  linear equivalence, changing their domain, as a continuous linear map.
* `ContinuousLinearEquiv.transportTestFunction_apply`: evaluation of a transported test function.
* `ContinuousLinearEquiv.transportTestFunction_trans`,
  `ContinuousLinearEquiv.transportTestFunction_transportTestFunction_symm`: functoriality.
* `ContinuousLinearEquiv.transportTestFunction_postcompCLM`: transport commutes with
  postcomposition by a continuous linear map.
* `ContinuousLinearEquiv.fderiv_transportTestFunction`: the Fréchet derivative of a transported
  test function.
* `ContinuousLinearEquiv.divergenceCLM_postcompCLM_transportTestFunction`: the divergence of a
  transported test vector field is the transported divergence.

## Implementation notes

Both transports work at every order of smoothness `n`. Continuity of `transportTestFunction` is
checked on each space of tests supported in a fixed compact `K ⊆ V`, whose transports are
supported in `e '' K` (`transportSupportedIn`); there the `i`-th derivative of `φ ∘ e.symm` is
bounded by `‖e.symm‖ ^ i` times that of `φ`.
-/

public section

noncomputable section

namespace ContinuousLinearEquiv

open Set TestFunction TopologicalSpace
open scoped Distributions

variable {E E' F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : Opens E} {Ω : Opens E'} {n : ℕ∞}

/-- Transport along `e` of tests supported in a compact `K`, which are supported in `e '' K`, as a
continuous linear map. Its `i`-th seminorm is at most `‖e.symm‖ ^ i` times that of the original
test. -/
def transportSupportedIn (e : E ≃L[ℝ] E') (K : Compacts E) :
    𝓓^{n}_{K}(E, F) →L[ℝ] 𝓓^{n}_{K.map e e.continuous}(E', F) :=
  letI P : 𝓓^{n}_{K}(E, F) →ₗ[ℝ] 𝓓^{n}_{K.map e e.continuous}(E', F) :=
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
      refine ⟨{i}, ‖(e.symm : E' →L[ℝ] E)‖ ^ i, fun φ ↦ ((P φ).seminorm_le_iff ℝ
        (by positivity) i).2 fun hi y _ ↦ ?_⟩
      rw [Finset.sup_singleton]
      exact (e.symm.norm_iteratedFDeriv_comp_right_le φ y i).trans <| mul_le_mul_of_nonneg_left
        (ContDiffMapSupportedIn.norm_iteratedFDeriv_apply_le_seminorm ℝ hi) (by positivity) }

/-- A transported test supported in `K` is evaluated at the inversely transported point. -/
@[simp]
theorem transportSupportedIn_apply (e : E ≃L[ℝ] E') (K : Compacts E) (φ : 𝓓^{n}_{K}(E, F))
    (y : E') : transportSupportedIn e K φ y = φ (e.symm y) :=
  (rfl)

/-- Transport test functions on `V` along a continuous linear equivalence `e`, regarding the
result `φ ∘ e.symm` as a test function on an open set `Ω` containing `e '' V`. This is a
continuous linear map for the LF topologies. -/
def transportTestFunction (e : E ≃L[ℝ] E') (hVO : MapsTo e V Ω) :
    𝓓^{n}(V, F) →L[ℝ] 𝓓^{n}(Ω, F) :=
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
  TestFunction.limitCLM ℝ T
    (fun K hK ↦ ofSupportedInCLM ℝ (by
        rw [Compacts.coe_map]
        exact image_subset_iff.2 fun x hx ↦ hVO (hK hx)) ∘L
      transportSupportedIn e K)
    (fun _ _ _ ↦ rfl)

/-- A transported test function is evaluated at the inversely transported point. -/
@[simp]
theorem transportTestFunction_apply (e : E ≃L[ℝ] E') (hVO : MapsTo e V Ω) (φ : 𝓓^{n}(V, F))
    (y : E') : transportTestFunction e hVO φ y = φ (e.symm y) :=
  (rfl)

/-- Transporting along a composite of continuous linear equivalences is transporting along each
in turn. -/
theorem transportTestFunction_trans {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace ℝ E'']
    {W : Opens E''} (e₁ : E ≃L[ℝ] E') (e₂ : E' ≃L[ℝ] E'') (h₁ : MapsTo e₁ V Ω)
    (h₂ : MapsTo e₂ Ω W) (h : MapsTo (e₁.trans e₂) V W) (φ : 𝓓^{n}(V, F)) :
    (e₁.trans e₂).transportTestFunction h φ =
      e₂.transportTestFunction h₂ (e₁.transportTestFunction h₁ φ) := by
  ext y
  simp

/-- Transporting along `e.symm` and then along `e` gives back the original test function. -/
@[simp]
theorem transportTestFunction_transportTestFunction_symm (e : E ≃L[ℝ] E') (hVO : MapsTo e V Ω)
    (hOV : MapsTo e.symm Ω V) (φ : 𝓓^{n}(Ω, F)) :
    e.transportTestFunction hVO (e.symm.transportTestFunction hOV φ) = φ := by
  ext y
  simp

/-- Transport commutes with postcomposition by a continuous linear map. -/
theorem transportTestFunction_postcompCLM {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (e : E ≃L[ℝ] E') (hVO : MapsTo e V Ω) (L : F →L[ℝ] G) (φ : 𝓓^{n}(V, F)) :
    e.transportTestFunction hVO (postcompCLM L φ) =
      postcompCLM L (e.transportTestFunction hVO φ) := by
  ext y
  simp

/-- The Fréchet derivative of a transported test function is the transported derivative,
precomposed with `e.symm`. -/
@[simp]
theorem fderiv_transportTestFunction (e : E ≃L[ℝ] E') (hVO : MapsTo e V Ω) (φ : 𝓓(V, F))
    (y : E') :
    fderiv ℝ (transportTestFunction e hVO φ : E' → F) y =
      (fderiv ℝ (φ : E → F) (e.symm y)).comp (e.symm : E' →L[ℝ] E) :=
  e.symm.comp_right_fderiv

/-- The divergence of a transported test vector field `y ↦ e (φ (e.symm y))` is the transported
divergence of `φ`. -/
@[simp]
theorem divergenceCLM_postcompCLM_transportTestFunction [FiniteDimensional ℝ E]
    [FiniteDimensional ℝ E'] (e : E ≃L[ℝ] E') (hVO : MapsTo e V Ω) (φ : 𝓓(V, E)) :
    divergenceCLM (postcompCLM (e : E →L[ℝ] E') (transportTestFunction e hVO φ)) =
      transportTestFunction e hVO (divergenceCLM φ) := by
  ext y
  rw [divergenceCLM_apply, transportTestFunction_apply, divergenceCLM_apply,
    ← LinearMap.trace_conj' _ e.toLinearEquiv]
  congr 1
  ext v
  simp [e.comp_fderiv, LinearEquiv.conj_apply]

end ContinuousLinearEquiv
