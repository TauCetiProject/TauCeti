/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.TestFunction.Divergence
import Mathlib.Analysis.Calculus.FDeriv.Equiv

/-!
# Transport of test functions along continuous linear equivalences

A continuous linear equivalence `e : E ≃L[ℝ] E'` carries a test function `φ` on an open set `V`
of `E` to the test function `φ ∘ e.symm` on any open set `Ω` of `E'` containing `e '' V`. Its
derivative is the derivative of `φ` precomposed with `e.symm`. A test vector field is transported
by also applying `e` to its values, `y ↦ e (φ (e.symm y))`; its divergence is then the transported
divergence of `φ`, because the trace is invariant under conjugation.

These formulas transport the test-field pairings that define distributional derivatives,
variation and perimeter along linear changes of variables, in particular along rotations and
reflections.

## Main declarations

* `ContinuousLinearEquiv.transportTestFunction`: transport a test function along a continuous
  linear equivalence, changing its domain.
* `ContinuousLinearEquiv.transportTestFunction_apply`: evaluation of a transported test function.
* `ContinuousLinearEquiv.fderiv_transportTestFunction`: the Fréchet derivative of a transported
  test function.
* `ContinuousLinearEquiv.divergenceCLM_postcompCLM_transportTestFunction`: the divergence of a
  transported test vector field is the transported divergence.
-/

public section

noncomputable section

namespace ContinuousLinearEquiv

open Set TestFunction TopologicalSpace
open scoped Distributions

variable {E E' F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : Opens E} {Ω : Opens E'}

/-- Transport a test function on `V` along a continuous linear equivalence `e`, regarding the
result `φ ∘ e.symm` as a test function on an open set containing `e '' V`. -/
def transportTestFunction (e : E ≃L[ℝ] E') (hVO : MapsTo e V Ω) (φ : 𝓓(V, F)) : 𝓓(Ω, F) :=
  ⟨φ ∘ e.symm, φ.contDiff.comp e.symm.contDiff,
    φ.hasCompactSupport.comp_homeomorph e.symm.toHomeomorph,
    by
      intro y hy
      -- Composition with the homeomorphism underlying `e.symm` is the function `φ ∘ e.symm`, so
      -- its topological support is the preimage of that of `φ`.
      have hy' : e.symm y ∈ tsupport (φ : E → F) := by
        have hycomp : y ∈ tsupport ((φ : E → F) ∘ e.symm.toHomeomorph) := hy
        rwa [tsupport_comp_eq_preimage] at hycomp
      simpa only [ContinuousLinearEquiv.apply_symm_apply] using hVO (φ.tsupport_subset hy')⟩

/-- A transported test function is evaluated at the inversely transported point. -/
@[simp]
theorem transportTestFunction_apply (e : E ≃L[ℝ] E') (hVO : MapsTo e V Ω) (φ : 𝓓(V, F))
    (y : E') : transportTestFunction e hVO φ y = φ (e.symm y) :=
  (rfl)

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
