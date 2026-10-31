/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.TestFunction.ExtDeriv
import TauCeti.Analysis.Calculus.DifferentialForm.Basic

/-!
# Smooth multiplication of test forms and the Leibniz rule for currents

For an open set `Ω` of a real normed space `E`, a smooth function `f : E → ℝ` acts on test
functions on `Ω` by pointwise multiplication, and a smooth covector field `α : E → E →L[ℝ] ℝ`
acts on test `k`-forms by the wedge product `ω ↦ α ∧ ω`, with values in test `(k + 1)`-forms.
Both are continuous linear maps for the LF topology, built from Mathlib's
`TestFunction.bilinLeftCLM`. They do not enlarge supports and commute with extension of test
functions to a larger open set.

The exterior derivative satisfies the Leibniz rule `d (f ω) = df ∧ ω + f dω` on test forms.
Transposing, for a current `T` (a continuous linear functional on test `(k + 1)`-forms), the
current `fT = T ∘ (f ·)` has boundary
`∂(fT) = f ∂T - T ⌞ df`, where `∂T = T ∘ d` and `(T ⌞ df) ω = T (df ∧ ω)`.

The wedge `α ∧ ω` with a one-form is the alternatization of `v ↦ α v • ω`, the operation through
which Mathlib's `extDeriv` is defined, so that it lands in degree `k + 1` like the exterior
derivative. `ContinuousAlternatingMap.alternatizeUncurryFin_smulRight_apply` identifies it with
the paired wedge `ContinuousAlternatingMap.pairedWedge` of the one-form `α` with `ω`.

## Main declarations

* `TestFunction.smulLeftCLM`: multiplication `φ ↦ f φ` of test functions by a smooth function.
* `TestFunction.oneFormWedgeCLM`: the wedge `ω ↦ α ∧ ω` of test forms with a smooth one-form.
* `TestFunction.extDerivCLM_smulLeftCLM`: the Leibniz rule `d (f ω) = df ∧ ω + f dω`.
* `ContinuousLinearMap.comp_smulLeftCLM_comp_extDerivCLM`: the boundary of a smooth multiple of
  a current, `∂(fT) = f ∂T - T ⌞ df`.

## References

* H. Federer, *Geometric Measure Theory*, §4.1.7.
* L. Simon, *Introduction to Geometric Measure Theory*, Chapter 6.
-/

public section

namespace TestFunction

open TopologicalSpace ContinuousAlternatingMap
open scoped Distributions

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {Ω Ω' : Opens E} {n : ℕ∞} {k : ℕ}

section SmulLeft

variable {f g : E → ℝ}

/-- Multiplication of test functions on `Ω` by a `C^n` real function `f`, as a continuous linear
map `φ ↦ f φ`. -/
noncomputable def smulLeftCLM (hf : ContDiff ℝ n f) : 𝓓^{n}(Ω, F) →L[ℝ] 𝓓^{n}(Ω, F) :=
  bilinLeftCLM (ContinuousLinearMap.lsmul ℝ ℝ).flip hf

@[simp]
theorem smulLeftCLM_apply (hf : ContDiff ℝ n f) (φ : 𝓓^{n}(Ω, F)) (x : E) :
    smulLeftCLM hf φ x = f x • φ x := by
  simp [smulLeftCLM]

/-- A smooth multiple of a test function, as a function, is the pointwise product. -/
theorem coe_smulLeftCLM (hf : ContDiff ℝ n f) (φ : 𝓓^{n}(Ω, F)) :
    (smulLeftCLM hf φ : E → F) = f • ⇑φ :=
  funext (smulLeftCLM_apply hf φ)

/-- Multiplying by a smooth function does not enlarge the support of a test function. -/
theorem tsupport_smulLeftCLM_subset (hf : ContDiff ℝ n f) (φ : 𝓓^{n}(Ω, F)) :
    tsupport (smulLeftCLM hf φ : E → F) ⊆ tsupport f ∩ tsupport φ := by
  rw [coe_smulLeftCLM]
  exact Set.subset_inter (tsupport_smul_subset_left f φ) (tsupport_smul_subset_right f φ)

/-- Multiplying by two smooth functions in turn is multiplying by their product. -/
@[simp]
theorem smulLeftCLM_smulLeftCLM (hf : ContDiff ℝ n f) (hg : ContDiff ℝ n g)
    (φ : 𝓓^{n}(Ω, F)) :
    smulLeftCLM hf (smulLeftCLM hg φ) = smulLeftCLM (hf.mul hg) φ := by
  ext x
  simp [smul_smul]

/-- Multiplication by a smooth function commutes with extending test functions from `Ω'` to
`Ω`. -/
@[simp]
theorem smulLeftCLM_monoCLM (hf : ContDiff ℝ n f) (φ : 𝓓^{n}(Ω', F)) :
    smulLeftCLM hf (monoCLM ℝ φ : 𝓓^{n}(Ω, F)) = monoCLM ℝ (smulLeftCLM hf φ) := by
  ext x
  by_cases h : Ω' ≤ Ω <;> simp [monoCLM_apply, h]

end SmulLeft

section OneFormWedge

variable {α : E → E →L[ℝ] ℝ}

/-- The wedge `α ∧ ω` of a test `k`-form `ω` on `Ω` with a `C^n` one-form `α`, as a continuous
linear map into test `(k + 1)`-forms. Pointwise, `α ∧ ω` is the alternatization of
`v ↦ α v • ω`, see `TestFunction.oneFormWedgeCLM_apply`. -/
noncomputable def oneFormWedgeCLM (hα : ContDiff ℝ n α) :
    𝓓^{n}(Ω, E [⋀^Fin k]→L[ℝ] F) →L[ℝ] 𝓓^{n}(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F) :=
  bilinLeftCLM
    ((ContinuousLinearMap.compL ℝ (E →L[ℝ] ℝ) _ _ (alternatizeUncurryFinCLM ℝ E F)) ∘L
      (ContinuousLinearMap.smulRightL ℝ E (E [⋀^Fin k]→L[ℝ] F)).flip) hα

@[simp]
theorem oneFormWedgeCLM_apply (hα : ContDiff ℝ n α) (ω : 𝓓^{n}(Ω, E [⋀^Fin k]→L[ℝ] F)) (x : E) :
    oneFormWedgeCLM hα ω x = alternatizeUncurryFin ((α x).smulRight (ω x)) := by
  simp [oneFormWedgeCLM]

/-- The wedge with a smooth one-form does not enlarge the support of a test form. -/
theorem tsupport_oneFormWedgeCLM_subset (hα : ContDiff ℝ n α)
    (ω : 𝓓^{n}(Ω, E [⋀^Fin k]→L[ℝ] F)) :
    tsupport (oneFormWedgeCLM hα ω : E → E [⋀^Fin (k + 1)]→L[ℝ] F) ⊆ tsupport α ∩ tsupport ω := by
  have h₀ : alternatizeUncurryFin (0 : E →L[ℝ] E [⋀^Fin k]→L[ℝ] F) = 0 :=
    map_zero (alternatizeUncurryFinCLM ℝ E F)
  refine Set.subset_inter (closure_mono fun x hx ↦ ?_) (closure_mono fun x hx ↦ ?_) <;>
    contrapose hx <;> simp [Function.notMem_support.1 hx, h₀]

/-- The wedge with a smooth one-form commutes with extending test forms from `Ω'` to `Ω`. -/
@[simp]
theorem oneFormWedgeCLM_monoCLM (hα : ContDiff ℝ n α) (ω : 𝓓^{n}(Ω', E [⋀^Fin k]→L[ℝ] F)) :
    oneFormWedgeCLM hα (monoCLM ℝ ω : 𝓓^{n}(Ω, E [⋀^Fin k]→L[ℝ] F)) =
      monoCLM ℝ (oneFormWedgeCLM hα ω) := by
  have h₀ : alternatizeUncurryFin (0 : E →L[ℝ] E [⋀^Fin k]→L[ℝ] F) = 0 :=
    map_zero (alternatizeUncurryFinCLM ℝ E F)
  ext x : 1
  by_cases h : Ω' ≤ Ω <;> simp [monoCLM_apply, h, h₀]

end OneFormWedge

section Leibniz

variable {f : E → ℝ}

/-- **The Leibniz rule** for test forms: `d (f ω) = df ∧ ω + f dω` for a smooth function `f`. -/
theorem extDerivCLM_smulLeftCLM (hf : ContDiff ℝ (⊤ : ℕ∞) f) (ω : 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F)) :
    extDerivCLM (smulLeftCLM hf ω) =
      oneFormWedgeCLM (contDiff_infty_iff_fderiv.1 hf).2 ω + smulLeftCLM hf (extDerivCLM ω) := by
  ext x : 1
  rw [extDerivCLM_apply, coe_smulLeftCLM,
    TauCeti.extDeriv_function_smul (hf.differentiable (by simp) x)
      (ω.contDiff.differentiable (by simp) x)]
  simp [add_comm]

end Leibniz

end TestFunction

namespace ContinuousLinearMap

open TestFunction
open scoped Distributions

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [AddCommGroup G] [Module ℝ G] [TopologicalSpace G]
  [IsTopologicalAddGroup G] {Ω : TopologicalSpace.Opens E} {k : ℕ} {f : E → ℝ}

/-- **The boundary of a smooth multiple of a current**: for a continuous linear functional `T` on
test `(k + 1)`-forms and a smooth function `f`, `∂(fT) = f ∂T - T ⌞ df`. Here `fT = T ∘ (f ·)`,
the boundary is `∂T = T ∘ d`, and `(T ⌞ df) ω = T (df ∧ ω)`. -/
theorem comp_smulLeftCLM_comp_extDerivCLM
    (T : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] G) (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    (T ∘L smulLeftCLM hf) ∘L extDerivCLM =
      (T ∘L extDerivCLM) ∘L smulLeftCLM hf -
        T ∘L oneFormWedgeCLM (contDiff_infty_iff_fderiv.1 hf).2 := by
  ext ω
  simp [extDerivCLM_smulLeftCLM hf ω]

end ContinuousLinearMap
