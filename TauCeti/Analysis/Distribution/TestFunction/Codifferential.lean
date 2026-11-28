/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.DifferentialForm.Codifferential
public import TauCeti.Analysis.Distribution.TestFunction.ExtDeriv

/-!
# The codifferential of test forms

On an open set `Ω` of an oriented finite-dimensional real inner product space `V` of dimension
`n`, the codifferential `δ = (-1) ^ (n (k + 2) + 1) ⋆ d ⋆` of `(k + 1)`-forms,
`Orientation.codifferential`, sends test forms to test forms: the Hodge star acts pointwise by a
linear isomorphism of the fibres, and the exterior derivative of test forms is
`TestFunction.extDerivCLM`. This file packages it as a continuous linear map
`Orientation.testCodifferentialCLM` between test forms, alongside `TestFunction.extDerivCLM`.

On test forms `δ` is the formal adjoint of `d` for the Gram inner product of forms integrated
against the volume measure, `∫ ⟪dφ, ψ⟫ = ∫ ⟪φ, δψ⟫`
(`Orientation.integral_alternatingFormInner_extDerivCLM_eq_testCodifferentialCLM`). This is the
identity through which weak exterior derivatives and the adjoints of `d` on spaces of
square-integrable forms are tested.

## Main declarations

* `Orientation.testCodifferentialCLM`: the codifferential `𝓓(Ω, Λᵏ⁺¹) →L[ℝ] 𝓓(Ω, Λᵏ)`.
* `Orientation.testCodifferentialCLM_apply`: pointwise it is `Orientation.codifferential`.
* `Orientation.testCodifferentialCLM_neg_orientation`: `δ` does not depend on the orientation.
* `Orientation.testCodifferentialCLM_testCodifferentialCLM`: `δ (δ ψ) = 0`.
* `Orientation.integral_alternatingFormInner_extDerivCLM_eq_testCodifferentialCLM`:
  `∫ ⟪dφ, ψ⟫ = ∫ ⟪φ, δψ⟫`.

## References

* D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus, homological techniques,
  and applications*, Acta Numerica 15 (2006), §2, (2.7) and (2.8).
-/

public section

noncomputable section

open Module MeasureTheory TopologicalSpace TestFunction TauCeti
open scoped Distributions

namespace Orientation

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {n : ℕ} [Fact (finrank ℝ V = n)] (o : Orientation ℝ V (Fin n)) {Ω : Opens V} {k l : ℕ}

/-- The **codifferential of test forms** `δ = (-1) ^ (n (k + 2) + 1) ⋆ d ⋆`, from test
`(k + 1)`-forms to test `k`-forms on `Ω`, for `k + 1 + l = finrank ℝ V`. The Hodge stars act
pointwise and the exterior derivative is `TestFunction.extDerivCLM`, so pointwise it is
`Orientation.codifferential` (`Orientation.testCodifferentialCLM_apply`). -/
def testCodifferentialCLM (hkl : k + 1 + l = finrank ℝ V) :
    𝓓(Ω, V [⋀^Fin (k + 1)]→L[ℝ] ℝ) →L[ℝ] 𝓓(Ω, V [⋀^Fin k]→L[ℝ] ℝ) :=
  (-1 : ℝ) ^ (n * (k + 2) + 1) •
    (postcompCLM (LinearMap.toContinuousLinearMap
        (o.formHodgeStar (show l + 1 + k = finrank ℝ V by omega)).toLinearMap) ∘L
      extDerivCLM ∘L
        postcompCLM (LinearMap.toContinuousLinearMap (o.formHodgeStar hkl).toLinearMap))

/-- The codifferential of a test form is pointwise its codifferential as a differential form. -/
@[simp]
theorem testCodifferentialCLM_apply (hkl : k + 1 + l = finrank ℝ V)
    (ψ : 𝓓(Ω, V [⋀^Fin (k + 1)]→L[ℝ] ℝ)) (x : V) :
    o.testCodifferentialCLM hkl ψ x = o.codifferential hkl ψ x := by
  rw [codifferential_apply _ hkl (by omega)]
  simp [testCodifferentialCLM, postcompCLM_apply, Function.comp_def]

/-- The codifferential of a test form, as a function, is its codifferential as a differential
form. -/
theorem coe_testCodifferentialCLM (hkl : k + 1 + l = finrank ℝ V)
    (ψ : 𝓓(Ω, V [⋀^Fin (k + 1)]→L[ℝ] ℝ)) :
    (o.testCodifferentialCLM hkl ψ : V → V [⋀^Fin k]→L[ℝ] ℝ) = o.codifferential hkl ψ :=
  funext (o.testCodifferentialCLM_apply hkl ψ)

/-- Reversing the orientation does not change the codifferential of test forms. -/
@[simp]
theorem testCodifferentialCLM_neg_orientation (hkl : k + 1 + l = finrank ℝ V) :
    ((-o).testCodifferentialCLM hkl : 𝓓(Ω, V [⋀^Fin (k + 1)]→L[ℝ] ℝ) →L[ℝ] _) =
      o.testCodifferentialCLM hkl := by
  ext ψ x : 2
  simp

/-- **`δ ∘ δ = 0`** on test forms. -/
@[simp]
theorem testCodifferentialCLM_testCodifferentialCLM {l' : ℕ} (hkl : k + 1 + l = finrank ℝ V)
    (hkl' : k + 1 + 1 + l' = finrank ℝ V) (ψ : 𝓓(Ω, V [⋀^Fin (k + 1 + 1)]→L[ℝ] ℝ)) :
    o.testCodifferentialCLM hkl (o.testCodifferentialCLM hkl' ψ) = 0 := by
  ext x : 1
  rw [testCodifferentialCLM_apply, coe_testCodifferentialCLM,
    o.codifferential_codifferential hkl hkl' ψ.contDiff (by simp)]
  simp

/-- **`δ ∘ δ = 0`** on test forms, as an identity of continuous linear maps. -/
@[simp]
theorem testCodifferentialCLM_comp_testCodifferentialCLM {l' : ℕ}
    (hkl : k + 1 + l = finrank ℝ V) (hkl' : k + 1 + 1 + l' = finrank ℝ V) :
    (o.testCodifferentialCLM hkl ∘L o.testCodifferentialCLM hkl' :
      𝓓(Ω, V [⋀^Fin (k + 1 + 1)]→L[ℝ] ℝ) →L[ℝ] 𝓓(Ω, V [⋀^Fin k]→L[ℝ] ℝ)) = 0 := by
  ext ψ : 1
  exact o.testCodifferentialCLM_testCodifferentialCLM hkl hkl' ψ

variable [MeasurableSpace V] [BorelSpace V]

/-- **The codifferential of test forms is the formal adjoint of their exterior derivative**:
`∫ ⟪dφ, ψ⟫ = ∫ ⟪φ, δψ⟫` for test forms `φ` of degree `k` and `ψ` of degree `k + 1`, with the
Gram inner product of forms integrated against the volume measure. -/
theorem integral_alternatingFormInner_extDerivCLM_eq_testCodifferentialCLM
    (hkl : k + 1 + l = finrank ℝ V)
    (φ : 𝓓(Ω, V [⋀^Fin k]→L[ℝ] ℝ)) (ψ : 𝓓(Ω, V [⋀^Fin (k + 1)]→L[ℝ] ℝ)) :
    ∫ x, alternatingFormInner V (k + 1) (extDerivCLM φ x) (ψ x) =
      ∫ x, alternatingFormInner V k (φ x) (o.testCodifferentialCLM hkl ψ x) := by
  simpa only [extDerivCLM_apply, testCodifferentialCLM_apply] using
    o.integral_alternatingFormInner_extDeriv_eq_codifferential hkl (φ.contDiff.of_le (by simp))
      (ψ.contDiff.of_le (by simp)) ψ.hasCompactSupport

end Orientation
