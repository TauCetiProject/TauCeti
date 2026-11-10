/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.Distribution
public import TauCeti.Analysis.Distribution.ComplexPairing

/-!
# Restriction of distributions to open subsets

A test function on an open set `Ω' ⊆ Ω` extends by zero to a test function on `Ω`
(Mathlib's `TestFunction.monoCLM`). Transposing this extension restricts a distribution `T` on
`Ω` to a distribution `T|Ω'` on `Ω'`, the dual of the inclusion of test function spaces
(Hörmander I, §2.2). This is how local statements about distributions, such as smoothness near a
point or the wave front set over an open set, are compared with statements on a smaller open set.

## Main declarations

* `Distribution.restrictCLM Ω'`: the restriction `T ↦ T|Ω'`, as a continuous linear map
  `𝓓'^{n}(Ω, F) →L[ℝ] 𝓓'^{n}(Ω', F)`.
* `Distribution.restrictCLM_apply`: `T|Ω' φ = T φ`, with `φ` extended by zero.
* `Distribution.restrictCLM_self`, `Distribution.restrictCLM_restrictCLM`: restriction to `Ω`
  itself is the identity, and restricting in two steps is restricting once.
* `Distribution.complexPairing_restrictCLM`: the complex-linear extension of `T|Ω'` to complex
  test functions on `Ω'` is that of `T`, on test functions extended by zero.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, §2.2.
-/

public section

noncomputable section

open Complex TopologicalSpace
open scoped Distributions

namespace Distribution

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {Ω Ω' Ω'' : Opens E}
  {F : Type*} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F] [IsTopologicalAddGroup F]
  [ContinuousSMul ℝ F] {n : ℕ∞}

variable (Ω') in
/-- The **restriction** `T|Ω'` of a distribution `T` on `Ω` to an open set `Ω'`: it pairs with a
test function on `Ω'` by pairing `T` with its extension by zero to `Ω`. Following
`TestFunction.monoCLM`, this is the zero map unless `Ω' ⊆ Ω`. -/
def restrictCLM : 𝓓'^{n}(Ω, F) →L[ℝ] 𝓓'^{n}(Ω', F) :=
  (TestFunction.monoCLM ℝ : 𝓓^{n}(Ω', ℝ) →L[ℝ] 𝓓^{n}(Ω, ℝ)).precompCompactConvergenceCLM F

@[simp]
theorem restrictCLM_apply (T : 𝓓'^{n}(Ω, F)) (φ : 𝓓^{n}(Ω', ℝ)) :
    restrictCLM Ω' T φ = T (TestFunction.monoCLM ℝ φ) :=
  (rfl)

/-- Restricting a distribution to its own domain does nothing. -/
@[simp]
theorem restrictCLM_self (T : 𝓓'^{n}(Ω, F)) : restrictCLM Ω T = T := by
  ext φ
  rw [restrictCLM_apply]
  congr 1
  ext x
  simp

/-- Restricting a distribution from `Ω` to `Ω'` and then to `Ω''` is restricting it to `Ω''`. -/
@[simp]
theorem restrictCLM_restrictCLM (h' : Ω'' ≤ Ω') (h : Ω' ≤ Ω) (T : 𝓓'^{n}(Ω, F)) :
    restrictCLM Ω'' (restrictCLM Ω' T) = restrictCLM Ω'' T := by
  ext φ
  simp only [restrictCLM_apply]
  congr 1
  ext x
  simp [h, h', h'.trans h]

/-- The complex-linear extension of the restriction `T|Ω'` pairs with a complex test function on
`Ω'` as the extension of `T` pairs with its extension by zero to `Ω`. -/
theorem complexPairing_restrictCLM (h : Ω' ≤ Ω) (T : 𝓓'^{n}(Ω, ℂ)) (φ : 𝓓^{n}(Ω', ℂ)) :
    (restrictCLM Ω' T).complexPairing φ = T.complexPairing (TestFunction.monoCLM ℝ φ) := by
  have hmono (L : ℂ →L[ℝ] ℝ) :
      TestFunction.monoCLM ℝ (TestFunction.postcompCLM (𝕜 := ℝ) L φ) =
        TestFunction.postcompCLM (𝕜 := ℝ) L (TestFunction.monoCLM ℝ φ : 𝓓^{n}(Ω, ℂ)) := by
    ext x
    by_cases hx : x ∈ tsupport φ <;> simp [h]
  simp only [complexPairing_apply, restrictCLM_apply, hmono]

end Distribution
