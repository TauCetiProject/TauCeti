/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.ComplexPairing

/-!
# Restriction of distributions to open subsets

A test function on an open set `Ω'` extends by zero to a test function on any larger open set `Ω`;
this is Mathlib's `TestFunction.monoCLM`. Transposing it, a distribution `T` on `Ω` restricts to
the distribution `T|Ω' : φ ↦ T φ` on `Ω'`. Restriction is how distributions are localized: it is
the operation along which local properties of distributions, such as smoothness near a point or
the wave front set over an open set, are compared.

As for `TestFunction.monoCLM`, the restriction is defined for every pair of open sets and is the
zero map unless `Ω' ≤ Ω`.

## Main declarations

* `Distribution.restrictCLM Ω'`: the restriction `𝓓'^{n}(Ω, F) →L[ℝ] 𝓓'^{n}(Ω', F)`.
* `Distribution.restrictCLM_apply`: it pairs a test function on `Ω'` with `T` through its
  extension by zero.
* `Distribution.restrictCLM_self`, `Distribution.restrictCLM_restrictCLM`: restricting to `Ω`
  itself does nothing, and restricting twice is restricting once.
* `Distribution.complexPairing_restrictCLM`: the complex-linear extension of `T|Ω'` to complex
  test functions is that of `T`, through extension by zero.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, §2.2.
-/

public section

noncomputable section

open Complex TopologicalSpace TestFunction
open scoped Distributions

namespace Distribution

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {Ω Ω' Ω'' : Opens E} {n : ℕ∞}
  {F : Type*} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F] [IsTopologicalAddGroup F]
  [ContinuousSMul ℝ F]

variable (Ω') in
/-- The **restriction** of distributions on `Ω` to the open set `Ω'`: the transpose
`T ↦ (φ ↦ T φ)` of the extension by zero of test functions on `Ω'`. It is the zero map unless
`Ω' ≤ Ω`, since `TestFunction.monoCLM` is. -/
def restrictCLM : 𝓓'^{n}(Ω, F) →L[ℝ] 𝓓'^{n}(Ω', F) :=
  (monoCLM ℝ : 𝓓^{n}(Ω', ℝ) →L[ℝ] 𝓓^{n}(Ω, ℝ)).precompCompactConvergenceCLM F

/-- The restriction of `T` pairs a test function on `Ω'` with `T` through its extension by zero
to `Ω`. -/
@[simp]
theorem restrictCLM_apply (T : 𝓓'^{n}(Ω, F)) (φ : 𝓓^{n}(Ω', ℝ)) :
    restrictCLM Ω' T φ = T (monoCLM ℝ φ) :=
  (rfl)

/-- Restricting a distribution to its own domain gives it back. -/
@[simp]
theorem restrictCLM_self (T : 𝓓'^{n}(Ω, F)) : restrictCLM Ω T = T := by
  ext φ
  rw [restrictCLM_apply]
  congr 1
  ext x
  simp

/-- Restricting to `Ω'` and then to `Ω''` is restricting to `Ω''`. -/
theorem restrictCLM_restrictCLM (h' : Ω'' ≤ Ω') (h : Ω' ≤ Ω) (T : 𝓓'^{n}(Ω, F)) :
    restrictCLM Ω'' (restrictCLM Ω' T) = restrictCLM Ω'' T := by
  ext φ
  simp only [restrictCLM_apply]
  congr 1
  ext x
  simp [h, h', h'.trans h]

/-- The complex-linear extension of the restriction `T|Ω'` pairs a complex test function on `Ω'`
with `T` through its extension by zero to `Ω`. -/
@[simp]
theorem complexPairing_restrictCLM (T : 𝓓'^{n}(Ω, ℂ)) (φ : 𝓓^{n}(Ω', ℂ)) :
    (restrictCLM Ω' T).complexPairing φ = T.complexPairing (monoCLM ℝ φ) := by
  have hmono (L : ℂ →L[ℝ] ℝ) :
      (monoCLM ℝ (postcompCLM (𝕜 := ℝ) L φ) : 𝓓^{n}(Ω, ℝ)) =
        postcompCLM (𝕜 := ℝ) L (monoCLM ℝ φ) := by
    ext x
    by_cases h : Ω' ≤ Ω <;> simp [h]
  simp only [complexPairing_apply, restrictCLM_apply, hmono]

end Distribution
