/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.SmulLeft

/-!
# Restriction of distributions to open subsets

A test function on an open set `Ω' ⊆ Ω`, extended by zero, is a test function on `Ω`
(`TestFunction.monoCLM`). Transposing, a distribution `T` on `Ω` restricts to the distribution
`T|_{Ω'} : φ ↦ T φ` on `Ω'`. This file packages the restriction as a continuous linear map
`Distribution.restrictCLM`, which, like `TestFunction.monoCLM`, is zero when `Ω'` is not contained
in `Ω`. Restriction is what makes distributions a sheaf on open sets; the gluing half of the sheaf
property is `Distribution.existsUnique_gluing`.

## Main declarations

* `Distribution.restrictCLM`: the restriction `T|_{Ω'}`, with `Distribution.restrictCLM_apply`.
* `Distribution.restrictCLM_self`, `Distribution.restrictCLM_restrictCLM`: restriction to `Ω`
  itself is the identity, and restrictions compose.
* `Distribution.restrictCLM_smulLeftCLM`: restriction commutes with multiplication by smooth
  functions.
* `Distribution.complexPairing_restrictCLM`: the pairing of `T|_{Ω'}` with a complex test function.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, §2.2.
-/

public section

noncomputable section

open Complex Set TopologicalSpace
open scoped Distributions

namespace Distribution

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {Ω Ω' Ω'' : Opens E} {n : ℕ∞}
  [AddCommGroup F] [Module ℝ F] [TopologicalSpace F] [IsTopologicalAddGroup F]
  [ContinuousSMul ℝ F]

/-- The **restriction** `T|_{Ω'}` of a distribution `T` on `Ω` to an open set `Ω'`, defined by
`T|_{Ω'} φ = T φ` for test functions `φ` on `Ω'` extended by zero. It is zero unless `Ω' ≤ Ω`. -/
def restrictCLM : 𝓓'^{n}(Ω, F) →L[ℝ] 𝓓'^{n}(Ω', F) :=
  (TestFunction.monoCLM ℝ : 𝓓^{n}(Ω', ℝ) →L[ℝ] 𝓓^{n}(Ω, ℝ)).precompCompactConvergenceCLM F

@[simp]
theorem restrictCLM_apply (T : 𝓓'^{n}(Ω, F)) (φ : 𝓓^{n}(Ω', ℝ)) :
    restrictCLM T φ = T (TestFunction.monoCLM ℝ φ) :=
  (rfl)

/-- Restricting a distribution on `Ω` to `Ω` itself does nothing. -/
@[simp]
theorem restrictCLM_self (T : 𝓓'^{n}(Ω, F)) : (restrictCLM T : 𝓓'^{n}(Ω, F)) = T := by
  ext φ
  rw [restrictCLM_apply]
  congr 1
  ext x
  simp

/-- Restricting from `Ω` to `Ω'` and then to `Ω'' ≤ Ω'` is restricting from `Ω` to `Ω''`. -/
theorem restrictCLM_restrictCLM (h₁ : Ω'' ≤ Ω') (h₂ : Ω' ≤ Ω) (T : 𝓓'^{n}(Ω, F)) :
    (restrictCLM (restrictCLM T : 𝓓'^{n}(Ω', F)) : 𝓓'^{n}(Ω'', F)) = restrictCLM T := by
  ext φ
  simp only [restrictCLM_apply]
  congr 1
  ext x
  simp [h₁, h₂, h₁.trans h₂]

/-- Restriction commutes with multiplication by a smooth function. -/
@[simp]
theorem restrictCLM_smulLeftCLM {g : E → ℝ} (hg : ContDiff ℝ n g) (T : 𝓓'^{n}(Ω, F)) :
    (restrictCLM (smulLeftCLM hg T) : 𝓓'^{n}(Ω', F)) = smulLeftCLM hg (restrictCLM T) := by
  ext φ
  simp

/-- The complex-linear extension of `T|_{Ω'}` pairs it with a complex test function `ψ` on `Ω'`
as `T` with the extension of `ψ` by zero. -/
@[simp]
theorem complexPairing_restrictCLM (T : 𝓓'^{n}(Ω, ℂ)) (ψ : 𝓓^{n}(Ω', ℂ)) :
    (restrictCLM T).complexPairing ψ = T.complexPairing (TestFunction.monoCLM ℝ ψ) := by
  have hpart (L : ℂ →L[ℝ] ℝ) :
      TestFunction.postcompCLM (𝕜 := ℝ) L (TestFunction.monoCLM ℝ ψ : 𝓓^{n}(Ω, ℂ)) =
        TestFunction.monoCLM ℝ (TestFunction.postcompCLM (𝕜 := ℝ) L ψ) := by
    ext x
    by_cases h : Ω' ≤ Ω <;> simp [h]
  simp [complexPairing_apply, hpart]

end Distribution
