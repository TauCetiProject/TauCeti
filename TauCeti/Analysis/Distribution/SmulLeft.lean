/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.Restriction
public import TauCeti.Analysis.Distribution.TestFunction.SmulLeft
import TauCeti.Analysis.Distribution.Support

/-!
# Multiplication of distributions by smooth functions

A `C^n` real function `f` multiplies test functions on `Ω` (`TestFunction.smulLeftCLM`).
Transposing, it multiplies a distribution `T` on `Ω` to the distribution `f T : φ ↦ T (f φ)`.
Together with distributional derivatives, these multiplications make up the linear differential
operators with smooth coefficients acting on distributions.

## Main declarations

* `Distribution.smulLeftCLM hf`: the multiplication `T ↦ f T`, as a continuous linear map
  `𝓓'^{n}(Ω, F) →L[ℝ] 𝓓'^{n}(Ω, F)`.
* `Distribution.smulLeftCLM_apply`: `(f T) φ = T (f φ)`.
* `Distribution.smulLeftCLM_smulLeftCLM`: multiplying by `g` and then by `f` is multiplying by
  `f g`.
* `Distribution.restrictCLM_smulLeftCLM`: multiplication commutes with restriction.
* `Distribution.dsupport_smulLeftCLM_subset_inter`: the support of `f T` lies in the supports of
  `f` and of `T`.
* `Distribution.complexPairing_smulLeftCLM`: the complex-linear extension of `f T` to complex
  test functions is that of `T`, applied to `f φ`.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, §2.1.
-/

public section

noncomputable section

open Complex Set TopologicalSpace
open scoped Distributions

namespace Distribution

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {Ω Ω' : Opens E} {n : ℕ∞}
  {F : Type*} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F] [IsTopologicalAddGroup F]
  [ContinuousSMul ℝ F] {f g : E → ℝ}

/-- **Multiplication of distributions by a `C^n` real function** `f`: the transpose
`T ↦ (φ ↦ T (f φ))` of multiplication of test functions by `f`. -/
def smulLeftCLM (hf : ContDiff ℝ n f) : 𝓓'^{n}(Ω, F) →L[ℝ] 𝓓'^{n}(Ω, F) :=
  (TestFunction.smulLeftCLM (F := ℝ) (Ω := Ω) hf).precompCompactConvergenceCLM F

/-- The product `f T` pairs a test function `φ` with `T` through `f φ`. -/
@[simp]
theorem smulLeftCLM_apply (hf : ContDiff ℝ n f) (T : 𝓓'^{n}(Ω, F)) (φ : 𝓓^{n}(Ω, ℝ)) :
    smulLeftCLM hf T φ = T (TestFunction.smulLeftCLM hf φ) :=
  (rfl)

/-- Multiplying a distribution by `g` and then by `f` is multiplying it by `f g`. -/
@[simp]
theorem smulLeftCLM_smulLeftCLM (hf : ContDiff ℝ n f) (hg : ContDiff ℝ n g)
    (T : 𝓓'^{n}(Ω, F)) :
    smulLeftCLM hf (smulLeftCLM hg T) = smulLeftCLM (hf.mul hg) T := by
  ext φ
  simp only [smulLeftCLM_apply]
  congr 1
  ext x
  simp [mul_comm]

/-- Multiplication by a smooth function commutes with restriction to an open subset. -/
theorem restrictCLM_smulLeftCLM (hf : ContDiff ℝ n f) (T : 𝓓'^{n}(Ω, F)) :
    restrictCLM Ω' (smulLeftCLM hf T) = smulLeftCLM hf (restrictCLM Ω' T) := by
  ext φ
  simp

/-- The support of `f T` lies both in the support of `f` and in the support of `T`. -/
theorem dsupport_smulLeftCLM_subset_inter (hf : ContDiff ℝ n f) (T : 𝓓'^{n}(Ω, F)) :
    dsupport (smulLeftCLM hf T) ⊆ tsupport f ∩ dsupport T :=
  dsupport_comp_smulLeftCLM_subset T hf

/-- The complex-linear extension of `f T` pairs a complex test function `φ` with `T` through
`f φ`. -/
@[simp]
theorem complexPairing_smulLeftCLM (hf : ContDiff ℝ n f) (T : 𝓓'^{n}(Ω, ℂ))
    (φ : 𝓓^{n}(Ω, ℂ)) :
    (smulLeftCLM hf T).complexPairing φ = T.complexPairing (TestFunction.smulLeftCLM hf φ) := by
  have hpost (L : ℂ →L[ℝ] ℝ) :
      TestFunction.smulLeftCLM hf (TestFunction.postcompCLM (𝕜 := ℝ) L φ) =
        TestFunction.postcompCLM (𝕜 := ℝ) L (TestFunction.smulLeftCLM hf φ) := by
    ext x
    simp [-Complex.real_smul]
  simp only [complexPairing_apply, smulLeftCLM_apply, hpost]

end Distribution
