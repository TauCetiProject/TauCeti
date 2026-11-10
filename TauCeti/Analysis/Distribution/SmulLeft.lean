/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.Restrict
public import TauCeti.Analysis.Distribution.TestFunction.SmulLeft
import TauCeti.Analysis.Distribution.Support

/-!
# Multiplication of distributions by smooth functions

A `C^n` real function `g` multiplies test functions on `Ω` (`TestFunction.smulLeftCLM`).
Transposing, it multiplies a distribution `T` of order `n` by the rule `(g T) φ = T (g φ)`
(Hörmander I, §2.1). Multiplying by smooth cutoffs is how distributions are localized, for
instance in the definition of the wave front set.

## Main declarations

* `Distribution.smulLeftCLM hg`: the multiplication `T ↦ g T`, as a continuous linear map
  `𝓓'^{n}(Ω, F) →L[ℝ] 𝓓'^{n}(Ω, F)`.
* `Distribution.smulLeftCLM_apply`: `(g T) φ = T (g φ)`.
* `Distribution.smulLeftCLM_const`, `Distribution.smulLeftCLM_smulLeftCLM`: a constant `c`
  acts as the scalar `c`, and multiplying by `f` and then by `g` is multiplying by `g f`.
* `Distribution.restrictCLM_smulLeftCLM`: multiplication commutes with restriction to an open
  subset.
* `Distribution.dsupport_smulLeftCLM_subset_inter`: the support of `g T` lies in the supports of `g`
  and of `T`.
* `Distribution.complexPairing_smulLeftCLM`: the complex-linear extension of `g T` to complex
  test functions is that of `T`, on test functions multiplied by `g`.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, §2.1.
-/

public section

noncomputable section

open Complex Set TopologicalSpace
open scoped Distributions

namespace Distribution

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {Ω Ω' : Opens E}
  {F : Type*} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F] [IsTopologicalAddGroup F]
  [ContinuousSMul ℝ F] {n : ℕ∞} {f g : E → ℝ}

/-- **Multiplication of a distribution by a `C^n` real function** `g`, as a continuous linear map
`T ↦ g T` on distributions of order `n`, where `(g T) φ = T (g φ)`. -/
def smulLeftCLM (hg : ContDiff ℝ n g) : 𝓓'^{n}(Ω, F) →L[ℝ] 𝓓'^{n}(Ω, F) :=
  (TestFunction.smulLeftCLM hg : 𝓓^{n}(Ω, ℝ) →L[ℝ] 𝓓^{n}(Ω, ℝ)).precompCompactConvergenceCLM F

@[simp]
theorem smulLeftCLM_apply (hg : ContDiff ℝ n g) (T : 𝓓'^{n}(Ω, F)) (φ : 𝓓^{n}(Ω, ℝ)) :
    smulLeftCLM hg T φ = T (TestFunction.smulLeftCLM hg φ) :=
  (rfl)

/-- Multiplying a distribution by the constant function `c` is scalar multiplication by `c`. -/
@[simp]
theorem smulLeftCLM_const (c : ℝ) (T : 𝓓'^{n}(Ω, F)) :
    smulLeftCLM (contDiff_const (c := c)) T = c • T := by
  ext φ
  have h : TestFunction.smulLeftCLM (contDiff_const (c := c)) φ = c • φ := by
    ext x
    simp
  simp [h]

/-- Multiplying a distribution by `f` and then by `g` is multiplying it by `g f`. -/
@[simp]
theorem smulLeftCLM_smulLeftCLM (hf : ContDiff ℝ n f) (hg : ContDiff ℝ n g)
    (T : 𝓓'^{n}(Ω, F)) :
    smulLeftCLM hg (smulLeftCLM hf T) = smulLeftCLM (hg.mul hf) T := by
  ext φ
  simp only [smulLeftCLM_apply, TestFunction.smulLeftCLM_smulLeftCLM]
  congr 1
  ext x
  simp [mul_comm]

/-- Multiplication by a smooth function commutes with restriction to an open subset. -/
theorem restrictCLM_smulLeftCLM (hg : ContDiff ℝ n g) (T : 𝓓'^{n}(Ω, F)) :
    restrictCLM Ω' (smulLeftCLM hg T) = smulLeftCLM hg (restrictCLM Ω' T) := by
  ext φ
  simp

/-- The support of `g T` lies both in the support of `g` and in the support of `T`. -/
theorem dsupport_smulLeftCLM_subset_inter (hg : ContDiff ℝ n g) (T : 𝓓'^{n}(Ω, F)) :
    dsupport (smulLeftCLM hg T) ⊆ tsupport g ∩ dsupport T := by
  have h : ⇑(smulLeftCLM hg T) = T ∘ TestFunction.smulLeftCLM hg :=
    funext (smulLeftCLM_apply hg T)
  rw [h]
  exact dsupport_comp_smulLeftCLM_subset T hg

/-- The complex-linear extension of `g T` pairs with a complex test function `φ` as the extension
of `T` pairs with `g φ`. -/
theorem complexPairing_smulLeftCLM (hg : ContDiff ℝ n g) (T : 𝓓'^{n}(Ω, ℂ))
    (φ : 𝓓^{n}(Ω, ℂ)) :
    (smulLeftCLM hg T).complexPairing φ = T.complexPairing (TestFunction.smulLeftCLM hg φ) := by
  have hsmul (L : ℂ →L[ℝ] ℝ) :
      TestFunction.smulLeftCLM hg (TestFunction.postcompCLM (𝕜 := ℝ) L φ) =
        TestFunction.postcompCLM (𝕜 := ℝ) L (TestFunction.smulLeftCLM hg φ) := by
    ext x
    simp only [TestFunction.smulLeftCLM_apply, TestFunction.postcompCLM_apply,
      Function.comp_apply, map_smul]
  simp only [complexPairing_apply, smulLeftCLM_apply, hsmul]

end Distribution
