/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.ComplexPairing
public import TauCeti.Analysis.Distribution.TestFunction.SmulLeft
import TauCeti.Analysis.Distribution.Support

/-!
# Multiplication of distributions by smooth functions

For a `C^n` function `g : E → ℝ` and a distribution `T` of order at most `n` on an open set `Ω`,
the product `g T` is the distribution `φ ↦ T (g φ)`. It is the transpose of multiplication of test
functions by `g` (`TestFunction.smulLeftCLM`), and on a locally integrable function `f` it is the
pointwise product `g f`. This file packages it as a continuous linear map
`Distribution.smulLeftCLM` on `𝓓'^{n}(Ω, F)`, in the way Mathlib's `Distribution.lineDerivCLM`
transposes differentiation of test functions.

A complex multiplier `g + i h` acts on a complex distribution as `g T + i (h T)`; on complex test
functions the product pairs as `(g T) ψ = T (g ψ)` (`Distribution.complexPairing_smulLeftCLM`).

## Main declarations

* `Distribution.smulLeftCLM`: the product `g T`, with `Distribution.smulLeftCLM_apply` and
  `Distribution.coe_smulLeftCLM`.
* `Distribution.smulLeftCLM_const`: a constant `c` acts as the scalar `c`.
* `Distribution.smulLeftCLM_smulLeftCLM`: multiplying by `h` and then by `g` is multiplying by
  `g h`.
* `Distribution.dsupport_smulLeftCLM_subset_inter`: the support of `g T` lies in the supports of `g`
  and of `T`.
* `Distribution.complexPairing_smulLeftCLM`: the pairing of `g T` with a complex test function.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, §2.1.
-/

public section

noncomputable section

open Complex Set TopologicalSpace
open scoped Distributions

namespace Distribution

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {Ω : Opens E} {n : ℕ∞}
  [AddCommGroup F] [Module ℝ F] [TopologicalSpace F] [IsTopologicalAddGroup F]
  [ContinuousSMul ℝ F] {g h : E → ℝ}

/-- The product `g T` of a distribution `T` with a `C^n` function `g`, defined by
`(g T) φ = T (g φ)`, as a continuous linear map on distributions of order at most `n`. -/
def smulLeftCLM (hg : ContDiff ℝ n g) : 𝓓'^{n}(Ω, F) →L[ℝ] 𝓓'^{n}(Ω, F) :=
  (TestFunction.smulLeftCLM hg).precompCompactConvergenceCLM F

@[simp]
theorem smulLeftCLM_apply (hg : ContDiff ℝ n g) (T : 𝓓'^{n}(Ω, F)) (φ : 𝓓^{n}(Ω, ℝ)) :
    smulLeftCLM hg T φ = T (TestFunction.smulLeftCLM hg φ) :=
  (rfl)

/-- As a function on test functions, `g T` is `T` composed with multiplication by `g`. -/
theorem coe_smulLeftCLM (hg : ContDiff ℝ n g) (T : 𝓓'^{n}(Ω, F)) :
    ⇑(smulLeftCLM hg T) = ⇑T ∘ ⇑(TestFunction.smulLeftCLM hg) :=
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

/-- Multiplying a distribution by `h` and then by `g` is multiplying it by `g h`. -/
@[simp]
theorem smulLeftCLM_smulLeftCLM (hg : ContDiff ℝ n g) (hh : ContDiff ℝ n h)
    (T : 𝓓'^{n}(Ω, F)) :
    smulLeftCLM hg (smulLeftCLM hh T) = smulLeftCLM (hg.mul hh) T := by
  ext φ
  simp only [smulLeftCLM_apply]
  congr 1
  ext x
  simp [mul_comm]

/-- The support of `g T` lies both in the support of `g` and in the support of `T`. -/
theorem dsupport_smulLeftCLM_subset_inter (hg : ContDiff ℝ n g) (T : 𝓓'^{n}(Ω, F)) :
    dsupport (smulLeftCLM hg T) ⊆ tsupport g ∩ dsupport T := by
  rw [coe_smulLeftCLM]
  exact dsupport_comp_smulLeftCLM_subset T hg

/-- The complex-linear extension of `g T` to complex test functions pairs `g T` with `ψ` as `T`
with `g ψ`. -/
@[simp]
theorem complexPairing_smulLeftCLM (hg : ContDiff ℝ n g) (T : 𝓓'^{n}(Ω, ℂ))
    (ψ : 𝓓^{n}(Ω, ℂ)) :
    (smulLeftCLM hg T).complexPairing ψ = T.complexPairing (TestFunction.smulLeftCLM hg ψ) := by
  have hpart (L : ℂ →L[ℝ] ℝ) :
      TestFunction.postcompCLM (𝕜 := ℝ) L (TestFunction.smulLeftCLM hg ψ) =
        TestFunction.smulLeftCLM hg (TestFunction.postcompCLM (𝕜 := ℝ) L ψ) := by
    ext x
    simp [-real_smul]
  simp [complexPairing_apply, hpart]

end Distribution
