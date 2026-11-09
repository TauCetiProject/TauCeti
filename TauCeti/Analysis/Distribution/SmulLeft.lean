/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.Distribution
public import TauCeti.Analysis.Distribution.ComplexPairing
public import TauCeti.Analysis.Distribution.TestFunction.SmulLeft

/-!
# Multiplication of distributions by smooth functions

A distribution `T` on an open set `Ω` can be multiplied by a smooth real function `g`: the product
`g T` is the distribution `φ ↦ T (g φ)`. This file defines this operation as the continuous linear
map `Distribution.smulLeftCLM`, the transpose of multiplication of test functions
`TestFunction.smulLeftCLM`, in the same way as Mathlib defines the derivative
`Distribution.lineDerivCLM` as the transpose of the derivative of test functions.

## Main declarations

* `Distribution.smulLeftCLM`: the product `g T` of a distribution with a smooth function.
* `Distribution.smulLeftCLM_smulLeftCLM`: multiplying by two smooth functions in turn is
  multiplying by their product.
* `Distribution.complexPairing_smulLeftCLM`: for a complex distribution, the complex-linear
  extension of `g T` to complex test functions pairs `T` with `g ψ`.
* `Distribution.lineDerivOp_smulLeftCLM`: the Leibniz rule `∂_v (g T) = g ∂_v T + (∂_v g) T`.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, §3.1.
-/

public section

noncomputable section

open LineDeriv TopologicalSpace
open scoped Distributions ContDiff

namespace Distribution

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {Ω : Opens E} {n : ℕ∞} {f g : E → ℝ}

/-- The product `g T` of a distribution `T` with a `C^n` real function `g`, the distribution
`φ ↦ T (g φ)`, as a continuous linear map. -/
def smulLeftCLM (hg : ContDiff ℝ n g) : 𝓓'^{n}(Ω, F) →L[ℝ] 𝓓'^{n}(Ω, F) :=
  (TestFunction.smulLeftCLM hg).precompCompactConvergenceCLM F

@[simp]
theorem smulLeftCLM_apply_apply (hg : ContDiff ℝ n g) (T : 𝓓'^{n}(Ω, F)) (φ : 𝓓^{n}(Ω, ℝ)) :
    smulLeftCLM hg T φ = T (TestFunction.smulLeftCLM hg φ) :=
  (rfl)

/-- Multiplying by two smooth functions in turn is multiplying by their product. -/
@[simp]
theorem smulLeftCLM_smulLeftCLM (hf : ContDiff ℝ n f) (hg : ContDiff ℝ n g)
    (T : 𝓓'^{n}(Ω, F)) :
    smulLeftCLM hf (smulLeftCLM hg T) = smulLeftCLM (hg.mul hf) T := by
  ext φ
  simp

/-- Multiplying by the constant function `1` is the identity. -/
@[simp]
theorem smulLeftCLM_one (T : 𝓓'^{n}(Ω, F)) :
    smulLeftCLM (contDiff_const (c := (1 : ℝ))) T = T := by
  ext φ
  rw [smulLeftCLM_apply_apply]
  congr 1
  ext x
  simp

/-- The complex-linear extension of `g T` pairs `T` with `g ψ`. -/
theorem complexPairing_smulLeftCLM (hg : ContDiff ℝ n g) (T : 𝓓'^{n}(Ω, ℂ))
    (ψ : 𝓓^{n}(Ω, ℂ)) :
    (smulLeftCLM hg T).complexPairing ψ = T.complexPairing (TestFunction.smulLeftCLM hg ψ) := by
  have h (L : ℂ →L[ℝ] ℝ) : TestFunction.smulLeftCLM hg (TestFunction.postcompCLM L ψ) =
      TestFunction.postcompCLM L (TestFunction.smulLeftCLM hg ψ) := by
    ext x
    simp only [TestFunction.smulLeftCLM_apply, TestFunction.postcompCLM_apply,
      Function.comp_apply, map_smul]
  simp [complexPairing_apply, h]

/-- The **Leibniz rule** for the product of a distribution with a smooth function:
`∂_v (g T) = g ∂_v T + (∂_v g) T`. -/
theorem lineDerivOp_smulLeftCLM (hg : ContDiff ℝ ∞ g) (v : E) (T : 𝓓'(Ω, F)) :
    ∂_{v} (smulLeftCLM hg T) =
      smulLeftCLM hg (∂_{v} T) +
        smulLeftCLM ((contDiff_infty_iff_fderiv.1 hg).2.clm_apply (contDiff_const (c := v))) T := by
  ext φ
  simp [TestFunction.lineDerivOp_smulLeftCLM hg]

end Distribution
