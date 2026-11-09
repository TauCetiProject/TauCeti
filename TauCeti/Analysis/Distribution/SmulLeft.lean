/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.ComplexPairing
public import TauCeti.Analysis.Distribution.Support

/-!
# Multiplication of distributions by smooth functions

For an open set `Ω` of a real normed space `E` and a `C^n` function `g : E → ℝ`, a distribution
`T` of order at most `n` on `Ω` is multiplied by `g` through its action on test functions:
`(g T) φ = T (g φ)`. This is the transpose of `TestFunction.smulLeftCLM`, multiplication of test
functions by `g`, and it is the distributional counterpart of Mathlib's
`TemperedDistribution.smulLeftCLM`.

## Main declarations

* `Distribution.smulLeftCLM`: multiplication `T ↦ g T` of distributions by a smooth function, as
  a continuous linear map for the topology of compact convergence.
* `Distribution.smulLeftCLM_ofFun`: on the distribution of a locally integrable function `f`, it is
  the distribution of the pointwise product `g f`.
* `Distribution.dsupport_smulLeftCLM_subset_inter`: `g T` is supported in the supports of both
  `g` and `T`.
* `Distribution.complexPairing_smulLeftCLM`: the complex-linear extension of `g T` to complex test
  functions pairs `T` with `g φ`.
-/

public section

noncomputable section

open Set TopologicalSpace MeasureTheory
open scoped Distributions CompactConvergenceCLM

namespace Distribution

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {Ω : Opens E} {n : ℕ∞}
  {F : Type*} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F] [IsTopologicalAddGroup F]
  [ContinuousSMul ℝ F] {g h : E → ℝ}

/-- Multiplication `T ↦ g T` of distributions of order at most `n` on `Ω` by a `C^n` function `g`,
defined by `(g T) φ = T (g φ)`. -/
def smulLeftCLM (hg : ContDiff ℝ n g) : 𝓓'^{n}(Ω, F) →L[ℝ] 𝓓'^{n}(Ω, F) :=
  (TestFunction.smulLeftCLM (F := ℝ) hg).precompCompactConvergenceCLM F

@[simp]
theorem smulLeftCLM_apply_apply (hg : ContDiff ℝ n g) (T : 𝓓'^{n}(Ω, F)) (φ : 𝓓^{n}(Ω, ℝ)) :
    smulLeftCLM hg T φ = T (TestFunction.smulLeftCLM hg φ) :=
  (rfl)

/-- Multiplying by two smooth functions in turn is multiplying by their product. -/
@[simp]
theorem smulLeftCLM_smulLeftCLM (hg : ContDiff ℝ n g) (hh : ContDiff ℝ n h) (T : 𝓓'^{n}(Ω, F)) :
    smulLeftCLM hg (smulLeftCLM hh T) = smulLeftCLM (hh.mul hg) T := by
  ext φ
  simp

/-- Multiplying by the constant function `c` is scalar multiplication by `c`. -/
@[simp]
theorem smulLeftCLM_const (c : ℝ) (T : 𝓓'^{n}(Ω, F)) :
    smulLeftCLM (contDiff_const (c := c)) T = c • T := by
  ext φ
  have hφ : TestFunction.smulLeftCLM (contDiff_const (c := c)) φ = c • φ := by
    ext x
    simp
  simp [hφ]

/-- A smooth multiple `g T` is supported both in the support of `g` and in the support of `T`.
(The name `Distribution.dsupport_smulLeftCLM_subset` is held by a deprecated Mathlib alias for
tempered distributions.) -/
theorem dsupport_smulLeftCLM_subset_inter (hg : ContDiff ℝ n g) (T : 𝓓'^{n}(Ω, F)) :
    dsupport (smulLeftCLM hg T) ⊆ tsupport g ∩ dsupport T :=
  dsupport_comp_smulLeftCLM_subset T hg

/-- The complex-linear extension of a smooth multiple `g T` of a complex distribution pairs `T`
with the product `g φ`. -/
@[simp]
theorem complexPairing_smulLeftCLM (hg : ContDiff ℝ n g) (T : 𝓓'^{n}(Ω, ℂ))
    (φ : 𝓓^{n}(Ω, ℂ)) :
    (smulLeftCLM hg T).complexPairing φ = T.complexPairing (TestFunction.smulLeftCLM hg φ) := by
  have hre : TestFunction.smulLeftCLM hg (TestFunction.postcompCLM (𝕜 := ℝ) Complex.reCLM φ) =
      TestFunction.postcompCLM (𝕜 := ℝ) Complex.reCLM (TestFunction.smulLeftCLM hg φ) := by
    ext x
    simp
  have him : TestFunction.smulLeftCLM hg (TestFunction.postcompCLM (𝕜 := ℝ) Complex.imCLM φ) =
      TestFunction.postcompCLM (𝕜 := ℝ) Complex.imCLM (TestFunction.smulLeftCLM hg φ) := by
    ext x
    simp
  simp only [complexPairing_apply, smulLeftCLM_apply_apply, hre, him]

/-- On the distribution of a function `f` locally integrable on `Ω`, multiplication by a smooth
function `g` is the distribution of the pointwise product `g f`. -/
theorem smulLeftCLM_ofFun [FiniteDimensional ℝ E] [MeasurableSpace E] [OpensMeasurableSpace E]
    {G : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] {f : E → G} {μ : Measure E}
    (hf : LocallyIntegrableOn f Ω μ) (hg : ContDiff ℝ n g) :
    smulLeftCLM hg (ofFun Ω f μ n) = ofFun Ω (g • f) μ n := by
  have hgf : LocallyIntegrableOn (g • f) Ω μ :=
    hf.continuousOn_smul (hs := Ω.isOpen.isLocallyClosed) hg.continuous.continuousOn
  ext φ
  rw [smulLeftCLM_apply_apply, ofFun_apply hf, ofFun_apply hgf]
  congr 1
  ext x
  simp [smul_smul, mul_comm]

end Distribution
