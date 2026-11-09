/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.ComplexPairing
public import TauCeti.Analysis.Distribution.TestFunction.SmulLeft

/-!
# Multiplication of complex distributions by smooth complex functions

A complex distribution `T : 𝓓'^{n}(Ω, ℂ)` can be multiplied by a `C^n` complex function `g`:
the product `g T` is the distribution `φ ↦ T (g φ)`, where `g φ` is a complex test function and
`T` acts on it through its complex-linear extension `Distribution.complexPairing`. Writing
`g = u + i v` with real `u` and `v`, this is `φ ↦ T (u φ) + i T (v φ)`, which is how
`Distribution.smulLeftCLM` is defined; for real `g` it is the precomposition of `T` with
`TestFunction.smulLeftCLM`, the convention already used for real multipliers. Smooth
multiplication is one of the basic operations under which the wave front set is studied, and
the complex multipliers include the characters `x ↦ exp(i ⟪x, η⟫)` of Fourier analysis.

## Main declarations

* `Distribution.smulLeftCLM`: the product `g T`, complex-linear and continuous in `T`.
* `Distribution.complexPairing_smulLeftCLM`: on complex test functions, `(g T) φ = T (g φ)`.
* `Distribution.smulLeftCLM_apply_eq_complexPairing`: the same formula on real test functions.
* `Distribution.smulLeftCLM_ofReal_apply`: for real `g` the product is `φ ↦ T (g φ)`, the
  precomposition with `TestFunction.smulLeftCLM`.
* `Distribution.smulLeftCLM_smulLeftCLM`, `Distribution.smulLeftCLM_const`: multiplying in turn
  by `g` and `h` is multiplying by `g h`, and a constant multiplier is scalar multiplication.
* `Distribution.smulLeftCLM_mapCLM_ofRealCLM_delta`, `Distribution.smulLeftCLM_ofFun`: `g δₓ` is
  `g x δₓ`, and the product with the distribution of a locally integrable function `f` is the
  distribution of `g f`.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, §2.1.
-/

public section

noncomputable section

open Complex TopologicalSpace TestFunction
open scoped Distributions CompactConvergenceCLM

namespace Distribution

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {Ω : Opens E} {n : ℕ∞}
  {g h : E → ℂ}

/-- The product `g T` of a complex distribution `T` with a `C^n` complex function `g`, defined by
`(g T) φ = T (re g • φ) + i T (im g • φ)`, that is, `T` applied to the complex test function
`g φ` (`Distribution.smulLeftCLM_apply_eq_complexPairing`). -/
def smulLeftCLM (hg : ContDiff ℝ n g) : 𝓓'^{n}(Ω, ℂ) →L[ℂ] 𝓓'^{n}(Ω, ℂ) where
  toFun T :=
    (TestFunction.smulLeftCLM (reCLM.contDiff.comp hg)).precompCompactConvergenceCLM ℂ T +
      I • (TestFunction.smulLeftCLM (imCLM.contDiff.comp hg)).precompCompactConvergenceCLM ℂ T
  map_add' S T := by
    simp only [map_add, smul_add]
    abel
  map_smul' c T := by
    -- Precomposition with a test-function operator commutes with complex scalars, although
    -- `precompCompactConvergenceCLM` is only bundled as a real-linear map.
    have hP (L : 𝓓^{n}(Ω, ℝ) →L[ℝ] 𝓓^{n}(Ω, ℝ)) :
        L.precompCompactConvergenceCLM ℂ (c • T) = c • L.precompCompactConvergenceCLM ℂ T :=
      (rfl)
    rw [RingHom.id_apply, hP, hP, smul_comm I c]
    exact (smul_add c _ _).symm
  cont := by fun_prop

/-- The defining formula of `g T` on a real test function `φ`:
`(g T) φ = T (re g • φ) + i T (im g • φ)`. -/
theorem smulLeftCLM_apply (hg : ContDiff ℝ n g) (T : 𝓓'^{n}(Ω, ℂ)) (φ : 𝓓^{n}(Ω, ℝ)) :
    smulLeftCLM hg T φ = T (TestFunction.smulLeftCLM (reCLM.contDiff.comp hg) φ) +
      I * T (TestFunction.smulLeftCLM (imCLM.contDiff.comp hg) φ) :=
  (rfl)

/-- **The product with a smooth function on complex test functions.** The complex-linear
extension of `g T` pairs a complex test function `φ` with `T` after multiplying it by `g`. -/
theorem complexPairing_smulLeftCLM (hg : ContDiff ℝ n g) (T : 𝓓'^{n}(Ω, ℂ))
    (φ : 𝓓^{n}(Ω, ℂ)) :
    (smulLeftCLM hg T).complexPairing φ =
      T.complexPairing (bilinLeftCLM (ContinuousLinearMap.mul ℝ ℂ) hg φ) := by
  -- Both sides expand into the pairings of `T` with the four real products `re/im g • re/im φ`.
  have hre : postcompCLM (𝕜 := ℝ) reCLM (bilinLeftCLM (ContinuousLinearMap.mul ℝ ℂ) hg φ) =
      TestFunction.smulLeftCLM (reCLM.contDiff.comp hg) (postcompCLM (𝕜 := ℝ) reCLM φ) -
        TestFunction.smulLeftCLM (imCLM.contDiff.comp hg) (postcompCLM (𝕜 := ℝ) imCLM φ) := by
    ext x
    simp [bilinLeftCLM_apply, mul_comm]
  have him : postcompCLM (𝕜 := ℝ) imCLM (bilinLeftCLM (ContinuousLinearMap.mul ℝ ℂ) hg φ) =
      TestFunction.smulLeftCLM (imCLM.contDiff.comp hg) (postcompCLM (𝕜 := ℝ) reCLM φ) +
        TestFunction.smulLeftCLM (reCLM.contDiff.comp hg) (postcompCLM (𝕜 := ℝ) imCLM φ) := by
    ext x
    simp [bilinLeftCLM_apply]
    ring
  rw [complexPairing_apply, complexPairing_apply T, hre, him, smulLeftCLM_apply,
    smulLeftCLM_apply, map_sub, map_add]
  ring_nf
  rw [I_sq]
  ring_nf

/-- **The product with a smooth function on real test functions.** `(g T) φ` is the pairing of
`T` with the complex test function `g φ`. -/
theorem smulLeftCLM_apply_eq_complexPairing (hg : ContDiff ℝ n g) (T : 𝓓'^{n}(Ω, ℂ))
    (φ : 𝓓^{n}(Ω, ℝ)) :
    smulLeftCLM hg T φ =
      T.complexPairing (bilinLeftCLM (ContinuousLinearMap.lsmul ℝ ℝ) hg φ) := by
  rw [← complexPairing_postcompCLM_ofRealCLM, complexPairing_smulLeftCLM]
  refine congrArg T.complexPairing (TestFunction.ext fun x ↦ ?_)
  simp [bilinLeftCLM_apply, real_smul]

/-- For a real multiplier `g`, the product `g T` is the precomposition of `T` with the
multiplication `φ ↦ g φ` of real test functions. -/
@[simp]
theorem smulLeftCLM_ofReal_apply {g : E → ℝ} (hg : ContDiff ℝ n g) (T : 𝓓'^{n}(Ω, ℂ))
    (φ : 𝓓^{n}(Ω, ℝ)) :
    smulLeftCLM (ofRealCLM.contDiff.comp hg) T φ = T (TestFunction.smulLeftCLM hg φ) := by
  have hre : TestFunction.smulLeftCLM (reCLM.contDiff.comp (ofRealCLM.contDiff.comp hg)) φ =
      TestFunction.smulLeftCLM hg φ := by
    ext x
    simp
  have him : TestFunction.smulLeftCLM (imCLM.contDiff.comp (ofRealCLM.contDiff.comp hg)) φ =
      0 := by
    ext x
    simp
  rw [smulLeftCLM_apply, hre, him, map_zero, mul_zero, add_zero]

/-- Multiplying a distribution by `h` and then by `g` is multiplying it by `g h`. -/
@[simp]
theorem smulLeftCLM_smulLeftCLM (hg : ContDiff ℝ n g) (hh : ContDiff ℝ n h)
    (T : 𝓓'^{n}(Ω, ℂ)) :
    smulLeftCLM hg (smulLeftCLM hh T) = smulLeftCLM (hg.mul hh) T := by
  ext φ
  rw [smulLeftCLM_apply_eq_complexPairing, smulLeftCLM_apply_eq_complexPairing,
    complexPairing_smulLeftCLM]
  congr 1
  ext x
  simp [bilinLeftCLM_apply]
  ring

/-- Multiplication by a constant function `c` is scalar multiplication by `c`. -/
@[simp]
theorem smulLeftCLM_const (c : ℂ) (T : 𝓓'^{n}(Ω, ℂ)) :
    smulLeftCLM (contDiff_const (c := c)) T = c • T := by
  ext φ
  rw [smulLeftCLM_apply_eq_complexPairing, smul_apply, smul_eq_mul,
    ← complexPairing_postcompCLM_ofRealCLM, ← smul_eq_mul, ← map_smul]
  congr 1
  ext x
  simp [bilinLeftCLM_apply, mul_comm]

/-- The product of a smooth function `g` with the complex point mass at `x` is `g x` times that
point mass. -/
@[simp]
theorem smulLeftCLM_mapCLM_ofRealCLM_delta (hg : ContDiff ℝ n g) (x : E) :
    smulLeftCLM hg (mapCLM ofRealCLM (delta x : 𝓓'^{n}(Ω, ℝ))) =
      g x • mapCLM ofRealCLM (delta x : 𝓓'^{n}(Ω, ℝ)) := by
  ext φ
  rw [smulLeftCLM_apply_eq_complexPairing, complexPairing_mapCLM_ofRealCLM_delta, smul_apply,
    smul_eq_mul]
  simp [bilinLeftCLM_apply, real_smul, mul_comm]

/-- The product of a smooth function `g` with the distribution of a locally integrable function
`f` is the distribution of the pointwise product `g f`. -/
theorem smulLeftCLM_ofFun [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (hg : ContDiff ℝ n g) {f : E → ℂ} {μ : MeasureTheory.Measure E}
    (hf : MeasureTheory.LocallyIntegrableOn f Ω μ) :
    smulLeftCLM hg (ofFun Ω f μ n) = ofFun Ω (fun x ↦ g x * f x) μ n := by
  ext φ
  rw [smulLeftCLM_apply_eq_complexPairing, complexPairing_ofFun hf,
    ofFun_apply (hf.continuousOn_mul hg.continuous.continuousOn Ω.isOpen.isLocallyClosed)]
  simp [bilinLeftCLM_apply, mul_assoc]

end Distribution
