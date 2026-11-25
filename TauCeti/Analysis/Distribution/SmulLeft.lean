/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.ComplexPairing
public import TauCeti.Analysis.Distribution.TestFunction.PartitionOfUnity
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

In a finite-dimensional space the multiplier only needs to be `C^n` on `Ω`
(`Distribution.smulLeftCLMOfContDiffOn`), the transpose of `TestFunction.smulLeftCLMOfContDiffOn`,
so a distribution on `Ω` can be multiplied by any function smooth on `Ω`.

A complex multiplier `g + i h` acts on a complex distribution as `g T + i (h T)`; on complex test
functions the product pairs as `(g T) ψ = T (g ψ)` (`Distribution.complexPairing_smulLeftCLM`).

When the support of `g` meets an open set `Ω'` only inside `Ω`, multiplication by `g` sends tests
on `Ω'` to tests on `Ω` (`TestFunction.cutoffCLM`), and its transpose `Distribution.cutoffCLM`
sends a distribution `T` on `Ω` to the distribution `φ ↦ T (g φ)` on `Ω'`, supported in the
support of `g`. For a test function `g` on `Ω` and `Ω' = ⊤` this is the extension by zero of the
compactly supported distribution `g T` from `Ω` to the whole space.

## Main declarations

* `Distribution.smulLeftCLM`: the product `g T`, with `Distribution.smulLeftCLM_apply` and
  `Distribution.coe_smulLeftCLM`.
* `Distribution.smulLeftCLM_const`: a constant `c` acts as the scalar `c`.
* `Distribution.smulLeftCLM_smulLeftCLM`: multiplying by `h` and then by `g` is multiplying by
  `g h`.
* `Distribution.mapCLM_smulLeftCLM`: multiplying by `g` commutes with a linear map of the values.
* `Distribution.dsupport_smulLeftCLM_subset_inter`: the support of `g T` lies in the supports of `g`
  and of `T`.
* `Distribution.complexPairing_eq_of_coe_eq_comp`: a multiplication operator pairs with complex
  test functions through multiplication of complex test functions.
* `Distribution.complexPairing_smulLeftCLM`: the pairing of `g T` with a complex test function.
* `Distribution.smulLeftCLMOfContDiffOn`: the product `g T` for a function `g` that is `C^n` on `Ω`
  only, with `Distribution.smulLeftCLMOfContDiffOn_eq_smulLeftCLM`,
  `Distribution.smulLeftCLMOfContDiffOn_congr`,
  `Distribution.smulLeftCLMOfContDiffOn_smulLeftCLMOfContDiffOn`,
  `Distribution.mapCLM_smulLeftCLMOfContDiffOn`,
  `Distribution.dsupport_smulLeftCLMOfContDiffOn_subset_inter` and
  `Distribution.complexPairing_smulLeftCLMOfContDiffOn`.
* `Distribution.cutoffCLM`: the distribution `φ ↦ T (g φ)` on `Ω'`, with
  `Distribution.cutoffCLM_apply`, `Distribution.dsupport_cutoffCLM_subset_inter` and
  `Distribution.complexPairing_cutoffCLM`.

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

/-- Let `S = T ∘ P` for a map `P` of real test functions on `Ω'` to real test functions on `Ω`
acting as multiplication by `g`. Then the complex-linear extension of `S` pairs with a complex test
function `ψ` as that of `T` with the complex test function `g ψ`. Every multiplication operator on
distributions pairs with complex test functions this way. -/
theorem complexPairing_eq_of_coe_eq_comp {Ω' : Opens E} {S : 𝓓'^{n}(Ω', ℂ)}
    {T : 𝓓'^{n}(Ω, ℂ)} {P : 𝓓^{n}(Ω', ℝ) → 𝓓^{n}(Ω, ℝ)} (hS : ⇑S = ⇑T ∘ P)
    (hP : ∀ φ x, P φ x = g x • φ x) {ψ : 𝓓^{n}(Ω', ℂ)} {ψ' : 𝓓^{n}(Ω, ℂ)}
    (hψ : ∀ x, ψ' x = g x • ψ x) : S.complexPairing ψ = T.complexPairing ψ' := by
  have hpart (L : ℂ →L[ℝ] ℝ) :
      TestFunction.postcompCLM (𝕜 := ℝ) L ψ' = P (TestFunction.postcompCLM (𝕜 := ℝ) L ψ) := by
    ext x
    simp [hP, hψ, -real_smul]
  simp [complexPairing_apply, hS, hpart]

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

/-- Multiplication by a smooth function commutes with applying a continuous linear map to the
values. -/
theorem mapCLM_smulLeftCLM {F' : Type*} [AddCommGroup F'] [Module ℝ F'] [TopologicalSpace F']
    [IsTopologicalAddGroup F'] [ContinuousSMul ℝ F'] (A : F →L[ℝ] F') (hg : ContDiff ℝ n g)
    (T : 𝓓'^{n}(Ω, F)) : mapCLM A (smulLeftCLM hg T) = smulLeftCLM hg (mapCLM A T) := by
  ext φ
  simp

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
    (smulLeftCLM hg T).complexPairing ψ = T.complexPairing (TestFunction.smulLeftCLM hg ψ) :=
  complexPairing_eq_of_coe_eq_comp (coe_smulLeftCLM hg T) (TestFunction.smulLeftCLM_apply hg)
    (TestFunction.smulLeftCLM_apply hg ψ)

section SmulLeftOfContDiffOn

variable [FiniteDimensional ℝ E]

/-- The product `g T` of a distribution `T` on `Ω` with a function `g` that is `C^n` on `Ω` only,
defined by `(g T) φ = T (g φ)`, as a continuous linear map on distributions of order at most `n`.
Nothing is required of `g` off `Ω`. -/
def smulLeftCLMOfContDiffOn (hg : ContDiffOn ℝ n g Ω) : 𝓓'^{n}(Ω, F) →L[ℝ] 𝓓'^{n}(Ω, F) :=
  (TestFunction.smulLeftCLMOfContDiffOn hg).precompCompactConvergenceCLM F

@[simp]
theorem smulLeftCLMOfContDiffOn_apply (hg : ContDiffOn ℝ n g Ω) (T : 𝓓'^{n}(Ω, F))
    (φ : 𝓓^{n}(Ω, ℝ)) :
    smulLeftCLMOfContDiffOn hg T φ = T (TestFunction.smulLeftCLMOfContDiffOn hg φ) :=
  (rfl)

/-- As a function on test functions, `g T` is `T` composed with multiplication by `g`. -/
theorem coe_smulLeftCLMOfContDiffOn (hg : ContDiffOn ℝ n g Ω) (T : 𝓓'^{n}(Ω, F)) :
    ⇑(smulLeftCLMOfContDiffOn hg T) = ⇑T ∘ ⇑(TestFunction.smulLeftCLMOfContDiffOn hg) :=
  (rfl)

/-- For a globally `C^n` multiplier `g`, `Distribution.smulLeftCLMOfContDiffOn` is
`Distribution.smulLeftCLM`. -/
theorem smulLeftCLMOfContDiffOn_eq_smulLeftCLM (hg : ContDiff ℝ n g) :
    (smulLeftCLMOfContDiffOn hg.contDiffOn : 𝓓'^{n}(Ω, F) →L[ℝ] 𝓓'^{n}(Ω, F)) =
      smulLeftCLM hg := by
  ext T φ
  rw [smulLeftCLMOfContDiffOn_apply, smulLeftCLM_apply,
    TestFunction.smulLeftCLMOfContDiffOn_eq_smulLeftCLM]

/-- Multiplication of distributions by a function `C^n` on `Ω` depends only on the values of the
multiplier on `Ω`. -/
theorem smulLeftCLMOfContDiffOn_congr (hg : ContDiffOn ℝ n g Ω) (hh : ContDiffOn ℝ n h Ω)
    (hgh : EqOn g h Ω) :
    (smulLeftCLMOfContDiffOn hg : 𝓓'^{n}(Ω, F) →L[ℝ] 𝓓'^{n}(Ω, F)) =
      smulLeftCLMOfContDiffOn hh := by
  ext T φ
  rw [smulLeftCLMOfContDiffOn_apply, smulLeftCLMOfContDiffOn_apply,
    TestFunction.smulLeftCLMOfContDiffOn_congr hg hh hgh]

/-- Multiplying a distribution by `h` and then by `g`, both `C^n` on `Ω`, is multiplying it by
`g h`. -/
@[simp]
theorem smulLeftCLMOfContDiffOn_smulLeftCLMOfContDiffOn (hg : ContDiffOn ℝ n g Ω)
    (hh : ContDiffOn ℝ n h Ω) (T : 𝓓'^{n}(Ω, F)) :
    smulLeftCLMOfContDiffOn hg (smulLeftCLMOfContDiffOn hh T) =
      smulLeftCLMOfContDiffOn (hg.mul hh) T := by
  ext φ
  simp only [smulLeftCLMOfContDiffOn_apply,
    TestFunction.smulLeftCLMOfContDiffOn_smulLeftCLMOfContDiffOn]
  congr 1
  ext x
  simp [mul_comm]

/-- Multiplication by a function `C^n` on `Ω` commutes with applying a continuous linear map to
the values. -/
theorem mapCLM_smulLeftCLMOfContDiffOn {F' : Type*} [AddCommGroup F'] [Module ℝ F']
    [TopologicalSpace F'] [IsTopologicalAddGroup F'] [ContinuousSMul ℝ F'] (A : F →L[ℝ] F')
    (hg : ContDiffOn ℝ n g Ω) (T : 𝓓'^{n}(Ω, F)) :
    mapCLM A (smulLeftCLMOfContDiffOn hg T) = smulLeftCLMOfContDiffOn hg (mapCLM A T) := by
  ext φ
  simp

/-- The support of `g T` lies both in the support of `g` and in the support of `T`. -/
theorem dsupport_smulLeftCLMOfContDiffOn_subset_inter (hg : ContDiffOn ℝ n g Ω)
    (T : 𝓓'^{n}(Ω, F)) : dsupport (smulLeftCLMOfContDiffOn hg T) ⊆ tsupport g ∩ dsupport T := by
  rw [coe_smulLeftCLMOfContDiffOn]
  exact dsupport_comp_smulLeftCLMOfContDiffOn_subset T hg

/-- The complex-linear extension of `g T` to complex test functions pairs `g T` with `ψ` as `T`
with `g ψ`. -/
@[simp]
theorem complexPairing_smulLeftCLMOfContDiffOn (hg : ContDiffOn ℝ n g Ω) (T : 𝓓'^{n}(Ω, ℂ))
    (ψ : 𝓓^{n}(Ω, ℂ)) :
    (smulLeftCLMOfContDiffOn hg T).complexPairing ψ =
      T.complexPairing (TestFunction.smulLeftCLMOfContDiffOn hg ψ) :=
  complexPairing_eq_of_coe_eq_comp (coe_smulLeftCLMOfContDiffOn hg T)
    (TestFunction.smulLeftCLMOfContDiffOn_apply hg)
    (TestFunction.smulLeftCLMOfContDiffOn_apply hg ψ)

end SmulLeftOfContDiffOn

section Cutoff

variable {Ω' : Opens E} (hg : ContDiff ℝ n g) (hgΩ : tsupport g ∩ Ω' ⊆ Ω)

/-- For a `C^n` function `g` whose support meets `Ω'` only inside `Ω`, the distribution
`φ ↦ T (g φ)` on `Ω'` defined by a distribution `T` on `Ω`, as a continuous linear map on
distributions of order at most `n`. For a test function `g` on `Ω` and `Ω' = ⊤` it is the
extension by zero of `g T` from `Ω` to the whole space. -/
def cutoffCLM : 𝓓'^{n}(Ω, F) →L[ℝ] 𝓓'^{n}(Ω', F) :=
  (TestFunction.cutoffCLM hg hgΩ).precompCompactConvergenceCLM F

@[simp]
theorem cutoffCLM_apply (T : 𝓓'^{n}(Ω, F)) (φ : 𝓓^{n}(Ω', ℝ)) :
    cutoffCLM hg hgΩ T φ = T (TestFunction.cutoffCLM hg hgΩ φ) :=
  (rfl)

/-- As a function on test functions, `cutoffCLM hg hgΩ T` is `T` composed with multiplication
by `g`. -/
theorem coe_cutoffCLM (T : 𝓓'^{n}(Ω, F)) :
    ⇑(cutoffCLM hg hgΩ T) = ⇑T ∘ ⇑(TestFunction.cutoffCLM hg hgΩ) :=
  (rfl)

/-- The support of `φ ↦ T (g φ)` lies both in the support of `g` and in the support of `T`. -/
theorem dsupport_cutoffCLM_subset_inter (T : 𝓓'^{n}(Ω, F)) :
    dsupport (cutoffCLM hg hgΩ T) ⊆ tsupport g ∩ dsupport T := by
  rw [coe_cutoffCLM]
  exact dsupport_comp_cutoffCLM_subset T hg hgΩ

/-- The complex-linear extension of `φ ↦ T (g φ)` to complex test functions pairs it with `ψ` as
`T` with `g ψ`. -/
@[simp]
theorem complexPairing_cutoffCLM (T : 𝓓'^{n}(Ω, ℂ)) (ψ : 𝓓^{n}(Ω', ℂ)) :
    (cutoffCLM hg hgΩ T).complexPairing ψ =
      T.complexPairing (TestFunction.cutoffCLM hg hgΩ ψ) :=
  complexPairing_eq_of_coe_eq_comp (coe_cutoffCLM hg hgΩ T) (TestFunction.cutoffCLM_apply hg hgΩ)
    (TestFunction.cutoffCLM_apply hg hgΩ ψ)

end Cutoff

end Distribution
