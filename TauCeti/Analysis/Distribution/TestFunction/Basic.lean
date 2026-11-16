/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.TestFunction

/-!
# Components of vector-valued test functions in a basis

Let `F` be a finite-dimensional real normed space with a basis `(bᵢ)`. An `F`-valued test
function `φ` has the real-valued components `bᵢ* ∘ φ`, obtained by postcomposition with the
coordinate functionals of the basis, and is recovered from them as `φ = ∑ᵢ (bᵢ* ∘ φ) • bᵢ`.
Conversely, for a real test function `ψ` and a vector `v : F`, any continuous linear functional
`f` on `F` sends the test function `ψ • v` to the multiple `f v • ψ`; in particular the components
of `ψ • v` are the multiples `b.repr v i • ψ`. These identities reduce statements about
`F`-valued test functions to statements about real-valued ones. Pointwise complex conjugation,
postcomposition with `Complex.conjCLE`, is an involution on complex test functions. Multiplying
a test function by a smooth function through a bilinear map (`TestFunction.bilinLeftCLM`) does
not enlarge its support.

## Main declarations

* `TestFunction.postcompCLM_postcompCLM`: postcomposing with `L₁` and then with `L₂` is
  postcomposing with `L₂ ∘L L₁`.
* `TestFunction.postcompCLM_conj_postcompCLM_conj`: conjugating a complex test function twice
  gives it back.
* `TestFunction.sum_postcompCLM_toSpanSingleton_coord`: an `F`-valued test function is the sum
  of its components in a basis, times the basis vectors.
* `TestFunction.postcompCLM_postcompCLM_toSpanSingleton`: a continuous linear functional applied
  to `ψ • v`.
* `TestFunction.tsupport_bilinLeftCLM_subset`: multiplying by a smooth function through a bilinear
  map does not enlarge the support.
-/

public section

namespace TestFunction

open TopologicalSpace ContinuousLinearMap
open scoped Distributions BoundedContinuousFunction

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {Ω : Opens E}
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {n : ℕ∞}

/-- A test function is zero as a bounded continuous function exactly when it is zero. -/
@[simp]
theorem toBoundedContinuousFunction_eq_zero (φ : 𝓓^{n}(Ω, F)) :
    (φ : E →ᵇ F) = 0 ↔ φ = 0 := by
  simpa only [map_zero, toBoundedContinuousFunctionCLM_apply] using
    ((injective_toBoundedContinuousFunctionCLM ℝ).eq_iff (a := φ) (b := 0))

/-- Postcomposing a test function with `L₁` and then with `L₂` is postcomposing it with
`L₂ ∘L L₁`. Unlike `SchwartzMap.postcompCLM_postcompCLM`, this is not a simp lemma: it would merge
the factors of the basis expansion in `sum_postcompCLM_toSpanSingleton_coord` into composites such
as `toSpanSingleton ℝ (b i) ∘L b.coord i`, which simp cannot evaluate further. -/
theorem postcompCLM_postcompCLM {𝕜 : Type*} [NontriviallyNormedField 𝕜] [Algebra ℝ 𝕜]
    [NormedSpace 𝕜 F] [IsScalarTower ℝ 𝕜 F] {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedSpace 𝕜 G] [IsScalarTower ℝ 𝕜 G] {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedSpace 𝕜 H] [IsScalarTower ℝ 𝕜 H] (L₁ : F →L[𝕜] G) (L₂ : G →L[𝕜] H)
    (φ : 𝓓^{n}(Ω, F)) :
    postcompCLM L₂ (postcompCLM L₁ φ) = postcompCLM (L₂ ∘L L₁) φ :=
  rfl

/-- Conjugating a complex test function twice gives it back. -/
@[simp]
theorem postcompCLM_conj_postcompCLM_conj (φ : 𝓓^{n}(Ω, ℂ)) :
    postcompCLM (𝕜 := ℝ) Complex.conjCLE.toContinuousLinearMap
      (postcompCLM (𝕜 := ℝ) Complex.conjCLE.toContinuousLinearMap φ) = φ := by
  ext y
  simp

/-- An `F`-valued test function `φ` is the sum of its components `bᵢ* ∘ φ` in a basis `b` of `F`,
each multiplied by the corresponding basis vector `bᵢ`. -/
theorem sum_postcompCLM_toSpanSingleton_coord [FiniteDimensional ℝ F] {ι : Type*} [Fintype ι]
    (b : Module.Basis ι ℝ F) (φ : 𝓓^{n}(Ω, F)) :
    ∑ i, postcompCLM (toSpanSingleton ℝ (b i))
      (postcompCLM (b.coord i).toContinuousLinearMap φ) = φ := by
  ext x
  simp only [sum_apply, postcompCLM_apply, Function.comp_apply, toSpanSingleton_apply,
    LinearMap.coe_toContinuousLinearMap', Module.Basis.coord_apply]
  exact b.sum_repr (φ x)

/-- Multiplying a test function by a smooth function through a continuous bilinear map `B` does
not enlarge its support. -/
theorem tsupport_bilinLeftCLM_subset {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedAlgebra ℝ 𝕜]
    {F₁ F₂ F₃ : Type*} [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] [NormedSpace ℝ F₁]
    [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂] [NormedSpace ℝ F₂]
    [NormedAddCommGroup F₃] [NormedSpace 𝕜 F₃] [NormedSpace ℝ F₃]
    (B : F₁ →L[𝕜] F₂ →L[𝕜] F₃) {g : E → F₂} (hg : ContDiff ℝ n g) (φ : 𝓓^{n}(Ω, F₁)) :
    tsupport (bilinLeftCLM B hg φ : E → F₃) ⊆ tsupport φ :=
  closure_mono fun x hx => Function.mem_support.2 fun h => hx (by simp [h])

/-- A continuous linear functional `f` on `F` sends the test function `ψ • v` to `f v • ψ`. -/
@[simp]
theorem postcompCLM_postcompCLM_toSpanSingleton (f : F →L[ℝ] ℝ) (ψ : 𝓓^{n}(Ω, ℝ)) (v : F) :
    postcompCLM f (postcompCLM (toSpanSingleton ℝ v) ψ) = f v • ψ := by
  ext x
  rw [postcompCLM_postcompCLM, postcompCLM_apply]
  simp [mul_comm]

end TestFunction
