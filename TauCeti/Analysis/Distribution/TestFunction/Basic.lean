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
Conversely, the components of the test function `ψ • v`, for a real test function `ψ` and a
vector `v : F`, are the multiples `b.repr v i • ψ`. These identities reduce statements about
`F`-valued test functions to statements about real-valued ones.

## Main declarations

* `TestFunction.sum_postcompCLM_toSpanSingleton_coord`: an `F`-valued test function is the sum
  of its components in a basis, times the basis vectors.
* `TestFunction.postcompCLM_coord_postcompCLM_toSpanSingleton`: the components of `ψ • v` in a
  basis.
-/

public section

namespace TestFunction

open TopologicalSpace ContinuousLinearMap
open scoped Distributions

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {Ω : Opens E}
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] {n : ℕ∞}

/-- An `F`-valued test function `φ` is the sum of its components `bᵢ* ∘ φ` in a basis `b` of `F`,
each multiplied by the corresponding basis vector `bᵢ`. -/
theorem sum_postcompCLM_toSpanSingleton_coord {ι : Type*} [Fintype ι] (b : Module.Basis ι ℝ F)
    (φ : 𝓓^{n}(Ω, F)) :
    ∑ i, postcompCLM (toSpanSingleton ℝ (b i))
      (postcompCLM (b.coord i).toContinuousLinearMap φ) = φ := by
  ext x
  simp only [sum_apply, postcompCLM_apply, Function.comp_apply, toSpanSingleton_apply,
    LinearMap.coe_toContinuousLinearMap', Module.Basis.coord_apply]
  exact b.sum_repr (φ x)

/-- The `i`-th component, in a basis `b` of `F`, of the test function `ψ • v` is `b.repr v i • ψ`.
-/
@[simp]
theorem postcompCLM_coord_postcompCLM_toSpanSingleton {ι : Type*} (b : Module.Basis ι ℝ F)
    (i : ι) (ψ : 𝓓^{n}(Ω, ℝ)) (v : F) :
    postcompCLM (b.coord i).toContinuousLinearMap (postcompCLM (toSpanSingleton ℝ v) ψ) =
      b.repr v i • ψ := by
  ext x
  rw [postcompCLM_apply, postcompCLM_apply]
  simp [mul_comm]

end TestFunction
