/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.TestFunction
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff

/-!
# Basic facts about test functions

A test function on `Ω` supported in an open set `Ω' ≤ Ω` is the extension by zero
(`TestFunction.monoCLM`) of a test function on `Ω'`. A test function on `Ω` times a function that
is `C^n` on `Ω`, with no condition off `Ω`, is again a test function on `Ω`.

Let `F` be a finite-dimensional real normed space with a basis `(bᵢ)`. An `F`-valued test
function `φ` has the real-valued components `bᵢ* ∘ φ`, obtained by postcomposition with the
coordinate functionals of the basis, and is recovered from them as `φ = ∑ᵢ (bᵢ* ∘ φ) • bᵢ`.
Conversely, for a real test function `ψ` and a vector `v : F`, any continuous linear functional
`f` on `F` sends the test function `ψ • v` to the multiple `f v • ψ`; in particular the components
of `ψ • v` are the multiples `b.repr v i • ψ`. These identities reduce statements about
`F`-valued test functions to statements about real-valued ones. Pointwise complex conjugation,
postcomposition with `Complex.conjCLE`, is an involution on complex test functions. On an
infinite-dimensional space every test function is zero (Riesz).

## Main declarations

* `TestFunction.coe_monoCLM`: extending a test function by zero does not change it as a
  function.
* `TestFunction.exists_monoCLM_eq_of_tsupport_subset`: a test function supported in a smaller
  open set is the extension by zero of a test function on that set.
* `TestFunction.exists_coe_eq_smul_of_contDiffOn`: the product of a `C^n` test function on `Ω`
  with a function `C^n` on `Ω` is a `C^n` test function on `Ω`.
* `TestFunction.tsupport_subset_inter_of_apply_eq_smul`: a test function with values `g x • φ x`
  is supported in the supports of `g` and of `φ`.
* `TestFunction.eq_zero_of_not_finiteDimensional`: on an infinite-dimensional space every test
  function is zero.
* `TestFunction.postcompCLM_postcompCLM`: postcomposing with `L₁` and then with `L₂` is
  postcomposing with `L₂ ∘L L₁`.
* `TestFunction.postcompCLM_conj_postcompCLM_conj`: conjugating a complex test function twice
  gives it back.
* `TestFunction.sum_postcompCLM_toSpanSingleton_coord`: an `F`-valued test function is the sum
  of its components in a basis, times the basis vectors.
* `TestFunction.postcompCLM_postcompCLM_toSpanSingleton`: a continuous linear functional applied
  to `ψ • v`.
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

/-- Extending a test function on an open set `Ω' ≤ Ω` by zero to `Ω` does not change it as a
function on `E`. -/
theorem coe_monoCLM {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 F] [Algebra ℝ 𝕜]
    [IsScalarTower ℝ 𝕜 F] {Ω' : Opens E} (h : Ω' ≤ Ω) (φ : 𝓓^{n}(Ω', F)) :
    ⇑(monoCLM 𝕜 φ : 𝓓^{n}(Ω, F)) = φ := by
  simp [h]

/-- A test function on `Ω` supported in an open set `Ω' ≤ Ω` is the extension by zero of a test
function on `Ω'`. -/
theorem exists_monoCLM_eq_of_tsupport_subset {Ω' : Opens E} (h : Ω' ≤ Ω) {φ : 𝓓^{n}(Ω, F)}
    (hφ : tsupport φ ⊆ Ω') : ∃ ψ : 𝓓^{n}(Ω', F), monoCLM ℝ ψ = φ :=
  ⟨⟨φ, φ.contDiff, φ.hasCompactSupport, hφ⟩, TestFunction.ext fun x ↦ by simp [h]⟩

/-- **A test function times a function `C^n` on `Ω` is a test function.** If `g` is `C^n` on
`Ω`, with no condition off `Ω`, and `φ ∈ 𝓓^{n}(Ω, F)`, then `x ↦ g x • φ x` is again a `C^n` test
function on `Ω`: it is `C^n` on `Ω`, which contains the support of `φ`. The multiplier may take
values in any nontrivially normed field `𝕜` that is a normed `ℝ`-algebra acting on `F`, such as
`ℂ` acting on a complex test function. -/
theorem exists_coe_eq_smul_of_contDiffOn {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    [NormedAlgebra ℝ 𝕜] [NormedSpace 𝕜 F] [IsScalarTower ℝ 𝕜 F] {g : E → 𝕜}
    (hg : ContDiffOn ℝ n g Ω) (φ : 𝓓^{n}(Ω, F)) : ∃ ψ : 𝓓^{n}(Ω, F), ⇑ψ = fun x => g x • φ x :=
  ⟨⟨fun x => g x • φ x, (lsmul ℝ 𝕜 : 𝕜 →L[ℝ] F →L[ℝ] F).contDiff_of_tsupport_subset_right hg
      φ.contDiff.contDiffOn Ω.isOpen φ.tsupport_subset, φ.hasCompactSupport.smul_left,
    (tsupport_smul_subset_right _ _).trans φ.tsupport_subset⟩, rfl⟩

/-- A test function with values `g x • φ x` is supported both in the support of `g` and in the
support of `φ`. This bounds the support of every multiple of a test function, whatever operator
produces it. -/
theorem tsupport_subset_inter_of_apply_eq_smul {Ω' : Opens E} {m : ℕ∞} {g : E → ℝ}
    {φ : 𝓓^{m}(Ω', F)} {ψ : 𝓓^{n}(Ω, F)} (h : ∀ x, ψ x = g x • φ x) :
    tsupport ψ ⊆ tsupport g ∩ tsupport φ := by
  rw [show ⇑ψ = g • ⇑φ from funext h]
  exact Set.subset_inter (tsupport_smul_subset_left g φ) (tsupport_smul_subset_right g φ)

/-- On an infinite-dimensional space every test function is zero: a nonzero continuous function
with compact support forces finite dimension (Riesz,
`HasCompactSupport.eq_zero_or_finiteDimensional`). -/
theorem eq_zero_of_not_finiteDimensional (φ : 𝓓^{n}(Ω, F)) (hE : ¬FiniteDimensional ℝ E) :
    φ = 0 :=
  DFunLike.coe_injective <|
    (φ.hasCompactSupport.eq_zero_or_finiteDimensional ℝ φ.continuous).resolve_right hE

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

/-- A continuous linear functional `f` on `F` sends the test function `ψ • v` to `f v • ψ`. -/
@[simp]
theorem postcompCLM_postcompCLM_toSpanSingleton (f : F →L[ℝ] ℝ) (ψ : 𝓓^{n}(Ω, ℝ)) (v : F) :
    postcompCLM f (postcompCLM (toSpanSingleton ℝ v) ψ) = f v • ψ := by
  ext x
  rw [postcompCLM_postcompCLM, postcompCLM_apply]
  simp [mul_comm]

end TestFunction
