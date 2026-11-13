/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.TestFunction

/-!
# Basic constructions on test functions

A test function on an open set `Ω` contained in a compact set `K` is a smooth function supported
in `K`; `TestFunction.toSupportedInCLM` records this as a continuous linear map from the test
functions on `Ω` to `𝓓^{n}_{K}(E, F)`, the space on which estimates by finitely many `C^k`
seminorms are stated.

Let `F` be a finite-dimensional real normed space with a basis `(bᵢ)`. An `F`-valued test
function `φ` has the real-valued components `bᵢ* ∘ φ`, obtained by postcomposition with the
coordinate functionals of the basis, and is recovered from them as `φ = ∑ᵢ (bᵢ* ∘ φ) • bᵢ`.
Conversely, for a real test function `ψ` and a vector `v : F`, any continuous linear functional
`f` on `F` sends the test function `ψ • v` to the multiple `f v • ψ`; in particular the components
of `ψ • v` are the multiples `b.repr v i • ψ`. These identities reduce statements about
`F`-valued test functions to statements about real-valued ones.

## Main declarations

* `TestFunction.postcompCLM_postcompCLM`: postcomposing with `L₁` and then with `L₂` is
  postcomposing with `L₂ ∘L L₁`.
* `TestFunction.sum_postcompCLM_toSpanSingleton_coord`: an `F`-valued test function is the sum
  of its components in a basis, times the basis vectors.
* `TestFunction.postcompCLM_postcompCLM_toSpanSingleton`: a continuous linear functional applied
  to `ψ • v`.
* `TestFunction.toSupportedInCLM`: a test function on an open set contained in a compact set `K`,
  as a function supported in `K`.
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

section ToSupportedIn

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 F] [SMulCommClass ℝ 𝕜 F]

variable (𝕜) in
/-- A test function on an open set `Ω` contained in a compact set `K` is a function supported in
`K`. This forgetful map `𝓓^{n}(Ω, F) →L[𝕜] 𝓓^{n}_{K}(E, F)` is continuous for the LF topology. -/
noncomputable def toSupportedInCLM {K : Compacts E} (hΩK : (Ω : Set E) ⊆ K) :
    𝓓^{n}(Ω, F) →L[𝕜] 𝓓^{n}_{K}(E, F) where
  toFun φ := .of_support_subset φ.contDiff ((subset_tsupport _).trans (φ.tsupport_subset.trans hΩK))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := (TestFunction.mkCLM ℝ (V := 𝓓^{n}_{K}(E, F)) (fun φ ↦ .of_support_subset φ.contDiff
      ((subset_tsupport _).trans (φ.tsupport_subset.trans hΩK)))
    (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)
    (fun K' hK' ↦ (ContDiffMapSupportedIn.monoCLM ℝ (K₁ := K') (K₂ := K) (n₁ := n)
      (n₂ := n)).continuous.congr fun φ ↦ by
        ext x
        simp [SetLike.coe_subset_coe.1 (hK'.trans hΩK)])).continuous

@[simp]
theorem toSupportedInCLM_apply {K : Compacts E} (hΩK : (Ω : Set E) ⊆ K) (φ : 𝓓^{n}(Ω, F)) :
    ⇑(toSupportedInCLM 𝕜 hΩK φ) = φ :=
  (rfl)

theorem toSupportedInCLM_eq_of_scalars (𝕜' : Type*) [NontriviallyNormedField 𝕜']
    [NormedSpace 𝕜' F] [SMulCommClass ℝ 𝕜' F] {K : Compacts E} (hΩK : (Ω : Set E) ⊆ K) :
    (toSupportedInCLM 𝕜 hΩK : 𝓓^{n}(Ω, F) → 𝓓^{n}_{K}(E, F)) = toSupportedInCLM 𝕜' hΩK := by
  ext φ x
  simp

/-- A test function on `Ω'`, read as a function supported in a compact set `K ⊆ Ω` and then as a
test function on `Ω`, is its extension by zero `monoCLM`. -/
@[simp]
theorem ofSupportedIn_toSupportedInCLM {Ω' : Opens E} {K : Compacts E}
    (hΩ'K : (Ω' : Set E) ⊆ K) (hKΩ : (K : Set E) ⊆ Ω) (φ : 𝓓^{n}(Ω', F)) :
    ofSupportedIn hKΩ (toSupportedInCLM 𝕜 hΩ'K φ) = monoCLM ℝ φ := by
  ext x
  simp [SetLike.coe_subset_coe.1 (hΩ'K.trans hKΩ)]

/-- A function supported in `K'`, read as a test function on `Ω` and then as a function supported
in a compact set `K ⊇ Ω`, is its inclusion `monoCLM` into the functions supported in `K`. -/
@[simp]
theorem toSupportedInCLM_ofSupportedIn {K K' : Compacts E} (hK'Ω : (K' : Set E) ⊆ Ω)
    (hΩK : (Ω : Set E) ⊆ K) (φ : 𝓓^{n}_{K'}(E, F)) :
    toSupportedInCLM 𝕜 hΩK (ofSupportedIn hK'Ω φ) = ContDiffMapSupportedIn.monoCLM 𝕜 φ := by
  ext x
  simp [SetLike.coe_subset_coe.1 (hK'Ω.trans hΩK)]

/-- Reading a test function as supported in `K` and then in a larger compact set `K'` is reading
it as supported in `K'`. -/
@[simp]
theorem monoCLM_toSupportedInCLM {K K' : Compacts E} (hΩK : (Ω : Set E) ⊆ K) (hKK' : K ≤ K')
    (φ : 𝓓^{n}(Ω, F)) :
    (ContDiffMapSupportedIn.monoCLM 𝕜 (toSupportedInCLM 𝕜 hΩK φ) : 𝓓^{n}_{K'}(E, F)) =
      toSupportedInCLM 𝕜 (hΩK.trans hKK') φ := by
  ext x
  simp [hKK']

/-- Extending a test function from `Ω` to `Ω'` and reading it as supported in `K ⊇ Ω'` is reading
it as supported in `K`. -/
@[simp]
theorem toSupportedInCLM_monoCLM {Ω' : Opens E} {K : Compacts E} (hΩΩ' : Ω ≤ Ω')
    (hΩ'K : (Ω' : Set E) ⊆ K) (φ : 𝓓^{n}(Ω, F)) :
    toSupportedInCLM 𝕜 hΩ'K (monoCLM ℝ φ) =
      toSupportedInCLM 𝕜 ((SetLike.coe_subset_coe.2 hΩΩ').trans hΩ'K) φ := by
  ext x
  simp [hΩΩ']

end ToSupportedIn

end TestFunction
