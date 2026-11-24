/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.TestFunction
public import TauCeti.Topology.Algebra.Module.FiniteDimension

/-!
# Basic facts about test functions

A test function on `Ω` supported in an open set `Ω' ≤ Ω` is the extension by zero
(`TestFunction.monoCLM`) of a test function on `Ω'`.

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

* `TestFunction.exists_monoCLM_eq_of_tsupport_subset`: a test function supported in a smaller
  open set is the extension by zero of a test function on that set.
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
* `TestFunction.compOfIsClosedEmbedding`: the pullback of a test function along a smooth closed
  embedding, with its support bound and linearity, and `TestFunction.lineTestFunction`: its
  restriction `t ↦ ψ (y + t • e)` to an affine line, the pullback along the closed embedding
  `isClosedEmbedding_add_smul_left`.
-/

public section

namespace TestFunction

open TopologicalSpace ContinuousLinearMap Topology
open scoped Distributions BoundedContinuousFunction

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {Ω : Opens E}
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {n : ℕ∞}

/-- A test function is zero as a bounded continuous function exactly when it is zero. -/
@[simp]
theorem toBoundedContinuousFunction_eq_zero (φ : 𝓓^{n}(Ω, F)) :
    (φ : E →ᵇ F) = 0 ↔ φ = 0 := by
  simpa only [map_zero, toBoundedContinuousFunctionCLM_apply] using
    ((injective_toBoundedContinuousFunctionCLM ℝ).eq_iff (a := φ) (b := 0))

/-- A test function on `Ω` supported in an open set `Ω' ≤ Ω` is the extension by zero of a test
function on `Ω'`. -/
theorem exists_monoCLM_eq_of_tsupport_subset {Ω' : Opens E} (h : Ω' ≤ Ω) {φ : 𝓓^{n}(Ω, F)}
    (hφ : tsupport φ ⊆ Ω') : ∃ ψ : 𝓓^{n}(Ω', F), monoCLM ℝ ψ = φ :=
  ⟨⟨φ, φ.contDiff, φ.hasCompactSupport, hφ⟩, TestFunction.ext fun x ↦ by simp [h]⟩

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

/-- The pullback `ψ ∘ f` of a test function on `Ω` along a `C^n` closed embedding `f : D → E`,
as a test function on the open set `f ⁻¹' Ω`. -/
noncomputable def compOfIsClosedEmbedding {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    (ψ : 𝓓^{n}(Ω, F)) {f : D → E} (hf : ContDiff ℝ n f) (hfe : IsClosedEmbedding f) :
    𝓓^{n}(Opens.comap ⟨f, hfe.continuous⟩ Ω, F) :=
  ⟨fun x => ψ (f x), ψ.contDiff.comp hf, ψ.hasCompactSupport.comp_isClosedEmbedding hfe,
    (tsupport_comp_subset_preimage (ψ : E → F) hfe.continuous).trans
      fun _ hx => ψ.tsupport_subset hx⟩

/-- Evaluating the pullback of a test function along a closed embedding. -/
@[simp]
theorem compOfIsClosedEmbedding_apply {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    (ψ : 𝓓^{n}(Ω, F)) {f : D → E} (hf : ContDiff ℝ n f) (hfe : IsClosedEmbedding f) (x : D) :
    ψ.compOfIsClosedEmbedding hf hfe x = ψ (f x) :=
  (rfl)

/-- The support of the pullback of `ψ` along `f` lies in the preimage of the support of `ψ`. -/
theorem tsupport_compOfIsClosedEmbedding_subset {D : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] (ψ : 𝓓^{n}(Ω, F)) {f : D → E} (hf : ContDiff ℝ n f)
    (hfe : IsClosedEmbedding f) :
    tsupport (ψ.compOfIsClosedEmbedding hf hfe) ⊆ f ⁻¹' tsupport ψ :=
  tsupport_comp_subset_preimage (ψ : E → F) hfe.continuous

/-- The pullback along the identity is the test function itself; the open sets agree
definitionally (`Opens.comap_id`). -/
@[simp]
theorem compOfIsClosedEmbedding_id (ψ : 𝓓^{n}(Ω, F)) :
    ψ.compOfIsClosedEmbedding contDiff_id IsClosedEmbedding.id = ψ :=
  (rfl)

/-- Pulling back along `f` and then along `g` is pulling back along `f ∘ g`; the open sets agree
definitionally (`Opens.comap_comp`). -/
theorem compOfIsClosedEmbedding_compOfIsClosedEmbedding {D D' : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] [NormedAddCommGroup D'] [NormedSpace ℝ D'] (ψ : 𝓓^{n}(Ω, F)) {f : D → E}
    (hf : ContDiff ℝ n f) (hfe : IsClosedEmbedding f) {g : D' → D} (hg : ContDiff ℝ n g)
    (hge : IsClosedEmbedding g) :
    (ψ.compOfIsClosedEmbedding hf hfe).compOfIsClosedEmbedding hg hge =
      ψ.compOfIsClosedEmbedding (hf.comp hg) (hfe.comp hge) :=
  (rfl)

/-- The pullback of the zero test function is zero. -/
@[simp]
theorem compOfIsClosedEmbedding_zero {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    {f : D → E} (hf : ContDiff ℝ n f) (hfe : IsClosedEmbedding f) :
    (0 : 𝓓^{n}(Ω, F)).compOfIsClosedEmbedding hf hfe = 0 := by
  ext x
  simp

/-- The pullback along a closed embedding is additive. -/
@[simp]
theorem compOfIsClosedEmbedding_add {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    (ψ ψ' : 𝓓^{n}(Ω, F)) {f : D → E} (hf : ContDiff ℝ n f) (hfe : IsClosedEmbedding f) :
    (ψ + ψ').compOfIsClosedEmbedding hf hfe =
      ψ.compOfIsClosedEmbedding hf hfe + ψ'.compOfIsClosedEmbedding hf hfe := by
  ext x
  simp

/-- The pullback along a closed embedding commutes with real scalar multiplication. -/
@[simp]
theorem compOfIsClosedEmbedding_smul {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    (c : ℝ) (ψ : 𝓓^{n}(Ω, F)) {f : D → E} (hf : ContDiff ℝ n f) (hfe : IsClosedEmbedding f) :
    (c • ψ).compOfIsClosedEmbedding hf hfe = c • ψ.compOfIsClosedEmbedding hf hfe := by
  ext x
  simp

/-- The restriction `t ↦ ψ (y + t • e)` of a test function on `Ω` to the line through `y` in a
nonzero direction `e`, as a test function on the open set of parameters of the line lying in
`Ω`: the pullback along the closed embedding `t ↦ y + t • e`. -/
noncomputable def lineTestFunction (ψ : 𝓓^{n}(Ω, F)) (y e : E) (he : e ≠ 0) :
    𝓓^{n}(Opens.comap ⟨fun t : ℝ => y + t • e,
      (isClosedEmbedding_add_smul_left y he).continuous⟩ Ω, F) :=
  ψ.compOfIsClosedEmbedding (contDiff_const.add (contDiff_id.smul contDiff_const))
    (isClosedEmbedding_add_smul_left y he)

/-- Evaluating the restriction of a test function to a line. -/
@[simp]
theorem lineTestFunction_apply (ψ : 𝓓^{n}(Ω, F)) (y e : E) (he : e ≠ 0) (t : ℝ) :
    ψ.lineTestFunction y e he t = ψ (y + t • e) :=
  (rfl)

/-- The support of the restriction of `ψ` to a line lies in the parameters `t` with
`y + t • e ∈ tsupport ψ`. -/
theorem tsupport_lineTestFunction_subset (ψ : 𝓓^{n}(Ω, F)) (y e : E) (he : e ≠ 0) :
    tsupport (ψ.lineTestFunction y e he) ⊆ (fun t : ℝ => y + t • e) ⁻¹' tsupport ψ :=
  ψ.tsupport_compOfIsClosedEmbedding_subset _ _

/-- Restricting the zero test function to a line gives zero. -/
@[simp]
theorem lineTestFunction_zero (y e : E) (he : e ≠ 0) :
    (0 : 𝓓^{n}(Ω, F)).lineTestFunction y e he = 0 :=
  compOfIsClosedEmbedding_zero _ _

/-- Restriction to a line is additive. -/
@[simp]
theorem lineTestFunction_add (ψ ψ' : 𝓓^{n}(Ω, F)) (y e : E) (he : e ≠ 0) :
    (ψ + ψ').lineTestFunction y e he = ψ.lineTestFunction y e he + ψ'.lineTestFunction y e he :=
  compOfIsClosedEmbedding_add _ _ _ _

/-- Restriction to a line commutes with real scalar multiplication. -/
@[simp]
theorem lineTestFunction_smul (c : ℝ) (ψ : 𝓓^{n}(Ω, F)) (y e : E) (he : e ≠ 0) :
    (c • ψ).lineTestFunction y e he = c • ψ.lineTestFunction y e he :=
  compOfIsClosedEmbedding_smul _ _ _ _

end TestFunction
