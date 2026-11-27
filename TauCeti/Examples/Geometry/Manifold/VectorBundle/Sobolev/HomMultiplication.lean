/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.HomMultiplication
public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.ContMDiffSection
public import Mathlib.Geometry.Manifold.VectorBundle.Hom
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# Conjugation as a compact rough bundle multiplier

For a finite atlas of the trivial complex line bundle over a closed surface, conjugation is an
actual order-zero Sobolev section of the real hom bundle. Its action conjugates the chart
readings. At coefficient exponent `p = 3` it is compact for `q = 3`, `q = 2`, `q = 3/2` and `q = 1`.
It is nonzero on a nonempty base and cannot be replaced by a complex-linear fibre map.
-/

public section
noncomputable section

open Bundle Filter MeasureTheory Module Set TopologicalSpace
open scoped Manifold ContDiff ENNReal NNReal

namespace TauCeti.HomMultiplicationExamples

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]

private def conjSection :
    Cₛ^0⟮𝓘(ℝ, ℂ); ℂ →L[ℝ] ℂ, fun x ↦ Trivial M ℂ x →L[ℝ] Trivial M ℂ x⟯ :=
  ⟨fun _ ↦ Complex.conjCLE.toContinuousLinearMap, by
    apply contMDiff_zero_iff.2
    apply continuous_iff_continuousAt.2
    intro x
    apply (continuousAt_hom_bundle (RingHom.id ℝ) _).2
    refine ⟨continuousAt_id, ?_⟩
    simpa only [ContinuousLinearMap.inCoordinates, Trivial.fiberBundle_trivializationAt',
      Trivial.continuousLinearMapAt_trivialization, Trivial.symmL_trivialization,
      ContinuousLinearMap.id_comp, ContinuousLinearMap.comp_id] using
        (continuousAt_const (y := Complex.conjCLE.toContinuousLinearMap))⟩

private theorem conjSection_apply (x : M) :
    conjSection x = Complex.conjCLE.toContinuousLinearMap := by
  unfold conjSection
  exact congrFun (ContMDiffSection.coeFn_mk _ _) x

variable [T2Space M] [IsManifold 𝓘(ℝ, ℂ) ∞ M]
  (A : FiniteBundleAtlas ℂ M ℂ (Trivial M ℂ)) (μ : Measure ℂ) [μ.IsAddHaarMeasure]

/-- Conjugation as a native order-zero Sobolev coefficient in the bundle of real homomorphisms.
-/
def conjCoeff (p : ℝ≥0) [Fact (1 ≤ (p : ℝ≥0∞))] :
    SobolevSection (A.hom (𝕜 := ℝ) A.closure_dom_subset_baseSet) μ p 0 :=
  SobolevSection.ofContMDiffSection (A.hom (𝕜 := ℝ) A.closure_dom_subset_baseSet) μ p 0
    conjSection

omit [T2Space M] in
/-- The conjugation coefficient reads as the actual real-linear conjugation map in each chart. -/
theorem chartValueL_conjCoeff_ae (p : ℝ≥0) [Fact (1 ≤ (p : ℝ≥0∞))] (i : Fin A.n) :
    (A.hom (𝕜 := ℝ) A.closure_dom_subset_baseSet).sectionChartData.chartValueL μ p 0 i
        (conjCoeff A μ p) =ᵐ[μ.restrict (A.image i)] fun _ ↦ (Complex.conjCLE : ℂ →L[ℝ] ℂ) := by
  have h := SobolevSection.chartValueL_ofContMDiffSection_ae
    (A.hom (𝕜 := ℝ) A.closure_dom_subset_baseSet) μ p 0 conjSection i
  rw [FiniteBundleAtlas.image_hom] at h
  rw [conjCoeff]
  refine h.trans (Filter.Eventually.of_forall fun y ↦ ?_)
  rw [FiniteBundleAtlas.coord_hom]
  simp only [ContinuousLinearMap.inCoordinates, Trivial.fiberBundle_trivializationAt',
    Trivial.continuousLinearMapAt_trivialization, Trivial.symmL_trivialization,
    ContinuousLinearMap.id_comp, ContinuousLinearMap.comp_id]
  exact conjSection_apply _

omit [T2Space M] in
/-- The native coefficient is nonzero on a nonempty surface. -/
theorem conjCoeff_ne_zero [Nonempty M] (p : ℝ≥0) [Fact (1 ≤ (p : ℝ≥0∞))] :
    conjCoeff A μ p ≠ 0 := by
  intro h
  rw [conjCoeff] at h
  have hz := map_zero (SobolevSection.ofContMDiffSection
    (A.hom (𝕜 := ℝ) A.closure_dom_subset_baseSet) μ p 0)
  have hs : (conjSection (M := M)) = 0 :=
    SobolevSection.ofContMDiffSection_injective
      (A.hom (𝕜 := ℝ) A.closure_dom_subset_baseSet) μ p 0 (h.trans hz.symm)
  have h1 := congrArg (fun s ↦ s (Classical.arbitrary M) (1 : ℂ)) hs
  simp [conjSection_apply] at h1

/-- No complex-linear map has the values of the real conjugation coefficient. -/
theorem conj_not_complex_linear :
    ¬ ∃ T : ℂ →L[ℂ] ℂ, ∀ z, T z = Complex.conjCLE z := by
  rintro ⟨T, hT⟩
  have h : Complex.conjCLE Complex.I = Complex.I := by
    calc
      _ = T Complex.I := (hT _).symm
      _ = Complex.I • T 1 := by simpa using T.map_smul Complex.I (1 : ℂ)
      _ = Complex.I := by rw [hT]; simp
  have him := congrArg Complex.im h
  norm_num at him

/-- The actual native multiplier conjugates the chart readings of every input section. -/
theorem chartValueL_homMulL_conjCoeff_ae {p q : ℝ≥0}
    [Fact (1 ≤ (p : ℝ≥0∞))] [Fact (1 ≤ (q : ℝ≥0∞))]
    (hp : (finrank ℝ ℂ : ℝ≥0) < p) (hqp : q ≤ p)
    (ξ : SobolevSection A μ q 1) (j : Fin A.n) :
    (A.ofBaseSet A.closure_dom_subset_baseSet).sectionChartData.chartValueL μ q 0 j
        (SobolevSection.homMulL A A.closure_dom_subset_baseSet μ hp hqp (conjCoeff A μ p) ξ)
      =ᵐ[μ.restrict (A.image j)] fun y ↦
        Complex.conjCLE (A.sectionChartData.chartValueL μ q 1 j ξ y) := by
  have hT := SobolevSection.chartValueL_homMulL_ae A A.closure_dom_subset_baseSet μ hp hqp
    (conjCoeff A μ p) ξ j
  rw [FiniteBundleAtlas.image_ofBaseSet] at hT
  filter_upwards [hT, chartValueL_conjCoeff_ae A μ p j] with y hT hα
  rw [hT, hα]
  simp only [ContinuousLinearEquiv.coe_coe]

private theorem finrank_lt_three : (finrank ℝ ℂ : ℝ≥0) < 3 := by
  norm_num

local instance : Fact (1 ≤ ((3 : ℝ≥0) : ℝ≥0∞)) := ⟨by norm_num⟩
local instance : Fact (1 ≤ ((2 : ℝ≥0) : ℝ≥0∞)) := ⟨by norm_num⟩
local instance : Fact (1 ≤ ((3 / 2 : ℝ≥0) : ℝ≥0∞)) :=
  ⟨ENNReal.coe_le_coe.2
    (by exact_mod_cast (by norm_num : (1 : ℝ) ≤ 3 / 2) : (1 : ℝ≥0) ≤ 3 / 2)⟩
local instance : Fact (1 ≤ ((1 : ℝ≥0) : ℝ≥0∞)) := ⟨le_rfl⟩

-- The equal-exponent endpoint uses the actual conjugation coefficient.
example : IsCompactOperator (SobolevSection.homMulL A A.closure_dom_subset_baseSet μ
    finrank_lt_three le_rfl (conjCoeff A μ 3)) :=
  SobolevSection.isCompactOperator_homMulL A A.closure_dom_subset_baseSet μ
    (q := 3) finrank_lt_three le_rfl _

-- The critical surface exponent remains included.
example : IsCompactOperator (SobolevSection.homMulL A A.closure_dom_subset_baseSet μ (q := 2)
    finrank_lt_three (by norm_num) (conjCoeff A μ 3)) :=
  SobolevSection.isCompactOperator_homMulL A A.closure_dom_subset_baseSet μ
    (q := 2) finrank_lt_three (by norm_num) _

-- A genuinely subcritical exponent.
example : IsCompactOperator (SobolevSection.homMulL A A.closure_dom_subset_baseSet μ
    (q := (3 / 2 : ℝ≥0)) finrank_lt_three
    (by exact_mod_cast (by norm_num : (3 / 2 : ℝ) ≤ 3)) (conjCoeff A μ 3)) :=
  SobolevSection.isCompactOperator_homMulL A A.closure_dom_subset_baseSet μ
    (q := (3 / 2 : ℝ≥0)) finrank_lt_three
    (by exact_mod_cast (by norm_num : (3 / 2 : ℝ) ≤ 3)) _

-- The natural extra endpoint follows from the same native construction.
example : IsCompactOperator (SobolevSection.homMulL A A.closure_dom_subset_baseSet μ (q := 1)
    finrank_lt_three (by norm_num) (conjCoeff A μ 3)) :=
  SobolevSection.isCompactOperator_homMulL A A.closure_dom_subset_baseSet μ
    (q := 1) finrank_lt_three (by norm_num) _

section ZeroRankChecks

open SobolevSection

variable {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace ℝ F₁] [FiniteDimensional ℝ F₁]
  {V₁ : M → Type*} [TopologicalSpace (TotalSpace F₁ V₁)] [∀ x, AddCommGroup (V₁ x)]
  [∀ x, Module ℝ (V₁ x)] [∀ x, TopologicalSpace (V₁ x)] [FiberBundle F₁ V₁]
  [VectorBundle ℝ F₁ V₁]
  {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace ℝ F₂] [FiniteDimensional ℝ F₂]
  {V₂ : M → Type*} [TopologicalSpace (TotalSpace F₂ V₂)] [∀ x, AddCommGroup (V₂ x)]
  [∀ x, Module ℝ (V₂ x)] [∀ x, TopologicalSpace (V₂ x)] [FiberBundle F₂ V₂]
  [VectorBundle ℝ F₂ V₂] [∀ x, IsTopologicalAddGroup (V₂ x)] [∀ x, ContinuousSMul ℝ (V₂ x)]
  [ContMDiffVectorBundle ∞ F₂ V₂ 𝓘(ℝ, ℂ)]
  (B : FiniteBundleAtlas ℂ M F₁ V₁)
  (h : ∀ i, closure (B.dom i) ⊆ (trivializationAt F₂ V₂ (B.center i)).baseSet)
  {p q : ℝ≥0} [Fact (1 ≤ (p : ℝ≥0∞))] [Fact (1 ≤ (q : ℝ≥0∞))]

-- A zero-rank source gives the zero action, without excluding the native input carrier.
example [Subsingleton F₁] (hp : 2 < p) (hqp : q ≤ p)
    (α : SobolevSection (B.hom (𝕜 := ℝ) h) μ p 0) (ξ : SobolevSection B μ q 1) :
    homMulL B h μ (by simpa using hp) hqp α ξ = 0 := by
  have hξ : ξ = 0 := by
    apply Subtype.ext
    funext i m
    exact (Nat.not_lt_zero _ (m.isLt.trans_le
      (le_of_eq (Module.finrank_zero_of_subsingleton (R := ℝ) (M := F₁))))).elim
  rw [hξ, map_zero]

example [Subsingleton F₂] (hp : 2 < p) (hqp : q ≤ p)
    (α : SobolevSection (B.hom (𝕜 := ℝ) h) μ p 0) (ξ : SobolevSection B μ q 1) :
    homMulL B h μ (by simpa using hp) hqp α ξ = 0 := by
  apply Subtype.ext
  funext i m
  exact (Nat.not_lt_zero _ (m.isLt.trans_le
    (le_of_eq (Module.finrank_zero_of_subsingleton (R := ℝ) (M := F₂))))).elim

-- Linearity in the actual rough coefficient is over the reals.
example (hp : 2 < p) (hqp : q ≤ p)
    (α β : SobolevSection (B.hom (𝕜 := ℝ) h) μ p 0) (ξ : SobolevSection B μ q 1) :
    homMulL B h μ (by simpa using hp) hqp (α + β) ξ =
      homMulL B h μ (by simpa using hp) hqp α ξ + homMulL B h μ (by simpa using hp) hqp β ξ := by
  exact congrArg (fun T ↦ T ξ) (map_add (homMulL B h μ (by simpa using hp) hqp) α β)

-- The bilinear bound controls both native inputs with one constant.
example (hp : 2 < p) (hqp : q ≤ p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (α : SobolevSection (B.hom (𝕜 := ℝ) h) μ p 0)
      (ξ : SobolevSection B μ q 1), ‖homMulL B h μ (by simpa using hp) hqp α ξ‖ ≤
        C * ‖α‖ * ‖ξ‖ :=
  exists_norm_homMulL_apply_le B h μ (by simpa using hp) hqp

end ZeroRankChecks

end TauCeti.HomMultiplicationExamples
