/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.Rellich.ZeroOneForm

/-!
# Native clients of Sobolev order inclusions

These clients use the canonical bundled order maps, their pointwise one-step law,
Rellich with an infinite source exponent, Ehrling's inequality, and native `(0,1)` projections.
The finite atlases for the empty base and zero-dimensional complex fibre are constructed by
`FiniteBundleAtlas.nonempty`.
-/

public noncomputable section

open Bundle MeasureTheory Set
open scoped Manifold ContDiff ENNReal TauCeti.ComplexManifold

namespace TauCeti.Examples.RellichOrders

section ChartData
variable {E F S : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [AddCommGroup S] [Module ℝ S] (C : SectionChartData E F S)
  (μ : Measure E) [μ.IsAddHaarMeasure] (p : ℝ≥0∞) [Fact (1 ≤ p)] (k : ℕ)

-- Evaluation of the bundled one-step law gives the pointwise inclusion.
example (w : C.sobolevSections μ p (k + 1)) :
    C.lowerOrdersL μ p k 1 w = C.lowerOrderL μ p k w :=
  congrArg (fun T ↦ T w) (C.lowerOrdersL_one μ p k)

example (w : C.sobolevSections μ p k) : C.lowerOrdersL μ p k 0 w = w :=
  C.lowerOrdersL_zero μ p k w

end ChartData

section NativeBundle
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, E)]
  (A : FiniteBundleAtlas E M F V) (μ : Measure E) [μ.IsAddHaarMeasure]
  (p : ℝ≥0∞) [Fact (1 ≤ p)] (k d : ℕ)

example (hp : p ≠ ⊤) :
    let : Fact (1 ≤ (∞ : ℝ≥0∞)) := ⟨le_top⟩
    IsCompactOperator ((A.sectionChartData.lowerOrdersL μ p k (d + 1)).comp
      (A.sectionChartData.ofExponentLEL (p := p) (q := ∞) μ (k + (d + 1)) le_top)) := by
  let : Fact (1 ≤ (∞ : ℝ≥0∞)) := ⟨le_top⟩
  exact SobolevSection.isCompactOperator_lowerOrdersL_comp_ofExponentLEL A μ p k hp le_top d

-- Arbitrary order bounds recover an actual compact inclusion with the chart formula.
example (hp : p ≠ ⊤) (l n : ℕ) (hln : l < n) :
    let : Fact (1 ≤ (∞ : ℝ≥0∞)) := ⟨le_top⟩
    ∃ K : SobolevSection A μ ∞ n →L[ℝ] SobolevSection A μ p l,
      IsCompactOperator K ∧ ∀ w i,
        A.sectionChartData.chartValueL μ p l i (K w) =
          Lp.ofExponentLEL ℝ F (p := p) (q := ∞) le_top
            (A.sectionChartData.chartValueL μ ∞ n i w) := by
  let : Fact (1 ≤ (∞ : ℝ≥0∞)) := ⟨le_top⟩
  obtain ⟨e, he⟩ := Nat.exists_eq_add_of_le (Nat.succ_le_of_lt hln)
  have hn : n = l + (e + 1) := by omega
  clear he
  subst n
  let K : SobolevSection A μ ∞ (l + (e + 1)) →L[ℝ] SobolevSection A μ p l :=
    (A.sectionChartData.lowerOrdersL μ p l (e + 1)).comp
      (A.sectionChartData.ofExponentLEL (p := p) (q := ∞) μ (l + (e + 1)) le_top)
  have hK : IsCompactOperator K :=
    SobolevSection.isCompactOperator_lowerOrdersL_comp_ofExponentLEL A μ p l hp le_top e
  refine ⟨K, hK, ?_⟩
  intro w i
  simp only [K, ContinuousLinearMap.comp_apply, SectionChartData.chartValueL_lowerOrdersL,
    SectionChartData.chartValueL_ofExponentLEL]

example (hp : p ≠ ⊤) {ε : ℝ} (hε : 0 < ε) :
    ∃ C, 0 ≤ C ∧ ∀ w : SobolevSection A μ p (k + (d + 1)),
      ‖A.sectionChartData.lowerOrdersL μ p k (d + 1) w‖ ≤
        ε * ‖w‖ + C * ‖A.sectionChartData.chartValuesL μ p (k + (d + 1)) w‖ :=
  SobolevSection.exists_norm_lowerOrdersL_le A μ p k hp d hε

end NativeBundle

attribute [local instance] ChartedSpace.empty

/-- An actual finite atlas of a trivial normed bundle over the empty complex manifold. -/
def emptyAtlas (F : Type*) [NormedAddCommGroup F] :
    FiniteBundleAtlas ℂ Empty F (Trivial Empty F) :=
  Classical.choice (FiniteBundleAtlas.nonempty (E := ℂ) (M := Empty) (F := F)
    (V := Trivial Empty F))

/-- An actual finite atlas of a trivial complex bundle with zero-dimensional fibre. -/
def zeroFibreAtlas (M : Type*) [TopologicalSpace M] [ChartedSpace ℂ M] [CompactSpace M]
    [T2Space M] : FiniteBundleAtlas ℂ M (Fin 0 → ℂ) (Trivial M (Fin 0 → ℂ)) :=
  Classical.choice (FiniteBundleAtlas.nonempty (E := ℂ) (M := M) (F := Fin 0 → ℂ)
    (V := Trivial M (Fin 0 → ℂ)))

attribute [local instance] instVectorBundleRealZeroOneForm

section NativeZeroOne
variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ) ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F]
  [IsScalarTower ℝ ℂ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [∀ x, Module ℂ (V x)]
  [∀ x, IsScalarTower ℝ ℂ (V x)] [∀ x, TopologicalSpace (V x)]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle ℂ F V]
  (A : FiniteBundleAtlas ℂ M F V) (μ : Measure ℂ) [μ.IsAddHaarMeasure] (k d : ℕ)

-- The true exponent facts form the native endpoint carriers.
example :
    let : Fact (1 ≤ (∞ : ℝ≥0∞)) := ⟨le_top⟩
    ∀ w : zeroOneSobolevSections A μ ∞ k, zeroOneLowerOrdersL A μ ∞ k 0 w = w := by
  let : Fact (1 ≤ (∞ : ℝ≥0∞)) := ⟨le_top⟩
  exact fun w ↦ zeroOneLowerOrdersL_zero w

example :
    let : Fact (1 ≤ (∞ : ℝ≥0∞)) := ⟨le_top⟩
    ∀ w : SobolevSection A.tangentHom μ ∞ (k + d),
      zeroOneLowerOrdersL A μ ∞ k d (zeroOnePartSobolevL A μ ∞ (k + d) w) =
        zeroOnePartSobolevL A μ ∞ k (A.tangentHom.sectionChartData.lowerOrdersL μ ∞ k d w) := by
  let : Fact (1 ≤ (∞ : ℝ≥0∞)) := ⟨le_top⟩
  exact fun w ↦ zeroOneLowerOrdersL_zeroOnePartSobolevL d w

end NativeZeroOne

example {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ) ∞ M]
    [CompactSpace M] [T2Space M] (μ : Measure ℂ) [μ.IsAddHaarMeasure]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (k d : ℕ) :
    Function.Injective (zeroOneLowerOrdersL (zeroFibreAtlas M) μ p k d) :=
  zeroOneLowerOrdersL_injective d

example (p : ℝ≥0∞) [Fact (1 ≤ p)] (k d : ℕ)
    (w : zeroOneSobolevSections (emptyAtlas ℂ) volume p (k + d)) :
    zeroOneLowerOrdersL (emptyAtlas ℂ) volume p k d w = 0 := by
  apply Subtype.ext
  apply (emptyAtlas ℂ).tangentHom.sectionChartData.chartValuesL_injective volume p k
  funext i
  exact ((emptyAtlas ℂ).tangentHom.center i).elim

end TauCeti.Examples.RellichOrders
