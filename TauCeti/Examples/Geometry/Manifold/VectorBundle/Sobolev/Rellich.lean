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

-- Loss one stays in the all-loss simp normal form until explicitly rewritten.
example (w : C.sobolevSections μ p (k + 1)) (i : Fin C.n) (j : Fin (Module.finrank ℝ F)) :
    Wkp.value k ((C.lowerOrdersL μ p k 1 w : C.SobolevData μ p k) i j) =
      Wkp.value (k + 1) ((w : C.SobolevData μ p (k + 1)) i j) := by
  simp

example (d : ℕ) (w : C.sobolevSections μ p ((k + d) + 1)) :
    C.lowerOrdersL μ p k d (C.lowerOrdersL μ p (k + d) 1 w) =
      C.lowerOrdersL μ p k (d + 1) ((Nat.add_assoc k d 1) ▸ w) := by
  simp

example (d : ℕ) (w : C.sobolevSections μ p ((k + 1) + d)) :
    C.lowerOrdersL μ p k 1 (C.lowerOrdersL μ p (k + 1) d w) =
      C.lowerOrdersL μ p k (1 + d) ((Nat.add_assoc k 1 d) ▸ w) := by
  simp

example (d e : ℕ) (w : C.sobolevSections μ p ((k + d) + e)) (i : Fin C.n) :
    C.chartValueL μ p k i (C.lowerOrdersL μ p k d (C.lowerOrdersL μ p (k + d) e w)) =
      C.chartValueL μ p ((k + d) + e) i w := by
  simp

example {a b : ℕ} (h : a = b) (w : C.sobolevSections μ p a) (i : Fin C.n) :
    C.chartValueL μ p b i (h ▸ w : C.sobolevSections μ p b) = C.chartValueL μ p a i w := by
  simp

example (d e : ℕ) (w : C.sobolevSections μ p ((k + d) + e))
    (i : Fin C.n) (j : Fin (Module.finrank ℝ F)) :
    Wkp.value k
        ((C.lowerOrdersL μ p k d (C.lowerOrdersL μ p (k + d) e w) : C.SobolevData μ p k) i j) =
      Wkp.value ((k + d) + e) ((w : C.SobolevData μ p ((k + d) + e)) i j) := by
  simp

-- The removed one-step constant-map law is an explicit specialization of the all-loss law.
example {L : F →L[ℝ] F} {Ψ : S → S}
    (hΨ : ∀ i s, ∀ y ∈ C.image i, C.coord i (Ψ s) y = L (C.coord i s y))
    (w : C.sobolevSections μ p (k + 1)) :
    C.lowerOrderL μ p k (C.constMapL μ p (k + 1) L Ψ hΨ w) =
      C.constMapL μ p k L Ψ hΨ (C.lowerOrderL μ p k w) := by
  simpa only [C.lowerOrdersL_one μ p k] using C.lowerOrdersL_constMapL μ p k 1 hΨ w

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

-- The removed one-step exponent law uses the all-loss API on the original native bundle.
example {q : ℝ≥0∞} [Fact (1 ≤ q)] (hpq : p ≤ q)
    (w : SobolevSection A μ q (k + 1)) :
    A.sectionChartData.lowerOrderL μ p k (A.sectionChartData.ofExponentLEL μ (k + 1) hpq w) =
      A.sectionChartData.ofExponentLEL μ k hpq (A.sectionChartData.lowerOrderL μ q k w) := by
  simpa only [SectionChartData.lowerOrdersL_one] using
    SectionChartData.lowerOrdersL_ofExponentLEL (C := A.sectionChartData)
      (μ := μ) (k := k) 1 hpq w

example :
    IsCompactOperator ((A.sectionChartData.lowerOrdersL μ p k (d + 1)).comp
      (A.sectionChartData.ofExponentLEL (p := p) (q := ∞) μ (k + (d + 1)) le_top)) := by
  exact SobolevSection.isCompactOperator_lowerOrdersL_comp_ofExponentLEL A μ p k le_top d

-- Arbitrary order bounds recover an actual compact inclusion with the chart formula.
example (l n : ℕ) (hln : l < n) :
    ∃ K : SobolevSection A μ ∞ n →L[ℝ] SobolevSection A μ p l,
      IsCompactOperator K ∧ ∀ w i,
        A.sectionChartData.chartValueL μ p l i (K w) =
          Lp.ofExponentLEL ℝ F (p := p) (q := ∞) le_top
            (A.sectionChartData.chartValueL μ ∞ n i w) := by
  obtain ⟨e, he⟩ := Nat.exists_eq_add_of_le (Nat.succ_le_of_lt hln)
  have hn : n = l + (e + 1) := by omega
  clear he
  subst n
  let K : SobolevSection A μ ∞ (l + (e + 1)) →L[ℝ] SobolevSection A μ p l :=
    (A.sectionChartData.lowerOrdersL μ p l (e + 1)).comp
      (A.sectionChartData.ofExponentLEL (p := p) (q := ∞) μ (l + (e + 1)) le_top)
  have hK : IsCompactOperator K :=
    SobolevSection.isCompactOperator_lowerOrdersL_comp_ofExponentLEL A μ p l le_top e
  refine ⟨K, hK, ?_⟩
  intro w i
  simp only [K, ContinuousLinearMap.comp_apply, SectionChartData.chartValueL_lowerOrdersL,
    SectionChartData.chartValueL_ofExponentLEL]

example {ε : ℝ} (hε : 0 < ε) :
    ∃ C, 0 ≤ C ∧ ∀ w : SobolevSection A μ p (k + (d + 1)),
      ‖A.sectionChartData.lowerOrdersL μ p k (d + 1) w‖ ≤
        ε * ‖w‖ + C * ‖A.sectionChartData.chartValuesL μ p (k + (d + 1)) w‖ :=
  SobolevSection.exists_norm_lowerOrdersL_le A μ p k d hε

end NativeBundle

attribute [local instance] ChartedSpace.empty

/-- An actual finite atlas of a trivial normed bundle over the empty complex manifold. -/
private def emptyAtlas (F : Type*) [NormedAddCommGroup F] :
    FiniteBundleAtlas ℂ Empty F (Trivial Empty F) :=
  Classical.choice (FiniteBundleAtlas.nonempty (E := ℂ) (M := Empty) (F := F)
    (V := Trivial Empty F))

/-- An actual finite atlas of a trivial complex bundle with zero-dimensional fibre. -/
private def zeroFiberAtlas (M : Type*) [TopologicalSpace M] [ChartedSpace ℂ M] [CompactSpace M]
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

-- Mathlib's existing exponent fact supplies the infinite-exponent carriers.
example :
    ∀ w : zeroOneSobolevSections A μ ∞ k, zeroOneLowerOrdersL A μ ∞ k 0 w = w := by
  exact fun w ↦ zeroOneLowerOrdersL_zero w

example :
    ∀ w : SobolevSection (A.tangentHom 𝓘(ℝ, ℂ)) μ ∞ (k + d),
      zeroOneLowerOrdersL A μ ∞ k d (zeroOnePartSobolevL A μ ∞ (k + d) w) =
        zeroOnePartSobolevL A μ ∞ k
          ((A.tangentHom 𝓘(ℝ, ℂ)).sectionChartData.lowerOrdersL μ ∞ k d w) := by
  exact fun w ↦ zeroOneLowerOrdersL_zeroOnePartSobolevL d w

-- At loss one, the inclusion forgets the highest derivative.
example (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (w : zeroOneSobolevSections A μ p (k + 1)) :
    (zeroOneLowerOrdersL A μ p k 1 w : SobolevSection (A.tangentHom 𝓘(ℝ, ℂ)) μ p k) =
      (A.tangentHom 𝓘(ℝ, ℂ)).sectionChartData.lowerOrderL μ p k w := by
  rw [coe_zeroOneLowerOrdersL, (A.tangentHom 𝓘(ℝ, ℂ)).sectionChartData.lowerOrdersL_one μ p k]

-- Both orders of one-step composition are instances of native transitivity.
example (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (w : zeroOneSobolevSections A μ p ((k + d) + 1)) :
    zeroOneLowerOrdersL A μ p k d (zeroOneLowerOrdersL A μ p (k + d) 1 w) =
      zeroOneLowerOrdersL A μ p k (d + 1) ((Nat.add_assoc k d 1) ▸ w) :=
  zeroOneLowerOrdersL_zeroOneLowerOrdersL d 1 w

example (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (w : zeroOneSobolevSections A μ p ((k + 1) + d)) :
    zeroOneLowerOrdersL A μ p k 1 (zeroOneLowerOrdersL A μ p (k + 1) d w) =
      zeroOneLowerOrdersL A μ p k (1 + d) ((Nat.add_assoc k 1 d) ▸ w) :=
  zeroOneLowerOrdersL_zeroOneLowerOrdersL 1 d w

-- The same one-step inclusion commutes with the actual native projection.
example (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (w : SobolevSection (A.tangentHom 𝓘(ℝ, ℂ)) μ p (k + 1)) :
    zeroOneLowerOrdersL A μ p k 1 (zeroOnePartSobolevL A μ p (k + 1) w) =
      zeroOnePartSobolevL A μ p k
        ((A.tangentHom 𝓘(ℝ, ℂ)).sectionChartData.lowerOrderL μ p k w) := by
  simpa only [(A.tangentHom 𝓘(ℝ, ℂ)).sectionChartData.lowerOrdersL_one μ p k] using
    zeroOneLowerOrdersL_zeroOnePartSobolevL (A := A) (μ := μ) (p := p) (k := k) 1 w

example (p : ℝ≥0∞) [Fact (1 ≤ p)] [T2Space M]
    [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, ℂ)] :
    IsCompactOperator (zeroOneLowerOrdersL A μ p k 1) :=
  isCompactOperator_zeroOneLowerOrdersL A μ p k 0

end NativeZeroOne

example {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ) ∞ M]
    [CompactSpace M] [T2Space M] (μ : Measure ℂ) [μ.IsAddHaarMeasure]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (k d : ℕ) :
    Function.Injective (zeroOneLowerOrdersL (zeroFiberAtlas M) μ p k d) :=
  zeroOneLowerOrdersL_injective d

/-- The actual empty base admits a finite atlas whose native order inclusions vanish. -/
theorem exists_emptyAtlas_zeroOneLowerOrdersL_eq_zero
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (k d : ℕ) :
    ∃ A : FiniteBundleAtlas ℂ Empty ℂ (Trivial Empty ℂ),
      ∀ w : zeroOneSobolevSections A volume p (k + d),
        zeroOneLowerOrdersL A volume p k d w = 0 := by
  refine ⟨emptyAtlas ℂ, fun w ↦ ?_⟩
  apply Subtype.ext
  apply SectionChartData.eq_of_chartValueL_ae_eq
  intro i
  exact (((emptyAtlas ℂ).tangentHom 𝓘(ℝ, ℂ)).center i).elim

end TauCeti.Examples.RellichOrders
