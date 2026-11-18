/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.Exponent

/-!
# Lowering the order of Sobolev sections

Let `C` be chart data for the sections of a vector bundle with model fibre `F`, read on open
subsets of a finite-dimensional real inner product space `E` with Haar measure `μ`. For orders
`l ≤ k` the continuous inclusion `W^{k,p} → W^{l,p}` of Sobolev sections forgets the derivatives of
every component above order `l`. It is the composite of the `k - l` one-step inclusions
`TauCeti.SectionChartData.lowerOrderL`, defined by recursion on `l ≤ k` with `Nat.leRec`. It keeps
the chart data, so it is injective, it is transitive, and it commutes with lowering the
integrability exponent and with the Sobolev sections of `Cᵏ` sections.

## Main definitions

* `TauCeti.SectionChartData.ofOrderLEL`: the continuous inclusion `W^{k,p} → W^{l,p}` of Sobolev
  sections for `l ≤ k`.

## Main results

* `TauCeti.SectionChartData.ofOrderLEL_self`, `TauCeti.SectionChartData.ofOrderLEL_lowerOrderL`,
  `TauCeti.SectionChartData.lowerOrderL_ofOrderLEL`,
  `TauCeti.SectionChartData.ofOrderLEL_ofOrderLEL`: the identity at `l = k`, compatibility with the
  one-step inclusions, and transitivity.
* `TauCeti.SectionChartData.ofOrderLEL_succ`: the one-step case is
  `TauCeti.SectionChartData.lowerOrderL`.
* `TauCeti.SectionChartData.chartValueL_ofOrderLEL`, `TauCeti.SectionChartData.value_ofOrderLEL`:
  the chart data and the `Lᵖ` values of the components do not change.
* `TauCeti.SectionChartData.ofOrderLEL_constMapL`: compatibility with constant fibre maps.
* `TauCeti.SectionChartData.ofOrderLEL_injective`: the inclusion is injective.
* `TauCeti.SectionChartData.ofOrderLEL_ofExponentLEL`: compatibility with lowering the exponent.
* `TauCeti.SobolevSection.ofOrderLEL_ofContMDiffSection`: compatibility with the Sobolev sections
  of `Cᵏ` sections.
-/

public section

noncomputable section

open Bundle MeasureTheory Module Set TopologicalSpace
open scoped Manifold ContDiff ENNReal

universe u

namespace TauCeti

namespace SectionChartData

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {S : Type*} [AddCommGroup S] [Module ℝ S]
  (C : SectionChartData E F S) (μ : Measure E) [μ.IsAddHaarMeasure]
  (p : ℝ≥0∞) [Fact (1 ≤ p)] {l m k : ℕ}

/-- **Lowering the order.** For `l ≤ k`, the continuous inclusion of the Sobolev sections of order
`k` into those of order `l`, forgetting the derivatives of every component above order `l`: the
composite of the one-step inclusions `TauCeti.SectionChartData.lowerOrderL`. -/
def ofOrderLEL (h : l ≤ k) : C.sobolevSections μ p k →L[ℝ] C.sobolevSections μ p l :=
  Nat.leRec (motive := fun k _ ↦ C.sobolevSections μ p k →L[ℝ] C.sobolevSections μ p l)
    (ContinuousLinearMap.id ℝ _) (fun k _ T ↦ T.comp (C.lowerOrderL μ p k)) h

variable {C μ p}

/-- Lowering the order from `l` to itself is the identity. -/
@[simp]
theorem ofOrderLEL_self (w : C.sobolevSections μ p l) : C.ofOrderLEL μ p le_rfl w = w := by
  rw [ofOrderLEL, Nat.leRec_self, ContinuousLinearMap.id_apply]

/-- Lowering the order from `k + 1` to `l` first forgets the highest derivative. -/
theorem ofOrderLEL_lowerOrderL (h : l ≤ k) (w : C.sobolevSections μ p (k + 1)) :
    C.ofOrderLEL μ p h (C.lowerOrderL μ p k w) = C.ofOrderLEL μ p (h.trans k.le_succ) w := by
  rw [ofOrderLEL, ofOrderLEL, Nat.leRec_succ _ _ h, ContinuousLinearMap.comp_apply]

/-- Lowering the order by one step is the one-step inclusion
`TauCeti.SectionChartData.lowerOrderL`. -/
theorem ofOrderLEL_succ : C.ofOrderLEL μ p k.le_succ = C.lowerOrderL μ p k :=
  ContinuousLinearMap.ext fun w ↦ by rw [← ofOrderLEL_lowerOrderL le_rfl, ofOrderLEL_self]

/-- Lowering the order from `k` to `l + 1` and then forgetting the highest derivative is lowering
the order from `k` to `l`. -/
theorem lowerOrderL_ofOrderLEL (h : l + 1 ≤ k) (w : C.sobolevSections μ p k) :
    C.lowerOrderL μ p l (C.ofOrderLEL μ p h w) = C.ofOrderLEL μ p (l.le_succ.trans h) w := by
  induction k, h using Nat.le_induction with
  | base => rw [ofOrderLEL_self, ofOrderLEL_succ]
  | succ k hk ih =>
    rw [← ofOrderLEL_lowerOrderL hk, ih, ofOrderLEL_lowerOrderL]

/-- Order inclusions compose transitively. -/
@[simp]
theorem ofOrderLEL_ofOrderLEL (hlm : l ≤ m) (hmk : m ≤ k) (w : C.sobolevSections μ p k) :
    C.ofOrderLEL μ p hlm (C.ofOrderLEL μ p hmk w) = C.ofOrderLEL μ p (hlm.trans hmk) w := by
  induction k, hmk using Nat.le_induction with
  | base => rw [ofOrderLEL_self]
  | succ k hk ih =>
    rw [← ofOrderLEL_lowerOrderL hk, ih, ofOrderLEL_lowerOrderL]

/-- Lowering the order does not change the `Lᵖ` values of the components. -/
@[simp]
theorem value_ofOrderLEL (h : l ≤ k) (w : C.sobolevSections μ p k) (i : Fin C.n)
    (j : Fin (finrank ℝ F)) :
    Wkp.value l ((C.ofOrderLEL μ p h w : C.SobolevData μ p l) i j) =
      Wkp.value k ((w : C.SobolevData μ p k) i j) := by
  induction k, h using Nat.le_induction with
  | base => rw [ofOrderLEL_self]
  | succ k hk ih =>
    rw [← ofOrderLEL_lowerOrderL hk, ih, lowerOrderL_apply, Wkp.value_succ]

/-- Lowering the order does not change the chart data. -/
@[simp]
theorem chartValueL_ofOrderLEL (h : l ≤ k) (w : C.sobolevSections μ p k) (i : Fin C.n) :
    C.chartValueL μ p l i (C.ofOrderLEL μ p h w) = C.chartValueL μ p k i w := by
  induction k, h using Nat.le_induction with
  | base => rw [ofOrderLEL_self]
  | succ k hk ih =>
    rw [← ofOrderLEL_lowerOrderL hk, ih, chartValueL_coe_lowerOrderL]

/-- Lowering the order is injective. -/
theorem ofOrderLEL_injective (h : l ≤ k) : Function.Injective (C.ofOrderLEL μ p h) :=
  fun w w' hw ↦ eq_of_chartValueL_ae_eq fun i ↦ .of_eq <| by
    rw [← chartValueL_ofOrderLEL h, hw, chartValueL_ofOrderLEL]

/-- Lowering the order commutes with fibrewise maps given in every chart by a constant linear map
of the model fibre. -/
theorem ofOrderLEL_constMapL {L : F →L[ℝ] F} {Ψ : S → S}
    (hΨ : ∀ i s, ∀ y ∈ C.image i, C.coord i (Ψ s) y = L (C.coord i s y)) (h : l ≤ k)
    (w : C.sobolevSections μ p k) :
    C.ofOrderLEL μ p h (constMapL μ p k L Ψ hΨ w) =
      constMapL μ p l L Ψ hΨ (C.ofOrderLEL μ p h w) := by
  induction k, h using Nat.le_induction with
  | base => simp only [ofOrderLEL_self]
  | succ k hk ih =>
    rw [← ofOrderLEL_lowerOrderL hk, lowerOrderL_constMapL, ih, ofOrderLEL_lowerOrderL]

/-- Lowering the order commutes with lowering the exponent. -/
theorem ofOrderLEL_ofExponentLEL [∀ i, IsFiniteMeasure (μ.restrict (C.image i : Set E))]
    {q : ℝ≥0∞} [Fact (1 ≤ q)] (hpq : p ≤ q) (h : l ≤ k) (w : C.sobolevSections μ q k) :
    C.ofOrderLEL μ p h (C.ofExponentLEL μ k hpq w) =
      C.ofExponentLEL μ l hpq (C.ofOrderLEL μ q h w) :=
  eq_of_chartValueL_ae_eq fun i ↦ .of_eq <| by
    rw [chartValueL_ofOrderLEL, chartValueL_ofExponentLEL, chartValueL_ofExponentLEL,
      chartValueL_ofOrderLEL]

end SectionChartData

namespace SobolevSection

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)]
  [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)] [FiberBundle F V] [VectorBundle ℝ F V]
  {A : FiniteBundleAtlas E M F V} {μ : Measure E} [μ.IsAddHaarMeasure]
  {p : ℝ≥0∞} [Fact (1 ≤ p)] {l k : ℕ}
  [IsManifold 𝓘(ℝ, E) k M] [ContMDiffVectorBundle k F V 𝓘(ℝ, E)]
  [IsManifold 𝓘(ℝ, E) l M] [ContMDiffVectorBundle l F V 𝓘(ℝ, E)]

/-- Lowering the order sends the Sobolev section of order `k` of a `Cᵏ` section to its Sobolev
section of order `l`. -/
theorem ofOrderLEL_ofContMDiffSection (h : l ≤ k) (s : Cₛ^k⟮𝓘(ℝ, E); F, V⟯) :
    A.sectionChartData.ofOrderLEL μ p h (ofContMDiffSection A μ p k s) =
      ofContMDiffSection A μ p l ⟨s, s.contMDiff.of_le (by exact_mod_cast h)⟩ :=
  eq_of_ae_eq_coord (s := s)
    (fun i ↦ by
      rw [SectionChartData.chartValueL_ofOrderLEL]
      exact chartValueL_ofContMDiffSection_ae A μ p k s i)
    (fun i ↦ chartValueL_ofContMDiffSection_ae A μ p l _ i)

end SobolevSection

end TauCeti
