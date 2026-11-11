/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Wkp.Exponent
public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.ContMDiffSection

/-!
# Lowering the integrability exponent of Sobolev sections

Let `A` be a finite bundle atlas of a real vector bundle `V → M` over a manifold modelled on a
finite-dimensional real inner product space `E`, with Haar measure `μ` on `E`. Every chart image
`A.image i` has compact closure, so it has finite measure
(`TauCeti.FiniteBundleAtlas.isFiniteMeasure_restrict_image`), and the scalar inclusions
`TauCeti.Wkp.ofExponentLEL` apply to every component of an element of `W^{k,q}(V)`. Applied
componentwise they give the continuous linear inclusion `W^{k,q}(V) → W^{k,p}(V)` for
`1 ≤ p ≤ q ≤ ∞`. It does not change the chart data, so it keeps the underlying section, is
injective, commutes with forgetting the highest derivative, and sends the Sobolev section of
exponent `q` of a `Cᵏ` section to its Sobolev section of exponent `p`.

## Main definitions

* `TauCeti.SobolevSection.ofExponentLEL`: the continuous inclusion `W^{k,q}(V) → W^{k,p}(V)`.

## Main results

* `TauCeti.SobolevSection.chartValueL_ofExponentLEL_ae`: the chart data are unchanged.
* `TauCeti.SobolevSection.ofExponentLEL_injective`: the inclusion is injective.
* `TauCeti.SobolevSection.lowerOrderL_ofExponentLEL`: compatibility with `lowerOrderL`.
* `TauCeti.SobolevSection.ofExponentLEL_ofContMDiffSection`: compatibility with the Sobolev
  sections of `Cᵏ` sections.
-/

public section

noncomputable section

open Bundle MeasureTheory Module Set TopologicalSpace
open scoped Manifold ContDiff ENNReal

universe u

namespace TauCeti

open FiniteBundleAtlas

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)]
  [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)] [FiberBundle F V] [VectorBundle ℝ F V]
  (A : FiniteBundleAtlas E M F V) (μ : Measure E) [μ.IsAddHaarMeasure]
  {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] (k : ℕ)

omit [FiniteDimensional ℝ F] [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [VectorBundle ℝ F V] in
/-- The image of a chart of a finite bundle atlas has finite Haar measure, since its closure is
compact. -/
instance FiniteBundleAtlas.isFiniteMeasure_restrict_image (i : Fin A.n) :
    IsFiniteMeasure (μ.restrict (A.image i)) :=
  isFiniteMeasure_restrict.2
    ((measure_mono subset_closure).trans_lt (A.isCompact_closure_image i).measure_lt_top).ne

omit [FiniteDimensional ℝ F] in
/-- The image of chart `i` in the chart data of a finite bundle atlas has finite Haar measure. -/
instance FiniteBundleAtlas.isFiniteMeasure_restrict_sectionChartData_image
    (i : Fin A.sectionChartData.n) :
    IsFiniteMeasure (μ.restrict (A.sectionChartData.image i)) :=
  A.isFiniteMeasure_restrict_image μ i

omit [FiniteDimensional ℝ F] in
/-- The image of chart `i` in the chart data of a finite bundle atlas has finite Haar measure, for
`i` indexed by the charts of the atlas. Instance search does not identify `Fin A.n` with
`Fin A.sectionChartData.n`, so this is a separate instance. -/
instance FiniteBundleAtlas.isFiniteMeasure_restrict_sectionChartData_image' (i : Fin A.n) :
    IsFiniteMeasure (μ.restrict (A.sectionChartData.image i)) :=
  A.isFiniteMeasure_restrict_image μ i

namespace SobolevSection

/-- **Lowering the exponent.** For `p ≤ q`, the continuous inclusion `W^{k,q}(V) → W^{k,p}(V)`
applying `TauCeti.Wkp.ofExponentLEL` to every chartwise component. -/
def ofExponentLEL (hpq : p ≤ q) : SobolevSection A μ q k →L[ℝ] SobolevSection A μ p k :=
  ((ContinuousLinearMap.piMap fun _ ↦ ContinuousLinearMap.piMap fun _ ↦
    Wkp.ofExponentLEL hpq k).comp (A.sectionChartData.sobolevSections μ q k).subtypeL).codRestrict
      (A.sectionChartData.sobolevSections μ p k) fun w ↦ by
      obtain ⟨s, hs⟩ := A.sectionChartData.exists_section μ q k w
      exact (A.sectionChartData.mem_sobolevSections_iff μ p k).2 ⟨s, fun i ↦
        A.sectionChartData.chartValueL_ae_eq_coord μ p k fun j ↦
        (Wkp.value_ofExponentLEL_ae hpq k _).trans
          ((A.sectionChartData.chartValueL_ae_eq_coord_iff μ q k).1 (hs i) j)⟩

variable {A μ k}

/-- The components of `ofExponentLEL hpq w` are the components of `w` with lowered exponent. -/
@[simp]
theorem ofExponentLEL_apply (hpq : p ≤ q) (w : SobolevSection A μ q k) (i : Fin A.n)
    (j : Fin (finrank ℝ F)) :
    (ofExponentLEL A μ k hpq w : A.sectionChartData.SobolevData μ p k) i j =
      Wkp.ofExponentLEL hpq k ((w : A.sectionChartData.SobolevData μ q k) i j) :=
  (rfl)

/-- Lowering the exponent does not change the chart data. -/
theorem chartValueL_ofExponentLEL_ae (hpq : p ≤ q) (w : SobolevSection A μ q k) (i : Fin A.n) :
    ⇑(A.sectionChartData.chartValueL μ p k i (ofExponentLEL A μ k hpq w)) =ᵐ[μ.restrict (A.image i)]
      A.sectionChartData.chartValueL μ q k i w := by
  filter_upwards [A.sectionChartData.chartValueL_apply_ae μ p k i (ofExponentLEL A μ k hpq w),
    A.sectionChartData.chartValueL_apply_ae μ q k i w,
    ae_all_iff.2 fun j ↦
      Wkp.value_ofExponentLEL_ae hpq k ((w : A.sectionChartData.SobolevData μ q k) i j)]
    with y hp hq hj
  rw [hp, hq]
  exact Finset.sum_congr rfl fun j _ ↦ by rw [ofExponentLEL_apply, hj j]

/-- Lowering the exponent keeps the underlying section: if the chart data of `w` are the
coordinates of `s`, so are those of `ofExponentLEL hpq w`. -/
theorem chartValueL_ofExponentLEL_ae_coord (hpq : p ≤ q) {w : SobolevSection A μ q k}
    {s : ∀ x, V x} {i : Fin A.n}
    (hs : A.sectionChartData.chartValueL μ q k i w =ᵐ[μ.restrict (A.image i)] A.coord i s) :
    A.sectionChartData.chartValueL μ p k i (ofExponentLEL A μ k hpq w)
      =ᵐ[μ.restrict (A.image i)] A.coord i s :=
  (chartValueL_ofExponentLEL_ae hpq w i).trans hs

/-- Lowering the exponent is injective. -/
theorem ofExponentLEL_injective (hpq : p ≤ q) :
    Function.Injective (ofExponentLEL A μ k hpq) := fun w w' h ↦
  Subtype.ext <| funext fun (i : Fin A.n) ↦ funext fun j ↦
    Wkp.ofExponentLEL_injective hpq k <| by
      rw [← ofExponentLEL_apply, ← ofExponentLEL_apply, h]

/-- Lowering the exponent commutes with forgetting the highest derivative. -/
theorem lowerOrderL_ofExponentLEL (hpq : p ≤ q) (w : SobolevSection A μ q (k + 1)) :
    A.sectionChartData.lowerOrderL μ p k (ofExponentLEL A μ (k + 1) hpq w) =
      ofExponentLEL A μ k hpq (A.sectionChartData.lowerOrderL μ q k w) :=
  Subtype.ext <| funext fun (i : Fin A.n) ↦ funext fun j ↦ by
    erw [SectionChartData.lowerOrderL_apply, ofExponentLEL_apply, ofExponentLEL_apply,
      SectionChartData.lowerOrderL_apply, Wkp.lowerOrder_ofExponentLEL]

variable [IsManifold 𝓘(ℝ, E) k M] [ContMDiffVectorBundle k F V 𝓘(ℝ, E)]

/-- Lowering the exponent sends the Sobolev section of exponent `q` of a `Cᵏ` section to its
Sobolev section of exponent `p`. -/
@[simp]
theorem ofExponentLEL_ofContMDiffSection (hpq : p ≤ q) (s : Cₛ^k⟮𝓘(ℝ, E); F, V⟯) :
    ofExponentLEL A μ k hpq (ofContMDiffSection A μ q k s) = ofContMDiffSection A μ p k s :=
  eq_of_ae_eq_coord (s := s)
    (fun i ↦ chartValueL_ofExponentLEL_ae_coord hpq
      (chartValueL_ofContMDiffSection_ae A μ q k s i))
    (fun i ↦ chartValueL_ofContMDiffSection_ae A μ p k s i)

end SobolevSection

end TauCeti
