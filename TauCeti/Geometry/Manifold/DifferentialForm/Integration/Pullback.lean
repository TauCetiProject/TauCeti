/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.OrientationLift
public import Mathlib.Analysis.Convex.Measure

/-!
# Chart integral comparison with ordinary manifold pullback

The coordinate expression uses derivatives within the model range. Ordinary pullback uses the
unrestricted manifold derivative, and the two can differ at boundary points. The model range is
convex, so its frontier is Haar-null. They agree almost everywhere on every preferred-chart
target, giving the actual integral and integrability comparison required by chart integration.
-/

public section

noncomputable section

open Set MeasureTheory
open scoped Manifold Topology

namespace TauCeti.RoughForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] {k : ℕ}

omit [FiniteDimensional ℝ E] in
private theorem measurableSet_chartTarget (α : M) : MeasurableSet (extChartAt I α).target := by
  rw [extChartAt_target]
  exact ((chartAt H α).open_target.preimage I.continuous_symm).measurableSet.inter
    I.isClosed_range.measurableSet

/-- The within-range chart expression equals ordinary pullback almost everywhere on the target.
No pointwise equality is claimed on the model boundary. -/
theorem inChartAt_ae_eq_mpullback (φ : RoughForm I M ℝ k) (α : M)
    (μ : Measure E) [μ.IsAddHaarMeasure] :
    ∀ᵐ y ∂μ.restrict (extChartAt I α).target,
      φ.inChartAt α y = mpullback 𝓘(ℝ, E) I (extChartAt I α).symm φ y := by
  have ht := measurableSet_chartTarget (I := I) α
  have hb : ∀ᵐ y ∂μ, y ∉ frontier (range I) :=
    measure_eq_zero_iff_ae_notMem.mp (I.convex_range.addHaar_frontier μ)
  filter_upwards [ae_restrict_mem ht, ae_restrict_of_ae hb] with y hy hboundary
  have hI : y ∈ interior (range I) := by
    by_contra hn
    exact hboundary ⟨subset_closure (extChartAt_target_subset_range α hy), hn⟩
  have hd := mfderivWithin_of_mem_nhds (I := 𝓘(ℝ, E)) (I' := I)
    (f := (extChartAt I α).symm) (mem_interior_iff_mem_nhds.mp hI)
  ext v
  have he := congrArg (fun L : TangentSpace 𝓘(ℝ, E) y →L[ℝ]
    TangentSpace I ((extChartAt I α).symm y) ↦
      φ ((extChartAt I α).symm y) (fun i ↦ L (v i))) hd
  exact (inChartAt_apply φ α y v).trans (he.trans
    (mpullback_apply (I := 𝓘(ℝ, E)) (I' := I) (extChartAt I α).symm φ y v).symm)

end TauCeti.RoughForm

namespace Manifold.OrientationLift

open TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  {k : ℕ}

/-- The actual source-signed coefficient agrees almost everywhere with the characteristic
ordinary-pullback coefficient. The possible difference on model-boundary points is Haar-null. -/
theorem signedInChartAt_ae_eq_mpullback (l : OrientationLift I M (Fin k))
    (φ : TauCeti.RoughForm I M ℝ k) (b : Module.Basis (Fin k) ℝ E) (α : M)
    (μ : Measure E) [μ.IsAddHaarMeasure] :
    ∀ᵐ y ∂μ.restrict (extChartAt I α).target,
      φ.signedInChartAt b α (l.sign α) y =
        (l.signAt α ((extChartAt I α).symm y) : ℝ) *
          mpullback 𝓘(ℝ, E) I (extChartAt I α).symm φ y b := by
  filter_upwards [φ.inChartAt_ae_eq_mpullback α μ,
    ae_restrict_mem (TauCeti.RoughForm.measurableSet_chartTarget (I := I) α)] with y he hy
  have he' := congrArg (fun L : E [⋀^Fin k]→L[ℝ] ℝ ↦ L b) he
  have hs := l.signAt_of_mem ((extChartAt I α).map_target hy)
  calc
    φ.signedInChartAt b α (l.sign α) y =
        (l.sign α ⟨(extChartAt I α).symm y, (extChartAt I α).map_target hy⟩ : ℝ) *
          φ.inChartAt α y b :=
      (φ.signedInChartAt_apply b α (l.sign α) y).trans (dite_eq_left hy)
    _ = (l.signAt α ((extChartAt I α).symm y) : ℝ) * φ.inChartAt α y b :=
      (congrArg (fun u : ℤˣ ↦ (u : ℝ) * φ.inChartAt α y b) hs).symm
    _ = _ := congrArg (fun r : ℝ ↦ (l.signAt α ((extChartAt I α).symm y) : ℝ) * r) he'

/-- The chart functional equals the ordinary-pullback target integral, with a relative basis
sign. The characteristic formula also covers negative model orientation in dimension zero. -/
theorem chartIntegral_eq_integral_mpullback (l : OrientationLift I M (Fin k))
    (φ : TauCeti.RoughForm I M ℝ k) (b : Module.Basis (Fin k) ℝ E) (α : M) :
    l.chartIntegral φ α = (_root_.Orientation.signBasis l.modelOrientation b : ℝ) *
      ∫ y in (extChartAt I α).target,
        (l.signAt α ((extChartAt I α).symm y) : ℝ) *
          mpullback 𝓘(ℝ, E) I (extChartAt I α).symm φ y b ∂b.addHaar := by
  have ht : (∫ y in (extChartAt I α).target, φ.signedInChartAt b α (l.sign α) y ∂b.addHaar) =
      ∫ y, φ.signedInChartAt b α (l.sign α) y ∂b.addHaar :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy ↦ by
      rw [TauCeti.RoughForm.signedInChartAt_apply, dite_eq_right hy]
  rw [chartIntegral_eq_integral l φ b α, ← ht]
  congr 1
  exact integral_congr_ae (l.signedInChartAt_ae_eq_mpullback φ b α b.addHaar)

/-- Genuine integrability of the signed chart coefficient is equivalent to integrability of
the ordinary-pullback coefficient on the target, with both integrability statements retained. -/
theorem integrable_signedInChartAt_iff_mpullback (l : OrientationLift I M (Fin k))
    (φ : TauCeti.RoughForm I M ℝ k) (b : Module.Basis (Fin k) ℝ E) (α : M)
    (μ : Measure E) [μ.IsAddHaarMeasure] :
    Integrable (φ.signedInChartAt b α (l.sign α)) μ ↔
      IntegrableOn (fun y ↦ (l.signAt α ((extChartAt I α).symm y) : ℝ) *
        mpullback 𝓘(ℝ, E) I (extChartAt I α).symm φ y b) (extChartAt I α).target μ := by
  have hs : Function.support (φ.signedInChartAt b α (l.sign α)) ⊆ (extChartAt I α).target := by
    intro y hy
    by_contra hn
    exact Function.mem_support.mp hy (by
      rw [TauCeti.RoughForm.signedInChartAt_apply, dite_eq_right hn])
  rw [← integrableOn_iff_integrable_of_support_subset hs]
  exact integrable_congr (l.signedInChartAt_ae_eq_mpullback φ b α μ)

end Manifold.OrientationLift
