/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Density.Integral
import TauCeti.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.Disjointed

/-!
# Direct integration of zero-dimensional densities

On a zero-dimensional charted manifold, every tangent space is trivial, charts are locally
constant, and the normalized Haar measure of the empty basis is a Dirac mass. A rough `0`-density
is therefore integrable iff its support is finite (`TauCeti.integrableDensity_zeroDim_iff`), and
its integral is unconditionally the finite sum `∑ᶠ x : M, μ x 0`
(`TauCeti.integralDensity_zeroDim`), with specializations to singleton support and finite
manifolds.
-/

public section

noncomputable section

open MeasureTheory Set Module
open scoped Manifold

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Subsingleton E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]

/-- On a zero-dimensional manifold, a rough density is integrable iff its support is finite. -/
theorem integrableDensity_zeroDim_iff (μ : RoughDensity I M 0) :
    IntegrableDensity μ ↔ {x | μ x ≠ 0}.Finite := by
  have : DiscreteTopology M := I.discreteTopology M
  let : MeasurableSpace E := borel E
  have : BorelSpace E := ⟨rfl⟩
  rw [integrableDensity_iff]
  unfold _root_.tsupport
  rw [closure_discrete, isCompact_iff_finite]
  exact ⟨fun h ↦ h.1, fun hfin ↦ ⟨hfin, ⟨Basis.empty E⟩, fun _ _ ↦ by
    rw [Basis.addHaar_eq_dirac]
    exact integrable_dirac (by simp)⟩⟩

/-- On a zero-dimensional charted manifold, `integralDensity μ = ∑ᶠ x : M, μ x 0` unconditionally,
with no orientation signs or smoothness hypothesis. -/
theorem integralDensity_zeroDim (μ : RoughDensity I M 0) :
    integralDensity μ = ∑ᶠ x : M, μ x 0 := by
  classical
  have hsupp_eq : Function.support (fun x : M ↦ μ x 0) = {x | μ x ≠ 0} := Set.ext fun x ↦
    not_congr ⟨fun h ↦ by
      dsimp only at h
      ext v
      rw [Subsingleton.elim v 0, h, Density.zero_apply],
      fun h ↦ by dsimp only; rw [h, Density.zero_apply]⟩
  by_cases hfin : {x | μ x ≠ 0}.Finite
  swap
  · rw [integralDensity_eq_zero_of_not_integrable (mt (integrableDensity_zeroDim_iff μ).mp hfin),
      finsum_of_infinite_support (by rwa [hsupp_eq])]
  have : DiscreteTopology M := I.discreteTopology M
  have : IsManifold I 1 M := isManifold_of_contDiffOn I 1 M fun _ _ _ _ ↦
    contDiffOn_const (c := (0 : E)).congr fun _ _ ↦ Subsingleton.elim _ _
  let : MeasurableSpace E := borel E
  have : BorelSpace E := ⟨rfl⟩
  let b : Basis (Fin 0) ℝ E := Basis.empty E
  let s := hfin.toFinset
  let e := s.equivFin
  let α (i : Fin s.card) : M := e.symm i
  have hdisj : Pairwise fun i j ↦ Disjoint ({α i} : Set M) {α j} := fun _ _ hij ↦
    disjoint_singleton.mpr fun h ↦ hij (e.symm.injective (Subtype.ext h))
  rw [integralDensity_eq_sum_disjointed_chart_integrals
      ((integrableDensity_zeroDim_iff μ).mpr hfin) b α (fun i ↦ {α i})
      (fun i ↦ (extChartAt_source_zeroDim (I := I) (α i) ▸
        isOpen_extChartAt_source (α i)).isChartMeasurable)
      (fun i ↦ (extChartAt_source_zeroDim (I := I) (α i)).ge)
      (fun x hx ↦ mem_iUnion.mpr ⟨e ⟨x, hfin.mem_toFinset.mpr hx⟩, by simp [α]⟩)]
  have hterm (i : Fin s.card) : (∫ y in (extChartAt I (α i)) '' disjointed (fun j ↦ {α j}) i,
      μ.inChartAt b (α i) y ∂b.addHaar) = μ (α i) 0 := by
    rw [disjointed_eq_self fun j hj ↦ hdisj hj.ne, image_singleton,
      b.setIntegral_addHaar_of_subsingleton _ (singleton_nonempty _) (extChartAt I (α i) (α i)),
      μ.inChartAt_self]
    exact congrArg (μ (α i)) (Subsingleton.elim _ 0)
  simp_rw [hterm]
  rw [finsum_eq_sum_of_support_subset (f := fun x : M ↦ μ x 0) (s := s)
    (hsupp_eq ▸ hfin.coe_toFinset.ge)]
  exact (Fintype.sum_equiv e.symm (fun i ↦ μ (α i) 0) (fun x : s ↦ μ x.val 0) fun _ ↦ rfl).trans
    (Finset.sum_attach s fun x ↦ μ x 0)

/-- On a zero-dimensional charted manifold, any rough density supported in `{x}` is integrable. -/
theorem integrableDensity_zeroDim_singleton (μ : RoughDensity I M 0) (x : M)
    (hs : _root_.tsupport (α := Density E 0) μ ⊆ {x}) : IntegrableDensity μ :=
  (integrableDensity_zeroDim_iff μ).mpr
    ((finite_singleton x).subset fun _ hy ↦ hs (_root_.subset_tsupport (α := Density E 0) μ hy))

/-- On a zero-dimensional manifold, a rough density supported in `{x}` integrates to `μ x 0`. -/
theorem integralDensity_zeroDim_singleton (μ : RoughDensity I M 0) (x : M)
    (hs : _root_.tsupport (α := Density E 0) μ ⊆ {x}) : integralDensity μ = μ x 0 := by
  rw [integralDensity_zeroDim, finsum_eq_single _ x]
  intro y hy
  have h0 : μ y = 0 := _root_.image_eq_zero_of_notMem_tsupport (α := Density E 0) fun h ↦ hy (hs h)
  rw [h0, Density.zero_apply]

/-- On a finite zero-dimensional charted manifold, `integralDensity μ = ∑ x : M, μ x 0`. -/
theorem integralDensity_finite_zeroDim [Fintype M] (μ : RoughDensity I M 0) :
    integralDensity μ = ∑ x : M, μ x 0 := by
  rw [integralDensity_zeroDim, finsum_eq_sum_of_fintype]

end TauCeti
