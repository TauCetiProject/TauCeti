/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.ExtChartAt
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Function.Jacobian
import TauCeti.Geometry.Manifold.MFDeriv.Chart.Basic

/-!
# Set integrals over coordinate images of chart pieces

A finite family of chart-measurable sets is disjointed into pieces. An integral over the coordinate
image of a chart-measurable subset of a chart source splits along these pieces
(`TauCeti.setIntegral_image_extChartAt_eq_sum_disjointed`), and two finite chart-measurable covers
of a set give the same sum of chart integrals for chart coefficients that agree on chart overlaps
(`TauCeti.sum_setIntegral_image_extChartAt_disjointed_eq`). This is the cover-independence step
in the integration of top forms and of densities. Chart coefficients related by the absolute
Jacobian of the transition map have equal integrals over the two coordinate images of a subset
of a chart overlap (`TauCeti.setIntegral_image_extChartAt_changeChart`). Only the model carries a
measurable structure.
-/

public section

open MeasureTheory Set
open scoped Manifold

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]

/-- An integral over the coordinate image of a chart-measurable subset `u` of a chart source
splits along the disjointed pieces of a finite chart-measurable family `v`, when the integrand
vanishes at the coordinates of the points of `u` outside that family. -/
theorem setIntegral_image_extChartAt_eq_sum_disjointed [MeasurableSpace E]
    {ν : Measure E} {f : E → ℝ} (α : M) {u : Set M} (hf : IntegrableOn f ((extChartAt I α) '' u) ν)
    (hu : IsChartMeasurable I u) (hus : u ⊆ (extChartAt I α).source) {n : ℕ}
    {v : Fin n → Set M} (hv : ∀ j, IsChartMeasurable I (v j))
    (hz : ∀ x ∈ u, x ∉ ⋃ j, v j → f (extChartAt I α x) = 0) :
    (∫ y in (extChartAt I α) '' u, f y ∂ν) =
      ∑ j, ∫ y in (extChartAt I α) '' (u ∩ disjointed v j), f y ∂ν := by
  let e := extChartAt I α
  let w : Fin n → Set E := fun j ↦ e '' (u ∩ disjointed v j)
  have hw (j : Fin n) : MeasurableSet (w j) :=
    (hu.inter (IsChartMeasurable.disjointed hv j)).image_extChartAt α
      (inter_subset_left.trans hus)
  have hws : (⋃ j, w j) ⊆ e '' u := iUnion_subset fun _ ↦ image_mono inter_subset_left
  have hdisj : Pairwise (fun i j ↦ Disjoint (w i) (w j)) := fun i j hij ↦
    ((disjoint_disjointed v hij).mono inter_subset_right inter_subset_right).image e.injOn
      (inter_subset_left.trans hus) (inter_subset_left.trans hus)
  have hw0 : ∀ y ∈ e '' u \ ⋃ j, w j, f y = 0 := by
    rintro y ⟨⟨x, hx, rfl⟩, hn⟩
    refine hz x hx fun hxv ↦ hn ?_
    rw [← iUnion_disjointed] at hxv
    obtain ⟨j, hj⟩ := mem_iUnion.mp hxv
    exact mem_iUnion.mpr ⟨j, mem_image_of_mem e ⟨hx, hj⟩⟩
  exact (setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (hu.image_extChartAt α hus) hws
    hw0).trans (integral_iUnion_fintype hw hdisj fun _ ↦ hf.mono_set (image_mono inter_subset_left))

/-- Two finite chart-measurable covers of a set `S` give the same sum of chart integrals over
their disjointed pieces, for chart coefficients `f α` that are integrable, vanish at the
coordinates of points outside `S`, and have equal integrals over the coordinate images of
chart-measurable subsets of chart overlaps. Each coefficient need only be integrable on the
coordinate images of the disjointed pieces of its own cover. -/
theorem sum_setIntegral_image_extChartAt_disjointed_eq [MeasurableSpace E]
    {ν : Measure E} {f : M → E → ℝ} {S : Set M}
    (hz : ∀ α, ∀ x ∈ (extChartAt I α).source, x ∉ S → f α (extChartAt I α x) = 0)
    (hchange : ∀ (α β : M) (s : Set M), s ⊆ (extChartAt I α).source ∩ (extChartAt I β).source →
      IsChartMeasurable I s →
        (∫ y in (extChartAt I α) '' s, f α y ∂ν) = ∫ y in (extChartAt I β) '' s, f β y ∂ν)
    {n n' : ℕ} (α : Fin n → M) (u : Fin n → Set M) (hu : ∀ i, IsChartMeasurable I (u i))
    (hus : ∀ i, u i ⊆ (extChartAt I (α i)).source) (hc : S ⊆ ⋃ i, u i)
    (hfu : ∀ i, IntegrableOn (f (α i)) ((extChartAt I (α i)) '' disjointed u i) ν)
    (β : Fin n' → M) (v : Fin n' → Set M) (hv : ∀ j, IsChartMeasurable I (v j))
    (hvs : ∀ j, v j ⊆ (extChartAt I (β j)).source) (hd : S ⊆ ⋃ j, v j)
    (hfv : ∀ j, IntegrableOn (f (β j)) ((extChartAt I (β j)) '' disjointed v j) ν) :
    ∑ i, (∫ y in (extChartAt I (α i)) '' disjointed u i, f (α i) y ∂ν) =
      ∑ j, ∫ y in (extChartAt I (β j)) '' disjointed v j, f (β j) y ∂ν := by
  have hsplit (γ : M) {w : Set M} (hw : IsChartMeasurable I w)
      (hwγ : w ⊆ (extChartAt I γ).source) (hfw : IntegrableOn (f γ) ((extChartAt I γ) '' w) ν)
      {k : ℕ} {t : Fin k → Set M}
      (ht : ∀ j, IsChartMeasurable I (t j)) (hS : S ⊆ ⋃ j, t j) :
      (∫ y in (extChartAt I γ) '' w, f γ y ∂ν) =
        ∑ j, ∫ y in (extChartAt I γ) '' (w ∩ disjointed t j), f γ y ∂ν :=
    setIntegral_image_extChartAt_eq_sum_disjointed γ hfw hw hwγ ht
      fun x hx hn ↦ hz γ x (hwγ hx) fun hxS ↦ hn (hS hxS)
  have hpu (i : Fin n) : disjointed u i ⊆ (extChartAt I (α i)).source :=
    (disjointed_subset u i).trans (hus i)
  have hpv (j : Fin n') : disjointed v j ⊆ (extChartAt I (β j)).source :=
    (disjointed_subset v j).trans (hvs j)
  calc
    ∑ i, (∫ y in (extChartAt I (α i)) '' disjointed u i, f (α i) y ∂ν) =
        ∑ i, ∑ j, ∫ y in (extChartAt I (α i)) '' (disjointed u i ∩ disjointed v j),
          f (α i) y ∂ν :=
      Finset.sum_congr rfl fun i _ ↦
        hsplit (α i) (IsChartMeasurable.disjointed hu i) (hpu i) (hfu i) hv hd
    _ = ∑ j, ∑ i, ∫ y in (extChartAt I (β j)) '' (disjointed v j ∩ disjointed u i),
          f (β j) y ∂ν := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun i _ ↦ ?_
      rw [inter_comm (disjointed v j)]
      exact hchange (α i) (β j) _ (fun x hx ↦ ⟨hpu i hx.1, hpv j hx.2⟩)
        ((IsChartMeasurable.disjointed hu i).inter (IsChartMeasurable.disjointed hv j))
    _ = ∑ j, ∫ y in (extChartAt I (β j)) '' disjointed v j, f (β j) y ∂ν :=
      (Finset.sum_congr rfl fun j _ ↦
        hsplit (β j) (IsChartMeasurable.disjointed hv j) (hpv j) (hfv j) hu hc).symm

/-- Chart coefficients that satisfy the absolute Jacobian law on a chart overlap have equal
integrals over the coordinate images of a subset of the overlap, and are integrable there
together. This is the change of variables shared by top forms and densities; the derivatives are
taken within `range I`, so boundary and corner models are included. -/
theorem setIntegral_image_extChartAt_changeChart [MeasurableSpace E] [BorelSpace E]
    [IsManifold I 1 M] [FiniteDimensional ℝ E] {f g : E → ℝ} (α β : M) {s : Set M}
    (hsub : s ⊆ (extChartAt I α).source ∩ (extChartAt I β).source)
    (hs : MeasurableSet ((extChartAt I α) '' s))
    (hfg : ∀ x ∈ s, |(fderivWithin ℝ (extChartAt I β ∘ (extChartAt I α).symm) (range I)
        (extChartAt I α x)).toLinearMap.det| * g (extChartAt I β x) = f (extChartAt I α x))
    (μ : Measure E) [μ.IsAddHaarMeasure] :
    (∫ y in (extChartAt I α) '' s, f y ∂μ) = (∫ y in (extChartAt I β) '' s, g y ∂μ) ∧
      (IntegrableOn f ((extChartAt I α) '' s) μ ↔ IntegrableOn g ((extChartAt I β) '' s) μ) := by
  let A := (extChartAt I α) '' s
  let e := (extChartAt I α).symm ≫ extChartAt I β
  let D := fun y ↦ fderivWithin ℝ (extChartAt I β ∘ (extChartAt I α).symm) (range I) y
  have himage := TauCeti.extChartAt_coordChange_image α β hsub
  have hinj := TauCeti.injOn_extChartAt_coordChange α β hsub
  have hderiv := TauCeti.hasFDerivWithinAt_extChartAt_coordChange α β hsub
  have hcoef : ∀ y ∈ A, |(D y).toLinearMap.det| • g (e y) = f y := by
    rintro _ ⟨x, hx, rfl⟩
    have he : e (extChartAt I α x) = extChartAt I β x :=
      congrArg (extChartAt I β) ((extChartAt I α).left_inv (hsub hx).1)
    rw [he, smul_eq_mul]
    exact hfg x hx
  constructor
  · rw [← himage, integral_image_eq_integral_abs_det_fderiv_smul μ hs hderiv hinj]
    exact setIntegral_congr_fun hs fun y hy ↦ (hcoef y hy).symm
  · rw [← himage, integrableOn_image_iff_integrableOn_abs_det_fderiv_smul μ hs hderiv hinj]
    exact (integrableOn_congr_fun (fun y hy ↦ hcoef y hy) hs).symm

end TauCeti
