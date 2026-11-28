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
in the integration of top forms and of densities; when the integrand vanishes almost everywhere
outside one preferred chart, the cover sum reduces to that single chart's global integral
(`TauCeti.sum_setIntegral_image_extChartAt_piece_eq_integral`). Chart coefficients related by the
absolute Jacobian of the transition map have equal integrals over the two coordinate images of a
subset of a chart overlap (`TauCeti.setIntegral_image_extChartAt_changeChart`). Only the model
carries a measurable structure. The coefficients take values in any real normed space.

A coefficient in a preferred chart is integrable when it vanishes off the chart target and at the
coordinates of the points outside a compact set, and is integrable on the coordinate images of the
pieces of an open cover of that set (`TauCeti.integrable_of_isCompact_of_open_cover_extChartAt`).

A finite open chart cover of a set, `TauCeti.ChartCover`, is chosen for each compact set by
`TauCeti.chooseChartCover`; the integrals of top forms and of densities are defined through it.

A nonnegative function that is integrable and continuous on a chart target and positive at one
target point—including boundary points—has positive integral there
(`TauCeti.setIntegral_pos_of_nonneg_of_pos_at_extChartAt_target`). This is the positivity step for
integrals of top forms and of densities.
-/

public section

open MeasureTheory Set
open scoped Manifold

namespace TauCeti

variable {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The disjointed pieces of a family of chart-measurable sets are chart measurable. -/
theorem IsChartMeasurable.disjointed [MeasurableSpace E] {ι : Type*} [Preorder ι]
    [LocallyFiniteOrderBot ι] {s : ι → Set M} (hs : ∀ i, IsChartMeasurable I (s i)) (i : ι) :
    IsChartMeasurable I (_root_.disjointed s i) := by
  rw [disjointed_apply]
  exact (hs i).diff (Finset.sup_induction (isChartMeasurable_empty (I := I))
    (fun _ ha _ hb ↦ ha.union hb) fun j _ ↦ hs j)

/-- A finite cover of a set `s` by open subsets of preferred chart sources. -/
structure ChartCover (I : ModelWithCorners ℝ E H) (s : Set M) where
  /-- The number of charts. -/
  n : ℕ
  /-- The centers of the preferred charts. -/
  center : Fin n → M
  /-- The open sets of the cover. -/
  domain : Fin n → Set M
  isOpen_domain : ∀ i, IsOpen (domain i)
  domain_subset : ∀ i, domain i ⊆ (extChartAt I (center i)).source
  covers : s ⊆ ⋃ i, domain i

/-- A chosen finite open chart cover of a compact set. -/
noncomputable def chooseChartCover (s : Set M) (hc : IsCompact s) : ChartCover I s :=
  let h := hc.elim_finite_subcover (fun x : M ↦ (extChartAt I x).source)
    (fun x ↦ isOpen_extChartAt_source x) fun y _ ↦ mem_iUnion.2 ⟨y, mem_extChartAt_source y⟩
  let e := h.choose.equivFin
  { n := h.choose.card
    center := fun i ↦ e.symm i
    domain := fun i ↦ (extChartAt I (e.symm i : M)).source
    isOpen_domain := fun _ ↦ isOpen_extChartAt_source _
    domain_subset := fun _ ↦ subset_rfl
    covers := fun y hy ↦ by
      obtain ⟨x, hx, hyx⟩ := mem_iUnion₂.1 (h.choose_spec hy)
      exact mem_iUnion.2 ⟨e ⟨x, hx⟩, by rwa [Equiv.symm_apply_apply]⟩ }

namespace ChartCover

variable {s : Set M} (c : ChartCover I s)

/-- The disjointed pieces of a chart cover. -/
def piece (i : Fin c.n) : Set M :=
  disjointed c.domain i

theorem piece_def (i : Fin c.n) : c.piece i = disjointed c.domain i := (rfl)

theorem piece_subset (i : Fin c.n) : c.piece i ⊆ (extChartAt I (c.center i)).source :=
  (disjointed_subset c.domain i).trans (c.domain_subset i)

theorem piece_covers : s ⊆ ⋃ i, c.piece i := by
  simpa only [piece, iUnion_disjointed] using c.covers

theorem pairwise_disjoint : Pairwise (fun i j ↦ Disjoint (c.piece i) (c.piece j)) :=
  disjoint_disjointed c.domain

variable [MeasurableSpace E] [OpensMeasurableSpace E]

theorem isChartMeasurable_piece (i : Fin c.n) : IsChartMeasurable I (c.piece i) :=
  IsChartMeasurable.disjointed (fun j ↦ (c.isOpen_domain j).isChartMeasurable) i

theorem measurableSet_image_piece (i : Fin c.n) :
    MeasurableSet ((extChartAt I (c.center i)) '' c.piece i) :=
  (c.isChartMeasurable_piece i).image_extChartAt (c.center i) (c.piece_subset i)

end ChartCover

omit [NormedSpace ℝ F] in
/-- A coefficient in the preferred chart at `α` is integrable when it vanishes off the chart
target and at the coordinates of the points outside a compact set `S`, and is integrable on the
coordinate images of the parts in the chart source of the sets of an open cover of `S`. -/
theorem integrable_of_isCompact_of_open_cover_extChartAt [MeasurableSpace E] {ν : Measure E}
    {g : E → F} (α : M) {S : Set M} (hS : IsCompact S) {J : Type*} (u : J → Set M)
    (hu : ∀ i, IsOpen (u i)) (hcover : S ⊆ ⋃ i, u i)
    (hpiece : ∀ i, IntegrableOn g ((extChartAt I α) '' ((extChartAt I α).source ∩ u i)) ν)
    (hz : ∀ y, g y ≠ 0 → y ∈ (extChartAt I α).target ∧ (extChartAt I α).symm y ∈ S) :
    Integrable g ν := by
  classical
  obtain ⟨t, ht⟩ := hS.elim_finite_subcover u hu hcover
  have htot : IntegrableOn g (⋃ i ∈ t, (extChartAt I α) '' ((extChartAt I α).source ∩ u i)) ν :=
    integrableOn_finset_iUnion.mpr fun i _ ↦ hpiece i
  refine (integrableOn_iff_integrable_of_support_subset fun y hy ↦ ?_).mp htot
  obtain ⟨hyt, hyS⟩ := hz y hy
  obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp (ht hyS)
  exact mem_iUnion₂.mpr ⟨i, hi, (extChartAt I α).symm y, ⟨(extChartAt I α).map_target hyt, hxi⟩,
    (extChartAt I α).right_inv hyt⟩

/-- An integral over the coordinate image of a chart-measurable subset `u` of a chart source
splits along the disjointed pieces of a finite chart-measurable family `v`, when the integrand
vanishes at the coordinates of the points of `u` outside that family. -/
theorem setIntegral_image_extChartAt_eq_sum_disjointed [MeasurableSpace E]
    {ν : Measure E} {f : E → F} (α : M) {u : Set M} (hf : IntegrableOn f ((extChartAt I α) '' u) ν)
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
    {ν : Measure E} {f : M → E → F} {S : Set M}
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

/-- If a `ChartCover` `c` covers `S`, and chart coefficients `f : M → E → F` vanish off the chart
target, vanish at coordinates outside `S`, agree in integral on chart overlaps, and vanish almost
everywhere outside `(extChartAt I α).source` on each piece of `c`, then the cover sum equals the
global integral of `f α`. -/
theorem sum_setIntegral_image_extChartAt_piece_eq_integral [MeasurableSpace E]
    [OpensMeasurableSpace E] {ν : Measure E} {f : M → E → F} {S : Set M} (c : ChartCover I S)
    (α : M) (hfα : Integrable (f α) ν)
    (ht : Function.support (f α) ⊆ (extChartAt I α).target)
    (hz : ∀ x ∈ (extChartAt I α).source, x ∉ S → f α (extChartAt I α x) = 0)
    (hchange : ∀ (i : Fin c.n) (s : Set M),
      s ⊆ (extChartAt I (c.center i)).source ∩ (extChartAt I α).source →
        IsChartMeasurable I s →
          (∫ y in (extChartAt I (c.center i)) '' s, f (c.center i) y ∂ν) =
            ∫ y in (extChartAt I α) '' s, f α y ∂ν)
    (hae : ∀ i : Fin c.n, ∀ᵐ y ∂ν,
      y ∉ (extChartAt I (c.center i)) ''
          ((extChartAt I (c.center i)).source ∩ (extChartAt I α).source) →
        y ∈ (extChartAt I (c.center i)) '' c.piece i → f (c.center i) y = 0) :
    ∑ i, (∫ y in (extChartAt I (c.center i)) '' c.piece i, f (c.center i) y ∂ν) =
      ∫ y, f α y ∂ν := by
  have hα_full : (∫ y, f α y ∂ν) =
      ∫ y in (extChartAt I α) '' (extChartAt I α).source, f α y ∂ν := by
    rw [(extChartAt I α).image_source_eq_target]
    exact (setIntegral_eq_integral_of_forall_compl_eq_zero fun _ hy ↦
      Function.notMem_support.mp fun hn ↦ hy (ht hn)).symm
  have hα_split := setIntegral_image_extChartAt_eq_sum_disjointed α hfα.integrableOn
    (isOpen_extChartAt_source (I := I) α).isChartMeasurable Subset.rfl
    (fun i ↦ (c.isOpen_domain i).isChartMeasurable)
    fun x hx hn ↦ hz x hx fun hS ↦ hn (c.covers hS)
  rw [hα_full, hα_split]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have hpiece_meas := c.isChartMeasurable_piece i
  have hα_meas : IsChartMeasurable I (extChartAt I α).source :=
    (isOpen_extChartAt_source α).isChartMeasurable
  have hch := hchange i (c.piece i ∩ (extChartAt I α).source)
    (fun _ hx ↦ ⟨c.piece_subset i hx.1, hx.2⟩) (hpiece_meas.inter hα_meas)
  rw [inter_comm ((extChartAt I α).source) (disjointed c.domain i)]
  simp_rw [← ChartCover.piece_def]
  rw [← hch]
  refine setIntegral_eq_of_subset_of_ae_sdiff_eq_zero
    (c.measurableSet_image_piece i).nullMeasurableSet
    (image_mono (inter_subset_left : c.piece i ∩ (extChartAt I α).source ⊆ c.piece i)) ?_
  filter_upwards [hae i] with y hy
  rintro ⟨⟨x, hx, rfl⟩, hnot⟩
  have hxo : extChartAt I (c.center i) x ∉ (extChartAt I (c.center i)) ''
      ((extChartAt I (c.center i)).source ∩ (extChartAt I α).source) := by
    rintro ⟨x', hx', heq⟩
    have hx_eq : x' = x := (extChartAt I (c.center i)).injOn hx'.1 (c.piece_subset i hx) heq
    exact hnot ⟨x, ⟨hx, hx_eq ▸ hx'.2⟩, rfl⟩
  exact hy hxo (mem_image_of_mem _ hx)

/-- Chart coefficients that satisfy the absolute Jacobian law on a chart overlap have equal
integrals over the coordinate images of a subset of the overlap, and are integrable there
together. This is the change of variables shared by top forms and densities; the derivatives are
taken within `range I`, so boundary and corner models are included. -/
theorem setIntegral_image_extChartAt_changeChart [MeasurableSpace E] [BorelSpace E]
    [IsManifold I 1 M] [FiniteDimensional ℝ E] {f g : E → F} (α β : M) {s : Set M}
    (hsub : s ⊆ (extChartAt I α).source ∩ (extChartAt I β).source)
    (hs : MeasurableSet ((extChartAt I α) '' s))
    (hfg : ∀ x ∈ s, |(fderivWithin ℝ (extChartAt I β ∘ (extChartAt I α).symm) (range I)
        (extChartAt I α x)).toLinearMap.det| • g (extChartAt I β x) = f (extChartAt I α x))
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
    rw [he]
    exact hfg x hx
  constructor
  · rw [← himage, integral_image_eq_integral_abs_det_fderiv_smul μ hs hderiv hinj]
    exact setIntegral_congr_fun hs fun y hy ↦ (hcoef y hy).symm
  · rw [← himage, integrableOn_image_iff_integrableOn_abs_det_fderiv_smul μ hs hderiv hinj]
    exact (integrableOn_congr_fun (fun y hy ↦ hcoef y hy) hs).symm

/-- A nonnegative function continuous on a chart target has positive integral on that target
for any measure positive on nonempty open sets, if it is integrable there and positive at one
target point. This also applies at boundary points, since the interior of the target is dense
in the target. -/
theorem setIntegral_pos_of_nonneg_of_pos_at_extChartAt_target
    [MeasurableSpace E] {μ : Measure E} [μ.IsOpenPosMeasure] (α : M) {g : E → ℝ}
    (hnn : ∀ y, 0 ≤ g y) (hint : IntegrableOn g (extChartAt I α).target μ)
    (hcont : ContinuousOn g (extChartAt I α).target) {y₀ : E}
    (hy₀ : y₀ ∈ (extChartAt I α).target) (hg₀ : 0 < g y₀) :
    0 < ∫ y in (extChartAt I α).target, g y ∂μ := by
  rw [setIntegral_pos_iff_support_of_nonneg_ae (Filter.Eventually.of_forall hnn) hint]
  -- Positivity reaches an open subset of the interior, including from a boundary point.
  let V := interior (extChartAt I α).target ∩ g ⁻¹' Ioi 0
  have hV : IsOpen V :=
    (hcont.mono interior_subset).isOpen_inter_preimage isOpen_interior isOpen_Ioi
  obtain ⟨U, hUo, hxU, hUg⟩ := mem_nhdsWithin.mp
    ((hcont.continuousWithinAt hy₀).eventually (lt_mem_nhds hg₀))
  obtain ⟨z, hzU, hz⟩ := mem_closure_iff.mp
    (extChartAt_target_subset_closure_interior hy₀) U hUo hxU
  have hVne : V.Nonempty := ⟨z, hz, hUg ⟨hzU, interior_subset hz⟩⟩
  refine (hV.measure_pos μ hVne).trans_le (measure_mono fun y hy ↦ ?_)
  exact ⟨(ne_of_gt hy.2 : g y ≠ 0), interior_subset hy.1⟩

end TauCeti
