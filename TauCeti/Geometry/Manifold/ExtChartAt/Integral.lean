/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.Jacobian
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import TauCeti.Geometry.Manifold.ExtChartAt
public import TauCeti.Geometry.Manifold.ExtChartAt.Measure
import TauCeti.Geometry.Manifold.ExtChartAt.CoordChange
import TauCeti.Geometry.Manifold.ExtChartAt.Measurable
import TauCeti.Geometry.Manifold.MFDeriv.Chart.Det
import TauCeti.Geometry.Manifold.ModelWithCorners.Measure

/-!
# Set integrals and Jacobian change of variables for extended charts

A finite family of chart-measurable sets is disjointed into pieces. An integral over the coordinate
image of a chart-measurable subset of a chart source splits along these pieces
(`TauCeti.setIntegral_image_extChartAt_eq_sum_disjointed`), and two finite chart-measurable covers
of a set give the same sum of chart integrals for chart coefficients that agree on chart overlaps
(`TauCeti.sum_setIntegral_image_extChartAt_disjointed_eq`). This is the cover-independence step
in the integration of top forms and of densities. Chart coefficients related by the absolute
Jacobian of the transition map have equal integrals over the two coordinate images of a subset
of a chart overlap (`TauCeti.setIntegral_image_extChartAt_changeChart`). Only the model carries a
measurable structure. The coefficients take values in any real normed space.

A coefficient in a preferred chart is integrable when it vanishes off the chart target and at the
coordinates of the points outside a compact set, and is integrable on the coordinate images of the
pieces of an open cover of that set (`TauCeti.integrable_of_isCompact_of_open_cover_extChartAt`).

A finite open chart cover of a set, `TauCeti.ChartCover`, is chosen for each compact set by
`TauCeti.chooseChartCover`; the integrals of top forms and of densities are defined through it.

For arbitrary extended charts `e.extend I` and charts of the `C¹` maximal atlas,
`ModelWithCorners.setLIntegral_extendCoordChange` gives the coordinate change-of-variables formula
for lower integrals against an additive Haar measure, yielding overlap pushforward and Jacobian
density identities (`OpenPartialHomeomorph.map_restrict_localChartMeasure_apply`,
`OpenPartialHomeomorph.map_restrict_extend_apply_of_subset_extendCoordChange_source`, and
`ModelWithCorners.eqOn_abs_det_mul_of_map_restrict_eq`).
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

end TauCeti

section JacobianChangeOfVariables

open scoped ENNReal Topology

noncomputable section

namespace ModelWithCorners

/-- Change of variables between two charts of the maximal atlas for a weighted Haar integral. -/
theorem setLIntegral_extendCoordChange {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    (ν : Measure E) [ν.IsAddHaarMeasure]
    {e e' : OpenPartialHomeomorph M H}
    (he : e ∈ IsManifold.maximalAtlas I 1 M) (he' : e' ∈ IsManifold.maximalAtlas I 1 M)
    {A : Set E} (hA : MeasurableSet A) (hAsub : A ⊆ (I.extendCoordChange e e').source)
    (g : E → ℝ≥0∞) :
    ∫⁻ z in I.extendCoordChange e e' '' A, g z ∂ν =
      ∫⁻ y in A,
        ENNReal.ofReal |(fderivWithin ℝ (I.extendCoordChange e e') (range I) y).det| *
          g (I.extendCoordChange e e' y) ∂ν := by
  have hArange : A ⊆ range I :=
    hAsub.trans (by rw [I.extendCoordChange_source]; exact image_subset_range _ _)
  have hderiv : ∀ y ∈ A,
      HasFDerivWithinAt (I.extendCoordChange e e')
        (fderivWithin ℝ (I.extendCoordChange e e') (range I) y) A y := fun y hy ↦
    ((I.contDiffWithinAt_extendCoordChange he he' (hAsub hy)).differentiableWithinAt
      one_ne_zero).hasFDerivWithinAt.mono hArange
  exact lintegral_image_eq_lintegral_abs_det_fderiv_mul ν hA hderiv
    ((I.extendCoordChange e e').injOn.mono hAsub) g

end ModelWithCorners

open Classical in
/-- Pushing `e₁.localChartMeasure I ν g` restricted to `e₀.source` forward along `e₀.extend I`
yields a weighted Haar integral whose density weights `g (I.extendCoordChange e₀ e₁ y)` by
`ENNReal.ofReal |det D(e₁ ∘ e₀⁻¹)|` on `(I.extendCoordChange e₀ e₁).source` and vanishes off the
overlap. -/
theorem OpenPartialHomeomorph.map_restrict_localChartMeasure_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    {H : Type*} [TopologicalSpace H]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [MeasurableSpace M] [BorelSpace M]
    (e₀ e₁ : OpenPartialHomeomorph M H) (I : ModelWithCorners ℝ E H)
    (he₀ : e₀ ∈ IsManifold.maximalAtlas I 1 M) (he₁ : e₁ ∈ IsManifold.maximalAtlas I 1 M)
    (ν : Measure E) [ν.IsAddHaarMeasure] (g : E → ℝ≥0∞) {A : Set E} (hA : MeasurableSet A) :
    (((e₁.localChartMeasure I ν g).restrict e₀.source).map (e₀.extend I)) A =
      ∫⁻ y in A ∩ (e₀.extend I).target,
        (I.extendCoordChange e₀ e₁).source.indicator
          (fun y ↦ ENNReal.ofReal
            |(fderivWithin ℝ (I.extendCoordChange e₀ e₁) (range I) y).det| *
              g (I.extendCoordChange e₀ e₁ y)) y ∂ν := by
  set Φ := I.extendCoordChange e₀ e₁
  have hΦ_meas := I.measurableSet_extendCoordChange_source e₀ e₁
  have hT₀ : MeasurableSet (e₀.extend I).target := e₀.measurableSet_extend_target I
  have hs_meas : MeasurableSet (e₀.extend I ⁻¹' A ∩ e₀.source) :=
    e₀.measurableSet_preimage_extend_inter I hA
  rw [e₀.map_restrict_extend_apply I _ hA, e₁.localChartMeasure_apply I ν g hs_meas,
    e₀.image_extend_preimage_inter e₁ I A,
    I.setLIntegral_extendCoordChange ν he₀ he₁ (hA.inter hΦ_meas) inter_subset_right,
    ← lintegral_indicator (hA.inter hΦ_meas), ← lintegral_indicator (hA.inter hT₀)]
  refine lintegral_congr fun y ↦ ?_
  by_cases hy : y ∈ A ∩ Φ.source
  · have hyT : y ∈ A ∩ (e₀.extend I).target :=
      ⟨hy.1, I.mem_extend_target_of_mem_extendCoordChange_source hy.2⟩
    rw [indicator_of_mem hy, indicator_of_mem hyT, indicator_of_mem hy.2]
  · rw [indicator_of_notMem hy]
    by_cases hy' : y ∈ A ∩ (e₀.extend I).target
    · rw [indicator_of_mem hy', indicator_of_notMem (fun h ↦ hy ⟨hy'.1, h⟩)]
    · rw [indicator_of_notMem hy']

/-- On a measurable subset `A ⊆ (I.extendCoordChange e e').source` of a chart overlap, the
pushforward measure `((μ.restrict e.source).map (e.extend I)) A` equals the Haar integral of
`ENNReal.ofReal` applied to the Jacobian-weight product `|det D(e' ∘ e⁻¹)| * w' (e' ∘ e⁻¹)` for any
chart weight `w'` presenting `(μ.restrict e'.source).map (e'.extend I)` against `ν`. -/
theorem OpenPartialHomeomorph.map_restrict_extend_apply_of_subset_extendCoordChange_source
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    {H : Type*} [TopologicalSpace H]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [MeasurableSpace M] [BorelSpace M]
    (e e' : OpenPartialHomeomorph M H) (I : ModelWithCorners ℝ E H)
    {μ : Measure M} {ν : Measure E} [ν.IsAddHaarMeasure]
    (he : e ∈ IsManifold.maximalAtlas I 1 M) (he' : e' ∈ IsManifold.maximalAtlas I 1 M)
    {w' : E → ℝ}
    (hmap' : (μ.restrict e'.source).map (e'.extend I) =
      (ν.restrict (e'.extend I).target).withDensity fun y ↦ ENNReal.ofReal (w' y))
    {A : Set E} (hA : MeasurableSet A) (hAsub : A ⊆ (I.extendCoordChange e e').source) :
    ((μ.restrict e.source).map (e.extend I)) A =
      ∫⁻ y in A,
        ENNReal.ofReal (|(fderivWithin ℝ (I.extendCoordChange e e') (range I) y).det| *
          w' (I.extendCoordChange e e' y)) ∂ν := by
  set s := e.extend I ⁻¹' A ∩ e.source
  have hs_meas : MeasurableSet s := e.measurableSet_preimage_extend_inter I hA
  have hse' : s ⊆ e'.source := fun x ⟨hxA, hxe⟩ ↦ by
    have hmem : (e.extend I).symm (e.extend I x) ∈ e'.source :=
      I.extend_symm_mem_of_mem_extendCoordChange_source (hAsub hxA)
    rwa [(e.extend I).left_inv (e.extend_source (I := I) ▸ hxe)] at hmem
  have him : e'.extend I '' s = I.extendCoordChange e e' '' A := by
    rw [← inter_eq_left.2 hse', e.image_extend_preimage_inter e' I A, inter_eq_left.2 hAsub]
  have hB : MeasurableSet (e'.extend I '' s) := e'.measurableSet_image_extend I hs_meas hse'
  have hBT : e'.extend I '' s ⊆ (e'.extend I).target :=
    (image_mono (e'.extend_source (I := I) ▸ hse')).trans
      (e'.extend I).image_source_eq_target.subset
  have hμs : μ s = ((μ.restrict e'.source).map (e'.extend I)) (e'.extend I '' s) :=
    (e'.map_restrict_extend_apply_image I μ hse').symm
  rw [e.map_restrict_extend_apply I μ hA, hμs, hmap', withDensity_apply _ hB,
    Measure.restrict_restrict hB, inter_eq_left.2 hBT, him,
    I.setLIntegral_extendCoordChange ν he he' hA hAsub]
  exact setLIntegral_congr_fun hA fun y _ ↦ (ENNReal.ofReal_mul (abs_nonneg _)).symm

namespace ModelWithCorners

section OverlapJacobian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [MeasurableSpace M] [BorelSpace M]

/-- Shared Jacobian transformation identity for two continuous nonnegative chart weights presenting
the same measure on their chart overlap. -/
theorem eqOn_abs_det_mul_of_map_restrict_eq
    {μ : Measure M} {ν : Measure E} [ν.IsAddHaarMeasure]
    {e e' : OpenPartialHomeomorph M H}
    (he : e ∈ IsManifold.maximalAtlas I 1 M) (he' : e' ∈ IsManifold.maximalAtlas I 1 M)
    {w w' : E → ℝ}
    (hw : ContinuousOn w (e.extend I).target) (hw' : ContinuousOn w' (e'.extend I).target)
    (hw0 : ∀ y ∈ (e.extend I).target, 0 ≤ w y) (hw'0 : ∀ y ∈ (e'.extend I).target, 0 ≤ w' y)
    (hmap : (μ.restrict e.source).map (e.extend I) =
      (ν.restrict (e.extend I).target).withDensity fun y ↦ ENNReal.ofReal (w y))
    (hmap' : (μ.restrict e'.source).map (e'.extend I) =
      (ν.restrict (e'.extend I).target).withDensity fun y ↦ ENNReal.ofReal (w' y)) :
    EqOn w (fun y ↦ |(fderivWithin ℝ (I.extendCoordChange e e') (range I) y).det| *
      w' (I.extendCoordChange e e' y)) (I.extendCoordChange e e').source := by
  set Φ := I.extendCoordChange e e'
  have hΦ_src : Φ.source = I.symm ⁻¹' (e.symm ≫ₕ e').source ∩ range I := by
    rw [I.extendCoordChange_source, I.image_eq]
  have hΦ_meas : MeasurableSet Φ.source := I.measurableSet_extendCoordChange_source e e'
  have hsubT : Φ.source ⊆ (e.extend I).target :=
    I.extendCoordChange_source_subset_extend_target e e'
  have hmeq :
      (ν.restrict Φ.source).withDensity (fun y ↦ ENNReal.ofReal (w y)) =
        (ν.restrict Φ.source).withDensity fun y ↦
          ENNReal.ofReal (|(fderivWithin ℝ Φ (range I) y).det| * w' (Φ y)) := by
    ext A hA
    have h1 := withDensity_apply (fun y ↦ ENNReal.ofReal (w y)) (hA.inter hΦ_meas)
      (μ := ν.restrict (e.extend I).target)
    rw [Measure.restrict_restrict (hA.inter hΦ_meas),
      inter_eq_left.2 (inter_subset_right.trans hsubT), ← hmap,
      e.map_restrict_extend_apply_of_subset_extendCoordChange_source e' I he he' hmap'
        (hA.inter hΦ_meas) inter_subset_right] at h1
    rw [withDensity_apply _ hA, withDensity_apply _ hA, Measure.restrict_restrict hA, h1]
  have hcont_rhs : ContinuousOn
      (fun y ↦ |(fderivWithin ℝ Φ (range I) y).det| * w' (Φ y)) Φ.source :=
    (I.continuousOn_abs_det_fderivWithin_extendCoordChange he he').mul
      (hw'.comp (I.contDiffOn_extendCoordChange he he').continuousOn fun _ hy ↦
        I.extendCoordChange_mem_extend_target hy)
  rw [hΦ_src] at hmeq hcont_rhs ⊢
  exact I.eqOn_of_withDensity_ofReal_eq (e.symm ≫ₕ e').open_source
    (hw.mono (hΦ_src ▸ hsubT)) hcont_rhs
    (fun y hy ↦ hw0 y (hsubT (hΦ_src.symm ▸ hy)))
    (fun y hy ↦ mul_nonneg (abs_nonneg _)
      (hw'0 _ (I.extendCoordChange_mem_extend_target (hΦ_src.symm ▸ hy)))) hmeq

end OverlapJacobian

end ModelWithCorners

end

end JacobianChangeOfVariables
