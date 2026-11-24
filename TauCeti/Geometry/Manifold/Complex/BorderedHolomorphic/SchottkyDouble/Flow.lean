/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Complex.BorderedHolomorphic.SchottkyDouble.Basic
public import TauCeti.Geometry.Manifold.IntegralCurve.GlobalFlow
import TauCeti.Geometry.Manifold.VectorField.Regularity
import TauCeti.Geometry.Manifold.IntegralCurve.Monotone
import Mathlib.Tactic.Choose

/-!
# Signed flow entry into the interior sheets of a Schottky double

A complete C¹ ambient field whose preferred doubled-chart imaginary derivative is positive on a
compact subset of the native gluing set `(borderedInterior M)ᶜ` flows into the first interior sheet
at positive small times and
into the second interior sheet at negative small times. One time interval works for every start
in that compact set. On the same interval the flow meets the gluing set exactly at time zero.

For compact original surfaces, ambient completeness follows from the existing compact-manifold
theorem.
-/

public section

noncomputable section

open Set Filter Topology
open scoped Manifold ContDiff

namespace TauCeti.SchottkyDouble

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ClosedUpperHalfPlane M]
  [IsManifold closedUpperHalfPlaneModel 1 M] [T2Space M]
  [IsManifold 𝓘(ℝ, ℂ) 1 (SchottkyDouble M)]

local notation "A" => (borderedInterior M : Set M)ᶜ
local notation "D" => SchottkyDouble M
local notation "J" => 𝓘(ℝ, ℂ)

omit [T2Space M] in
/-- A fixed doubled-chart defining function is real C¹ on its source. -/
private theorem contMDiffOn_chart_im (p : D) :
    ContMDiffOn J 𝓘(ℝ) 1 (fun z : D ↦ (chartAt ℂ p z).im) (chartAt ℂ p).source := by
  exact (Complex.imCLM.contMDiff).comp_contMDiffOn (contMDiffOn_chart (I := J))

omit [T2Space M] in
/-- The fixed-chart directional derivative varies continuously on its chart source. -/
private theorem continuousOn_chart_im_mvfderiv
    {v : (z : D) → TangentSpace J z}
    (hv : ContMDiff J (J).tangent 0 (fun z ↦ (⟨z, v z⟩ : TangentBundle J D))) (p : D) :
    ContinuousOn
      (fun z ↦ mvfderiv J (fun w : D ↦ (chartAt ℂ p w).im) z (v z))
      (chartAt ℂ p).source := by
  exact ((contMDiffOn_chart_im p).contMDiffOn_mvfderiv_apply (m := 0)
    (chartAt ℂ p).open_source hv.contMDiffOn (by simp)).continuousOn

/-- Strict chart-coordinate crossing along a flow which stays in its positive-derivative domain. -/
private theorem globalFlow_im_chartAt_sign
    {v : (z : D) → TangentSpace J z}
    (hv : ContMDiff J (J).tangent 1 (fun z ↦ (⟨z, v z⟩ : TangentBundle J D)))
    (hc : IsCompleteVectorField v) {x y : M} {ε : ℝ} (hy : y ∈ A)
    (hstay : ∀ t ∈ Ioo (-ε) ε,
      globalFlow v hv hc t (DoubleAlong.inl A y) ∈ (chartAt ℂ (DoubleAlong.inl A x)).source ∧
      0 < mvfderiv J (fun z : D ↦ (chartAt ℂ (DoubleAlong.inl A x) z).im)
        (globalFlow v hv hc t (DoubleAlong.inl A y))
        (v (globalFlow v hv hc t (DoubleAlong.inl A y)))) :
    (∀ t ∈ Ioo 0 ε,
      0 < (chartAt ℂ (DoubleAlong.inl A x) (globalFlow v hv hc t (DoubleAlong.inl A y))).im) ∧
    (∀ t ∈ Ioo (-ε) 0,
      (chartAt ℂ (DoubleAlong.inl A x) (globalFlow v hv hc t (DoubleAlong.inl A y))).im < 0) := by
  by_cases hε : 0 < ε
  · let p := DoubleAlong.inl A x
    let c := chartAt ℂ p
    let f : D → ℝ := fun z ↦ (c z).im
    let γ : ℝ → D := fun t ↦ globalFlow v hv hc t (DoubleAlong.inl A y)
    have hγ := (isMIntegralCurve_globalFlow hv hc (DoubleAlong.inl A y)).isMIntegralCurveOn
      (Ioo (-ε) ε)
    have hz : f (γ 0) = 0 := by
      simp only [γ, Flow.map_zero_apply]
      exact (mem_image_inl_compl_iff_im_chartAt_eq_zero (by
        simpa only [Flow.map_zero_apply] using (hstay 0 ⟨neg_neg_of_pos hε, hε⟩).1)).1
        (mem_image_of_mem _ hy)
    have hdiff (t : ℝ) (ht : t ∈ Ioo (-ε) ε) :
        MDifferentiableAt J 𝓘(ℝ) f (γ t) ∧ 0 < mvfderiv J f (γ t) (v (γ t)) :=
      ⟨((contMDiffOn_chart_im p).contMDiffAt
        (c.open_source.mem_nhds (hstay t ht).1)).mdifferentiableAt one_ne_zero, (hstay t ht).2⟩
    have hcont : ContinuousOn (f ∘ γ) (Ioo (-ε) ε) :=
      (contMDiffOn_chart_im p).continuousOn.comp hγ.continuousOn (fun t ht ↦ (hstay t ht).1)
    constructor
    · intro t ht
      have hsub : Icc 0 t ⊆ Ioo (-ε) ε := Icc_subset_Ioo (neg_lt_zero.mpr hε) ht.2
      exact hγ.lt_apply_of_le_apply isOpen_Ioo hsub (hcont.mono hsub)
        (fun u hu _ ↦ hdiff u (hsub hu)) (by rw [hz]) ⟨ht.1, le_rfl⟩
    · intro t ht
      have hsub : Icc t 0 ⊆ Ioo (-ε) ε := Icc_subset_Ioo ht.1 hε
      exact hγ.apply_lt_of_apply_le isOpen_Ioo hsub (hcont.mono hsub)
        (fun u hu _ ↦ hdiff u (hsub hu)) (by rw [hz]) ⟨le_rfl, ht.2⟩
  · constructor
    · intro t ht
      exact False.elim (hε (ht.1.trans ht.2))
    · intro t ht
      exact False.elim (hε (neg_lt_zero.mp (ht.1.trans ht.2)))

/-- Uniform crossing on a box around a fixed seam point, using its fixed native chart. -/
theorem exists_local_globalFlow_mem_interiorSheets
    {v : (z : D) → TangentSpace J z}
    (hv : ContMDiff J (J).tangent 1 (fun z ↦ (⟨z, v z⟩ : TangentBundle J D)))
    (hc : IsCompleteVectorField v) {x : M}
    (hpos : 0 < mvfderiv J (fun z : D ↦ (chartAt ℂ (DoubleAlong.inl A x) z).im)
      (DoubleAlong.inl A x) (v (DoubleAlong.inl A x))) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ U : Set M, IsOpen U ∧ x ∈ U ∧
      ∀ y ∈ U, y ∈ A →
        (∀ t ∈ Ioo 0 ε, globalFlow v hv hc t (DoubleAlong.inl A y) ∈
          range (SchottkyDouble.interiorInl M)) ∧
        (∀ t ∈ Ioo (-ε) 0, globalFlow v hv hc t (DoubleAlong.inl A y) ∈
          range (SchottkyDouble.interiorInr M)) := by
  let p := DoubleAlong.inl A x
  let c := chartAt ℂ p
  let f : D → ℝ := fun z ↦ (c z).im
  let R : D → ℝ := fun z ↦ mvfderiv J f z (v z)
  have hcp : p ∈ c.source := mem_chart_source ℂ p
  have hR : ContinuousAt R p :=
    (continuousOn_chart_im_mvfderiv (hv.of_le (by simp)) p).continuousAt
      (c.open_source.mem_nhds hcp)
  have hgood : {z | z ∈ c.source ∧ 0 < R z} ∈ 𝓝 p :=
    inter_mem (c.open_source.mem_nhds hcp) (hR.preimage_mem_nhds (Ioi_mem_nhds hpos))
  obtain ⟨W, hWsub, hWopen, hpW⟩ := mem_nhds_iff.mp hgood
  have hflow : Continuous (fun q : ℝ × M ↦ globalFlow v hv hc q.1 (DoubleAlong.inl A q.2)) :=
    (globalFlow v hv hc).continuous continuous_fst
      ((DoubleAlong.inl A).continuous.comp continuous_snd)
  have hzeroW : globalFlow v hv hc 0 (DoubleAlong.inl A x) ∈ W := by
    simpa only [Flow.map_zero_apply] using hpW
  have hbox := (hflow.continuousAt (x := (0, x))).preimage_mem_nhds
    (hWopen.mem_nhds hzeroW)
  obtain ⟨T, U, hTopen, hTzero, hUopen, hxU, hTU⟩ := mem_nhds_prod_iff'.mp hbox
  obtain ⟨ε, hε, hεT⟩ := Metric.mem_nhds_iff.mp (hTopen.mem_nhds hTzero)
  have hstay (y : M) (hy : y ∈ U) (t : ℝ) (ht : t ∈ Ioo (-ε) ε) :
      globalFlow v hv hc t (DoubleAlong.inl A y) ∈ W := by
    apply hTU (a := (t, y))
    refine ⟨hεT ?_, hy⟩
    simpa only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, abs_lt, mem_Ioo] using ht
  refine ⟨ε, hε, U, hUopen, hxU, ?_⟩
  intro y hy hyA
  obtain ⟨hplus, hminus⟩ := globalFlow_im_chartAt_sign hv hc hyA
    (fun t ht ↦ hWsub (hstay y hy t ht))
  constructor
  · intro t ht
    exact (mem_range_interiorInl_iff_im_chartAt_pos
      (hWsub (hstay y hy t ⟨(neg_neg_of_pos hε).trans ht.1, ht.2⟩)).1).2 (hplus t ht)
  · intro t ht
    exact (mem_range_interiorInr_iff_im_chartAt_neg
      (hWsub (hstay y hy t ⟨ht.1, ht.2.trans hε⟩)).1).2 (hminus t ht)

/-- A compact set in the actual seam has a common signed flow-side interval. -/
theorem exists_uniform_globalFlow_mem_interiorSheets
    {v : (z : D) → TangentSpace J z}
    (hv : ContMDiff J (J).tangent 1 (fun z ↦ (⟨z, v z⟩ : TangentBundle J D)))
    (hc : IsCompleteVectorField v) {K : Set M} (hK : IsCompact K) (hKA : K ⊆ A)
    (hpos : ∀ x ∈ K,
      0 < mvfderiv J (fun z : D ↦ (chartAt ℂ (DoubleAlong.inl A x) z).im)
        (DoubleAlong.inl A x) (v (DoubleAlong.inl A x))) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ K,
      (∀ t ∈ Ioo 0 ε, globalFlow v hv hc t (DoubleAlong.inl A x) ∈
        range (SchottkyDouble.interiorInl M)) ∧
      (∀ t ∈ Ioo (-ε) 0, globalFlow v hv hc t (DoubleAlong.inl A x) ∈
        range (SchottkyDouble.interiorInr M)) ∧
      (∀ t ∈ Ioo (-ε) ε,
        globalFlow v hv hc t (DoubleAlong.inl A x) ∈ DoubleAlong.inl A '' A ↔ t = 0) := by
  classical
  choose δ hδ U hU hxU hside using
    (fun x : K ↦ exists_local_globalFlow_mem_interiorSheets hv hc (hpos x x.property))
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover U hU (fun x hx ↦
    mem_iUnion.mpr ⟨⟨x, hx⟩, hxU ⟨x, hx⟩⟩)
  have hmin : ∃ ε : ℝ, 0 < ε ∧ ∀ i ∈ s, ε ≤ δ i := by
    rcases s.eq_empty_or_nonempty with rfl | hne
    · exact ⟨1, one_pos, by simp⟩
    · exact ⟨s.inf' hne δ, (Finset.lt_inf'_iff hne).2 (fun i _ ↦ hδ i),
        fun i hi ↦ Finset.inf'_le δ hi⟩
  obtain ⟨ε, hε, hεs⟩ := hmin
  refine ⟨ε, hε, ?_⟩
  intro x hx
  obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp (hs hx)
  obtain ⟨hplus, hminus⟩ := hside i x hxi (hKA hx)
  have hp (t : ℝ) (ht : t ∈ Ioo 0 ε) :=
    hplus t ⟨ht.1, ht.2.trans_le (hεs i hi)⟩
  have hm (t : ℝ) (ht : t ∈ Ioo (-ε) 0) :=
    hminus t ⟨lt_of_le_of_lt (neg_le_neg (hεs i hi)) ht.1, ht.2⟩
  refine ⟨hp, hm, ?_⟩
  intro t ht
  constructor
  · intro hseam
    have hzero := (mem_image_inl_compl_iff_im_chartAt_eq_zero
      (mem_chart_source ℂ (globalFlow v hv hc t (DoubleAlong.inl A x)))).1 hseam
    rcases lt_trichotomy t 0 with hneg | heq | hpos
    · have him := (mem_range_interiorInr_iff_im_chartAt_neg
        (mem_chart_source ℂ _)).1 (hm t ⟨ht.1, hneg⟩)
      rw [hzero] at him
      exact (lt_irrefl 0 him).elim
    · exact heq
    · have him := (mem_range_interiorInl_iff_im_chartAt_pos
        (mem_chart_source ℂ _)).1 (hp t ⟨hpos, ht.2⟩)
      rw [hzero] at him
      exact (lt_irrefl 0 him).elim
  · rintro rfl
    simpa only [Flow.map_zero_apply] using mem_image_of_mem (DoubleAlong.inl A) (hKA hx)

/-- Compactness of the original bordered surface gives one time for its entire native seam. -/
theorem exists_uniform_globalFlow_mem_interiorSheets_of_compactSpace [CompactSpace M]
    {v : (z : D) → TangentSpace J z}
    (hv : ContMDiff J (J).tangent 1 (fun z ↦ (⟨z, v z⟩ : TangentBundle J D)))
    (hpos : ∀ x ∈ A,
      0 < mvfderiv J (fun z : D ↦ (chartAt ℂ (DoubleAlong.inl A x) z).im)
        (DoubleAlong.inl A x) (v (DoubleAlong.inl A x))) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ A,
      (∀ t ∈ Ioo 0 ε, globalFlow v hv (isCompleteVectorField_of_compactSpace hv) t
        (DoubleAlong.inl A x) ∈
        range (SchottkyDouble.interiorInl M)) ∧
      (∀ t ∈ Ioo (-ε) 0, globalFlow v hv (isCompleteVectorField_of_compactSpace hv) t
        (DoubleAlong.inl A x) ∈
        range (SchottkyDouble.interiorInr M)) ∧
      (∀ t ∈ Ioo (-ε) ε,
        globalFlow v hv (isCompleteVectorField_of_compactSpace hv) t
        (DoubleAlong.inl A x) ∈ DoubleAlong.inl A '' A ↔ t = 0) :=
  exists_uniform_globalFlow_mem_interiorSheets hv (isCompleteVectorField_of_compactSpace hv)
    (borderedInterior M).isOpen.isClosed_compl.isCompact
    (Subset.refl A) hpos

end TauCeti.SchottkyDouble
