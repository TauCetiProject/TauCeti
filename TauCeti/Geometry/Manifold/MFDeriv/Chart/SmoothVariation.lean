/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import TauCeti.Geometry.Manifold.MFDeriv.Variation
import TauCeti.Analysis.Calculus.Taylor.Integral
import TauCeti.Analysis.Convex.Combination
import TauCeti.Geometry.Manifold.ContMDiff.Atlas
import TauCeti.Topology.Compactness.Compact
import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# Smooth fixed-endpoint variations from localized first jets

A first jet along the central curve can be realized by smooth nearby curves after
localizing in one chart. A quadratic inward correction keeps the coordinate points
in the model range and preserves the first variation, including at boundary points.
-/

public section

noncomputable section

open Set Filter Metric
open scoped Topology ContDiff Manifold

namespace TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The affine transverse jet, with a quadratic correction towards a fixed interior point. -/
private def inwardFirstJet (f : ℝ × ℝ → E) (C : ℝ) (y : E) (φ : ℝ → ℝ) (u t : ℝ) : E :=
  (1 - C * (u * φ t) ^ 2) •
      (f (0, t) + (u * φ t) • fderiv ℝ f (0, t) (1, 0)) +
    (C * (u * φ t) ^ 2) • y

/-- The correction preserves the entire central curve. -/
@[simp]
private theorem inwardFirstJet_zero (f : ℝ × ℝ → E) (C : ℝ) (y : E) (φ : ℝ → ℝ) (t : ℝ) :
    inwardFirstJet f C y φ 0 t = f (0, t) := by
  simp [inwardFirstJet]

/-- The correction has the localized original transverse derivative. -/
private theorem hasDerivAt_inwardFirstJet (f : ℝ × ℝ → E) (C : ℝ) (y : E) (φ : ℝ → ℝ)
    (t : ℝ) :
    HasDerivAt (fun u ↦ inwardFirstJet f C y φ u t)
      (φ t • fderiv ℝ f (0, t) (1, 0)) 0 := by
  have hq : HasDerivAt (fun u : ℝ ↦ u * φ t) (φ t) 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).mul_const (φ t)
  have hweight : HasDerivAt (fun u : ℝ ↦ C * (u * φ t) ^ 2) 0 0 := by
    simpa using (hq.pow 2).const_mul C
  have hlin := (hasDerivAt_const (0 : ℝ) (f (0, t))).add
    (hq.smul_const (fderiv ℝ f (0, t) (1, 0)))
  have h := (((hasDerivAt_const (0 : ℝ) 1).sub hweight).smul hlin).add (hweight.smul_const y)
  convert h using 1
  · funext u
    rfl
  · simp [Pi.sub_apply]

/-- Smoothness of the axis germ gives smoothness of the corrected family at every point of
the corresponding vertical line, including when the original nearby slices are not smooth. -/
private theorem contDiffAt_inwardFirstJet {f : ℝ × ℝ → E} {t : ℝ}
    (hf : ContDiffAt ℝ ∞ f (0, t)) {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (C : ℝ) (y : E) (u : ℝ) :
    ContDiffAt ℝ ∞ (fun z : ℝ × ℝ ↦ inwardFirstJet f C y φ z.1 z.2) (u, t) := by
  have hc : ContDiffAt ℝ ∞ (fun t ↦ f (0, t)) t :=
    hf.comp t (contDiff_const.prodMk contDiff_id).contDiffAt
  have hv : ContDiffAt ℝ ∞ (fun t ↦ fderiv ℝ f (0, t) (1, 0)) t :=
    ((hf.fderiv_right (m := ∞) (by simp)).comp t
      (contDiff_const.prodMk contDiff_id).contDiffAt).clm_apply contDiffAt_const
  have hq : ContDiffAt ℝ ∞ (fun z : ℝ × ℝ ↦ z.1 * φ z.2) (u, t) :=
    contDiffAt_fst.mul (hφ.contDiffAt.comp (u, t) contDiffAt_snd)
  have hweight : ContDiffAt ℝ ∞ (fun z : ℝ × ℝ ↦ C * (z.1 * φ z.2) ^ 2) (u, t) :=
    contDiffAt_const.mul (hq.pow 2)
  exact ((contDiffAt_const.sub hweight).smul
    ((hc.comp (u, t) contDiffAt_snd).add (hq.smul (hv.comp (u, t) contDiffAt_snd)))).add
      (hweight.smul contDiffAt_const)

/-- A compact axis in a convex set admits one inward correction whose small-parameter
members stay in the set, uniformly over the compact axis. -/
private theorem exists_inwardFirstJet_eventually_mem {S : Set E} (hS : Convex ℝ S)
    (hSi : (interior S).Nonempty) {K : Set ℝ} (hK : IsCompact K)
    {f : ℝ × ℝ → E} (hf : ∀ t ∈ K, ContDiffAt ℝ ∞ f (0, t))
    (hfS : ∀ u t, t ∈ K → f (u, t) ∈ S)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) :
    ∃ C > 0, ∃ y ∈ interior S,
      ∀ᶠ u in 𝓝 (0 : ℝ), ∀ t ∈ K, inwardFirstJet f C y φ u t ∈ S := by
  obtain ⟨δ, hδ, B, hB, hrem⟩ :=
    hK.exists_pos_uniform_quadratic_remainder_compact_slice
      (fun t ht ↦ (hf t ht).of_le (by simp))
  obtain ⟨y, hy⟩ := hSi
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hy)
  let C := (B + 1) / r
  have hC : 0 < C := div_pos (by linarith) hr
  have hBC : B < C * r := by
    dsimp only [C]
    rw [div_mul_cancel₀ _ hr.ne']
    linarith
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hφ.continuous.continuousOn
  let L : ℝ := |M| + 1
  have hL : 0 < L := by dsimp [L]; positivity
  have hML : M ≤ L := (le_abs_self M).trans (by dsimp [L]; linarith)
  have hsmall : ∀ᶠ u : ℝ in 𝓝 0, |u| * L < δ ∧ C * (|u| * L) ^ 2 < 1 := by
    have h₁ : Tendsto (fun u : ℝ ↦ |u| * L) (𝓝 0) (𝓝 0) := by
      simpa using (continuous_abs.mul_const L).continuousAt.tendsto (x := (0 : ℝ))
    have hweight : Continuous (fun u : ℝ ↦ C * (|u| * L) ^ 2) :=
      continuous_const.mul ((continuous_abs.mul_const L).pow 2)
    have h₂ : Tendsto (fun u : ℝ ↦ C * (|u| * L) ^ 2) (𝓝 0) (𝓝 0) := by
      simpa only [abs_zero, zero_mul, zero_pow (by decide : 2 ≠ 0), mul_zero] using
        (hweight.continuousAt (x := (0 : ℝ))).tendsto
    exact (h₁.eventually (gt_mem_nhds hδ)).and
      (h₂.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)))
  refine ⟨C, hC, y, hy, hsmall.mono fun u hu t ht ↦ ?_⟩
  have hq : |u * φ t| ≤ |u| * L := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left ((hM t ht).trans hML) (abs_nonneg u)
  have hsq : (u * φ t) ^ 2 ≤ (|u| * L) ^ 2 := by
    simpa only [sq_abs] using
      (sq_le_sq₀ (abs_nonneg (u * φ t)) (mul_nonneg (abs_nonneg u) hL.le)).2 hq
  exact hS.affineFirstJet_mem (hfS (u * φ t) t ht) hball hC hBC
    ((mul_le_mul_of_nonneg_left hsq hC.le).trans hu.2.le)
    (hrem (u * φ t) (hq.trans_lt hu.1) t ht)

variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {a b : ℝ} {F : ℝ → ℝ → M} {x : M} {φ : ℝ → ℝ}

omit [IsManifold I ∞ M] in
/-- The corrected family of a localized transverse jet stays in the full extended-chart
target uniformly on a compact set of chart times. -/
private theorem exists_inwardFirstJet_eventually_mem_target
    {f : ℝ × ℝ → E} {K : Set ℝ} (hK : IsCompact K)
    (hf : ∀ t ∈ K, ContDiffAt ℝ ∞ f (0, t))
    (hfS : ∀ u t, t ∈ K → f (u, t) ∈ range I)
    (hf₀ : ∀ t ∈ K, f (0, t) ∈ (extChartAt I x).target) (hφ : ContDiff ℝ ∞ φ) :
    ∃ C : ℝ, ∃ y : E,
      ∀ᶠ u in 𝓝 (0 : ℝ), ∀ t ∈ K, inwardFirstJet f C y φ u t ∈ (extChartAt I x).target := by
  obtain ⟨C, _, y, _, hP⟩ := exists_inwardFirstJet_eventually_mem I.convex_range
    I.nonempty_interior hK hf hfS hφ
  let O := I.symm ⁻¹' (chartAt H x).target
  have hO : IsOpen O := (chartAt H x).open_target.preimage I.continuous_symm
  have hPO : ∀ᶠ u in 𝓝 (0 : ℝ), ∀ t ∈ K, inwardFirstJet f C y φ u t ∈ O := by
    refine hK.eventually_forall_mem_of_tendsto_prod_nhds (g := fun t ↦ f (0, t)) hO ?_ ?_
    · intro t ht
      simpa only [← nhds_prod_eq, inwardFirstJet_zero] using
        (contDiffAt_inwardFirstJet (hf t ht) hφ C y 0).continuousAt.tendsto
    · intro t ht
      rw [extChartAt_target] at hf₀
      exact (hf₀ t ht).1
  refine ⟨C, y, (hPO.and hP).mono fun u hu t ht ↦ ?_⟩
  rw [extChartAt_target]
  exact ⟨hu.1 t ht, hu.2 t ht⟩

/-- In extended coordinates, the corrected jet and the localized original curve have the
same velocity at the central time. -/
private theorem curveVelocity_inwardFirstJet
    {t C : ℝ} {y : E} (hft : ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I ∞
      (fun z : ℝ × ℝ ↦ F z.1 z.2) (0, t))
    (hchart : F 0 t ∈ (extChartAt I x).source)
    (hP : ∀ᶠ u in 𝓝 (0 : ℝ),
      inwardFirstJet (fun z : ℝ × ℝ ↦ extChartAt I x (F z.1 z.2)) C y φ u t ∈ range I) :
    curveVelocity I (fun u ↦ (extChartAt I x).symm
      (inwardFirstJet (fun z : ℝ × ℝ ↦ extChartAt I x (F z.1 z.2)) C y φ u t)) 0 =
      φ t • variationField I F t := by
  let f : ℝ × ℝ → E := fun z ↦ extChartAt I x (F z.1 z.2)
  let q : ℝ → ℝ := fun u ↦ u * φ t
  have hft' : ContDiffAt ℝ ∞ f (0, t) :=
    contMDiffAt_iff_contDiffAt.mp ((contMDiffAt_extChartAt'
      (by simpa only [← extChartAt_source I] using hchart)).comp _ hft)
  have hq : HasDerivAt q (φ t) 0 := by simpa [q] using (hasDerivAt_id (0 : ℝ)).mul_const (φ t)
  have hline : HasDerivAt (fun u ↦ (q u, t)) (φ t, 0) 0 :=
    hq.prodMk (hasDerivAt_const 0 t)
  have hQ : HasDerivAt (fun u ↦ f (q u, t)) (φ t • fderiv ℝ f (0, t) (1, 0)) 0 := by
    have hd := hft'.differentiableAt (by simp)
    have hsmul : (φ t, (0 : ℝ)) = φ t • ((1, 0) : ℝ × ℝ) := by simp [Prod.smul_mk]
    rw [hsmul] at hline
    simpa only [Function.comp_def, ContinuousLinearMap.map_smul] using
      (hd.hasFDerivAt.comp_hasDerivAt_of_eq 0 hline (by simp [q]))
  have hR : ∀ᶠ u in 𝓝 (0 : ℝ), f (q u, t) ∈ range I :=
    .of_forall fun _ ↦ ⟨_, rfl⟩
  have htarget : inwardFirstJet f C y φ 0 t ∈ (extChartAt I x).target := by
    simpa only [inwardFirstJet_zero] using (extChartAt I x).map_source hchart
  have hsame := (hasDerivAt_inwardFirstJet f C y φ t)
    |>.curveVelocity_extChartAt_symm_comp_eq_of_hasDerivAt (I := I) (a := x) hQ
      (by simp [q]) htarget hP hR
  have hgeo : ContMDiffAt 𝓘(ℝ, ℝ) I ∞ (fun u ↦ F (q u) t) 0 := by
    have hq' : ContDiff ℝ ∞ q := contDiff_id.mul contDiff_const
    exact hft.comp_of_eq (hq'.prodMk contDiff_const).contMDiff.contMDiffAt (by simp [q])
  have heq : ((extChartAt I x).symm ∘ fun u ↦ f (q u, t))
      =ᶠ[𝓝 (0 : ℝ)] fun u ↦ F (q u) t := by
    have h₀ : F (q 0) t ∈ (extChartAt I x).source := by simpa [q] using hchart
    filter_upwards [hgeo.continuousAt.eventually_mem ((isOpen_extChartAt_source x).mem_nhds h₀)]
      with u hu
    exact (extChartAt I x).left_inv hu
  have hFline : MDifferentiableAt 𝓘(ℝ, ℝ) I (fun u ↦ F u t) (q 0) := by
    simpa only [q, zero_mul, Function.comp_def] using
      (hft.comp 0 (contDiff_prodMk_left t).contMDiff.contMDiffAt).mdifferentiableAt (by simp)
  have hq₀ : q 0 = 0 := zero_mul _
  have hchain := curveVelocity_comp hq hFline
  rw [hq₀] at hchain
  simpa only [variationField_apply, Function.comp_def] using
    hsame.trans ((heq.curveVelocity_eq (I := I)).trans hchain)

/-- A smooth fixed-endpoint variation has a localized representative whose nearby curves
are all smooth along the parameter interval. Its variation field is the original field
multiplied by the smooth profile supported in one chart. The model may have boundary. -/
theorem IsFixedEndpointVariation.exists_localized_smooth_slices
    (hF : IsFixedEndpointVariation I ∞ F a b)
    {J K : Set ℝ} (hJo : IsOpen J) (hK : IsCompact K) (hJK : J ⊆ K)
    (hKab : K ⊆ uIoo a b) (hchart : ∀ t ∈ K, F 0 t ∈ (extChartAt I x).source)
    (hφ : ContDiff ℝ ∞ φ) (hφJ : tsupport φ ⊆ J) :
    ∃ G : ℝ → ℝ → M, G 0 = F 0 ∧ IsFixedEndpointVariation I ∞ G a b ∧
      (∀ᶠ u in 𝓝 (0 : ℝ), ∀ t ∈ uIcc a b, ContMDiffAt 𝓘(ℝ, ℝ) I ∞ (G u) t) ∧
      ∀ t ∈ uIcc a b, variationField I G t = φ t • variationField I F t := by
  classical
  let f : ℝ × ℝ → E := fun z ↦ extChartAt I x (F z.1 z.2)
  have hf (t : ℝ) (ht : t ∈ K) : ContDiffAt ℝ ∞ f (0, t) :=
    contMDiffAt_iff_contDiffAt.mp
      ((contMDiffAt_extChartAt' (by simpa only [← extChartAt_source I] using hchart t ht)).comp _
        (hF.contMDiffAt t (uIoo_subset_uIcc_self (hKab ht))))
  obtain ⟨C, y, hP⟩ := exists_inwardFirstJet_eventually_mem_target hK hf
    (fun _ _ _ ↦ ⟨_, rfl⟩) (fun t ht ↦ (extChartAt I x).map_source (hchart t ht)) hφ
  let P := inwardFirstJet f C y φ
  obtain ⟨U, hU, hUo, h0⟩ := _root_.mem_nhds_iff.mp (Filter.eventually_mem_set.mpr hP)
  let G (u t : ℝ) := if t ∈ J then (extChartAt I x).symm (P u t) else F 0 t
  have hGflat (u t : ℝ) (ht : φ t = 0) : G u t = F 0 t := by
    by_cases hj : t ∈ J
    · simpa [G, hj, P, inwardFirstJet, ht, f] using (extChartAt I x).left_inv (hchart t (hJK hj))
    · simp [G, hj]
  have hG₀ : G 0 = F 0 := by
    funext t
    by_cases hj : t ∈ J
    · simpa only [G, ite_eq_left hj, P, inwardFirstJet_zero, f] using
        (extChartAt I x).left_inv (hchart t (hJK hj))
    · simp [G, hj]
  have hjoint (u t : ℝ) (hu : u ∈ U) (ht : t ∈ uIcc a b) :
      ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I ∞ (fun z : ℝ × ℝ ↦ G z.1 z.2) (u, t) := by
    by_cases hj : t ∈ J
    · have hrange : ∀ᶠ z : ℝ × ℝ in 𝓝 (u, t), P z.1 z.2 ∈ range I := by
        filter_upwards [(hUo.prod hJo).mem_nhds ⟨hu, hj⟩] with z hz
        exact extChartAt_target_subset_range x (hU hz.1 z.2 (hJK hz.2))
      refine ((contDiffAt_inwardFirstJet (hf t (hJK hj)) hφ C y u)
        |>.contMDiffAt_extChartAt_symm_comp_of_eventually_mem_range hrange
          (hU hu t (hJK hj))).congr_of_eventuallyEq ?_
      filter_upwards [(isOpen_univ.prod hJo).mem_nhds ⟨mem_univ u, hj⟩] with z hz
      exact ite_eq_left hz.2
    · have hnot : t ∉ tsupport φ := fun h ↦ hj (hφJ h)
      have hcentral : ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I ∞ (fun z : ℝ × ℝ ↦ F 0 z.2) (u, t) :=
        (hF.contMDiffAt_apply_zero ht).comp (u, t) contDiff_snd.contMDiff.contMDiffAt
      refine hcentral.congr_of_eventuallyEq ?_
      filter_upwards [(isOpen_univ.prod (isClosed_tsupport φ).isOpen_compl).mem_nhds
        ⟨mem_univ u, hnot⟩] with z hz
      exact hGflat z.1 z.2 (notMem_tsupport_iff_eventuallyEq.mp hz.2 |>.eq_of_nhds)
  have hend (u t : ℝ) (ht : t ∉ uIoo a b) : G u t = F 0 t :=
    ite_eq_right fun h ↦ ht (hKab (hJK h))
  refine ⟨G, hG₀, ⟨fun t ht ↦ hjoint _ t h0 ht, ?_, ?_⟩, ?_, ?_⟩
  · exact .of_forall fun u ↦ (hend u a left_notMem_uIoo).trans
      (congrFun hG₀ a).symm
  · exact .of_forall fun u ↦ (hend u b right_notMem_uIoo).trans
      (congrFun hG₀ b).symm
  · filter_upwards [hUo.mem_nhds h0] with u hu t ht
    exact (hjoint u t hu ht).comp t (contDiff_prodMk_right u).contMDiff.contMDiffAt
  · intro t ht
    by_cases hj : t ∈ J
    · have hl : (fun u ↦ G u t) = (fun u ↦ (extChartAt I x).symm (P u t)) :=
        funext fun _ ↦ ite_eq_left hj
      have hvel := curveVelocity_inwardFirstJet (hF.contMDiffAt t ht) (hchart t (hJK hj))
        (C := C) (y := y) (φ := φ)
        (hP.mono fun _ hu ↦ extChartAt_target_subset_range x (hu t (hJK hj)))
      exact (variationField_apply (I := I) G t).trans <|
        ((Filter.EventuallyEq.of_eq hl).curveVelocity_eq (I := I) (t := 0)).trans hvel
    · have hφt : φ t = 0 := Function.notMem_support.mp fun h ↦ hj (hφJ (subset_tsupport φ h))
      rw [hφt, zero_smul]
      exact variationField_eq_zero (.of_forall fun u ↦ (hGflat u t hφt).trans
        (congrFun hG₀ t).symm)

end TauCeti.Manifold
