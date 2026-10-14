/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.ThricePuncturedSphere.FilledCover.Basic
public import TauCeti.AlgebraicTopology.ThricePuncturedSphere.SegmentComponents

/-!
# Edges in a filled cover

For a finite cover of the thrice-punctured sphere, the connected components over the open
segment `(0, 1)` are the open edges of its dessin. This file regards those components as subsets
of the filled cover and identifies their black and white endpoints. In particular, the added
point over a component at `0` or `1` lies in the closure of an edge exactly when the corresponding
monodromy cycle contains that edge.

## Main definitions

* `FilledCover.edge`: the open edge indexed by a sheet, included in the filled cover.

## Main results

* `FilledCover.center_overZero_mem_closure_edge_iff`: the black endpoints of an edge are described
  by the cycles of `σ0`.
* `FilledCover.center_overOne_mem_closure_edge_iff`: the white endpoints of an edge are described
  by the cycles of `σ1`.
-/

public section

noncomputable section

namespace TauCeti

open Complex Equiv Equiv.Perm FilledPoint Filter Set ThricePuncturedSphere Topology

namespace FilledCover

local notation "𝔻" => Set.Elem (Metric.ball (0 : ℂ) 1)
local notation "𝔻*" => Set.Elem (Metric.ball (0 : ℂ) 1 \ {0})

variable {E : Type*} [TopologicalSpace E] {p : E → ThricePuncturedSphere}

/-- The open edge of the filled cover indexed by `i`: the connected component indexed by `i` of
the preimage of `(0, 1)`, included into the filled surface. -/
def edge {n : ℕ} (hp : IsCoveringMap p) (ν : p ⁻¹' {basePt} ≃ Fin n)
    (i : Fin n) : Set (FilledCover p) :=
  PunctureFilling.incl (chart p) ''
    {x | ∃ hx : p x ∈ unitSegment,
      ConnectedComponents.mk ⟨x, hx⟩ = hp.finEquivConnectedComponentsUnitSegment ν i}

/-- Membership in an open edge, expressed using its connected-component label before inclusion in
the filled cover. -/
theorem mem_edge_iff {n : ℕ} (hp : IsCoveringMap p) (ν : p ⁻¹' {basePt} ≃ Fin n)
    (i : Fin n) (z : FilledCover p) :
    z ∈ edge hp ν i ↔ ∃ (x : E) (hx : p x ∈ unitSegment),
      ConnectedComponents.mk ⟨x, hx⟩ = hp.finEquivConnectedComponentsUnitSegment ν i ∧
        PunctureFilling.incl (chart p) x = z := by
  simp only [edge, mem_image, mem_ofPred_eq]
  constructor
  · rintro ⟨x, ⟨hx, hi⟩, rfl⟩
    exact ⟨x, hx, hi, rfl⟩
  · rintro ⟨x, hx, hi, rfl⟩
    exact ⟨x, ⟨hx, hi⟩, rfl⟩

/-- The radial sequence from `w` towards the missing centre of the punctured disc. -/
private def radialPoint (w : 𝔻*) (k : ℕ) : 𝔻* :=
  ⟨(1 / (k + 1 : ℝ)) • (w : ℂ), by
    have hk : 0 < (k + 1 : ℝ) := by positivity
    have hscale : 0 < 1 / (k + 1 : ℝ) := by positivity
    constructor
    · rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos hscale]
      have hw := (mem_ball_zero_iff.1 w.2.1)
      have hle : 1 / (k + 1 : ℝ) ≤ 1 := by
        rw [div_le_one hk]
        norm_num
      nlinarith [norm_nonneg (w : ℂ)]
    · simp only [mem_singleton_iff]
      exact smul_ne_zero (ne_of_gt hscale) w.2.2⟩

@[simp]
private theorem coe_radialPoint (w : 𝔻*) (k : ℕ) :
    (radialPoint w k : ℂ) = (1 / (k + 1 : ℝ)) • (w : ℂ) :=
  by simp [radialPoint]

private theorem tendsto_radialPoint_zero (w : 𝔻*) :
    Tendsto (fun k ↦ (⟨radialPoint w k, (radialPoint w k).2.1⟩ : 𝔻)) atTop (𝓝 0) := by
  rw [tendsto_subtype_rng]
  convert (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℂ)).mul_const (w : ℂ) using 1 <;>
    simp [coe_radialPoint]

/-- The radial path from a point of the radial sequence back to its starting point. -/
private def radialPath (w : 𝔻*) (k : ℕ) : Path (radialPoint w k) w where
  toFun t :=
    ⟨(1 / (k + 1 : ℝ) + (t : ℝ) * (1 - 1 / (k + 1 : ℝ))) • (w : ℂ), by
      have hk : 0 < (k + 1 : ℝ) := by positivity
      have hrpos : 0 < 1 / (k + 1 : ℝ) := by positivity
      have hrle : 1 / (k + 1 : ℝ) ≤ 1 := by
        rw [div_le_one hk]
        norm_num
      have ht0 : 0 ≤ (t : ℝ) := t.2.1
      have ht1 : (t : ℝ) ≤ 1 := t.2.2
      have hspos : 0 < 1 / (k + 1 : ℝ) + (t : ℝ) * (1 - 1 / (k + 1 : ℝ)) := by
        nlinarith
      have hsle : 1 / (k + 1 : ℝ) + (t : ℝ) * (1 - 1 / (k + 1 : ℝ)) ≤ 1 := by
        nlinarith
      constructor
      · rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos hspos]
        have hw := mem_ball_zero_iff.1 w.2.1
        nlinarith [norm_nonneg (w : ℂ)]
      · simp only [mem_singleton_iff]
        exact smul_ne_zero (ne_of_gt hspos) w.2.2⟩
  continuous_toFun := by fun_prop
  source' := by
    ext
    simp [radialPoint]
  target' := by
    ext
    simp

private theorem coe_coord_of_eq_zero {q : Puncture} (hq : q = Puncture.zero)
    (z : q.neighborhood) : (q.coord z : ℂ) = 2 * (z : ThricePuncturedSphere) := by
  subst q
  exact Puncture.coe_coord_zero z

private theorem coe_coord_of_eq_one {q : Puncture} (hq : q = Puncture.one)
    (z : q.neighborhood) : (q.coord z : ℂ) = 2 * (1 - (z : ThricePuncturedSphere)) := by
  subst q
  exact Puncture.coe_coord_one z

/-- Radial motion in a filling chart over `0` stays above the open real segment if its starting
point does. -/
private theorem chart_radialPath_mem_unitSegment_zero (hp : IsCoveringMap p)
    (hfin : Finite (p ⁻¹' {basePt}))
    (b : ConnectedComponents (p ⁻¹' puncturedNeighborhoodZero)) (w : 𝔻*)
    (hw : p (chart p (overZero p b) w) ∈ unitSegment) (k : ℕ) (t : unitInterval) :
    p (chart p (overZero p b) (radialPath w k t)) ∈ unitSegment := by
  let s : ℝ := 1 / (k + 1 : ℝ) + (t : ℝ) * (1 - 1 / (k + 1 : ℝ))
  have hk : 0 < (k + 1 : ℝ) := by positivity
  have hrpos : 0 < 1 / (k + 1 : ℝ) := by positivity
  have hrle : 1 / (k + 1 : ℝ) ≤ 1 := by
    rw [div_le_one hk]
    norm_num
  have hspos : 0 < s := by
    dsimp [s]
    nlinarith [t.2.1, t.2.2]
  have hsle : s ≤ 1 := by
    dsimp [s]
    nlinarith [t.2.1, t.2.2]
  let e := degree p (overZero p b)
  obtain ⟨hu, -, hcoordu⟩ :=
    exists_coe_coord_chart_eq_pow hp hfin (overZero p b) (radialPath w k t)
  obtain ⟨hw0, -, hcoordw⟩ :=
    exists_coe_coord_chart_eq_pow hp hfin (overZero p b) w
  have hq : (sigmaEquiv p (overZero p b)).1 = Puncture.zero :=
    congrArg Sigma.fst (sigmaEquiv_overZero (p := p) b)
  have hcoordu' : 2 * (p (chart p (overZero p b) (radialPath w k t)) : ℂ) =
      ((radialPath w k t : 𝔻*) : ℂ) ^ e :=
    (coe_coord_of_eq_zero hq ⟨_, hu⟩).symm.trans hcoordu
  have hcoordw' : 2 * (p (chart p (overZero p b) w) : ℂ) = (w : ℂ) ^ e :=
    (coe_coord_of_eq_zero hq ⟨_, hw0⟩).symm.trans hcoordw
  have hpath : ((radialPath w k t : 𝔻*) : ℂ) = s • (w : ℂ) := by
    simp [radialPath, s]
  have hpath_mul : ((radialPath w k t : 𝔻*) : ℂ) = (s : ℂ) * (w : ℂ) := by
    rw [hpath, real_smul]
  have hmap : (p (chart p (overZero p b) (radialPath w k t)) : ℂ) =
      (s ^ e) • (p (chart p (overZero p b) w) : ℂ) := by
    have htwo_ne : (2 : ℂ) ≠ 0 := by norm_num
    apply mul_left_cancel₀ htwo_ne
    rw [hcoordu', hpath_mul]
    rw [mul_pow, ← hcoordw']
    rw [real_smul]
    rw [ofReal_pow]
    ring
  rw [mem_unitSegment] at hw ⊢
  rw [hmap]
  have hspowpos : 0 < s ^ e := pow_pos hspos _
  have hspowle : s ^ e ≤ 1 := by
    exact pow_le_one₀ (le_of_lt hspos) hsle
  constructor
  · rw [Complex.smul_im, hw.1, smul_zero]
  · rw [Complex.smul_re, smul_eq_mul]
    constructor <;> nlinarith [hw.2.1, hw.2.2]

/-- Radial motion in a filling chart over `1` stays above the open real segment if its starting
point does. -/
private theorem chart_radialPath_mem_unitSegment_one (hp : IsCoveringMap p)
    (hfin : Finite (p ⁻¹' {basePt}))
    (b : ConnectedComponents (p ⁻¹' puncturedNeighborhoodOne)) (w : 𝔻*)
    (hw : p (chart p (overOne p b) w) ∈ unitSegment) (k : ℕ) (t : unitInterval) :
    p (chart p (overOne p b) (radialPath w k t)) ∈ unitSegment := by
  let s : ℝ := 1 / (k + 1 : ℝ) + (t : ℝ) * (1 - 1 / (k + 1 : ℝ))
  have hk : 0 < (k + 1 : ℝ) := by positivity
  have hrpos : 0 < 1 / (k + 1 : ℝ) := by positivity
  have hrle : 1 / (k + 1 : ℝ) ≤ 1 := by
    rw [div_le_one hk]
    norm_num
  have hspos : 0 < s := by
    dsimp [s]
    nlinarith [t.2.1, t.2.2]
  have hsle : s ≤ 1 := by
    dsimp [s]
    nlinarith [t.2.1, t.2.2]
  let e := degree p (overOne p b)
  obtain ⟨hu, -, hcoordu⟩ :=
    exists_coe_coord_chart_eq_pow hp hfin (overOne p b) (radialPath w k t)
  obtain ⟨hw1, -, hcoordw⟩ :=
    exists_coe_coord_chart_eq_pow hp hfin (overOne p b) w
  have hq : (sigmaEquiv p (overOne p b)).1 = Puncture.one :=
    congrArg Sigma.fst (sigmaEquiv_overOne (p := p) b)
  have hcoordu' : 2 * (1 - (p (chart p (overOne p b) (radialPath w k t)) : ℂ)) =
      ((radialPath w k t : 𝔻*) : ℂ) ^ e :=
    (coe_coord_of_eq_one hq ⟨_, hu⟩).symm.trans hcoordu
  have hcoordw' : 2 * (1 - (p (chart p (overOne p b) w) : ℂ)) = (w : ℂ) ^ e :=
    (coe_coord_of_eq_one hq ⟨_, hw1⟩).symm.trans hcoordw
  have hpath : ((radialPath w k t : 𝔻*) : ℂ) = s • (w : ℂ) := by
    simp [radialPath, s]
  have hpath_mul : ((radialPath w k t : 𝔻*) : ℂ) = (s : ℂ) * (w : ℂ) := by
    rw [hpath, real_smul]
  have hgap : 1 - (p (chart p (overOne p b) (radialPath w k t)) : ℂ) =
      (s ^ e) • (1 - (p (chart p (overOne p b) w) : ℂ)) := by
    have htwo_ne : (2 : ℂ) ≠ 0 := by norm_num
    apply mul_left_cancel₀ htwo_ne
    rw [hcoordu', hpath_mul]
    rw [mul_pow, ← hcoordw', real_smul, ofReal_pow]
    ring
  have hmap : (p (chart p (overOne p b) (radialPath w k t)) : ℂ) =
      1 - (s ^ e) • (1 - (p (chart p (overOne p b) w) : ℂ)) := by
    linear_combination -hgap
  rw [mem_unitSegment] at hw ⊢
  rw [hmap]
  have hspowpos : 0 < s ^ e := pow_pos hspos _
  have hspowle : s ^ e ≤ 1 := by
    exact pow_le_one₀ (le_of_lt hspos) hsle
  constructor
  · simp only [Complex.sub_im, Complex.one_im, Complex.smul_im, hw.1, sub_zero, smul_zero]
  · simp only [Complex.sub_re, Complex.one_re, Complex.smul_re, smul_eq_mul]
    constructor
    · have hmul := mul_le_mul_of_nonneg_right hspowle (by linarith [hw.2.2] :
          0 ≤ 1 - (p (chart p (overOne p b) w) : ℂ).re)
      nlinarith [hw.2.1]
    · have hmul := mul_pos hspowpos (by linarith [hw.2.2] :
          0 < 1 - (p (chart p (overOne p b) w) : ℂ).re)
      linarith

/-- An added point over `0` is a black endpoint of an edge exactly when its punctured-neighborhood
component is the cycle of that edge under `σ0`. -/
theorem center_overZero_mem_closure_edge_iff {n : ℕ} (hp : IsCoveringMap p)
    (ν : p ⁻¹' {basePt} ≃ Fin n) (i : Fin n)
    (b : ConnectedComponents (p ⁻¹' puncturedNeighborhoodZero)) :
    PunctureFilling.center (chart p) (overZero p b) ∈ closure (edge hp ν i) ↔
      b = hp.sameCycleQuotientσ0EquivConnectedComponents ν (Quotient.mk _ i) := by
  let hfin : Finite (p ⁻¹' {basePt}) := .of_equiv _ ν.symm
  constructor
  · intro hclosure
    let U := PunctureFilling.disc (chart p) (overZero p b) ''
      {z : 𝔻 | ‖(z : ℂ)‖ < 1}
    have hU : U ∈ 𝓝 (PunctureFilling.center (chart p) (overZero p b)) := by
      apply (PunctureFilling.hasBasis_nhds_center
        (fun j ↦ (isOpenEmbedding_chart hp hfin j).continuous)
        (isOpenEmbedding_chart hp hfin (overZero p b))).mem_iff.2
      exact ⟨1, zero_lt_one, Subset.rfl⟩
    obtain ⟨z, hzU, hzedge⟩ := (mem_closure_iff_nhds.1 hclosure U hU)
    obtain ⟨d, -, rfl⟩ := hzU
    obtain ⟨x, hx, hi, hdisc⟩ := (mem_edge_iff hp ν i _).1 hzedge
    obtain ⟨w, -, hchart⟩ := PunctureFilling.disc_eq_incl_iff.1 hdisc.symm
    have hxrange : x ∈ range (chart p (overZero p b)) := ⟨w, hchart⟩
    rw [range_chart hp hfin, sigmaEquiv_overZero] at hxrange
    obtain ⟨hx0, hb⟩ := hxrange
    exact (hp.exists_common_point_iff_eq_sameCycleQuotientσ0 ν i b).1
      ⟨x, hx, hx0, hi, hb⟩
  · intro hb
    obtain ⟨x, hx, hx0, hi, hb'⟩ :=
      (hp.exists_common_point_iff_eq_sameCycleQuotientσ0 ν i b).2 hb
    have hxrange : x ∈ range (chart p (overZero p b)) := by
      rw [range_chart hp hfin, sigmaEquiv_overZero]
      exact ⟨hx0, hb'⟩
    obtain ⟨w, rfl⟩ := hxrange
    let f : ℕ → FilledCover p := PunctureFilling.disc (chart p) (overZero p b) ∘
      fun k ↦ (⟨radialPoint w k, (radialPoint w k).2.1⟩ : 𝔻)
    refine mem_closure_of_tendsto (f := f) (b := atTop) ?_ (.of_forall fun k ↦ ?_)
    · have hlim := (PunctureFilling.continuous_disc (φ := chart p)
        (overZero p b)).continuousAt.tendsto.comp (tendsto_radialPoint_zero w)
      simpa only [f, PunctureFilling.disc_zero] using hlim
    · have hfk : f k = PunctureFilling.incl (chart p)
          (chart p (overZero p b) (radialPoint w k)) := by
        simp only [f, Function.comp_apply]
        exact PunctureFilling.disc_inclusion (overZero p b) (radialPoint w k)
      rw [hfk]
      apply (mem_edge_iff hp ν i _).2
      have hy : p (chart p (overZero p b) (radialPoint w k)) ∈ unitSegment := by
        simpa using chart_radialPath_mem_unitSegment_zero hp hfin b w hx k 0
      refine ⟨_, hy, ?_, rfl⟩
      have hjoined : JoinedIn (p ⁻¹' unitSegment)
          (chart p (overZero p b) (radialPoint w k)) (chart p (overZero p b) w) :=
        ⟨(radialPath w k).map (isOpenEmbedding_chart hp hfin _).continuous,
          fun t ↦ chart_radialPath_mem_unitSegment_zero hp hfin b w hx k t⟩
      have hcomponent : ConnectedComponents.mk
          (⟨chart p (overZero p b) (radialPoint w k), hy⟩ : p ⁻¹' unitSegment) =
          ConnectedComponents.mk ⟨chart p (overZero p b) w, hx⟩ := by
        rw [ConnectedComponents.coe_eq_coe]
        exact connectedComponent_eq
          (pathComponent_subset_component _ hjoined.joined_subtype)
      exact hcomponent.trans hi

/-- An added point over `1` is a white endpoint of an edge exactly when its punctured-neighborhood
component is the cycle of that edge under `σ1`. -/
theorem center_overOne_mem_closure_edge_iff {n : ℕ} (hp : IsCoveringMap p)
    (ν : p ⁻¹' {basePt} ≃ Fin n) (i : Fin n)
    (b : ConnectedComponents (p ⁻¹' puncturedNeighborhoodOne)) :
    PunctureFilling.center (chart p) (overOne p b) ∈ closure (edge hp ν i) ↔
      b = hp.sameCycleQuotientσ1EquivConnectedComponents ν (Quotient.mk _ i) := by
  let hfin : Finite (p ⁻¹' {basePt}) := .of_equiv _ ν.symm
  constructor
  · intro hclosure
    let U := PunctureFilling.disc (chart p) (overOne p b) ''
      {z : 𝔻 | ‖(z : ℂ)‖ < 1}
    have hU : U ∈ 𝓝 (PunctureFilling.center (chart p) (overOne p b)) := by
      apply (PunctureFilling.hasBasis_nhds_center
        (fun j ↦ (isOpenEmbedding_chart hp hfin j).continuous)
        (isOpenEmbedding_chart hp hfin (overOne p b))).mem_iff.2
      exact ⟨1, zero_lt_one, Subset.rfl⟩
    obtain ⟨z, hzU, hzedge⟩ := (mem_closure_iff_nhds.1 hclosure U hU)
    obtain ⟨d, -, rfl⟩ := hzU
    obtain ⟨x, hx, hi, hdisc⟩ := (mem_edge_iff hp ν i _).1 hzedge
    obtain ⟨w, -, hchart⟩ := PunctureFilling.disc_eq_incl_iff.1 hdisc.symm
    have hxrange : x ∈ range (chart p (overOne p b)) := ⟨w, hchart⟩
    rw [range_chart hp hfin, sigmaEquiv_overOne] at hxrange
    obtain ⟨hx1, hb⟩ := hxrange
    exact (hp.exists_common_point_iff_eq_sameCycleQuotientσ1 ν i b).1
      ⟨x, hx, hx1, hi, hb⟩
  · intro hb
    obtain ⟨x, hx, hx1, hi, hb'⟩ :=
      (hp.exists_common_point_iff_eq_sameCycleQuotientσ1 ν i b).2 hb
    have hxrange : x ∈ range (chart p (overOne p b)) := by
      rw [range_chart hp hfin, sigmaEquiv_overOne]
      exact ⟨hx1, hb'⟩
    obtain ⟨w, rfl⟩ := hxrange
    let f : ℕ → FilledCover p := PunctureFilling.disc (chart p) (overOne p b) ∘
      fun k ↦ (⟨radialPoint w k, (radialPoint w k).2.1⟩ : 𝔻)
    refine mem_closure_of_tendsto (f := f) (b := atTop) ?_ (.of_forall fun k ↦ ?_)
    · have hlim := (PunctureFilling.continuous_disc (φ := chart p)
        (overOne p b)).continuousAt.tendsto.comp (tendsto_radialPoint_zero w)
      simpa only [f, PunctureFilling.disc_zero] using hlim
    · have hfk : f k = PunctureFilling.incl (chart p)
          (chart p (overOne p b) (radialPoint w k)) := by
        simp only [f, Function.comp_apply]
        exact PunctureFilling.disc_inclusion (overOne p b) (radialPoint w k)
      rw [hfk]
      apply (mem_edge_iff hp ν i _).2
      have hy : p (chart p (overOne p b) (radialPoint w k)) ∈ unitSegment := by
        simpa using chart_radialPath_mem_unitSegment_one hp hfin b w hx k 0
      refine ⟨_, hy, ?_, rfl⟩
      have hjoined : JoinedIn (p ⁻¹' unitSegment)
          (chart p (overOne p b) (radialPoint w k)) (chart p (overOne p b) w) :=
        ⟨(radialPath w k).map (isOpenEmbedding_chart hp hfin _).continuous,
          fun t ↦ chart_radialPath_mem_unitSegment_one hp hfin b w hx k t⟩
      have hcomponent : ConnectedComponents.mk
          (⟨chart p (overOne p b) (radialPoint w k), hy⟩ : p ⁻¹' unitSegment) =
          ConnectedComponents.mk ⟨chart p (overOne p b) w, hx⟩ := by
        rw [ConnectedComponents.coe_eq_coe]
        exact connectedComponent_eq
          (pathComponent_subset_component _ hjoined.joined_subtype)
      exact hcomponent.trans hi

end FilledCover

end TauCeti
