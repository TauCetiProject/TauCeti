/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.ThricePuncturedSphere.FilledCover.Basic
public import TauCeti.AlgebraicTopology.ThricePuncturedSphere.SegmentComponents
public import TauCeti.AlgebraicTopology.ThricePuncturedSphere.UpperHalfPlaneComponents

/-!
# Edges and positive triangles in a filled cover

For a finite cover of the thrice-punctured sphere, the connected components over the open
segment `(0, 1)` are the open edges of its dessin. This file regards those components as subsets
of the filled cover and identifies their black and white endpoints. In particular, the added
point over a component at `0` or `1` lies in the closure of an edge exactly when the corresponding
monodromy cycle contains that edge.

The connected components over the open upper half-plane, the positive triangles of the dessin, are
likewise regarded as subsets of the filled cover. They are the cells that turn around the added
points over `∞`, which no edge reaches.

## Main definitions

* `FilledCover.edge`: the open edge indexed by a sheet, included in the filled cover.
* `FilledCover.upperTriangle`: the open positive triangle indexed by a sheet, included in the
  filled cover.

## Main results

* `FilledCover.exists_mk_eq_of_coe_eq_ofReal_mul`: in a chart in which the cover is a power map
  and `(0, 1)` is the positive real axis, radial motion stays on one edge.
* `FilledCover.center_overZero_mem_closure_edge_iff`: the black endpoints of an edge are described
  by the cycles of `σ0`.
* `FilledCover.center_overOne_mem_closure_edge_iff`: the white endpoints of an edge are described
  by the cycles of `σ1`.
* `FilledCover.center_notMem_edge`, `FilledCover.center_notMem_upperTriangle`: the added points
  lie on no edge and in no positive triangle.
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

/-- A point of `E` lies on the open edge indexed by `i` exactly when it lies over `(0, 1)`, in the
connected component of `p ⁻¹' (0, 1)` indexed by `i`. -/
@[simp]
theorem incl_mem_edge_iff {n : ℕ} (hp : IsCoveringMap p) (ν : p ⁻¹' {basePt} ≃ Fin n)
    (i : Fin n) (x : E) :
    PunctureFilling.incl (chart p) x ∈ edge hp ν i ↔ ∃ hx : p x ∈ unitSegment,
      ConnectedComponents.mk ⟨x, hx⟩ = hp.finEquivConnectedComponentsUnitSegment ν i := by
  simp only [edge, PunctureFilling.incl_injective.mem_set_image, mem_ofPred_eq]

/-- The added points of the filled cover lie on no edge. -/
theorem center_notMem_edge {n : ℕ} (hp : IsCoveringMap p) (ν : p ⁻¹' {basePt} ≃ Fin n)
    (i : FilledPoint p) (m : Fin n) : PunctureFilling.center (chart p) i ∉ edge hp ν m := by
  intro h
  obtain ⟨x, -, -, hx⟩ := (mem_edge_iff hp ν m _).1 h
  exact PunctureFilling.incl_ne_center x i hx

/-- The open positive triangle of the filled cover indexed by `i`: the connected component indexed
by `i` of the preimage of the upper half-plane, included into the filled surface. -/
def upperTriangle {n : ℕ} (hp : IsCoveringMap p) (ν : p ⁻¹' {basePt} ≃ Fin n)
    (i : Fin n) : Set (FilledCover p) :=
  PunctureFilling.incl (chart p) ''
    {x | ∃ hx : p x ∈ upperHalfPlane,
      ConnectedComponents.mk ⟨x, hx⟩ = hp.finEquivConnectedComponentsUpperHalfPlane ν i}

/-- Membership in an open positive triangle, expressed using its connected-component label before
inclusion in the filled cover. -/
theorem mem_upperTriangle_iff {n : ℕ} (hp : IsCoveringMap p) (ν : p ⁻¹' {basePt} ≃ Fin n)
    (i : Fin n) (z : FilledCover p) :
    z ∈ upperTriangle hp ν i ↔ ∃ (x : E) (hx : p x ∈ upperHalfPlane),
      ConnectedComponents.mk ⟨x, hx⟩ = hp.finEquivConnectedComponentsUpperHalfPlane ν i ∧
        PunctureFilling.incl (chart p) x = z := by
  simp only [upperTriangle, mem_image, mem_ofPred_eq]
  constructor
  · rintro ⟨x, ⟨hx, hi⟩, rfl⟩
    exact ⟨x, hx, hi, rfl⟩
  · rintro ⟨x, hx, hi, rfl⟩
    exact ⟨x, ⟨hx, hi⟩, rfl⟩

/-- A point of `E` lies in the open positive triangle indexed by `i` exactly when it lies over the
upper half-plane, in the connected component of its preimage indexed by `i`. -/
@[simp]
theorem incl_mem_upperTriangle_iff {n : ℕ} (hp : IsCoveringMap p) (ν : p ⁻¹' {basePt} ≃ Fin n)
    (i : Fin n) (x : E) :
    PunctureFilling.incl (chart p) x ∈ upperTriangle hp ν i ↔ ∃ hx : p x ∈ upperHalfPlane,
      ConnectedComponents.mk ⟨x, hx⟩ = hp.finEquivConnectedComponentsUpperHalfPlane ν i := by
  simp only [upperTriangle, PunctureFilling.incl_injective.mem_set_image, mem_ofPred_eq]

/-- The added points of the filled cover lie in no positive triangle. -/
theorem center_notMem_upperTriangle {n : ℕ} (hp : IsCoveringMap p)
    (ν : p ⁻¹' {basePt} ≃ Fin n) (i : FilledPoint p) (m : Fin n) :
    PunctureFilling.center (chart p) i ∉ upperTriangle hp ν m := by
  intro h
  obtain ⟨x, -, -, hx⟩ := (mem_upperTriangle_iff hp ν m _).1 h
  exact PunctureFilling.incl_ne_center x i hx

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

omit [TopologicalSpace E] in
/-- Along a map `φ : 𝔻* → E` in which `p` is `w ↦ w ^ e` in the coordinate of `D_q*`, and when
`(0, 1)` is the positive real axis in that coordinate, a point of `𝔻*` goes over `(0, 1)` exactly
when its `e`-th power is a positive real. -/
theorem mem_unitSegment_iff_of_coe_coord_eq_pow {q : Puncture} {φ : 𝔻* → E} {e : ℕ}
    (hφq : ∀ w, ∃ hw : p (φ w) ∈ q.neighborhood, (q.coord ⟨p (φ w), hw⟩ : ℂ) = (w : ℂ) ^ e)
    (hseg : ∀ z (hz : z ∈ q.neighborhood),
      z ∈ unitSegment ↔ (q.coord ⟨z, hz⟩ : ℂ).im = 0 ∧ 0 < (q.coord ⟨z, hz⟩ : ℂ).re)
    (w : 𝔻*) : p (φ w) ∈ unitSegment ↔ ((w : ℂ) ^ e).im = 0 ∧ 0 < ((w : ℂ) ^ e).re := by
  obtain ⟨hw, h⟩ := hφq w
  rw [hseg _ hw, h]

/-- **Radial motion does not change the edge.** Along a continuous map `φ : 𝔻* → E` in which `p`
is `w ↦ w ^ e` in the coordinate of `D_q*`, where `(0, 1)` is the positive real axis, scaling a
point of `𝔻*` by a positive real keeps its image over `(0, 1)` and in the same component of
`p ⁻¹' (0, 1)`. -/
theorem exists_mk_eq_of_coe_eq_ofReal_mul {q : Puncture} {φ : 𝔻* → E} {e : ℕ}
    (hφ : Continuous φ)
    (hφq : ∀ w, ∃ hw : p (φ w) ∈ q.neighborhood, (q.coord ⟨p (φ w), hw⟩ : ℂ) = (w : ℂ) ^ e)
    (hseg : ∀ z (hz : z ∈ q.neighborhood),
      z ∈ unitSegment ↔ (q.coord ⟨z, hz⟩ : ℂ).im = 0 ∧ 0 < (q.coord ⟨z, hz⟩ : ℂ).re)
    {w w' : 𝔻*} {s : ℝ} (hs : 0 < s) (hww' : (w' : ℂ) = s * w)
    (hw : p (φ w) ∈ unitSegment) :
    ∃ hw' : p (φ w') ∈ unitSegment,
      ConnectedComponents.mk (⟨φ w', hw'⟩ : p ⁻¹' unitSegment) =
        ConnectedComponents.mk ⟨φ w, hw⟩ := by
  -- The scalars `c t = (1 - t) + t * s` interpolate between `1` and `s`, and stay positive.
  have hc (t : unitInterval) : 0 < (1 - t : ℝ) + t * s := by
    rcases t.2.2.lt_or_eq with ht | ht
    · nlinarith [mul_nonneg t.2.1 hs.le]
    · rw [ht]
      linarith
  have hmem (t : unitInterval) :
      (((1 - t : ℝ) + t * s : ℝ) : ℂ) * w ∈ Metric.ball (0 : ℂ) 1 \ {0} := by
    have hw1 : ‖(w : ℂ)‖ < 1 := mem_ball_zero_iff.1 w.2.1
    have hw'1 : s * ‖(w : ℂ)‖ < 1 := by
      have := mem_ball_zero_iff.1 w'.2.1
      rwa [hww', norm_mul, norm_real, Real.norm_of_nonneg hs.le] at this
    refine ⟨mem_ball_zero_iff.2 ?_, mul_ne_zero (ofReal_ne_zero.2 (hc t).ne') w.2.2⟩
    rw [norm_mul, norm_real, Real.norm_of_nonneg (hc t).le]
    rcases t.2.2.lt_or_eq with ht | ht
    · nlinarith [mul_pos (sub_pos.2 ht) (sub_pos.2 hw1), mul_nonneg t.2.1 (sub_pos.2 hw'1).le]
    · rw [ht]
      linarith
  -- Positive scalings of a point over `(0, 1)` lie over `(0, 1)`.
  have hseg' (c : ℝ) (hc : 0 < c) (v : 𝔻*) (hv : (v : ℂ) = c * w) : p (φ v) ∈ unitSegment := by
    rw [mem_unitSegment_iff_of_coe_coord_eq_pow hφq hseg] at hw ⊢
    rw [hv, mul_pow, ← ofReal_pow, re_ofReal_mul, im_ofReal_mul, hw.1, mul_zero]
    exact ⟨rfl, mul_pos (pow_pos hc _) hw.2⟩
  let γ : Path (φ w) (φ w') :=
    { toFun t := φ ⟨_, hmem t⟩
      continuous_toFun := hφ.comp (Continuous.subtype_mk (by fun_prop) _)
      source' := by simp
      target' := by
        congr 1
        exact Subtype.ext (by simp [hww']) }
  have hγ (t : unitInterval) : γ t ∈ p ⁻¹' unitSegment := hseg' _ (hc t) _ rfl
  refine ⟨hseg' s hs w' hww', ConnectedComponents.coe_eq_coe.2 ?_⟩
  exact (connectedComponent_eq
    (pathComponent_subset_component _ (JoinedIn.joined_subtype ⟨γ, hγ⟩))).symm

/-- A filling-chart centre over a puncture in whose coordinate `(0, 1)` is the positive real axis
is in the closure of an included connected component of `p ⁻¹' (0, 1)` exactly when the chart
meets that component. -/
private theorem center_mem_closure_component_iff (hp : IsCoveringMap p)
    (hfin : Finite (p ⁻¹' {basePt})) (j : FilledPoint p)
    (hseg : ∀ z (hz : z ∈ (sigmaEquiv p j).1.neighborhood), z ∈ unitSegment ↔
      ((sigmaEquiv p j).1.coord ⟨z, hz⟩ : ℂ).im = 0 ∧
        0 < ((sigmaEquiv p j).1.coord ⟨z, hz⟩ : ℂ).re)
    (c : ConnectedComponents (p ⁻¹' unitSegment)) :
    PunctureFilling.center (chart p) j ∈
        closure (PunctureFilling.incl (chart p) ''
          {x | ∃ hx : p x ∈ unitSegment, ConnectedComponents.mk ⟨x, hx⟩ = c}) ↔
      ∃ (w : 𝔻*) (hw : p (chart p j w) ∈ unitSegment),
        ConnectedComponents.mk ⟨chart p j w, hw⟩ = c := by
  constructor
  · intro hclosure
    let U := PunctureFilling.disc (chart p) j '' {z : 𝔻 | ‖(z : ℂ)‖ < 1}
    have hU : U ∈ 𝓝 (PunctureFilling.center (chart p) j) := by
      apply (PunctureFilling.hasBasis_nhds_center
        (fun i ↦ (isOpenEmbedding_chart hp hfin i).continuous)
        (isOpenEmbedding_chart hp hfin j)).mem_iff.2
      exact ⟨1, zero_lt_one, Subset.rfl⟩
    obtain ⟨z, hzU, x, ⟨hx, hc⟩, hzx⟩ := (mem_closure_iff_nhds.1 hclosure U hU)
    obtain ⟨d, -, rfl⟩ := hzU
    obtain ⟨w, -, hchart⟩ := PunctureFilling.disc_eq_incl_iff.1 hzx.symm
    subst x
    exact ⟨w, hx, hc⟩
  · rintro ⟨w, hw, hc⟩
    let f : ℕ → FilledCover p := PunctureFilling.disc (chart p) j ∘
      fun k ↦ (⟨radialPoint w k, (radialPoint w k).2.1⟩ : 𝔻)
    refine mem_closure_of_tendsto (f := f) (b := atTop) ?_ (.of_forall fun k ↦ ?_)
    · have hlim := (PunctureFilling.continuous_disc (φ := chart p) j).continuousAt.tendsto.comp
        (tendsto_radialPoint_zero w)
      simpa only [f, PunctureFilling.disc_zero] using hlim
    · have hfk : f k = PunctureFilling.incl (chart p) (chart p j (radialPoint w k)) := by
        simp only [f, Function.comp_apply]
        exact PunctureFilling.disc_inclusion j (radialPoint w k)
      rw [hfk]
      -- The radial sequence stays on the component of `w`.
      obtain ⟨hy, hyw⟩ := exists_mk_eq_of_coe_eq_ofReal_mul
        (isOpenEmbedding_chart hp hfin j).continuous
        (fun w ↦ (exists_coe_coord_chart_eq_pow hp hfin j w).imp fun _ h ↦ h.2) hseg
        (w' := radialPoint w k) (s := 1 / (k + 1 : ℝ)) (by positivity) (by simp [real_smul]) hw
      exact ⟨_, ⟨hy, hyw.trans hc⟩, rfl⟩

/-- An added point over `0` is a black endpoint of an edge exactly when its punctured-neighborhood
component is the cycle of that edge under `σ0`. -/
theorem center_overZero_mem_closure_edge_iff {n : ℕ} (hp : IsCoveringMap p)
    (ν : p ⁻¹' {basePt} ≃ Fin n) (i : Fin n)
    (b : ConnectedComponents (p ⁻¹' puncturedNeighborhoodZero)) :
    PunctureFilling.center (chart p) (overZero p b) ∈ closure (edge hp ν i) ↔
      b = hp.sameCycleQuotientσ0EquivConnectedComponents ν (Quotient.mk _ i) := by
  let hfin : Finite (p ⁻¹' {basePt}) := .of_equiv _ ν.symm
  rw [edge, center_mem_closure_component_iff hp hfin (overZero p b)
    (by rw [sigmaEquiv_overZero]; exact mem_unitSegment_iff_coord_zero)
    (hp.finEquivConnectedComponentsUnitSegment ν i)]
  constructor
  · rintro ⟨w, hx, hi⟩
    have hxrange : chart p (overZero p b) w ∈ range (chart p (overZero p b)) := ⟨w, rfl⟩
    rw [range_chart hp hfin, sigmaEquiv_overZero] at hxrange
    obtain ⟨hx0, hb⟩ := hxrange
    exact (hp.exists_common_point_iff_eq_sameCycleQuotientσ0 ν i b).1
      ⟨chart p (overZero p b) w, hx, hx0, hi, hb⟩
  · intro hb
    obtain ⟨x, hx, hx0, hi, hb'⟩ :=
      (hp.exists_common_point_iff_eq_sameCycleQuotientσ0 ν i b).2 hb
    have hxrange : x ∈ range (chart p (overZero p b)) := by
      rw [range_chart hp hfin, sigmaEquiv_overZero]
      exact ⟨hx0, hb'⟩
    obtain ⟨w, rfl⟩ := hxrange
    exact ⟨w, hx, hi⟩

/-- An added point over `1` is a white endpoint of an edge exactly when its punctured-neighborhood
component is the cycle of that edge under `σ1`. -/
theorem center_overOne_mem_closure_edge_iff {n : ℕ} (hp : IsCoveringMap p)
    (ν : p ⁻¹' {basePt} ≃ Fin n) (i : Fin n)
    (b : ConnectedComponents (p ⁻¹' puncturedNeighborhoodOne)) :
    PunctureFilling.center (chart p) (overOne p b) ∈ closure (edge hp ν i) ↔
      b = hp.sameCycleQuotientσ1EquivConnectedComponents ν (Quotient.mk _ i) := by
  let hfin : Finite (p ⁻¹' {basePt}) := .of_equiv _ ν.symm
  rw [edge, center_mem_closure_component_iff hp hfin (overOne p b)
    (by rw [sigmaEquiv_overOne]; exact mem_unitSegment_iff_coord_one)
    (hp.finEquivConnectedComponentsUnitSegment ν i)]
  constructor
  · rintro ⟨w, hx, hi⟩
    have hxrange : chart p (overOne p b) w ∈ range (chart p (overOne p b)) := ⟨w, rfl⟩
    rw [range_chart hp hfin, sigmaEquiv_overOne] at hxrange
    obtain ⟨hx1, hb⟩ := hxrange
    exact (hp.exists_common_point_iff_eq_sameCycleQuotientσ1 ν i b).1
      ⟨chart p (overOne p b) w, hx, hx1, hi, hb⟩
  · intro hb
    obtain ⟨x, hx, hx1, hi, hb'⟩ :=
      (hp.exists_common_point_iff_eq_sameCycleQuotientσ1 ν i b).2 hb
    have hxrange : x ∈ range (chart p (overOne p b)) := by
      rw [range_chart hp hfin, sigmaEquiv_overOne]
      exact ⟨hx1, hb'⟩
    obtain ⟨w, rfl⟩ := hxrange
    exact ⟨w, hx, hi⟩

end FilledCover

end TauCeti
