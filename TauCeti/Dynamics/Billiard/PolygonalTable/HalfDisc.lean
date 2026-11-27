/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Dynamics.Billiard.PolygonalTable
import Mathlib.Analysis.Convex.PathConnected
import TauCeti.Topology.Frontier
import TauCeti.Analysis.Complex.Circle.Basic

/-!
# A polygonal table is a half-disc near a point of a side

Let `p` be a point of the relative interior of a side `S` of a polygonal table `P`, and let `d` be
the unit direction of `S`. The signed distance of a point `z` from the line through `S` is
`sideHeight S p z = Im (conj d · (z − p))`. Near `p` the table is a half-disc: there are `r > 0`
and a sign `ε = ±1` such that a point `z` of the disc of radius `r` about `p` lies in the interior
of `P` exactly when `ε · sideHeight S p z > 0`, and in `P` exactly when `ε · sideHeight S p z ≥ 0`
(`TauCeti.PolygonalTable.exists_halfDisc`). So near `p` the frontier of `P` is the line through
`S`.

The proof: the other sides are closed and miss `p`, so near `p` the frontier of `P` lies in `S`.
The two open half-discs on either side of the line through `S` are convex and miss the frontier,
so each lies in the interior of `P` or in its complement. They cannot both lie in the interior,
since then `p` would be an interior point, nor both in the complement, since `p` lies in the
closure of the interior.

## Main definitions

* `TauCeti.PolygonalTable.sideHeight`: the signed distance from the line through a side.

## Main results

* `TauCeti.PolygonalTable.exists_ball_inter_frontier_subset_side`: near a point of the relative
  interior of a side, the frontier of the table lies in that side.
* `TauCeti.PolygonalTable.exists_halfDisc`: near a point of the relative interior of a side, the
  table is a half-disc.

## References

* N. Chernov, R. Markarian, *Chaotic Billiards*, Mathematical Surveys and Monographs 127, AMS
  (2006), Chapter 2.
-/

public section

open Set Metric Topology Filter ComplexConjugate

namespace TauCeti

namespace PolygonalTable

variable {T : PolygonalTable}

/-- The **signed distance** of `z` from the line through the side `s` passing through `p`: the
imaginary part of `conj d · (z − p)`, for the unit direction `d` of `s`. -/
noncomputable def sideHeight (s : T.Side) (p z : ℂ) : ℝ :=
  (conj (s.direction : ℂ) * (z - p)).im

theorem sideHeight_def (s : T.Side) (p z : ℂ) :
    sideHeight s p z = (conj (s.direction : ℂ) * (z - p)).im :=
  (rfl)

@[simp]
theorem sideHeight_self (s : T.Side) (p : ℂ) : sideHeight s p p = 0 := by
  simp [sideHeight]

/-- The signed distance changes along a direction `w` by `Im (conj d · w)` per unit time. -/
theorem sideHeight_add_mul (s : T.Side) (p z w : ℂ) (t : ℝ) :
    sideHeight s p (z + t * w) = sideHeight s p z + t * (conj (s.direction : ℂ) * w).im := by
  simp only [sideHeight, add_sub_right_comm z, mul_add, Complex.add_im, mul_left_comm _ (t : ℂ),
    Complex.im_ofReal_mul]

/-- The signed distance from a side increases at unit rate along `i d`. -/
theorem sideHeight_add_mul_I_mul_direction (s : T.Side) (p z : ℂ) (t : ℝ) :
    sideHeight s p (z + t * (Complex.I * s.direction)) = sideHeight s p z + t := by
  rw [sideHeight_add_mul]
  simp [mul_left_comm, Circle.conj_coe_mul_self]

/-- Every point of a side lies on the line through any point of the side. -/
theorem sideHeight_eq_zero_of_mem_side {s : T.Side} {p z : ℂ} (hp : p ∈ T.side s)
    (hz : z ∈ T.side s) : sideHeight s p z = 0 := by
  rw [side_eq_segment, segment_eq_image_lineMap] at hp hz
  obtain ⟨a, -, rfl⟩ := hp
  obtain ⟨b, -, rfl⟩ := hz
  have hsub : AffineMap.lineMap s.start s.finish b - AffineMap.lineMap s.start s.finish a =
      ((b - a) * ‖s.finish - s.start‖ : ℝ) * (s.direction : ℂ) := by
    rw [s.coe_direction, AffineMap.lineMap_apply_module', AffineMap.lineMap_apply_module']
    have h : (‖s.finish - s.start‖ : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.2 (norm_ne_zero_iff.2 (sub_ne_zero.2 s.start_ne_finish.symm))
    simp only [Complex.real_smul]
    push_cast
    field_simp
    ring
  rw [sideHeight, hsub]
  simp [mul_left_comm, Circle.conj_coe_mul_self]

/-- **Near a point of the relative interior of a side, the frontier of the table lies in that
side.** -/
theorem exists_ball_inter_frontier_subset_side {s : T.Side} {p : ℂ}
    (hp : p ∈ T.sideInterior s) : ∃ r > 0, ball p r ∩ frontier T.carrier ⊆ T.side s := by
  have hK : IsClosed (⋃ t ∈ ({s}ᶜ : Set T.Side), T.side t) :=
    (Set.toFinite _).isClosed_biUnion fun t _ => T.isClosed_side t
  have hpK : p ∉ ⋃ t ∈ ({s}ᶜ : Set T.Side), T.side t := by
    simp only [mem_iUnion, mem_compl_iff, mem_singleton_iff, not_exists]
    exact fun t hts => T.notMem_side_of_mem_sideInterior hp hts
  obtain ⟨r, hr, hrK⟩ := Metric.mem_nhds_iff.1 (hK.isOpen_compl.mem_nhds hpK)
  refine ⟨r, hr, fun z ⟨hzb, hzf⟩ => ?_⟩
  rw [frontier_eq_iUnion_side, mem_iUnion] at hzf
  obtain ⟨t, hzt⟩ := hzf
  by_contra hzs
  have hts : t ≠ s := fun h => hzs (h ▸ hzt)
  exact hrK hzb (mem_iUnion₂.2 ⟨t, hts, hzt⟩)

/-- A point of the open disc on the line through a side lies in the closure of each of the two open
half-discs: for every `c ≠ 0`, of the points of the disc where `c · sideHeight` is positive. -/
theorem mem_closure_ball_inter_sideHeight_pos {s : T.Side} {p z : ℂ} {r : ℝ} (hz : z ∈ ball p r)
    (hz0 : sideHeight s p z = 0) {c : ℝ} (hc : c ≠ 0) :
    z ∈ closure (ball p r ∩ {w | 0 < c * sideHeight s p w}) := by
  have hT : Tendsto (fun t : ℝ => z + (t * c : ℝ) * (Complex.I * s.direction)) (𝓝[>] 0)
      (𝓝 z) :=
    ((by fun_prop : Continuous fun t : ℝ => z + (t * c : ℝ) * (Complex.I * s.direction)).tendsto'
      0 z (by simp)).mono_left nhdsWithin_le_nhds
  refine mem_closure_of_tendsto hT ?_
  filter_upwards [hT.eventually (isOpen_ball.mem_nhds hz), self_mem_nhdsWithin] with t hb ht
  refine ⟨hb, ?_⟩
  simp only [mem_ofPred_eq, sideHeight_add_mul_I_mul_direction, hz0, zero_add]
  have ht' : 0 < t := ht
  nlinarith [sq_pos_of_ne_zero hc]

/-- The disc on one side of the line through a side is convex. -/
theorem convex_ball_inter_sideHeight_pos (s : T.Side) (p : ℂ) (r c : ℝ) :
    Convex ℝ (ball p r ∩ {w | 0 < c * sideHeight s p w}) := by
  refine (convex_ball p r).inter ?_
  have hlin : IsLinearMap ℝ fun w : ℂ => c * (conj (s.direction : ℂ) * w).im :=
    ⟨fun x y => by simp [mul_add], fun a x => by
      simp only [Complex.real_smul, mul_left_comm _ (a : ℂ), Complex.im_ofReal_mul, smul_eq_mul]
      ring⟩
  convert convex_halfSpace_gt hlin (c * (conj (s.direction : ℂ) * p).im) using 1
  ext w
  simp only [mem_ofPred_eq, sideHeight, mul_sub, Complex.sub_im]
  constructor <;> intro h <;> nlinarith

/-- If the open half-disc where `ε · sideHeight` is positive lies in the interior of the table and
the opposite one lies outside, then the disc meets the interior and the table exactly in the
half-discs where `ε · sideHeight` is positive and nonnegative. -/
private theorem halfDisc_of_subset {s : T.Side} {p : ℂ} {r ε : ℝ} (hε : ε = 1 ∨ ε = -1)
    (hin : ball p r ∩ {w | 0 < ε * sideHeight s p w} ⊆ interior T.carrier)
    (hout : ball p r ∩ {w | 0 < -ε * sideHeight s p w} ⊆ T.carrierᶜ) :
    ∀ z ∈ ball p r, (z ∈ interior T.carrier ↔ 0 < ε * sideHeight s p z) ∧
      (z ∈ T.carrier ↔ 0 ≤ ε * sideHeight s p z) := by
  have hε0 : ε ≠ 0 := by rcases hε with rfl | rfl <;> norm_num
  intro z hz
  rcases lt_trichotomy (ε * sideHeight s p z) 0 with h | h | h
  · have hzo : z ∈ T.carrierᶜ := hout ⟨hz, by rw [mem_ofPred_eq, neg_mul]; linarith⟩
    exact ⟨iff_of_false (fun hi => hzo (interior_subset hi)) h.not_gt,
      iff_of_false hzo h.not_ge⟩
  · have hz0 : sideHeight s p z = 0 := (mul_eq_zero.1 h).resolve_left hε0
    have hcl := (closure_mono hin) (mem_closure_ball_inter_sideHeight_pos hz hz0 hε0)
    have hcl' := (closure_mono hout)
      (mem_closure_ball_inter_sideHeight_pos hz hz0 (neg_ne_zero.2 hε0))
    rw [closure_compl] at hcl'
    refine ⟨iff_of_false hcl' (by rw [h]; exact lt_irrefl 0), iff_of_true ?_ h.ge⟩
    exact T.isClosed_carrier.closure_subset (closure_mono interior_subset hcl)
  · have hzi : z ∈ interior T.carrier := hin ⟨hz, h⟩
    exact ⟨iff_of_true hzi h, iff_of_true (interior_subset hzi) h.le⟩

/-- **Near a point of the relative interior of a side, a polygonal table is a half-disc.** There
are `r > 0` and a sign `ε = ±1` such that a point `z` at distance less than `r` from `p` lies in
the interior of the table exactly when `ε · sideHeight s p z > 0`, and in the table exactly when
`ε · sideHeight s p z ≥ 0`. -/
theorem exists_halfDisc {s : T.Side} {p : ℂ} (hp : p ∈ T.sideInterior s) :
    ∃ r > 0, ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧ ∀ z ∈ ball p r,
      (z ∈ interior T.carrier ↔ 0 < ε * sideHeight s p z) ∧
      (z ∈ T.carrier ↔ 0 ≤ ε * sideHeight s p z) := by
  obtain ⟨r, hr, hrf⟩ := T.exists_ball_inter_frontier_subset_side hp
  have hps : p ∈ T.side s := T.sideInterior_subset_side s hp
  have hpf : p ∈ frontier T.carrier := T.sideInterior_subset_frontier s hp
  -- The open half-disc where `c · sideHeight` is positive misses the frontier.
  have hdisj (c : ℝ) : Disjoint (ball p r ∩ {w | 0 < c * sideHeight s p w}) (frontier T.carrier) :=
    Set.disjoint_left.2 fun w ⟨hwb, hwh⟩ hwf => by
      have := sideHeight_eq_zero_of_mem_side hps (hrf ⟨hwb, hwf⟩)
      simp [this] at hwh
  have hsplit (c : ℝ) : ball p r ∩ {w | 0 < c * sideHeight s p w} ⊆ interior T.carrier ∨
      ball p r ∩ {w | 0 < c * sideHeight s p w} ⊆ T.carrierᶜ :=
    IsPreconnected.subset_interior_or_subset_compl_of_isClosed
      (convex_ball_inter_sideHeight_pos s p r c).isPreconnected T.isClosed_carrier (hdisj c)
  -- The two half-discs cannot lie on the same side of the frontier.
  have hball_carrier : ¬ (ball p r ∩ {w | 0 < 1 * sideHeight s p w} ⊆ interior T.carrier ∧
      ball p r ∩ {w | 0 < -1 * sideHeight s p w} ⊆ interior T.carrier) := by
    rintro ⟨h₁, h₂⟩
    have hsub : ball p r ⊆ T.carrier := by
      intro z hz
      rcases lt_trichotomy (sideHeight s p z) 0 with h | h | h
      · exact interior_subset (h₂ ⟨hz, by rw [mem_ofPred_eq]; linarith⟩)
      · exact T.isClosed_carrier.closure_subset (closure_mono (h₁.trans interior_subset)
          (mem_closure_ball_inter_sideHeight_pos hz h one_ne_zero))
      · exact interior_subset (h₁ ⟨hz, by rw [mem_ofPred_eq]; linarith⟩)
    exact Set.disjoint_left.1 (disjoint_interior_frontier (s := T.carrier))
      (mem_interior.2 ⟨ball p r, hsub, isOpen_ball, mem_ball_self hr⟩) hpf
  have hball_compl : ¬ (ball p r ∩ {w | 0 < 1 * sideHeight s p w} ⊆ T.carrierᶜ ∧
      ball p r ∩ {w | 0 < -1 * sideHeight s p w} ⊆ T.carrierᶜ) := by
    rintro ⟨h₁, h₂⟩
    have hpcl : p ∈ closure (interior T.carrier) := by
      rw [T.closure_interior]
      exact T.isClosed_carrier.frontier_subset hpf
    obtain ⟨z, hzi, hz⟩ := Metric.mem_closure_iff.1 hpcl r hr
    have hz : z ∈ ball p r := mem_ball.2 (dist_comm p z ▸ hz)
    rcases lt_trichotomy (sideHeight s p z) 0 with h | h | h
    · exact h₂ ⟨hz, by rw [mem_ofPred_eq]; linarith⟩ (interior_subset hzi)
    · have hcl := (closure_mono h₁) (mem_closure_ball_inter_sideHeight_pos hz h one_ne_zero)
      rw [closure_compl] at hcl
      exact hcl hzi
    · exact h₁ ⟨hz, by rw [mem_ofPred_eq]; linarith⟩ (interior_subset hzi)
  rcases hsplit 1 with h₁ | h₁ <;> rcases hsplit (-1) with h₂ | h₂
  · exact (hball_carrier ⟨h₁, h₂⟩).elim
  · exact ⟨r, hr, 1, Or.inl rfl, halfDisc_of_subset (Or.inl rfl) h₁ h₂⟩
  · refine ⟨r, hr, -1, Or.inr rfl, halfDisc_of_subset (Or.inr rfl) h₂ ?_⟩
    simpa using h₁
  · exact (hball_compl ⟨h₁, h₂⟩).elim

end PolygonalTable

end TauCeti
