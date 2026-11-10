/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Module.Convex
public import Mathlib.Analysis.Convex.Topology
import Mathlib.Tactic.Module
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-!
# Strict inward cones

A vector is strictly inward to a set at a point if small positive steps along it carry a ball
whose radius is proportional to the step size into the set. Unlike the closed tangent cone,
this excludes directions tangent to the boundary of a half-space.

For convex sets, membership is equivalent to reaching an interior point along the positive ray.
The cone is open and convex, is invariant under positive scaling, and has ball estimates uniform
near each admissible point and vector. These estimates supply the local geometric input for
constructing strictly inward vector fields on models with corners.
-/

public section

open Set Metric Filter
open scoped Topology

namespace TauCeti

variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
variable {s u : Set E} {x v : E}

/-- The strict inward cone consists of directions along which balls of linearly increasing
radius remain in the set for all sufficiently small positive times. -/
def strictInwardCone (s : Set E) (x : E) : Set E :=
  {v | ∃ ε > 0, ∃ δ > 0, ∀ t ∈ Ioo (0 : ℝ) δ, ball (x + t • v) (ε * t) ⊆ s}

/-- The ball criterion defining the strict inward cone. -/
theorem mem_strictInwardCone_iff : v ∈ strictInwardCone s x ↔
    ∃ ε > 0, ∃ δ > 0, ∀ t ∈ Ioo (0 : ℝ) δ, ball (x + t • v) (ε * t) ⊆ s := Iff.rfl

/-- Enlarging the set enlarges its strict inward cone. -/
theorem strictInwardCone_mono (h : s ⊆ u) : strictInwardCone s x ⊆ strictInwardCone u x := by
  rintro v ⟨ε, hε, δ, hδ, hv⟩
  exact ⟨ε, hε, δ, hδ, fun t ht ↦ (hv t ht).trans h⟩

/-- The zero vector is strictly inward exactly at interior points. -/
@[simp]
theorem zero_mem_strictInwardCone_iff : (0 : E) ∈ strictInwardCone s x ↔ x ∈ interior s := by
  constructor
  · rintro ⟨ε, hε, δ, hδ, h⟩
    have hb := h (δ / 2) ⟨by positivity, by linarith⟩
    simp only [smul_zero, add_zero] at hb
    exact mem_interior_iff_mem_nhds.mpr
      (Filter.mem_of_superset (ball_mem_nhds x (by positivity : 0 < ε * (δ / 2))) hb)
  · intro hx
    obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hx)
    refine ⟨r, hr, 1, zero_lt_one, fun t ht ↦ ?_⟩
    simpa only [smul_zero, add_zero] using
      (ball_subset_ball (mul_le_of_le_one_right hr.le ht.2.le)).trans hball

/-- All directions are strictly inward exactly at interior points, without a convexity
assumption. -/
@[simp]
theorem strictInwardCone_eq_univ_iff : strictInwardCone s x = univ ↔ x ∈ interior s := by
  constructor
  · intro h
    apply zero_mem_strictInwardCone_iff.mp
    rw [h]
    exact mem_univ _
  · intro hx
    obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hx)
    apply eq_univ_of_forall
    intro v
    refine ⟨1, zero_lt_one, r / (‖v‖ + 1), by positivity, fun t ht z hz ↦ hball ?_⟩
    have hz' : dist z (x + t • v) < t := by simpa using hz
    have htx : dist (x + t • v) x = t * ‖v‖ := by
      simp [dist_eq_norm, norm_smul, Real.norm_eq_abs, abs_of_pos ht.1]
    have htbound := (lt_div_iff₀ (by positivity : 0 < ‖v‖ + 1)).mp ht.2
    apply mem_ball.mpr
    have := dist_triangle z (x + t • v) x
    rw [htx] at this
    nlinarith

/-- Every vector is strictly inward to the whole space. -/
@[simp]
theorem strictInwardCone_univ (x : E) : strictInwardCone (univ : Set E) x = univ :=
  strictInwardCone_eq_univ_iff.mpr (by simp)

/-- Positive rescaling preserves and reflects strict inwardness, even without convexity. -/
@[simp]
theorem smul_mem_strictInwardCone_iff {c : ℝ} (hc : 0 < c) :
    c • v ∈ strictInwardCone s x ↔ v ∈ strictInwardCone s x := by
  have hsmul {c : ℝ} {v : E} (hc : 0 < c) (hv : v ∈ strictInwardCone s x) :
      c • v ∈ strictInwardCone s x := by
    obtain ⟨ε, hε, δ, hδ, h⟩ := hv
    refine ⟨ε * c, mul_pos hε hc, δ / c, div_pos hδ hc, fun t ht ↦ ?_⟩
    have ht' : t * c ∈ Ioo (0 : ℝ) δ :=
      ⟨mul_pos ht.1 hc, (lt_div_iff₀ hc).mp ht.2⟩
    simpa only [smul_smul, mul_assoc, mul_comm c t] using h (t * c) ht'
  constructor
  · intro h
    simpa only [smul_smul, inv_mul_cancel₀ hc.ne', one_smul] using hsmul (inv_pos.mpr hc) h
  · exact hsmul hc

end TauCeti

open TauCeti

variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
variable {s : Set E} {x v q : E}

/-- An interior point on a positive ray gives uniform inward ball estimates near the starting
point and direction, with the starting point restricted to the convex set. -/
theorem Convex.exists_uniform_ball_subset_of_add_smul_mem_interior (hs : Convex ℝ s)
    {T : ℝ} (hT : 0 < T) (hq : x + T • v ∈ interior s) :
    ∃ ε > 0, ∃ δ > 0, ∀ᶠ p : E × E in 𝓝 (x, v), p.1 ∈ s →
      ∀ t ∈ Ioo (0 : ℝ) δ, ball (p.1 + t • p.2) (ε * t) ⊆ s := by
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hq)
  refine ⟨r / (2 * T), by positivity, T, hT, ?_⟩
  have hc : Continuous (fun p : E × E ↦ p.1 + T • p.2) := by fun_prop
  have he : ∀ᶠ p : E × E in 𝓝 (x, v),
      p.1 + T • p.2 ∈ ball (x + T • v) (r / 2) :=
    hc.continuousAt.eventually (ball_mem_nhds (x + T • v) (half_pos hr))
  filter_upwards [he] with p hp hps t ht
  have hb : ball (p.1 + T • p.2) (r / 2) ⊆ s := by
    intro z hz
    apply hball
    exact mem_ball.mpr ((dist_triangle _ _ _).trans_lt
      (by have := mem_ball.mp hp; have := mem_ball.mp hz; linarith))
  have h := hs.ball_add_smul_sub_subset hb hps
    (by have := (div_lt_one hT).mpr ht.2; linarith : 0 ≤ 1 - t / T)
    (by have := div_pos ht.1 hT; linarith : 1 - t / T ≤ 1)
  have hcenter : p.1 + T • p.2 + (1 - t / T) • (p.1 - (p.1 + T • p.2)) =
      p.1 + t • p.2 := by
    match_scalars <;> field_simp <;> ring
  have hradius : (1 - (1 - t / T)) * (r / 2) = r / (2 * T) * t := by ring
  rwa [hcenter, hradius] at h

/-- In a convex set, a direction is strictly inward if and only if its positive ray meets the
interior. No closedness or finite-dimensionality is required. -/
theorem Convex.mem_strictInwardCone_iff (hs : Convex ℝ s) (hx : x ∈ s) :
    v ∈ strictInwardCone s x ↔ ∃ t : ℝ, 0 < t ∧ x + t • v ∈ interior s := by
  constructor
  · rintro ⟨ε, hε, δ, hδ, h⟩
    refine ⟨δ / 2, by positivity, mem_interior_iff_mem_nhds.mpr ?_⟩
    exact Filter.mem_of_superset (ball_mem_nhds _ (by positivity))
      (h (δ / 2) ⟨by positivity, by linarith⟩)
  · rintro ⟨T, hT, hq⟩
    obtain ⟨ε, hε, δ, hδ, h⟩ := hs.exists_uniform_ball_subset_of_add_smul_mem_interior hT hq
    exact ⟨ε, hε, δ, hδ, h.self_of_nhds hx⟩

/-- The inward ball estimates can be chosen uniformly near any strictly inward point-vector
pair, as long as the perturbed starting point stays in the convex set. -/
theorem Convex.exists_uniform_ball_subset_of_mem_strictInwardCone (hs : Convex ℝ s)
    (hx : x ∈ s) (hv : v ∈ strictInwardCone s x) :
    ∃ ε > 0, ∃ δ > 0, ∀ᶠ p : E × E in 𝓝 (x, v), p.1 ∈ s →
      ∀ t ∈ Ioo (0 : ℝ) δ, ball (p.1 + t • p.2) (ε * t) ⊆ s := by
  obtain ⟨T, hT, hq⟩ := (hs.mem_strictInwardCone_iff hx).mp hv
  exact hs.exists_uniform_ball_subset_of_add_smul_mem_interior hT hq

/-- Every interior anchor supplies a strictly inward vector at every point of a convex set. -/
theorem Convex.sub_mem_strictInwardCone (hs : Convex ℝ s) (hx : x ∈ s)
    (hq : q ∈ interior s) : q - x ∈ strictInwardCone s x := by
  apply (hs.mem_strictInwardCone_iff hx).mpr
  exact ⟨1, zero_lt_one, by simpa using hq⟩

/-- A convex set with nonempty interior has nonempty strict inward cones at all its points. -/
theorem Convex.strictInwardCone_nonempty (hs : Convex ℝ s) (hx : x ∈ s)
    (hi : (interior s).Nonempty) : (strictInwardCone s x).Nonempty := by
  obtain ⟨q, hq⟩ := hi
  exact ⟨q - x, hs.sub_mem_strictInwardCone hx hq⟩

/-- The strict inward cone of a convex set is convex. -/
theorem Convex.convex_strictInwardCone (hs : Convex ℝ s) (hx : x ∈ s) :
    Convex ℝ (strictInwardCone s x) := by
  intro v hv w hw a b ha hb hab
  obtain ⟨T, hT, hvT⟩ := (hs.mem_strictInwardCone_iff hx).mp hv
  obtain ⟨U, hU, hwU⟩ := (hs.mem_strictInwardCone_iff hx).mp hw
  let t := min T U
  have ht : 0 < t := lt_min hT hU
  have hv' : x + t • v ∈ interior s := by
    have h := hs.add_smul_mem_interior hx hvT
      ⟨div_pos ht hT, (div_le_one hT).mpr (min_le_left T U)⟩
    simpa only [smul_smul, div_mul_cancel₀ _ hT.ne'] using h
  have hw' : x + t • w ∈ interior s := by
    have h := hs.add_smul_mem_interior hx hwU
      ⟨div_pos ht hU, (div_le_one hU).mpr (min_le_right T U)⟩
    simpa only [smul_smul, div_mul_cancel₀ _ hU.ne'] using h
  apply (hs.mem_strictInwardCone_iff hx).mpr
  refine ⟨t, ht, ?_⟩
  convert hs.interior hv' hw' ha hb hab using 1
  match_scalars <;> nlinarith

/-- Strict inwardness is open jointly in the base point (relative to the set) and direction. -/
theorem Convex.isOpen_setOf_mem_strictInwardCone (hs : Convex ℝ s) :
    IsOpen {p : s × E | p.2 ∈ strictInwardCone s p.1} := by
  have heq : {p : s × E | p.2 ∈ strictInwardCone s p.1} =
      ⋃ t : ℝ, ⋃ (_ : 0 < t), {p : s × E | (p.1 : E) + t • p.2 ∈ interior s} := by
    ext p
    simp [hs.mem_strictInwardCone_iff p.1.property]
  rw [heq]
  exact isOpen_iUnion fun t ↦ isOpen_iUnion fun _ ↦
    isOpen_interior.preimage (by fun_prop)

/-- At a fixed point of a convex set the strict inward cone is open. -/
theorem Convex.isOpen_strictInwardCone (hs : Convex ℝ s) (hx : x ∈ s) :
    IsOpen (strictInwardCone s x) := by
  have hc : Continuous (fun v : E ↦ (⟨x, hx⟩, v) : E → s × E) := by fun_prop
  exact hs.isOpen_setOf_mem_strictInwardCone.preimage hc

namespace TauCeti

/-- At the endpoint of the half-line the strict cone is the positive, not the nonnegative,
half-line. In particular neither zero nor an outward vector is admitted. -/
@[simp]
theorem strictInwardCone_Ici_zero : strictInwardCone (Ici (0 : ℝ)) 0 = Ioi 0 := by
  ext v
  rw [(convex_Ici (0 : ℝ)).mem_strictInwardCone_iff (by simp)]
  simp only [interior_Ici, zero_add, smul_eq_mul, mem_Ioi]
  constructor
  · rintro ⟨t, ht, htv⟩
    exact (mul_pos_iff_of_pos_left ht).mp htv
  · intro hv
    exact ⟨1, zero_lt_one, by simpa using hv⟩

/-- At the vertex of the quadrant, both coordinates must point strictly inward. In particular
an edge direction such as `(1, 0)` is excluded. -/
@[simp]
theorem strictInwardCone_quadrant_zero :
    strictInwardCone (Ici (0 : ℝ × ℝ)) 0 = Ioi 0 ×ˢ Ioi 0 := by
  have hset : Ici (0 : ℝ × ℝ) = Ici (0 : ℝ) ×ˢ Ici (0 : ℝ) := by
    simpa only [Prod.mk_zero_zero] using (Ici_prod_Ici (0 : ℝ) (0 : ℝ)).symm
  rw [hset]
  ext v
  have hs : Convex ℝ (Ici (0 : ℝ) ×ˢ Ici (0 : ℝ)) :=
    (convex_Ici (0 : ℝ)).prod (convex_Ici (0 : ℝ))
  have hx : (0 : ℝ × ℝ) ∈ Ici (0 : ℝ) ×ˢ Ici (0 : ℝ) := by
    exact ⟨by norm_num, by norm_num⟩
  rw [hs.mem_strictInwardCone_iff hx]
  simp only [interior_prod_eq, interior_Ici, zero_add, mem_prod, mem_Ioi,
    Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  constructor
  · rintro ⟨t, ht, h₁, h₂⟩
    exact ⟨(mul_pos_iff_of_pos_left ht).mp h₁, (mul_pos_iff_of_pos_left ht).mp h₂⟩
  · rintro ⟨h₁, h₂⟩
    exact ⟨1, zero_lt_one, by simpa using h₁, by simpa using h₂⟩

end TauCeti
