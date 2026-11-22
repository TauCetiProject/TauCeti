/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Module.Convex
public import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Tactic.Module
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-!
# Strict inward cones

A vector is strictly inward to a set at a point if small positive steps along it carry a ball
whose radius is proportional to the step size into the set. Unlike the closed tangent cone,
this excludes directions tangent to the boundary of a half-space.

For convex sets and base points in the set, membership is equivalent to reaching an interior
point along the positive ray.
The cone is open and convex, is invariant under positive scaling, and has ball estimates uniform
near each admissible point and vector (hence along any relatively continuous vector field). Any
convex set admitting a strictly inward vector has nonempty interior, so its open intersections
enjoy unique differentiability (`Convex.uniqueDiffOn_inter_of_mem_strictInwardCone`). Curves with
one-sided derivatives in the strict inward cone immediately enter and remain in the interior
(`HasDerivWithinAt.eventually_mem_interior_of_mem_strictInwardCone`,
`Convex.mem_interior_of_hasDerivWithinAt_Iic`,
`Convex.mapsTo_Ioo_interior_of_hasDerivWithinAt_Ico`). These estimates supply the local geometric
input for constructing strictly inward vector fields and their forward semiflows on models with
corners.

A derivative of dense range of a map into a convex set with nonempty interior sends strictly
inward directions to strictly inward directions
(`HasFDerivWithinAt.mapsTo_strictInwardCone`). Hence the strict inward cones of a convex model
are invariant under the derivatives of `C¹` changes of coordinates, and define a cone in each
tangent space of a manifold with corners.
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

/-- Small positive steps along a strictly inward vector lie in the interior, without any
convexity assumption. -/
theorem add_smul_mem_interior_of_mem_strictInwardCone (hv : v ∈ strictInwardCone s x) :
    ∃ δ > 0, ∀ t ∈ Ioo (0 : ℝ) δ, x + t • v ∈ interior s := by
  obtain ⟨ε, hε, δ, hδ, h⟩ := hv
  refine ⟨δ, hδ, fun t ht ↦ mem_interior_iff_mem_nhds.mpr ?_⟩
  exact Filter.mem_of_superset (ball_mem_nhds _ (mul_pos hε ht.1)) (h t ht)

/-- The strict inward cone at any fixed point of any set is open. -/
theorem isOpen_strictInwardCone (s : Set E) (x : E) : IsOpen (strictInwardCone s x) := by
  apply Metric.isOpen_iff.mpr
  rintro v ⟨ε, hε, δ, hδ, hv⟩
  refine ⟨ε / 2, half_pos hε, ?_⟩
  intro w hw
  refine ⟨ε / 2, half_pos hε, δ, hδ, fun t ht ↦ ?_⟩
  apply Subset.trans (ball_subset_ball' ?_) (hv t ht)
  have hd : dist (x + t • w) (x + t • v) = t * dist w v := by
    simp [dist_eq_norm, ← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos ht.1]
  rw [hd]
  have := mul_lt_mul_of_pos_left (mem_ball.mp hw) ht.1
  linarith

/-- The zero vector is strictly inward exactly at interior points. -/
@[simp]
theorem zero_mem_strictInwardCone_iff : (0 : E) ∈ strictInwardCone s x ↔ x ∈ interior s := by
  constructor
  · intro hv
    obtain ⟨δ, hδ, h⟩ := add_smul_mem_interior_of_mem_strictInwardCone hv
    simpa only [smul_zero, add_zero] using h (δ / 2) ⟨by positivity, by linarith⟩
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
  · intro hv
    obtain ⟨δ, hδ, h⟩ := add_smul_mem_interior_of_mem_strictInwardCone hv
    exact ⟨δ / 2, by positivity, h (δ / 2) ⟨by positivity, by linarith⟩⟩
  · rintro ⟨T, hT, hq⟩
    obtain ⟨ε, hε, δ, hδ, h⟩ := hs.exists_uniform_ball_subset_of_add_smul_mem_interior hT hq
    exact ⟨ε, hε, δ, hδ, h.self_of_nhds hx⟩

/-- The inward ball estimates can be chosen uniformly near any strictly inward point-vector
pair, as long as the perturbed starting point stays in the convex set. -/
theorem Convex.exists_uniform_ball_subset_of_mem_strictInwardCone (hs : Convex ℝ s)
    (hv : v ∈ strictInwardCone s x) :
    ∃ ε > 0, ∃ δ > 0, ∀ᶠ p : E × E in 𝓝 (x, v), p.1 ∈ s →
      ∀ t ∈ Ioo (0 : ℝ) δ, ball (p.1 + t • p.2) (ε * t) ⊆ s := by
  obtain ⟨δ, hδ, h⟩ := add_smul_mem_interior_of_mem_strictInwardCone hv
  exact hs.exists_uniform_ball_subset_of_add_smul_mem_interior
    (by positivity : 0 < δ / 2) (h (δ / 2) ⟨by positivity, by linarith⟩)

/-- If `X` is continuous within `u` at `x` and `X x ∈ strictInwardCone s x` for a convex set `s`,
then uniform inward ball estimates hold for `X` at all points of `s` sufficiently close to `x`
within `u`. -/
theorem Convex.exists_uniform_ball_subset_of_continuousWithinAt {u : Set E} (hs : Convex ℝ s)
    {X : E → E} (hv : X x ∈ strictInwardCone s x) (hX : ContinuousWithinAt X u x) :
    ∃ ε > 0, ∃ δ > 0, ∀ᶠ y in 𝓝[u] x, y ∈ s →
      ∀ t ∈ Ioo (0 : ℝ) δ, ball (y + t • X y) (ε * t) ⊆ s := by
  obtain ⟨ε, hε, δ, hδ, hev⟩ := hs.exists_uniform_ball_subset_of_mem_strictInwardCone hv
  exact ⟨ε, hε, δ, hδ, (continuousWithinAt_id.prodMk hX).eventually hev⟩

/-- If `X` is continuous within `u` at `x` and `X x ∈ strictInwardCone s x` for a convex set `s`,
then `X y ∈ strictInwardCone s y` for all `y ∈ s` sufficiently close to `x` within `u`. -/
theorem Convex.eventually_mem_strictInwardCone_of_continuousWithinAt {u : Set E} (hs : Convex ℝ s)
    {X : E → E} (hv : X x ∈ strictInwardCone s x) (hX : ContinuousWithinAt X u x) :
    ∀ᶠ y in 𝓝[u] x, y ∈ s → X y ∈ strictInwardCone s y := by
  obtain ⟨ε, hε, δ, hδ, hev⟩ := hs.exists_uniform_ball_subset_of_continuousWithinAt hv hX
  exact hev.mono fun _ hy hys ↦ ⟨ε, hε, δ, hδ, hy hys⟩

/-- If a convex set `s` admits a strictly inward vector at any point, then `u ∩ s` has unique
derivatives for every open set `u`. -/
theorem Convex.uniqueDiffOn_inter_of_mem_strictInwardCone {u : Set E} (hs : Convex ℝ s)
    (hu : IsOpen u) (hv : v ∈ strictInwardCone s x) : UniqueDiffOn ℝ (u ∩ s) := by
  obtain ⟨δ, hδ, h⟩ := add_smul_mem_interior_of_mem_strictInwardCone hv
  exact inter_comm s u ▸
    (uniqueDiffOn_convex hs ⟨_, h (δ / 2) ⟨half_pos hδ, half_lt_self hδ⟩⟩).inter hu

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
theorem Convex.convex_strictInwardCone (hs : Convex ℝ s) (x : E) :
    Convex ℝ (strictInwardCone s x) := by
  intro v hv w hw a b ha hb hab
  obtain ⟨εv, hεv, δv, hδv, hv⟩ := hv
  obtain ⟨εw, hεw, δw, hδw, hw⟩ := hw
  refine ⟨min εv εw, lt_min hεv hεw, min δv δw, lt_min hδv hδw, ?_⟩
  intro t ht z hz
  let d := z - (x + t • (a • v + b • w))
  have hd : ‖d‖ < min εv εw * t := by simpa [d, dist_eq_norm] using hz
  have hmem {u : E} {ε δ : ℝ}
      (hu : ∀ t ∈ Ioo (0 : ℝ) δ, ball (x + t • u) (ε * t) ⊆ s)
      (hδ : min δv δw ≤ δ) (hε : min εv εw ≤ ε) : x + t • u + d ∈ s := by
    apply hu t ⟨ht.1, ht.2.trans_le hδ⟩
    exact mem_ball.mpr (by
      simpa only [dist_eq_norm, add_sub_cancel_left] using
        hd.trans_le (mul_le_mul_of_nonneg_right hε ht.1.le))
  have h := hs (hmem hv (min_le_left _ _) (min_le_left _ _))
    (hmem hw (min_le_right _ _) (min_le_right _ _)) ha hb hab
  have heq : a • (x + t • v + d) + b • (x + t • w + d) =
      x + t • (a • v + b • w) + d := by
    calc
      _ = (a + b) • x + t • (a • v + b • w) + (a + b) • d := by module
      _ = _ := by rw [hab, one_smul, one_smul]
  rw [heq] at h
  simpa only [d, add_sub_cancel] using h

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

/-- **Derivatives preserve strict inwardness.** Let `f` send points of `s` near `x` into a convex
set `t` with nonempty interior. If `f` has a derivative `f'` of dense range within `s` at `x`,
then `f'` sends directions strictly inward to `s` at `x` to directions strictly inward to `t` at
`f x`. The point `f x` need not lie in `t`. Without the density of the range this fails, as for a
constant map. -/
theorem HasFDerivWithinAt.mapsTo_strictInwardCone {F : Type*} [SeminormedAddCommGroup F]
    [NormedSpace ℝ F] {t : Set F} {f : E → F} {f' : E →L[ℝ] F}
    (hf : HasFDerivWithinAt f f' s x) (hf' : DenseRange f') (ht : Convex ℝ t)
    (hti : (interior t).Nonempty) (hft : ∀ᶠ z in 𝓝[s] x, f z ∈ t) :
    MapsTo f' (strictInwardCone s x) (strictInwardCone t (f x)) := by
  intro v hv
  -- Small steps along a strictly inward direction tend to `x` within `s`.
  have hstep {u : E} (hu : u ∈ strictInwardCone s x) :
      Tendsto (fun τ : ℝ ↦ x + τ • u) (𝓝[>] 0) (𝓝[s] x) := by
    obtain ⟨δ, hδ, hint⟩ := add_smul_mem_interior_of_mem_strictInwardCone hu
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have : Tendsto (fun τ : ℝ ↦ x + τ • u) (𝓝 0) (𝓝 x) :=
        (continuous_const.add (continuous_id.smul continuous_const)).tendsto' _ _ (by simp)
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [Ioo_mem_nhdsGT hδ] with τ hτ using interior_subset (hint τ hτ)
  -- Hence `f x` lies in the closure of `t`, and it suffices to work with the closure.
  have hfx : f x ∈ closure t :=
    mem_closure_of_tendsto (hf.continuousWithinAt.tendsto.comp (hstep hv))
      ((hstep hv).eventually hft)
  have hint : interior (closure t) = interior t :=
    ht.interior_closure_eq_interior_of_nonempty_interior hti
  suffices f' v ∈ strictInwardCone (closure t) (f x) by
    obtain ⟨ε, hε, δ, hδ, h⟩ := this
    exact ⟨ε, hε, δ, hδ, fun τ hτ ↦
      (interior_maximal (h τ hτ) isOpen_ball).trans (hint.subset.trans interior_subset)⟩
  by_contra hnot
  -- The segment from `f x` to `f x + f' v` misses the interior of the closure of `t`.
  have hdisj : Disjoint (interior (closure t)) (segment ℝ (f x) (f x + f' v)) := by
    refine disjoint_right.mpr ?_
    rw [segment_eq_image']
    rintro _ ⟨τ, hτ, rfl⟩ hmem
    rw [add_sub_cancel_left] at hmem
    rcases hτ.1.eq_or_lt with rfl | hτ₀
    · simp only [zero_smul, add_zero] at hmem
      exact hnot (strictInwardCone_eq_univ_iff.mpr hmem ▸ mem_univ _)
    · exact hnot ((ht.closure.mem_strictInwardCone_iff hfx).mpr ⟨τ, hτ₀, hmem⟩)
  obtain ⟨g, c, hg0, hgt, hgs⟩ := geometric_hahn_banach_of_nonempty_interior ht.closure
    (convex_segment _ _) hdisj (hint ▸ hti) ⟨f x, left_mem_segment _ _ _⟩
  have hgfx : g (f x) = c := le_antisymm (hgt _ hfx) (hgs _ (left_mem_segment _ _ _))
  have hgv : 0 ≤ g (f' v) := by
    have := hgs _ (right_mem_segment _ _ _)
    rw [map_add, hgfx] at this
    linarith
  -- As `g` is nonzero and `f'` has dense range, `g ∘ f'` is positive somewhere.
  obtain ⟨w, hw⟩ : ∃ w, 0 < g (f' w) := by
    by_contra! h
    have hg : ⇑g = fun _ ↦ 0 := hf'.equalizer g.continuous continuous_const <| funext fun w ↦
      le_antisymm (h w) (by simpa using h (-w))
    exact hg0 (DFunLike.ext' hg)
  -- Perturb `v` towards `w` inside the open cone `strictInwardCone s x`.
  have hpert : ∀ᶠ ε in 𝓝[>] (0 : ℝ), v + ε • w ∈ strictInwardCone s x := by
    have : Tendsto (fun ε : ℝ ↦ v + ε • w) (𝓝 0) (𝓝 v) :=
      (continuous_const.add (continuous_id.smul continuous_const)).tendsto' _ _ (by simp)
    exact nhdsWithin_le_nhds (this.eventually ((isOpen_strictInwardCone s x).mem_nhds hv))
  obtain ⟨ε, hεv, hε⟩ := (hpert.and self_mem_nhdsWithin).exists
  set v' := v + ε • w
  have hpos : 0 < g (f' v') := by
    simp only [v', map_add, map_smul, smul_eq_mul]
    exact add_pos_of_nonneg_of_pos hgv (mul_pos hε hw)
  -- Small steps along `v'` stay in `s` and are sent into `t`, so `g ∘ f'` is nonpositive at `v'`.
  have hs : ∀ᶠ τ in 𝓝[>] (0 : ℝ), x + τ • v' ∈ s := (tendsto_nhdsWithin_iff.mp (hstep hεv)).2
  have hd : Tendsto (fun τ : ℝ ↦ τ • v') (𝓝[>] 0) (𝓝 0) :=
    ((continuous_id.smul continuous_const).tendsto' _ _ (by simp)).mono_left nhdsWithin_le_nhds
  have hcd : Tendsto (fun τ : ℝ ↦ τ⁻¹ • τ • v') (𝓝[>] 0) (𝓝 v') :=
    tendsto_const_nhds.congr' <| by
      filter_upwards [self_mem_nhdsWithin] with τ (hτ : 0 < τ)
      simp [smul_smul, hτ.ne']
  have hlim := hf.lim hd hs hcd
  refine hpos.not_ge (le_of_tendsto ((g.continuous.tendsto _).comp hlim) ?_)
  filter_upwards [(hstep hεv).eventually hft, self_mem_nhdsWithin] with τ hτ (hτ₀ : 0 < τ)
  simp only [Function.comp_apply, map_smul, map_sub, hgfx, smul_eq_mul]
  exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr hτ₀.le)
    (sub_nonpos.mpr (hgt _ (subset_closure hτ)))

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

/-! ### Interior entry and persistence along curves -/

section InteriorPersistence

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A curve whose right derivative at `a` lies in `strictInwardCone s (γ a)` lies in `interior s`
for all sufficiently small times strictly greater than `a`. No convexity of `s` is required. -/
theorem HasDerivWithinAt.eventually_mem_interior_of_mem_strictInwardCone {s : Set E} {γ : ℝ → E}
    {v : E} {a : ℝ} (hγ : HasDerivWithinAt γ v (Ici a) a)
    (hv : v ∈ TauCeti.strictInwardCone s (γ a)) :
    ∀ᶠ t in 𝓝[>] a, γ t ∈ interior s := by
  obtain ⟨ε, hε, δ, hδ, hball⟩ := TauCeti.mem_strictInwardCone_iff.mp hv
  filter_upwards [((hasDerivWithinAt_iff_isLittleO.mp hγ).bound (half_pos hε)).filter_mono
    (nhdsWithin_mono a Ioi_subset_Ici_self), Ioo_mem_nhdsGT (lt_add_of_pos_right a hδ)]
    with t ht hIoo
  have hpos : 0 < t - a := sub_pos.mpr hIoo.1
  rw [Real.norm_of_nonneg hpos.le] at ht
  refine mem_interior.mpr ⟨ball (γ t) (ε / 2 * (t - a)), Subset.trans (fun z hz ↦ ?_)
    (hball (t - a) ⟨hpos, sub_lt_iff_lt_add'.mpr hIoo.2⟩), isOpen_ball,
    mem_ball_self (mul_pos (half_pos hε) hpos)⟩
  rw [mem_ball, dist_eq_norm] at hz ⊢
  calc ‖z - (γ a + (t - a) • v)‖ = ‖(z - γ t) + (γ t - γ a - (t - a) • v)‖ := by congr 1; abel
    _ ≤ ‖z - γ t‖ + ‖γ t - γ a - (t - a) • v‖ := norm_add_le _ _
    _ < ε * (t - a) := by linarith

/-- In a convex set `C`, if `γ` lies in `C` for times just before `t` and has left derivative at `t`
in `strictInwardCone C (γ t)`, then `γ t` already lies in `interior C`. -/
theorem Convex.mem_interior_of_hasDerivWithinAt_Iic {C : Set E} (hC : Convex ℝ C) {γ : ℝ → E}
    {v : E} {t : ℝ} (hγ' : HasDerivWithinAt γ v (Iic t) t) (hγC : ∀ᶠ s in 𝓝[<] t, γ s ∈ C)
    (hv : v ∈ TauCeti.strictInwardCone C (γ t)) :
    γ t ∈ interior C := by
  obtain ⟨ε, hε, δ, hδ, hball⟩ := TauCeti.mem_strictInwardCone_iff.mp hv
  obtain ⟨s, hs_err, hsC, hsIoo⟩ := ((((hasDerivWithinAt_iff_isLittleO.mp hγ').bound
    (half_pos hε)).filter_mono (nhdsWithin_mono t Iio_subset_Iic_self)).and
    (hγC.and (eventually_mem_set.mpr (Ioo_mem_nhdsLT (sub_lt_self t hδ))))).exists
  set h := t - s; have hh_pos : 0 < h := sub_pos.mpr hsIoo.2
  rw [Real.norm_eq_abs, abs_sub_comm, abs_of_pos hh_pos] at hs_err
  refine mem_interior.mpr ⟨ball (γ t) (ε * h / 4), fun z hz ↦ ?_,
    isOpen_ball, mem_ball_self (by positivity)⟩
  rw [mem_ball, dist_eq_norm] at hz
  have hq : (2 : ℝ) • z - γ s ∈ C := by
    refine hball h ⟨hh_pos, sub_lt_comm.mp hsIoo.1⟩ (mem_ball_iff_norm.mpr ?_)
    calc ‖(2 : ℝ) • z - γ s - (γ t + h • v)‖
        = ‖(2 : ℝ) • (z - γ t) - (γ s - γ t - (s - t) • v)‖ := by congr 1; simp only [h]; module
      _ ≤ 2 * ‖z - γ t‖ + ‖γ s - γ t - (s - t) • v‖ :=
          (norm_sub_le _ _).trans (by rw [norm_smul, Real.norm_of_nonneg zero_le_two])
      _ < ε * h := by linarith
  rw [← show (1 / 2 : ℝ) • γ s + (1 / 2 : ℝ) • ((2 : ℝ) • z - γ s) = z by module]
  exact hC hsC hq (by norm_num) (by norm_num) (by norm_num)

/-- Any curve in a convex set `C` on `[a, b]` whose left derivatives on `(a, b]` lie in the strict
inward cone of `C` stays in `interior C` for all `t ∈ (a, b]`. -/
theorem Convex.mapsTo_Ioc_interior_of_hasDerivWithinAt_Iic {C : Set E} (hC : Convex ℝ C)
    {v γ : ℝ → E} {a b : ℝ} (hγ : MapsTo γ (Icc a b) C)
    (hγ' : ∀ t ∈ Ioc a b, HasDerivWithinAt γ (v t) (Iic t) t)
    (hv : ∀ t ∈ Ioc a b, v t ∈ TauCeti.strictInwardCone C (γ t)) :
    MapsTo γ (Ioc a b) (interior C) := fun t ht ↦
  hC.mem_interior_of_hasDerivWithinAt_Iic (hγ' t ht)
    (Filter.mem_of_superset (Ioo_mem_nhdsLT ht.1) fun _ hs ↦ hγ ⟨hs.1.le, hs.2.le.trans ht.2⟩)
    (hv t ht)

/-- Any curve in a convex set `C` on `[a, b]` whose derivatives within `[a, b]` on `(a, b]` lie in
the strict inward cone of `C` maps `(a, b]` into `interior C`. -/
theorem Convex.mapsTo_Ioc_interior_of_hasDerivWithinAt_Icc {C : Set E} (hC : Convex ℝ C)
    {v γ : ℝ → E} {a b : ℝ} (hγ : MapsTo γ (Icc a b) C)
    (hγ' : ∀ t ∈ Ioc a b, HasDerivWithinAt γ (v t) (Icc a b) t)
    (hv : ∀ t ∈ Ioc a b, v t ∈ TauCeti.strictInwardCone C (γ t)) :
    MapsTo γ (Ioc a b) (interior C) := hC.mapsTo_Ioc_interior_of_hasDerivWithinAt_Iic hγ
  (fun t ht ↦ (hγ' t ht).mono_of_mem_nhdsWithin <| mem_nhdsWithin.mpr
    ⟨Ioi a, isOpen_Ioi, ht.1, fun _ hs ↦ ⟨hs.1.le, hs.2.trans ht.2⟩⟩) hv

/-- Any curve in a convex set `C` on `[a, b)` whose derivatives within `[a, b)` on `(a, b)` lie in
the strict inward cone of `C` maps `(a, b)` into `interior C`. -/
theorem Convex.mapsTo_Ioo_interior_of_hasDerivWithinAt_Ico {C : Set E} (hC : Convex ℝ C)
    {v γ : ℝ → E} {a b : ℝ} (hγ : MapsTo γ (Ico a b) C)
    (hγ' : ∀ t ∈ Ioo a b, HasDerivWithinAt γ (v t) (Ico a b) t)
    (hv : ∀ t ∈ Ioo a b, v t ∈ TauCeti.strictInwardCone C (γ t)) :
    MapsTo γ (Ioo a b) (interior C) := fun t ht ↦ hC.mem_interior_of_hasDerivWithinAt_Iic
  (((hγ' t ht).hasDerivAt (Ico_mem_nhds ht.1 ht.2)).hasDerivWithinAt)
  (Filter.mem_of_superset (Ioo_mem_nhdsLT ht.1) fun _ hs ↦ hγ ⟨hs.1.le, hs.2.trans ht.2⟩) (hv t ht)

end InteriorPersistence
