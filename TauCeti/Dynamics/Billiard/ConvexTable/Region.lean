/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Dynamics.Billiard.ConvexTable
public import Mathlib.Analysis.Convex.Strict
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Normed.Affine.AddTorsorBases
import Mathlib.Topology.Instances.Real.Lemmas
import TauCeti.Analysis.Convex.Caratheodory
import TauCeti.LinearAlgebra.Complex.Module

/-!
# The region bounded by a convex table

The *region* `Ω` of a convex billiard table `γ` (`TauCeti.ConvexTable.region`) is the convex hull
of the image of `γ`. It is the closed convex hull: the image is compact, so its convex hull is
compact in the plane.

The defining inequality of a table, `0 < τ(s) × (γ t − γ s)` for `t ≢ s`, passes to the convex
hull: every point of `Ω` other than `γ s` lies strictly to the left of the tangent line at `γ s`
(`TauCeti.ConvexTable.im_conj_deriv_mul_sub_pos_of_mem_region`), since the open half-plane with
the point `γ s` added is convex. Every linear functional on `ℂ` that kills the unit tangent
`τ(s)` is a multiple of `w ↦ τ(s) × w`. Hence the image of `γ` spans the plane (a functional
constant on the image kills every tangent), and a supporting line of `Ω` at a point `z` of its
frontier, which supports `Ω` at a point `γ s` of the curve where the functional is maximal on the
curve, is the tangent line at `γ s`, so `z = γ s`.

## Main declarations

* `TauCeti.ConvexTable.region`: the region `Ω` bounded by a table.
* `TauCeti.ConvexTable.isCompact_region`: `Ω` is compact.
* `TauCeti.ConvexTable.region_shift`, `TauCeti.ConvexTable.region_ofLE`,
  `TauCeti.ConvexTable.region_rigidMotion`: the region under the operations on tables.
* `TauCeti.ConvexTable.im_conj_deriv_mul_sub_pos_of_mem_region`: `Ω` minus the point of tangency
  lies in the open half-plane to the left of each tangent line.
* `TauCeti.ConvexTable.interior_region_nonempty`: `Ω` has nonempty interior.
* `TauCeti.ConvexTable.frontier_region`: the frontier of `Ω` is the image of the table.
* `TauCeti.ConvexTable.mem_region_iff`: `Ω` is the set of points to the left of or on every
  tangent line.
* `TauCeti.ConvexTable.interior_region`: the interior of `Ω` is `Ω` minus the image of the table.
* `TauCeti.ConvexTable.mem_interior_region_iff`: the interior of `Ω` is the set of points strictly
  to the left of every tangent line.
* `TauCeti.ConvexTable.strictConvex_region`: `Ω` is strictly convex.
* `TauCeti.ConvexTable.region_circle`: the region of the circle of radius `R` is the closed disc.

## References

* Serge Tabachnikov, *Geometry and Billiards*, Student Mathematical Library 30, American
  Mathematical Society, 2005, Chapter 3.
-/

public section

noncomputable section

open Function Set Filter Topology Complex
open scoped ComplexConjugate

namespace TauCeti

namespace ConvexTable

variable {k : ℕ∞} {ℓ : ℝ} [Fact (0 < ℓ)] (T : ConvexTable k ℓ)

/-- The **region** `Ω` bounded by a convex table: the convex hull of the image of the table. It is
compact (`TauCeti.ConvexTable.isCompact_region`), so it is also the closed convex hull. -/
def region : Set ℂ := convexHull ℝ (range T)

theorem region_def : T.region = convexHull ℝ (range T) := (rfl)

theorem convex_region : Convex ℝ T.region := convex_convexHull ℝ _

theorem subset_region : range T ⊆ T.region := subset_convexHull ℝ _

@[simp]
theorem apply_mem_region (s : ℝ) : T s ∈ T.region := T.subset_region (mem_range_self s)

/-- The image of a table is compact. -/
theorem isCompact_range : IsCompact (range T) :=
  Function.Periodic.compact_of_continuous T.periodic (Fact.out : 0 < ℓ).ne' T.continuous

/-- The region of a table is compact. -/
theorem isCompact_region : IsCompact T.region := T.isCompact_range.convexHull

theorem isClosed_region : IsClosed T.region := T.isCompact_region.isClosed

/-- Reparametrizing a table by a shift does not change its region. -/
@[simp]
theorem region_shift (c : ℝ) : (T.shift c).region = T.region := by
  rw [region_def, region_def, range_shift]

/-- Weakening the smoothness of a table does not change its region. -/
@[simp]
theorem region_ofLE {j : ℕ∞} (hj : 1 ≤ j) (hjk : j ≤ k) : (T.ofLE hj hjk).region = T.region := by
  rw [region_def, region_def, coe_ofLE]

/-- The region of a table moved by the rigid motion `z ↦ a z + b` is the image of its region. -/
@[simp]
theorem region_rigidMotion (a : Circle) (b : ℂ) :
    (T.rigidMotion a b).region = (fun z => a * z + b) '' T.region := by
  let f : ℂ →ᵃ[ℝ] ℂ := (LinearMap.mulLeft ℝ (a : ℂ)).toAffineMap + AffineMap.const ℝ ℂ b
  have hf : ⇑f = fun z => a * z + b := by
    funext z
    simp [f]
  rw [region_def, region_def, ← hf, f.image_convexHull, ← range_comp]
  congr 2
  funext s
  simp [hf]

/-- At a local maximum of `f ∘ γ` for a continuous linear functional `f`, the functional kills the
unit tangent. -/
private theorem map_deriv_eq_zero_of_isLocalMax {f : ℂ →L[ℝ] ℝ} {s : ℝ}
    (h : IsLocalMax (fun t => f (T t)) s) : f (deriv T s) = 0 :=
  h.hasDerivAt_eq_zero (f.hasFDerivAt.comp_hasDerivAt s (T.hasDerivAt s))

/-- **A supporting line of the region is tangent to the table.** A continuous linear functional
`f` attains its maximum on the region at a point `γ s` of the curve, and there it kills the unit
tangent, so `f w = f (i τ(s)) · (τ(s) × w)`. -/
private theorem exists_forall_mem_region_le_and_apply_eq (f : ℂ →L[ℝ] ℝ) :
    ∃ s, (∀ w ∈ T.region, f w ≤ f (T s)) ∧
      ∀ w, f w = f (I * deriv T s) * (conj (deriv T s) * w).im := by
  obtain ⟨_, ⟨s, rfl⟩, hmax⟩ :=
    T.isCompact_range.exists_isMaxOn (range_nonempty T) f.continuous.continuousOn
  refine ⟨s, fun w hw => convexHull_min (fun w hw => hmax hw) (convex_halfSpace_le f.isLinear _)
    hw, f.toLinearMap.apply_eq_mul_im_conj_mul (T.conj_deriv_mul_deriv s) ?_⟩
  exact T.map_deriv_eq_zero_of_isLocalMax (Eventually.of_forall fun t => hmax (mem_range_self t))

/-- **The region lies to the left of each tangent line.** Every point `z ≠ γ s` of the region
satisfies `0 < τ(s) × (z − γ s)`. -/
theorem im_conj_deriv_mul_sub_pos_of_mem_region {s : ℝ} {z : ℂ} (hz : z ∈ T.region)
    (hzs : z ≠ T s) : 0 < (conj (deriv T s) * (z - T s)).im := by
  set τ := deriv T s
  let H : Set ℂ := {w | 0 < (conj τ * (w - T s)).im} ∪ {T s}
  have hH : Convex ℝ H := by
    refine convex_iff_forall_pos.2 fun x hx y hy a b ha hb hab => ?_
    by_cases hxy : x = T s ∧ y = T s
    · rw [hxy.1, hxy.2, ← add_smul, hab, one_smul]
      exact Or.inr rfl
    refine Or.inl ?_
    simp only [H, mem_union, mem_ofPred_eq, mem_singleton_iff] at hx hy ⊢
    rw [Complex.im_conj_mul_smul_add_smul_sub hab]
    rcases hx with hx | rfl <;> rcases hy with hy | rfl
    · positivity
    · simp only [sub_self, mul_zero, zero_im]; positivity
    · simp only [sub_self, mul_zero, zero_im]; positivity
    · exact absurd ⟨rfl, rfl⟩ hxy
  have hsub : range T ⊆ H := by
    rintro _ ⟨t, rfl⟩
    by_cases ht : (s : AddCircle ℓ) = t
    · exact Or.inr (T.apply_eq_apply_iff.2 ht).symm
    · exact Or.inl (T.im_conj_deriv_mul_sub_pos ht)
  rcases convexHull_min hsub hH hz with h | h
  · exact h
  · exact absurd h hzs

/-- A point of the region with `τ(s) × (z − γ s) ≤ 0` is the point of tangency `γ s`. -/
theorem eq_of_mem_region_of_im_conj_deriv_mul_sub_nonpos {s : ℝ} {z : ℂ} (hz : z ∈ T.region)
    (h : (conj (deriv T s) * (z - T s)).im ≤ 0) : z = T s :=
  by_contra fun hzs => (T.im_conj_deriv_mul_sub_pos_of_mem_region hz hzs).not_ge h

/-- Every point of the region satisfies `0 ≤ τ(s) × (z − γ s)`. -/
theorem im_conj_deriv_mul_sub_nonneg_of_mem_region {s : ℝ} {z : ℂ} (hz : z ∈ T.region) :
    0 ≤ (conj (deriv T s) * (z - T s)).im := by
  by_cases h : z = T s
  · simp [h]
  · exact (T.im_conj_deriv_mul_sub_pos_of_mem_region hz h).le

/-- The image of a table spans the plane as an affine space. -/
theorem affineSpan_range_eq_top : affineSpan ℝ (range T) = ⊤ := by
  by_contra hne
  have hlt : vectorSpan ℝ (range T) < ⊤ := by
    rw [lt_top_iff_ne_top, ← direction_affineSpan]
    exact fun h => hne ((AffineSubspace.direction_eq_top_iff_of_nonempty
      ((range_nonempty T).mono (subset_affineSpan ℝ _))).1 h)
  obtain ⟨f, hf0, hf⟩ := (vectorSpan ℝ (range T)).exists_le_ker_of_lt_top hlt
  have hconst (t : ℝ) : f (T t) = f (T 0) := by
    have := hf (vsub_mem_vectorSpan ℝ (mem_range_self t) (mem_range_self 0))
    rwa [LinearMap.mem_ker, vsub_eq_sub, map_sub, sub_eq_zero] at this
  have hτ (s : ℝ) : f (deriv T s) = 0 :=
    T.map_deriv_eq_zero_of_isLocalMax (f := LinearMap.toContinuousLinearMap f)
      (Eventually.of_forall fun t => by simp [hconst])
  -- `f` also kills `i τ(0)`, so `f = 0`.
  have hI : f (I * deriv T 0) = 0 := by
    have hℓ : (0 : ℝ) < ℓ := Fact.out
    have hpos := T.im_conj_deriv_mul_sub_pos (s := 0) (t := ℓ / 2)
      ((AddCircle.coe_eq_coe_iff_of_mem_Ico (a := 0) ⟨le_rfl, by linarith⟩
        ⟨by linarith, by linarith⟩).not.2 (by linarith))
    have h := f.apply_eq_mul_im_conj_mul (T.conj_deriv_mul_deriv 0) (hτ 0) (T (ℓ / 2) - T 0)
    rw [map_sub, hconst, sub_self] at h
    exact (mul_eq_zero.1 h.symm).resolve_right hpos.ne'
  exact hf0 (LinearMap.ext fun w => by
    rw [f.apply_eq_mul_im_conj_mul (T.conj_deriv_mul_deriv 0) (hτ 0), hI, zero_mul,
      LinearMap.zero_apply])

/-- The region of a table has nonempty interior. -/
theorem interior_region_nonempty : (interior T.region).Nonempty :=
  interior_convexHull_nonempty_iff_affineSpan_eq_top.2 T.affineSpan_range_eq_top

/-- The points `γ s − ε i τ(s)` with `ε > 0`, strictly to the right of the tangent line at `γ s`,
lie outside the region. -/
private theorem sub_smul_I_mul_deriv_notMem_region (s : ℝ) {ε : ℝ} (hε : 0 < ε) :
    T s - ε • (I * deriv T s) ∉ T.region := fun h => by
  have := T.im_conj_deriv_mul_sub_pos_of_mem_region (s := s) h (by
    rw [Ne, sub_eq_self, smul_eq_zero, not_or]
    exact ⟨hε.ne', mul_ne_zero I_ne_zero (T.deriv_ne_zero s)⟩)
  have h2 : conj (deriv T s) * (T s - ε • (I * deriv T s) - T s) = -(ε * I) := by
    rw [sub_sub_cancel_left, real_smul]
    linear_combination (-(ε : ℂ) * I) * T.conj_deriv_mul_deriv s
  rw [h2] at this
  have hneg : 0 < -ε := by simpa using this
  linarith

/-- **The frontier of the region is the image of the table.** -/
@[simp]
theorem frontier_region : frontier T.region = range T := by
  refine Subset.antisymm (fun z hz => ?_) ?_
  · rw [T.isClosed_region.frontier_eq] at hz
    by_contra hzT
    -- A supporting functional at `z`.
    obtain ⟨f, hf⟩ := geometric_hahn_banach_open_point (convex_region T).interior isOpen_interior
      hz.2
    have hle : T.region ⊆ {w | f w ≤ f z} := by
      rw [← T.isClosed_region.closure_eq,
        ← (convex_region T).closure_interior_eq_closure_of_nonempty_interior
          T.interior_region_nonempty]
      exact closure_minimal (fun w hw => (hf w hw).le) (isClosed_le f.continuous continuous_const)
    -- `f` is maximal on the region at some `γ s`, where it is tangent to the curve.
    obtain ⟨s, hmax, hlin⟩ := T.exists_forall_mem_region_le_and_apply_eq f
    have hzs : f z ≤ f (T s) := hmax z hz.1
    have hfI : f (I * deriv T s) ≠ 0 := fun h0 => by
      obtain ⟨a, ha⟩ := T.interior_region_nonempty
      have := hf a ha
      rw [hlin a, hlin z, h0, zero_mul, zero_mul] at this
      exact lt_irrefl _ this
    have h := hlin (z - T s)
    rw [map_sub, sub_eq_zero.2 (le_antisymm hzs (hle (T.apply_mem_region s)))] at h
    exact hzT ⟨s, (T.eq_of_mem_region_of_im_conj_deriv_mul_sub_nonpos hz.1
      ((mul_eq_zero.1 h.symm).resolve_left hfI).le).symm⟩
  · rintro _ ⟨s, rfl⟩
    rw [T.isClosed_region.frontier_eq]
    refine ⟨T.apply_mem_region s, fun hint => ?_⟩
    have ht : Tendsto (fun ε : ℝ => T s - ε • (I * deriv T s)) (𝓝[>] 0) (𝓝 (T s)) := by
      have : Continuous fun ε : ℝ => T s - ε • (I * deriv T s) := by fun_prop
      have h0 := (this.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
      simpa using h0
    obtain ⟨ε, hmem, hε⟩ := ((ht.eventually_mem (isOpen_interior.mem_nhds hint)).and
      eventually_mem_nhdsWithin).exists
    exact T.sub_smul_I_mul_deriv_notMem_region s hε (interior_subset hmem)

/-- **The interior of the region** is the region with the image of the table removed. -/
theorem interior_region : interior T.region = T.region \ range T := by
  rw [← self_sdiff_frontier, frontier_region]

/-- A point outside the region lies strictly to the right of some tangent line:
`τ(s) × (z − γ s) < 0` for some `s`. -/
private theorem exists_im_conj_deriv_mul_sub_neg_of_notMem_region {z : ℂ}
    (hz : z ∉ T.region) : ∃ s, (conj (deriv T s) * (z - T s)).im < 0 := by
  -- A functional separating `z` from the region, maximal on the curve at `γ s`.
  obtain ⟨f, u, hfu, hzu⟩ := geometric_hahn_banach_closed_point T.convex_region T.isClosed_region hz
  obtain ⟨s, hmax, hlin⟩ := T.exists_forall_mem_region_le_and_apply_eq f
  -- `f (i τ(s))` is nonpositive, as an interior point `a` does not lie beyond `γ s`, while `z`
  -- does.
  have hz' : 0 < f (I * deriv T s) * (conj (deriv T s) * (z - T s)).im := by
    rw [← hlin, map_sub]
    linarith [hfu _ (T.apply_mem_region s)]
  obtain ⟨a, ha⟩ := T.interior_region_nonempty
  rw [interior_region] at ha
  have ha' : f (I * deriv T s) * (conj (deriv T s) * (a - T s)).im ≤ 0 := by
    rw [← hlin, map_sub, sub_nonpos]
    exact hmax a ha.1
  exact ⟨s, neg_of_mul_pos_right hz' (nonpos_of_mul_nonpos_left ha'
    (T.im_conj_deriv_mul_sub_pos_of_mem_region ha.1 fun h => ha.2 ⟨s, h.symm⟩))⟩

/-- A point lies in the region exactly when it lies to the left of every tangent line, or on it:
`0 ≤ τ(s) × (z − γ s)` for all `s`. -/
theorem mem_region_iff {z : ℂ} :
    z ∈ T.region ↔ ∀ s, 0 ≤ (conj (deriv T s) * (z - T s)).im :=
  ⟨fun hz _ => T.im_conj_deriv_mul_sub_nonneg_of_mem_region hz, fun h => by_contra fun hz =>
    let ⟨s, hs⟩ := T.exists_im_conj_deriv_mul_sub_neg_of_notMem_region hz
    (h s).not_gt hs⟩

/-- A point lies in the interior of the region exactly when it lies strictly to the left of every
tangent line: `0 < τ(s) × (z − γ s)` for all `s`. -/
theorem mem_interior_region_iff {z : ℂ} :
    z ∈ interior T.region ↔ ∀ s, 0 < (conj (deriv T s) * (z - T s)).im := by
  rw [interior_region]
  exact ⟨fun hz s => T.im_conj_deriv_mul_sub_pos_of_mem_region hz.1 fun h => hz.2 ⟨s, h.symm⟩,
    fun h => ⟨T.mem_region_iff.2 fun s => (h s).le, fun ⟨s, hs⟩ => by simpa [hs] using h s⟩⟩

/-- **The region of a table is strictly convex.** -/
theorem strictConvex_region : StrictConvex ℝ T.region := by
  intro x hx y hy hxy a b ha hb hab
  have hp : a • x + b • y ∈ T.region := T.convex_region hx hy ha.le hb.le hab
  by_contra hint
  obtain ⟨s, hs⟩ : a • x + b • y ∈ range T := by
    by_contra hT
    exact hint (T.interior_region ▸ ⟨hp, hT⟩)
  have hzero := Complex.im_conj_mul_smul_add_smul_sub hab (deriv T s) x y (T s)
  rw [← hs, sub_self, mul_zero, zero_im] at hzero
  have hx' := T.im_conj_deriv_mul_sub_nonneg_of_mem_region (s := s) hx
  have hy' := T.im_conj_deriv_mul_sub_nonneg_of_mem_region (s := s) hy
  have h1 := T.eq_of_mem_region_of_im_conj_deriv_mul_sub_nonpos hx (by nlinarith)
  have h2 := T.eq_of_mem_region_of_im_conj_deriv_mul_sub_nonpos hy (by nlinarith)
  exact hxy (h1.trans h2.symm)

attribute [local instance] Complex.finrank_real_complex_fact in
/-- The region of the circle of radius `R` is the closed disc of radius `R`. -/
@[simp]
theorem region_circle (R : ℝ) [Fact (0 < 2 * Real.pi * R)] :
    (circle R).region = Metric.closedBall 0 R := by
  rw [region_def, range_circle, convexHull_sphere_eq_closedBall]

end ConvexTable

end TauCeti
