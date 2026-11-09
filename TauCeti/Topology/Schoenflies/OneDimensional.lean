/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Ball.Action
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import TauCeti.Geometry.Manifold.LocallyFlat.Bicollar
import TauCeti.AlgebraicTopology.Sphere.Zero
import TauCeti.Analysis.Normed.Module.Ball.Homeomorph
import TauCeti.Geometry.Sphere.Circle
import TauCeti.Topology.Circle.Arc
import TauCeti.Topology.JordanCurve.Separation

/-!
# The generalized Schoenflies theorem in dimension one

M. Brown's generalized Schoenflies theorem says that if `Σ ⊆ Sᵐ` is the zero slice of a bicollar
`β : Sᵐ⁻¹ × ℝ → Sᵐ`, then the closure of each component of `Sᵐ \ Σ` is homeomorphic to the closed
disc `Dᵐ` by a homeomorphism carrying the frontier `Σ` onto the boundary sphere `∂Dᵐ`. Brown's
proof recognizes the two closures as cells by collapsing cellular sets. In dimension one the
statement is elementary, and this file proves the case `m = 1` directly from the arcs of the
circle.

Here `Sᵐ⁻¹ = S⁰` is the unit sphere of a one-dimensional real normed space `E`, two antipodal
points, and `S¹` is the unit sphere of a two-dimensional real normed space `F`. The image of an
injective map `σ : S⁰ → S¹` is a pair of distinct points of the circle, and nothing more is needed:
in dimension one every such pair is bicollared, and the conclusions hold without a collar.

* Each component of the complement of `range σ` has frontier `range σ`
  (`TauCeti.frontier_connectedComponentIn_compl_range_sphere_of_finrank_eq_one`).
* Its closure is homeomorphic to the closed unit ball `D¹` of `E` by a homeomorphism carrying
  `range σ` onto the unit sphere `∂D¹ = S⁰`
  (`TauCeti.exists_homeomorph_closure_connectedComponentIn_compl_range_sphere_of_finrank_eq_one`).
* When `σ` is the zero slice of a bicollar `b`, the two collar arcs `b(u, t)`, `t > 0`, and
  `b(u, t)`, `t < 0`, at a point `u` of `S⁰` lie in different components
  (`TauCeti.IsBicollar.connectedComponentIn_compl_range_ne_of_finrank_eq_one`). In higher
  dimensions each of the two sides of a bicollar is connected and lies in one component; in
  dimension one each side consists of two arcs, one at each point of `S⁰`, and the two arcs of one
  side may lie in the same component: a bicollar of `{1, -1} ⊆ S¹` can send both of its positive
  arcs, at `1` and at `-1`, into the upper half circle.

The proofs read the circle through a homeomorphism with Mathlib's `Circle`, on which two distinct
points cut out the two open arcs `Circle.path x y '' Set.Ioo 0 1`
(`Circle.connectedComponentIn_compl_pair`), with closures the closed arcs
(`Circle.exists_homeomorph_closure_connectedComponentIn_compl_pair`). For the collar arcs, the
image of `σ` is the frontier of every component, so an open neighbourhood swept out by the collar
line through `u` meets the component on each side of `σ u`.

## Main results

* `TauCeti.frontier_connectedComponentIn_compl_range_sphere_of_finrank_eq_one`: the frontier of
  each complementary component is the embedded `S⁰`.
* `TauCeti.exists_homeomorph_closure_connectedComponentIn_compl_range_sphere_of_finrank_eq_one`:
  the closure of each complementary component is a closed `1`-cell with boundary the embedded
  `S⁰`.
* `TauCeti.IsBicollar.connectedComponentIn_compl_range_ne_of_finrank_eq_one`: at each point of
  `S⁰` the two collar arcs lie in different complementary components.

## References

* M. Brown, *A proof of the generalized Schoenflies theorem*, Bull. Amer. Math. Soc. 66 (1960),
  74–76, Theorem 5.
-/

public section

namespace TauCeti

open Metric Module Set Topology

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] {σ : sphere (0 : E) 1 → sphere (0 : F) 1} {x : sphere (0 : F) 1}

/-- Read through `TauCeti.sphereHomeomorphCircleOfFinrankEqTwo`, the image of an injective map of
the `0`-sphere into the circle is a pair of distinct points of `Circle`. -/
private lemma exists_image_range_eq_pair_circle (hE : finrank ℝ E = 1) (hF : finrank ℝ F = 2)
    (hσ : Function.Injective σ) :
    ∃ a b : Circle, a ≠ b ∧ sphereHomeomorphCircleOfFinrankEqTwo hF '' range σ = {a, b} := by
  have : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ) (by omega)
  obtain ⟨u, hu⟩ := (NormedSpace.sphere_nonempty (x := (0 : E))).mpr zero_le_one
  exact ⟨_, _, (sphereHomeomorphCircleOfFinrankEqTwo hF).injective.ne
    (hσ.ne (ne_neg_of_mem_unit_sphere ℝ ⟨u, hu⟩)),
    by rw [range_eq_pair_of_finrank_eq_one hE σ ⟨u, hu⟩, image_pair]⟩

/-- **The one-dimensional Schoenflies theorem, frontier form.** For an injective map `σ` of the
`0`-sphere into the circle, each component of the complement of the image of `σ` has that image as
its frontier. -/
theorem frontier_connectedComponentIn_compl_range_sphere_of_finrank_eq_one
    (hE : finrank ℝ E = 1) (hF : finrank ℝ F = 2) (hσ : Function.Injective σ)
    (hx : x ∉ range σ) : frontier (connectedComponentIn (range σ)ᶜ x) = range σ := by
  -- Read the circle as Mathlib's `Circle`.
  let e := sphereHomeomorphCircleOfFinrankEqTwo hF
  obtain ⟨a, b, hab, hr⟩ := exists_image_range_eq_pair_circle hE hF hσ
  have hx' : e x ∉ ({a, b} : Set Circle) := by rwa [← hr, e.injective.mem_set_image]
  apply e.injective.image_injective
  rw [e.image_frontier, e.image_connectedComponentIn hx, e.image_compl, hr,
    Circle.frontier_connectedComponentIn_compl_pair hab hx']

/-- **The one-dimensional Schoenflies theorem.** For an injective map `σ` of the `0`-sphere `S⁰`,
the unit sphere of a one-dimensional real normed space `E`, into the circle, the closure of each
component of the complement of the image of `σ` is homeomorphic to the closed unit ball `D¹` of
`E`, by a homeomorphism carrying the image of `σ` onto the unit sphere `S⁰ = ∂D¹`. -/
theorem exists_homeomorph_closure_connectedComponentIn_compl_range_sphere_of_finrank_eq_one
    (hE : finrank ℝ E = 1) (hF : finrank ℝ F = 2) (hσ : Function.Injective σ)
    (hx : x ∉ range σ) :
    ∃ h : closure (connectedComponentIn (range σ)ᶜ x) ≃ₜ closedBall (0 : E) 1,
      ∀ y : closure (connectedComponentIn (range σ)ᶜ x),
        (y : sphere (0 : F) 1) ∈ range σ ↔ ‖(h y : E)‖ = 1 := by
  -- Read the circle as Mathlib's `Circle`, where the closure of the component is an arc.
  let e := sphereHomeomorphCircleOfFinrankEqTwo hF
  obtain ⟨a, b, hab, hr⟩ := exists_image_range_eq_pair_circle hE hF hσ
  have key (w : sphere (0 : F) 1) : w ∈ range σ ↔ e w ∈ ({a, b} : Set Circle) := by
    rw [← hr, e.injective.mem_set_image]
  have hcl (w : sphere (0 : F) 1) :
      w ∈ closure (connectedComponentIn (range σ)ᶜ x) ↔
        e w ∈ closure (connectedComponentIn {a, b}ᶜ (e x)) := by
    rw [← e.injective.mem_set_image, e.image_closure, e.image_connectedComponentIn hx,
      e.image_compl, hr]
  obtain ⟨φ, hφ⟩ :=
    Circle.exists_homeomorph_closure_connectedComponentIn_compl_pair hab ((key x).not.mp hx)
  obtain ⟨ι, hι⟩ := exists_homeomorph_unitInterval_closedBall hE
  refine ⟨(e.subtype hcl).trans (φ.trans ι), fun y => ?_⟩
  rw [Homeomorph.trans_apply, Homeomorph.trans_apply, hι, ← hφ, Homeomorph.subtype_apply_coe,
    key]

/-- **The collar arcs of a bicollared `0`-sphere in the circle.** If `b` is a bicollar of an
injective map `σ` of the `0`-sphere into the circle, then at each point `u` of the `0`-sphere the
collar arc `b(u, t)`, `t > 0`, and the collar arc `b(u, t)`, `t < 0`, lie in different components of
the complement of the image of `σ`. -/
theorem IsBicollar.connectedComponentIn_compl_range_ne_of_finrank_eq_one
    (hE : finrank ℝ E = 1) (hF : finrank ℝ F = 2) {b : sphere (0 : E) 1 × ℝ → sphere (0 : F) 1}
    (hb : IsBicollar σ b) (u : sphere (0 : E) 1) {s t : ℝ} (hs : 0 < s) (ht : t < 0) :
    connectedComponentIn (range σ)ᶜ (b (u, s)) ≠ connectedComponentIn (range σ)ᶜ (b (u, t)) := by
  have hσ := hb.injective
  -- Off the zero slice the bicollar misses the image of `σ`, so each half of the collar line
  -- through `u` lies in a single component.
  have hoff {r : ℝ} (hr : r ≠ 0) : b (u, r) ∉ range σ := fun h =>
    hr (hb.preimage_range ▸ h : (u, r) ∈ univ ×ˢ ({0} : Set ℝ)).2
  have hray {I : Set ℝ} (hI : IsPreconnected I) (h0 : (0 : ℝ) ∉ I) {r : ℝ} (hr : r ∈ I) :
      b '' ({u} ×ˢ I) ⊆ connectedComponentIn (range σ)ᶜ (b (u, r)) := by
    refine (isPreconnected_singleton.prod hI).image _ hb.isOpenEmbedding.continuous.continuousOn
      |>.subset_connectedComponentIn ⟨(u, r), ⟨rfl, hr⟩, rfl⟩ ?_
    rintro _ ⟨⟨v, r'⟩, ⟨rfl, hr'⟩, rfl⟩
    exact hoff (ne_of_mem_of_not_mem hr' h0)
  intro hC
  -- The complement of the two points is disconnected, so it has a point `z` outside the
  -- component `C` of the collar arcs.
  obtain ⟨z, hz, hzC⟩ :
      ∃ z ∈ (range σ)ᶜ, z ∉ connectedComponentIn (range σ)ᶜ (b (u, s)) := by
    by_contra! hsub
    have hJ : IsJordanCurve (univ : Set (sphere (0 : F) 1)) :=
      isJordanCurve_iff.mpr
        ⟨(Homeomorph.Set.univ _).trans (sphereHomeomorphCircleOfFinrankEqTwo hF)⟩
    have hpre : IsPreconnected (range σ)ᶜ := by
      rw [← (connectedComponentIn_subset _ _).antisymm hsub]
      exact isPreconnected_connectedComponentIn
    rw [range_eq_pair_of_finrank_eq_one hE σ u, compl_eq_univ_sdiff] at hpre
    exact hJ.not_isPreconnected_sdiff_pair (mem_univ _) (mem_univ _)
      (hσ.ne (ne_neg_of_mem_unit_sphere ℝ u)) hpre
  -- `σ u` is in the frontier of the component `D` of `z`, so the open set swept out by the collar
  -- line through `u` meets `D`, off the zero slice.
  have hD : σ u ∈ closure (connectedComponentIn (range σ)ᶜ z) :=
    frontier_subset_closure <| by
      rw [frontier_connectedComponentIn_compl_range_sphere_of_finrank_eq_one hE hF hσ hz]
      exact mem_range_self u
  have := discreteTopology_sphere_of_finrank_eq_one hE (0 : E) 1
  obtain ⟨_, ⟨⟨v, r⟩, ⟨hv, -⟩, rfl⟩, hw⟩ := mem_closure_iff.mp hD _
    (hb.isOpenEmbedding.isOpenMap _ ((isOpen_discrete {u}).prod isOpen_univ))
    ⟨(u, 0), ⟨rfl, mem_univ _⟩, hb.apply_zero u⟩
  obtain rfl : v = u := hv
  have hr : r ≠ 0 := by
    rintro rfl
    exact connectedComponentIn_subset _ _ hw ⟨v, (hb.apply_zero v).symm⟩
  -- On either side of the zero slice the collar line lies in `C`, which is disjoint from `D`.
  have hwC : b (v, r) ∈ connectedComponentIn (range σ)ᶜ (b (v, s)) := by
    rcases hr.lt_or_gt with hr | hr
    · exact hC ▸ hray (I := Iio 0) isPreconnected_Iio (by simp) ht ⟨(v, r), ⟨rfl, hr⟩, rfl⟩
    · exact hray (I := Ioi 0) isPreconnected_Ioi (by simp) hs ⟨(v, r), ⟨rfl, hr⟩, rfl⟩
  apply hzC
  rw [connectedComponentIn_eq hwC, ← connectedComponentIn_eq hw]
  exact mem_connectedComponentIn hz

end TauCeti
