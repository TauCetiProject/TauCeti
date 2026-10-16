/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.Star.Basic
import Mathlib.Topology.Algebra.Ring.Real

/-!
# Extending link maps across a vertex star

A map between geometric vertex links extends radially to their closed stars, taking the
apex to the apex and preserving its barycentric coordinate. When the realizations have
their coordinate topologies, continuous link maps have continuous extensions, including
at the apex. Consequently a homeomorphism of links extends to a homeomorphism of closed
stars. This supplies the conical extension of local models used in triangulated manifolds.

No compactness or nonempty-link assumption is needed: the coordinates of every link point
lie in `[0, 1]`, so all non-apex coordinates tend uniformly to zero at the apex. An isolated
vertex has empty link and a singleton closed star, and is covered by the same construction.
The result concerns topological homeomorphisms; it does not assert PL regularity.

## References

* C. P. Rourke, B. J. Sanderson, *Introduction to Piecewise-Linear Topology*, Springer (1972),
  Chapter 2, “Pseudo-Radial Projection”, pp. 20–21 (conical extension of link models).
-/

public section

noncomputable section

open Set Filter TauCeti.SetLike
open scoped Topology

namespace AbstractSimplicialComplex

variable {ι κ ν : Type*} [DecidableEq ι] [DecidableEq κ] [DecidableEq ν]
  {K : AbstractSimplicialComplex ι} {L : AbstractSimplicialComplex κ}
  {N : AbstractSimplicialComplex ν} {v : ι} {w : κ} {u : ν}

/-- Radially extend a link map, preserving the apex coordinate and sending apex to apex. -/
def closedStarMap (f : geometricLink K v → geometricLink L w)
    (x : closedStarRealization K {v}) : closedStarRealization L {w} :=
  if h : x.1.1 v < 1 then
    let y := starRay L w (f (starLinkProjection K v
      ⟨x.1, (mem_puncturedClosedStar K v _).mpr ⟨x.2, h⟩⟩))
      ⟨x.1.1 v, Realization.nonneg K x.1 v, h⟩
    ⟨y.1, ((mem_puncturedClosedStar L w _).mp y.2).1⟩
  else starApex L w

/-- A radial extension takes the apex to the apex. -/
@[simp]
theorem closedStarMap_starApex (f : geometricLink K v → geometricLink L w) :
    closedStarMap f (starApex K v) = starApex L w := by
  simp [closedStarMap]

/-- On a punctured star, the extension applies the link map and preserves the ray parameter. -/
theorem closedStarMap_of_lt (f : geometricLink K v → geometricLink L w)
    (x : closedStarRealization K {v}) (hx : x.1.1 v < 1) :
    closedStarMap f x =
      ⟨(starRay L w (f (starLinkProjection K v
        ⟨x.1, (mem_puncturedClosedStar K v _).mpr ⟨x.2, hx⟩⟩))
        ⟨x.1.1 v, Realization.nonneg K x.1 v, hx⟩).1,
       ((mem_puncturedClosedStar L w _).mp
        (starRay L w (f (starLinkProjection K v ⟨x.1,
          (mem_puncturedClosedStar K v _).mpr ⟨x.2, hx⟩⟩))
          ⟨x.1.1 v, Realization.nonneg K x.1 v, hx⟩).2).1⟩ := by
  simp [closedStarMap, hx]

/-- Away from the apex, radial extension preserves its coordinate and scales the link image
coordinates by the mass outside the apex. -/
@[simp]
theorem closedStarMap_apply_of_lt (f : geometricLink K v → geometricLink L w)
    (x : closedStarRealization K {v}) (hx : x.1.1 v < 1) (j : κ) :
    (closedStarMap f x).1.1 j = if j = w then x.1.1 v else
      (1 - x.1.1 v) * (f (starLinkProjection K v
        ⟨x.1, (mem_puncturedClosedStar K v _).mpr ⟨x.2, hx⟩⟩)).1.1 j := by
  rw [closedStarMap_of_lt f x hx]
  by_cases hj : j = w
  · simp [hj]
  · simp [hj, Ne.symm hj]

/-- On a link point, radial extension agrees with the original link map. -/
@[simp]
theorem closedStarMap_link (f : geometricLink K v → geometricLink L w)
    (y : geometricLink K v) :
    (closedStarMap f ⟨y.1, ((mem_geometricLink K v _).mp y.2).2⟩).1 = (f y).1 := by
  have hy : y.1.1 v < 1 := by simp
  rw [closedStarMap_of_lt f _ hy]
  have hp : starLinkProjection K v
      ⟨y.1, (mem_puncturedClosedStar K v _).mpr
        ⟨((mem_geometricLink K v _).mp y.2).2, hy⟩⟩ = y := by
    apply Subtype.ext
    apply Subtype.ext
    ext j
    by_cases hj : j = v <;> simp [starLinkProjection_apply, hj]
  rw [hp]
  apply Subtype.ext
  ext j
  simp

/-- The apex coordinate is unchanged by radial extension. -/
@[simp]
theorem closedStarMap_apex_coordinate (f : geometricLink K v → geometricLink L w)
    (x : closedStarRealization K {v}) : (closedStarMap f x).1.1 w = x.1.1 v := by
  by_cases hx : x.1.1 v < 1
  · rw [closedStarMap_of_lt f x hx]
    simp
  · have heq : x.1.1 v = 1 := le_antisymm (Realization.le_one K x.1 v) (not_lt.mp hx)
    simp [closedStarMap, heq]

/-- Every other coordinate of the extension is bounded by the mass outside the apex. -/
theorem closedStarMap_coordinate_le (f : geometricLink K v → geometricLink L w)
    (x : closedStarRealization K {v}) {j : κ} (hj : j ≠ w) :
    (closedStarMap f x).1.1 j ≤ 1 - x.1.1 v := by
  by_cases hx : x.1.1 v < 1
  · rw [closedStarMap_of_lt f x hx]
    simp only [starRay_apply, Ne.symm hj, ↓reduceIte, add_zero]
    exact mul_le_of_le_one_right (sub_pos.mpr hx).le (Realization.le_one L _ j)
  · have heq : x.1.1 v = 1 := le_antisymm (Realization.le_one K x.1 v) (not_lt.mp hx)
    simp [closedStarMap, heq, Ne.symm hj]

/-- Radial extension of the identity fixes every point of the closed star. -/
@[simp]
theorem closedStarMap_id (x : closedStarRealization K {v}) : closedStarMap id x = x := by
  by_cases hx : x.1.1 v < 1
  · rw [closedStarMap_of_lt id x hx]
    have h := congrArg (fun z : puncturedClosedStar K v => z.1)
      (starRay_starLinkProjection K v
        ⟨x.1, (mem_puncturedClosedStar K v _).mpr ⟨x.2, hx⟩⟩)
    exact Subtype.ext h
  · have heq : x.1 = vertex K v := (Realization.eq_vertex_iff K x.1 v).mpr
      (le_antisymm (Realization.le_one K x.1 v) (not_lt.mp hx))
    apply Subtype.ext
    simpa [closedStarMap, hx] using heq.symm

/-- Radial extension respects composition of link maps. -/
@[simp]
theorem closedStarMap_comp (g : geometricLink L w → geometricLink N u)
    (f : geometricLink K v → geometricLink L w) (x : closedStarRealization K {v}) :
    closedStarMap g (closedStarMap f x) = closedStarMap (g ∘ f) x := by
  by_cases hx : x.1.1 v < 1
  · rw [closedStarMap_of_lt f x hx,
      closedStarMap_of_lt g _ (by simpa using hx), closedStarMap_of_lt (g ∘ f) x hx]
    simp
  · simp [closedStarMap, hx]

/-- Continuous link maps extend continuously across the apex, when both realizations have
their coordinate topologies. -/
theorem continuous_closedStarMap
    (hK : Topology.IsInducing (fun x : Realization K => (x.1 : ι → ℝ)))
    (hL : Topology.IsInducing (fun x : Realization L => (x.1 : κ → ℝ)))
    {f : geometricLink K v → geometricLink L w} (hf : Continuous f) :
    Continuous (closedStarMap f) := by
  have hc : Continuous (fun x : closedStarRealization K {v} => x.1.1 v) :=
    (continuous_apply v).comp ((continuous_realization_coe K).comp continuous_subtype_val)
  let S : Set (closedStarRealization K {v}) := {x | x.1.1 v < 1}
  have hS : IsOpen S := isOpen_lt hc continuous_const
  -- Off the apex, use the existing product coordinates on the punctured star.
  have haway : ContinuousOn (closedStarMap f) S := by
    rw [continuousOn_iff_continuous_domRestrict]
    let p : S → puncturedClosedStar K v := fun x =>
      ⟨x.1.1, (mem_puncturedClosedStar K v _).mpr ⟨x.1.2, x.2⟩⟩
    have hp : Continuous p :=
      (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
    have ht : Continuous (fun x : S =>
        (⟨x.1.1.1 v, Realization.nonneg K x.1.1 v, x.2⟩ : Ico (0 : ℝ) 1)) :=
      (hc.comp continuous_subtype_val).subtype_mk _
    have hr := (continuous_starRay L w hL).comp
      ((hf.comp ((continuous_starLinkProjection K v hK).comp hp)).prodMk ht)
    exact (continuous_subtype_val.comp hr).subtype_mk _ |>.congr fun x => by
      exact (closedStarMap_of_lt f x.1 x.2).symm
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x.1.1 v < 1
  · exact haway.continuousAt (hS.mem_nhds hx)
  · -- At the apex, squeeze every other coordinate between zero and the remaining mass.
    have heq : x.1.1 v = 1 := le_antisymm (Realization.le_one K x.1 v) (not_lt.mp hx)
    apply Topology.IsInducing.subtypeVal.continuousAt_iff.mpr
    apply hL.continuousAt_iff.mpr
    apply continuousAt_pi.mpr
    intro j
    by_cases hj : j = w
    · subst j
      simpa only [Function.comp_apply, closedStarMap_apex_coordinate] using hc.continuousAt
    · have hzero : (closedStarMap f x).1.1 j = 0 := by
        simp [closedStarMap, hx, Ne.symm hj]
      have hupper : Tendsto (fun y : closedStarRealization K {v} => 1 - y.1.1 v)
          (𝓝 x) (𝓝 0) := by
        have hd : Continuous (fun y : closedStarRealization K {v} => 1 - y.1.1 v) :=
          continuous_const.sub hc
        simpa only [ContinuousAt, heq, sub_self] using hd.continuousAt (x := x)
      have hbound := tendsto_const_nhds.squeeze hupper
        (fun y => Realization.nonneg L (closedStarMap f y).1 j)
        (fun y => closedStarMap_coordinate_le f y hj)
      simpa only [ContinuousAt, Function.comp_apply, hzero] using hbound

/-- A homeomorphism between vertex links extends radially to a homeomorphism of their
closed stars. This includes empty links and isolated vertices. -/
def closedStarHomeomorph
    (hK : Topology.IsInducing (fun x : Realization K => (x.1 : ι → ℝ)))
    (hL : Topology.IsInducing (fun x : Realization L => (x.1 : κ → ℝ)))
    (e : geometricLink K v ≃ₜ geometricLink L w) :
    closedStarRealization K {v} ≃ₜ closedStarRealization L {w} where
  toFun := closedStarMap e
  invFun := closedStarMap e.symm
  left_inv x := by
    rw [closedStarMap_comp]
    have hid : (e.symm ∘ e : geometricLink K v → geometricLink K v) = id := by
      funext y
      exact e.symm_apply_apply y
    rw [hid, closedStarMap_id]
  right_inv x := by
    rw [closedStarMap_comp]
    have hid : (e ∘ e.symm : geometricLink L w → geometricLink L w) = id := by
      funext y
      exact e.apply_symm_apply y
    rw [hid, closedStarMap_id]
  continuous_toFun := continuous_closedStarMap hK hL e.continuous
  continuous_invFun := continuous_closedStarMap hL hK e.symm.continuous

/-- The radial homeomorphism acts by the closed-star extension of its link homeomorphism. -/
@[simp]
theorem closedStarHomeomorph_apply
    (hK : Topology.IsInducing (fun x : Realization K => (x.1 : ι → ℝ)))
    (hL : Topology.IsInducing (fun x : Realization L => (x.1 : κ → ℝ)))
    (e : geometricLink K v ≃ₜ geometricLink L w) (x : closedStarRealization K {v}) :
    closedStarHomeomorph hK hL e x = closedStarMap e x := (rfl)

/-- The inverse radial homeomorphism extends the inverse link homeomorphism. -/
@[simp]
theorem closedStarHomeomorph_symm_apply
    (hK : Topology.IsInducing (fun x : Realization K => (x.1 : ι → ℝ)))
    (hL : Topology.IsInducing (fun x : Realization L => (x.1 : κ → ℝ)))
    (e : geometricLink K v ≃ₜ geometricLink L w) (x : closedStarRealization L {w}) :
    (closedStarHomeomorph hK hL e).symm x = closedStarMap e.symm x := (rfl)

end AbstractSimplicialComplex
