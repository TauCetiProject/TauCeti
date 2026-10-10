/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.Star.Ball.Basic
public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.Star.Cone
public import TauCeti.Topology.PL.Cone

/-!
# Piecewise-linear ball models for vertex stars

The radial homeomorphism from a closed vertex star to a Euclidean ball is piecewise linear when
the link-to-sphere map is piecewise linear in barycentric coordinates.  This is the local model
needed at an interior vertex in the reconciliation between combinatorial and chart-based PL
manifolds.  The theorem is stated with the compactness of the coordinate link made explicit: a
combinatorial link supplies it through its finite realization, while the radial PL extension itself
does not require a finite ambient vertex type.

The conical extension includes the apex and agrees with the radial formula away from it, so the
resulting ambient coordinate formula represents the closed-star ball homeomorphism on every point.

## References

* C. P. Rourke and B. J. Sanderson, *Introduction to Piecewise-Linear Topology*, Springer
  (1972), Chapter 2, “Pseudo-Radial Projection”, pp. 20–21.
* `TauCeti.AlgebraicTopology.SimplicialComplex.Realization.Star.PL`: PL radial maps into a
  geometric star.
-/

public section

noncomputable section

open Set TauCeti

namespace AbstractSimplicialComplex

variable {ι E : Type*} [DecidableEq ι]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {K : AbstractSimplicialComplex ι} {v : ι}

/-- A PL link-to-sphere formula extends to a PL formula for the closed-star ball model.

The input is a finite piecewise-affine decomposition on the link coordinate image.  This keeps the
result independent of the ambient vertex type; local PL data can be made finite on compact links
before applying the theorem. -/
theorem exists_isPiecewiseAffineOn_closedStarHomeomorphClosedBall
    (hK : IsCompact (closedStarRealization K {v}))
    (e : geometricLink K v ≃ₜ Metric.sphere (0 : E) 1)
    (F : (ι → ℝ) → E)
    (hF : ∀ y : geometricLink K v, F (y.1.1 : ι → ℝ) = e y)
  (hf : IsPiecewiseAffineOn F (range (fun y : geometricLink K v => (y.1.1 : ι → ℝ)))) :
    ∃ G : (ι → ℝ) → E,
      IsPiecewiseAffineOn G (range (fun x : closedStarRealization K {v} => (x.1.1 : ι → ℝ))) ∧
      ∀ x : closedStarRealization K {v},
        G (x.1.1 : ι → ℝ) = (closedStarHomeomorphClosedBall hK e x : E) := by
  let S := range (fun x : closedStarRealization K {v} => (x.1.1 : ι → ℝ))
  let T := range (fun y : geometricLink K v => (y.1.1 : ι → ℝ))
  have hmap : MapsTo (starToCone v) S T.cone := by
    rintro _ ⟨x, rfl⟩
    exact starToCone_mem x
  have hcone : IsPiecewiseAffineOn (coneMap F) T.cone := hf.coneMap
  have hcom : IsPiecewiseAffineOn (coneMap F ∘ starToCone v) S :=
    hcone.comp (isPiecewiseAffineOn_continuousAffineMap (starToCone v) S) hmap
  let π : (E × ℝ) →ᴬ[ℝ] E :=
    (ContinuousLinearMap.fst ℝ E ℝ).toContinuousAffineMap
  have hproj' : IsPiecewiseAffineOn (π ∘ (coneMap F ∘ starToCone v)) S :=
    (isPiecewiseAffineOn_continuousAffineMap π univ).comp hcom (subset_univ _)
  refine ⟨π ∘ (coneMap F ∘ starToCone v), hproj', ?_⟩
  intro x
  by_cases hx : x.1.1 v < 1
  · rw [closedStarHomeomorphClosedBall_apply_of_lt hK e x hx]
    rw [Function.comp_apply, Function.comp_apply, starToCone_of_lt x hx,
      coneMap_smul F _ (sub_pos.mpr hx).ne']
    simp [π, hF]
  · have hv : x.1.1 v = 1 := le_antisymm (Realization.le_one K x.1 v) (not_lt.mp hx)
    have he : x = starApex K v := by
      apply Subtype.ext
      simpa only [starApex_val] using (Realization.eq_vertex_iff K x.1 v).mpr hv
    rw [he]
    rw [Function.comp_apply, Function.comp_apply,
      starToCone_of_not_lt (starApex K v) (by simp), coneMap_zero,
      closedStarHomeomorphClosedBall_starApex hK e]
    simp [π]

/-- The piecewise-affine ball formula is piecewise linear on the closed-star coordinates. -/
theorem exists_isPLOn_closedStarHomeomorphClosedBall
    (hK : IsCompact (closedStarRealization K {v}))
    (e : geometricLink K v ≃ₜ Metric.sphere (0 : E) 1)
    (F : (ι → ℝ) → E)
    (hF : ∀ y : geometricLink K v, F (y.1.1 : ι → ℝ) = e y)
    (hf : IsPiecewiseAffineOn F (range (fun y : geometricLink K v => (y.1.1 : ι → ℝ)))) :
    ∃ G : (ι → ℝ) → E,
      IsPLOn G (range (fun x : closedStarRealization K {v} => (x.1.1 : ι → ℝ))) ∧
      ∀ x : closedStarRealization K {v},
        G (x.1.1 : ι → ℝ) = (closedStarHomeomorphClosedBall hK e x : E) := by
  obtain ⟨G, hG, hG_eq⟩ := exists_isPiecewiseAffineOn_closedStarHomeomorphClosedBall
    hK e F hF hf
  exact ⟨G, hG.isPLOn, hG_eq⟩

/-- A PL link-to-sphere map extends to a PL formula for the compact closed-star ball model.

For a finite ambient vertex type, the closed-star compactness needed by the construction is
provided internally by `isCompact_closedStarRealization_of_finite`. -/
theorem exists_isPLOn_closedStarHomeomorphClosedBall_of_isPLOn [Finite ι]
    (e : geometricLink K v ≃ₜ Metric.sphere (0 : E) 1)
    (F : (ι → ℝ) → E)
    (hF : ∀ y : geometricLink K v, F (y.1.1 : ι → ℝ) = e y)
    (hf : IsPLOn F (range (fun y : geometricLink K v => (y.1.1 : ι → ℝ)))) :
    ∃ G : (ι → ℝ) → E,
      IsPLOn G (range (fun x : closedStarRealization K {v} => (x.1.1 : ι → ℝ))) ∧
      ∀ x : closedStarRealization K {v},
        G (x.1.1 : ι → ℝ) =
          (closedStarHomeomorphClosedBall
            (K.isCompact_closedStarRealization_of_finite v) e x : E) := by
  let hK : IsCompact (closedStarRealization K {v}) :=
    K.isCompact_closedStarRealization_of_finite v
  have hlink : IsCompact (range (fun y : geometricLink K v => (y.1.1 : ι → ℝ))) := by
    have hcompact := K.isCompact_geometricLink v hK
    let : CompactSpace (geometricLink K v) := isCompact_iff_compactSpace.mp hcompact
    exact isCompact_range ((continuous_realization_coe K).comp continuous_subtype_val)
  simpa only [hK] using exists_isPLOn_closedStarHomeomorphClosedBall hK e F hF
    (hf.isPiecewiseAffineOn_of_isCompact hlink)

end AbstractSimplicialComplex
