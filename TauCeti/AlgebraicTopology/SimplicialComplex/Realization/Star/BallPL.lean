/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.Star.Ball
public import TauCeti.Topology.PL.Cone

/-!
# Piecewise-linear ball models for vertex stars

The radial homeomorphism from a closed vertex star to a Euclidean ball is piecewise linear when
the link-to-sphere map is piecewise linear in barycentric coordinates.  This is the local model
needed at an interior vertex in the reconciliation between combinatorial and chart-based PL
manifolds.  The theorem is stated with the compactness of the coordinate link made explicit: a
combinatorial link supplies it through its finite realization, while the radial PL extension itself
does not require a finite ambient vertex type.

The proof reads the star as a cone, applies `IsPLOn.coneMap`, and projects away the height
coordinate.  Thus the apex is included in the same PL formula as every other point.

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

/-- Delete the apex coordinate and record its complementary mass as the cone height. -/
private def ballStarToCone (v : ι) : (ι → ℝ) →ᴬ[ℝ] ((ι → ℝ) × ℝ) :=
  ((ContinuousLinearMap.id ℝ (ι → ℝ) -
      (ContinuousLinearMap.proj v).smulRight (Pi.single v 1)).toContinuousAffineMap).prod
    (ContinuousAffineMap.const ℝ (ι → ℝ) 1 -
      (ContinuousLinearMap.proj v).toContinuousAffineMap)

private theorem ballStarToCone_apply (v : ι) (x : ι → ℝ) :
    ballStarToCone v x = (x - x v • Pi.single v 1, 1 - x v) := (rfl)

private theorem ballStarToCone_of_lt (x : closedStarRealization K {v}) (hx : x.1.1 v < 1) :
    ballStarToCone v (x.1.1 : ι → ℝ) =
      ((1 - x.1.1 v) •
        ((starLinkProjection K v
          ⟨x.1, (mem_puncturedClosedStar K v _).mpr ⟨x.2, hx⟩⟩).1.1 : ι → ℝ),
        1 - x.1.1 v) := by
  rw [ballStarToCone_apply]
  congr 1
  ext j
  by_cases hj : j = v
  · simp [hj]
  · simp [starLinkProjection_apply, hj,
      ← mul_assoc, mul_inv_cancel₀ (sub_pos.mpr hx).ne']

private theorem ballStarToCone_of_not_lt (x : closedStarRealization K {v})
    (hx : ¬x.1.1 v < 1) : ballStarToCone v (x.1.1 : ι → ℝ) = 0 := by
  have hv : x.1.1 v = 1 := le_antisymm (Realization.le_one K x.1 v) (not_lt.mp hx)
  have he : x.1 = vertex K v := (Realization.eq_vertex_iff K x.1 v).mpr hv
  rw [ballStarToCone_apply, he]
  ext j <;> simp [vertex_val, Finsupp.single_apply, Pi.single_apply, eq_comm]

private theorem ballStarToCone_mem (x : closedStarRealization K {v}) :
    ballStarToCone v (x.1.1 : ι → ℝ) ∈
      (range (fun y : geometricLink K v => (y.1.1 : ι → ℝ))).cone := by
  by_cases hx : x.1.1 v < 1
  · rw [ballStarToCone_of_lt x hx]
    exact (smul_mem_cone_iff _ (sub_pos.mpr hx)).mpr (mem_range_self _)
  · rw [ballStarToCone_of_not_lt x hx]
    exact zero_mem_cone _

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
  have hmap : MapsTo (ballStarToCone v) S T.cone := by
    rintro _ ⟨x, rfl⟩
    exact ballStarToCone_mem x
  have hcone : IsPiecewiseAffineOn (coneMap F) T.cone := hf.coneMap
  have hcom : IsPiecewiseAffineOn (coneMap F ∘ ballStarToCone v) S :=
    hcone.comp (isPiecewiseAffineOn_continuousAffineMap (ballStarToCone v) S) hmap
  let π : (E × ℝ) →ᴬ[ℝ] E :=
    (ContinuousLinearMap.fst ℝ E ℝ).toContinuousAffineMap
  have hproj' : IsPiecewiseAffineOn (π ∘ (coneMap F ∘ ballStarToCone v)) S :=
    (isPiecewiseAffineOn_continuousAffineMap π univ).comp hcom (subset_univ _)
  refine ⟨π ∘ (coneMap F ∘ ballStarToCone v), hproj', ?_⟩
  intro x
  by_cases hx : x.1.1 v < 1
  · rw [closedStarHomeomorphClosedBall_apply_of_lt hK e x hx]
    rw [Function.comp_apply, Function.comp_apply, ballStarToCone_of_lt x hx,
      coneMap_smul F _ (sub_pos.mpr hx).ne']
    simp [π, hF]
  · have hv : x.1.1 v = 1 := le_antisymm (Realization.le_one K x.1 v) (not_lt.mp hx)
    have he : x = starApex K v := by
      apply Subtype.ext
      simpa only [starApex_val] using (Realization.eq_vertex_iff K x.1 v).mpr hv
    rw [he]
    change π (coneMap F (ballStarToCone v ((starApex K v).1.1 : ι → ℝ))) = _
    rw [ballStarToCone_of_not_lt (starApex K v) (by simp), coneMap_zero]
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

/-- Compact finite-dimensional link coordinates turn local PL link data into the ball formula. -/
theorem exists_isPLOn_closedStarHomeomorphClosedBall_of_isPLOn [Finite ι]
    (hK : IsCompact (closedStarRealization K {v}))
    (hlink : IsCompact (range (fun y : geometricLink K v => (y.1.1 : ι → ℝ))))
    (e : geometricLink K v ≃ₜ Metric.sphere (0 : E) 1)
    (F : (ι → ℝ) → E)
    (hF : ∀ y : geometricLink K v, F (y.1.1 : ι → ℝ) = e y)
    (hf : IsPLOn F (range (fun y : geometricLink K v => (y.1.1 : ι → ℝ)))) :
    ∃ G : (ι → ℝ) → E,
      IsPLOn G (range (fun x : closedStarRealization K {v} => (x.1.1 : ι → ℝ))) ∧
      ∀ x : closedStarRealization K {v},
        G (x.1.1 : ι → ℝ) = (closedStarHomeomorphClosedBall hK e x : E) := by
  exact exists_isPLOn_closedStarHomeomorphClosedBall hK e F hF
    (hf.isPiecewiseAffineOn_of_isCompact hlink)

end AbstractSimplicialComplex
