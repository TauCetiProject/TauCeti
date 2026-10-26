/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.Subdivision.Homeomorph
public import TauCeti.Geometry.Manifold.SmoothTriangulation.Basic

import TauCeti.AlgebraicTopology.SimplicialComplex.Subdivision.Injective
import TauCeti.Order.Chain

/-!
# Smooth triangulations and barycentric subdivision

A smooth triangulation `f : |K| ≃ₜ M` stays a smooth triangulation after barycentric
subdivision: composing `f` with the canonical homeomorphism `|K'| ≃ₜ |K|` from the realization
of the barycentric subdivision `K'` gives a smooth triangulation of `M` of the same class.

A simplex of `K'` is a chain of faces of `K`, and the canonical homeomorphism maps it into the
greatest face `σ` of the chain, sending each vertex of the chain to the barycenter of its face.
In barycentric coordinates this is a linear map, injective because the barycenters of a chain of
faces are linearly independent. So the restriction of the subdivided triangulation to the
simplex is the restriction of `f` to `σ` precomposed with an injective linear map of simplices,
and is again an immersion of the simplex.

Subdivisions are how smooth triangulations are compared: by Whitehead's theorem any two smooth
triangulations of a manifold have subdivisions which are linearly isomorphic (Munkres, Theorem
10.5), and the triangulations in that statement are subdivisions of the given ones.

## Main results

* `TauCeti.IsSmoothTriangulation.barycentricSubdivisionRealizationHomeomorph_trans`: the
  barycentric subdivision of a smooth triangulation is a smooth triangulation of the same class.

## References

* J. H. C. Whitehead, *On C¹-complexes*, Ann. of Math. 41 (1940), 809–824.
* J. Munkres, *Elementary Differential Topology*, Annals of Math. Studies 54 (1966), Chapter II,
  Definition 8.3 and Theorem 10.5.
-/

public section

noncomputable section

open Set Function AbstractSimplicialComplex TauCeti.SetLike

namespace TauCeti

variable {ι : Type*}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {n : WithTop ℕ∞}

namespace IsSmoothTriangulation

/-- The barycentric subdivision of a `Cⁿ` triangulation of `M` is a `Cⁿ` triangulation of `M`:
composing it with the canonical homeomorphism from the realization of the barycentric
subdivision gives a smooth triangulation. -/
theorem barycentricSubdivisionRealizationHomeomorph_trans {K : AbstractSimplicialComplex ι}
    {f : Realization K ≃ₜ M} (h : IsSmoothTriangulation I n f) :
    IsSmoothTriangulation I n ((barycentricSubdivisionRealizationHomeomorph K).trans f) := by
  refine isSmoothTriangulation_iff.mpr fun ρ => ?_
  have hρ := PreAbstractSimplicialComplex.mem_barycentricSubdivision_iff.mp ρ.2
  obtain ⟨σ, -, hσmax⟩ := hρ.2.exists_isGreatest ρ.1.finite_toSet hρ.1
  -- The canonical homeomorphism maps the simplex `ρ` into the greatest face `σ` of the chain.
  let φ : StandardSimplex ρ.1 → StandardSimplex σ.1 := fun x =>
    ⟨barycentricSubdivisionLinearMap K x.1,
      barycentricSubdivisionLinearMap_mem_closedSimplex K σ x hσmax⟩
  have hfactor : (barycentricSubdivisionRealizationHomeomorph K).trans f ∘ faceInclusion _ ρ =
      (f ∘ faceInclusion K σ) ∘ φ := by
    funext x
    simp only [comp_apply, Homeomorph.trans_apply,
      barycentricSubdivisionRealizationHomeomorph_apply]
    congr 1
    exact Subtype.ext (by simp [φ])
  rw [hfactor]
  -- In barycentric coordinates, `φ` is the linear map sending the vertex `τ` of `ρ` to the
  -- barycenter of `τ`.
  refine (isSmoothTriangulation_iff.mp h σ).comp_linear (Fintype.linearCombination ℝ
    fun (τ : ρ.1) (b : σ.1) => faceBarycenter K τ b) (fun x => funext fun b => ?_)
    (fun v _ hv => ?_)
  · have hsupp : x.1 ∈ Finsupp.supported ℝ ℝ (ρ.1 : Set (Face K)) :=
      (Finsupp.mem_supported ℝ x.1).mpr (StandardSimplex.support_subset x)
    simp only [φ, Fintype.linearCombination_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [barycentricSubdivisionLinearMap_eq_linearCombination,
      Finsupp.linearCombination_apply_of_mem_supported ℝ hsupp, Finset.sum_apply']
    -- The vertices of the subdivision are the faces of `K` read as a precomplex, which is the
    -- same subtype as `Face K`; `exact` identifies the two index sets of the sums.
    exact (Finset.sum_coe_sort _ fun τ => x.1 τ * faceBarycenter K τ b).symm
  · -- A linear relation among the barycenters of the chain `ρ` is trivial.
    funext τ
    refine Fintype.linearIndependent_iff.mp (linearIndepOn_faceBarycenter K hρ.2) v ?_ τ
    ext b
    rw [Finset.sum_apply']
    by_cases hb : b ∈ σ.1
    · have hvb := congrFun hv ⟨b, hb⟩
      simp only [Fintype.linearCombination_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
        Pi.zero_apply] at hvb
      simp only [Finsupp.smul_apply, smul_eq_mul]
      -- As above, the two sums differ only in how the type of faces of `K` is written.
      exact hvb
    · refine Finset.sum_eq_zero fun τ _ => ?_
      have hbτ : b ∉ τ.1.1 := fun hbτ => hb (hσmax τ.2 hbτ)
      simp [hbτ]

end IsSmoothTriangulation

end TauCeti
