/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Convex.StdSimplex
public import TauCeti.AlgebraicTopology.SimplicialComplex.Subdivision.Edgewise.Realization
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Topology.Algebra.Module.FiniteDimension
import TauCeti.AlgebraicTopology.SimplicialComplex.Simplex.Realization

/-!
# Simplexwise smoothness on edgewise subdivisions

A map of the realization of a complex `K` is `Cⁿ` on a closed simplex when, in barycentric
coordinates, it is the restriction of a map which is `Cⁿ` within the standard simplex. On a
simplex of the `k`-th edgewise subdivision, the canonical map onto `|K|` is linear in barycentric
coordinates and lands in a single face of `K`. Hence a map which is `Cⁿ` on every closed simplex
of `K` stays `Cⁿ` on every closed simplex of the subdivision, read through the canonical map.

## Main results

* `AbstractSimplicialComplex.exists_contDiffOn_edgewiseSubdivisionRealizationMap_faceInclusion`:
  a map which is `Cⁿ` on every closed simplex of `K` stays `Cⁿ` on every closed simplex of the
  edgewise subdivisions, read through the canonical map onto `|K|`.

## References

* J. Munkres, *Elementary Differential Topology*, Annals of Math. Studies 54 (1966), Chapter II,
  Section 9.
-/

public section

open Finset PreAbstractSimplicialComplex TauCeti.SetLike

namespace AbstractSimplicialComplex

open TauCeti

variable {ι : Type*} [LinearOrder ι] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {K : AbstractSimplicialComplex ι} {k : ℕ}

/-- A map of `|K|` which is `Cⁿ` on every closed simplex of `K`, read on the `k`-th edgewise
subdivision through the canonical map onto `|K|`, is `Cⁿ` on every closed simplex of the
subdivision. Being `Cⁿ` on a closed simplex means being, in barycentric coordinates, the
restriction of a map which is `Cⁿ` within the standard simplex. -/
theorem exists_contDiffOn_edgewiseSubdivisionRealizationMap_faceInclusion {n : WithTop ℕ∞}
    {f : Realization K → E}
    (hf : ∀ σ : Face K, ∃ F : (σ.1 → ℝ) → E,
      (∀ x : StandardSimplex σ.1, F (fun a => x.1 a) = f (faceInclusion K σ x)) ∧
        ContDiffOn ℝ n F (Set.range fun t : Convexity.StdSimplex ℝ σ.1 => ⇑t.weights))
    (ρ : Face (K.edgewiseSubdivision k)) :
    ∃ G : (ρ.1 → ℝ) → E,
      (∀ x : StandardSimplex ρ.1,
        G (fun a => x.1 a) = f (edgewiseSubdivisionRealizationMap K k (faceInclusion _ ρ x))) ∧
        ContDiffOn ℝ n G (Set.range fun t : Convexity.StdSimplex ℝ ρ.1 => ⇑t.weights) := by
  -- The simplex `ρ` lies in the face `σ` of `K` spanned by the entries of its vertices.
  let σ : Face K := ⟨_, biUnion_image_mem_of_mem_edgewiseSubdivision ρ.2⟩
  have hρσ : ∀ u ∈ ρ.1, ∀ l, u.1 l ∈ σ.1 := fun u hu l =>
    mem_biUnion.mpr ⟨u, hu, mem_image_of_mem _ (mem_univ l)⟩
  obtain ⟨F, hFf, hF⟩ := hf σ
  -- In barycentric coordinates, the canonical map sends the vertex `u` of `ρ` to
  -- `edgewisePoint u` and is linear.
  let A : (ρ.1 → ℝ) →L[ℝ] (σ.1 → ℝ) :=
    (Fintype.linearCombination ℝ fun (a : ρ.1) (b : σ.1) =>
      edgewisePoint a.1.1 b).toContinuousLinearMap
  have hA (x : StandardSimplex ρ.1) :
      A (fun a => x.1 a) = fun b : σ.1 => (edgewiseSubdivisionFaceMap hρσ x).1 b := by
    funext b
    simp only [A, LinearMap.coe_toContinuousLinearMap', Fintype.linearCombination_apply,
      Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [edgewiseSubdivisionFaceMap_apply]
    exact Finset.sum_coe_sort ρ.1 fun u => x.1 u * edgewisePoint u.1 b
  refine ⟨F ∘ A, fun x => ?_, hF.comp A.contDiff.contDiffOn fun w hw => ?_⟩
  · rw [Function.comp_apply, hA, hFf]
    exact congrArg f
      (congrFun (edgewiseSubdivisionRealizationMap_comp_faceInclusion ρ σ hρσ) x).symm
  · rw [← Finset.range_standardSimplex_coordinates] at hw ⊢
    obtain ⟨x, rfl⟩ := hw
    exact ⟨_, (hA x).symm⟩

end AbstractSimplicialComplex
