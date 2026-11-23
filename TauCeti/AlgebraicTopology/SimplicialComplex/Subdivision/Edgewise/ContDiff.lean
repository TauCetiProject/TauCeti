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
    (hf : ∀ σ : Face K, ∃ F : (σ.val → ℝ) → E,
      (∀ x : StandardSimplex σ.val, F (fun a => x.val a) = f (faceInclusion K σ x)) ∧
        ContDiffOn ℝ n F (Set.range fun t : Convexity.StdSimplex ℝ σ.val => ⇑t.weights))
    (ρ : Face (K.edgewiseSubdivision k)) :
    ∃ G : (ρ.val → ℝ) → E,
      (∀ x : StandardSimplex ρ.val,
        G (fun a => x.val a) = f (edgewiseSubdivisionRealizationMap K k (faceInclusion _ ρ x))) ∧
        ContDiffOn ℝ n G (Set.range fun t : Convexity.StdSimplex ℝ ρ.val => ⇑t.weights) := by
  -- The simplex `ρ` lies in the face `σ` of `K` spanned by the entries of its vertices.
  let σ : Face K := ⟨_, biUnion_image_mem_of_mem_edgewiseSubdivision ρ.property⟩
  have hρσ : ∀ u ∈ ρ.val, ∀ l, u.val l ∈ σ.val := fun u hu l =>
    mem_biUnion.mpr ⟨u, hu, mem_image_of_mem _ (mem_univ l)⟩
  obtain ⟨F, hFf, hF⟩ := hf σ
  -- In barycentric coordinates, the canonical map sends the vertex `u` of `ρ` to
  -- `edgewisePoint u` and is linear.
  let A : (ρ.val → ℝ) →L[ℝ] (σ.val → ℝ) :=
    (Fintype.linearCombination ℝ fun (a : ρ.val) (b : σ.val) =>
      edgewisePoint a.val.val b).toContinuousLinearMap
  have hA (x : StandardSimplex ρ.val) :
      A (fun a => x.val a) = fun b : σ.val => (edgewiseSubdivisionFaceMap hρσ x).val b := by
    funext b
    simp only [A, LinearMap.coe_toContinuousLinearMap', Fintype.linearCombination_apply,
      Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [edgewiseSubdivisionFaceMap_apply]
    exact Finset.sum_coe_sort ρ.val fun u => x.val u * edgewisePoint u.val b
  refine ⟨F ∘ A, fun x => ?_, hF.comp A.contDiff.contDiffOn fun w hw => ?_⟩
  · rw [Function.comp_apply, hA, hFf]
    exact congrArg f
      (congrFun (edgewiseSubdivisionRealizationMap_comp_faceInclusion ρ σ hρσ) x).symm
  · rw [← Finset.range_standardSimplex_coordinates] at hw ⊢
    obtain ⟨x, rfl⟩ := hw
    exact ⟨_, (hA x).symm⟩

end AbstractSimplicialComplex
