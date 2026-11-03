/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.Subdivision.Edgewise.Homeomorph
public import TauCeti.AlgebraicTopology.SimplicialComplex.Simplex.Realization
public import TauCeti.Analysis.Convex.Lipschitz
import TauCeti.Analysis.Convex.StdSimplex

/-!
# Lipschitz bounds across an edgewise subdivision

The geometric simplices of a nonzero edgewise subdivision cover the original polyhedron.
Here the geometric simplices are the convex hulls of the coordinate vectors `edgewisePoint`,
not the coordinate simplices in the subdivided vertex space. On a finite vertex set these
hulls are compact, hence closed. Consequently a common Lipschitz bound on the subdivided
simplices of a standard simplex holds on the whole original simplex, without increasing
the constant.

This is the geometric gluing step in secant approximation: estimates for a secant error on
individual subdivided faces can be combined even though that error need not be differentiable
across their boundaries. The bound uses distances in the original coordinates throughout.

## References

* J. Munkres, *Elementary Differential Topology*, Chapter II, Section 9.
* H. Freudenthal, *Simplizialzerlegungen von beschränkter Flachheit*, Ann. of Math. 43
  (1942), 580–582.
-/

public section

open Set AbstractSimplicialComplex PreAbstractSimplicialComplex TauCeti TauCeti.SetLike
open scoped NNReal

namespace AbstractSimplicialComplex

variable {ι : Type*} [LinearOrder ι] {K : AbstractSimplicialComplex ι} {k : ℕ}

/-- In the original coordinates, the image of a closed subdivided simplex is the convex hull
of the points assigned to its vertices. This statement does not require finitely many original
vertices. -/
theorem range_edgewiseSubdivisionRealizationMap_faceInclusion
    (ρ : Face (K.edgewiseSubdivision k)) :
    range (fun x : StandardSimplex ρ.1 =>
      ((edgewiseSubdivisionRealizationMap K k (faceInclusion _ ρ x)).1 : ι → ℝ)) =
      convexHull ℝ (range fun a : ρ.1 => (edgewisePoint a.1.1 : ι → ℝ)) := by
  classical
  let L : (K.EdgewiseVertex k →₀ ℝ) →ₗ[ℝ] (ι → ℝ) :=
    (Finsupp.lcoeFun : (ι →₀ ℝ) →ₗ[ℝ] (ι → ℝ)).comp
      (Finsupp.linearCombination ℝ fun a : K.EdgewiseVertex k => edgewisePoint a.1)
  have hformula : (fun x : StandardSimplex ρ.1 =>
      ((edgewiseSubdivisionRealizationMap K k (faceInclusion _ ρ x)).1 : ι → ℝ)) =
      L ∘ Subtype.val := by
    funext x
    simp [L]
  simp only [hformula, range_comp, Subtype.range_coe]
  rw [L.image_convexHull]
  congr 1
  have hsingle (a : K.EdgewiseVertex k) :
      L (Finsupp.single a 1) = (edgewisePoint a.1 : ι → ℝ) := by simp [L]
  simp only [Finset.coe_image, image_image]
  simp only [hsingle, image_eq_range]
  rfl

/-- The geometric simplices of a nonzero edgewise subdivision cover precisely the original
polyhedron, expressed in its original coordinate space. -/
theorem iUnion_convexHull_range_edgewisePoint (K : AbstractSimplicialComplex ι) (hk : k ≠ 0) :
    (⋃ ρ : Face (K.edgewiseSubdivision k),
      convexHull ℝ (range fun a : ρ.1 => (edgewisePoint a.1.1 : ι → ℝ))) =
      range (fun x : Realization K => (x.1 : ι → ℝ)) := by
  simp_rw [← range_edgewiseSubdivisionRealizationMap_faceInclusion]
  ext z
  constructor
  · intro hz
    obtain ⟨ρ, x, rfl⟩ := mem_iUnion.mp hz
    exact ⟨edgewiseSubdivisionRealizationMap K k (faceInclusion _ ρ x), rfl⟩
  · rintro ⟨x, rfl⟩
    obtain ⟨y, rfl⟩ := edgewiseSubdivisionRealizationMap_surjective (K := K) hk x
    let ρ := carrier _ y
    let t : StandardSimplex ρ.1 := ⟨y.1, mem_convexHull_carrier _ y⟩
    have ht : faceInclusion _ ρ t = y := Subtype.ext (faceInclusion_val _ _ _)
    exact mem_iUnion.mpr ⟨ρ, t, by simp only [ht]⟩

end AbstractSimplicialComplex

namespace TauCeti

/-- A common Lipschitz bound on the geometric faces of a nonzero edgewise subdivision of the
standard simplex holds on the whole simplex, with no loss in the constant. Distances are
measured in the original coordinate space, not in the subdivided barycentric coordinates.
The codomain can be any pseudometric space. -/
theorem lipschitzOnWith_stdSimplex_of_edgewiseSubdivision
    {ι Y : Type*} [LinearOrder ι] [Fintype ι] [PseudoMetricSpace Y]
    {k : ℕ} (hk : k ≠ 0) {f : (ι → ℝ) → Y} {C : ℝ≥0}
    (hf : ∀ ρ : Face ((⊤ : AbstractSimplicialComplex ι).edgewiseSubdivision k),
      LipschitzOnWith C f
        (convexHull ℝ (range fun a : ρ.1 => (edgewisePoint a.1.1 : ι → ℝ)))) :
    LipschitzOnWith C f (range fun t : Convexity.StdSimplex ℝ ι => ⇑t.weights) := by
  classical
  let K : AbstractSimplicialComplex ι := ⊤
  have : Finite (K.EdgewiseVertex k) := Finite.of_injective Subtype.val Subtype.val_injective
  have : Finite (Face (K.edgewiseSubdivision k)) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  refine Convex.lipschitzOnWith_of_finite_closed_cover
    (Convexity.StdSimplex.convex_range_toFun_comp_weights ℝ ι)
    (fun ρ : Face (K.edgewiseSubdivision k) =>
      convexHull ℝ (range fun a : ρ.1 => (edgewisePoint a.1.1 : ι → ℝ)))
    (fun ρ => (finite_range _).isCompact_convexHull ℝ |>.isClosed) ?_
    (fun ρ => (hf ρ).mono inter_subset_right)
  rw [iUnion_convexHull_range_edgewisePoint K hk, range_realization_coe_top]

end TauCeti
