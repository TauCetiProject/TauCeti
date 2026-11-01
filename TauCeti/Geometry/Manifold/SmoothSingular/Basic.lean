/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Subcomplex
public import TauCeti.AlgebraicTopology.SimplicialSet.TopAdj
public import TauCeti.Geometry.Convex.FullSimplex
public import TauCeti.Geometry.Manifold.ContMDiff.OnSubset

/-!
# Smooth singular simplices

A singular `k`-simplex `σ` of a manifold `M` is *smooth* when, read on the full-dimensional
standard simplex `Δᵏ = {x ∈ ℝᵏ | 0 ≤ xᵢ, ∑ xᵢ ≤ 1}` through `fullSimplexEquivStdSimplex`, it is
smooth in the sense of maps on arbitrary subsets (`TauCeti.ContMDiffOnSubset`): near every point
of `Δᵏ`, including the points of its faces and corners, it agrees with a smooth map defined on a
neighbourhood in `ℝᵏ`.

Every simplicial operator of the standard simplices is the restriction of a continuous affine map
of the ambient Euclidean spaces (`TauCeti.simplexMapAmbient_coe`), so the
smooth simplices are closed under faces and degeneracies and form a subcomplex
`TauCeti.smoothSingularSubcomplex` of Mathlib's singular simplicial set `TopCat.toSSet.obj M`.
Applying Mathlib's simplicial chain functor gives the complex of smooth singular chains
`(smoothSingularSubcomplex I M : SSet).chainComplex R`, with boundary the alternating sum of the
faces, and `SSet.chainComplexMap (smoothSingularSubcomplex I M).ι R` is its inclusion into singular
chains. A smooth map of manifolds carries smooth simplices to smooth simplices
(`TauCeti.smoothSingularSubcomplexMap`).

These are the chains on which forms are integrated in the comparison of de Rham cohomology with
singular cohomology. Only a charted space is required for the definitions.

## Main definitions and results

* `TauCeti.smoothSingularSubcomplex`: the subcomplex of smooth singular simplices.
* `TauCeti.smoothSingularSubcomplex_le_preimage`: smooth maps preserve smooth simplices.
* `TauCeti.smoothSingularSubcomplexMap`: the induced map of smooth singular subcomplexes.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Chapter 18, *Smooth Singular Homology*.
-/

public section

noncomputable section

open CategoryTheory Convexity Set Topology
open scoped Manifold ContDiff

universe u

namespace TauCeti

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H) (M : Type u) [TopologicalSpace M] [ChartedSpace H M]

/-- The smooth singular simplices of `M`: those singular simplices which, read on the
full-dimensional standard simplex, are smooth in the sense of maps on arbitrary subsets. They form a
subcomplex of the singular simplicial set, since every simplicial operator is the restriction of a
smooth map of the ambient Euclidean spaces. -/
def smoothSingularSubcomplex : (TopCat.toSSet.obj (TopCat.of M)).Subcomplex where
  obj k := {σ | ContMDiffOnSubset I ∞
    ((TopCat.of M).toSSetObjEquiv k σ ∘ fullSimplexEquivStdSimplex k.unop.len)}
  map {k l} f σ hσ := by
    let A := simplexMapAmbient f.unop.toOrderHom
    have hst : MapsTo A (fullSimplex l.unop.len) (fullSimplex k.unop.len) := fun x hx ↦
      simplexMapAmbient_coe _ ⟨x, hx⟩ ▸ Subtype.prop _
    rw [Set.mem_preimage, Set.mem_ofPred_eq]
    convert hσ.comp_contDiff A.contDiff hst using 2
    funext x
    have hx : hst.restrict A _ _ x = (fullSimplexEquivStdSimplex _).symm
        ((fullSimplexEquivStdSimplex _ x).map f.unop.toOrderHom) :=
      Subtype.ext (simplexMapAmbient_coe _ x)
    simp only [Function.comp_apply, hx, Homeomorph.apply_symm_apply]
    exact TopCat.toSSetObjEquiv_naturality_apply f.unop σ _

variable {I M}

/-- A singular simplex is smooth exactly when, read on the full-dimensional standard simplex, it is
smooth in the sense of maps on arbitrary subsets. -/
@[simp]
theorem mem_smoothSingularSubcomplex_iff {k : SimplexCategoryᵒᵖ}
    (σ : (TopCat.toSSet.obj (TopCat.of M)).obj k) :
    σ ∈ (smoothSingularSubcomplex I M).obj k ↔ ContMDiffOnSubset I ∞
      ((TopCat.of M).toSSetObjEquiv k σ ∘ fullSimplexEquivStdSimplex k.unop.len) :=
  Iff.rfl

/-- A singular simplex which, read on the full-dimensional standard simplex, is the restriction of
a map that is smooth on a neighbourhood of the simplex in `ℝᵏ` is smooth. -/
theorem mem_smoothSingularSubcomplex_of_contMDiffOn {k : SimplexCategoryᵒᵖ}
    (σ : (TopCat.toSSet.obj (TopCat.of M)).obj k) {U : Set (EuclideanSpace ℝ (Fin k.unop.len))}
    {g : EuclideanSpace ℝ (Fin k.unop.len) → M}
    (hg : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin k.unop.len)) I ∞ g U)
    (hU : U ∈ 𝓝ˢ (fullSimplex k.unop.len))
    (hσ : ∀ x, (TopCat.of M).toSSetObjEquiv k σ (fullSimplexEquivStdSimplex _ x) = g x) :
    σ ∈ (smoothSingularSubcomplex I M).obj k := by
  rw [mem_smoothSingularSubcomplex_iff]
  convert hg.contMDiffOnSubset hU using 1
  exact funext hσ

variable {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} {N : Type u} [TopologicalSpace N] [ChartedSpace H' N]
  {φ : M → N}

/-- A smooth map carries smooth singular simplices to smooth singular simplices. -/
theorem smoothSingularSubcomplex_le_preimage (hφ : ContMDiff I J ∞ φ) :
    smoothSingularSubcomplex I M ≤ (smoothSingularSubcomplex J N).preimage
      (TopCat.toSSet.map (TopCat.ofHom ⟨φ, hφ.continuous⟩)) := fun k σ hσ ↦ by
  rw [SSet.Subcomplex.preimage_obj, Set.mem_preimage, mem_smoothSingularSubcomplex_iff,
    TopCat.toSSetObjEquiv_toSSet_map_app, ConcreteCategory.hom_ofHom, ContinuousMap.coe_comp,
    ContinuousMap.coe_mk, Function.comp_assoc]
  exact hφ.comp_contMDiffOnSubset hσ

variable (φ) in
/-- The map of smooth singular subcomplexes induced by a smooth map. -/
def smoothSingularSubcomplexMap (hφ : ContMDiff I J ∞ φ) :
    (smoothSingularSubcomplex I M : SSet) ⟶ (smoothSingularSubcomplex J N : SSet) :=
  SSet.Subcomplex.lift
    ((smoothSingularSubcomplex I M).ι ≫ TopCat.toSSet.map (TopCat.ofHom ⟨φ, hφ.continuous⟩)) (by
      rintro k _ ⟨σ, rfl⟩
      exact smoothSingularSubcomplex_le_preimage hφ k σ.2)

/-- The map of smooth singular subcomplexes is the restriction of the map of singular simplicial
sets. -/
@[reassoc (attr := simp)]
theorem smoothSingularSubcomplexMap_ι (hφ : ContMDiff I J ∞ φ) :
    smoothSingularSubcomplexMap φ hφ ≫ (smoothSingularSubcomplex J N).ι =
      (smoothSingularSubcomplex I M).ι ≫ TopCat.toSSet.map (TopCat.ofHom ⟨φ, hφ.continuous⟩) :=
  SSet.Subcomplex.lift_ι _ _

/-- The identity of `M` induces the identity of its smooth singular subcomplex. -/
@[simp]
theorem smoothSingularSubcomplexMap_id :
    smoothSingularSubcomplexMap (I := I) (J := I) (M := M) id contMDiff_id = 𝟙 _ := by
  -- Both sides send a smooth simplex to the same underlying singular simplex.
  ext k σ
  rfl

/-- The map of smooth singular subcomplexes induced by a composite is the composite of the induced
maps. -/
theorem smoothSingularSubcomplexMap_comp {E'' H'' : Type*} [NormedAddCommGroup E'']
    [NormedSpace ℝ E''] [TopologicalSpace H''] {K : ModelWithCorners ℝ E'' H''} {P : Type u}
    [TopologicalSpace P] [ChartedSpace H'' P] {ψ : N → P} (hψ : ContMDiff J K ∞ ψ)
    (hφ : ContMDiff I J ∞ φ) :
    smoothSingularSubcomplexMap (ψ ∘ φ) (hψ.comp hφ) =
      smoothSingularSubcomplexMap φ hφ ≫ smoothSingularSubcomplexMap ψ hψ := by
  -- Both sides postcompose the underlying singular simplex with `ψ ∘ φ`.
  ext k σ
  rfl

end TauCeti
