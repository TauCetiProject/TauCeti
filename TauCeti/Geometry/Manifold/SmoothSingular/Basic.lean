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

The `p`-simplices of the subcomplex form the type `TauCeti.SmoothSimplex I M p`. A smooth simplex
is determined by the continuous map it induces on `Δᵖ` (`TauCeti.SmoothSimplex.toContinuousMap`),
and every continuous map on `Δᵖ` that is smooth in the sense of maps on arbitrary subsets is one
(`TauCeti.SmoothSimplex.mk`). Its extension to `ℝᵖ` by its value at the origin
(`TauCeti.SmoothSimplex.extension`) is smooth within `Δᵖ`.

These are the chains on which forms are integrated in the comparison of de Rham cohomology with
singular cohomology. Only a charted space is required for the definitions.

## Main definitions and results

* `TauCeti.smoothSingularSubcomplex`: the subcomplex of smooth singular simplices.
* `TauCeti.smoothSingularSubcomplex_le_preimage`: smooth maps preserve smooth simplices.
* `TauCeti.smoothSingularSubcomplexMap`: the induced map of smooth singular subcomplexes.
* `TauCeti.SmoothSimplex`: the smooth singular `p`-simplices, the `p`-simplices of
  `TauCeti.smoothSingularSubcomplex`.
* `TauCeti.SmoothSimplex.toContinuousMap`, `TauCeti.SmoothSimplex.mk`: a smooth simplex as a
  continuous map on `Δᵖ`, and back.
* `TauCeti.SmoothSimplex.extension`: a smooth simplex extended to `ℝᵖ`, smooth within `Δᵖ`.
* `TauCeti.SmoothSimplex.toContinuousMap_δ`: the faces of a smooth simplex are its composites with
  the face inclusions.
* `TauCeti.SmoothSimplex.toContinuousMap_smoothSingularSubcomplexMap_app`: a smooth map acts on
  smooth simplices by composition.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Chapter 18, *Smooth Singular Homology*.
-/

public section

noncomputable section

open CategoryTheory Convexity Set Topology Simplicial Opposite
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

variable (I M) in
/-- The smooth singular `p`-simplices of `M`: the `p`-simplices of the subcomplex
`TauCeti.smoothSingularSubcomplex I M` of the singular simplicial set. They generate the smooth
singular chains. -/
abbrev SmoothSimplex (p : ℕ) : Type u :=
  (smoothSingularSubcomplex I M : SSet.{u}) _⦋p⦌

namespace SmoothSimplex

variable {p : ℕ}

/-- A smooth singular simplex as a continuous map on the full-dimensional simplex `Δᵖ`. -/
def toContinuousMap (σ : SmoothSimplex I M p) : C(fullSimplex p, M) :=
  ((TopCat.of M).toSSetObjEquiv _ σ.1).comp
    ⟨fullSimplexEquivStdSimplex p, (fullSimplexEquivStdSimplex p).continuous⟩

/-- A smooth singular simplex read on `Δᵖ` is the underlying singular simplex read through the
identification of `Δᵖ` with the barycentric standard simplex. -/
theorem toContinuousMap_apply (σ : SmoothSimplex I M p) (x : fullSimplex p) :
    σ.toContinuousMap x = (TopCat.of M).toSSetObjEquiv _ σ.1 (fullSimplexEquivStdSimplex p x) :=
  (rfl)

/-- The `i`-th face of a smooth simplex, read on `Δᵖ`, is the simplex composed with the `i`-th face
inclusion `Δᵖ → Δᵖ⁺¹`. -/
theorem toContinuousMap_δ (σ : SmoothSimplex I M (p + 1)) (i : Fin (p + 2)) (x : fullSimplex p) :
    toContinuousMap ((smoothSingularSubcomplex I M : SSet).δ i σ) x =
      σ.toContinuousMap (simplexFace p i x) := by
  rw [toContinuousMap_apply, toContinuousMap_apply, fullSimplexEquivStdSimplex_simplexFace]
  -- The face of a simplex of a subcomplex is the face of the underlying singular simplex, and
  -- `TopCat.toSSetObjEquiv` reads faces through `StdSimplex.map`, both by definition.
  rfl

/-- A smooth singular simplex is smooth on `Δᵖ` in the sense of maps on arbitrary subsets. -/
theorem contMDiffOnSubset_toContinuousMap (σ : SmoothSimplex I M p) :
    ContMDiffOnSubset I ∞ σ.toContinuousMap :=
  (mem_smoothSingularSubcomplex_iff σ.1).mp σ.2

/-- A smooth singular simplex is determined by the map it induces on `Δᵖ`. -/
theorem toContinuousMap_injective :
    Function.Injective (toContinuousMap : SmoothSimplex I M p → C(fullSimplex p, M)) := by
  intro σ τ h
  refine Subtype.ext (((TopCat.of M).toSSetObjEquiv _).injective (ContinuousMap.ext fun y ↦ ?_))
  simpa only [toContinuousMap_apply, Homeomorph.apply_symm_apply] using
    DFunLike.congr_fun h ((fullSimplexEquivStdSimplex p).symm y)

/-- Two smooth singular simplices agreeing on `Δᵖ` are equal. -/
@[ext]
theorem ext {σ τ : SmoothSimplex I M p} (h : ∀ x, σ.toContinuousMap x = τ.toContinuousMap x) :
    σ = τ :=
  toContinuousMap_injective (ContinuousMap.ext h)

/-- The smooth singular simplex given by a continuous map on `Δᵖ` that is smooth in the sense of
maps on arbitrary subsets. -/
def mk (f : C(fullSimplex p, M)) (hf : ContMDiffOnSubset I ∞ f) : SmoothSimplex I M p :=
  ⟨((TopCat.of M).toSSetObjEquiv _).symm (f.comp (fullSimplexEquivStdSimplex p).symm),
    by simpa [mem_smoothSingularSubcomplex_iff, Function.comp_def] using hf⟩

/-- The smooth simplex given by a map on `Δᵖ` induces that map. -/
@[simp]
theorem toContinuousMap_mk (f : C(fullSimplex p, M)) (hf : ContMDiffOnSubset I ∞ f) :
    (mk f hf).toContinuousMap = f := by
  ext x
  simp [toContinuousMap_apply, mk]

/-- The extension of a smooth singular simplex to `ℝᵖ` by its value at the origin off `Δᵖ`. Only
its values on `Δᵖ` and its derivatives within `Δᵖ` carry information. -/
def extension (σ : SmoothSimplex I M p) : EuclideanSpace ℝ (Fin p) → M :=
  Function.extend Subtype.val σ.toContinuousMap
    fun _ ↦ σ.toContinuousMap ⟨0, zero_mem_fullSimplex p⟩

/-- The extension of a smooth simplex agrees with it on `Δᵖ`. -/
@[simp]
theorem extension_coe (σ : SmoothSimplex I M p) (x : fullSimplex p) :
    σ.extension x = σ.toContinuousMap x :=
  Subtype.val_injective.extend_apply _ _ x

/-- The extension of a smooth simplex is smooth within `Δᵖ`. -/
theorem contMDiffOn_extension (σ : SmoothSimplex I M p) :
    ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) I ∞ σ.extension (fullSimplex p) :=
  σ.contMDiffOnSubset_toContinuousMap.contMDiffOn σ.extension_coe

end SmoothSimplex

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

/-- The image of a smooth simplex under a smooth map, read on `Δᵖ`, is the composite. -/
theorem SmoothSimplex.toContinuousMap_smoothSingularSubcomplexMap_app {p : ℕ}
    (hφ : ContMDiff I J ∞ φ) (σ : SmoothSimplex I M p) :
    toContinuousMap ((smoothSingularSubcomplexMap φ hφ).app (op ⦋p⦌) σ) =
      (ContinuousMap.mk φ hφ.continuous).comp σ.toContinuousMap := by
  have h := ConcreteCategory.congr_hom
    (NatTrans.congr_app (smoothSingularSubcomplexMap_ι hφ) (op ⦋p⦌)) σ
  simp only [NatTrans.comp_app, ConcreteCategory.comp_apply, Subfunctor.ι_app,
    TypeCat.ofHom_apply] at h
  ext x
  rw [toContinuousMap_apply, h, TopCat.toSSetObjEquiv_toSSet_map_app]
  simp [toContinuousMap_apply]

end TauCeti
