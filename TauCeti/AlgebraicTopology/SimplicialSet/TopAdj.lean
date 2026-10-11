/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.TopAdj
public import TauCeti.Geometry.Convex.ConvexSpace.Topology

/-!
# Naturality of singular simplices

The identification of singular simplices with continuous maps from standard simplices commutes
with continuous maps, which act by postcomposition; in particular, so does the identification of
points with singular zero-simplices. Faces of singular simplices obtained by precomposition with
affine simplices are also expressed in terms of their vertex maps.
This transfers naturality of simplicial vertex classes to singular homology, giving naturality
of the basepoint section of the augmentation in `TauCeti.singularHomology₀Section_naturality`.
Along an inducing map, a singular simplex of the target is induced from the source exactly when
its image lies in the range (`Topology.IsInducing.mem_range_toSSet_map_app_iff`).
A morphism `Δ[m] ⟶ Sing X` is determined by its underlying continuous map
(`TauCeti.TopCat.hom_ext_stdSimplex`), its faces are its restrictions to the facets
(`TauCeti.TopCat.toSSetObjEquiv_yonedaEquiv_δ_comp_apply`), and the constant morphism at a point
is the constant map (`TauCeti.TopCat.toSSetObjEquiv_yonedaEquiv_const_apply`).
-/

public section

open CategoryTheory Simplicial Convexity

universe u

namespace TauCeti.TopCat

/-- Mapping the singular vertex of a point gives the singular vertex of its image. -/
@[simp]
lemma toSSet_map_app_toSSetObj₀Equiv_symm {X Y : TopCat.{u}} (f : X ⟶ Y) (x : X) :
    (TopCat.toSSet.map f).app (Opposite.op ⦋0⦌) (TopCat.toSSetObj₀Equiv.symm x) =
      TopCat.toSSetObj₀Equiv.symm (f x) := rfl

/-- The map of singular simplicial sets induced by a continuous map acts on singular simplices
by postcomposition. -/
@[simp]
lemma toSSetObjEquiv_toSSet_map_app {X Y : TopCat.{u}} (f : X ⟶ Y) {n : SimplexCategoryᵒᵖ}
    (σ : (TopCat.toSSet.obj X).obj n) :
    Y.toSSetObjEquiv n ((TopCat.toSSet.map f).app n σ) =
      (ConcreteCategory.hom f).comp (X.toSSetObjEquiv n σ) := rfl

/-- The map of singular simplicial sets induced by a continuous map sends the singular simplex
of a continuous map `g` from a standard simplex to that of its composite with the map. -/
@[simp]
lemma toSSet_map_app_toSSetObjEquiv_symm {X Y : TopCat.{u}} (f : X ⟶ Y) {n : SimplexCategoryᵒᵖ}
    (g : C(StdSimplex ℝ (Fin (n.unop.len + 1)), X)) :
    (TopCat.toSSet.map f).app n ((X.toSSetObjEquiv n).symm g) =
      (Y.toSSetObjEquiv n).symm ((ConcreteCategory.hom f).comp g) := rfl

/-- Precomposing a singular simplex with the affine simplex with vertices `v`, and then with
the inclusion of a facet, is precomposing it with the affine simplex with the restricted vertices.
-/
@[simp]
lemma δ_toSSetObjEquiv_symm_comp_affineMapMk {X : TopCat.{u}} {m n : ℕ}
    (σ : C(StdSimplex ℝ (Fin (m + 1)), X)) (v : Fin (n + 2) → StdSimplex ℝ (Fin (m + 1)))
    (k : Fin (n + 2)) :
    (TopCat.toSSet.obj X).δ k ((X.toSSetObjEquiv _).symm
        (σ.comp (StdSimplex.continuousAffineMapMk v))) =
      (X.toSSetObjEquiv _).symm (σ.comp
        (StdSimplex.continuousAffineMapMk (v ∘ k.succAbove))) := by
  apply (X.toSSetObjEquiv _).injective
  ext z
  simp [StdSimplex.affineMapMk_apply]

/-- Precomposing a facet of a singular simplex with the affine simplex with vertices `v` is
precomposing the singular simplex with the affine simplex with the pushed-forward vertices. -/
@[simp]
lemma toSSetObjEquiv_symm_comp_affineMapMk_δ {X : TopCat.{u}} {m n : ℕ}
    (σ : TopCat.toSSet.obj X _⦋m + 1⦌)
    (v : Fin (n + 1) → StdSimplex ℝ (Fin (m + 1))) (j : Fin (m + 2)) :
    (X.toSSetObjEquiv (.op ⦋n⦌)).symm ((X.toSSetObjEquiv _ ((TopCat.toSSet.obj X).δ j σ)).comp
        (StdSimplex.continuousAffineMapMk v)) =
      (X.toSSetObjEquiv (.op ⦋n⦌)).symm ((X.toSSetObjEquiv _ σ).comp
        (StdSimplex.continuousAffineMapMk (StdSimplex.map j.succAbove ∘ v))) := by
  apply (X.toSSetObjEquiv _).injective
  ext z
  have h := congr($(StdSimplex.comp_affineMapMk (R := ℝ) (StdSimplex.affineMap j.succAbove) v) z)
  simp only [ConvexSpace.AffineMap.coe_comp, Function.comp_apply,
    StdSimplex.coe_affineMap] at h
  simp [h]

/-- A morphism from a standard simplex to the singular simplicial set of a space is determined by
the continuous map underlying the corresponding singular simplex. -/
lemma hom_ext_stdSimplex {X : TopCat.{u}} {m : ℕ} {f g : Δ[m] ⟶ TopCat.toSSet.obj X}
    (h : ∀ z, X.toSSetObjEquiv _ (SSet.yonedaEquiv f) z =
      X.toSSetObjEquiv _ (SSet.yonedaEquiv g) z) : f = g :=
  SSet.yonedaEquiv.injective ((X.toSSetObjEquiv _).injective (ContinuousMap.ext h))

/-- The continuous map underlying the face `δ i ≫ g` of a morphism `g : Δ[m + 1] ⟶ Sing X` is the
restriction of the continuous map underlying `g` to the facet opposite `i`. -/
@[simp]
lemma toSSetObjEquiv_yonedaEquiv_δ_comp_apply {X : TopCat.{u}} {m : ℕ}
    (g : Δ[m + 1] ⟶ TopCat.toSSet.obj X) (i : Fin (m + 2)) (z : StdSimplex ℝ (Fin (m + 1))) :
    X.toSSetObjEquiv _ (SSet.yonedaEquiv (SSet.stdSimplex.δ i ≫ g)) z =
      X.toSSetObjEquiv _ (SSet.yonedaEquiv g) (z.map i.succAbove) := by
  rw [SSet.stdSimplex.yonedaEquiv_δ_comp, TopCat.toSSetObjEquiv_δ_apply]

/-- The constant morphism `Δ[m] ⟶ Sing X` at the singular vertex of a point `x` is the constant
map to `x`. -/
@[simp]
lemma toSSetObjEquiv_yonedaEquiv_const_apply {X : TopCat.{u}} {m : ℕ} (x : X)
    (z : StdSimplex ℝ (Fin (m + 1))) :
    X.toSSetObjEquiv _ (SSet.yonedaEquiv
      (SSet.const (TopCat.toSSetObj₀Equiv.symm x) : Δ[m] ⟶ TopCat.toSSet.obj X)) z = x :=
  (rfl)

end TauCeti.TopCat

namespace Topology.IsInducing

open TauCeti.TopCat in
/-- A singular simplex of `X` is induced from `Y` along an inducing map `f : Y ⟶ X` exactly when
its image lies in the range of `f`. -/
lemma mem_range_toSSet_map_app_iff {X Y : TopCat.{u}} {f : Y ⟶ X} (hf : IsInducing f)
    (n : SimplexCategoryᵒᵖ) (σ : (TopCat.toSSet.obj X).obj n) :
    σ ∈ Set.range ((TopCat.toSSet.map f).app n) ↔
      Set.range (X.toSSetObjEquiv n σ) ⊆ Set.range f := by
  constructor
  · rintro ⟨τ, rfl⟩
    rw [toSSetObjEquiv_toSSet_map_app, ContinuousMap.coe_comp, Set.range_comp]
    exact Set.image_subset_range _ _
  · intro h
    choose g hg using fun t ↦ h (Set.mem_range_self t)
    have hgc : Continuous g := hf.continuous_iff.mpr (by
      convert (X.toSSetObjEquiv n σ).continuous using 1
      exact funext hg)
    refine ⟨(Y.toSSetObjEquiv n).symm ⟨g, hgc⟩, ?_⟩
    rw [toSSet_map_app_toSSetObjEquiv_symm, Equiv.symm_apply_eq]
    ext t
    exact hg t

end Topology.IsInducing
