/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Abelian.Refinements
public import TauCeti.AlgebraicTopology.EilenbergSteenrod
public import TauCeti.Topology.Category.TopTriple

/-!
# The long exact sequence of a triple for a homology pretheory

Let `HP` be a homology pretheory (`TopPair.HomologyPretheory`) with the long exact sequence of
pairs (`TopPair.HomologyPretheory.HasPairSequence`). For a triple `B ⊆ A ⊆ X` of topological
spaces (`TauCeti.TopTriple`), the relative groups of the three pairs `(A, B)`, `(X, B)` and
`(X, A)` form the long exact sequence of the triple

`⋯ ⟶ Hᵢ(A, B) ⟶ Hᵢ(X, B) ⟶ Hᵢ(X, A) ⟶ Hⱼ(A, B) ⟶ Hⱼ(X, B) ⟶ ⋯` (for `c.Rel i j`).

The first two maps are induced by the maps of pairs `(A, B) ⟶ (X, B) ⟶ (X, A)`. The connecting
morphism `HP.tripleδ i j` is the boundary `Hᵢ(X, A) ⟶ Hⱼ(A)` of the pair `(X, A)` followed by
the map `Hⱼ(A) ⟶ Hⱼ(A, B)`; it is natural in the triple, and morphisms of homology pretheories
commute with it.

Exactness is derived from the exactness axiom for the three pairs, in any abelian coefficient
category. When `i` has no successor in the complex shape, the sequence ends with the epimorphism
`Hᵢ(X, B) ⟶ Hᵢ(X, A)`. Since the coefficient category is arbitrary, the results also apply to a
pretheory valued in an opposite category `Dᵒᵖ`, whose functors are contravariant in the pair:
read in `D`, they give the long exact sequence of a triple in cohomology.

## Main declarations

* `TopPair.HomologyPretheory.tripleδ`: the connecting morphism `Hᵢ(X, A) ⟶ Hⱼ(A, B)` of a
  triple, as a natural transformation.
* `TopPair.HomologyPretheory.Hom.tripleδ_comm`: morphisms of homology pretheories commute with
  the connecting morphisms of triples.
* `TopPair.HomologyPretheory.exact_triple_total`, `exact_triple_outer`, `exact_triple_inner`:
  exactness of the sequence of a triple at `Hᵢ(X, B)`, at `Hᵢ(X, A)` and at `Hⱼ(A, B)`.
* `TopPair.HomologyPretheory.epi_map_totalToOuter_of_not_rel`: the sequence ends with an
  epimorphism.

## References

* S. Eilenberg and N. Steenrod, *Foundations of Algebraic Topology*, Chapter I, Section 10.
-/

public section

open CategoryTheory Limits TauCeti TauCeti.TopTriple

universe u

namespace TopPair.HomologyPretheory

variable {C : Type*} [Category* C] {ι : Type*} {c : ComplexShape ι}

section HasZeroMorphisms

variable [HasZeroMorphisms C] (HP : HomologyPretheory.{u} C c)

/-- The boundary `Hᵢ(X, A) ⟶ Hⱼ(A)` of a pair, with its target written as the homology of the
subspace `X.snd`, so that it composes with maps out of `Hⱼ(A)` up to reducible unfolding. -/
private def pairδ (i j : ι) (X : TopPair.{u}) : (HP.Hₚ i).obj X ⟶ (HP.H j).obj X.snd :=
  (HP.δ i j).app X

@[reassoc]
private lemma map_comp_pairδ (i j : ι) {X Y : TopPair.{u}} (f : X ⟶ Y) :
    (HP.Hₚ i).map f ≫ HP.pairδ i j Y = HP.pairδ i j X ≫ (HP.H j).map (Hom.snd f) :=
  (HP.δ i j).naturality f

/-- The connecting morphism `Hᵢ(X, A) ⟶ Hⱼ(A, B)` of the long exact sequence of a triple
`(X, A, B)`: the boundary `Hᵢ(X, A) ⟶ Hⱼ(A)` of the pair `(X, A)` followed by the map
`Hⱼ(A) ⟶ Hⱼ(A, B)`. -/
def tripleδ (i j : ι) : outerPair ⋙ HP.Hₚ i ⟶ innerPair ⋙ HP.Hₚ j where
  app T := HP.pairδ i j (outerPair.obj T) ≫ HP.hFstToHₚ j (innerPair.obj T)
  naturality T T' φ := by
    have hn := HP.hFstToHₚ_naturality (innerPair.map φ) j
    erw [innerPair_map_fst] at hn
    dsimp only [CategoryTheory.Functor.comp_map]
    erw [map_comp_pairδ_assoc, outerPair_map_snd]
    simpa only [Category.assoc] using
      congrArg (HP.pairδ i j (outerPair.obj T) ≫ ·) hn.symm


private lemma tripleδ_app' (i j : ι) (T : TopTriple.{u}) :
    (HP.tripleδ i j).app T = HP.pairδ i j (outerPair.obj T) ≫ HP.hFstToHₚ j (innerPair.obj T) := by
  rw [tripleδ.eq_def]

/-- The connecting morphism of a triple is the boundary of the pair `(X, A)` followed by the map
`Hⱼ(A) ⟶ Hⱼ(A, B)`. -/
lemma tripleδ_app (i j : ι) (T : TopTriple.{u}) :
    (HP.tripleδ i j).app T =
      (HP.δ i j).app (outerPair.obj T) ≫ HP.hFstToHₚ j (innerPair.obj T) :=
  HP.tripleδ_app' i j T

/-- The connecting morphism of a triple vanishes unless `c.Rel i j`. -/
lemma shape_tripleδ (i j : ι) (h : ¬ c.Rel i j) : HP.tripleδ i j = 0 := by
  ext T
  have : HP.pairδ i j (outerPair.obj T) = 0 := by
    rw [pairδ, HP.shape_δ i j h]
    exact zero_app _ _ _
  rw [tripleδ_app', this, zero_comp]
  exact (zero_app (outerPair ⋙ HP.Hₚ i) (innerPair ⋙ HP.Hₚ j) T).symm

/-- A morphism of homology pretheories commutes with the connecting morphisms of triples. -/
@[reassoc]
lemma Hom.tripleδ_comm {HP' : HomologyPretheory.{u} C c} (f : HP ⟶ HP') (i j : ι)
    (T : TopTriple.{u}) :
    (HP.tripleδ i j).app T ≫ (f.homₚ j).app (innerPair.obj T) =
      (f.homₚ i).app (outerPair.obj T) ≫ (HP'.tripleδ i j).app T := by
  have h : HP.pairδ i j (outerPair.obj T) ≫ (f.hom j).app T.snd =
      (f.homₚ i).app (outerPair.obj T) ≫ HP'.pairδ i j (outerPair.obj T) :=
    Hom.w_app f i j (outerPair.obj T)
  rw [tripleδ_app', tripleδ_app', Category.assoc, Hom.hFstToHₚ_comm, reassoc_of% h]

variable [HP.HasPairSequence]

/-- The maps `Hᵢ(X, B) ⟶ Hᵢ(X, A) ⟶ Hⱼ(A, B)` of a triple compose to zero. -/
@[reassoc (attr := simp)]
lemma map_totalToOuter_comp_tripleδ (i j : ι) (T : TopTriple.{u}) :
    (HP.Hₚ i).map (totalToOuter.app T) ≫ (HP.tripleδ i j).app T = 0 := by
  have h : (HP.H j).map T.innerMap ≫ HP.hFstToHₚ j (innerPair.obj T) = 0 :=
    (HP.exact_fst (innerPair.obj T) j).toIsComplex.zero 0
  rw [tripleδ_app', map_comp_pairδ_assoc, totalToOuter_app_snd, h, comp_zero]

/-- The maps `Hᵢ(X, A) ⟶ Hⱼ(A, B) ⟶ Hⱼ(X, B)` of a triple compose to zero. -/
@[reassoc (attr := simp)]
lemma tripleδ_comp_map_innerToTotal (i j : ι) (T : TopTriple.{u}) :
    (HP.tripleδ i j).app T ≫ (HP.Hₚ j).map (innerToTotal.app T) = 0 := by
  by_cases hij : c.Rel i j
  · have h : HP.pairδ i j (outerPair.obj T) ≫ (HP.H j).map T.outerMap = 0 :=
      (HP.exact_snd (outerPair.obj T) i j hij).toIsComplex.zero 0
    rw [tripleδ_app', Category.assoc, hFstToHₚ_naturality, innerToTotal_app_fst,
      ← Category.assoc, h, zero_comp]
  · simp [HP.shape_tripleδ i j hij]

/-- When `i` has no successor in the complex shape, the sequence of a triple ends with the
epimorphism `Hᵢ(X, B) ⟶ Hᵢ(X, A)`. -/
theorem epi_map_totalToOuter_of_not_rel (i : ι) (hi : ∀ j, ¬ c.Rel i j) (T : TopTriple.{u}) :
    Epi ((HP.Hₚ i).map (totalToOuter.app T)) := by
  have := HP.epi_hFstToHₚ_of_not_rel i hi (outerPair.obj T)
  have h := HP.hFstToHₚ_naturality (totalToOuter.app T) i
  rw [totalToOuter_app_fst, CategoryTheory.Functor.map_id, Category.id_comp] at h
  exact epi_of_epi_fac h

end HasZeroMorphisms

section Preadditive

variable [Preadditive C] (HP : HomologyPretheory.{u} C c) [HP.HasPairSequence]

/-- The maps `Hᵢ(A, B) ⟶ Hᵢ(X, B) ⟶ Hᵢ(X, A)` of a triple compose to zero: their composite
factors through the relative group `Hᵢ(A, A)`, which vanishes. -/
@[reassoc (attr := simp)]
lemma map_innerToTotal_comp_map_totalToOuter (i : ι) (T : TopTriple.{u}) :
    (HP.Hₚ i).map (innerToTotal.app T) ≫ (HP.Hₚ i).map (totalToOuter.app T) = 0 := by
  have h : innerToTotal.app T ≫ totalToOuter.app T =
      (TopPair.ofHom (𝟙 T.snd) T.innerMap : innerPair.obj T ⟶ diag.obj T.snd) ≫
        (TopPair.ofHom T.outerMap (𝟙 T.snd) : diag.obj T.snd ⟶ outerPair.obj T) :=
    MorphismProperty.Arrow.Hom.ext ((Category.id_comp _).trans (Category.comp_id _).symm)
      ((Category.comp_id _).trans (Category.id_comp _).symm)
  have : IsIso (diag.obj T.snd).map := inferInstanceAs (IsIso (𝟙 T.snd))
  rw [← CategoryTheory.Functor.map_comp, h, CategoryTheory.Functor.map_comp,
    (HP.isZero_Hₚ_of_isIso_map i (diag.obj T.snd)).eq_of_tgt
    ((HP.Hₚ i).map _) 0, zero_comp]

end Preadditive

section Abelian

variable [Abelian C] (HP : HomologyPretheory.{u} C c) [HP.HasPairSequence]

/-- Exactness of the sequence of a triple at `Hᵢ(X, B)`:
`Hᵢ(A, B) ⟶ Hᵢ(X, B) ⟶ Hᵢ(X, A)` is exact. -/
theorem exact_triple_total (i : ι) (T : TopTriple.{u}) :
    (ComposableArrows.mk₂ ((HP.Hₚ i).map (innerToTotal.app T))
      ((HP.Hₚ i).map (totalToOuter.app T))).Exact := by
  suffices h : ∀ ⦃W : C⦄ (y : W ⟶ (HP.Hₚ i).obj (totalPair.obj T)),
      y ≫ (HP.Hₚ i).map (totalToOuter.app T) = 0 → ∃ (W' : C) (π : W' ⟶ W) (_ : Epi π)
        (x : W' ⟶ (HP.Hₚ i).obj (innerPair.obj T)), π ≫ y = x ≫ (HP.Hₚ i).map (innerToTotal.app T)
    from ComposableArrows.exact₂_mk _ (HP.map_innerToTotal_comp_map_totalToOuter i T)
      ((ShortComplex.exact_iff_exact_up_to_refinements _).2 h)
  intro W y hy
  -- First write `y`, up to refinement, as `z ≫ a + w ≫ βQ` with `a : Hᵢ(A, B) ⟶ Hᵢ(X, B)` and
  -- `βQ : Hᵢ(X) ⟶ Hᵢ(X, B)`.
  obtain ⟨W₁, π₁, _, z, w, hzw⟩ : ∃ (W₁ : C) (π₁ : W₁ ⟶ W) (_ : Epi π₁)
      (z : W₁ ⟶ (HP.Hₚ i).obj (innerPair.obj T)) (w : W₁ ⟶ (HP.H i).obj T.fst),
      π₁ ≫ y = z ≫ (HP.Hₚ i).map (innerToTotal.app T) +
        w ≫ HP.hFstToHₚ i (totalPair.obj T) := by
    obtain ⟨j, hij⟩ | hi := em (∃ j, c.Rel i j)
    · -- The boundary of `y` in `Hⱼ(B)` vanishes in `Hⱼ(A)`, so it is a boundary of `Hᵢ(A, B)`.
      have hy' : (y ≫ HP.pairδ i j (totalPair.obj T)) ≫ (HP.H j).map T.innerMap = 0 := by
        rw [Category.assoc, ← totalToOuter_app_snd, ← map_comp_pairδ, reassoc_of% hy, zero_comp]
      obtain ⟨W₁, π₁, _, (z : W₁ ⟶ (HP.Hₚ i).obj (innerPair.obj T)), hz⟩ :=
        ((HP.exact_snd (innerPair.obj T) i j hij).exact 0).exact_up_to_refinements _ hy'
      replace hz : π₁ ≫ y ≫ HP.pairδ i j (totalPair.obj T) =
          z ≫ HP.pairδ i j (innerPair.obj T) := hz
      -- Then `y - z` has no boundary, so it comes from `Hᵢ(X)`.
      have hz' : (π₁ ≫ y - z ≫ (HP.Hₚ i).map (innerToTotal.app T)) ≫
          HP.pairδ i j (totalPair.obj T) = 0 := by
        simp [hz, map_comp_pairδ]
      obtain ⟨W₂, π₂, _, (w : W₂ ⟶ (HP.H i).obj T.fst), hw⟩ :=
        ((HP.exact_pair (totalPair.obj T) i j hij).exact 0).exact_up_to_refinements _ hz'
      replace hw : π₂ ≫ (π₁ ≫ y - z ≫ (HP.Hₚ i).map (innerToTotal.app T)) =
          w ≫ HP.hFstToHₚ i (totalPair.obj T) := hw
      refine ⟨W₂, π₂ ≫ π₁, epi_comp _ _, π₂ ≫ z, w, ?_⟩
      simp [← hw]
    · push Not at hi
      have := HP.epi_hFstToHₚ_of_not_rel i hi (totalPair.obj T)
      obtain ⟨W₁, π₁, _, w, hw⟩ :=
        surjective_up_to_refinements_of_epi (HP.hFstToHₚ i (totalPair.obj T)) y
      exact ⟨W₁, π₁, inferInstance, 0, w, by rw [hw, zero_comp, zero_add]⟩
  -- The component `w` vanishes in `Hᵢ(X, A)`, so it comes from `Hᵢ(A)`.
  have hw : w ≫ HP.hFstToHₚ i (outerPair.obj T) = 0 := by
    have hn := HP.hFstToHₚ_naturality (totalToOuter.app T) i
    rw [totalToOuter_app_fst, CategoryTheory.Functor.map_id, Category.id_comp] at hn
    simpa only [Preadditive.add_comp, Category.assoc, hn,
      map_innerToTotal_comp_map_totalToOuter, comp_zero, zero_add, hy] using
      (hzw =≫ (HP.Hₚ i).map (totalToOuter.app T)).symm
  obtain ⟨W₂, π₂, _, (v : W₂ ⟶ (HP.H i).obj T.snd), hv⟩ :=
    ((HP.exact_fst (outerPair.obj T) i).exact 0).exact_up_to_refinements _ hw
  replace hv : π₂ ≫ w = v ≫ (HP.H i).map T.outerMap := hv
  refine ⟨W₂, π₂ ≫ π₁, epi_comp _ _, π₂ ≫ z + v ≫ HP.hFstToHₚ i (innerPair.obj T), ?_⟩
  rw [Category.assoc, hzw, Preadditive.comp_add, Preadditive.add_comp, Category.assoc,
    Category.assoc, reassoc_of% hv, hFstToHₚ_naturality, innerToTotal_app_fst]

/-- Exactness of the sequence of a triple at `Hᵢ(X, A)`:
`Hᵢ(X, B) ⟶ Hᵢ(X, A) ⟶ Hⱼ(A, B)` is exact for `c.Rel i j`. -/
theorem exact_triple_outer (i j : ι) (hij : c.Rel i j) (T : TopTriple.{u}) :
    (ComposableArrows.mk₂ ((HP.Hₚ i).map (totalToOuter.app T)) ((HP.tripleδ i j).app T)).Exact := by
  suffices h : ∀ ⦃W : C⦄ (x : W ⟶ (HP.Hₚ i).obj (outerPair.obj T)),
      x ≫ (HP.tripleδ i j).app T = 0 → ∃ (W' : C) (π : W' ⟶ W) (_ : Epi π)
        (y : W' ⟶ (HP.Hₚ i).obj (totalPair.obj T)), π ≫ x = y ≫ (HP.Hₚ i).map (totalToOuter.app T)
    from ComposableArrows.exact₂_mk _ (HP.map_totalToOuter_comp_tripleδ i j T)
      ((ShortComplex.exact_iff_exact_up_to_refinements _).2 h)
  intro W x hx
  rw [tripleδ_app', ← Category.assoc] at hx
  -- The boundary of `x` in `Hⱼ(A)` comes from `Hⱼ(B)`.
  obtain ⟨W₁, π₁, _, (u : W₁ ⟶ (HP.H j).obj T.thd), hu⟩ :=
    ((HP.exact_fst (innerPair.obj T) j).exact 0).exact_up_to_refinements _ hx
  replace hu : π₁ ≫ x ≫ HP.pairδ i j (outerPair.obj T) = u ≫ (HP.H j).map T.innerMap := hu
  -- That class of `Hⱼ(B)` vanishes in `Hⱼ(X)`, so it is the boundary of some `y` in `Hᵢ(X, B)`.
  have hu' : u ≫ (HP.H j).map T.totalMap = 0 := by
    have h : HP.pairδ i j (outerPair.obj T) ≫ (HP.H j).map T.outerMap = 0 :=
      (HP.exact_snd (outerPair.obj T) i j hij).toIsComplex.zero 0
    rw [← T.innerMap_comp_outerMap, CategoryTheory.Functor.map_comp, ← reassoc_of% hu]
    simp [h]
  obtain ⟨W₂, π₂, _, (y : W₂ ⟶ (HP.Hₚ i).obj (totalPair.obj T)), hy⟩ :=
    ((HP.exact_snd (totalPair.obj T) i j hij).exact 0).exact_up_to_refinements _ hu'
  replace hy : π₂ ≫ u = y ≫ HP.pairδ i j (totalPair.obj T) := hy
  -- Then `x - y` has no boundary in `Hⱼ(A)`, so it comes from `Hᵢ(X)`.
  have hxy : (π₂ ≫ π₁ ≫ x - y ≫ (HP.Hₚ i).map (totalToOuter.app T)) ≫
      HP.pairδ i j (outerPair.obj T) = 0 := by
    simp [hu, reassoc_of% hy, map_comp_pairδ]
  obtain ⟨W₃, π₃, _, (w : W₃ ⟶ (HP.H i).obj T.fst), hw⟩ :=
    ((HP.exact_pair (outerPair.obj T) i j hij).exact 0).exact_up_to_refinements _ hxy
  replace hw : π₃ ≫ (π₂ ≫ π₁ ≫ x - y ≫ (HP.Hₚ i).map (totalToOuter.app T)) =
      w ≫ HP.hFstToHₚ i (outerPair.obj T) := hw
  refine ⟨W₃, π₃ ≫ π₂ ≫ π₁, inferInstance,
    π₃ ≫ y + w ≫ HP.hFstToHₚ i (totalPair.obj T), ?_⟩
  have hn := HP.hFstToHₚ_naturality (totalToOuter.app T) i
  rw [totalToOuter_app_fst, CategoryTheory.Functor.map_id, Category.id_comp] at hn
  simp only [Preadditive.add_comp, Category.assoc, hn, ← hw, Preadditive.comp_sub,
    Category.assoc]
  abel

/-- Exactness of the sequence of a triple at `Hⱼ(A, B)`:
`Hᵢ(X, A) ⟶ Hⱼ(A, B) ⟶ Hⱼ(X, B)` is exact for `c.Rel i j`. -/
theorem exact_triple_inner (i j : ι) (hij : c.Rel i j) (T : TopTriple.{u}) :
    (ComposableArrows.mk₂ ((HP.tripleδ i j).app T) ((HP.Hₚ j).map (innerToTotal.app T))).Exact := by
  suffices h : ∀ ⦃W : C⦄ (z : W ⟶ (HP.Hₚ j).obj (innerPair.obj T)),
      z ≫ (HP.Hₚ j).map (innerToTotal.app T) = 0 → ∃ (W' : C) (π : W' ⟶ W) (_ : Epi π)
        (x : W' ⟶ (HP.Hₚ i).obj (outerPair.obj T)), π ≫ z = x ≫ (HP.tripleδ i j).app T
    from ComposableArrows.exact₂_mk _ (HP.tripleδ_comp_map_innerToTotal i j T)
      ((ShortComplex.exact_iff_exact_up_to_refinements _).2 h)
  intro W z hz
  -- First lift `z`, up to refinement, to `v` in `Hⱼ(A)`.
  obtain ⟨W₁, π₁, _, v, hv⟩ : ∃ (W₁ : C) (π₁ : W₁ ⟶ W) (_ : Epi π₁)
      (v : W₁ ⟶ (HP.H j).obj T.snd), π₁ ≫ z = v ≫ HP.hFstToHₚ j (innerPair.obj T) := by
    by_cases hj : ∃ k, c.Rel j k
    · obtain ⟨k, hjk⟩ := hj
      have hz' : z ≫ HP.pairδ j k (innerPair.obj T) = 0 := by
        simpa [map_comp_pairδ] using hz =≫ HP.pairδ j k (totalPair.obj T)
      exact ((HP.exact_pair (innerPair.obj T) j k hjk).exact 0).exact_up_to_refinements _ hz'
    · push Not at hj
      have := HP.epi_hFstToHₚ_of_not_rel j hj (innerPair.obj T)
      exact surjective_up_to_refinements_of_epi (HP.hFstToHₚ j (innerPair.obj T)) z
  -- The image of `v` in `Hⱼ(X)` vanishes in `Hⱼ(X, B)`, so it comes from `Hⱼ(B)`.
  have hv' : (v ≫ (HP.H j).map T.outerMap) ≫ HP.hFstToHₚ j (totalPair.obj T) = 0 := by
    have hn := HP.hFstToHₚ_naturality (innerToTotal.app T) j
    rw [innerToTotal_app_fst] at hn
    simpa only [Category.assoc, hn, hz, comp_zero] using
      (hv =≫ (HP.Hₚ j).map (innerToTotal.app T)).symm
  obtain ⟨W₂, π₂, _, (u : W₂ ⟶ (HP.H j).obj T.thd), hu⟩ :=
    ((HP.exact_fst (totalPair.obj T) j).exact 0).exact_up_to_refinements _ hv'
  replace hu : π₂ ≫ v ≫ (HP.H j).map T.outerMap = u ≫ (HP.H j).map T.totalMap := hu
  -- Then `v` minus the image of `u` vanishes in `Hⱼ(X)`, so it is a boundary of `Hᵢ(X, A)`.
  have huv : (π₂ ≫ v - u ≫ (HP.H j).map T.innerMap) ≫ (HP.H j).map T.outerMap = 0 := by
    rw [Preadditive.sub_comp, Category.assoc, hu, Category.assoc, ← CategoryTheory.Functor.map_comp,
      T.innerMap_comp_outerMap, sub_self]
  obtain ⟨W₃, π₃, _, (x : W₃ ⟶ (HP.Hₚ i).obj (outerPair.obj T)), hx⟩ :=
    ((HP.exact_snd (outerPair.obj T) i j hij).exact 0).exact_up_to_refinements _ huv
  replace hx : π₃ ≫ (π₂ ≫ v - u ≫ (HP.H j).map T.innerMap) =
      x ≫ HP.pairδ i j (outerPair.obj T) := hx
  have hB : (HP.H j).map T.innerMap ≫ HP.hFstToHₚ j (innerPair.obj T) = 0 :=
    (HP.exact_fst (innerPair.obj T) j).toIsComplex.zero 0
  refine ⟨W₃, π₃ ≫ π₂ ≫ π₁, inferInstance, x, ?_⟩
  rw [tripleδ_app', ← reassoc_of% hx]
  simp only [Category.assoc, hv, Preadditive.sub_comp, hB, comp_zero, sub_zero]

end Abelian

end TopPair.HomologyPretheory
