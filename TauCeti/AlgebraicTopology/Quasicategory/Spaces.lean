/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Quasicategory.CatInfty
public import TauCeti.AlgebraicTopology.Quasicategory.FullSubcategory
public import TauCeti.AlgebraicTopology.Quasicategory.RightMappingSpace
public import TauCeti.AlgebraicTopology.SimplicialNerve.Basic

/-!
# The simplicial category of Kan complexes and the quasicategory `Spaces`

The full simplicial subcategory `SSet.SpacesΔ` of `SSet` spanned by the Kan complexes has mapping
simplicial sets `Fun(A, B)`, which are themselves Kan complexes (`SSet.SpacesΔ.kanComplex_sHom`).
Its simplicial (homotopy coherent) nerve is `SSet.spaces`, the quasicategory of small spaces
(HTT Definition 1.2.16.1), which is a quasicategory by
`CategoryTheory.SimplicialNerve.quasicategory` (`SSet.spaces.quasicategory`).

Because every simplex of a function complex `Fun(A, B)` into a Kan complex `B` lies in its core
(`SSet.core_sHom_eq_top`), the identity on underlying simplicial sets upgrades to a simplicial
functor `SSet.SpacesΔ.toCatInftyΔ : EnrichedFunctor SSet SpacesΔ CatInftyΔ` that is an isomorphism
on every mapping simplicial set (`SSet.SpacesΔ.isIso_toCatInftyΔ_map`). Passing to simplicial
nerves produces the inclusion `SSet.spacesToCatInfty : SSet.spaces ⟶ SSet.catInfty`, which
identifies `SSet.spaces` with the full enhanced subcategory of `SSet.catInfty` spanned by the Kan
complexes (`SSet.spacesIsoFullSubcategory`). In particular, `SSet.spacesToCatInfty` is a
monomorphism, an inner fibration, and induces isomorphisms on all right mapping spaces.

## Main definitions

* `SSet.SpacesΔ`: the full simplicial subcategory of `SSet` spanned by the Kan complexes.
* `SSet.spaces`: the simplicial nerve of `SSet.SpacesΔ`, the quasicategory of small spaces.
* `SSet.SpacesΔ.toCatInftyΔ`: the canonical simplicial functor from `SSet.SpacesΔ` to
  `SSet.CatInftyΔ`.
* `SSet.spacesToCatInfty`: the induced map of quasicategories `SSet.spaces ⟶ SSet.catInfty`.
* `SSet.spacesIsoFullSubcategory`: the isomorphism identifying `SSet.spaces` with the full
  enhanced subcategory of `SSet.catInfty` spanned by the Kan complexes.

## Main results

* `SSet.SpacesΔ.kanComplex_sHom`: the mapping simplicial sets of `SSet.SpacesΔ` are Kan complexes.
* `SSet.spaces.quasicategory`: `SSet.spaces` is a quasicategory.
* `SSet.SpacesΔ.isIso_toCatInftyΔ_map`: `SSet.SpacesΔ.toCatInftyΔ` induces isomorphisms on mapping
  simplicial sets.
* `SSet.spacesIsoFullSubcategory_hom_ι`: the isomorphism `SSet.spacesIsoFullSubcategory`
  intertwines the full enhanced subcategory inclusion with `SSet.spacesToCatInfty`.
* `SSet.mono_spacesToCatInfty`, `SSet.innerFibration_spacesToCatInfty`,
  `SSet.isIso_rightMappingSpace_map_spacesToCatInfty`: `SSet.spacesToCatInfty` is a monomorphism,
  an inner fibration, and induces isomorphisms on right mapping spaces.

## References

* J. Lurie, *Higher Topos Theory*, Proposition 1.1.5.10, Definition 1.2.16.1, and §1.2.11.
-/

public section

open CategoryTheory MonoidalCategory MonoidalClosed EnrichedCategory SimplicialCategory Opposite
  Simplicial

universe u

namespace SSet

/-- The simplicial category of small Kan complexes, realized as the full simplicial subcategory of
`SSet` spanned by the Kan complexes. Its mapping simplicial sets are the function complexes
`Fun(A, B)`. -/
abbrev SpacesΔ : Type (u + 1) :=
  ObjectProperty.FullSubcategory fun A : SSet.{u} ↦ KanComplex A

/-- The simplicial (homotopy coherent) nerve of `SpacesΔ`, the quasicategory of small spaces whose
vertices are the Kan complexes in universe `u`. -/
noncomputable abbrev spaces : SSet.{u + 1} :=
  SimplicialNerve SpacesΔ.{u}

namespace SpacesΔ

/-- The mapping simplicial sets of `SpacesΔ` are Kan complexes, as function complexes into Kan
complexes. -/
instance kanComplex_sHom (A B : SpacesΔ.{u}) : KanComplex (sHom A B) :=
  have := B.property
  inferInstanceAs (KanComplex ((ihom A.obj).obj B.obj))

/-- The canonical simplicial functor from `SpacesΔ` to `CatInftyΔ`, viewing each Kan complex as a
quasicategory and lifting `Fun(A, B)` along `Fun(A, B)^≃ = Fun(A, B)`. -/
@[expose]
noncomputable def toCatInftyΔ : EnrichedFunctor SSet.{u} SpacesΔ.{u} CatInftyΔ.{u} where
  obj A := ⟨CoreEnriched.of A.obj, have := A.property; inferInstance⟩
  map A B := Subcomplex.lift (𝟙 (sHom A.obj B.obj)) (by
    have := B.property
    rw [core_sHom_eq_top]
    exact le_top)
  map_id A := by
    rw [← cancel_mono (Subcomplex.ι _), Category.assoc, Subcomplex.lift_ι]
    change eId SSet A.obj ≫ 𝟙 (sHom A.obj A.obj) =
      eId SSet (CoreEnriched.of A.obj) ≫ (sHom A.obj A.obj).core.ι
    rw [Category.comp_id, CoreEnriched.eId_ι]
  map_comp A B C := by
    rw [← cancel_mono (Subcomplex.ι _), Category.assoc, Subcomplex.lift_ι, Category.assoc]
    change eComp SSet A.obj B.obj C.obj ≫ 𝟙 (sHom A.obj C.obj) =
      (Subcomplex.lift (𝟙 _) _ ⊗ₘ Subcomplex.lift (𝟙 _) _) ≫
        eComp SSet (CoreEnriched.of A.obj) (CoreEnriched.of B.obj) (CoreEnriched.of C.obj) ≫
          (sHom A.obj C.obj).core.ι
    rw [Category.comp_id, CoreEnriched.eComp_ι, tensorHom_comp_tensorHom_assoc, Subcomplex.lift_ι,
      Subcomplex.lift_ι, id_tensorHom_id, Category.id_comp]

/-- `SpacesΔ.toCatInftyΔ` preserves underlying simplicial sets on objects. -/
@[simp]
lemma toCatInftyΔ_obj_toSSet (A : SpacesΔ.{u}) :
    (toCatInftyΔ.obj A).obj.toSSet = A.obj :=
  rfl

/-- Composing `toCatInftyΔ.map A B` with the core inclusion gives the identity on `Fun(A, B)`. -/
@[simp]
lemma toCatInftyΔ_map_ι (A B : SpacesΔ.{u}) :
    toCatInftyΔ.map A B ≫ (sHom A.obj B.obj).core.ι = 𝟙 (sHom A.obj B.obj) := by
  dsimp [toCatInftyΔ]

/-- Composing the core inclusion with `toCatInftyΔ.map A B` gives the identity on `Fun(A, B)^≃`. -/
@[simp]
lemma ι_toCatInftyΔ_map (A B : SpacesΔ.{u}) :
    (sHom A.obj B.obj).core.ι ≫ toCatInftyΔ.map A B =
      𝟙 ((sHom A.obj B.obj).core : SSet.{u}) := by
  refine (cancel_mono (sHom A.obj B.obj).core.ι).1 ?_
  dsimp only [toCatInftyΔ]
  rw [Category.assoc, Subcomplex.lift_ι, Category.comp_id, Category.id_comp]

/-- The simplicial functor `SpacesΔ.toCatInftyΔ` induces isomorphisms on all mapping simplicial
sets. -/
instance isIso_toCatInftyΔ_map (A B : SpacesΔ.{u}) : IsIso (toCatInftyΔ.map A B) :=
  ⟨⟨(sHom A.obj B.obj).core.ι, toCatInftyΔ_map_ι A B, ι_toCatInftyΔ_map A B⟩⟩

end SpacesΔ

/-- **HTT Proposition 1.1.5.10**: the simplicial nerve `Spaces` of small Kan complexes is a
quasicategory, as `SpacesΔ` is locally Kan. -/
instance spaces.quasicategory : Quasicategory spaces.{u} :=
  CategoryTheory.SimplicialNerve.quasicategory SpacesΔ.{u}

/-- The canonical map of quasicategories from `Spaces` to `Cat∞`, induced on simplicial nerves by
`SpacesΔ.toCatInftyΔ`. -/
noncomputable def spacesToCatInfty : spaces.{u} ⟶ catInfty.{u} :=
  simplicialNerveMap SpacesΔ.toCatInftyΔ

/-- On vertices, `spacesToCatInfty` preserves the underlying simplicial set. -/
lemma vertexEquiv_spacesToCatInfty_app (x : spaces.{u} _⦋0⦌) :
    (SimplicialNerve.vertexEquiv CatInftyΔ.{u} (spacesToCatInfty.app (op ⦋0⦌) x)).obj.toSSet =
      (SimplicialNerve.vertexEquiv SpacesΔ.{u} x).obj := by
  rw [SimplicialNerve.vertexEquiv_apply, SimplicialNerve.vertexEquiv_apply,
    spacesToCatInfty, simplicialNerveMap_app]
  rfl

/-- Every vertex of a simplex in the full enhanced subcategory of `Cat∞` on Kan complexes has a
Kan complex as its underlying simplicial set. -/
private lemma kanComplex_of_mem_spacesSubcomplex {n : SimplexCategoryᵒᵖ}
    (G : (catInfty.{u}.fullEnhancedSubcategory
      fun x ↦ KanComplex (SimplicialNerve.vertexEquiv CatInftyΔ.{u} x).obj.toSSet).obj n)
    (k : SimplicialThickening (ULift.{u} (Fin (n.unop.len + 1)))) :
    KanComplex (G.1.obj k).obj.toSSet := by
  have h := (mem_fullEnhancedSubcategory_obj_iff _ _).1 G.2
    (SimplexCategory.const ⦋0⦌ n.unop k.as.down)
  rw [SimplicialNerve.vertexEquiv_apply] at h
  exact h

/-- View an `n`-simplex of `Cat∞` whose vertices are Kan complexes as an `n`-simplex of `Spaces`. -/
private noncomputable def spacesOfCatInftySimplex {n : SimplexCategoryᵒᵖ}
    (F : EnrichedFunctor SSet (SimplicialThickening (ULift.{u} (Fin (n.unop.len + 1))))
      CatInftyΔ.{u})
    (hF : ∀ k, KanComplex (F.obj k).obj.toSSet) :
    EnrichedFunctor SSet (SimplicialThickening (ULift.{u} (Fin (n.unop.len + 1))))
      SpacesΔ.{u} where
  obj k := ⟨(F.obj k).obj.toSSet, hF k⟩
  map i j := F.map i j ≫ (sHom (F.obj i).obj.toSSet (F.obj j).obj.toSSet).core.ι
  map_id i := by
    rw [← Category.assoc, F.map_id]
    exact CoreEnriched.eId_ι (F.obj i).obj
  map_comp i j k := by
    rw [← Category.assoc, F.map_comp, Category.assoc]
    change _ ≫ eComp SSet (F.obj i).obj (F.obj j).obj (F.obj k).obj ≫ Subcomplex.ι _ = _
    rw [CoreEnriched.eComp_ι, tensorHom_comp_tensorHom_assoc]
    rfl

/-- The quasicategory `Spaces` of small Kan complexes is isomorphic to the full enhanced
subcategory of `Cat∞` spanned by the Kan complexes. -/
noncomputable def spacesIsoFullSubcategory :
    spaces.{u} ≅
      (catInfty.{u}.fullEnhancedSubcategory
        fun x ↦ KanComplex (SimplicialNerve.vertexEquiv CatInftyΔ.{u} x).obj.toSSet :
          SSet.{u + 1}) where
  hom := Subcomplex.lift spacesToCatInfty <| by
    rw [range_le_fullEnhancedSubcategory_iff]
    intro x
    rw [vertexEquiv_spacesToCatInfty_app]
    exact (SimplicialNerve.vertexEquiv SpacesΔ.{u} x).property
  inv :=
    { app n := ↾fun G ↦ spacesOfCatInftySimplex G.1 (kanComplex_of_mem_spacesSubcomplex G)
      naturality m n f := by
        ext G
        refine EnrichedFunctor.ext SSet (fun _ ↦ rfl) fun i j ↦ ?_
        exact Category.assoc _ _ _ }
  hom_inv_id := by
    ext n G
    let G' : EnrichedFunctor SSet (SimplicialThickening (ULift.{u} (Fin (n.unop.len + 1))))
      SpacesΔ.{u} := G
    have hG : spacesToCatInfty.app n G' = EnrichedFunctor.comp SSet G' SpacesΔ.toCatInftyΔ :=
      simplicialNerveMap_app _ _ _
    change spacesOfCatInftySimplex (spacesToCatInfty.app n G') _ = G'
    have key : ∀ (F : EnrichedFunctor SSet
        (SimplicialThickening (ULift.{u} (Fin (n.unop.len + 1)))) CatInftyΔ.{u})
        (hF : ∀ k, KanComplex (F.obj k).obj.toSSet),
        F = EnrichedFunctor.comp SSet G' SpacesΔ.toCatInftyΔ →
        spacesOfCatInftySimplex F hF = G' := by
      rintro _ hF rfl
      refine EnrichedFunctor.ext SSet (fun _ ↦ rfl) fun i j ↦ ?_
      change (G'.map i j ≫ SpacesΔ.toCatInftyΔ.map (G'.obj i) (G'.obj j)) ≫
        (sHom (G'.obj i).obj (G'.obj j).obj).core.ι = G'.map i j
      dsimp only [SpacesΔ.toCatInftyΔ]
      rw [Category.assoc, Subcomplex.lift_ι]
      exact Category.comp_id _
    exact key _ _ hG
  inv_hom_id := by
    ext n G
    refine Subtype.ext ?_
    let F : EnrichedFunctor SSet (SimplicialThickening (ULift.{u} (Fin (n.unop.len + 1))))
      CatInftyΔ.{u} := G.1
    refine (simplicialNerveMap_app SpacesΔ.toCatInftyΔ n
      (spacesOfCatInftySimplex F (kanComplex_of_mem_spacesSubcomplex G))).trans ?_
    refine EnrichedFunctor.ext SSet (fun _ ↦ rfl) fun i j ↦ ?_
    refine (cancel_mono (sHom (F.obj i).obj.toSSet (F.obj j).obj.toSSet).core.ι).1 ?_
    change ((F.map i j ≫ (sHom (F.obj i).obj.toSSet (F.obj j).obj.toSSet).core.ι) ≫
      SpacesΔ.toCatInftyΔ.map ⟨(F.obj i).obj.toSSet, kanComplex_of_mem_spacesSubcomplex G i⟩
        ⟨(F.obj j).obj.toSSet, kanComplex_of_mem_spacesSubcomplex G j⟩) ≫
      (sHom (F.obj i).obj.toSSet (F.obj j).obj.toSSet).core.ι =
      F.map i j ≫ (sHom (F.obj i).obj.toSSet (F.obj j).obj.toSSet).core.ι
    dsimp only [SpacesΔ.toCatInftyΔ]
    rw [Category.assoc, Subcomplex.lift_ι, Category.comp_id]

/-- Under `spacesIsoFullSubcategory`, the full enhanced subcategory inclusion corresponds to
`spacesToCatInfty`. -/
@[reassoc (attr := simp)]
lemma spacesIsoFullSubcategory_hom_ι :
    spacesIsoFullSubcategory.{u}.hom ≫ Subcomplex.ι _ = spacesToCatInfty.{u} :=
  (rfl)

/-- The inclusion `Spaces ⟶ Cat∞` is a monomorphism of simplicial sets. -/
instance mono_spacesToCatInfty : Mono spacesToCatInfty.{u} := by
  rw [← spacesIsoFullSubcategory_hom_ι]
  exact mono_comp _ _

/-- The inclusion `Spaces ⟶ Cat∞` is an inner fibration. -/
instance innerFibration_spacesToCatInfty : InnerFibration spacesToCatInfty.{u} :=
  ⟨by
    rw [← spacesIsoFullSubcategory_hom_ι]
    exact innerFibrations.comp_mem _ _ (innerFibrations.of_isIso _) InnerFibration.mem⟩

/-- The inclusion `Spaces ⟶ Cat∞` induces isomorphisms on all right mapping spaces. -/
instance isIso_rightMappingSpace_map_spacesToCatInfty (x y : spaces.{u} _⦋0⦌) :
    IsIso (rightMappingSpace.map x y spacesToCatInfty) := by
  rw [← spacesIsoFullSubcategory_hom_ι, rightMappingSpace.map_comp]
  exact inferInstance

end SSet
