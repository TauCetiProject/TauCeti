/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Quasicategory.CatInfty
public import TauCeti.AlgebraicTopology.Quasicategory.FullyFaithful
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
monomorphism, an inner fibration, and fully faithful (inducing isomorphisms on all right mapping
spaces).

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
* `SSet.SpacesΔ.toCatInftyΔ_obj_obj`, `SSet.SpacesΔ.toCatInftyΔ_obj_toSSet`,
  `SSet.SpacesΔ.toCatInftyΔ_map_ι`, `SSet.SpacesΔ.ι_toCatInftyΔ_map`,
  `SSet.SpacesΔ.isIso_toCatInftyΔ_map`: projection and invertibility properties of
  `SSet.SpacesΔ.toCatInftyΔ`.
* `SSet.spacesToCatInfty_app`, `SSet.vertexEquiv_spacesToCatInfty_app`: action of
  `SSet.spacesToCatInfty` on simplices and vertices.
* `SSet.spacesIsoFullSubcategory_hom_ι`: the isomorphism `SSet.spacesIsoFullSubcategory`
  intertwines the full enhanced subcategory inclusion with `SSet.spacesToCatInfty`.
* `SSet.mono_spacesToCatInfty`, `SSet.innerFibration_spacesToCatInfty`,
  `SSet.isIso_rightMappingSpace_map_spacesToCatInfty`, `SSet.isFullyFaithful_spacesToCatInfty`:
  `SSet.spacesToCatInfty` is a monomorphism, an inner fibration, and fully faithful.

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
noncomputable def toCatInftyΔ : EnrichedFunctor SSet.{u} SpacesΔ.{u} CatInftyΔ.{u} where
  obj A := ⟨CoreEnriched.of A.obj, have := A.property; inferInstance⟩
  map A B := Subcomplex.lift (𝟙 (sHom A.obj B.obj)) (by
    have := B.property
    rw [core_sHom_eq_top]
    exact le_top)
  map_id A := by
    rw [← cancel_mono (Subcomplex.ι _), Category.assoc, Subcomplex.lift_ι,
      ObjectProperty.FullSubcategory.eId_eq, ObjectProperty.FullSubcategory.eId_eq,
      CoreEnriched.eId_ι]
    exact Category.comp_id _
  map_comp A B C := by
    rw [← cancel_mono (Subcomplex.ι _), Category.assoc, Subcomplex.lift_ι, Category.assoc,
      ObjectProperty.FullSubcategory.eComp_eq, ObjectProperty.FullSubcategory.eComp_eq,
      CoreEnriched.eComp_ι, tensorHom_comp_tensorHom_assoc, Subcomplex.lift_ι, Subcomplex.lift_ι]
    rfl

/-- `SpacesΔ.toCatInftyΔ` sends a Kan complex `A` to `CoreEnriched.of A.obj` in `CatInftyΔ`. -/
@[simp]
lemma toCatInftyΔ_obj_obj (A : SpacesΔ.{u}) :
    (toCatInftyΔ.obj A).obj = CoreEnriched.of A.obj :=
  (rfl)

/-- `SpacesΔ.toCatInftyΔ` preserves underlying simplicial sets on objects. -/
lemma toCatInftyΔ_obj_toSSet (A : SpacesΔ.{u}) :
    (toCatInftyΔ.obj A).obj.toSSet = A.obj :=
  (rfl)

/-- Composing `toCatInftyΔ.map A B` with the core inclusion gives the identity on `Fun(A, B)`, up
to the object identification `toCatInftyΔ_obj_toSSet`. -/
@[reassoc (attr := simp)]
lemma toCatInftyΔ_map_ι (A B : SpacesΔ.{u}) :
    toCatInftyΔ.map A B ≫
        (sHom (toCatInftyΔ.obj A).obj.toSSet (toCatInftyΔ.obj B).obj.toSSet).core.ι =
      eqToHom (by rw [toCatInftyΔ_obj_toSSet, toCatInftyΔ_obj_toSSet]; exact (rfl)) := by
  dsimp only [toCatInftyΔ]
  change Subcomplex.lift (𝟙 (sHom A.obj B.obj)) _ ≫ _ = _
  rw [Subcomplex.lift_ι]
  exact (eqToHom_refl _ _).symm

/-- Composing the core inclusion with `toCatInftyΔ.map A B` gives the identity on `Fun(A, B)^≃`. -/
@[reassoc (attr := simp)]
lemma ι_toCatInftyΔ_map (A B : SpacesΔ.{u}) :
    (sHom (toCatInftyΔ.obj A).obj.toSSet (toCatInftyΔ.obj B).obj.toSSet).core.ι ≫
        eqToHom (by rw [toCatInftyΔ_obj_toSSet, toCatInftyΔ_obj_toSSet]; exact (rfl)) ≫
          toCatInftyΔ.map A B =
      𝟙 ((sHom (toCatInftyΔ.obj A).obj.toSSet (toCatInftyΔ.obj B).obj.toSSet).core : SSet.{u}) := by
  rw [← cancel_mono (Subcomplex.ι _)]
  simp

/-- The simplicial functor `SpacesΔ.toCatInftyΔ` induces isomorphisms on all mapping simplicial
sets. -/
instance isIso_toCatInftyΔ_map (A B : SpacesΔ.{u}) : IsIso (toCatInftyΔ.map A B) :=
  ⟨⟨(sHom (toCatInftyΔ.obj A).obj.toSSet (toCatInftyΔ.obj B).obj.toSSet).core.ι ≫
      eqToHom (by rw [toCatInftyΔ_obj_toSSet, toCatInftyΔ_obj_toSSet]; exact (rfl)),
    by simp, by exact (ι_toCatInftyΔ_map A B).trans rfl⟩⟩

end SpacesΔ

/-- **HTT Proposition 1.1.5.10**: the simplicial nerve `Spaces` of small Kan complexes is a
quasicategory, as `SpacesΔ` is locally Kan. -/
instance spaces.quasicategory : Quasicategory spaces.{u} :=
  CategoryTheory.SimplicialNerve.quasicategory SpacesΔ.{u}

/-- The canonical map of quasicategories from `Spaces` to `Cat∞`, induced on simplicial nerves by
`SpacesΔ.toCatInftyΔ`. -/
noncomputable def spacesToCatInfty : spaces.{u} ⟶ catInfty.{u} :=
  simplicialNerveMap SpacesΔ.toCatInftyΔ

/-- On arbitrary simplices, `spacesToCatInfty` acts by postcomposition with
`SpacesΔ.toCatInftyΔ`. -/
@[simp]
lemma spacesToCatInfty_app (n : SimplexCategoryᵒᵖ) (G : spaces.{u}.obj n) :
    spacesToCatInfty.app n G = EnrichedFunctor.comp SSet G SpacesΔ.toCatInftyΔ :=
  simplicialNerveMap_app _ _ _

/-- On vertices, `spacesToCatInfty` preserves the underlying simplicial set. -/
@[simp↓]
lemma vertexEquiv_spacesToCatInfty_app (x : spaces.{u} _⦋0⦌) :
    (SimplicialNerve.vertexEquiv CatInftyΔ.{u} (spacesToCatInfty.app (op ⦋0⦌) x)).obj.toSSet =
      (SimplicialNerve.vertexEquiv SpacesΔ.{u} x).obj := by
  rw [SimplicialNerve.vertexEquiv_apply, SimplicialNerve.vertexEquiv_apply,
    spacesToCatInfty_app]
  dsimp only [EnrichedFunctor.comp]
  exact SpacesΔ.toCatInftyΔ_obj_toSSet _

/-- Every vertex of a simplex in the full enhanced subcategory of `Cat∞` on Kan complexes has a
Kan complex as its underlying simplicial set. -/
private lemma kanComplex_of_mem_spacesSubcomplex {n : SimplexCategoryᵒᵖ}
    (G : (catInfty.{u}.fullEnhancedSubcategory
      fun x ↦ KanComplex (SimplicialNerve.vertexEquiv CatInftyΔ.{u} x).obj.toSSet).obj n)
    (k : SimplicialThickening (ULift.{u} (Fin (n.unop.len + 1)))) :
    KanComplex (G.val.obj k).obj.toSSet := by
  have h := (mem_fullEnhancedSubcategory_obj_iff _ _).1 G.property
    (SimplexCategory.const ⦋0⦌ n.unop k.as.down)
  rw [SimplicialNerve.vertexEquiv_apply, SimplicialNerve.map_apply_obj] at h
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
    rw [← Category.assoc, F.map_id, ObjectProperty.FullSubcategory.eId_eq,
      ObjectProperty.FullSubcategory.eId_eq, CoreEnriched.eId_ι]
  map_comp i j k := by
    rw [← Category.assoc, F.map_comp]
    simp only [Category.assoc, ObjectProperty.FullSubcategory.eComp_eq]
    rw [CoreEnriched.eComp_ι, tensorHom_comp_tensorHom_assoc]

/-- Postcomposing with `SpacesΔ.toCatInftyΔ` and viewing back in `SpacesΔ` recovers the original
enriched functor. -/
private lemma spacesOfCatInftySimplex_comp_toCatInftyΔ {n : SimplexCategoryᵒᵖ}
    {F : EnrichedFunctor SSet (SimplicialThickening (ULift.{u} (Fin (n.unop.len + 1))))
      CatInftyΔ.{u}}
    {G : EnrichedFunctor SSet (SimplicialThickening (ULift.{u} (Fin (n.unop.len + 1))))
      SpacesΔ.{u}}
    (hF : ∀ k, KanComplex (F.obj k).obj.toSSet)
    (hFG : F = G.comp SSet SpacesΔ.toCatInftyΔ) :
    spacesOfCatInftySimplex F hF = G := by
  subst hFG
  have h_obj : ∀ k, (spacesOfCatInftySimplex (G.comp SSet SpacesΔ.toCatInftyΔ) hF).obj k =
      G.obj k := fun k ↦ ObjectProperty.FullSubcategory.ext (SpacesΔ.toCatInftyΔ_obj_toSSet _)
  refine EnrichedFunctor.ext SSet h_obj fun i j ↦ ?_
  have hmap : (spacesOfCatInftySimplex (G.comp SSet SpacesΔ.toCatInftyΔ) hF).map i j =
      G.map i j ≫ eqToHom (by rw [h_obj, h_obj]) :=
    (Category.assoc _ _ _).trans (congrArg (G.map i j ≫ ·) (SpacesΔ.toCatInftyΔ_map_ι _ _))
  rw [hmap, Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]

/-- Viewing an enriched functor into `CatInftyΔ` with Kan vertices in `SpacesΔ` and
postcomposing with `SpacesΔ.toCatInftyΔ` recovers the original enriched functor. -/
private lemma spacesOfCatInftySimplex_comp {n : SimplexCategoryᵒᵖ}
    (F : EnrichedFunctor SSet (SimplicialThickening (ULift.{u} (Fin (n.unop.len + 1))))
      CatInftyΔ.{u})
    (hF : ∀ k, KanComplex (F.obj k).obj.toSSet) :
    (spacesOfCatInftySimplex F hF).comp SSet SpacesΔ.toCatInftyΔ = F := by
  have h_obj : ∀ k, ((spacesOfCatInftySimplex F hF).comp SSet SpacesΔ.toCatInftyΔ).obj k =
      F.obj k := fun k ↦ ObjectProperty.FullSubcategory.ext (SpacesΔ.toCatInftyΔ_obj_obj _)
  refine EnrichedFunctor.ext SSet h_obj fun i j ↦ ?_
  have hι : ∀ {U V : CatInftyΔ.{u}}, U = F.obj i → V = F.obj j →
      ∀ (hHom : (U ⟶[SSet] V) = (F.obj i ⟶[SSet] F.obj j))
        (hSSet : sHom U.obj.toSSet V.obj.toSSet = sHom (F.obj i).obj.toSSet (F.obj j).obj.toSSet),
      eqToHom hHom ≫ (sHom (F.obj i).obj.toSSet (F.obj j).obj.toSSet).core.ι =
        (sHom U.obj.toSSet V.obj.toSSet).core.ι ≫ eqToHom hSSet := by
    rintro U V rfl rfl hHom hSSet
    simp
  let C := (spacesOfCatInftySimplex F hF).comp SSet SpacesΔ.toCatInftyΔ
  have hcomp :
      C.map i j ≫ (sHom (C.obj i).obj.toSSet (C.obj j).obj.toSSet).core.ι =
      F.map i j ≫ (sHom (F.obj i).obj.toSSet (F.obj j).obj.toSSet).core.ι ≫
        eqToHom (by rw [EnrichedFunctor.comp_obj, SpacesΔ.toCatInftyΔ_obj_toSSet,
          EnrichedFunctor.comp_obj, SpacesΔ.toCatInftyΔ_obj_toSSet]; exact (rfl)) :=
    (Category.assoc _ _ _).trans (congrArg (_ ≫ ·) (SpacesΔ.toCatInftyΔ_map_ι _ _))
  rw [← cancel_mono (sHom (F.obj i).obj.toSSet (F.obj j).obj.toSSet).core.ι, Category.assoc,
    hι (h_obj i) (h_obj j) _
      (by rw [EnrichedFunctor.comp_obj, SpacesΔ.toCatInftyΔ_obj_toSSet,
          EnrichedFunctor.comp_obj, SpacesΔ.toCatInftyΔ_obj_toSSet]; exact (rfl)),
    ← Category.assoc, hcomp, Category.assoc, Category.assoc, eqToHom_trans, eqToHom_refl,
    Category.comp_id]

/-- Every vertex in the image of `spacesToCatInfty` is a Kan complex. -/
private lemma range_spacesToCatInfty_le :
    Subcomplex.range spacesToCatInfty.{u} ≤
      catInfty.{u}.fullEnhancedSubcategory
        fun x ↦ KanComplex (SimplicialNerve.vertexEquiv CatInftyΔ.{u} x).obj.toSSet := by
  rw [range_le_fullEnhancedSubcategory_iff]
  intro x
  rw [vertexEquiv_spacesToCatInfty_app]
  exact (SimplicialNerve.vertexEquiv SpacesΔ.{u} x).property

/-- The quasicategory `Spaces` of small Kan complexes is isomorphic to the full enhanced
subcategory of `Cat∞` spanned by the Kan complexes. -/
noncomputable def spacesIsoFullSubcategory :
    spaces.{u} ≅
      (catInfty.{u}.fullEnhancedSubcategory
        fun x ↦ KanComplex (SimplicialNerve.vertexEquiv CatInftyΔ.{u} x).obj.toSSet :
          SSet.{u + 1}) where
  hom := Subcomplex.lift spacesToCatInfty range_spacesToCatInfty_le
  inv :=
    { app n := ↾fun G ↦ spacesOfCatInftySimplex G.val (kanComplex_of_mem_spacesSubcomplex G)
      naturality m n f := by
        ext G
        have hcat : ((catInfty.{u}.fullEnhancedSubcategory _).toFunctor.map f G).val =
            (SimplicialThickening.functor f.unop.toOrderHom.uliftMap).comp SSet G.val := by
          rw [Subfunctor.toFunctor_map]
          exact SimplicialNerve.map_apply _ f G.val
        have hsp : spaces.{u}.map f (spacesOfCatInftySimplex G.val
            (kanComplex_of_mem_spacesSubcomplex G)) =
            (SimplicialThickening.functor f.unop.toOrderHom.uliftMap).comp SSet
              (spacesOfCatInftySimplex G.val (kanComplex_of_mem_spacesSubcomplex G)) :=
          SimplicialNerve.map_apply _ f _
        have hcongr : ∀ {G₀ : EnrichedFunctor SSet
            (SimplicialThickening (ULift.{u} (Fin (m.unop.len + 1)))) CatInftyΔ.{u}}
            {F' : EnrichedFunctor SSet
            (SimplicialThickening (ULift.{u} (Fin (n.unop.len + 1)))) CatInftyΔ.{u}},
            F' = (SimplicialThickening.functor f.unop.toOrderHom.uliftMap).comp SSet G₀ →
            ∀ (hG₀ : ∀ k, KanComplex (G₀.obj k).obj.toSSet)
              (h₁ : ∀ k, KanComplex (F'.obj k).obj.toSSet),
            spacesOfCatInftySimplex F' h₁ =
              (SimplicialThickening.functor f.unop.toOrderHom.uliftMap).comp SSet
                (spacesOfCatInftySimplex G₀ hG₀) := by
          rintro G₀ _ rfl hG₀ h₁
          have hobj : ∀ k,
              (spacesOfCatInftySimplex
                ((SimplicialThickening.functor f.unop.toOrderHom.uliftMap).comp SSet G₀) h₁).obj
                  k =
                ((SimplicialThickening.functor f.unop.toOrderHom.uliftMap).comp SSet
                  (spacesOfCatInftySimplex G₀ hG₀)).obj k := fun _ ↦ rfl
          refine EnrichedFunctor.ext SSet hobj fun _ _ ↦ ?_
          exact (congrArg (_ ≫ ·) (eqToHom_refl _ _)).trans
            ((Category.comp_id _).trans (Category.assoc _ _ _))
        exact (hcongr hcat (kanComplex_of_mem_spacesSubcomplex G) _).trans hsp.symm }
  hom_inv_id := by
    ext n G
    exact spacesOfCatInftySimplex_comp_toCatInftyΔ _
      ((Subcomplex.lift_app_coe _ _ _).trans (spacesToCatInfty_app n G))
  inv_hom_id := by
    ext n G
    refine Subtype.ext ?_
    exact ((Subcomplex.lift_app_coe spacesToCatInfty range_spacesToCatInfty_le
      (spacesOfCatInftySimplex G.val (kanComplex_of_mem_spacesSubcomplex G))).trans
      (spacesToCatInfty_app n _)).trans (spacesOfCatInftySimplex_comp G.val _)

/-- Under `spacesIsoFullSubcategory`, the full enhanced subcategory inclusion corresponds to
`spacesToCatInfty`. -/
@[reassoc (attr := simp)]
lemma spacesIsoFullSubcategory_hom_ι :
    spacesIsoFullSubcategory.{u}.hom ≫ Subcomplex.ι _ = spacesToCatInfty.{u} :=
  Subcomplex.lift_ι spacesToCatInfty range_spacesToCatInfty_le

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

/-- The inclusion `Spaces ⟶ Cat∞` is fully faithful. -/
instance isFullyFaithful_spacesToCatInfty : IsFullyFaithful spacesToCatInfty.{u} :=
  IsFullyFaithful.of_isIso_map _ inferInstance

end SSet
