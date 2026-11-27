/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Quasicategory.CategoricalEquivalence
public import TauCeti.AlgebraicTopology.Quasicategory.FullyFaithful
public import TauCeti.AlgebraicTopology.SimplicialSet.InternalHom
public import TauCeti.CategoryTheory.Localization.Predicate

/-!
# Localizations of simplicial sets at sets of edges

Let `C` be a simplicial set and `W` a set of edges of `C`. For a quasicategory `E`, the maps
`C ⟶ E` sending every edge of `W` to an equivalence span a full subquasicategory
`SSet.functorsInverting W E` of the functor quasicategory `Fun(C, E)`. A map `f : C ⟶ D` sending
`W` to isomorphisms of `ho D` is a *localization of `C` at `W`* (`SSet.IsLocalization f W`) when,
for every quasicategory `E`, precomposition with `f` is a categorical equivalence from `Fun(D, E)`
to `SSet.functorsInverting W E`. This is the functor-space universal property of the
`∞`-categorical localization `C[W⁻¹]`: sending `W` to isomorphisms of `ho D` is exactly what makes
every composite `C ⟶ D ⟶ E` with a quasicategory `E` send `W` to equivalences (test on
`E = N (ho D)`), and for a quasicategory `D` it means sending `W` to equivalences of `D`.

A localization induces a localization of homotopy categories
`ho C ⥤ ho D` at the classes of the edges of `W`, in the sense of Mathlib's
`CategoryTheory.Functor.IsLocalization`. To see this, the universal property is tested against the
nerves `E = N A` of categories: the comparison `ho Fun(X, N A) ⥤ (ho X ⥤ ho (N A))` is an
equivalence (`SSet.isEquivalence_ihomHoFunctor_nerve`), so the categorical equivalence
`Fun(D, N A) ⟶ SSet.functorsInverting W (N A)` says that precomposition with `ho f` reflects
isomorphisms of functors `ho D ⥤ A` and reaches every functor `ho C ⥤ A` inverting the classes of
`W` up to isomorphism. This recognizes a localization of categories
(`CategoryTheory.Functor.IsLocalization.of_exists_comp_iso_Q`).

## Main declarations

* `SSet.functorsInverting W E`: the full subquasicategory of `Fun(C, E)` on the maps sending every
  edge of `W` to an equivalence.
* `SSet.functorsInverting.precomp`: precomposition with a map `f : C ⟶ D` sending `W` to
  isomorphisms of `ho D`, as a map `Fun(D, E) ⟶ SSet.functorsInverting W E`.
* `SSet.IsLocalization f W`: `f` is a localization of `C` at `W`.
* `SSet.IsLocalization.comp_iff`: the property is invariant under categorical equivalences of
  the target.
* `SSet.IsLocalization.isLocalization_mapHomotopyCategory`: a localization `f` induces a
  localization of homotopy categories `ho C ⥤ ho D` at the classes of the edges of `W`.
* `SSet.isLocalization_id`: the identity of `D` is a localization at any set of edges invertible
  in `ho D`, for instance at the equivalences of a quasicategory.

## References

* J. Lurie, *Higher Algebra*, Definition 1.3.4.1.
* J. Lurie, *Higher Topos Theory*, §1.2.7 (functor `∞`-categories).
-/

public section

universe u

open CategoryTheory MonoidalCategory MonoidalClosed Opposite Simplicial

namespace SSet

variable {C D : SSet.{u}} (W : Set (C _⦋1⦌))

/-- The full subquasicategory of the functor quasicategory `Fun(C, E)` on the maps `C ⟶ E` that
send every edge of `W` to an equivalence. Vertices correspond to maps via `SSet.ihomObj₀Equiv`. -/
def functorsInverting (E : SSet.{u}) : ((ihom C).obj E).Subcomplex :=
  ((ihom C).obj E).fullEnhancedSubcategory fun v ↦
    ∀ w ∈ W, ((Edge.mk' w).map (ihomObj₀Equiv _ _ v)).IsEquivalence

/-- The vertex of `Fun(C, E)` given by a map `g : C ⟶ E` lies in `SSet.functorsInverting W E`
exactly when `g` sends every edge of `W` to an equivalence. -/
@[simp]
lemma ihomObj₀Equiv_symm_mem_functorsInverting_iff {E : SSet.{u}} (g : C ⟶ E) :
    (ihomObj₀Equiv _ _).symm g ∈ (functorsInverting W E).obj (op ⦋0⦌) ↔
      ∀ w ∈ W, ((Edge.mk' w).map g).IsEquivalence := by
  rw [functorsInverting, mem_fullEnhancedSubcategory_obj_zero_iff, Equiv.apply_symm_apply]

/-- A simplex of `Fun(C, E)` lies in `SSet.functorsInverting W E` exactly when each of its vertices
sends every edge of `W` to an equivalence. -/
lemma mem_functorsInverting_obj_iff {E : SSet.{u}} {n : SimplexCategoryᵒᵖ}
    (x : ((ihom C).obj E).obj n) : x ∈ (functorsInverting W E).obj n ↔
      ∀ v : ⦋0⦌ ⟶ n.unop, ∀ w ∈ W, ((Edge.mk' w).map
        (ihomObj₀Equiv _ _ (((ihom C).obj E).map v.op x))).IsEquivalence :=
  mem_fullEnhancedSubcategory_obj_iff _ x

instance (E : SSet.{u}) [Quasicategory E] : Quasicategory (functorsInverting W E : SSet) :=
  inferInstanceAs (Quasicategory (((ihom C).obj E).fullEnhancedSubcategory _ : SSet))

/-- A map sending every edge of `W` to an isomorphism of the homotopy category composes with any
map of simplicial sets to another such map. -/
lemma isIso_homotopyCategoryHomMk_map_comp {f : C ⟶ D}
    (hf : ∀ w ∈ W, IsIso (HomotopyCategory.homMk ((Edge.mk' w).map f))) {E : SSet.{u}} (g : D ⟶ E) :
    ∀ w ∈ W, IsIso (HomotopyCategory.homMk ((Edge.mk' w).map (f ≫ g))) :=
  fun w hw ↦ by
    have := hf w hw
    -- The class of the image of an edge under `g` is the image of its class under `ho g`.
    exact (inferInstance : IsIso ((mapHomotopyCategory g).map
      (HomotopyCategory.homMk ((Edge.mk' w).map f))))

/-- A map sending every edge of `W` to an isomorphism of the homotopy category, followed by a map
to a quasicategory, sends every edge of `W` to an equivalence. -/
lemma isEquivalence_map_comp {f : C ⟶ D}
    (hf : ∀ w ∈ W, IsIso (HomotopyCategory.homMk ((Edge.mk' w).map f))) {E : SSet.{u}}
    [Quasicategory E] (g : D ⟶ E) :
    ∀ w ∈ W, ((Edge.mk' w).map (f ≫ g)).IsEquivalence :=
  fun w hw ↦ (Edge.isEquivalence_iff_isIso_homotopyCategoryHomMk _).2
    (isIso_homotopyCategoryHomMk_map_comp W hf g w hw)

namespace functorsInverting

variable {W}

/-- Precomposition `Fun(D, E) ⟶ Fun(C, E)` with a map `f : C ⟶ D` sending every edge of `W` to an
isomorphism of `ho D`, which lands in `SSet.functorsInverting W E` for a quasicategory `E`. -/
noncomputable def precomp (f : C ⟶ D)
    (hf : ∀ w ∈ W, IsIso (HomotopyCategory.homMk ((Edge.mk' w).map f))) (E : SSet.{u})
    [Quasicategory E] : (ihom D).obj E ⟶ (functorsInverting W E : SSet) :=
  Subcomplex.lift ((pre f).app E) <| (range_le_fullEnhancedSubcategory_iff _ _).2 fun y ↦ by
    obtain ⟨g, rfl⟩ := (ihomObj₀Equiv _ _).symm.surjective y
    rw [pre_app_app_ihomObj₀Equiv_symm, Equiv.apply_symm_apply]
    exact isEquivalence_map_comp W hf g

@[reassoc (attr := simp)]
lemma precomp_ι (f : C ⟶ D) (hf : ∀ w ∈ W, IsIso (HomotopyCategory.homMk ((Edge.mk' w).map f)))
    (E : SSet.{u}) [Quasicategory E] :
    precomp f hf E ≫ (functorsInverting W E).ι = (pre f).app E :=
  (rfl)

/-- Precomposition with `f ≫ g` is precomposition with `g` followed by precomposition with `f`. -/
lemma precomp_comp {D' : SSet.{u}} (f : C ⟶ D)
    (hf : ∀ w ∈ W, IsIso (HomotopyCategory.homMk ((Edge.mk' w).map f))) (g : D ⟶ D') (E : SSet.{u})
    [Quasicategory E] :
    precomp (f ≫ g) (isIso_homotopyCategoryHomMk_map_comp W hf g) E =
      (pre g).app E ≫ precomp f hf E := by
  rw [← cancel_mono (functorsInverting W E).ι, precomp_ι, Category.assoc, precomp_ι, pre_map,
    NatTrans.comp_app]

end functorsInverting

/-- A map `f : C ⟶ D` is a *localization of `C` at the set of edges `W`* when it sends every edge of
`W` to an isomorphism of `ho D` and, for every quasicategory `E`, precomposition with `f` is a
categorical equivalence from the functor quasicategory `Fun(D, E)` to its full subquasicategory
`SSet.functorsInverting W E` on the maps sending `W` to equivalences (HA Definition 1.3.4.1).

The first condition says exactly that every composite of `f` with a map to a quasicategory sends
`W` to equivalences, as it must for precomposition to land in `SSet.functorsInverting W E`; for a
quasicategory `D` it says that `f` sends `W` to equivalences
(`SSet.Edge.isEquivalence_iff_isIso_homotopyCategoryHomMk`). -/
structure IsLocalization (f : C ⟶ D) (W : Set (C _⦋1⦌)) : Prop where
  isIso_homotopyCategoryHomMk_map : ∀ w ∈ W, IsIso (HomotopyCategory.homMk ((Edge.mk' w).map f))
  isCategoricalEquivalence (E : SSet.{u}) [Quasicategory E] :
    QCat.IsCategoricalEquivalence (X := ⟨(ihom D).obj E, inferInstance⟩)
      (Y := ⟨functorsInverting W E, inferInstance⟩)
      (ObjectProperty.homMk (functorsInverting.precomp f isIso_homotopyCategoryHomMk_map E))

namespace IsLocalization

variable {W}

/-- **Invariance under categorical equivalences of the target**: for a categorical equivalence
`g : D ⟶ D'` of quasicategories, `f ≫ g` is a localization of `C` at `W` exactly when `f` is. -/
theorem comp_iff [Quasicategory D] {D' : SSet.{u}} [Quasicategory D'] {f : C ⟶ D} {g : D ⟶ D'}
    (hg : QCat.IsCategoricalEquivalence (X := ⟨D, inferInstance⟩) (Y := ⟨D', inferInstance⟩)
      (ObjectProperty.homMk g)) :
    IsLocalization (f ≫ g) W ↔ IsLocalization f W := by
  -- Precomposition with `f ≫ g` is precomposition with `g`, a categorical equivalence, followed
  -- by precomposition with `f`.
  have key (hf : ∀ w ∈ W, IsIso (HomotopyCategory.homMk ((Edge.mk' w).map f))) (E : SSet.{u})
      [Quasicategory E] :
      (ObjectProperty.homMk (functorsInverting.precomp (f ≫ g)
          (isIso_homotopyCategoryHomMk_map_comp W hf g) E) :
        (⟨(ihom D').obj E, inferInstance⟩ : QCat.{u}) ⟶ ⟨functorsInverting W E, inferInstance⟩) =
      ObjectProperty.homMk (Y := (⟨(ihom D).obj E, inferInstance⟩ : QCat.{u})) ((pre g).app E) ≫
        ObjectProperty.homMk (functorsInverting.precomp f hf E) := by
    ext1
    exact functorsInverting.precomp_comp f hf g E
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · -- The equivalence `ho g` reflects isomorphisms.
    have : (mapHomotopyCategory g).IsEquivalence := hg.isEquivalence_mapHomotopyCategory
    have hf (w) (hw : w ∈ W) : IsIso (HomotopyCategory.homMk ((Edge.mk' w).map f)) := by
      rw [← isIso_iff_of_reflects_iso _ (mapHomotopyCategory g), mapHomotopyCategory_map_homMk]
      exact h.isIso_homotopyCategoryHomMk_map w hw
    exact ⟨hf, fun E _ ↦ (hg.pre_app E).of_comp_left (key hf E ▸ h.isCategoricalEquivalence E)⟩
  · exact ⟨isIso_homotopyCategoryHomMk_map_comp W h.isIso_homotopyCategoryHomMk_map g, fun E _ ↦
      key h.isIso_homotopyCategoryHomMk_map E ▸ (hg.pre_app E).comp (h.isCategoricalEquivalence E)⟩

section HomotopyCategory

variable {f : C ⟶ D} (h : IsLocalization f W) (A : Type u) [Category.{u} A]
include h

/-- Precomposition with `f`, as a functor `ho Fun(D, N A) ⥤ ho Fun(C, N A)`, is the equivalence
onto the homotopy category of `SSet.functorsInverting W (N A)` followed by its inclusion. -/
private lemma mapHomotopyCategory_pre_app_eq :
    mapHomotopyCategory ((pre f).app (nerve A)) =
      mapHomotopyCategory
          (functorsInverting.precomp f h.isIso_homotopyCategoryHomMk_map (nerve A)) ⋙
        mapHomotopyCategory (functorsInverting W (nerve A)).ι := by
  rw [← functorsInverting.precomp_ι f h.isIso_homotopyCategoryHomMk_map]
  exact congrArg Cat.Hom.toFunctor (hoFunctor.map_comp _ _)

/-- Precomposition with `f`, as a functor `ho Fun(D, N A) ⥤ ho Fun(C, N A)`, is fully faithful. -/
private lemma full_faithful_mapHomotopyCategory_pre_app :
    (mapHomotopyCategory ((pre f).app (nerve A))).Full ∧
      (mapHomotopyCategory ((pre f).app (nerve A))).Faithful := by
  have : (mapHomotopyCategory (functorsInverting.precomp f h.isIso_homotopyCategoryHomMk_map
      (nerve A))).IsEquivalence :=
    (h.isCategoricalEquivalence (nerve A)).isEquivalence_mapHomotopyCategory
  have : IsFullyFaithful (functorsInverting W (nerve A)).ι :=
    IsFullyFaithful.fullEnhancedSubcategory_ι _
  rw [mapHomotopyCategory_pre_app_eq h]
  exact ⟨inferInstance, inferInstance⟩

/-- Two functors `ho D ⥤ ho (N A)` are isomorphic as soon as their composites with `ho f` are. -/
private lemma nonempty_iso_of_nonempty_iso_comp
    (F₁ F₂ : D.HomotopyCategory ⥤ (nerve A).HomotopyCategory)
    (α : Nonempty (mapHomotopyCategory f ⋙ F₁ ≅ mapHomotopyCategory f ⋙ F₂)) :
    Nonempty (F₁ ≅ F₂) := by
  obtain ⟨α⟩ := α
  obtain ⟨_, _⟩ := full_faithful_mapHomotopyCategory_pre_app h A
  let ΘC := ihomHoFunctor C (nerve A)
  let ΘD := ihomHoFunctor D (nerve A)
  let M := mapHomotopyCategory ((pre f).app (nerve A))
  let β := eqToIso (ihomHoFunctor_obj_mapHomotopyCategory_pre_app f _) ≪≫
    Functor.isoWhiskerLeft _ (ΘD.objObjPreimageIso F₁) ≪≫ α ≪≫
    Functor.isoWhiskerLeft _ (ΘD.objObjPreimageIso F₂).symm ≪≫
    eqToIso (ihomHoFunctor_obj_mapHomotopyCategory_pre_app f _).symm
  exact ⟨(ΘD.objObjPreimageIso F₁).symm ≪≫ ΘD.mapIso (M.preimageIso (ΘC.preimageIso β)) ≪≫
    ΘD.objObjPreimageIso F₂⟩

/-- Every functor `ho C ⥤ ho (N A)` inverting the classes of `W` is isomorphic to the composite of
`ho f` with a functor `ho D ⥤ ho (N A)`. -/
private lemma exists_nonempty_iso_comp (F : C.HomotopyCategory ⥤ (nerve A).HomotopyCategory)
    (hF : (MorphismProperty.ofHoms fun w : W ↦
      HomotopyCategory.homMk (Edge.mk' (w : C _⦋1⦌))).IsInvertedBy F) :
    ∃ G : D.HomotopyCategory ⥤ (nerve A).HomotopyCategory,
      Nonempty (mapHomotopyCategory f ⋙ G ≅ F) := by
  let P := functorsInverting.precomp f h.isIso_homotopyCategoryHomMk_map (nerve A)
  have : (mapHomotopyCategory P).IsEquivalence :=
    (h.isCategoricalEquivalence (nerve A)).isEquivalence_mapHomotopyCategory
  let ΘC := ihomHoFunctor C (nerve A)
  -- The functor `F` is `ho g` up to isomorphism for a map `g : C ⟶ N A`, which sends `W` to
  -- equivalences since `F` inverts the classes of `W`.
  obtain ⟨v, hv⟩ : ∃ v, ΘC.objPreimage F = HomotopyCategory.mk v :=
    ⟨_, (HomotopyCategory.objEquiv.symm_apply_apply _).symm⟩
  obtain ⟨g, rfl⟩ := (ihomObj₀Equiv _ _).symm.surjective v
  let e : mapHomotopyCategory g ≅ F :=
    eqToIso (by rw [hv, ihomHoFunctor_obj_mk_ihomObj₀Equiv_symm]) ≪≫ ΘC.objObjPreimageIso F
  have hg : (ihomObj₀Equiv _ _).symm g ∈ (functorsInverting W (nerve A)).obj (op ⦋0⦌) := by
    rw [ihomObj₀Equiv_symm_mem_functorsInverting_iff]
    intro w hw
    rw [Edge.isEquivalence_iff_isIso_homotopyCategoryHomMk]
    exact (MorphismProperty.IsInvertedBy.iff_of_iso _ e).2 hF _ (.mk ⟨w, hw⟩)
  -- By essential surjectivity of precomposition with `f` onto `SSet.functorsInverting W (N A)`,
  -- the vertex `g` is isomorphic to the image of a vertex of `Fun(D, N A)`.
  let a := (mapHomotopyCategory P).objPreimage
    (HomotopyCategory.mk (⟨_, hg⟩ : (functorsInverting W (nerve A) : SSet) _⦋0⦌))
  let i : (mapHomotopyCategory ((pre f).app (nerve A))).obj a ≅
      HomotopyCategory.mk ((ihomObj₀Equiv _ _).symm g) :=
    eqToIso (by rw [mapHomotopyCategory_pre_app_eq h]) ≪≫
      (mapHomotopyCategory (functorsInverting W (nerve A)).ι).mapIso
        ((mapHomotopyCategory P).objObjPreimageIso _)
  refine ⟨(ihomHoFunctor D (nerve A)).obj a, ⟨eqToIso ?_ ≪≫ ΘC.mapIso i ≪≫ eqToIso ?_ ≪≫ e⟩⟩
  · exact (ihomHoFunctor_obj_mapHomotopyCategory_pre_app f a).symm
  · rw [ihomHoFunctor_obj_mk_ihomObj₀Equiv_symm]

/-- **The homotopy category of a localization.** If `f : C ⟶ D` is a localization of `C` at `W`,
then the induced functor of homotopy categories `ho C ⥤ ho D` is a localization of categories at
the classes of the edges of `W`. -/
theorem isLocalization_mapHomotopyCategory :
    (mapHomotopyCategory f).IsLocalization
      (MorphismProperty.ofHoms fun w : W ↦ HomotopyCategory.homMk (Edge.mk' (w : C _⦋1⦌))) := by
  set W' := MorphismProperty.ofHoms fun w : W ↦ HomotopyCategory.homMk (Edge.mk' (w : C _⦋1⦌))
  have hL : W'.IsInvertedBy (mapHomotopyCategory f) := by
    rintro _ _ _ ⟨w⟩
    rw [mapHomotopyCategory_map_homMk]
    exact h.isIso_homotopyCategoryHomMk_map w w.property
  refine Functor.IsLocalization.of_exists_comp_iso_Q _ W' hL ?_ fun F₁ F₂ ⟨α⟩ ↦ ?_
  · -- Apply `exists_nonempty_iso_comp` to `W'.Q` followed by the inverse of the counit
    -- equivalence `ho (N W'.Localization) ≌ W'.Localization` (`nerveHomotopyCategoryEquiv`).
    let ε := nerveHomotopyCategoryEquiv W'.Localization
    obtain ⟨G, ⟨e⟩⟩ := exists_nonempty_iso_comp h W'.Localization (W'.Q ⋙ ε.inverse)
      (MorphismProperty.IsInvertedBy.of_comp _ _ W'.Q_inverts _)
    exact ⟨G ⋙ ε.functor, ⟨(Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight e _ ≪≫
      Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ ε.counitIso ≪≫ Functor.rightUnitor _⟩⟩
  · -- Apply `nonempty_iso_of_nonempty_iso_comp` to `F₁` and `F₂` followed by the inverse of the
    -- counit equivalence `ho (N (ho D)) ≌ ho D` (`nerveHomotopyCategoryEquiv`).
    let ε := nerveHomotopyCategoryEquiv D.HomotopyCategory
    obtain ⟨β⟩ := nonempty_iso_of_nonempty_iso_comp h D.HomotopyCategory
      (F₁ ⋙ ε.inverse) (F₂ ⋙ ε.inverse)
      ⟨(Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight α _ ≪≫ Functor.associator _ _ _⟩
    exact ⟨(Functor.rightUnitor _).symm ≪≫ Functor.isoWhiskerLeft _ ε.counitIso.symm ≪≫
      (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight β _ ≪≫ Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ ε.counitIso ≪≫ Functor.rightUnitor _⟩

end HomotopyCategory

end IsLocalization

/-- The identity of a simplicial set `D` is a localization of `D` at any set `W` of edges that are
invertible in `ho D`, for instance at the equivalences of a quasicategory `D`
(`SSet.Edge.IsEquivalence.isIso_homotopyCategoryHomMk`). -/
theorem isLocalization_id (W : Set (D _⦋1⦌))
    (hW : ∀ w ∈ W, IsIso (HomotopyCategory.homMk (Edge.mk' w))) :
    IsLocalization (𝟙 D) W := by
  -- The image of an edge under the identity is that edge, by definition.
  have hid : ∀ w ∈ W, IsIso (HomotopyCategory.homMk ((Edge.mk' w).map (𝟙 D))) := hW
  refine ⟨hid, fun E _ ↦ ?_⟩
  -- Every map out of `D` to a quasicategory sends `W` to equivalences (the edges `(𝟙 D ≫ g)(w)`
  -- and `g(w)` agree by definition), so the full subquasicategory is all of `Fun(D, E)` and
  -- precomposition with the identity is an isomorphism onto it.
  have htop : functorsInverting W E = ⊤ :=
    top_le_iff.1 ((le_fullEnhancedSubcategory_iff _ _).2 fun x _ w hw ↦
      (Edge.isEquivalence_iff_of_edge_eq rfl).1
        (isEquivalence_map_comp W hid (ihomObj₀Equiv _ _ x) w hw))
  have : IsIso (functorsInverting.precomp (𝟙 D) hid E) := by
    have : IsIso (functorsInverting W E).ι := by
      rw [htop]
      exact (Subcomplex.topIso _).isIso_hom
    have : IsIso (functorsInverting.precomp (𝟙 D) hid E ≫ (functorsInverting W E).ι) := by
      rw [functorsInverting.precomp_ι, pre_id, NatTrans.id_app]
      infer_instance
    exact IsIso.of_isIso_comp_right _ (functorsInverting _ E).ι
  exact @QCat.IsCategoricalEquivalence.of_isIso ⟨_, inferInstance⟩ ⟨_, inferInstance⟩ _
    ⟨ObjectProperty.homMk (inv (functorsInverting.precomp (𝟙 D) hid E)), by ext1; simp,
      by ext1; simp⟩

end SSet
