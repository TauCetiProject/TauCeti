/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Sheaves.SupportedCohomology.Module
public import TauCeti.Topology.Sheaves.LocalCohomology.Basic
import TauCeti.CategoryTheory.Sites.Limits
import TauCeti.Topology.Sheaves.Flasque.Locality

/-!
# The sheaf of supported sections of a sheaf of modules

For a closed subset `S`, the modules `Γ_S(W, F)` form a sheaf of modules, not merely a
presheaf. This file constructs this sheaf and its functorial inclusion into `F`, together
with the factorization property of that inclusion. Forgetting scalars identifies it with
`CategoryTheory.Sheaf.supportedSectionsSheaf` of the underlying abelian sheaf.
The comparison is natural
in `F` and respects the inclusion, so abelian supported-section constructions can be used
without discarding the module structure. In particular, the supported-section functor is
additive and left exact.

The supported-section sheaf of a flasque sheaf is flasque. In degree zero the supported
cohomology presheaf is naturally isomorphic to this sheaf; in particular it already
satisfies the sheaf condition. These are the degree-zero inputs for resolutions computing
module-valued local cohomology.

## References

* A. Grothendieck, *Local cohomology*, Lecture Notes in Mathematics 41, §1.
* M. Kashiwara and P. Schapira, *Sheaves on Manifolds*, §2.3 and §2.6.
-/

public section

open CategoryTheory Limits Opposite TopologicalSpace

universe u

namespace CategoryTheory.Sheaf

variable {X : TopCat.{u}} {R : Type u} [CommRing R]
  (F : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)) (S : Closeds X)

noncomputable section

/-- The presheaf of `R`-modules of sections supported in `S`, with the restriction maps of `F`. -/
@[expose]
def supportedSubmodulePresheaf : TopCat.Presheaf (ModuleCat.{u} R) X where
  obj W := ModuleCat.of R (F.supportedSubmodule S W.unop)
  map f := ModuleCat.ofHom <|
    ((F.obj.map f).hom.comp (F.supportedSubmodule S _).subtype).codRestrict _
      fun s ↦ F.map_mem_supportedSubmodule_of_le (leOfHom f.unop) s.2
  map_id W := by
    ext s
    exact congr($(F.obj.map_id W) s.1)
  map_comp f g := by
    ext s
    exact congr($(F.obj.map_comp f g) s.1)

@[simp]
lemma supportedSubmodulePresheaf_obj (W : (Opens X)ᵒᵖ) :
    (F.supportedSubmodulePresheaf S).obj W = ModuleCat.of R (F.supportedSubmodule S W.unop) :=
  (rfl)

@[simp]
lemma coe_supportedSubmodulePresheaf_map_apply {W W' : (Opens X)ᵒᵖ} (f : W ⟶ W')
    (s : F.supportedSubmodule S W.unop) :
    Subtype.val (p := (· ∈ F.supportedSubmodule S W'.unop))
      ((F.supportedSubmodulePresheaf S).map f s) = F.obj.map f s :=
  (rfl)

/-- Forgetting scalars in the supported-section presheaf gives the supported-section
presheaf of the underlying abelian sheaf. -/
private def supportedSubmodulePresheafForgetIso :
    F.supportedSubmodulePresheaf S ⋙ forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u} ≅
      supportedSectionsPresheaf
        ((sheafCompose _ (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})).obj F) S :=
  NatIso.ofComponents (fun _ ↦ AddEquiv.toAddCommGrpIso
    { toFun s := ⟨s.1, (mem_supportedSections_iff _).2
        ((F.mem_supportedSubmodule_iff).1 s.2)⟩
      invFun s := ⟨s.1, (F.mem_supportedSubmodule_iff).2
        ((mem_supportedSections_iff _).1 s.2)⟩
      left_inv _ := rfl
      right_inv _ := rfl
      map_add' _ _ := rfl }) (fun _ ↦ rfl)

/-- Sections supported in a closed subset form a sheaf of `R`-modules. -/
theorem isSheaf_supportedSubmodulePresheaf : (F.supportedSubmodulePresheaf S).IsSheaf :=
  (TopCat.Presheaf.isSheaf_iff_isSheaf_comp
    (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}) _).2 <|
      (Presheaf.isSheaf_of_iso_iff (F.supportedSubmodulePresheafForgetIso S)).2
        (isSheaf_supportedSectionsPresheaf
          ((sheafCompose _ (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})).obj F) S)

/-- The sheaf `Γ_S(F)` of `R`-module sections supported in `S`. -/
@[expose]
def supportedSubmoduleSheaf : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R) :=
  ⟨F.supportedSubmodulePresheaf S, F.isSheaf_supportedSubmodulePresheaf S⟩

@[simp]
lemma supportedSubmoduleSheaf_obj :
    (F.supportedSubmoduleSheaf S).obj = F.supportedSubmodulePresheaf S :=
  (rfl)

/-- The inclusion of the supported-section sheaf into its ambient sheaf. -/
def supportedSubmoduleι : F.supportedSubmoduleSheaf S ⟶ F :=
  ObjectProperty.homMk
    { app W := ModuleCat.ofHom (F.supportedSubmodule S W.unop).subtype
      naturality _ _ _ := rfl }

@[simp]
lemma supportedSubmoduleι_hom_app_apply (W : (Opens X)ᵒᵖ)
    (s : F.supportedSubmodule S W.unop) : (F.supportedSubmoduleι S).hom.app W s = s :=
  (rfl)

@[simp]
lemma range_supportedSubmoduleι_hom_app (W : (Opens X)ᵒᵖ) :
    ((F.supportedSubmoduleι S).hom.app W).hom.range = F.supportedSubmodule S W.unop :=
  (F.supportedSubmodule S W.unop).range_subtype

/-- The supported-section inclusion is a monomorphism. -/
instance mono_supportedSubmoduleι : Mono (F.supportedSubmoduleι S) := by
  have (W : (Opens X)ᵒᵖ) : Mono ((F.supportedSubmoduleι S).hom.app W) :=
    (ModuleCat.mono_iff_injective _).2 Subtype.val_injective
  have : Mono (F.supportedSubmoduleι S).hom := NatTrans.mono_of_mono_app _
  exact Sheaf.Hom.mono_of_presheaf_mono _ _ _

variable {F S} in
/-- A morphism into `F` whose sections are supported in `S` factors through `Γ_S(F)`. -/
def supportedSubmoduleLift {G : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)}
    (φ : G ⟶ F) (h : ∀ W s, φ.hom.app W s ∈ F.supportedSubmodule S W.unop) :
    G ⟶ F.supportedSubmoduleSheaf S :=
  ObjectProperty.homMk
    { app W := ModuleCat.ofHom ((φ.hom.app W).hom.codRestrict _ (h W))
      naturality _ _ f := by
        ext s
        exact Subtype.ext congr($(φ.hom.naturality f) s) }

variable {F S} in
@[reassoc (attr := simp)]
lemma supportedSubmoduleLift_ι {G : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)}
    (φ : G ⟶ F) (h : ∀ W s, φ.hom.app W s ∈ F.supportedSubmodule S W.unop) :
    supportedSubmoduleLift φ h ≫ F.supportedSubmoduleι S = φ := by
  ext
  rfl

/-- Forgetting scalars identifies the supported-section sheaf with the abelian one. -/
def supportedSubmoduleSheafForgetIso :
    (sheafCompose _ (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})).obj
        (F.supportedSubmoduleSheaf S) ≅
      supportedSectionsSheaf
        ((sheafCompose _ (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})).obj F) S :=
  ⟨ObjectProperty.homMk (F.supportedSubmodulePresheafForgetIso S).hom,
    ObjectProperty.homMk (F.supportedSubmodulePresheafForgetIso S).inv,
    by ext; rfl, by ext; rfl⟩

@[simp]
lemma coe_supportedSubmoduleSheafForgetIso_hom_app_apply (W : (Opens X)ᵒᵖ)
    (s : F.supportedSubmodule S W.unop) :
    Subtype.val (p := (· ∈ supportedSections
      ((sheafCompose _ (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})).obj F) S W.unop))
      ((F.supportedSubmoduleSheafForgetIso S).hom.hom.app W s) = s.1 :=
  (rfl)

@[simp]
lemma coe_supportedSubmoduleSheafForgetIso_inv_app_apply (W : (Opens X)ᵒᵖ)
    (s : supportedSections
      ((sheafCompose _ (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})).obj F) S W.unop) :
    Subtype.val (p := (· ∈ F.supportedSubmodule S W.unop))
      ((F.supportedSubmoduleSheafForgetIso S).inv.hom.app W s) = s.1 :=
  (rfl)

@[reassoc (attr := simp)]
lemma supportedSubmoduleSheafForgetIso_hom_ι :
    (F.supportedSubmoduleSheafForgetIso S).hom ≫
        supportedSectionsι
          ((sheafCompose _ (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})).obj F) S =
      (sheafCompose _ (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})).map
        (F.supportedSubmoduleι S) := by
  ext W s
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app, AddCommGrpCat.comp_apply]
  exact (supportedSectionsι_hom_app_apply _ S W _).trans
    (F.coe_supportedSubmoduleSheafForgetIso_hom_app_apply S W s)

/-- Taking supported sections preserves flasqueness. -/
instance isFlasque_supportedSubmoduleSheaf [TopCat.Presheaf.IsFlasque F.obj] :
    TopCat.Presheaf.IsFlasque (F.supportedSubmoduleSheaf S).obj := by
  let G := (sheafCompose _ (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})).obj F
  have : TopCat.Presheaf.IsFlasque G.obj := TopCat.Presheaf.isFlasque_comp F.obj _
  have : TopCat.Presheaf.IsFlasque (G.supportedSectionsPresheaf S) := by
    simpa only [supportedSectionsSheaf_obj] using
      (inferInstance : TopCat.Presheaf.IsFlasque (G.supportedSectionsSheaf S).obj)
  exact (TopCat.Presheaf.isFlasque_comp_iff _
    (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})).1
      (TopCat.Presheaf.IsFlasque.of_iso (F.supportedSubmodulePresheafForgetIso S).symm)

/-- The functor taking a sheaf of modules to its sheaf of sections supported in `S`. -/
abbrev supportedSubmoduleFunctor (S : Closeds X) :
    Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R) ⥤
      Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R) where
  obj F := F.supportedSubmoduleSheaf S
  map {F G} f := supportedSubmoduleLift (F.supportedSubmoduleι S ≫ f)
    fun W s ↦ map_mem_supportedSubmodule f
      (range_supportedSubmoduleι_hom_app F S W ▸ LinearMap.mem_range.2 ⟨s, rfl⟩)
  map_id F := by
    rw [← cancel_mono (F.supportedSubmoduleι S)]
    simp
  map_comp {_ _ H} f g := by
    rw [← cancel_mono (H.supportedSubmoduleι S)]
    simp

variable {F G : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)}

@[reassoc]
lemma supportedSubmoduleFunctor_map_ι (f : F ⟶ G) :
    (supportedSubmoduleFunctor S).map f ≫ G.supportedSubmoduleι S =
      F.supportedSubmoduleι S ≫ f :=
  supportedSubmoduleLift_ι _ _

@[simp]
lemma coe_supportedSubmoduleFunctor_map_hom_app_apply (f : F ⟶ G) (W : (Opens X)ᵒᵖ)
    (s : F.supportedSubmodule S W.unop) :
    Subtype.val (p := (· ∈ G.supportedSubmodule S W.unop))
      (((supportedSubmoduleFunctor S).map f).hom.app W s) = f.hom.app W s :=
  (rfl)

/-- The supported-section functor is additive. -/
instance additive_supportedSubmoduleFunctor : (supportedSubmoduleFunctor (R := R) S).Additive where
  map_add {F G f g} := (cancel_mono (G.supportedSubmoduleι S)).1 (by simp)

/-- The comparison with underlying abelian supported sections is natural in the sheaf. -/
def supportedSubmoduleFunctorForgetIso :
    supportedSubmoduleFunctor S ⋙ sheafCompose _ (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}) ≅
      sheafCompose _ (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}) ⋙ supportedSectionsFunctor S :=
  NatIso.ofComponents (fun F ↦ F.supportedSubmoduleSheafForgetIso S) fun {F G} f ↦ by
    apply (cancel_mono (supportedSectionsι
      ((sheafCompose _ (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})).obj G) S)).1
    simp [Category.assoc, ← Functor.map_comp]

@[simp]
lemma supportedSubmoduleFunctorForgetIso_hom_app
    (F : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)) :
    (supportedSubmoduleFunctorForgetIso (R := R) S).hom.app F =
      (F.supportedSubmoduleSheafForgetIso S).hom :=
  (rfl)

@[simp]
lemma supportedSubmoduleFunctorForgetIso_inv_app
    (F : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)) :
    (supportedSubmoduleFunctorForgetIso (R := R) S).inv.app F =
      (F.supportedSubmoduleSheafForgetIso S).inv :=
  (rfl)

/-- Taking supported sections preserves monomorphisms. -/
instance mono_supportedSubmoduleFunctor_map (f : F ⟶ G) [Mono f] :
    Mono ((supportedSubmoduleFunctor S).map f) := by
  have : Mono ((supportedSubmoduleFunctor S).map f ≫ G.supportedSubmoduleι S) := by
    rw [supportedSubmoduleFunctor_map_ι]
    infer_instance
  exact mono_of_mono _ (G.supportedSubmoduleι S)

/-- The supported-section functor is left exact: it preserves exact sequences whose first
map is a monomorphism. -/
theorem exact_map_supportedSubmoduleFunctor
    {T : ShortComplex (Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R))}
    (hT : T.Exact) [Mono T.f] : (T.map (supportedSubmoduleFunctor S)).Exact := by
  let U := sheafCompose (Opens.grothendieckTopology X)
    (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})
  have : Mono (T.map U).f := inferInstanceAs (Mono (U.map T.f))
  apply U.reflects_exact_of_faithful
  rw [← ShortComplex.map_comp]
  apply (ShortComplex.exact_iff_of_iso
    (T.mapNatIso (supportedSubmoduleFunctorForgetIso (R := R) S))).2
  rw [ShortComplex.map_comp]
  exact exact_map_supportedSectionsFunctor S
    (hT.map_of_mono_of_preservesKernel U inferInstance inferInstance)

/-- Degree-zero supported cohomology is the presheaf underlying the supported-section sheaf. -/
def supportedModuleHPresheafZeroIso
    (F : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)) :
    F.supportedModuleHPresheaf S 0 ≅ (F.supportedSubmoduleSheaf S).obj :=
  NatIso.ofComponents (fun W ↦ (F.supportedModuleHZeroEquiv S W.unop).toModuleIso) fun f ↦ by
    ext x
    exact Subtype.ext (F.coe_supportedModuleHZeroEquiv_map S f x)

/-- The degree-zero comparison sends a cohomology class to its supported section. -/
@[simp]
lemma coe_supportedModuleHPresheafZeroIso_hom_app_apply
    (F : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)) (W : (Opens X)ᵒᵖ)
    (x : F.supportedModuleH S W.unop 0) :
    Subtype.val (p := (· ∈ F.supportedSubmodule S W.unop))
      ((F.supportedModuleHPresheafZeroIso S).hom.app W x) =
        F.supportedModuleHZeroEquiv S W.unop x :=
  (rfl)

/-- The degree-zero supported cohomology presheaf of modules already satisfies the sheaf law. -/
theorem isSheaf_supportedModuleHPresheaf_zero
    (F : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)) :
    (F.supportedModuleHPresheaf S 0).IsSheaf :=
  (Presheaf.isSheaf_of_iso_iff (F.supportedModuleHPresheafZeroIso S)).2
    (F.isSheaf_supportedSubmodulePresheaf S)

end

end CategoryTheory.Sheaf
