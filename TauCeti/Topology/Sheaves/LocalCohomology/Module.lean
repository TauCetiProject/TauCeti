/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Sheaves.LocalCohomology.Basic
public import TauCeti.Topology.Sheaves.SupportedCohomology.Module

/-!
# Local cohomology sheaves with module coefficients

For a sheaf `F` of modules over a commutative ring `R` and a closed subset `S`, the
modules of sections supported in `S` form a sheaf `Γ_S(F)`. Forgetting scalars recovers
the supported-section sheaf of the underlying sheaf of abelian groups.

Sheafifying the module-valued presheaf `W ↦ Extⁿ(Q_S(W), F)` defines the local
cohomology sheaf `𝓗_Sⁿ(F)`. In degree zero this is canonically `Γ_S(F)`, compatibly
with restriction and morphisms of coefficient sheaves. These constructions keep the
scalar action on local cohomology, rather than replacing its coefficients by abelian groups.

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

/-- The presheaf of `R`-modules of sections supported in `S`, with restriction induced by `F`. -/
@[expose]
def supportedSubmodulePresheaf : TopCat.Presheaf (ModuleCat.{u} R) X where
  obj W := ModuleCat.of R (F.supportedSubmodule S W.unop)
  map f := ModuleCat.ofHom
    { toFun s := ⟨F.obj.map f s, F.map_mem_supportedSubmodule_of_le (leOfHom f.unop) s.2⟩
      map_add' s t := Subtype.ext (map_add _ _ _)
      map_smul' r s := Subtype.ext (map_smul _ _ _) }
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

/-- Forgetting scalars in the presheaf of supported sections gives the abelian supported-section
presheaf. The comparison is the identity on the underlying sections. -/
def supportedSubmodulePresheafForgetIso :
    F.supportedSubmodulePresheaf S ⋙ forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u} ≅
      supportedSectionsPresheaf
        ((sheafCompose _ (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})).obj F) S :=
  NatIso.ofComponents (fun W ↦ AddEquiv.toAddCommGrpIso
    { toFun s := ⟨s.1, (mem_supportedSections_iff _).2
        ((F.mem_supportedSubmodule_iff).1 s.2)⟩
      invFun s := ⟨s.1, (F.mem_supportedSubmodule_iff).2
        ((mem_supportedSections_iff _).1 s.2)⟩
      left_inv _ := Subtype.ext rfl
      right_inv _ := Subtype.ext rfl
      map_add' _ _ := Subtype.ext rfl }) (fun _ ↦ by ext; rfl)

/-- Supported sections of a sheaf of modules satisfy the sheaf condition. -/
theorem isSheaf_supportedSubmodulePresheaf : (F.supportedSubmodulePresheaf S).IsSheaf := by
  rw [TopCat.Presheaf.isSheaf_iff_isSheaf_comp (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})]
  exact (Presheaf.isSheaf_of_iso_iff (F.supportedSubmodulePresheafForgetIso S)).2
    (isSheaf_supportedSectionsPresheaf _ S)

/-- The sheaf `Γ_S(F)` of sections of `F` supported in the closed subset `S`, retaining its
`R`-module structure. -/
@[expose]
def supportedSubmoduleSheaf : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R) :=
  ⟨F.supportedSubmodulePresheaf S, F.isSheaf_supportedSubmodulePresheaf S⟩

@[simp]
lemma supportedSubmoduleSheaf_obj :
    (F.supportedSubmoduleSheaf S).obj = F.supportedSubmodulePresheaf S :=
  (rfl)

/-- The inclusion of the supported-section sheaf into its coefficient sheaf. -/
def supportedSubmoduleι : F.supportedSubmoduleSheaf S ⟶ F :=
  ObjectProperty.homMk
    { app W := ModuleCat.ofHom (F.supportedSubmodule S W.unop).subtype
      naturality _ _ _ := rfl }

@[simp]
lemma supportedSubmoduleι_hom_app_apply (W : (Opens X)ᵒᵖ) (s : F.supportedSubmodule S W.unop) :
    (F.supportedSubmoduleι S).hom.app W s = s :=
  (rfl)

/-- The image of the supported-section inclusion is precisely the supported submodule. -/
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
/-- A morphism whose sections are supported in `S` factors through `Γ_S(F)`. -/
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

/-- Forgetting scalars identifies the module and abelian sheaves of supported sections. -/
def supportedSubmoduleSheafForgetIso :
    (sheafCompose _ (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})).obj
        (F.supportedSubmoduleSheaf S) ≅
      ((sheafCompose _ (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})).obj F).supportedSectionsSheaf
        S :=
  ObjectProperty.isoMk _ (F.supportedSubmodulePresheafForgetIso S)

/-- The supported-section comparison commutes with the inclusions into the underlying abelian
coefficient sheaf. -/
@[reassoc (attr := simp)]
lemma supportedSubmoduleSheafForgetIso_hom_ι :
    (F.supportedSubmoduleSheafForgetIso S).hom ≫ supportedSectionsι _ S =
      (sheafCompose _ (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})).map
        (F.supportedSubmoduleι S) := by
  ext W s
  -- Sheaf composition and coefficient forgetting are sectionwise; there is no
  -- `sheafCompose` evaluation lemma for this composite.
  change F.supportedSubmodule S W.unop at s
  exact (supportedSectionsι_hom_app_apply _ S W _).trans
    ((by rfl : ((F.supportedSubmodulePresheafForgetIso S).hom.app W s).val = s.val).trans
      (F.supportedSubmoduleι_hom_app_apply S W s).symm)

/-- The supported-section functor for sheaves of `R`-modules. -/
@[expose]
def supportedSubmoduleFunctor :
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

@[simp]
lemma supportedSubmoduleFunctor_obj :
    (supportedSubmoduleFunctor S).obj F = F.supportedSubmoduleSheaf S :=
  (rfl)

/-- The supported-section inclusions are natural in the coefficient sheaf. -/
@[reassoc]
lemma supportedSubmoduleFunctor_map_ι
    {F G : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)} (f : F ⟶ G) :
    (supportedSubmoduleFunctor S).map f ≫ G.supportedSubmoduleι S = F.supportedSubmoduleι S ≫ f :=
  supportedSubmoduleLift_ι _ _

/-- Taking supported sections commutes naturally with forgetting scalars. -/
def supportedSubmoduleFunctorForgetIso :
    supportedSubmoduleFunctor (R := R) S ⋙
        sheafCompose _ (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}) ≅
      sheafCompose _ (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}) ⋙
        supportedSectionsFunctor S :=
  NatIso.ofComponents (fun F ↦ F.supportedSubmoduleSheafForgetIso S) fun {F G} f ↦ by
    let A := sheafCompose (Opens.grothendieckTopology X)
      (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})
    let α : F.supportedSubmoduleSheaf S ⟶ G.supportedSubmoduleSheaf S :=
      (supportedSubmoduleFunctor S).map f
    let β : (A.obj F).supportedSectionsSheaf S ⟶ (A.obj G).supportedSectionsSheaf S :=
      (supportedSectionsFunctor S).map (A.map f)
    have hα : α ≫ G.supportedSubmoduleι S = F.supportedSubmoduleι S ≫ f :=
      supportedSubmoduleFunctor_map_ι S f
    have hβ : β ≫ (A.obj G).supportedSectionsι S =
        (A.obj F).supportedSectionsι S ≫ A.map f := supportedSectionsFunctor_map_ι S (A.map f)
    have hF : (F.supportedSubmoduleSheafForgetIso S).hom ≫ (A.obj F).supportedSectionsι S =
        A.map (F.supportedSubmoduleι S) := F.supportedSubmoduleSheafForgetIso_hom_ι S
    have hG : (G.supportedSubmoduleSheafForgetIso S).hom ≫ (A.obj G).supportedSectionsι S =
        A.map (G.supportedSubmoduleι S) := G.supportedSubmoduleSheafForgetIso_hom_ι S
    -- Explicit source objects keep the composite functors from being unfolded by rewriting.
    change A.map α ≫ (G.supportedSubmoduleSheafForgetIso S).hom =
      (F.supportedSubmoduleSheafForgetIso S).hom ≫ β
    rw [← cancel_mono ((A.obj G).supportedSectionsι S)]
    simp only [Category.assoc, hG, hβ]
    rw [← Category.assoc, hF]
    simpa only [Functor.map_comp] using congrArg A.map hα

@[simp]
lemma supportedSubmoduleFunctorForgetIso_app :
    (supportedSubmoduleFunctorForgetIso (R := R) S).app F = F.supportedSubmoduleSheafForgetIso S :=
  (rfl)

/-- Degree-zero supported cohomology is already the presheaf of supported sections. -/
def supportedModuleHPresheafZeroIso :
    F.supportedModuleHPresheaf S 0 ≅ (F.supportedSubmoduleSheaf S).obj :=
  NatIso.ofComponents (fun W ↦ (F.supportedModuleHZeroEquiv S W.unop).toModuleIso) fun f ↦ by
    ext x
    exact Subtype.ext (F.coe_supportedModuleHZeroEquiv_map S f x)

/-- The degree-zero comparison on sections is the supported Ext-Hom equivalence. -/
@[simp]
lemma supportedModuleHPresheafZeroIso_hom_app_apply (W : (Opens X)ᵒᵖ)
    (x : F.supportedModuleH S W.unop 0) :
    (F.supportedModuleHPresheafZeroIso S).hom.app W x = F.supportedModuleHZeroEquiv S W.unop x :=
  (rfl)

/-- The local cohomology sheaf `𝓗_Sⁿ(F)`, defined by sheafifying the module-valued supported
cohomology presheaf. -/
abbrev supportedModuleHSheaf (n : ℕ) : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R) :=
  (presheafToSheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)).obj
    (F.supportedModuleHPresheaf S n)

/-- The functor of module-valued local cohomology in degree `n`. -/
@[expose]
def supportedModuleHSheafFunctor (n : ℕ) :
    Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R) ⥤
      Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R) :=
  supportedModuleHPresheafFunctor S n ⋙ presheafToSheaf _ _

@[simp]
lemma supportedModuleHSheafFunctor_obj (n : ℕ) :
    (supportedModuleHSheafFunctor S n).obj F = F.supportedModuleHSheaf S n :=
  (rfl)

/-- The degree-zero local cohomology sheaf is the sheaf of supported sections. -/
def supportedModuleHSheafZeroIso : F.supportedModuleHSheaf S 0 ≅ F.supportedSubmoduleSheaf S :=
  (presheafToSheaf _ _).mapIso (F.supportedModuleHPresheafZeroIso S) ≪≫
    (sheafificationIso (F.supportedSubmoduleSheaf S)).symm

/-- The degree-zero comparison is induced by the sectionwise Ext-Hom equivalences through the
canonical sheafification map. -/
@[reassoc (attr := simp)]
lemma toSheafify_supportedModuleHSheafZeroIso_hom :
    toSheafify (Opens.grothendieckTopology X) (F.supportedModuleHPresheaf S 0) ≫
        (F.supportedModuleHSheafZeroIso S).hom.hom =
      (F.supportedModuleHPresheafZeroIso S).hom := by
  simp [supportedModuleHSheafZeroIso]

/-- The degree-zero comparison is natural in the coefficient sheaf. -/
@[reassoc]
lemma supportedModuleHSheafZeroIso_hom_naturality
    {F G : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)} (f : F ⟶ G) :
    (supportedModuleHSheafFunctor S 0).map f ≫ (G.supportedModuleHSheafZeroIso S).hom =
      (F.supportedModuleHSheafZeroIso S).hom ≫ (supportedSubmoduleFunctor S).map f := by
  let α : F.supportedModuleHPresheaf S 0 ⟶ G.supportedModuleHPresheaf S 0 :=
    (supportedModuleHPresheafFunctor S 0).map f
  let β : F.supportedSubmoduleSheaf S ⟶ G.supportedSubmoduleSheaf S :=
    (supportedSubmoduleFunctor S).map f
  -- Give the maps their concrete source objects before using sheafification's
  -- universal property; the functor object identifications are definitional.
  change (presheafToSheaf _ _).map α ≫ (G.supportedModuleHSheafZeroIso S).hom =
    (F.supportedModuleHSheafZeroIso S).hom ≫ β
  apply Sheaf.hom_ext
  apply sheafify_hom_ext _ _ _ (G.supportedSubmoduleSheaf S).property
  -- Normalize the source objects and the forgetful functor's composition to
  -- apply the unit's naturality without unfolding the comparison isomorphisms.
  change toSheafify _ (F.supportedModuleHPresheaf S 0) ≫
      ((presheafToSheaf _ _).map α).hom ≫ (G.supportedModuleHSheafZeroIso S).hom.hom =
    toSheafify _ (F.supportedModuleHPresheaf S 0) ≫
      (F.supportedModuleHSheafZeroIso S).hom.hom ≫ β.hom
  rw [← Category.assoc, ← toSheafify_naturality]
  simp only [Category.assoc, toSheafify_supportedModuleHSheafZeroIso_hom,
    toSheafify_supportedModuleHSheafZeroIso_hom_assoc]
  ext W x
  exact Subtype.ext (coe_supportedModuleHZeroEquiv_naturality_right S W.unop f x)

/-- Local cohomology with supports in `S` has zero stalks outside `S`. -/
theorem isZero_stalk_supportedModuleHSheaf_of_notMem {x : X} (hx : x ∉ S) (n : ℕ) :
    IsZero (TopCat.Presheaf.stalk (F.supportedModuleHSheaf S n).obj x) := by
  rw [TopCat.Presheaf.isZero_stalk_sheafify_iff, ModuleCat.isZero_iff_subsingleton]
  refine subsingleton_of_forall_eq 0 fun t ↦ ?_
  obtain ⟨W, hxW, c, rfl⟩ := (F.supportedModuleHPresheaf S n).exists_germ_eq t
  have hxV : x ∈ W ⊓ S.compl := ⟨hxW, hx⟩
  have : Subsingleton ((F.supportedModuleHPresheaf S n).obj (op (W ⊓ S.compl))) := by
    rw [F.supportedModuleHPresheaf_obj]
    exact F.subsingleton_supportedModuleH_of_le_compl S
      (inf_le_right : W ⊓ S.compl ≤ S.compl) n
  rw [← TopCat.Presheaf.germ_res_apply _ (homOfLE inf_le_left) x hxV]
  rw [Subsingleton.elim ((F.supportedModuleHPresheaf S n).map
    (homOfLE (inf_le_left : W ⊓ S.compl ≤ W)).op c) 0, map_zero]

end

end CategoryTheory.Sheaf
