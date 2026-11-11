/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Topology.LocallyConstant.Algebra
public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
public import Mathlib.Topology.Sheaves.Stalks

/-!
# Sheaves of `R`-modules as modules over the sheaf of locally constant functions

For a ring `R` and a topological space `X`, the locally constant `R`-valued functions form a sheaf
of rings `R_X` on `X`, the constant sheaf of rings with value `R`. Its ring of sections over an open
`U` is `LocallyConstant U R`; its ring of global sections is in general larger than `R` (on two
discrete points it is `R × R`). When `R` is commutative, `R_X` is a sheaf of commutative rings.

This file shows that sheaves of `R`-modules on `X` are the same as sheaves of modules over `R_X`.
A locally constant function `f` on `U` acts on a section `s` of a sheaf of `R`-modules `F` over `U`
by gluing the sections `r • s` over the open subsets `f⁻¹(r)`; on germs, `f • s` has germ
`f x • sₓ` at `x` (`TopCat.Sheaf.germ_smul`). Conversely, `R` acts on a sheaf of `R_X`-modules
through the constant functions. These constructions are inverse to each other.

## Main definitions

* `TopCat.locallyConstantRingCatSheaf X R`: the sheaf of rings of locally constant `R`-valued
  functions on `X`, and, for commutative `R`, `TopCat.locallyConstantSheaf X R`, the same sheaf as
  a sheaf of commutative rings.
* `TopCat.Sheaf.instModuleLocallyConstant`: the module structure over `LocallyConstant U R` on the
  sections over `U` of a sheaf of `R`-modules.
* `TopCat.Sheaf.toLocallyConstantModule F`: a sheaf of `R`-modules as a sheaf of `R_X`-modules.
* `SheafOfModules.restrictToConstants M`: a sheaf of `R_X`-modules as a sheaf of `R`-modules, via
  `SheafOfModules.forgetToSheafModuleCat` and restriction of scalars along the constant functions.
* `TopCat.sheafModuleCatEquivLocallyConstant X R`: the equivalence between sheaves of `R`-modules
  on `X` and sheaves of `R_X`-modules.

## Main results

* `TopCat.isSheaf_locallyConstantRingCatPresheaf`: locally constant functions glue.
* `TopCat.Sheaf.germ_smul`, `TopCat.Sheaf.eq_smul_iff`: the action of locally constant functions
  on sections, characterised on germs and by restriction to the opens where the function is
  constant.
* `TopCat.Sheaf.const_smul`: constant functions act through the `R`-module structure.
-/

public section

open CategoryTheory Limits Opposite TopologicalSpace

universe u

noncomputable section

namespace TopCat

variable (X : TopCat.{u}) (R : Type u)

section Ring

variable [Ring R]

/-- The presheaf of rings of locally constant `R`-valued functions on `X`. -/
@[expose] def locallyConstantRingCatPresheaf : X.Presheaf RingCat.{u} where
  obj U := RingCat.of (LocallyConstant U.unop R)
  map i := RingCat.ofHom
    (LocallyConstant.comapRingHom ⟨Set.inclusion i.unop.le, continuous_inclusion i.unop.le⟩)

@[simp]
theorem locallyConstantRingCatPresheaf_obj (U : (Opens X)ᵒᵖ) :
    (locallyConstantRingCatPresheaf X R).obj U = RingCat.of (LocallyConstant U.unop R) :=
  (rfl)

variable {X R}

@[simp]
theorem locallyConstantRingCatPresheaf_map_apply {U V : (Opens X)ᵒᵖ} (i : U ⟶ V)
    (f : LocallyConstant U.unop R) :
    (locallyConstantRingCatPresheaf X R).map i f =
      f.comap ⟨Set.inclusion i.unop.le, continuous_inclusion i.unop.le⟩ := (rfl)

variable (X R)

/-- Locally constant functions glue: the presheaf of locally constant `R`-valued functions is a
sheaf. -/
theorem isSheaf_locallyConstantRingCatPresheaf : (locallyConstantRingCatPresheaf X R).IsSheaf := by
  refine (Presheaf.isSheaf_iff_isSheafUniqueGluing _).mpr fun ι U sf hsf ↦ ?_
  -- The sections of `locallyConstantRingCatPresheaf X R` over `U i` are `LocallyConstant (U i) R`,
  -- but only up to unfolding `RingCat.of`; restate `sf` so that its members coerce to functions.
  change ∀ i, LocallyConstant (U i) R at sf
  have hmem (x : ↥(iSup U)) : ∃ i, x.1 ∈ U i := Opens.mem_iSup.mp x.2
  let g : ↥(iSup U) → R := fun x ↦ sf (hmem x).choose ⟨x, (hmem x).choose_spec⟩
  have hg (i : ι) (x : ↥(iSup U)) (hx : x.1 ∈ U i) : g x = sf i ⟨x, hx⟩ := by
    have h := hsf (hmem x).choose i
    simp only [locallyConstantRingCatPresheaf_map_apply] at h
    exact DFunLike.congr_fun (F := LocallyConstant ↥(U (hmem x).choose ⊓ U i) R) h
      ⟨x, (hmem x).choose_spec, hx⟩
  have hj (i : ι) : Topology.IsOpenEmbedding
      (Set.inclusion (Opens.leSupr U i).le : U i → ↥(iSup U)) :=
    .inclusion _ ((U i).isOpen.preimage continuous_subtype_val)
  have hgc : IsLocallyConstant g := by
    refine (IsLocallyConstant.iff_eventually_eq g).mpr fun x ↦ ?_
    obtain ⟨i, hx⟩ := hmem x
    -- Write `x` as the image of the point `⟨x, hx⟩` of `U i`, to transport neighbourhoods along
    -- the open embedding `hj i`.
    rw [← Set.inclusion_right (Opens.leSupr U i).le x hx, ← (hj i).map_nhds_eq,
      Filter.eventually_map]
    filter_upwards [(IsLocallyConstant.iff_eventually_eq _).mp (sf i).isLocallyConstant
      ⟨x, hx⟩] with z hz
    rw [hg i _ z.2, hg i _ hx]
    exact hz
  refine ⟨(⟨g, hgc⟩ : LocallyConstant ↥(iSup U) R), fun i ↦ ?_, fun t ht ↦ ?_⟩
  · refine LocallyConstant.ext fun x ↦ ?_
    exact hg i ⟨x.1, (Opens.leSupr U i).le x.2⟩ x.2
  · refine LocallyConstant.ext fun x ↦ ?_
    obtain ⟨i, hx⟩ := hmem x
    have h := DFunLike.congr_fun (F := LocallyConstant (U i) R) (ht i) ⟨x, hx⟩
    exact h.trans (hg i x hx).symm

/-- The sheaf `R_X` of rings of locally constant `R`-valued functions on `X`. Its sheaves of
modules are equivalent to sheaves of `R`-modules on `X`. -/
@[expose] def locallyConstantRingCatSheaf :
    CategoryTheory.Sheaf (Opens.grothendieckTopology X) RingCat.{u} :=
  ⟨locallyConstantRingCatPresheaf X R, isSheaf_locallyConstantRingCatPresheaf X R⟩

@[simp]
theorem locallyConstantRingCatSheaf_obj :
    (locallyConstantRingCatSheaf X R).obj = locallyConstantRingCatPresheaf X R :=
  (rfl)

variable {R} {S T : Type u} [Ring S] [Ring T]

/-- Applying a ring homomorphism to the values of locally constant functions, as a morphism of
sheaves of rings. -/
def locallyConstantRingCatSheafMap (φ : R →+* S) :
    locallyConstantRingCatSheaf X R ⟶ locallyConstantRingCatSheaf X S where
  hom :=
    { app := fun U ↦ RingCat.ofHom (LocallyConstant.mapRingHom φ)
      naturality := fun {_ _} _ ↦ by ext; rfl }

@[simp]
lemma locallyConstantRingCatSheafMap_app_apply (φ : R →+* S) (U : (Opens X)ᵒᵖ)
    (f : LocallyConstant U.unop R) :
    (locallyConstantRingCatSheafMap X φ).hom.app U f = f.map φ :=
  (rfl)

@[simp]
lemma locallyConstantRingCatSheafMap_id :
    locallyConstantRingCatSheafMap X (RingHom.id R) = 𝟙 _ := by
  ext
  rfl

@[simp]
lemma locallyConstantRingCatSheafMap_comp (φ : R →+* S) (ψ : S →+* T) :
    locallyConstantRingCatSheafMap X (ψ.comp φ) =
      locallyConstantRingCatSheafMap X φ ≫ locallyConstantRingCatSheafMap X ψ := by
  ext
  rfl

end Ring

section CommRing

variable [CommRing R]

/-- The presheaf of commutative rings of locally constant `R`-valued functions on `X`. -/
@[expose] def locallyConstantPresheaf : X.Presheaf CommRingCat.{u} where
  obj U := CommRingCat.of (LocallyConstant U.unop R)
  map i := CommRingCat.ofHom
    (LocallyConstant.comapRingHom ⟨Set.inclusion i.unop.le, continuous_inclusion i.unop.le⟩)

@[simp]
theorem locallyConstantPresheaf_obj (U : (Opens X)ᵒᵖ) :
    (locallyConstantPresheaf X R).obj U = CommRingCat.of (LocallyConstant U.unop R) :=
  (rfl)

variable {X R}

@[simp]
theorem locallyConstantPresheaf_map_apply {U V : (Opens X)ᵒᵖ} (i : U ⟶ V)
    (f : LocallyConstant U.unop R) :
    (locallyConstantPresheaf X R).map i f =
      f.comap ⟨Set.inclusion i.unop.le, continuous_inclusion i.unop.le⟩ := (rfl)

variable (X R)

/-- Forgetting commutativity, the presheaf of commutative rings of locally constant functions is
the presheaf of rings of locally constant functions. -/
theorem locallyConstantPresheaf_comp_forget₂ :
    locallyConstantPresheaf X R ⋙ forget₂ CommRingCat RingCat.{u} =
      locallyConstantRingCatPresheaf X R :=
  (rfl)

/-- Locally constant functions glue: the presheaf of commutative rings of locally constant
`R`-valued functions is a sheaf. -/
theorem isSheaf_locallyConstantPresheaf : (locallyConstantPresheaf X R).IsSheaf :=
  (CategoryTheory.Presheaf.isSheaf_iff_isSheaf_comp _ _ (forget₂ CommRingCat RingCat.{u})).mpr
    ((locallyConstantPresheaf_comp_forget₂ X R).symm ▸ isSheaf_locallyConstantRingCatPresheaf X R)

/-- The sheaf of commutative rings of locally constant `R`-valued functions on `X`. -/
@[expose] def locallyConstantSheaf : X.Sheaf CommRingCat.{u} :=
  ⟨locallyConstantPresheaf X R, isSheaf_locallyConstantPresheaf X R⟩

@[simp]
theorem locallyConstantSheaf_presheaf :
    (locallyConstantSheaf X R).presheaf = locallyConstantPresheaf X R :=
  (rfl)

/-- Forgetting commutativity, the sheaf of commutative rings of locally constant functions is the
sheaf `R_X` of rings of locally constant functions. -/
theorem sheafCompose_forget₂_obj_locallyConstantSheaf :
    (sheafCompose _ (forget₂ CommRingCat RingCat.{u})).obj (locallyConstantSheaf X R) =
      locallyConstantRingCatSheaf X R :=
  (rfl)

end CommRing

namespace Sheaf

variable {X R} [Ring R]

/-- The fiber of a locally constant function on an open `U` over `r`, as an open subset of `X`. -/
private def fiberOpen {U : Opens X} (f : LocallyConstant U R) (r : R) : Opens X :=
  ⟨Subtype.val '' {x | f x = r},
    U.isOpen.isOpenMap_subtype_val _ (f.isLocallyConstant.isOpen_fiber r)⟩

omit [Ring R] in
private lemma fiberOpen_le {U : Opens X} (f : LocallyConstant U R) (r : R) :
    fiberOpen f r ≤ U := by
  rintro _ ⟨x, -, rfl⟩
  exact x.2

omit [Ring R] in
private lemma mem_fiberOpen {U : Opens X} (f : LocallyConstant U R) {x : X} (hx : x ∈ U) :
    x ∈ fiberOpen f (f ⟨x, hx⟩) :=
  ⟨⟨x, hx⟩, rfl, rfl⟩

omit [Ring R] in
private lemma apply_eq_of_mem_fiberOpen {U : Opens X} (f : LocallyConstant U R) {r : R} {x : X}
    (h : x ∈ fiberOpen f r) (hx : x ∈ U) : f ⟨x, hx⟩ = r := by
  obtain ⟨y, hy, rfl⟩ := h
  exact hy

variable (F : X.Sheaf (ModuleCat.{u} R))

private lemma isCompatible_smul {U : Opens X} (f : LocallyConstant U R)
    (s : F.presheaf.obj (op U)) :
    F.presheaf.IsCompatible (fiberOpen f)
      (fun r ↦ r • F.presheaf.map (homOfLE (fiberOpen_le f r)).op s) := by
  intro r r'
  refine Presheaf.section_ext F _ _ _ fun x hx ↦ ?_
  simp only [Presheaf.germ_res_apply, map_smul]
  congr 1
  exact (apply_eq_of_mem_fiberOpen f hx.1 (fiberOpen_le f r hx.1)).symm.trans
    (apply_eq_of_mem_fiberOpen f hx.2 (fiberOpen_le f r' hx.2))

private lemma existsUnique_smul {U : Opens X} (f : LocallyConstant U R)
    (s : F.presheaf.obj (op U)) :
    ∃! t : F.presheaf.obj (op U), ∀ r : R,
      F.presheaf.map (homOfLE (fiberOpen_le f r)).op t =
        r • F.presheaf.map (homOfLE (fiberOpen_le f r)).op s :=
  F.existsUnique_gluing' _ U (fun r ↦ homOfLE (fiberOpen_le f r))
    (fun _ hx ↦ Opens.mem_iSup.mpr ⟨_, mem_fiberOpen f hx⟩) _ (isCompatible_smul F f s)

/-- The action of a locally constant function `f` on `U` on a section `s` of a sheaf of
`R`-modules over `U`: the section that agrees with `r • s` on the open subset where `f` takes the
value `r`. -/
private def locallyConstantSMul {U : Opens X} (f : LocallyConstant U R)
    (s : F.presheaf.obj (op U)) : F.presheaf.obj (op U) :=
  (existsUnique_smul F f s).exists.choose

@[no_expose] instance instSMulLocallyConstant (U : Opens X) :
    SMul (LocallyConstant U R) (F.presheaf.obj (op U)) where
  smul := locallyConstantSMul F

/-- The germ of a section at a point `x` of `U` is the germ of its restriction to the open subset
where `f` takes the value `f x`. -/
private lemma germ_eq_germ_res_fiberOpen {U : Opens X} (f : LocallyConstant U R)
    (s : F.presheaf.obj (op U)) {x : X} (hx : x ∈ U) :
    F.presheaf.germ U x hx s = F.presheaf.germ (fiberOpen f (f ⟨x, hx⟩)) x (mem_fiberOpen f hx)
      (F.presheaf.map (homOfLE (fiberOpen_le f (f ⟨x, hx⟩))).op s) :=
  (Presheaf.germ_res_apply F.presheaf _ x _ s).symm

/-- The germ of `f • s` at `x` is the value of `f` at `x` acting on the germ of `s`. -/
@[simp]
theorem germ_smul {U : Opens X} (f : LocallyConstant U R) (s : F.presheaf.obj (op U)) (x : X)
    (hx : x ∈ U) :
    F.presheaf.germ U x hx (f • s) = f ⟨x, hx⟩ • F.presheaf.germ U x hx s := by
  have h : F.presheaf.map (homOfLE (fiberOpen_le f (f ⟨x, hx⟩))).op (f • s) = _ :=
    (existsUnique_smul F f s).exists.choose_spec (f ⟨x, hx⟩)
  rw [germ_eq_germ_res_fiberOpen F f (f • s), h, map_smul, ← germ_eq_germ_res_fiberOpen]

/-- The sections over `U` of a sheaf of `R`-modules form a module over the ring of locally
constant `R`-valued functions on `U`: `f • s` agrees with `r • s` where `f` takes the value `r`. -/
instance instModuleLocallyConstant (U : Opens X) :
    Module (LocallyConstant U R) (F.presheaf.obj (op U)) where
  one_smul s := Presheaf.section_ext F _ _ _ fun x hx ↦ by simp
  mul_smul f g s := Presheaf.section_ext F _ _ _ fun x hx ↦ by simp [mul_smul]
  smul_zero f := Presheaf.section_ext F _ _ _ fun x hx ↦ by simp
  smul_add f s t := Presheaf.section_ext F _ _ _ fun x hx ↦ by simp
  add_smul f g s := Presheaf.section_ext F _ _ _ fun x hx ↦ by simp [add_smul]
  zero_smul s := Presheaf.section_ext F _ _ _ fun x hx ↦ by simp

/-- A constant function acts on sections through the `R`-module structure. -/
@[simp]
theorem const_smul {U : Opens X} (r : R) (s : F.presheaf.obj (op U)) :
    LocallyConstant.const U r • s = r • s :=
  Presheaf.section_ext F _ _ _ fun x hx ↦ by simp [map_smul]

/-- Restriction of sections is semilinear for the action of locally constant functions. -/
theorem map_smul_locallyConstant {U V : Opens X} (i : V ⟶ U) (f : LocallyConstant U R)
    (s : F.presheaf.obj (op U)) :
    F.presheaf.map i.op (f • s) =
      (f.comap ⟨Set.inclusion i.le, continuous_inclusion i.le⟩ : LocallyConstant V R) •
        F.presheaf.map i.op s :=
  Presheaf.section_ext F _ _ _ fun x hx ↦ by simp

/-- `f • s` is characterised by its restrictions: it is the section whose restriction to any open
`V ⊆ U` on which `f` is constant with value `r` is the restriction of `r • s`. -/
theorem eq_smul_iff {U : Opens X} (f : LocallyConstant U R) (s t : F.presheaf.obj (op U)) :
    t = f • s ↔ ∀ (V : Opens X) (i : V ⟶ U) (r : R), (∀ x : V, f ⟨x.1, i.le x.2⟩ = r) →
      F.presheaf.map i.op t = r • F.presheaf.map i.op s := by
  refine ⟨?_, fun h ↦ Presheaf.section_ext F _ _ _ fun x hx ↦ ?_⟩
  · rintro rfl V i r hr
    rw [map_smul_locallyConstant, ← const_smul]
    congr 1
    exact LocallyConstant.ext hr
  · have hV := h _ (homOfLE (fiberOpen_le f (f ⟨x, hx⟩))) _
      fun y ↦ apply_eq_of_mem_fiberOpen f y.2 _
    rw [germ_smul, germ_eq_germ_res_fiberOpen F f t, hV, map_smul, ← germ_eq_germ_res_fiberOpen]

variable {F} in
/-- Morphisms of sheaves of `R`-modules commute with the action of locally constant functions. -/
theorem hom_app_smul {G : X.Sheaf (ModuleCat.{u} R)} (φ : F ⟶ G) {U : Opens X}
    (f : LocallyConstant U R) (s : F.presheaf.obj (op U)) :
    φ.hom.app (op U) (f • s) = f • φ.hom.app (op U) s :=
  Presheaf.section_ext G _ _ _ fun x hx ↦ by
    rw [germ_smul, ← Presheaf.stalkFunctor_map_germ_apply, ← Presheaf.stalkFunctor_map_germ_apply,
      germ_smul]
    exact map_smul ((Presheaf.stalkFunctor (ModuleCat R) x).map φ.hom).hom _ _

/-- A sheaf of `R`-modules `F` as a sheaf of modules over the sheaf `R_X` of locally constant
`R`-valued functions: a locally constant function `f` acts on a section `s` by `f • s`, which
agrees with `r • s` where `f` takes the value `r`. Its underlying sheaf of abelian groups is that
of `F`. -/
@[expose] def toLocallyConstantModule : SheafOfModules.{u} (locallyConstantRingCatSheaf X R) where
  val :=
    letI (U : (Opens X)ᵒᵖ) : Module ((locallyConstantRingCatSheaf X R).obj.obj U)
        ((F.presheaf ⋙ forget₂ (ModuleCat R) Ab).obj U) :=
      instModuleLocallyConstant F U.unop
    PresheafOfModules.ofPresheaf (F.presheaf ⋙ forget₂ _ _)
      fun _ _ i f s ↦ map_smul_locallyConstant F i.unop f s
  isSheaf :=
    ((sheafCompose (Opens.grothendieckTopology X) (forget₂ (ModuleCat R) Ab)).obj F).property

/-- The sections of `F.toLocallyConstantModule` are those of `F`, with the same restrictions. -/
@[simp]
theorem toLocallyConstantModule_val_map_apply {U V : (Opens X)ᵒᵖ} (i : U ⟶ V)
    (s : F.toLocallyConstantModule.val.obj U) :
    F.toLocallyConstantModule.val.map i s = F.presheaf.map i s :=
  (rfl)

/-- A locally constant function acts on the sections of `F.toLocallyConstantModule` by
`TopCat.Sheaf.instModuleLocallyConstant`. -/
@[simp]
theorem toLocallyConstantModule_smul {U : Opens X} (f : LocallyConstant U R)
    (s : F.toLocallyConstantModule.val.obj (op U)) :
    @HSMul.hSMul ((locallyConstantRingCatSheaf X R).obj.obj (op U))
        (F.toLocallyConstantModule.val.obj (op U)) _ _ f s =
      @HSMul.hSMul (LocallyConstant U R) (F.presheaf.obj (op U)) _ _ f s :=
  (rfl)

variable (X R) in
/-- Sheaves of `R`-modules on `X` as sheaves of modules over the sheaf `R_X` of locally constant
`R`-valued functions. -/
@[expose, simps]
def toLocallyConstantModuleFunctor :
    X.Sheaf (ModuleCat.{u} R) ⥤ SheafOfModules.{u} (locallyConstantRingCatSheaf X R) where
  obj F := F.toLocallyConstantModule
  map φ := ⟨PresheafOfModules.homMk (Functor.whiskerRight φ.hom (forget₂ _ _))
    fun U f s ↦ hom_app_smul φ (U := U.unop) f s⟩

end Sheaf

end TopCat

namespace SheafOfModules

open TopCat

variable (X : TopCat.{u}) (R : Type u) [Ring R]

/-- Sheaves of modules over the sheaf `R_X` of locally constant `R`-valued functions as sheaves of
`R`-modules: the forgetful functor to sheaves of modules over the ring `R_X(X)` of global sections,
followed by restriction of scalars along the constant functions. -/
@[expose] def restrictToConstantsFunctor :
    SheafOfModules.{u} (locallyConstantRingCatSheaf X R) ⥤ X.Sheaf (ModuleCat.{u} R) :=
  forgetToSheafModuleCat _ (op ⊤) (initialOpOfTerminal isTerminalTop) ⋙
    -- Elaborated without an expected type: unifying with the codomain of the first factor would
    -- replace the ring structure carried by the ring hom, and `HasSheafCompose` is then not found.
    (sheafCompose (Opens.grothendieckTopology X) (ModuleCat.restrictScalars.{u}
      (LocallyConstant.constRingHom : R →+* (locallyConstantRingCatSheaf X R).obj.obj (op ⊤))) : _)

variable {X R} (M : SheafOfModules.{u} (locallyConstantRingCatSheaf X R))

/-- A sheaf of modules over `R_X`, the sheaf of locally constant `R`-valued functions, as a sheaf of
`R`-modules: `r : R` acts through the constant function with value `r`. -/
@[expose] def restrictToConstants : X.Sheaf (ModuleCat.{u} R) :=
  (restrictToConstantsFunctor X R).obj M

@[simp]
theorem restrictToConstantsFunctor_obj :
    (restrictToConstantsFunctor X R).obj M = M.restrictToConstants :=
  (rfl)

/-- The sections of `M.restrictToConstants` are those of `M`, with the same restrictions. -/
@[simp]
theorem restrictToConstants_presheaf_map_apply {U V : (Opens X)ᵒᵖ} (i : U ⟶ V)
    (m : M.restrictToConstants.presheaf.obj U) :
    M.restrictToConstants.presheaf.map i m = M.val.map i m :=
  (rfl)

/-- In `M.restrictToConstants`, `r : R` acts through the constant function with value `r`. -/
theorem restrictToConstants_smul {U : Opens X} (r : R)
    (m : M.restrictToConstants.presheaf.obj (op U)) :
    r • m = @HSMul.hSMul ((locallyConstantRingCatSheaf X R).obj.obj (op U)) (M.val.obj (op U)) _ _
      (LocallyConstant.const U r) m :=
  (rfl)

/-- The morphism of sheaves of `R`-modules induced by a morphism of sheaves of `R_X`-modules has the
same components. -/
@[simp]
theorem restrictToConstantsFunctor_map_hom_app_apply {N : SheafOfModules.{u}
    (locallyConstantRingCatSheaf X R)} (φ : M ⟶ N) (U : (Opens X)ᵒᵖ)
    (m : M.restrictToConstants.presheaf.obj U) :
    ((restrictToConstantsFunctor X R).map φ).hom.app U m = φ.val.app U m :=
  (rfl)

/-- The sheaf of `R_X`-modules obtained from `M.restrictToConstants` is `M`: the action of locally
constant functions glued from the action of constants is the given action. Both sheaves have the
same sections by construction, and the isomorphism is the identity on them. -/
@[expose] def restrictToConstantsToLocallyConstantModuleIso :
    M.restrictToConstants.toLocallyConstantModule ≅ M :=
  (SheafOfModules.fullyFaithfulForget _).preimageIso
    (PresheafOfModules.isoMk (fun U ↦
      letI : Module ((locallyConstantRingCatSheaf X R).obj.obj U)
          ((M.restrictToConstants.presheaf ⋙ forget₂ (ModuleCat R) Ab).obj U) :=
        Sheaf.instModuleLocallyConstant _ U.unop
      LinearEquiv.toModuleIso
      { toFun := fun m ↦ m
        invFun := fun m ↦ m
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun f m ↦ by
          refine ((Sheaf.eq_smul_iff M.restrictToConstants (U := U.unop) f m _).mpr
            fun V i r hr ↦ ?_).symm
          have hf : (locallyConstantRingCatSheaf X R).obj.map i.op f = LocallyConstant.const V r :=
            LocallyConstant.ext hr
          -- In `M.restrictToConstants`, `r` acts by the constant function `r`, which is the
          -- restriction of `f` to `V`.
          exact (M.val.map_smul i.op f m).trans (congrArg (· • M.val.map i.op m) hf)
        -- The sections of the two sheaves coincide by construction.
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl }) fun _ _ _ ↦ rfl)

@[simp]
theorem restrictToConstantsToLocallyConstantModuleIso_hom_val_app_apply (U : (Opens X)ᵒᵖ)
    (m : M.restrictToConstants.toLocallyConstantModule.val.obj U) :
    (M.restrictToConstantsToLocallyConstantModuleIso.hom.val.app U) m = m :=
  (rfl)

@[simp]
theorem restrictToConstantsToLocallyConstantModuleIso_inv_val_app_apply (U : (Opens X)ᵒᵖ)
    (m : M.val.obj U) :
    (M.restrictToConstantsToLocallyConstantModuleIso.inv.val.app U) m = m :=
  (rfl)

end SheafOfModules

namespace TopCat.Sheaf

variable {X : TopCat.{u}} {R : Type u} [Ring R] (F : X.Sheaf (ModuleCat.{u} R))

/-- Restricting the action of locally constant functions on a sheaf of `R`-modules `F` to the
constant functions recovers `F`. Both sheaves have the same sections by construction, and the
isomorphism is the identity on them. -/
@[expose] def toLocallyConstantModuleRestrictToConstantsIso :
    F ≅ F.toLocallyConstantModule.restrictToConstants :=
  ObjectProperty.isoMk _ (NatIso.ofComponents (fun U ↦ ModuleCat.isoMk (Iso.refl _) fun r ↦ by
    ext s
    exact (SheafOfModules.restrictToConstants_smul F.toLocallyConstantModule (U := U.unop) r
      s).trans (const_smul F (U := U.unop) r s))
    fun _ ↦ rfl)

@[simp]
theorem toLocallyConstantModuleRestrictToConstantsIso_hom_hom_app_apply (U : (Opens X)ᵒᵖ)
    (s : F.presheaf.obj U) :
    (F.toLocallyConstantModuleRestrictToConstantsIso.hom.hom.app U) s = s :=
  (rfl)

@[simp]
theorem toLocallyConstantModuleRestrictToConstantsIso_inv_hom_app_apply (U : (Opens X)ᵒᵖ)
    (s : F.toLocallyConstantModule.restrictToConstants.presheaf.obj U) :
    (F.toLocallyConstantModuleRestrictToConstantsIso.inv.hom.app U) s = s :=
  (rfl)

end TopCat.Sheaf

namespace TopCat

variable (X : TopCat.{u}) (R : Type u) [Ring R]

/-- Sheaves of `R`-modules on `X` are equivalent to sheaves of modules over the sheaf `R_X` of
locally constant `R`-valued functions. A locally constant function acts on a section by gluing the
actions of its values on the open subsets where it is constant; conversely, `R` acts on a sheaf of
`R_X`-modules through the constant functions. The unit and counit are the identity on sections. -/
@[expose] def sheafModuleCatEquivLocallyConstant :
    X.Sheaf (ModuleCat.{u} R) ≌ SheafOfModules.{u} (locallyConstantRingCatSheaf X R) :=
  -- Naturality holds componentwise because all components are the identity on sections.
  .mk (Sheaf.toLocallyConstantModuleFunctor X R) (SheafOfModules.restrictToConstantsFunctor X R)
    (NatIso.ofComponents Sheaf.toLocallyConstantModuleRestrictToConstantsIso fun _ ↦
      ObjectProperty.hom_ext _ (by ext; rfl))
    (NatIso.ofComponents SheafOfModules.restrictToConstantsToLocallyConstantModuleIso
      fun _ ↦ rfl)

@[simp]
theorem sheafModuleCatEquivLocallyConstant_functor :
    (sheafModuleCatEquivLocallyConstant X R).functor = Sheaf.toLocallyConstantModuleFunctor X R :=
  (rfl)

@[simp]
theorem sheafModuleCatEquivLocallyConstant_inverse :
    (sheafModuleCatEquivLocallyConstant X R).inverse =
      SheafOfModules.restrictToConstantsFunctor X R :=
  (rfl)

@[simp]
theorem sheafModuleCatEquivLocallyConstant_unitIso_app (F : X.Sheaf (ModuleCat.{u} R)) :
    (sheafModuleCatEquivLocallyConstant X R).unitIso.app F =
      F.toLocallyConstantModuleRestrictToConstantsIso :=
  (rfl)

@[simp]
theorem sheafModuleCatEquivLocallyConstant_counitIso_app
    (M : SheafOfModules.{u} (locallyConstantRingCatSheaf X R)) :
    (sheafModuleCatEquivLocallyConstant X R).counitIso.app M =
      M.restrictToConstantsToLocallyConstantModuleIso :=
  (rfl)

end TopCat
