/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.FormalScheme.SectionsTopology
public import TauCeti.Geometry.RingedSpace.LocallyRingedSpace.GlueMorphisms

/-!
# Morphisms into `Spf A` and automatic continuity for formal schemes

For a formal scheme `X` of finite ideal type and a complete separated adic ring `A` of finite ideal
type, every `f : X ⟶ ofSpf A` induces `sectionsHom f : A →+* Γ(X, ⊤)` satisfying
`ContinuousOnAffines X A` (`continuousOnAffines_sectionsHom`). Conversely, any `φ : A →+* Γ(X, ⊤)`
satisfying `ContinuousOnAffines X A φ` glues across affine formal opens via `IsAffineOpen.isoSpf`,
`ofSpfMap`, and `glueMorphisms` into a unique `X ⟶ ofSpf A` (`homSpfEquiv`; EGA I, Ch. I, 10.4.6;
Stacks Tag 0AHY). By `continuousOnAffines_iff_residue`, `ContinuousOnAffines X A φ` holds iff `φ`
maps an ideal of definition of `A` into the kernel of residue evaluation at every `x : X`.
-/

public section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry

universe u

namespace TauCeti.FormalScheme

section OpenCoverGluing

/-- For opens `V ≤ W` of a formal scheme `X`, the inclusion `X.restrict V ⟶ X.restrict W`. -/
noncomputable def restrictHomOfLE (X : FormalScheme.{u}) {V W : Opens X} (h : V ≤ W) :
    X.restrict V ⟶ X.restrict W :=
  InducedCategory.homMk (X.toLocallyRingedSpace.restrictHomOfLE h)

theorem forgetToLocallyRingedSpace_map_restrictHomOfLE (X : FormalScheme.{u}) {V W : Opens X}
    (h : V ≤ W) :
    forgetToLocallyRingedSpace.map (X.restrictHomOfLE h) =
      X.toLocallyRingedSpace.restrictHomOfLE h := (rfl)

@[reassoc (attr := simp)]
theorem restrictHomOfLE_ofRestrict (X : FormalScheme.{u}) {V W : Opens X} (h : V ≤ W) :
    X.restrictHomOfLE h ≫ X.ofRestrict W = X.ofRestrict V :=
  fullyFaithfulForgetToLocallyRingedSpace.map_injective <| by
    rw [Functor.map_comp, forgetToLocallyRingedSpace_map_restrictHomOfLE,
      forgetToLocallyRingedSpace_map_ofRestrict, forgetToLocallyRingedSpace_map_ofRestrict]
    exact X.toLocallyRingedSpace.restrictHomOfLE_ofRestrict h

@[simp]
theorem restrictHomOfLE_refl (X : FormalScheme.{u}) (V : Opens X) :
    X.restrictHomOfLE (le_refl V) = 𝟙 (X.restrict V) :=
  InducedCategory.hom_ext (X.toLocallyRingedSpace.restrictHomOfLE_refl V)

@[reassoc (attr := simp)]
theorem restrictHomOfLE_comp (X : FormalScheme.{u}) {U V W : Opens X} (h : U ≤ V) (k : V ≤ W) :
    X.restrictHomOfLE h ≫ X.restrictHomOfLE k = X.restrictHomOfLE (h.trans k) :=
  InducedCategory.hom_ext (X.toLocallyRingedSpace.restrictHomOfLE_comp h k)

/-- **Gluing morphisms of formal schemes along an open cover** (EGA I, Ch. I, 10.4.6). -/
noncomputable def glueMorphisms {X Y : FormalScheme.{u}} {ι : Type u} (U : ι → Opens X)
    (hU : ⨆ i, U i = ⊤) (f : ∀ i, X.restrict (U i) ⟶ Y)
    (hf : ∀ i j, X.restrictHomOfLE (inf_le_left : U i ⊓ U j ≤ U i) ≫ f i =
      X.restrictHomOfLE inf_le_right ≫ f j) : X ⟶ Y :=
  InducedCategory.homMk <|
    LocallyRingedSpace.glueMorphisms U hU (fun i ↦ forgetToLocallyRingedSpace.map (f i))
      fun i j ↦ congrArg InducedCategory.Hom.hom (hf i j)

@[reassoc (attr := simp)]
theorem ofRestrict_glueMorphisms {X Y : FormalScheme.{u}} {ι : Type u} (U : ι → Opens X)
    (hU : ⨆ i, U i = ⊤) (f : ∀ i, X.restrict (U i) ⟶ Y)
    (hf : ∀ i j, X.restrictHomOfLE (inf_le_left : U i ⊓ U j ≤ U i) ≫ f i =
      X.restrictHomOfLE inf_le_right ≫ f j) (i : ι) :
    X.ofRestrict (U i) ≫ glueMorphisms U hU f hf = f i :=
  fullyFaithfulForgetToLocallyRingedSpace.map_injective <| by
    simp only [Functor.map_comp, forgetToLocallyRingedSpace_map_ofRestrict]
    exact LocallyRingedSpace.ofRestrict_glueMorphisms U hU _
      (fun j k ↦ congrArg InducedCategory.Hom.hom (hf j k)) i

/-- Morphisms of formal schemes agreeing on every member of an open cover of the source coincide. -/
theorem hom_ext_of_ofRestrict {X Y : FormalScheme.{u}} {ι : Type u} (U : ι → Opens X)
    (hU : ⨆ i, U i = ⊤) {g g' : X ⟶ Y}
    (h : ∀ i, X.ofRestrict (U i) ≫ g = X.ofRestrict (U i) ≫ g') : g = g' :=
  fullyFaithfulForgetToLocallyRingedSpace.map_injective <|
    LocallyRingedSpace.hom_ext_of_ofRestrict U hU fun i ↦ by
      have hi := congrArg forgetToLocallyRingedSpace.map (h i)
      rwa [Functor.map_comp, Functor.map_comp, forgetToLocallyRingedSpace_map_ofRestrict] at hi

/-- Universal property of open-cover morphism gluing for formal schemes. -/
theorem existsUnique_glueMorphisms {X Y : FormalScheme.{u}} {ι : Type u} (U : ι → Opens X)
    (hU : ⨆ i, U i = ⊤) (f : ∀ i, X.restrict (U i) ⟶ Y)
    (hf : ∀ i j, X.restrictHomOfLE (inf_le_left : U i ⊓ U j ≤ U i) ≫ f i =
      X.restrictHomOfLE inf_le_right ≫ f j) :
    ∃! g : X ⟶ Y, ∀ i, X.ofRestrict (U i) ≫ g = f i :=
  ⟨glueMorphisms U hU f hf, ofRestrict_glueMorphisms U hU f hf, fun _ hg ↦
    hom_ext_of_ofRestrict U hU fun i ↦ (hg i).trans (ofRestrict_glueMorphisms U hU f hf i).symm⟩

/-- The affine formal opens of any formal scheme `X` cover `X`. -/
theorem iSup_affineOpens_eq_top (X : FormalScheme.{u}) :
    (⨆ U : {U : Opens X // X.IsAffineOpen U}, U.1) = ⊤ := by
  apply Opens.ext; rw [Opens.coe_iSup]; refine Set.eq_univ_iff_forall.mpr fun x ↦ ?_
  obtain ⟨U, hU, hx, -⟩ :=
    Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens (show x ∈ (⊤ : Opens X) from trivial)
  exact Set.mem_iUnion.mpr ⟨⟨U, hU⟩, hx⟩

end OpenCoverGluing

section SectionsHomAndContinuity

/-- Morphism `ofSpf B ⟶ ofSpf A` attached to a continuous ring homomorphism `φ : A →+* B`. -/
noncomputable def ofSpfMap {A B : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [IsAdicRing A] [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsAdicRing B]
    (φ : A →+* B) (hφ : Continuous φ) : ofSpf B ⟶ ofSpf A :=
  InducedCategory.homMk (Spf.map φ hφ)

@[simp]
theorem forgetToLocallyRingedSpace_map_ofSpfMap {A B : Type u} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [IsAdicRing A] [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
    [IsAdicRing B] (φ : A →+* B) (hφ : Continuous φ) :
    forgetToLocallyRingedSpace.map (ofSpfMap φ hφ) = Spf.map φ hφ := (rfl)

/-- Ring homomorphism `A →+* Γ(X, ⊤)` induced on global sections by `f : X ⟶ ofSpf A`. -/
noncomputable def sectionsHom {X : FormalScheme.{u}} {A : Type u} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [IsAdicRing A] (f : X ⟶ ofSpf A) : A →+* X.presheaf.obj (op ⊤) :=
  ((Spf.topSectionsIso A).inv ≫
    ((forgetToLocallyRingedSpace.map f).c.app (op ⊤) :
      (Spf A).presheaf.obj (op ⊤) ⟶ X.presheaf.obj (op ⊤))).hom

theorem sectionsHom_apply {X : FormalScheme.{u}} {A : Type u} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [IsAdicRing A] (f : X ⟶ ofSpf A) (a : A) :
    sectionsHom f a =
      (forgetToLocallyRingedSpace.map f).c.app (op ⊤) ((Spf.topSectionsIso A).inv a) := (rfl)

@[simp]
theorem sectionsHom_id (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [IsAdicRing A] : sectionsHom (𝟙 (ofSpf A)) = (Spf.topSectionsIso A).inv.hom :=
  RingHom.ext fun _ ↦ rfl

theorem topSectionsIso_hom_sectionsHom_id (A : Type u) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [IsAdicRing A] (a : A) :
    (Spf.topSectionsIso A).hom (sectionsHom (𝟙 (ofSpf A)) a) = a :=
  ConcreteCategory.congr_hom (Spf.topSectionsIso A).inv_hom_id a

/-- Functoriality of `sectionsHom` under precomposition with `g : X ⟶ Y`. -/
theorem sectionsHom_comp {X Y : FormalScheme.{u}} {A : Type u} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [IsAdicRing A] (g : X ⟶ Y) (f : Y ⟶ ofSpf A) :
    sectionsHom (g ≫ f) =
      ((forgetToLocallyRingedSpace.map g).c.app (op ⊤) :
        Y.presheaf.obj (op ⊤) ⟶ X.presheaf.obj (op ⊤)).hom.comp (sectionsHom f) :=
  RingHom.ext fun a ↦ ConcreteCategory.congr_hom
    (LocallyRingedSpace.Γ.map_comp (forgetToLocallyRingedSpace.map f).op
      (forgetToLocallyRingedSpace.map g).op) ((Spf.topSectionsIso A).inv a)

@[simp]
theorem topSectionsIso_hom_sectionsHom_ofSpf {A B : Type u} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [IsAdicRing A] [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
    [IsAdicRing B] (g : ofSpf B ⟶ ofSpf A) (a : A) :
    (Spf.topSectionsIso B).hom (sectionsHom g a) =
      Spf.sectionsHom (forgetToLocallyRingedSpace.map g) a :=
  (congrArg (Spf.topSectionsIso B).hom <| ConcreteCategory.congr_hom
    (Spf.globalSectionsIso_inv_comp_c_app_top (forgetToLocallyRingedSpace.map g)) a).trans
    (ConcreteCategory.congr_hom (Spf.topSectionsIso B).inv_hom_id _)

@[simp]
theorem topSectionsIso_hom_sectionsHom_ofSpfMap {A B : Type u} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [IsAdicRing A] [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
    [IsAdicRing B] (φ : A →+* B) (hφ : Continuous φ) (a : A) :
    (Spf.topSectionsIso B).hom (sectionsHom (ofSpfMap φ hφ) a) = φ a := by
  rw [topSectionsIso_hom_sectionsHom_ofSpf, forgetToLocallyRingedSpace_map_ofSpfMap,
    Spf.sectionsHom_map]

/-- Restricting a global section along `X.ofRestrict U` at `op ⊤` applies `Γ(X, ⊤) → Γ(X, U)`
followed by `restrictTopSectionsIso`. -/
theorem ofRestrict_c_app_top_apply (X : FormalScheme.{u}) (U : Opens X)
    (s : X.presheaf.obj (op ⊤)) :
    (forgetToLocallyRingedSpace.map (X.ofRestrict U)).c.app (op ⊤) s =
      (X.toLocallyRingedSpace.restrictTopSectionsIso U).hom
        (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op s) := by
  rw [forgetToLocallyRingedSpace_map_ofRestrict]
  let F := (X.toLocallyRingedSpace.restrict U.isOpenEmbedding).presheaf
  have hid : F.map (homOfLE (fun _ _ ↦ trivial : (⊤ : Opens _) ≤
        (Opens.map (X.toLocallyRingedSpace.ofRestrict U.isOpenEmbedding).base).obj ⊤)).op = 𝟙 _ :=
    (congrArg F.map (Quiver.Hom.unop_inj (Subsingleton.elim _ (𝟙 _)))).trans (F.map_id _)
  exact ConcreteCategory.congr_hom ((Category.comp_id _).symm.trans
    ((congrArg (_ ≫ ·) hid.symm).trans (X.toLocallyRingedSpace.ofRestrict_c_app_le le_top))) s

/-- Precomposing `f : X ⟶ ofSpf A` with `X.ofRestrict U` restricts `sectionsHom f` to `U`. -/
theorem sectionsHom_ofRestrict_comp_apply {X : FormalScheme.{u}} {A : Type u} [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] [IsAdicRing A] (f : X ⟶ ofSpf A) (U : Opens X)
    (a : A) :
    sectionsHom (X.ofRestrict U ≫ f) a =
      (X.toLocallyRingedSpace.restrictTopSectionsIso U).hom
        (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op (sectionsHom f a)) :=
  (congr($(sectionsHom_comp (X.ofRestrict U) f) a)).trans
    (ofRestrict_c_app_top_apply X U (sectionsHom f a))

/-- `φ : A →+* Γ(X, ⊤)` is continuous on affine opens if `A →+* Γ(X, U)` is continuous into
`X.sectionsTopology U hU` for every affine formal open `U ⊆ X` (EGA I, Ch. I, 10.4.6). -/
def ContinuousOnAffines (X : FormalScheme.{u}) (A : Type u) [CommRing A] [TopologicalSpace A]
    (φ : A →+* X.presheaf.obj (op ⊤)) : Prop :=
  ∀ (U : Opens X) (hU : X.IsAffineOpen U),
    @Continuous _ _ ‹TopologicalSpace A› (X.sectionsTopology U hU)
      ((X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom.comp φ)

/-- Defining characterization of `ContinuousOnAffines`. -/
theorem continuousOnAffines_iff (X : FormalScheme.{u}) (A : Type u) [CommRing A]
    [TopologicalSpace A] (φ : A →+* X.presheaf.obj (op ⊤)) :
    ContinuousOnAffines X A φ ↔
      ∀ (U : Opens X) (hU : X.IsAffineOpen U),
        @Continuous _ _ ‹TopologicalSpace A› (X.sectionsTopology U hU)
          ((X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom.comp φ) := Iff.rfl

/-- Eliminator extracting continuity on an affine formal open `U` from `ContinuousOnAffines`. -/
theorem ContinuousOnAffines.continuous_comp {X : FormalScheme.{u}} {A : Type u} [CommRing A]
    [TopologicalSpace A] {φ : A →+* X.presheaf.obj (op ⊤)} (hφ : ContinuousOnAffines X A φ)
    (U : Opens X) (hU : X.IsAffineOpen U) :
    @Continuous _ _ ‹TopologicalSpace A› (X.sectionsTopology U hU)
      ((X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom.comp φ) := hφ U hU

/-- `ContinuousOnAffines X A φ` is equivalent to continuity into `X.openSectionsTopology ⊤`. -/
theorem continuousOnAffines_iff_continuous (X : FormalScheme.{u}) (A : Type u) [CommRing A]
    [TopologicalSpace A] (φ : A →+* X.presheaf.obj (op ⊤)) :
    ContinuousOnAffines X A φ ↔
      @Continuous _ _ ‹TopologicalSpace A› (X.openSectionsTopology ⊤) φ := by
  rw [continuous_iff_openSectionsTopology]
  exact ⟨fun h U hU _ ↦ h U hU, fun h U hU ↦ h U hU le_top⟩

/-- For every morphism `f : X ⟶ ofSpf A`, `sectionsHom f` is continuous on affine formal opens of
`X` (EGA I, Ch. I, 10.4.6). -/
theorem continuousOnAffines_sectionsHom {X : FormalScheme.{u}} {A : Type u} [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] [IsAdicRing A] (f : X ⟶ ofSpf A) :
    ContinuousOnAffines X A (sectionsHom f) := fun U hU ↦ by
  let tTop : TopologicalSpace ((Spf A).presheaf.obj (op ⊤)) :=
    (ofSpf A).sectionsTopology ⊤ (isAffineOpen_top_ofSpf A)
  let _ := X.sectionsTopology U hU
  have hinv : @Continuous _ _ ‹TopologicalSpace A› tTop (Spf.topSectionsIso A).inv :=
    ((Spf.topSectionsIso A).commRingCatIsoToRingEquiv.toEquiv.isHomeomorph_iff.mp
      (isHomeomorph_topSectionsIso A)).2
  exact @Continuous.comp _ _ _ ‹TopologicalSpace A› tTop (X.sectionsTopology U hU) _ _
    (sectionMap_continuous f (isAffineOpen_top_ofSpf A) hU (fun _ _ ↦ trivial)) hinv

/-- **Residue-field criterion for `ContinuousOnAffines`** (EGA I, Ch. I, 10.4.6): for any ideal of
definition `I` of `A`, `ContinuousOnAffines X A φ` holds if and only if `φ a` vanishes in the
residue field of `X` at every `x : X` for all `a ∈ I`. -/
theorem continuousOnAffines_iff_residue {X : FormalScheme.{u}} {A : Type u} [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] [IsAdicRing A] {I : Ideal A} (hI : IsAdic I)
    (φ : A →+* X.presheaf.obj (op ⊤)) :
    ContinuousOnAffines X A φ ↔
      ∀ a ∈ I, ∀ x : X, X.toLocallyRingedSpace.Γevaluation x (φ a) = 0 := by
  obtain ⟨hKAfg, hKA, -⟩ := IsAdicRing.ideal_spec A
  have hchart (U : Opens X) (hU : X.IsAffineOpen U) :
      @Continuous _ _ ‹TopologicalSpace A› (X.sectionsTopology U hU)
          ((X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom.comp φ) ↔
        ∀ a ∈ I, ∀ x : U, X.toLocallyRingedSpace.Γevaluation x.1 (φ a) = 0 := by
    let _ := X.sectionsTopology U hU
    have := X.sectionsTopology_isTopologicalRing U hU
    have := X.sectionsTopology_isAdicRing U hU
    obtain ⟨-, hJU, -⟩ := IsAdicRing.ideal_spec (X.presheaf.obj (op U))
    rw [hI.continuous_iff_forall_isTopologicallyNilpotent hJU hKA hKAfg]
    refine forall₂_congr fun a _ ↦
      (isTopologicallyNilpotent_iff_forall_evaluation_eq_zero X U hU _).trans <|
        forall_congr' fun x ↦ iff_of_eq <| congrArg (· = 0) <|
          congrArg (X.toLocallyRingedSpace.residue x.1)
            (TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE (le_top : U ≤ ⊤)) x.1 x.2 (φ a))
  refine ⟨fun h a ha x ↦ ?_, fun h U hU ↦ (hchart U hU).mpr fun a ha x ↦ h a ha x.1⟩
  obtain ⟨U, hU, hx, -⟩ :=
    Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens (show x ∈ (⊤ : Opens X) from trivial)
  exact (hchart U hU).mp (h U hU) a ha ⟨x, hx⟩

end SectionsHomAndContinuity

section HomSpfCorrespondence

variable {X : FormalScheme.{u}} {A : Type u} [CommRing A] [TopologicalSpace A]
  [IsTopologicalRing A] [IsAdicRing A]

private noncomputable def chartHom (φ : A →+* X.presheaf.obj (op ⊤))
    (hφ : ContinuousOnAffines X A φ) (U : Opens X) (hU : X.IsAffineOpen U) :
    X.restrict U ⟶ ofSpf A :=
  hU.isoSpf.hom ≫
    @ofSpfMap A (X.presheaf.obj (op U)) _ _ _ _ _ (X.sectionsTopology U hU)
      (X.sectionsTopology_isTopologicalRing U hU) (X.sectionsTopology_isAdicRing U hU)
      ((X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom.comp φ) (hφ.continuous_comp U hU)

private theorem sectionsHom_chartHom (φ : A →+* X.presheaf.obj (op ⊤))
    (hφ : ContinuousOnAffines X A φ) (U : Opens X) (hU : X.IsAffineOpen U) (a : A) :
    sectionsHom (chartHom φ hφ U hU) a =
      (X.toLocallyRingedSpace.restrictTopSectionsIso U).hom
        (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op (φ a)) := by
  let tU := X.sectionsTopology U hU; let trU := X.sectionsTopology_isTopologicalRing U hU
  let adU := X.sectionsTopology_isAdicRing U hU
  let φU := (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom.comp φ
  let m := @ofSpfMap A (X.presheaf.obj (op U)) _ _ _ _ _ tU trU adU φU (hφ.continuous_comp U hU)
  let topU := @Spf.topSectionsIso (X.presheaf.obj (op U)) _ tU trU adU
  have hm_a : sectionsHom m a = topU.inv (φU a) :=
    (ConcreteCategory.congr_hom topU.hom_inv_id (sectionsHom m a)).symm.trans
      (congrArg topU.inv <|
        @topSectionsIso_hom_sectionsHom_ofSpfMap A (X.presheaf.obj (op U)) _ _ _ _ _ tU trU adU
          φU (hφ.continuous_comp U hU) a)
  exact (congr($(sectionsHom_comp hU.isoSpf.hom m) a)).trans <|
    (congrArg _ hm_a).trans
      (ConcreteCategory.congr_hom (topSectionsIso_inv_isoSpf_hom_c_app_top hU) (φU a))

private theorem hom_ofSpf_ext_of_isAffineOpen {U : Opens X} (hU : X.IsAffineOpen U)
    {g₁ g₂ : X.restrict U ⟶ ofSpf A} (h : sectionsHom g₁ = sectionsHom g₂) : g₁ = g₂ := by
  let tU := X.sectionsTopology U hU; let trU := X.sectionsTopology_isTopologicalRing U hU
  let adU := X.sectionsTopology_isAdicRing U hU
  refine (cancel_epi hU.isoSpf.inv).mp (InducedCategory.hom_ext ?_)
  refine @Spf.sectionsHom_injective _ _ _ _ _ _ _ tU trU adU _ _ (RingHom.ext fun a ↦ ?_)
  have hc : sectionsHom (hU.isoSpf.inv ≫ g₁) a = sectionsHom (hU.isoSpf.inv ≫ g₂) a :=
    (congr($(sectionsHom_comp hU.isoSpf.inv g₁) a)).trans <|
      (congrArg _ (congr($h a))).trans (congr($(sectionsHom_comp hU.isoSpf.inv g₂) a)).symm
  exact (@topSectionsIso_hom_sectionsHom_ofSpf _ _ _ _ _ _ _ tU trU adU
    (hU.isoSpf.inv ≫ g₁) a).symm.trans <| (congrArg _ hc).trans
      (@topSectionsIso_hom_sectionsHom_ofSpf _ _ _ _ _ _ _ tU trU adU (hU.isoSpf.inv ≫ g₂) a)

private theorem restrictHomOfLE_chartHom (φ : A →+* X.presheaf.obj (op ⊤))
    (hφ : ContinuousOnAffines X A φ) {W U : Opens X} (hW : X.IsAffineOpen W)
    (hU : X.IsAffineOpen U) (hWU : W ≤ U) :
    X.restrictHomOfLE hWU ≫ chartHom φ hφ U hU = chartHom φ hφ W hW := by
  refine hom_ofSpf_ext_of_isAffineOpen hW (RingHom.ext fun a ↦ ?_)
  have hres := ConcreteCategory.congr_hom
    (X.toLocallyRingedSpace.restrictTopSectionsIso_hom_restrictHomOfLE_c_app_top hWU)
    (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op (φ a))
  have hmap := ConcreteCategory.congr_hom
    (X.presheaf.map_comp (homOfLE (le_top : U ≤ ⊤)).op (homOfLE hWU).op).symm (φ a)
  exact (congr($(sectionsHom_comp (X.restrictHomOfLE hWU) (chartHom φ hφ U hU)) a)).trans <|
    (congrArg ((forgetToLocallyRingedSpace.map (X.restrictHomOfLE hWU)).c.app (op ⊤))
      (sectionsHom_chartHom φ hφ U hU a)).trans <| hres.trans <|
      (congrArg (X.toLocallyRingedSpace.restrictTopSectionsIso W).hom hmap).trans
        (sectionsHom_chartHom φ hφ W hW a).symm

private theorem chartHom_overlap (φ : A →+* X.presheaf.obj (op ⊤))
    (hφ : ContinuousOnAffines X A φ) (U V : {U : Opens X // X.IsAffineOpen U}) :
    X.restrictHomOfLE (inf_le_left : U.1 ⊓ V.1 ≤ U.1) ≫ chartHom φ hφ U.1 U.2 =
      X.restrictHomOfLE inf_le_right ≫ chartHom φ hφ V.1 V.2 := by
  let S := {W : Opens X // X.IsAffineOpen W ∧ W ≤ U.1 ⊓ V.1}
  let Wsub (w : S) : Opens (X.restrict (U.1 ⊓ V.1)) :=
    ⟨{x | x.1 ∈ w.1}, w.1.isOpen.preimage continuous_subtype_val⟩
  have hcov : (⨆ w : S, Wsub w) = ⊤ := by
    apply Opens.ext; rw [Opens.coe_iSup]; refine Set.eq_univ_iff_forall.mpr fun x ↦ ?_
    obtain ⟨W, hW, hxW, hWUV⟩ := Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens x.2
    exact Set.mem_iUnion.mpr ⟨⟨W, hW, hWUV⟩, hxW⟩
  refine hom_ext_of_ofRestrict Wsub hcov fun w ↦ ?_
  let jW := ((X.restrict (U.1 ⊓ V.1)).toLocallyRingedSpace).ofRestrict (Wsub w).isOpenEmbedding
  let rW := X.toLocallyRingedSpace.restrictHomOfLE w.2.2
  have hsub : Set.range jW.base ⊆ Set.range rW.base := by
    rintro _ ⟨x, rfl⟩
    exact ⟨⟨x.1.1, x.2⟩, by rw [LocallyRingedSpace.restrictHomOfLE_base]; exact Subtype.ext rfl⟩
  let hImm := X.toLocallyRingedSpace.isOpenImmersion_restrictHomOfLE w.2.2
  let l : (X.restrict (U.1 ⊓ V.1)).restrict (Wsub w) ⟶ X.restrict w.1 :=
    InducedCategory.homMk <| LocallyRingedSpace.IsOpenImmersion.lift (H := hImm) rW jW hsub
  have hl : l ≫ X.restrictHomOfLE w.2.2 = (X.restrict (U.1 ⊓ V.1)).ofRestrict (Wsub w) :=
    fullyFaithfulForgetToLocallyRingedSpace.map_injective <| by
      rw [Functor.map_comp, forgetToLocallyRingedSpace_map l,
        forgetToLocallyRingedSpace_map_restrictHomOfLE, forgetToLocallyRingedSpace_map_ofRestrict]
      exact LocallyRingedSpace.IsOpenImmersion.lift_fac (H := hImm) rW jW hsub
  rw [← hl, Category.assoc, Category.assoc, restrictHomOfLE_comp_assoc, restrictHomOfLE_comp_assoc,
    restrictHomOfLE_chartHom φ hφ w.2.1 U.2, restrictHomOfLE_chartHom φ hφ w.2.1 V.2]

/-- Morphism `X ⟶ ofSpf A` glued from `φ : A →+* Γ(X, ⊤)` satisfying `ContinuousOnAffines X A φ`. -/
noncomputable def homOfContinuousOnAffines (φ : A →+* X.presheaf.obj (op ⊤))
    (hφ : ContinuousOnAffines X A φ) : X ⟶ ofSpf A :=
  glueMorphisms (fun U : {U : Opens X // X.IsAffineOpen U} ↦ U.1) (iSup_affineOpens_eq_top X)
    (fun U ↦ chartHom φ hφ U.1 U.2) (chartHom_overlap φ hφ)

@[simp]
theorem ofRestrict_homOfContinuousOnAffines (φ : A →+* X.presheaf.obj (op ⊤))
    (hφ : ContinuousOnAffines X A φ) (U : Opens X) (hU : X.IsAffineOpen U) :
    X.ofRestrict U ≫ homOfContinuousOnAffines φ hφ =
      hU.isoSpf.hom ≫
        @ofSpfMap A (X.presheaf.obj (op U)) _ _ _ _ _ (X.sectionsTopology U hU)
          (X.sectionsTopology_isTopologicalRing U hU) (X.sectionsTopology_isAdicRing U hU)
          ((X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom.comp φ)
          (hφ.continuous_comp U hU) :=
  ofRestrict_glueMorphisms (fun V : {V : Opens X // X.IsAffineOpen V} ↦ V.1)
    (iSup_affineOpens_eq_top X) (fun V ↦ chartHom φ hφ V.1 V.2) (chartHom_overlap φ hφ) ⟨U, hU⟩

@[simp]
theorem homOfContinuousOnAffines_sectionsHom (f : X ⟶ ofSpf A) :
    homOfContinuousOnAffines (sectionsHom f) (continuousOnAffines_sectionsHom f) = f := by
  refine hom_ext_of_ofRestrict (fun U : {U : Opens X // X.IsAffineOpen U} ↦ U.1)
    (iSup_affineOpens_eq_top X) fun U ↦ ?_
  rw [ofRestrict_homOfContinuousOnAffines _ _ U.1 U.2]
  exact hom_ofSpf_ext_of_isAffineOpen U.2 (RingHom.ext fun a ↦
    (sectionsHom_chartHom (sectionsHom f) (continuousOnAffines_sectionsHom f) U.1 U.2 a).trans
      (sectionsHom_ofRestrict_comp_apply f U.1 a).symm)

@[simp]
theorem sectionsHom_homOfContinuousOnAffines (φ : A →+* X.presheaf.obj (op ⊤))
    (hφ : ContinuousOnAffines X A φ) :
    sectionsHom (homOfContinuousOnAffines φ hφ) = φ := by
  ext a; refine X.toLocallyRingedSpace.IsSheaf.section_ext fun x _ ↦ ?_
  obtain ⟨U, hU, hx, -⟩ :=
    Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens (show x ∈ (⊤ : Opens X) from trivial)
  refine ⟨U, le_top, hx, (ConcreteCategory.bijective_of_isIso
    (X.toLocallyRingedSpace.restrictTopSectionsIso U).hom).injective ?_⟩
  exact (sectionsHom_ofRestrict_comp_apply (homOfContinuousOnAffines φ hφ) U a).symm.trans <|
    (congrArg (fun k ↦ sectionsHom k a) (ofRestrict_homOfContinuousOnAffines φ hφ U hU)).trans
      (sectionsHom_chartHom φ hφ U hU a)

/-- **Universal property of `ofSpf A`** (EGA I, Ch. I, 10.4.6; Stacks Tag 0AHY): morphisms
`X ⟶ ofSpf A` correspond bijectively to `φ : A →+* Γ(X, ⊤)` satisfying `ContinuousOnAffines`. -/
noncomputable def homSpfEquiv (X : FormalScheme.{u}) (A : Type u) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [IsAdicRing A] :
    (X ⟶ ofSpf A) ≃ {φ : A →+* X.presheaf.obj (op ⊤) // ContinuousOnAffines X A φ} where
  toFun f := ⟨sectionsHom f, continuousOnAffines_sectionsHom f⟩
  invFun φ := homOfContinuousOnAffines φ.1 φ.2
  left_inv := homOfContinuousOnAffines_sectionsHom
  right_inv φ := Subtype.ext (sectionsHom_homOfContinuousOnAffines φ.1 φ.2)

@[simp]
theorem homSpfEquiv_apply_coe (f : X ⟶ ofSpf A) :
    (homSpfEquiv X A f : A →+* X.presheaf.obj (op ⊤)) = sectionsHom f := (rfl)

@[simp]
theorem homSpfEquiv_symm_apply
    (φ : {φ : A →+* X.presheaf.obj (op ⊤) // ContinuousOnAffines X A φ}) :
    (homSpfEquiv X A).symm φ = homOfContinuousOnAffines φ.1 φ.2 := (rfl)

/-- Global sections give a bijection `(X ⟶ ofSpf A) → {φ // ContinuousOnAffines X A φ}`. -/
theorem homSpf_bijective (X : FormalScheme.{u}) (A : Type u) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [IsAdicRing A] :
    Function.Bijective (fun f : X ⟶ ofSpf A ↦
      (⟨sectionsHom f, continuousOnAffines_sectionsHom f⟩ :
        {φ : A →+* X.presheaf.obj (op ⊤) // ContinuousOnAffines X A φ})) :=
  (homSpfEquiv X A).bijective

/-- Two morphisms `X ⟶ ofSpf A` with the same induced global-section homomorphism are equal. -/
theorem sectionsHom_injective : Function.Injective (sectionsHom (X := X) (A := A)) := fun _ _ h ↦
  (homSpf_bijective X A).injective (Subtype.ext h)

end HomSpfCorrespondence

end TauCeti.FormalScheme
