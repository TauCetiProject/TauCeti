/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.FormalScheme.GlueMorphisms
public import TauCeti.AlgebraicGeometry.FormalScheme.SectionsTopology

import TauCeti.Topology.Sheaves.Presheaf

/-!
# Morphisms into `Spf A` and automatic continuity for formal schemes

For a formal scheme `X` of finite ideal type and a complete separated adic ring `A` of finite ideal
type, every `f : X ⟶ ofSpf A` induces `sectionsHom f : A →+* Γ(X, ⊤)` satisfying
`ContinuousOnAffines X A` (`continuousOnAffines_sectionsHom`). Conversely, any `φ : A →+* Γ(X, ⊤)`
satisfying `ContinuousOnAffines X A φ` glues across affine formal opens via `IsAffineOpen.isoSpf`,
`ofSpfMap`, and `glueMorphisms` into a unique `X ⟶ ofSpf A` (`homSpfEquiv`; EGA I, Ch. I, 10.4.6;
Stacks Tag 0AHY). By `continuousOnAffines_iff_residue`, `ContinuousOnAffines X A φ` holds iff `φ`
maps an ideal of definition of `A` into the kernel of residue evaluation at every `x : X`. Out of an
empty formal scheme `X`, there is a unique morphism `X ⟶ ofSpf A`
(`nonempty_unique_hom_of_isEmpty`).
-/

public section
open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry
universe u
namespace TauCeti.FormalScheme

section SectionsHomAndContinuity

section SectionsHom
variable {X Y : FormalScheme.{u}} {A B : Type u} [CommRing A] [TopologicalSpace A]
  [IsTopologicalRing A] [IsAdicRing A] [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
  [IsAdicRing B]

/-- Ring homomorphism `A →+* Γ(X, ⊤)` induced on global sections by `f : X ⟶ ofSpf A`. -/
noncomputable def sectionsHom (f : X ⟶ ofSpf A) : A →+* X.presheaf.obj (op ⊤) :=
  ((Spf.topSectionsIso A).inv ≫ ((forgetToLocallyRingedSpace.map f).c.app (op ⊤) :
    (Spf A).presheaf.obj (op ⊤) ⟶ X.presheaf.obj (op ⊤))).hom

theorem sectionsHom_apply (f : X ⟶ ofSpf A) (a : A) : sectionsHom f a =
    (forgetToLocallyRingedSpace.map f).c.app (op ⊤) ((Spf.topSectionsIso A).inv a) := (rfl)

/-- Functoriality of `sectionsHom` under precomposition with `g : X ⟶ Y`. -/
theorem sectionsHom_comp (g : X ⟶ Y) (f : Y ⟶ ofSpf A) :
    sectionsHom (g ≫ f) = ((forgetToLocallyRingedSpace.map g).c.app (op ⊤) :
        _ ⟶ X.presheaf.obj (op ⊤)).hom.comp (sectionsHom f) :=
  RingHom.ext fun _ ↦ ConcreteCategory.congr_hom (LocallyRingedSpace.Γ.map_comp
    (forgetToLocallyRingedSpace.map f).op (forgetToLocallyRingedSpace.map g).op) _

@[simp] theorem sectionsHom_comp_apply (g : X ⟶ Y) (f : Y ⟶ ofSpf A) (a : A) :
    sectionsHom (g ≫ f) a = (forgetToLocallyRingedSpace.map g).c.app (op ⊤) (sectionsHom f a) :=
  congr($(sectionsHom_comp g f) a)
@[simp] theorem topSectionsIso_hom_sectionsHom_ofSpf (g : ofSpf B ⟶ ofSpf A) (a : A) :
    (Spf.topSectionsIso B).hom (sectionsHom g a) =
      Spf.sectionsHom (forgetToLocallyRingedSpace.map g) a :=
  (Spf.sectionsHom_apply (forgetToLocallyRingedSpace.map g) a).symm
theorem topSectionsIso_hom_sectionsHom_ofSpfMap (φ : A →+* B) (hφ : Continuous φ) (a : A) :
    (Spf.topSectionsIso B).hom (sectionsHom (ofSpfMap φ hφ) a) = φ a := by
  rw [topSectionsIso_hom_sectionsHom_ofSpf, forgetToLocallyRingedSpace_map_ofSpfMap,
    Spf.sectionsHom_map]
@[simp] theorem sectionsHom_ofSpfMap_apply (φ : A →+* B) (hφ : Continuous φ) (a : A) :
    sectionsHom (ofSpfMap φ hφ) a = (Spf.topSectionsIso B).inv (φ a) :=
  (ConcreteCategory.congr_hom (Spf.topSectionsIso B).hom_inv_id _).symm.trans <|
    congrArg _ (topSectionsIso_hom_sectionsHom_ofSpfMap φ hφ a)

/-- Naturality of `sectionsHom` under postcomposition with `ofSpfMap ψ hψ`. -/
@[simp] theorem sectionsHom_comp_ofSpfMap {C : Type u} [CommRing C] [TopologicalSpace C]
    [IsTopologicalRing C] [IsAdicRing C] (f : X ⟶ ofSpf B) (ψ : C →+* B) (hψ : Continuous ψ) :
    sectionsHom (f ≫ ofSpfMap ψ hψ) = (sectionsHom f).comp ψ := RingHom.ext fun _ ↦ by
  rw [RingHom.comp_apply, sectionsHom_comp_apply, sectionsHom_ofSpfMap_apply, sectionsHom_apply]

/-- Precomposing `f : X ⟶ ofSpf A` with `X.ofRestrict U` restricts `sectionsHom f` to `U`. -/
theorem sectionsHom_ofRestrict_comp_apply (f : X ⟶ ofSpf A) (U : Opens X) (a : A) :
    sectionsHom (X.ofRestrict U ≫ f) a = (X.toPresheafedSpace.restrictTopSectionsIso U).hom
      (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op (sectionsHom f a)) :=
  (sectionsHom_comp_apply _ f a).trans (ofRestrict_c_app_top_apply X U _)
end SectionsHom

@[simp] theorem sectionsHom_id (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [IsAdicRing A] : sectionsHom (𝟙 (ofSpf A)) = (Spf.topSectionsIso A).inv.hom :=
  RingHom.ext fun _ ↦ rfl

variable (X : FormalScheme.{u}) (A : Type u) [CommRing A] [TopologicalSpace A]

/-- `φ : A →+* Γ(X, ⊤)` is continuous on affine opens if `A →+* Γ(X, U)` is continuous into
`X.sectionsTopology U hU` for every affine formal open `U ⊆ X` (EGA I, Ch. I, 10.4.6). -/
def ContinuousOnAffines (φ : A →+* X.presheaf.obj (op ⊤)) : Prop :=
  ∀ (U : Opens X) (hU : X.IsAffineOpen U),
    @Continuous _ _ ‹TopologicalSpace A› (X.sectionsTopology U hU)
      ((X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom.comp φ)

/-- Defining characterization of `ContinuousOnAffines`. -/
theorem continuousOnAffines_iff (φ : A →+* X.presheaf.obj (op ⊤)) :
    ContinuousOnAffines X A φ ↔ ∀ (U : Opens X) (hU : X.IsAffineOpen U), @Continuous _ _
      ‹TopologicalSpace A› (X.sectionsTopology U hU)
      ((X.presheaf.map (homOfLE le_top).op).hom.comp φ) := Iff.rfl

/-- `ContinuousOnAffines X A φ` is equivalent to continuity into `X.openSectionsTopology ⊤`. -/
theorem continuousOnAffines_iff_continuous (φ : A →+* X.presheaf.obj (op ⊤)) :
    ContinuousOnAffines X A φ ↔
      @Continuous _ _ ‹TopologicalSpace A› (X.openSectionsTopology ⊤) φ := by
  rw [continuous_iff_openSectionsTopology]
  exact ⟨fun h U hU _ ↦ h U hU, fun h U hU ↦ h U hU le_top⟩
end SectionsHomAndContinuity

section HomSpfCorrespondence
variable {X : FormalScheme.{u}} {A : Type u} [CommRing A] [TopologicalSpace A]
/-- Eliminator extracting continuity on an affine formal open `U` from `ContinuousOnAffines`. -/
theorem ContinuousOnAffines.continuous_comp {φ : A →+* X.presheaf.obj (op ⊤)}
    (hφ : ContinuousOnAffines X A φ) (U : Opens X) (hU : X.IsAffineOpen U) : @Continuous _ _
      ‹TopologicalSpace A› (X.sectionsTopology U hU)
      ((X.presheaf.map (homOfLE le_top).op).hom.comp φ) := hφ U hU
variable [IsTopologicalRing A] [IsAdicRing A]

/-- For every morphism `f : X ⟶ ofSpf A`, `sectionsHom f` is continuous on affine formal opens of
`X` (EGA I, Ch. I, 10.4.6). -/
theorem continuousOnAffines_sectionsHom (f : X ⟶ ofSpf A) :
    ContinuousOnAffines X A (sectionsHom f) := fun U hU ↦ by
  let tTop : TopologicalSpace ((Spf A).presheaf.obj (op ⊤)) :=
    (ofSpf A).sectionsTopology ⊤ (isAffineOpen_top_ofSpf A)
  have hUV : U ≤ (Opens.map (forgetToLocallyRingedSpace.map f).base).obj ⊤ := fun _ _ ↦ trivial
  exact @Continuous.congr _ _ ‹TopologicalSpace A› (X.sectionsTopology U hU) _ _
    (@Continuous.comp _ _ _ ‹TopologicalSpace A› tTop (X.sectionsTopology U hU) _ _
      (continuous_c_app_comp_map_sectionsTopology f (isAffineOpen_top_ofSpf A) hU hUV)
      ((Spf.topSectionsIso A).commRingCatIsoToRingEquiv.toEquiv.isHomeomorph_iff.mp
        (isHomeomorph_topSectionsIso A)).2)
    fun a ↦ (ConcreteCategory.congr_hom
      (PresheafedSpace.Hom.appLE_def (forgetToLocallyRingedSpace.map f).toHom ⊤ U hUV)
      ((Spf.topSectionsIso A).inv a)).trans (ConcreteCategory.comp_apply _ _ _)

/-- **Residue-field criterion for `ContinuousOnAffines`** (EGA I, Ch. I, 10.4.6): for any ideal of
definition `I` of `A`, `ContinuousOnAffines X A φ` holds if and only if `φ a` vanishes in the
residue field of `X` at every `x : X` for all `a ∈ I`. -/
theorem continuousOnAffines_iff_residue {I : Ideal A} (hI : IsAdic I)
    (φ : A →+* X.presheaf.obj (op ⊤)) : ContinuousOnAffines X A φ ↔
      ∀ a ∈ I, ∀ x : X, X.toLocallyRingedSpace.Γevaluation x (φ a) = 0 := by
  obtain ⟨hKAfg, hKA, -⟩ := IsAdicRing.ideal_spec A
  have hchart (U : Opens X) (hU : X.IsAffineOpen U) :
      @Continuous _ _ ‹TopologicalSpace A› (X.sectionsTopology U hU) ((X.presheaf.map
        (homOfLE (le_top : U ≤ ⊤)).op).hom.comp φ) ↔ ∀ a ∈ I, ∀ x : U,
          X.toLocallyRingedSpace.Γevaluation x.1 (φ a) = 0 := by
    obtain ⟨-, hJU, -⟩ := IsAdicRing.ideal_spec hU.Sections
    refine (hI.continuous_iff_forall_isTopologicallyNilpotent (f := ((X.presheaf.map
      (homOfLE (le_top : U ≤ ⊤)).op).hom.comp φ : A →+* hU.Sections)) hJU hKA hKAfg).trans <|
      forall₂_congr fun a _ ↦ (isTopologicallyNilpotent_iff_forall_evaluation_eq_zero X U hU _
        ).trans <| forall_congr' fun x ↦ iff_of_eq <| congrArg
          (X.toLocallyRingedSpace.residue x.1 · = 0)
          (TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE le_top) x.1 x.2 (φ a))
  exact ⟨fun h a ha x ↦ let ⟨U, hU, hx⟩ := X.exists_isAffineOpen_mem x
    (hchart U hU).mp (h U hU) a ha ⟨x, hx⟩, fun h U hU ↦ (hchart U hU).mpr fun a ha x ↦ h a ha x.1⟩

section Construction
variable (φ : A →+* X.presheaf.obj (op ⊤)) (hφ : ContinuousOnAffines X A φ)

private noncomputable def chartHom (U : Opens X) (hU : X.IsAffineOpen U) : X.restrict U ⟶ ofSpf A :=
  hU.isoSpf.hom ≫ ofSpfMap (B := hU.Sections)
    ((X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom.comp φ) (hφ.continuous_comp U hU)

private theorem sectionsHom_chartHom (U : Opens X) (hU : X.IsAffineOpen U) (a : A) :
    sectionsHom (chartHom φ hφ U hU) a = (X.toPresheafedSpace.restrictTopSectionsIso U).hom
      (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op (φ a)) :=
  (sectionsHom_comp_apply _ _ a).trans <|
    (congrArg ((forgetToLocallyRingedSpace.map hU.isoSpf.hom).c.app (op ⊤))
      (sectionsHom_ofSpfMap_apply (B := hU.Sections)
        ((X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom.comp φ)
        (hφ.continuous_comp U hU) a)).trans <|
    ConcreteCategory.congr_hom (topSectionsIso_inv_isoSpf_hom_c_app_top hU) _

private theorem hom_ofSpf_ext_of_isAffineOpen {U : Opens X} (hU : X.IsAffineOpen U)
    {g₁ g₂ : X.restrict U ⟶ ofSpf A} (h : sectionsHom g₁ = sectionsHom g₂) : g₁ = g₂ :=
  (cancel_epi hU.isoSpf.inv).mp <| fullyFaithfulForgetToLocallyRingedSpace.map_injective <|
    Spf.sectionsHom_injective (B := hU.Sections) <| RingHom.ext fun a ↦ by
      simp only [← topSectionsIso_hom_sectionsHom_ofSpf, sectionsHom_comp_apply, h]

private theorem restrictHomOfLE_chartHom {W U : Opens X} (hW : X.IsAffineOpen W)
    (hU : X.IsAffineOpen U) (hWU : W ≤ U) :
    X.restrictHomOfLE hWU ≫ chartHom φ hφ U hU = chartHom φ hφ W hW := by
  refine hom_ofSpf_ext_of_isAffineOpen hW (RingHom.ext fun a ↦ ?_)
  rw [sectionsHom_comp_apply, sectionsHom_chartHom, sectionsHom_chartHom,
    forgetToLocallyRingedSpace_map_restrictHomOfLE]
  have h1 := (X.toLocallyRingedSpace.restrictHomOfLE_toHom hWU).symm ▸ ConcreteCategory.congr_hom
    (X.toPresheafedSpace.restrictTopSectionsIso_hom_restrictHomOfLE_c_app_top hWU)
    (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op (φ a))
  have h2 : (X.presheaf.map (homOfLE hWU).op ≫ (X.toPresheafedSpace.restrictTopSectionsIso W).hom)
        (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op (φ a)) =
      (X.toPresheafedSpace.restrictTopSectionsIso W).hom
        (X.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op (φ a)) :=
    (ConcreteCategory.comp_apply _ _ _).trans <| congrArg
      (X.toPresheafedSpace.restrictTopSectionsIso W).hom <|
      (ConcreteCategory.comp_apply (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op)
        (X.presheaf.map (homOfLE hWU).op) (φ a)).symm.trans <|
      ConcreteCategory.congr_hom (TopCat.Presheaf.map_comp_map_eq X.presheaf _ _ _) (φ a)
  exact h1.trans h2

private theorem chartHom_overlap (U V : {U : Opens X // X.IsAffineOpen U}) :
    X.restrictHomOfLE (inf_le_left : U.1 ⊓ V.1 ≤ U.1) ≫ chartHom φ hφ U.1 U.2 =
      X.restrictHomOfLE inf_le_right ≫ chartHom φ hφ V.1 V.2 := by
  let Wsub (w : {W : Opens X // X.IsAffineOpen W ∧ W ≤ U.1 ⊓ V.1}) :
      Opens (X.restrict (U.1 ⊓ V.1)) :=
    ⟨{x | x.1 ∈ w.1}, w.1.isOpen.preimage continuous_subtype_val⟩
  refine hom_ext_of_ofRestrict Wsub (eq_top_iff.mpr fun x _ ↦
    let ⟨W, hW, hxW, hWUV⟩ := X.exists_isAffineOpen_mem_le x.2
    Opens.mem_iSup.mpr ⟨⟨W, hW, hWUV⟩, hxW⟩) fun w ↦ ?_
  let jW := (X.restrict (U.1 ⊓ V.1)).toLocallyRingedSpace.ofRestrict (Wsub w).isOpenEmbedding
  let rW := X.toLocallyRingedSpace.restrictHomOfLE w.2.2
  have hsub : Set.range jW.base ⊆ Set.range rW.base := fun _ ⟨x, hx⟩ ↦
    ⟨⟨x.1.1, x.2⟩, by rw [LocallyRingedSpace.restrictHomOfLE_base]; exact hx ▸ Subtype.ext rfl⟩
  let hImm := X.toLocallyRingedSpace.isOpenImmersion_restrictHomOfLE w.2.2
  have hl : (InducedCategory.homMk <| LocallyRingedSpace.IsOpenImmersion.lift (H := hImm) rW jW
      hsub : (X.restrict (U.1 ⊓ V.1)).restrict (Wsub w) ⟶ X.restrict w.1) ≫
        X.restrictHomOfLE w.2.2 = (X.restrict (U.1 ⊓ V.1)).ofRestrict (Wsub w) :=
    fullyFaithfulForgetToLocallyRingedSpace.map_injective <| by
      simp only [Functor.map_comp, forgetToLocallyRingedSpace_map_restrictHomOfLE,
        forgetToLocallyRingedSpace_map_ofRestrict]
      exact LocallyRingedSpace.IsOpenImmersion.lift_fac (H := hImm) rW jW hsub
  rw [← hl, Category.assoc, Category.assoc, restrictHomOfLE_comp_assoc, restrictHomOfLE_comp_assoc,
    restrictHomOfLE_chartHom φ hφ w.2.1 U.2, restrictHomOfLE_chartHom φ hφ w.2.1 V.2]

/-- Morphism `X ⟶ ofSpf A` glued from `φ : A →+* Γ(X, ⊤)` satisfying `ContinuousOnAffines X A φ`. -/
noncomputable def homOfContinuousOnAffines : X ⟶ ofSpf A :=
  glueMorphisms (fun U : {U : Opens X // X.IsAffineOpen U} ↦ U.1) (iSup_affineOpens_eq_top X)
    (fun U ↦ chartHom φ hφ U.1 U.2) (chartHom_overlap φ hφ)

@[simp] theorem ofRestrict_homOfContinuousOnAffines (U : Opens X) (hU : X.IsAffineOpen U) :
    X.ofRestrict U ≫ homOfContinuousOnAffines φ hφ = hU.isoSpf.hom ≫ ofSpfMap (B := hU.Sections)
      ((X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom.comp φ) (hφ.continuous_comp U hU) :=
  ofRestrict_glueMorphisms _ (iSup_affineOpens_eq_top X) _ (chartHom_overlap φ hφ) ⟨U, hU⟩

@[simp] theorem homOfContinuousOnAffines_sectionsHom (f : X ⟶ ofSpf A) :
    homOfContinuousOnAffines (sectionsHom f) (continuousOnAffines_sectionsHom f) = f :=
  hom_ext_of_ofRestrict _ (iSup_affineOpens_eq_top X) fun U ↦
    (ofRestrict_homOfContinuousOnAffines _ _ U.1 U.2).trans <|
      hom_ofSpf_ext_of_isAffineOpen U.2 (RingHom.ext fun a ↦
        (sectionsHom_chartHom (sectionsHom f) (continuousOnAffines_sectionsHom f) U.1 U.2 a).trans
          (sectionsHom_ofRestrict_comp_apply f U.1 a).symm)

@[simp] theorem sectionsHom_homOfContinuousOnAffines :
    sectionsHom (homOfContinuousOnAffines φ hφ) = φ := by
  ext a; refine X.toLocallyRingedSpace.IsSheaf.section_ext fun x _ ↦ ?_
  obtain ⟨U, hU, hx⟩ := X.exists_isAffineOpen_mem x
  refine ⟨U, le_top, hx, (ConcreteCategory.bijective_of_isIso
    (X.toPresheafedSpace.restrictTopSectionsIso U).hom).injective ?_⟩
  rw [← sectionsHom_ofRestrict_comp_apply, ofRestrict_homOfContinuousOnAffines φ hφ U hU]
  exact sectionsHom_chartHom φ hφ U hU a
end Construction

/-- **Universal property of `ofSpf A`** (EGA I, Ch. I, 10.4.6; Stacks Tag 0AHY): morphisms
`X ⟶ ofSpf A` correspond bijectively to `φ : A →+* Γ(X, ⊤)` satisfying `ContinuousOnAffines`. -/
noncomputable def homSpfEquiv (X : FormalScheme.{u}) (A : Type u) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [IsAdicRing A] :
    (X ⟶ ofSpf A) ≃ {φ : A →+* X.presheaf.obj (op ⊤) // ContinuousOnAffines X A φ} where
  toFun f := ⟨sectionsHom f, continuousOnAffines_sectionsHom f⟩
  invFun φ := homOfContinuousOnAffines φ.1 φ.2
  left_inv := homOfContinuousOnAffines_sectionsHom
  right_inv φ := Subtype.ext (sectionsHom_homOfContinuousOnAffines φ.1 φ.2)

@[simp] theorem homSpfEquiv_apply_coe (f : X ⟶ ofSpf A) :
    (homSpfEquiv X A f : A →+* X.presheaf.obj (op ⊤)) = sectionsHom f := (rfl)
@[simp] theorem homSpfEquiv_symm_apply
    (φ : {φ : A →+* X.presheaf.obj (op ⊤) // ContinuousOnAffines X A φ}) :
    (homSpfEquiv X A).symm φ = homOfContinuousOnAffines φ.1 φ.2 := (rfl)

/-- Two morphisms `X ⟶ ofSpf A` with the same induced global-section homomorphism are equal. -/
theorem sectionsHom_injective : Function.Injective (sectionsHom (X := X) (A := A)) := fun _ _ h ↦
  (homSpfEquiv X A).injective (Subtype.ext h)

/-- Out of any empty formal scheme `X`, there is a unique morphism `X ⟶ ofSpf A`. -/
theorem nonempty_unique_hom_of_isEmpty (X : FormalScheme.{u}) (hX : IsEmpty X) (A : Type u)
    [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsAdicRing A] :
    Nonempty (Unique (X ⟶ ofSpf A)) :=
  have hsub : Subsingleton (X.presheaf.obj (op ⊤)) :=
    ⟨fun _ _ ↦ X.toLocallyRingedSpace.IsSheaf.section_ext fun x ↦ (hX.false x).elim⟩
  let φ0 : A →+* X.presheaf.obj (op ⊤) :=
    ⟨⟨⟨0, hsub.elim _ _⟩, fun _ _ ↦ hsub.elim _ _⟩, rfl, fun _ _ ↦ hsub.elim _ _⟩
  ⟨{ default := homOfContinuousOnAffines φ0 ((continuousOnAffines_iff_residue
       (IsAdicRing.ideal_spec A).2.1 φ0).mpr fun _ _ x ↦ (hX.false x).elim)
     uniq := fun _ ↦ sectionsHom_injective (RingHom.ext fun _ ↦ hsub.elim _ _) }⟩
end HomSpfCorrespondence
end TauCeti.FormalScheme
