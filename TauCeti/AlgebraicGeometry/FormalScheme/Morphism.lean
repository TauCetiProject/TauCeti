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
universe u w
namespace TauCeti.FormalScheme
section RestrictHom
variable (X : FormalScheme.{u})

/-- For opens `V ≤ W` of a formal scheme `X`, the inclusion `X.restrict V ⟶ X.restrict W`. -/
noncomputable def restrictHomOfLE {V W : Opens X} (h : V ≤ W) : X.restrict V ⟶ X.restrict W :=
  InducedCategory.homMk (X.toLocallyRingedSpace.restrictHomOfLE h)

theorem forgetToLocallyRingedSpace_map_restrictHomOfLE {V W : Opens X} (h : V ≤ W) :
    forgetToLocallyRingedSpace.map (X.restrictHomOfLE h) =
      X.toLocallyRingedSpace.restrictHomOfLE h := (rfl)
@[reassoc (attr := simp)] theorem restrictHomOfLE_ofRestrict {V W : Opens X} (h : V ≤ W) :
    X.restrictHomOfLE h ≫ X.ofRestrict W = X.ofRestrict V :=
  fullyFaithfulForgetToLocallyRingedSpace.map_injective <| by
    simp only [Functor.map_comp, forgetToLocallyRingedSpace_map_restrictHomOfLE,
      forgetToLocallyRingedSpace_map_ofRestrict]
    exact X.toLocallyRingedSpace.restrictHomOfLE_ofRestrict h
@[simp] theorem restrictHomOfLE_refl (V : Opens X) :
    X.restrictHomOfLE (le_refl V) = 𝟙 (X.restrict V) :=
  InducedCategory.hom_ext (X.toLocallyRingedSpace.restrictHomOfLE_refl V)
@[reassoc (attr := simp)] theorem restrictHomOfLE_comp {U V W : Opens X} (h : U ≤ V) (k : V ≤ W) :
    X.restrictHomOfLE h ≫ X.restrictHomOfLE k = X.restrictHomOfLE (h.trans k) :=
  InducedCategory.hom_ext (X.toLocallyRingedSpace.restrictHomOfLE_comp h k)
end RestrictHom

section Glue
variable {X Y : FormalScheme.{u}} {ι : Type w} (U : ι → Opens X) (hU : ⨆ i, U i = ⊤)
include hU

/-- Morphisms of formal schemes agreeing on every member of an open cover of the source coincide. -/
theorem hom_ext_of_ofRestrict {g g' : X ⟶ Y}
    (h : ∀ i, X.ofRestrict (U i) ≫ g = X.ofRestrict (U i) ≫ g') : g = g' :=
  fullyFaithfulForgetToLocallyRingedSpace.map_injective <|
    LocallyRingedSpace.hom_ext_of_ofRestrict U hU fun i ↦ by
      have hi := congrArg forgetToLocallyRingedSpace.map (h i)
      rwa [Functor.map_comp, Functor.map_comp, forgetToLocallyRingedSpace_map_ofRestrict] at hi

variable (f : ∀ i, X.restrict (U i) ⟶ Y)
  (hf : ∀ i j, X.restrictHomOfLE (inf_le_left : U i ⊓ U j ≤ U i) ≫ f i =
    X.restrictHomOfLE inf_le_right ≫ f j)
include hf

/-- **Gluing morphisms of formal schemes along an open cover** (EGA I, Ch. I, 10.4.6). -/
noncomputable def glueMorphisms : X ⟶ Y :=
  InducedCategory.homMk <| LocallyRingedSpace.glueMorphisms U hU
    (fun i ↦ forgetToLocallyRingedSpace.map (f i))
    fun i j ↦ congrArg InducedCategory.Hom.hom (hf i j)

@[reassoc (attr := simp)] theorem ofRestrict_glueMorphisms (i : ι) :
    X.ofRestrict (U i) ≫ glueMorphisms U hU f hf = f i :=
  fullyFaithfulForgetToLocallyRingedSpace.map_injective <| by
    simp only [Functor.map_comp, forgetToLocallyRingedSpace_map_ofRestrict]
    exact LocallyRingedSpace.ofRestrict_glueMorphisms U hU _ _ i

/-- Universal property of open-cover morphism gluing for formal schemes. -/
theorem existsUnique_glueMorphisms : ∃! g : X ⟶ Y, ∀ i, X.ofRestrict (U i) ≫ g = f i :=
  ⟨glueMorphisms U hU f hf, ofRestrict_glueMorphisms U hU f hf, fun _ hg ↦
    hom_ext_of_ofRestrict U hU fun i ↦ (hg i).trans (ofRestrict_glueMorphisms U hU f hf i).symm⟩
end Glue

section SectionsHomAndContinuity
/-- Restricting a global section along `X.ofRestrict U` at `op ⊤` applies `Γ(X, ⊤) → Γ(X, U)`
followed by `restrictTopSectionsIso`. -/
theorem ofRestrict_c_app_top_apply (X : FormalScheme.{u}) (U : Opens X)
    (s : X.presheaf.obj (op ⊤)) : (forgetToLocallyRingedSpace.map (X.ofRestrict U)).c.app (op ⊤) s =
      (X.toLocallyRingedSpace.restrictTopSectionsIso U).hom
        (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op s) := by
  rw [forgetToLocallyRingedSpace_map_ofRestrict]
  exact ConcreteCategory.congr_hom (X.toLocallyRingedSpace.ofRestrict_c_app_top U) s

section SectionsHom
variable {X Y : FormalScheme.{u}} {A B : Type u} [CommRing A] [TopologicalSpace A]
  [IsTopologicalRing A] [IsAdicRing A] [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
  [IsAdicRing B]

/-- Morphism `ofSpf B ⟶ ofSpf A` attached to a continuous ring homomorphism `φ : A →+* B`. -/
noncomputable def ofSpfMap (φ : A →+* B) (hφ : Continuous φ) : ofSpf B ⟶ ofSpf A :=
  InducedCategory.homMk (Spf.map φ hφ)

@[simp] theorem forgetToLocallyRingedSpace_map_ofSpfMap (φ : A →+* B) (hφ : Continuous φ) :
    forgetToLocallyRingedSpace.map (ofSpfMap φ hφ) = Spf.map φ hφ := (rfl)
@[simp] theorem ofSpfMap_id : ofSpfMap (RingHom.id A) continuous_id = 𝟙 (ofSpf A) :=
  InducedCategory.hom_ext Spf.map_id
@[reassoc] theorem ofSpfMap_comp {C : Type u} [CommRing C] [TopologicalSpace C]
    [IsTopologicalRing C] [IsAdicRing C] (φ : B →+* C) (hφ : Continuous φ) (ψ : A →+* B)
    (hψ : Continuous ψ) : ofSpfMap (φ.comp ψ) (hφ.comp hψ) = ofSpfMap φ hφ ≫ ofSpfMap ψ hψ :=
  InducedCategory.hom_ext (Spf.map_comp φ hφ ψ hψ)

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
    (Spf.topSectionsIso B).hom (sectionsHom (ofSpfMap φ hφ) a) = φ a :=
  (topSectionsIso_hom_sectionsHom_ofSpf _ a).trans <|
    (congr($(Spf.sectionsHom_map φ hφ) a) : _)
@[simp] theorem sectionsHom_ofSpfMap_apply (φ : A →+* B) (hφ : Continuous φ) (a : A) :
    sectionsHom (ofSpfMap φ hφ) a = (Spf.topSectionsIso B).inv (φ a) :=
  (ConcreteCategory.congr_hom (Spf.topSectionsIso B).hom_inv_id _).symm.trans <|
    congrArg _ (topSectionsIso_hom_sectionsHom_ofSpfMap φ hφ a)

/-- Precomposing `f : X ⟶ ofSpf A` with `X.ofRestrict U` restricts `sectionsHom f` to `U`. -/
theorem sectionsHom_ofRestrict_comp_apply (f : X ⟶ ofSpf A) (U : Opens X) (a : A) :
    sectionsHom (X.ofRestrict U ≫ f) a = (X.toLocallyRingedSpace.restrictTopSectionsIso U).hom
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
  exact @Continuous.comp _ _ _ ‹TopologicalSpace A› tTop (X.sectionsTopology U hU) _ _
    (sectionMap_continuous f (isAffineOpen_top_ofSpf A) hU fun _ _ ↦ trivial)
    ((Spf.topSectionsIso A).commRingCatIsoToRingEquiv.toEquiv.isHomeomorph_iff.mp
      (isHomeomorph_topSectionsIso A)).2

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
    sectionsHom (chartHom φ hφ U hU) a = (X.toLocallyRingedSpace.restrictTopSectionsIso U).hom
      (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op (φ a)) := by
  dsimp only [chartHom]; rw [sectionsHom_comp_apply]
  -- Unfold `hU.Sections` to `X.presheaf.obj (op U)`.
  erw [sectionsHom_ofSpfMap_apply (B := hU.Sections)]
  exact ConcreteCategory.congr_hom (topSectionsIso_inv_isoSpf_hom_c_app_top hU) _

private theorem hom_ofSpf_ext_of_isAffineOpen {U : Opens X} (hU : X.IsAffineOpen U)
    {g₁ g₂ : X.restrict U ⟶ ofSpf A} (h : sectionsHom g₁ = sectionsHom g₂) : g₁ = g₂ :=
  (cancel_epi hU.isoSpf.inv).mp <| fullyFaithfulForgetToLocallyRingedSpace.map_injective <|
    Spf.sectionsHom_injective (B := hU.Sections) <| RingHom.ext fun a ↦ by
      rw [← topSectionsIso_hom_sectionsHom_ofSpf, ← topSectionsIso_hom_sectionsHom_ofSpf,
        sectionsHom_comp_apply, sectionsHom_comp_apply, h]

private theorem restrictHomOfLE_chartHom {W U : Opens X} (hW : X.IsAffineOpen W)
    (hU : X.IsAffineOpen U) (hWU : W ≤ U) :
    X.restrictHomOfLE hWU ≫ chartHom φ hφ U hU = chartHom φ hφ W hW := by
  refine hom_ofSpf_ext_of_isAffineOpen hW (RingHom.ext fun a ↦ ?_)
  rw [sectionsHom_comp_apply, sectionsHom_chartHom, sectionsHom_chartHom,
    forgetToLocallyRingedSpace_map_restrictHomOfLE]
  -- Unfold `ConcreteCategory.comp_apply` across `restrictTopSectionsIso`.
  erw [ConcreteCategory.congr_hom
    (X.toLocallyRingedSpace.restrictTopSectionsIso_hom_restrictHomOfLE_c_app_top hWU)]
  exact congrArg _ (ConcreteCategory.congr_hom
    (X.presheaf.map_comp (homOfLE (le_top : U ≤ ⊤)).op (homOfLE hWU).op).symm (φ a))

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
noncomputable def homOfContinuousOnAffines : X ⟶ ofSpf A :=
  glueMorphisms (fun U : {U : Opens X // X.IsAffineOpen U} ↦ U.1) (iSup_affineOpens_eq_top X)
    (fun U ↦ chartHom φ hφ U.1 U.2) (chartHom_overlap φ hφ)

@[simp] theorem ofRestrict_homOfContinuousOnAffines (U : Opens X) (hU : X.IsAffineOpen U) :
    X.ofRestrict U ≫ homOfContinuousOnAffines φ hφ = hU.isoSpf.hom ≫ ofSpfMap (B := hU.Sections)
      ((X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom.comp φ) (hφ.continuous_comp U hU) :=
  ofRestrict_glueMorphisms _ (iSup_affineOpens_eq_top X) _ (chartHom_overlap φ hφ) ⟨U, hU⟩

@[simp] theorem homOfContinuousOnAffines_sectionsHom (f : X ⟶ ofSpf A) :
    homOfContinuousOnAffines (sectionsHom f) (continuousOnAffines_sectionsHom f) = f :=
  hom_ext_of_ofRestrict (fun U : {U : Opens X // X.IsAffineOpen U} ↦ U.1)
    (iSup_affineOpens_eq_top X) fun U ↦ (ofRestrict_homOfContinuousOnAffines _ _ U.1 U.2).trans <|
      hom_ofSpf_ext_of_isAffineOpen U.2 (RingHom.ext fun a ↦
        (sectionsHom_chartHom (sectionsHom f) (continuousOnAffines_sectionsHom f) U.1 U.2 a).trans
          (sectionsHom_ofRestrict_comp_apply f U.1 a).symm)

@[simp] theorem sectionsHom_homOfContinuousOnAffines :
    sectionsHom (homOfContinuousOnAffines φ hφ) = φ := by
  ext a; refine X.toLocallyRingedSpace.IsSheaf.section_ext fun x _ ↦ ?_
  obtain ⟨U, hU, hx⟩ := X.exists_isAffineOpen_mem x
  refine ⟨U, le_top, hx, (ConcreteCategory.bijective_of_isIso
    (X.toLocallyRingedSpace.restrictTopSectionsIso U).hom).injective ?_⟩
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
end HomSpfCorrespondence
end TauCeti.FormalScheme
