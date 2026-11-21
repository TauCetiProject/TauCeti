/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.FormalScheme.SectionsTopology

import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
import TauCeti.Geometry.RingedSpace.LocallyRingedSpace.Sections

/-!
# Morphisms of formal schemes, morphisms into `Spf A`, and automatic continuity

For a formal scheme `X` and an adic ring `A` of finite ideal type, this module establishes gluing
of morphisms, the residue-field criterion for continuity on affine formal opens, the bijection
`(X ⟶ ofSpf A) ≃ { φ : A →+* Γ(X, O_X) // ContinuousOnAffines X A φ }` (EGA I, Ch. I, 10.4.6),
and automatic continuity of every morphism of formal schemes on rings of sections for
`sheafSectionsTopology` (EGA I, Ch. I, 10.4.5).

## Main definitions

* `TauCeti.FormalScheme.restrictHomOfLE`, `TauCeti.FormalScheme.glueMorphisms`: open-subscheme
  inclusions and unique gluing of compatible morphisms over an open cover.
* `TauCeti.FormalScheme.ContinuousOnAffines`, `TauCeti.FormalScheme.sectionsHom`,
  `TauCeti.FormalScheme.homSpfEquiv`: continuity on affine formal opens, global-sections
  homomorphism, and the morphism correspondence into `Spf A`.

## Main results

* `TauCeti.FormalScheme.continuousOnAffines_iff_continuous_sheafSectionsTopology`,
  `TauCeti.FormalScheme.continuousOnAffines_iff_residue`: equivalences with `sheafSectionsTopology`
  and vanishing of an ideal of definition in every residue field.
* `TauCeti.FormalScheme.continuous_c_app_of_isAffineOpen`,
  `TauCeti.FormalScheme.continuous_c_app`: automatic continuity on rings of sections.

## References

* A. Grothendieck and J. Dieudonné, *Éléments de géométrie algébrique I*, Ch. I, 10.4.5–10.4.6.
* [Stacks Project, Tag 0AHY](https://stacks.math.columbia.edu/tag/0AHY).
-/

public section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry Topology

namespace TauCeti.FormalScheme

universe u

section Gluing

/-- For opens `V ≤ W` of a formal scheme `X`, the inclusion `X|_V ⟶ X|_W` of open formal
subschemes. -/
noncomputable def restrictHomOfLE (X : FormalScheme.{u}) {V W : Opens X} (h : V ≤ W) :
    X.restrict V ⟶ X.restrict W :=
  InducedCategory.homMk (X.toLocallyRingedSpace.restrictHomOfLE h)

/-- Composing `X|_V ⟶ X|_W` with `X|_W ⟶ X` gives `X|_V ⟶ X`. -/
@[reassoc (attr := simp)]
theorem restrictHomOfLE_ofRestrict (X : FormalScheme.{u}) {V W : Opens X} (h : V ≤ W) :
    X.restrictHomOfLE h ≫ X.ofRestrict W = X.ofRestrict V := InducedCategory.hom_ext <| by
  rw [InducedCategory.comp_hom, ← forgetToLocallyRingedSpace_map (X.ofRestrict W),
    ← forgetToLocallyRingedSpace_map (X.ofRestrict V),
    forgetToLocallyRingedSpace_map_ofRestrict, forgetToLocallyRingedSpace_map_ofRestrict]
  exact X.toLocallyRingedSpace.restrictHomOfLE_ofRestrict h

/-- The inclusion of an open formal subscheme into itself is the identity. -/
@[simp]
theorem restrictHomOfLE_refl (X : FormalScheme.{u}) (V : Opens X) :
    X.restrictHomOfLE (le_refl V) = 𝟙 (X.restrict V) :=
  InducedCategory.hom_ext (X.toLocallyRingedSpace.restrictHomOfLE_refl V)

/-- Inclusions of open formal subschemes compose functorially. -/
@[reassoc (attr := simp)]
theorem restrictHomOfLE_comp (X : FormalScheme.{u}) {U V W : Opens X} (h : U ≤ V) (k : V ≤ W) :
    X.restrictHomOfLE h ≫ X.restrictHomOfLE k = X.restrictHomOfLE (h.trans k) :=
  InducedCategory.hom_ext (X.toLocallyRingedSpace.restrictHomOfLE_comp h k)

/-- Glue a family of formal-scheme morphisms `f i : X|_{U i} ⟶ Y` over an open cover
`⨆ i, U i = ⊤` that agree on pairwise intersections `U i ⊓ U j`. -/
noncomputable def glueMorphisms {X Y : FormalScheme.{u}} {ι : Type*}
    (U : ι → Opens X) (hU : ⨆ i, U i = ⊤) (f : ∀ i, X.restrict (U i) ⟶ Y)
    (hcompat : ∀ i j,
      X.restrictHomOfLE (inf_le_left : U i ⊓ U j ≤ U i) ≫ f i =
        X.restrictHomOfLE (inf_le_right : U i ⊓ U j ≤ U j) ≫ f j) :
    X ⟶ Y :=
  InducedCategory.homMk <|
    X.toLocallyRingedSpace.glueMorphisms U hU (fun i ↦ (f i).hom) fun i j ↦
      X.toLocallyRingedSpace.pullback_fst_comp_eq_of_restrictHomOfLE
        (congrArg InducedCategory.Hom.hom (hcompat i j))

/-- Restricting the glued morphism to `U i` recovers `f i`. -/
@[reassoc (attr := simp)]
theorem ofRestrict_glueMorphisms {X Y : FormalScheme.{u}} {ι : Type*}
    (U : ι → Opens X) (hU : ⨆ i, U i = ⊤) (f : ∀ i, X.restrict (U i) ⟶ Y)
    (hcompat : ∀ i j,
      X.restrictHomOfLE (inf_le_left : U i ⊓ U j ≤ U i) ≫ f i =
        X.restrictHomOfLE (inf_le_right : U i ⊓ U j ≤ U j) ≫ f j)
    (i : ι) :
    X.ofRestrict (U i) ≫ glueMorphisms U hU f hcompat = f i := InducedCategory.hom_ext <| by
  rw [InducedCategory.comp_hom, ← forgetToLocallyRingedSpace_map (X.ofRestrict (U i)),
    forgetToLocallyRingedSpace_map_ofRestrict]
  exact X.toLocallyRingedSpace.ofRestrict_glueMorphisms U hU _ _ i

/-- Two morphisms of formal schemes that agree on every member of an open cover are equal. -/
theorem hom_ext_of_ofRestrict {X Y : FormalScheme.{u}} {ι : Type*}
    (U : ι → Opens X) (hU : ⨆ i, U i = ⊤) {f g : X ⟶ Y}
    (h : ∀ i, X.ofRestrict (U i) ≫ f = X.ofRestrict (U i) ≫ g) :
    f = g :=
  InducedCategory.hom_ext <| X.toLocallyRingedSpace.hom_ext_of_ofRestrict U hU fun i ↦ by
    have hi := congrArg InducedCategory.Hom.hom (h i)
    rwa [InducedCategory.comp_hom, InducedCategory.comp_hom,
      ← forgetToLocallyRingedSpace_map (X.ofRestrict (U i)),
      forgetToLocallyRingedSpace_map_ofRestrict] at hi

private theorem iSup_affineOpens (X : FormalScheme.{u}) :
    (⨆ U : { U : Opens X // X.IsAffineOpen U }, U.1) = ⊤ := by
  ext x; refine ⟨fun _ ↦ trivial, fun _ ↦ ?_⟩
  obtain ⟨U, hU, hxU, -⟩ := (Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens) (trivial : x ∈ ⊤)
  exact Opens.mem_iSup.mpr ⟨⟨U, hU⟩, hxU⟩

end Gluing

section ContinuousOnAffines

/-- A ring homomorphism `φ : A →+* Γ(X, O_X)` from a topological commutative ring `A` is
continuous on affine formal opens if for every affine formal open `U` of `X`, the composite
`A → Γ(X, O_X) → Γ(U, O_X)` is continuous for `sectionsTopology X U hU` (EGA I, Ch. I, 10.4.6). -/
def ContinuousOnAffines (X : FormalScheme.{u}) (A : Type*) [CommRing A] [TopologicalSpace A]
    (φ : A →+* X.presheaf.obj (op ⊤)) : Prop :=
  ∀ (U : Opens X) (hU : X.IsAffineOpen U),
    @Continuous _ _ _ (sectionsTopology X U hU) ((X.presheaf.map (homOfLE le_top).op) ∘ φ)

/-- Continuity on affine formal opens is equivalent to continuity for
`sheafSectionsTopology X ⊤`. -/
theorem continuousOnAffines_iff_continuous_sheafSectionsTopology (X : FormalScheme.{u})
    (A : Type*) [CommRing A] [TopologicalSpace A]
    (φ : A →+* X.presheaf.obj (op ⊤)) :
    ContinuousOnAffines X A φ ↔ @Continuous _ _ _ (sheafSectionsTopology X ⊤) φ := by
  rw [continuous_iff_sheafSectionsTopology]
  exact ⟨fun h W _ hW ↦ h W hW, fun h W hW ↦ h W le_top hW⟩

private theorem continuous_restrict_iff_residue_on_chart {X : FormalScheme.{u}}
    {A : Type*} {B : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsAdicRing A]
    [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsAdicRing B]
    {I : Ideal A} (hI : IsAdic I) {U : Opens X} (hU : X.IsAffineOpen U)
    (e : X.toLocallyRingedSpace.restrict U.isOpenEmbedding ≅ Spf B)
    (φ : A →+* X.presheaf.obj (op ⊤)) :
    @Continuous _ _ _ (sectionsTopology X U hU) ((X.presheaf.map (homOfLE le_top).op) ∘ φ) ↔
      ∀ a ∈ I, ∀ q : Spf.carrier B,
        X.toLocallyRingedSpace.Γevaluation
          ((e.inv ≫ X.toLocallyRingedSpace.ofRestrict U.isOpenEmbedding).base q) (φ a) = 0 := by
  let j := e.inv ≫ X.toLocallyRingedSpace.ofRestrict U.isOpenEmbedding
  let ψ := (sectionsIsoOfIsoSpf e).hom.hom.comp ((X.presheaf.map (homOfLE le_top).op).hom.comp φ)
  have hcont_iff :
      @Continuous _ _ _ (sectionsTopology X U hU) ((X.presheaf.map (homOfLE le_top).op) ∘ φ) ↔
        Continuous ψ := by
    let _ := sectionsTopology X U hU
    exact (isHomeomorph_sectionsIsoOfIsoSpf hU e).isInducing.continuous_iff
  rw [hcont_iff, hI.continuous_iff_map_le_radical (IsAdicRing.ideal_spec B).2.1
    (IsAdicRing.ideal_spec A).2.1 (IsAdicRing.ideal_spec A).1, Ideal.map_le_iff_le_comap]
  have hj_app (a : A) : j.c.app (op ⊤) (φ a) = (Spf.globalSectionsIsoOfIsAdicRing B).inv (ψ a) :=
    ConcreteCategory.congr_hom
      ((Iso.eq_comp_inv (Spf.globalSectionsIsoOfIsAdicRing B)).mpr (chartImmersion_c_app_top e))
      (φ a)
  refine ⟨fun h a ha q ↦ ?_, fun h a ha ↦ ?_⟩
  · have hzero := (Spf.mem_radical_iff_forall_Γevaluation_eq_zero
      (IsAdicRing.ideal_spec B).2.1 (ψ a)).mp (h ha) q
    let q' : Spf B := q
    rw [← map_eq_zero_iff (LocallyRingedSpace.residueFieldMap j q').hom
      (LocallyRingedSpace.residueFieldMap j q').hom.injective]
    -- `Spf B` and `Spf.carrier B` agree definitionally (`q' = q`),
    -- matching `Γevaluation_naturality_apply`.
    change (LocallyRingedSpace.residueFieldMap j q')
      (X.toLocallyRingedSpace.Γevaluation (j.base q') (φ a)) = 0
    rw [LocallyRingedSpace.Γevaluation_naturality_apply j q' (φ a), hj_app a]; exact hzero
  · refine (Spf.mem_radical_iff_forall_Γevaluation_eq_zero (IsAdicRing.ideal_spec B).2.1
      (ψ a)).mpr fun q ↦ ?_
    let q' : Spf B := q
    -- `Spf B` and `Spf.carrier B` agree definitionally (`q' = q`).
    change (Spf B).Γevaluation q' ((Spf.globalSectionsIsoOfIsAdicRing B).inv (ψ a)) = 0
    rw [← hj_app a, ← LocallyRingedSpace.Γevaluation_naturality_apply j q' (φ a),
      h a ha q, map_zero]

/-- **Residue-field criterion for continuity on affine formal opens** (EGA I, Ch. I, 10.4.6):
for any ideal of definition `I` of `A`, a ring homomorphism `φ : A →+* Γ(X, O_X)` is continuous on
all affine formal opens of `X` if and only if `φ a` vanishes in the residue field `κ(x)` for every
`a ∈ I` and every point `x : X`. -/
theorem continuousOnAffines_iff_residue {X : FormalScheme.{u}}
    {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsAdicRing A]
    {I : Ideal A} (hI : IsAdic I) (φ : A →+* X.presheaf.obj (op ⊤)) :
    ContinuousOnAffines X A φ ↔
      ∀ a ∈ I, ∀ x : X, X.toLocallyRingedSpace.Γevaluation x (φ a) = 0 := by
  refine ⟨fun hφ a ha x ↦ ?_, fun hres U hU ↦ ?_⟩
  · obtain ⟨U, hU, hxU, -⟩ := (Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens) (trivial : x ∈ ⊤)
    obtain ⟨B, _, _, _, _, ⟨e⟩⟩ := (X.isAffineOpen_iff U).mp hU
    have hres := (continuous_restrict_iff_residue_on_chart hI hU e φ).mp (hφ U hU) a ha
      (e.hom.base ⟨x, hxU⟩)
    have hpt : (e.inv ≫ X.toLocallyRingedSpace.ofRestrict U.isOpenEmbedding).base
        (e.hom.base ⟨x, hxU⟩) = x := by
      have hid := ConcreteCategory.congr_hom (congrArg (fun m ↦ m.base) e.hom_inv_id) ⟨x, hxU⟩
      exact congrArg Subtype.val hid
    rwa [hpt] at hres
  · obtain ⟨B, _, _, _, _, ⟨e⟩⟩ := (X.isAffineOpen_iff U).mp hU
    exact (continuous_restrict_iff_residue_on_chart hI hU e φ).mpr fun a ha _ ↦ hres a ha _

end ContinuousOnAffines

section SpfMorphismCorrespondence

/-- The global-sections ring homomorphism `A →+* Γ(X, O_X)` induced by a morphism
`f : X ⟶ ofSpf A`. -/
noncomputable def sectionsHom {X : FormalScheme.{u}}
    {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsAdicRing A]
    (f : X ⟶ ofSpf A) : A →+* X.presheaf.obj (op ⊤) :=
  ((Spf.globalSectionsIsoOfIsAdicRing A).inv ≫ f.hom.c.app (op ⊤)).hom

/-- Functoriality of `FormalScheme.sectionsHom` under precomposition. -/
theorem sectionsHom_comp {Y X : FormalScheme.{u}}
    {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsAdicRing A]
    (g : Y ⟶ X) (f : X ⟶ ofSpf A) :
    sectionsHom (g ≫ f) = (g.hom.c.app (op ⊤)).hom.comp (sectionsHom f) := by
  ext a; rfl

/-- On an affine formal scheme `ofSpf B`, `FormalScheme.sectionsHom` followed by
`Spf.globalSectionsIso` equals `Spf.sectionsHom`. -/
theorem globalSectionsIso_comp_sectionsHom {A B : Type u}
    [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsAdicRing A]
    [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsAdicRing B]
    (f : ofSpf B ⟶ ofSpf A) :
    ((Spf.globalSectionsIsoOfIsAdicRing B).hom.hom).comp (sectionsHom f) =
      Spf.sectionsHom f.hom :=
  congrArg CommRingCat.Hom.hom <|
    (congrArg ((Spf.globalSectionsIsoOfIsAdicRing A).inv ≫ ·)
        (Spf.c_app_top_comp_globalSectionsIso_hom f.hom)).trans
      (Iso.inv_hom_id_assoc (Spf.globalSectionsIsoOfIsAdicRing A) _)

private theorem sectionsHom_chart_comp {X : FormalScheme.{u}}
    {A B : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsAdicRing A]
    [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsAdicRing B]
    (f : X ⟶ ofSpf A) {U : Opens X}
    (e : X.toLocallyRingedSpace.restrict U.isOpenEmbedding ≅ Spf B) :
    Spf.sectionsHom (e.inv ≫ X.toLocallyRingedSpace.ofRestrict U.isOpenEmbedding ≫ f.hom) =
      (sectionsIsoOfIsoSpf e).hom.hom.comp
        ((X.presheaf.map (homOfLE le_top).op).hom.comp (sectionsHom f)) := by
  let f' : X.toLocallyRingedSpace ⟶ Spf A := f.hom
  let j := e.inv ≫ X.toLocallyRingedSpace.ofRestrict U.isOpenEmbedding
  have hcomp : (j ≫ f').c.app (op ⊤) ≫ (Spf.globalSectionsIsoOfIsAdicRing B).hom =
      f'.c.app (op ⊤) ≫ X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op ≫
        (sectionsIsoOfIsoSpf e).hom :=
    CommRingCat.hom_ext <| RingHom.ext fun s ↦
      ConcreteCategory.congr_hom (chartImmersion_c_app_top e) (f'.c.app (op ⊤) s)
  have heq : CommRingCat.ofHom (Spf.sectionsHom (j ≫ f')) =
      (Spf.globalSectionsIsoOfIsAdicRing A).inv ≫ f'.c.app (op ⊤) ≫
        X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op ≫ (sectionsIsoOfIsoSpf e).hom :=
    (Iso.inv_hom_id_assoc (Spf.globalSectionsIsoOfIsAdicRing A) _).symm.trans
      (congrArg ((Spf.globalSectionsIsoOfIsAdicRing A).inv ≫ ·)
        ((Spf.c_app_top_comp_globalSectionsIso_hom (j ≫ f')).symm.trans hcomp))
  have hassoc : (e.inv ≫ X.toLocallyRingedSpace.ofRestrict U.isOpenEmbedding ≫ f.hom :
      Spf B ⟶ Spf A) = j ≫ f' := (Category.assoc _ _ _).symm
  -- `erw`: `ofSpf A` unfolds definitionally to `Spf A`.
  erw [hassoc]
  exact congrArg CommRingCat.Hom.hom heq

/-- For every morphism `f : X ⟶ ofSpf A`, the global-sections homomorphism `sectionsHom f` is
continuous on every affine formal open of `X`. -/
theorem continuousOnAffines_sectionsHom {X : FormalScheme.{u}}
    {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsAdicRing A]
    (f : X ⟶ ofSpf A) :
    ContinuousOnAffines X A (sectionsHom f) := fun U hU ↦ by
  obtain ⟨B, _, _, _, _, ⟨e⟩⟩ := (X.isAffineOpen_iff U).mp hU
  let _ : TopologicalSpace (X.presheaf.obj (op U)) := sectionsTopology X U hU
  have hfun : ((sectionsIsoOfIsoSpf e).hom : _ → _) ∘
        ((X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op) ∘ (sectionsHom f)) =
      Spf.sectionsHom (e.inv ≫ X.toLocallyRingedSpace.ofRestrict U.isOpenEmbedding ≫ f.hom) :=
    funext fun a ↦ (RingHom.congr_fun (sectionsHom_chart_comp f e) a).symm
  rw [(isHomeomorph_sectionsIsoOfIsoSpf hU e).isInducing.continuous_iff, hfun]
  exact Spf.continuous_sectionsHom _

/-- Two morphisms `X ⟶ ofSpf A` with the same global-sections homomorphism are equal. -/
theorem hom_ext_of_sectionsHom_eq {X : FormalScheme.{u}}
    {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsAdicRing A]
    {f g : X ⟶ ofSpf A} (h : sectionsHom f = sectionsHom g) :
    f = g := by
  refine hom_ext_of_ofRestrict (fun U : { U : Opens X // X.IsAffineOpen U } ↦ U.1)
    (iSup_affineOpens X) fun ⟨U, hU⟩ ↦ InducedCategory.hom_ext ?_
  obtain ⟨B, _, _, _, _, ⟨e⟩⟩ := (X.isAffineOpen_iff U).mp hU
  have h1 : X.toLocallyRingedSpace.ofRestrict U.isOpenEmbedding ≫ f.hom =
      X.toLocallyRingedSpace.ofRestrict U.isOpenEmbedding ≫ g.hom := by
    rw [← cancel_epi e.inv]
    exact Spf.hom_ext_of_sectionsHom_eq <|
      (sectionsHom_chart_comp f e).trans (by rw [h]; exact (sectionsHom_chart_comp g e).symm)
  rw [InducedCategory.comp_hom, InducedCategory.comp_hom,
    ← forgetToLocallyRingedSpace_map (X.ofRestrict U),
    forgetToLocallyRingedSpace_map_ofRestrict]; exact h1

private noncomputable def localHomOfChart {X : FormalScheme.{u}}
    {A B : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsAdicRing A]
    [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsAdicRing B]
    (φ : A →+* X.presheaf.obj (op ⊤)) (hφ : ContinuousOnAffines X A φ)
    {U : Opens X} (hU : X.IsAffineOpen U)
    (e : X.toLocallyRingedSpace.restrict U.isOpenEmbedding ≅ Spf B) :
    X.restrict U ⟶ ofSpf A :=
  let ψ := (sectionsIsoOfIsoSpf e).hom.hom.comp ((X.presheaf.map (homOfLE le_top).op).hom.comp φ)
  have hψ : Continuous ψ := by
    let _ : TopologicalSpace (X.presheaf.obj (op U)) := sectionsTopology X U hU
    exact (isHomeomorph_sectionsIsoOfIsoSpf hU e).isInducing.continuous_iff.mp (hφ U hU)
  InducedCategory.homMk (e.hom ≫ Spf.map ψ hψ)

private theorem sectionsHom_localHomOfChart {X : FormalScheme.{u}}
    {A B : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsAdicRing A]
    [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsAdicRing B]
    (φ : A →+* X.presheaf.obj (op ⊤)) (hφ : ContinuousOnAffines X A φ)
    {U : Opens X} (hU : X.IsAffineOpen U)
    (e : X.toLocallyRingedSpace.restrict U.isOpenEmbedding ≅ Spf B) :
    sectionsHom (localHomOfChart φ hφ hU e) =
      ((X.toLocallyRingedSpace.ofRestrict U.isOpenEmbedding).c.app (op ⊤)).hom.comp φ := by
  let ψ := (sectionsIsoOfIsoSpf e).hom.hom.comp ((X.presheaf.map (homOfLE le_top).op).hom.comp φ)
  have hψ : Continuous ψ := by
    let _ : TopologicalSpace (X.presheaf.obj (op U)) := sectionsTopology X U hU
    exact (isHomeomorph_sectionsIsoOfIsoSpf hU e).isInducing.continuous_iff.mp (hφ U hU)
  have hmap : (Spf.globalSectionsIsoOfIsAdicRing A).inv ≫ (Spf.map ψ hψ).c.app (op ⊤) ≫
        (Spf.globalSectionsIsoOfIsAdicRing B).hom = CommRingCat.ofHom ψ :=
    (congrArg ((Spf.globalSectionsIsoOfIsAdicRing A).inv ≫ ·)
      (Spf.c_app_top_comp_globalSectionsIso_hom (Spf.map ψ hψ))).trans
      ((Iso.inv_hom_id_assoc (Spf.globalSectionsIsoOfIsAdicRing A) _).trans
        (by rw [Spf.sectionsHom_map]))
  ext a
  apply (LocallyRingedSpace.Γ.mapIso e.symm.op ≪≫
    Spf.globalSectionsIsoOfIsAdicRing B).commRingCatIsoToRingEquiv.injective
  have h1 : (LocallyRingedSpace.Γ.mapIso e.symm.op ≪≫ Spf.globalSectionsIsoOfIsAdicRing B).hom
        (sectionsHom (localHomOfChart φ hφ hU e) a) = ψ a := by
    have hc := ConcreteCategory.congr_hom
      (LocallyRingedSpace.comp_c_app e.hom (Spf.map ψ hψ) (op ⊤))
      ((Spf.globalSectionsIsoOfIsAdicRing A).inv a)
    have hee := ConcreteCategory.congr_hom (LocallyRingedSpace.Γ.mapIso e.symm.op).inv_hom_id
      ((Spf.map ψ hψ).c.app (op ⊤) ((Spf.globalSectionsIsoOfIsAdicRing A).inv a))
    -- `erw`: unfold `sectionsHom`, `localHomOfChart`, and `Γ.mapIso` to match `hc` and `hee`.
    erw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, hc, hee]
    exact ConcreteCategory.congr_hom hmap a
  exact h1.trans (ConcreteCategory.congr_hom (chartImmersion_c_app_top e) (φ a)).symm

private noncomputable def chosenLocalHom {X : FormalScheme.{u}}
    {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsAdicRing A]
    (φ : A →+* X.presheaf.obj (op ⊤)) (hφ : ContinuousOnAffines X A φ)
    {U : Opens X} (hU : X.IsAffineOpen U) :
    { f : X.restrict U ⟶ ofSpf A //
      sectionsHom f =
        ((X.toLocallyRingedSpace.ofRestrict U.isOpenEmbedding).c.app (op ⊤)).hom.comp φ } :=
  Classical.choice (by
    obtain ⟨B, _, _, _, _, ⟨e⟩⟩ := (X.isAffineOpen_iff U).mp hU
    exact ⟨⟨localHomOfChart φ hφ hU e, sectionsHom_localHomOfChart φ hφ hU e⟩⟩)

/-- Construct the morphism `X ⟶ ofSpf A` associated to a ring homomorphism `φ : A →+* Γ(X, O_X)`
continuous on affine formal opens, by gluing local morphisms over the affine formal cover of `X`. -/
noncomputable def homOfContinuousOnAffines {X : FormalScheme.{u}}
    {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsAdicRing A]
    (φ : A →+* X.presheaf.obj (op ⊤)) (hφ : ContinuousOnAffines X A φ) :
    X ⟶ ofSpf A := by
  refine glueMorphisms (fun U : { U : Opens X // X.IsAffineOpen U } ↦ U.1) (iSup_affineOpens X)
    (fun i ↦ (chosenLocalHom φ hφ i.2).1) fun i j ↦ hom_ext_of_sectionsHom_eq ?_
  rw [sectionsHom_comp, sectionsHom_comp, (chosenLocalHom φ hφ i.2).2, (chosenLocalHom φ hφ j.2).2]
  have hi := LocallyRingedSpace.comp_c_app
    (X.toLocallyRingedSpace.restrictHomOfLE (inf_le_left : i.1 ⊓ j.1 ≤ i.1))
    (X.toLocallyRingedSpace.ofRestrict i.1.isOpenEmbedding) (op ⊤)
  have hj := LocallyRingedSpace.comp_c_app
    (X.toLocallyRingedSpace.restrictHomOfLE (inf_le_right : i.1 ⊓ j.1 ≤ j.1))
    (X.toLocallyRingedSpace.ofRestrict j.1.isOpenEmbedding) (op ⊤)
  rw [LocallyRingedSpace.restrictHomOfLE_ofRestrict] at hi hj
  exact RingHom.ext fun a ↦
    (ConcreteCategory.congr_hom hi.symm (φ a)).trans (ConcreteCategory.congr_hom hj (φ a))

/-- Recovering `φ` by taking global sections of `homOfContinuousOnAffines φ hφ`. -/
@[simp]
theorem sectionsHom_homOfContinuousOnAffines {X : FormalScheme.{u}}
    {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsAdicRing A]
    (φ : A →+* X.presheaf.obj (op ⊤)) (hφ : ContinuousOnAffines X A φ) :
    sectionsHom (homOfContinuousOnAffines φ hφ) = φ := by
  ext a
  refine TopCat.Sheaf.eq_of_locally_eq' X.toLocallyRingedSpace.sheaf
    (fun U : { U : Opens X // X.IsAffineOpen U } ↦ U.1) ⊤ (fun _ ↦ homOfLE le_top)
    (le_of_eq (iSup_affineOpens X).symm) _ _ fun i ↦ ?_
  have hres : sectionsHom (X.ofRestrict i.1 ≫ homOfContinuousOnAffines φ hφ) =
      ((X.toLocallyRingedSpace.ofRestrict i.1.isOpenEmbedding).c.app (op ⊤)).hom.comp φ := by
    unfold homOfContinuousOnAffines
    rw [ofRestrict_glueMorphisms]; exact (chosenLocalHom φ hφ i.2).2
  have h1 := RingHom.congr_fun ((sectionsHom_comp (X.ofRestrict i.1) _).symm.trans hres) a
  dsimp only [RingHom.comp_apply] at h1
  rw [← forgetToLocallyRingedSpace_map (X.ofRestrict i.1),
    forgetToLocallyRingedSpace_map_ofRestrict] at h1
  have htop := Opens.isOpenEmbedding_obj_top i.1
  have hmap : (X.toLocallyRingedSpace.ofRestrict i.1.isOpenEmbedding).c.app (op ⊤) ≫
      X.presheaf.map (eqToHom (congrArg op htop)) = X.presheaf.map (homOfLE le_top).op := by
    -- `erw`: `ofRestrict.c.app` unfolds to `X.presheaf.map`.
    erw [← X.presheaf.map_comp]
    exact congrArg X.presheaf.map (Quiver.Hom.unop_inj (Subsingleton.elim _ _))
  exact (ConcreteCategory.congr_hom hmap _).symm.trans
    ((congrArg (X.presheaf.map (eqToHom (congrArg op htop))) h1).trans
      (ConcreteCategory.congr_hom hmap _))

/-- **Morphism correspondence into `Spf A`** (EGA I, Ch. I, 10.4.6): for any formal scheme `X`
and any adic ring `A` of finite ideal type, morphisms `X ⟶ ofSpf A` correspond bijectively via
global sections to ring homomorphisms `A →+* Γ(X, O_X)` that are continuous on every affine formal
open of `X` (equivalently, continuous for `sheafSectionsTopology X ⊤`). -/
noncomputable def homSpfEquiv (X : FormalScheme.{u})
    (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsAdicRing A] :
    (X ⟶ ofSpf A) ≃ { φ : A →+* X.presheaf.obj (op ⊤) // ContinuousOnAffines X A φ } where
  toFun f := ⟨sectionsHom f, continuousOnAffines_sectionsHom f⟩
  invFun φ := homOfContinuousOnAffines φ.1 φ.2
  left_inv _ := hom_ext_of_sectionsHom_eq (sectionsHom_homOfContinuousOnAffines _ _)
  right_inv φ := Subtype.ext (sectionsHom_homOfContinuousOnAffines φ.1 φ.2)

/-- The forward direction of `homSpfEquiv` sends a morphism to `sectionsHom`. -/
@[simp]
theorem homSpfEquiv_apply_val {X : FormalScheme.{u}}
    {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsAdicRing A]
    (f : X ⟶ ofSpf A) : (homSpfEquiv X A f).1 = sectionsHom f := (rfl)

/-- The inverse of `homSpfEquiv` is `homOfContinuousOnAffines`. -/
@[simp]
theorem homSpfEquiv_symm_apply {X : FormalScheme.{u}}
    {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsAdicRing A]
    (φ : { φ : A →+* X.presheaf.obj (op ⊤) // ContinuousOnAffines X A φ }) :
    (homSpfEquiv X A).symm φ = homOfContinuousOnAffines φ.1 φ.2 := (rfl)

end SpfMorphismCorrespondence

section AutomaticContinuity

private theorem exists_spfLift_sectionsIsoOfIsoSpf {X Y : FormalScheme.{u}} (f : X ⟶ Y)
    {V : Opens Y} {U : Opens X} (hUV : U ≤ (Opens.map f.hom.base).obj V)
    {A B : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsAdicRing A]
    [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsAdicRing B]
    (eV : Y.toLocallyRingedSpace.restrict V.isOpenEmbedding ≅ Spf A)
    (eU : X.toLocallyRingedSpace.restrict U.isOpenEmbedding ≅ Spf B) :
    ∃ g : Spf B ⟶ Spf A,
      (f.hom.c.app (op V) ≫ X.presheaf.map (homOfLE hUV).op) ≫ (sectionsIsoOfIsoSpf eU).hom =
        (sectionsIsoOfIsoSpf eV).hom ≫ CommRingCat.ofHom (Spf.sectionsHom g) := by
  let jU := eU.inv ≫ X.toLocallyRingedSpace.ofRestrict U.isOpenEmbedding
  let jV := eV.inv ≫ Y.toLocallyRingedSpace.ofRestrict V.isOpenEmbedding
  have hrange : Set.range (jU ≫ f.hom).base ⊆ Set.range jV.base := by
    rintro _ ⟨q, rfl⟩
    have hid := ConcreteCategory.congr_hom (congrArg (fun m ↦ m.base) eV.hom_inv_id)
      ⟨(jU ≫ f.hom).base q, hUV (eU.inv.base q).2⟩
    exact ⟨eV.hom.base ⟨(jU ≫ f.hom).base q, hUV (eU.inv.base q).2⟩, congrArg Subtype.val hid⟩
  let g := LocallyRingedSpace.IsOpenImmersion.lift jV (jU ≫ f.hom) hrange
  have hg : g ≫ jV = jU ≫ f.hom := LocallyRingedSpace.IsOpenImmersion.lift_fac _ _ hrange
  have hpreV : (Opens.map jV.base).obj V = ⊤ := eq_top_iff.mpr fun p _ ↦ (eV.inv.base p).2
  have hpreB : (Opens.map (g ≫ jV).base).obj V = ⊤ :=
    eq_top_iff.mpr fun q _ ↦ (eV.inv.base (g.base q)).2
  have hpreU : (Opens.map jU.base).obj ((Opens.map f.hom.base).obj V) = ⊤ :=
    eq_top_iff.mpr fun q _ ↦ hUV (eU.inv.base q).2
  have hleft : (g ≫ jV).c.app (op V) ≫ (Spf B).presheaf.map (eqToHom (congrArg op hpreB)) ≫
      (Spf.globalSectionsIsoOfIsAdicRing B).hom =
      (sectionsIsoOfIsoSpf eV).hom ≫ CommRingCat.ofHom (Spf.sectionsHom g) := by
    have hfac := ConcreteCategory.congr_hom
      (LocallyRingedSpace.comp_c_app_comp_eqToHom_of_map_eq_top g jV hpreV hpreB)
    refine CommRingCat.hom_ext <| RingHom.ext fun s ↦ ?_
    have hc := ConcreteCategory.congr_hom (chartImmersion_c_app (X := Y) (le_refl V) eV) s
    -- `erw`: `ConcreteCategory.hom` composition and `pushforward` evaluate pointwise.
    erw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, hfac s,
      ConcreteCategory.comp_apply, ConcreteCategory.comp_apply,
      ConcreteCategory.congr_hom (Spf.c_app_top_comp_globalSectionsIso_hom g),
      ConcreteCategory.comp_apply]
    -- `erw`: expand composition on `hc` to match `sectionsIsoOfIsoSpf eV`.
    erw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at hc
    exact congrArg (Spf.sectionsHom g)
      (hc.trans (congrArg _ (ConcreteCategory.congr_hom (Y.presheaf.map_id (op V)) s)))
  have hright : (jU ≫ f.hom).c.app (op V) ≫ (Spf B).presheaf.map (eqToHom (congrArg op hpreU)) ≫
      (Spf.globalSectionsIsoOfIsAdicRing B).hom =
      (f.hom.c.app (op V) ≫ X.presheaf.map (homOfLE hUV).op) ≫ (sectionsIsoOfIsoSpf eU).hom :=
    CommRingCat.hom_ext <| RingHom.ext fun s ↦
      ConcreteCategory.congr_hom (by simpa using chartImmersion_c_app (X := X) hUV eU)
        (f.hom.c.app (op V) s)
  have heq : (g ≫ jV).c.app (op V) ≫ (Spf B).presheaf.map (eqToHom (congrArg op hpreB)) =
      (jU ≫ f.hom).c.app (op V) ≫ (Spf B).presheaf.map (eqToHom (congrArg op hpreU)) := by
    rw [PresheafedSpace.congr_app (congrArg LocallyRingedSpace.Hom.toHom hg) (op V), Category.assoc,
      ← (Spf B).presheaf.map_comp]
    exact congrArg _ (congrArg (Spf B).presheaf.map (Quiver.Hom.unop_inj (Subsingleton.elim _ _)))
  exact ⟨g, by rw [← hright, ← hleft, ← Category.assoc, ← Category.assoc, heq]⟩

/-- **Automatic continuity on affine formal opens** (EGA I, Ch. I, 10.4.5): for any morphism
`f : X ⟶ Y` of formal schemes and affine formal opens `V ⊆ Y` and `U ⊆ f⁻¹ V`, the induced
homomorphism `Γ(V, O_Y) → Γ(U, O_X)` is continuous for `sectionsTopology`. -/
theorem continuous_c_app_of_isAffineOpen {X Y : FormalScheme.{u}} (f : X ⟶ Y)
    {V : Opens Y} {U : Opens X} (hV : Y.IsAffineOpen V) (hU : X.IsAffineOpen U)
    (hUV : U ≤ (Opens.map f.hom.base).obj V) :
    @Continuous _ _ (sectionsTopology Y V hV) (sectionsTopology X U hU)
      (f.hom.c.app (op V) ≫ X.presheaf.map (homOfLE hUV).op) := by
  obtain ⟨A, _, _, _, _, ⟨eV⟩⟩ := (Y.isAffineOpen_iff V).mp hV
  obtain ⟨B, _, _, _, _, ⟨eU⟩⟩ := (X.isAffineOpen_iff U).mp hU
  obtain ⟨g, hcomm⟩ := exists_spfLift_sectionsIsoOfIsoSpf f hUV eV eU
  let _ := sectionsTopology Y V hV; let _ := sectionsTopology X U hU
  have hfun : ((sectionsIsoOfIsoSpf eU).hom : _ → _) ∘
        (f.hom.c.app (op V) ≫ X.presheaf.map (homOfLE hUV).op) =
      (Spf.sectionsHom g) ∘ (sectionsIsoOfIsoSpf eV).hom :=
    funext fun s ↦ ConcreteCategory.congr_hom hcomm s
  rw [(isHomeomorph_sectionsIsoOfIsoSpf hU eU).isInducing.continuous_iff, hfun]
  exact (Spf.continuous_sectionsHom g).comp (isHomeomorph_sectionsIsoOfIsoSpf hV eV).continuous

private theorem continuous_chart_pullback_top {X Y : FormalScheme.{u}} (f : X ⟶ Y)
    {V : Opens Y} {U : Opens X} (hUV : U ≤ (Opens.map f.hom.base).obj V)
    {B : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsAdicRing B]
    (eU : X.toLocallyRingedSpace.restrict U.isOpenEmbedding ≅ Spf B) :
    let g : Spf B ⟶ Y.toLocallyRingedSpace :=
      (eU.inv ≫ X.toLocallyRingedSpace.ofRestrict U.isOpenEmbedding) ≫ f.hom
    have hg_pre : (Opens.map g.base).obj V = ⊤ := by
      ext q; exact iff_true_intro (hUV (eU.inv.base q).2)
    @Continuous _ _ (sheafSectionsTopology Y V)
      (Spf.quotientSectionsTopology (IsAdicRing.ideal_spec B).2.1 ⊤)
      (g.c.app (op V) ≫ (Spf B).presheaf.map (eqToHom (congrArg op hg_pre))) := by
  intro g hg_pre
  have hnbhd (q : Spf.carrier B) : ∃ W : Opens Y, Y.IsAffineOpen W ∧ W ≤ V ∧
      ∃ b : B, q ∈ Spf.basicOpen b ∧ Spf.basicOpen b ≤ (Opens.map g.base).obj W := by
    obtain ⟨W, hW, hqW, hWV⟩ :=
      (Opens.isBasis_iff_nbhd.mp Y.isBasis_affineOpens) (hUV (eU.inv.base q).2)
    have hqW' : q ∈ (Opens.map g.base).obj W := hqW
    obtain ⟨_, ⟨b, rfl⟩, hqb, hbW⟩ := (Opens.isBasis_iff_nbhd.mp Spf.isBasis_basicOpen) hqW'
    exact ⟨W, hW, hWV, b, hqb, hbW⟩
  choose W hW hWV b hqb hbW using hnbhd
  let _ : TopologicalSpace (Y.presheaf.obj (op V)) := sheafSectionsTopology Y V
  refine Spf.continuous_quotientSectionsTopology_of_cover (IsAdicRing.ideal_spec B).2.1
    (fun _ ↦ le_top) (fun q _ ↦ Opens.mem_iSup.mpr ⟨q, hqb q⟩) _ fun q ↦ ?_
  have hcoord : (g.c.app (op V) ≫ (Spf B).presheaf.map (eqToHom (congrArg op hg_pre))) ≫
      (Spf B).presheaf.map (homOfLE (le_top : Spf.basicOpen (b q) ≤ ⊤)).op =
      Y.presheaf.map (homOfLE (hWV q)).op ≫ g.c.app (op (W q)) ≫
        (Spf B).presheaf.map (homOfLE (hbW q)).op := by
    have hm : (Spf B).presheaf.map (eqToHom (congrArg op hg_pre)) ≫
        (Spf B).presheaf.map (homOfLE (le_top : Spf.basicOpen (b q) ≤ ⊤)).op =
        ((TopCat.Presheaf.pushforward CommRingCat g.base).obj (Spf B).presheaf).map
          (homOfLE (hWV q)).op ≫ (Spf B).presheaf.map (homOfLE (hbW q)).op := by
      -- `erw`: `pushforward` functor map unfolds to `(Spf B).presheaf.map`.
      erw [← (Spf B).presheaf.map_comp, ← (Spf B).presheaf.map_comp]
      exact congrArg (Spf B).presheaf.map (Quiver.Hom.unop_inj (Subsingleton.elim _ _))
    rw [Category.assoc, hm, ← Category.assoc, ← g.c.naturality (homOfLE (hWV q)).op, Category.assoc]
  have hfun : (fun s : Y.presheaf.obj (op V) ↦
        (Spf B).presheaf.map (homOfLE (le_top : Spf.basicOpen (b q) ≤ ⊤)).op
          ((g.c.app (op V) ≫ (Spf B).presheaf.map (eqToHom (congrArg op hg_pre))) s)) =
      (g.c.app (op (W q)) ≫ (Spf B).presheaf.map (homOfLE (hbW q)).op) ∘
        (Y.presheaf.map (homOfLE (hWV q)).op) := funext (ConcreteCategory.congr_hom hcoord)
  -- `erw`: `(Spf B).presheaf` unfolds to `(Spf.structureSheaf _).obj`.
  erw [hfun]
  exact @Continuous.comp _ _ _ (sheafSectionsTopology Y V) (sectionsTopology Y (W q) (hW q))
    (Spf.quotientSectionsTopology (IsAdicRing.ideal_spec B).2.1 (Spf.basicOpen (b q))) _ _
    ((sectionsTopology_ofSpf_basicOpen B (b q)) ▸ continuous_c_app_of_isAffineOpen
      (InducedCategory.homMk g : ofSpf B ⟶ Y) (hW q) (isAffineOpen_basicOpen B (b q)) (hbW q))
    ((sheafSectionsTopology_eq_sectionsTopology Y (W q) (hW q)) ▸
      sheafSectionsTopology_restrict Y (hWV q))

/-- **Automatic continuity of formal-scheme morphisms** (EGA I, Ch. I, 10.4.5): every morphism
`f : X ⟶ Y` of formal schemes induces continuous ring homomorphisms
`Γ(V, O_Y) → Γ(f⁻¹ V, O_X)` for `sheafSectionsTopology` on every open `V ⊆ Y`. -/
theorem continuous_c_app {X Y : FormalScheme.{u}} (f : X ⟶ Y) (V : Opens Y) :
    @Continuous _ _ (sheafSectionsTopology Y V)
      (sheafSectionsTopology X ((Opens.map f.hom.base).obj V))
      (f.hom.c.app (op V)) := by
  let _ : TopologicalSpace (Y.presheaf.obj (op V)) := sheafSectionsTopology Y V
  refine (continuous_iff_sheafSectionsTopology X ((Opens.map f.hom.base).obj V) _).mpr
    fun U hUV hU ↦ ?_
  obtain ⟨B, _, _, _, _, ⟨eU⟩⟩ := (X.isAffineOpen_iff U).mp hU
  have := (IsAdicRing.ideal_spec B).2.2; let _ := sectionsTopology X U hU
  rw [(isHomeomorph_sectionsIsoOfIsoSpf hU eU).isInducing.continuous_iff]
  let g : Spf B ⟶ Y.toLocallyRingedSpace :=
    (eU.inv ≫ X.toLocallyRingedSpace.ofRestrict U.isOpenEmbedding) ≫ f.hom
  have hg_pre : (Opens.map g.base).obj V = ⊤ := by
    ext q; exact iff_true_intro (hUV (eU.inv.base q).2)
  have hfun : ((sectionsIsoOfIsoSpf eU).hom : _ → _) ∘
      ((X.presheaf.map (homOfLE hUV).op) ∘ (f.hom.c.app (op V))) =
      (Spf.globalSectionsIsoOfIsAdicRing B).hom ∘
        (g.c.app (op V) ≫ (Spf B).presheaf.map (eqToHom (congrArg op hg_pre))) := by
    funext s
    have h1 := ConcreteCategory.congr_hom (chartImmersion_c_app (X := X) hUV eU)
      (f.hom.c.app (op V) s)
    -- `erw`: unpack `ConcreteCategory.hom` composition and `Spf.structureSheaf` on `h1`.
    erw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply,
      ConcreteCategory.comp_apply] at h1
    dsimp only [Function.comp_apply]
    -- `erw`: unfold `g.c.app` via `comp_c_app` and `ConcreteCategory.hom` composition.
    erw [ConcreteCategory.comp_apply,
      ConcreteCategory.congr_hom (LocallyRingedSpace.comp_c_app
        (eU.inv ≫ X.toLocallyRingedSpace.ofRestrict U.isOpenEmbedding) f.hom (op V)) s,
      ConcreteCategory.comp_apply]
    exact h1.symm
  rw [hfun]
  let tTop : TopologicalSpace ((Spf B).presheaf.obj (op ⊤)) :=
    Spf.quotientSectionsTopology (IsAdicRing.ideal_spec B).2.1 ⊤
  refine @Continuous.comp _ _ _ (sheafSectionsTopology Y V) tTop inferInstance _ _
    (@IsHomeomorph.continuous _ _ tTop _ _
      (Spf.isHomeomorph_globalSectionsIso (IsAdicRing.ideal_spec B).2.1))
    (continuous_chart_pullback_top f hUV eU)

end AutomaticContinuity

end TauCeti.FormalScheme
