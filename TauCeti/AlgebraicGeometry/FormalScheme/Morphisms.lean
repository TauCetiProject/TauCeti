/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.FormalScheme.SectionsTopology

import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-!
# Morphisms of formal schemes, morphisms into `Spf A`, and automatic continuity

Let `X` be a formal scheme of finite ideal type and `A` an adic ring of finite ideal type.
This module establishes the fundamental properties of morphisms of formal schemes (EGA I,
Ch. I, 10.4.5–10.4.6):

* **Gluing of morphisms** (`FormalScheme.glueMorphisms`, `FormalScheme.hom_ext_of_ofRestrict`):
  compatible morphisms from an open cover of `X` glue uniquely to a morphism `X ⟶ Y`.
* **Continuity on affine formal opens and residue-field criterion**
  (`FormalScheme.ContinuousOnAffines`, `FormalScheme.continuousOnAffines_iff_residue`):
  a ring homomorphism `φ : A →+* Γ(X, O_X)` is continuous on every affine formal open of `X`
  (equivalently, continuous for `FormalScheme.sheafSectionsTopology X ⊤`) if and only if for some
  (equivalently every) ideal of definition `I` of `A`, `φ a` vanishes in the residue field `κ(x)`
  for all `a ∈ I` and `x ∈ X`.
* **Morphism correspondence into `Spf A`** (`FormalScheme.homSpfEquiv`):
  taking global sections yields a bijection
  `(X ⟶ ofSpf A) ≃ { φ : A →+* Γ(X, O_X) // ContinuousOnAffines X A φ }` (EGA I, Ch. I, 10.4.6).
* **Automatic continuity** (`FormalScheme.continuous_c_app_of_isAffineOpen`,
  `FormalScheme.continuous_c_app`):
  every morphism `f : X ⟶ Y` of formal schemes (defined purely as a morphism of locally ringed
  spaces) is automatically continuous on rings of sections `Γ(V, O_Y) → Γ(f⁻¹ V, O_X)` with respect
  to `FormalScheme.sheafSectionsTopology` (EGA I, Ch. I, 10.4.5).

## Main definitions

* `TauCeti.FormalScheme.restrictHomOfLE`: the inclusion `X|_V ⟶ X|_W` for opens `V ≤ W`.
* `TauCeti.FormalScheme.glueMorphisms`: gluing a compatible family of morphisms over an open cover.
* `TauCeti.FormalScheme.ContinuousOnAffines`: predicate on `φ : A →+* Γ(X, O_X)` asserting
  continuity of `A → Γ(U, O_X)` for every affine formal open `U` of `X`.
* `TauCeti.FormalScheme.sectionsHom`: the global-sections ring homomorphism `A →+* Γ(X, O_X)`
  associated to a morphism `X ⟶ ofSpf A`.
* `TauCeti.FormalScheme.homSpfEquiv`: the bijection between `X ⟶ ofSpf A` and ring homomorphisms
  `A →+* Γ(X, O_X)` continuous on affine formal opens.

## Main results

* `TauCeti.FormalScheme.continuousOnAffines_iff_continuous_sheafSectionsTopology`: continuity on
  affine formal opens is equivalent to continuity for `sheafSectionsTopology X ⊤`.
* `TauCeti.FormalScheme.continuousOnAffines_iff_residue`: continuity on affine formal opens is
  equivalent to vanishing of an ideal of definition in every residue field of `X`.
* `TauCeti.FormalScheme.continuous_c_app`: every morphism `f : X ⟶ Y` of formal schemes induces
  continuous maps on rings of sections for `sheafSectionsTopology`.

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

private theorem ofRestrict_hom (X : FormalScheme.{u}) (U : Opens X) :
    (X.ofRestrict U).hom = X.toLocallyRingedSpace.ofRestrict U.isOpenEmbedding :=
  forgetToLocallyRingedSpace_map_ofRestrict X U

/-- Composing `X|_V ⟶ X|_W` with `X|_W ⟶ X` gives `X|_V ⟶ X`. -/
@[reassoc (attr := simp)]
theorem restrictHomOfLE_ofRestrict (X : FormalScheme.{u}) {V W : Opens X} (h : V ≤ W) :
    X.restrictHomOfLE h ≫ X.ofRestrict W = X.ofRestrict V := by
  apply InducedCategory.hom_ext
  change X.toLocallyRingedSpace.restrictHomOfLE h ≫ (X.ofRestrict W).hom = (X.ofRestrict V).hom
  rw [ofRestrict_hom, ofRestrict_hom]
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
    X.ofRestrict (U i) ≫ glueMorphisms U hU f hcompat = f i := by
  apply InducedCategory.hom_ext
  change (X.ofRestrict (U i)).hom ≫ (glueMorphisms U hU f hcompat).hom = (f i).hom
  rw [ofRestrict_hom]
  exact X.toLocallyRingedSpace.ofRestrict_glueMorphisms U hU _ _ i

/-- Two morphisms of formal schemes that agree on every member of an open cover are equal. -/
theorem hom_ext_of_ofRestrict {X Y : FormalScheme.{u}} {ι : Type*}
    (U : ι → Opens X) (hU : ⨆ i, U i = ⊤) {f g : X ⟶ Y}
    (h : ∀ i, X.ofRestrict (U i) ≫ f = X.ofRestrict (U i) ≫ g) :
    f = g :=
  InducedCategory.hom_ext <|
    X.toLocallyRingedSpace.hom_ext_of_ofRestrict U hU fun i ↦ by
      have hi := congrArg InducedCategory.Hom.hom (h i)
      change (X.ofRestrict (U i)).hom ≫ f.hom = (X.ofRestrict (U i)).hom ≫ g.hom at hi
      rwa [ofRestrict_hom] at hi

/-- The affine formal opens of `X` cover `⊤`. -/
private theorem iSup_affineOpens (X : FormalScheme.{u}) :
    (⨆ U : { U : Opens X // X.IsAffineOpen U }, U.1) = ⊤ := by
  ext x
  refine ⟨fun _ ↦ trivial, fun _ ↦ ?_⟩
  have hx : x ∈ (⊤ : Opens X) := trivial
  obtain ⟨U, hU, hxU, -⟩ := (Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens) hx
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

/-- For an affine formal open `U` with chart `e : X|_U ≅ Spf B`, continuity of `A → Γ(U, O_X)`
is equivalent to vanishing of an ideal of definition `I` of `A` in every residue field of `U`. -/
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
  let j : Spf B ⟶ X.toLocallyRingedSpace :=
    e.inv ≫ X.toLocallyRingedSpace.ofRestrict U.isOpenEmbedding
  let ψ : A →+* B :=
    (sectionsIsoOfIsoSpf e).hom.hom.comp ((X.presheaf.map (homOfLE le_top).op).hom.comp φ)
  have hhomeo := isHomeomorph_sectionsIsoOfIsoSpf hU e
  have hcont_iff :
      @Continuous _ _ _ (sectionsTopology X U hU) ((X.presheaf.map (homOfLE le_top).op) ∘ φ) ↔
        Continuous ψ := by
    let _ : TopologicalSpace (X.presheaf.obj (op U)) := sectionsTopology X U hU
    exact hhomeo.isInducing.continuous_iff
  rw [hcont_iff, hI.continuous_iff_map_le_radical (IsAdicRing.ideal_spec B).2.1
    (IsAdicRing.ideal_spec A).2.1 (IsAdicRing.ideal_spec A).1, Ideal.map_le_iff_le_comap]
  let gB : (Spf B).presheaf.obj (op ⊤) ≅ CommRingCat.of B :=
    @Spf.globalSectionsIso B _ _ _ _ (IsAdicRing.ideal_spec B).2.2 (IsAdicRing.ideal_spec B).2.1
  have hj_app : ∀ a : A, j.c.app (op ⊤) (φ a) = gB.inv (ψ a) := by
    intro a
    have h2 := ConcreteCategory.congr_hom (chartImmersion_c_app_top e) (φ a)
    have hinv := ConcreteCategory.congr_hom gB.hom_inv_id (j.c.app (op ⊤) (φ a))
    simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply,
      CommRingCat.hom_id] at h2 hinv
    exact hinv.symm.trans (congrArg gB.inv h2)
  refine ⟨fun h a ha q ↦ ?_, fun h a ha ↦ ?_⟩
  · have hmem : ψ a ∈ (IsAdicRing.ideal B).radical := h ha
    have hzero := (Spf.mem_radical_iff_forall_Γevaluation_eq_zero
      (IsAdicRing.ideal_spec B).2.1 (ψ a)).mp hmem q
    let q' : Spf B := q
    have hnat := LocallyRingedSpace.Γevaluation_naturality_apply j q' (φ a)
    have hinj : Function.Injective (LocallyRingedSpace.residueFieldMap j q').hom :=
      (LocallyRingedSpace.residueFieldMap j q').hom.injective
    rw [← map_eq_zero_iff (LocallyRingedSpace.residueFieldMap j q').hom hinj]
    change (LocallyRingedSpace.residueFieldMap j q')
      (X.toLocallyRingedSpace.Γevaluation (j.base q') (φ a)) = 0
    rw [hnat, hj_app a]
    exact hzero
  · change ψ a ∈ (IsAdicRing.ideal B).radical
    rw [Spf.mem_radical_iff_forall_Γevaluation_eq_zero (IsAdicRing.ideal_spec B).2.1]
    intro q
    let q' : Spf B := q
    have hnat := LocallyRingedSpace.Γevaluation_naturality_apply j q' (φ a)
    change (Spf B).Γevaluation q' (gB.inv (ψ a)) = 0
    rw [← hj_app a, ← hnat, h a ha q]
    exact map_zero (LocallyRingedSpace.residueFieldMap j q').hom

/-- **Residue-field criterion for continuity on affine formal opens** (EGA I, Ch. I, 10.4.6):
for any ideal of definition `I` of `A`, a ring homomorphism `φ : A →+* Γ(X, O_X)` is continuous on
all affine formal opens of `X` if and only if `φ a` vanishes in the residue field `κ(x)` for every
`a ∈ I` and every point `x : X`. -/
theorem continuousOnAffines_iff_residue {X : FormalScheme.{u}}
    {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsAdicRing A]
    {I : Ideal A} (hI : IsAdic I) (φ : A →+* X.presheaf.obj (op ⊤)) :
    ContinuousOnAffines X A φ ↔
      ∀ a ∈ I, ∀ x : X, X.toLocallyRingedSpace.Γevaluation x (φ a) = 0 := by
  constructor
  · intro hφ a ha x
    have hx : x ∈ (⊤ : Opens X) := trivial
    obtain ⟨U, hU, hxU, -⟩ := (Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens) hx
    obtain ⟨B, _, _, _, _, ⟨e⟩⟩ := (X.isAffineOpen_iff U).mp hU
    have hres := (continuous_restrict_iff_residue_on_chart hI hU e φ).mp (hφ U hU) a ha
      (e.hom.base ⟨x, hxU⟩)
    have hpt : (e.inv ≫ X.toLocallyRingedSpace.ofRestrict U.isOpenEmbedding).base
        (e.hom.base ⟨x, hxU⟩) = x := by
      have hid := ConcreteCategory.congr_hom
        (congrArg (fun m ↦ m.base) e.hom_inv_id) ⟨x, hxU⟩
      exact congrArg Subtype.val hid
    rwa [hpt] at hres
  · intro hres U hU
    obtain ⟨B, _, _, _, _, ⟨e⟩⟩ := (X.isAffineOpen_iff U).mp hU
    exact (continuous_restrict_iff_residue_on_chart hI hU e φ).mpr fun a ha q ↦ hres a ha _

end ContinuousOnAffines

section SpfMorphismCorrespondence

/-- The global-sections ring homomorphism `A →+* Γ(X, O_X)` induced by a morphism
`f : X ⟶ ofSpf A`. -/
noncomputable def sectionsHom {X : FormalScheme.{u}}
    {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsAdicRing A]
    (f : X ⟶ ofSpf A) : A →+* X.presheaf.obj (op ⊤) :=
  ((@Spf.globalSectionsIso A _ _ _ _ (IsAdicRing.ideal_spec A).2.2
    (IsAdicRing.ideal_spec A).2.1).inv ≫ f.hom.c.app (op ⊤)).hom

/-- Functoriality of `FormalScheme.sectionsHom` under precomposition. -/
theorem sectionsHom_comp {Y X : FormalScheme.{u}}
    {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsAdicRing A]
    (g : Y ⟶ X) (f : X ⟶ ofSpf A) :
    sectionsHom (g ≫ f) = (g.hom.c.app (op ⊤)).hom.comp (sectionsHom f) := by
  ext a
  rfl

/-- On an affine formal scheme `ofSpf B`, `FormalScheme.sectionsHom` followed by
`Spf.globalSectionsIso` equals `Spf.sectionsHom`. -/
theorem globalSectionsIso_comp_sectionsHom {A B : Type u}
    [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsAdicRing A]
    [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsAdicRing B]
    (f : ofSpf B ⟶ ofSpf A) :
    ((@Spf.globalSectionsIso B _ _ _ _ (IsAdicRing.ideal_spec B).2.2
      (IsAdicRing.ideal_spec B).2.1).hom.hom).comp (sectionsHom f) =
      Spf.sectionsHom f.hom := by
  let gA : (Spf A).presheaf.obj (op ⊤) ≅ CommRingCat.of A :=
    @Spf.globalSectionsIso A _ _ _ _ (IsAdicRing.ideal_spec A).2.2 (IsAdicRing.ideal_spec A).2.1
  let gB : (Spf B).presheaf.obj (op ⊤) ≅ CommRingCat.of B :=
    @Spf.globalSectionsIso B _ _ _ _ (IsAdicRing.ideal_spec B).2.2 (IsAdicRing.ideal_spec B).2.1
  have h : gA.inv ≫ f.hom.c.app (op ⊤) ≫ gB.hom = CommRingCat.ofHom (Spf.sectionsHom f.hom) :=
    (congrArg (gA.inv ≫ ·) (Spf.c_app_top_comp_globalSectionsIso_hom f.hom)).trans
      (Iso.inv_hom_id_assoc gA _)
  exact congrArg CommRingCat.Hom.hom h

/-- Restricting `f : X ⟶ ofSpf A` to an affine formal chart `e : X|_U ≅ Spf B` induces on
sections the composite `A → Γ(X, O_X) → Γ(U, O_X) ≅ B`. -/
private theorem sectionsHom_chart_comp {X : FormalScheme.{u}}
    {A B : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsAdicRing A]
    [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsAdicRing B]
    (f : X ⟶ ofSpf A) {U : Opens X}
    (e : X.toLocallyRingedSpace.restrict U.isOpenEmbedding ≅ Spf B) :
    Spf.sectionsHom (e.inv ≫ X.toLocallyRingedSpace.ofRestrict U.isOpenEmbedding ≫ f.hom) =
      (sectionsIsoOfIsoSpf e).hom.hom.comp
        ((X.presheaf.map (homOfLE le_top).op).hom.comp (sectionsHom f)) := by
  let f' : X.toLocallyRingedSpace ⟶ Spf A := f.hom
  let j : Spf B ⟶ X.toLocallyRingedSpace :=
    e.inv ≫ X.toLocallyRingedSpace.ofRestrict U.isOpenEmbedding
  let gA : (Spf A).presheaf.obj (op ⊤) ≅ CommRingCat.of A :=
    @Spf.globalSectionsIso A _ _ _ _ (IsAdicRing.ideal_spec A).2.2 (IsAdicRing.ideal_spec A).2.1
  let gB : (Spf B).presheaf.obj (op ⊤) ≅ CommRingCat.of B :=
    @Spf.globalSectionsIso B _ _ _ _ (IsAdicRing.ideal_spec B).2.2 (IsAdicRing.ideal_spec B).2.1
  have hj : j.c.app (op ⊤) ≫ gB.hom =
      X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op ≫ (sectionsIsoOfIsoSpf e).hom :=
    chartImmersion_c_app_top e
  have hcomp : (j ≫ f').c.app (op ⊤) ≫ gB.hom =
      f'.c.app (op ⊤) ≫ X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op ≫
        (sectionsIsoOfIsoSpf e).hom := by
    refine CommRingCat.hom_ext <| RingHom.ext fun s ↦ ?_
    exact ConcreteCategory.congr_hom hj (f'.c.app (op ⊤) s)
  have hsp := Spf.c_app_top_comp_globalSectionsIso_hom (j ≫ f')
  have heq : CommRingCat.ofHom (Spf.sectionsHom (j ≫ f')) =
      gA.inv ≫ f'.c.app (op ⊤) ≫ X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op ≫
        (sectionsIsoOfIsoSpf e).hom := by
    calc CommRingCat.ofHom (Spf.sectionsHom (j ≫ f'))
        = gA.inv ≫ gA.hom ≫ CommRingCat.ofHom (Spf.sectionsHom (j ≫ f')) :=
          (Iso.inv_hom_id_assoc gA _).symm
      _ = gA.inv ≫ (j ≫ f').c.app (op ⊤) ≫ gB.hom := congrArg (gA.inv ≫ ·) hsp.symm
      _ = gA.inv ≫ f'.c.app (op ⊤) ≫ X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op ≫
            (sectionsIsoOfIsoSpf e).hom := congrArg (gA.inv ≫ ·) hcomp
  have hassoc : e.inv ≫ X.toLocallyRingedSpace.ofRestrict U.isOpenEmbedding ≫ f' = j ≫ f' :=
    (Category.assoc _ _ _).symm
  change Spf.sectionsHom (e.inv ≫ X.toLocallyRingedSpace.ofRestrict U.isOpenEmbedding ≫ f') = _
  rw [hassoc]
  exact congrArg CommRingCat.Hom.hom heq

/-- For every morphism `f : X ⟶ ofSpf A`, the global-sections homomorphism `sectionsHom f` is
continuous on every affine formal open of `X`. -/
theorem continuousOnAffines_sectionsHom {X : FormalScheme.{u}}
    {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsAdicRing A]
    (f : X ⟶ ofSpf A) :
    ContinuousOnAffines X A (sectionsHom f) := by
  intro U hU
  obtain ⟨B, _, _, _, _, ⟨e⟩⟩ := (X.isAffineOpen_iff U).mp hU
  let _ : TopologicalSpace (X.presheaf.obj (op U)) := sectionsTopology X U hU
  rw [(isHomeomorph_sectionsIsoOfIsoSpf hU e).isInducing.continuous_iff]
  have hfun : ((sectionsIsoOfIsoSpf e).hom : _ → _) ∘
      ((X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op) ∘ (sectionsHom f)) =
      Spf.sectionsHom (e.inv ≫ X.toLocallyRingedSpace.ofRestrict U.isOpenEmbedding ≫ f.hom) := by
    ext a
    exact (RingHom.congr_fun (sectionsHom_chart_comp f e) a).symm
  rw [hfun]
  exact Spf.continuous_sectionsHom _

/-- Two morphisms `X ⟶ ofSpf A` with the same global-sections homomorphism are equal. -/
theorem hom_ext_of_sectionsHom_eq {X : FormalScheme.{u}}
    {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsAdicRing A]
    {f g : X ⟶ ofSpf A} (h : sectionsHom f = sectionsHom g) :
    f = g := by
  refine hom_ext_of_ofRestrict (fun U : { U : Opens X // X.IsAffineOpen U } ↦ U.1)
    (iSup_affineOpens X) fun ⟨U, hU⟩ ↦ ?_
  obtain ⟨B, _, _, _, _, ⟨e⟩⟩ := (X.isAffineOpen_iff U).mp hU
  have h1 : X.toLocallyRingedSpace.ofRestrict U.isOpenEmbedding ≫ f.hom =
      X.toLocallyRingedSpace.ofRestrict U.isOpenEmbedding ≫ g.hom := by
    rw [← cancel_epi e.inv]
    refine Spf.hom_ext_of_sectionsHom_eq ?_
    exact (sectionsHom_chart_comp f e).trans (by rw [h]; exact (sectionsHom_chart_comp g e).symm)
  apply InducedCategory.hom_ext
  change (X.ofRestrict U).hom ≫ f.hom = (X.ofRestrict U).hom ≫ g.hom
  rw [ofRestrict_hom]
  exact h1

/-- The local morphism `X|_U ⟶ ofSpf A` attached to a chart `e : X|_U ≅ Spf B` and a ring
homomorphism `φ : A →+* Γ(X, O_X)` continuous on affine formal opens. -/
private noncomputable def localHomOfChart {X : FormalScheme.{u}}
    {A B : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsAdicRing A]
    [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsAdicRing B]
    (φ : A →+* X.presheaf.obj (op ⊤)) (hφ : ContinuousOnAffines X A φ)
    {U : Opens X} (hU : X.IsAffineOpen U)
    (e : X.toLocallyRingedSpace.restrict U.isOpenEmbedding ≅ Spf B) :
    X.restrict U ⟶ ofSpf A :=
  let ψ : A →+* B :=
    (sectionsIsoOfIsoSpf e).hom.hom.comp ((X.presheaf.map (homOfLE le_top).op).hom.comp φ)
  have hψ : Continuous ψ := by
    let _ : TopologicalSpace (X.presheaf.obj (op U)) := sectionsTopology X U hU
    exact (isHomeomorph_sectionsIsoOfIsoSpf hU e).isInducing.continuous_iff.mp (hφ U hU)
  InducedCategory.homMk (e.hom ≫ Spf.map ψ hψ)

/-- The global-sections homomorphism of `localHomOfChart` is the restriction of `φ` along
`X.ofRestrict U`. -/
private theorem sectionsHom_localHomOfChart {X : FormalScheme.{u}}
    {A B : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsAdicRing A]
    [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsAdicRing B]
    (φ : A →+* X.presheaf.obj (op ⊤)) (hφ : ContinuousOnAffines X A φ)
    {U : Opens X} (hU : X.IsAffineOpen U)
    (e : X.toLocallyRingedSpace.restrict U.isOpenEmbedding ≅ Spf B) :
    sectionsHom (localHomOfChart φ hφ hU e) =
      ((X.toLocallyRingedSpace.ofRestrict U.isOpenEmbedding).c.app (op ⊤)).hom.comp φ := by
  let ψ : A →+* B :=
    (sectionsIsoOfIsoSpf e).hom.hom.comp ((X.presheaf.map (homOfLE le_top).op).hom.comp φ)
  have hψ : Continuous ψ := by
    let _ : TopologicalSpace (X.presheaf.obj (op U)) := sectionsTopology X U hU
    exact (isHomeomorph_sectionsIsoOfIsoSpf hU e).isInducing.continuous_iff.mp (hφ U hU)
  let gA : (Spf A).presheaf.obj (op ⊤) ≅ CommRingCat.of A :=
    @Spf.globalSectionsIso A _ _ _ _ (IsAdicRing.ideal_spec A).2.2 (IsAdicRing.ideal_spec A).2.1
  let gB : (Spf B).presheaf.obj (op ⊤) ≅ CommRingCat.of B :=
    @Spf.globalSectionsIso B _ _ _ _ (IsAdicRing.ideal_spec B).2.2 (IsAdicRing.ideal_spec B).2.1
  have hmap : gA.inv ≫ (Spf.map ψ hψ).c.app (op ⊤) ≫ gB.hom = CommRingCat.ofHom ψ :=
    (congrArg (gA.inv ≫ ·) (Spf.c_app_top_comp_globalSectionsIso_hom (Spf.map ψ hψ))).trans
      ((Iso.inv_hom_id_assoc gA _).trans (by rw [Spf.sectionsHom_map]))
  have hj : (e.inv ≫ X.toLocallyRingedSpace.ofRestrict U.isOpenEmbedding).c.app (op ⊤) ≫ gB.hom =
      X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op ≫ (sectionsIsoOfIsoSpf e).hom :=
    chartImmersion_c_app_top e
  ext a
  have h1 : (e.inv.c.app (op ⊤) ≫ gB.hom) (sectionsHom (localHomOfChart φ hφ hU e) a) = ψ a := by
    let m : X.toLocallyRingedSpace.restrict U.isOpenEmbedding ⟶ Spf A :=
      (localHomOfChart φ hφ hU e).hom
    have hcomp : e.inv ≫ m = Spf.map ψ hψ := Iso.inv_hom_id_assoc e (Spf.map ψ hψ)
    have hmap' : gA.inv ≫ (e.inv ≫ m).c.app (op ⊤) ≫ gB.hom = CommRingCat.ofHom ψ := by
      rw [hcomp]
      exact hmap
    exact ConcreteCategory.congr_hom hmap' a
  have h2 : (e.inv.c.app (op ⊤) ≫ gB.hom)
      (((X.toLocallyRingedSpace.ofRestrict U.isOpenEmbedding).c.app (op ⊤)).hom (φ a)) = ψ a :=
    ConcreteCategory.congr_hom hj (φ a)
  have hinj : Function.Injective (e.inv.c.app (op ⊤) ≫ gB.hom) := by
    refine Function.LeftInverse.injective (g := gB.inv ≫ e.hom.c.app (op ⊤)) fun x ↦ ?_
    have hgB : gB.inv (gB.hom (e.inv.c.app (op ⊤) x)) = e.inv.c.app (op ⊤) x :=
      ConcreteCategory.congr_hom gB.hom_inv_id (e.inv.c.app (op ⊤) x)
    have he : (e.hom ≫ e.inv).c.app (op ⊤) x = x := by
      rw [e.hom_inv_id]
      rfl
    change e.hom.c.app (op ⊤) (gB.inv (gB.hom (e.inv.c.app (op ⊤) x))) = x
    rw [hgB]
    exact he
  exact hinj (h1.trans h2.symm)

/-- Choose a local morphism `X|_U ⟶ ofSpf A` on an affine formal open `U` whose global-sections
homomorphism is the restriction of `φ`. -/
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
  let cov : { U : Opens X // X.IsAffineOpen U } → Opens X := Subtype.val
  refine glueMorphisms cov (iSup_affineOpens X)
    (fun i ↦ (chosenLocalHom φ hφ i.2).1) fun i j ↦ hom_ext_of_sectionsHom_eq ?_
  rw [sectionsHom_comp, sectionsHom_comp, (chosenLocalHom φ hφ i.2).2, (chosenLocalHom φ hφ j.2).2]
  ext a
  have hi := LocallyRingedSpace.comp_c_app
    (X.toLocallyRingedSpace.restrictHomOfLE (inf_le_left : i.1 ⊓ j.1 ≤ i.1))
    (X.toLocallyRingedSpace.ofRestrict i.1.isOpenEmbedding) (op ⊤)
  have hj := LocallyRingedSpace.comp_c_app
    (X.toLocallyRingedSpace.restrictHomOfLE (inf_le_right : i.1 ⊓ j.1 ≤ j.1))
    (X.toLocallyRingedSpace.ofRestrict j.1.isOpenEmbedding) (op ⊤)
  rw [LocallyRingedSpace.restrictHomOfLE_ofRestrict] at hi hj
  exact (ConcreteCategory.congr_hom hi.symm (φ a)).trans (ConcreteCategory.congr_hom hj (φ a))

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
    rw [ofRestrict_glueMorphisms]
    exact (chosenLocalHom φ hφ i.2).2
  have h1 := RingHom.congr_fun ((sectionsHom_comp (X.ofRestrict i.1) _).symm.trans hres) a
  dsimp only [RingHom.comp_apply] at h1
  rw [ofRestrict_hom] at h1
  have htop : i.1.isOpenEmbedding.functor.obj ⊤ = i.1 := by
    ext x
    simp
  have h2 := congrArg (X.presheaf.map (eqToHom (congrArg op htop))) h1
  have hmap : (X.toLocallyRingedSpace.ofRestrict i.1.isOpenEmbedding).c.app (op ⊤) ≫
      X.presheaf.map (eqToHom (congrArg op htop)) = X.presheaf.map (homOfLE le_top).op := by
    -- `erw`: `ofRestrict.c.app` unfolds to `X.presheaf.map`.
    erw [← X.presheaf.map_comp]
    exact congrArg X.presheaf.map (Quiver.Hom.unop_inj (Subsingleton.elim _ _))
  exact (ConcreteCategory.congr_hom hmap _).symm.trans
    (h2.trans (ConcreteCategory.congr_hom hmap _))

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
    (f : X ⟶ ofSpf A) :
    (homSpfEquiv X A f).1 = sectionsHom f :=
  (rfl)

/-- The inverse of `homSpfEquiv` is `homOfContinuousOnAffines`. -/
@[simp]
theorem homSpfEquiv_symm_apply {X : FormalScheme.{u}}
    {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsAdicRing A]
    (φ : { φ : A →+* X.presheaf.obj (op ⊤) // ContinuousOnAffines X A φ }) :
    (homSpfEquiv X A).symm φ = homOfContinuousOnAffines φ.1 φ.2 :=
  (rfl)

end SpfMorphismCorrespondence

section AutomaticContinuity

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
  let jU : Spf B ⟶ X.toLocallyRingedSpace :=
    eU.inv ≫ X.toLocallyRingedSpace.ofRestrict U.isOpenEmbedding
  let jV : Spf A ⟶ Y.toLocallyRingedSpace :=
    eV.inv ≫ Y.toLocallyRingedSpace.ofRestrict V.isOpenEmbedding
  have hrange : Set.range (jU ≫ f.hom).base ⊆ Set.range jV.base := by
    rintro _ ⟨q, rfl⟩
    have hqV : (jU ≫ f.hom).base q ∈ V := hUV (eU.inv.base q).2
    refine ⟨eV.hom.base ⟨(jU ≫ f.hom).base q, hqV⟩, ?_⟩
    have hid := ConcreteCategory.congr_hom
      (congrArg (fun m ↦ m.base) eV.hom_inv_id) ⟨(jU ≫ f.hom).base q, hqV⟩
    exact congrArg Subtype.val hid
  let g : Spf B ⟶ Spf A := LocallyRingedSpace.IsOpenImmersion.lift jV (jU ≫ f.hom) hrange
  have hg : g ≫ jV = jU ≫ f.hom :=
    LocallyRingedSpace.IsOpenImmersion.lift_fac jV (jU ≫ f.hom) hrange
  let gA : (Spf A).presheaf.obj (op ⊤) ≅ CommRingCat.of A :=
    @Spf.globalSectionsIso A _ _ _ _ (IsAdicRing.ideal_spec A).2.2 (IsAdicRing.ideal_spec A).2.1
  let gB : (Spf B).presheaf.obj (op ⊤) ≅ CommRingCat.of B :=
    @Spf.globalSectionsIso B _ _ _ _ (IsAdicRing.ideal_spec B).2.2 (IsAdicRing.ideal_spec B).2.1
  have hpreV : (Opens.map jV.base).obj V = ⊤ := by
    ext p
    exact iff_true_intro (eV.inv.base p).2
  have hpreB : (Opens.map (g ≫ jV).base).obj V = ⊤ := by
    ext q
    change jV.base (g.base q) ∈ V ↔ True
    exact iff_true_intro (eV.inv.base (g.base q)).2
  have hpreU : (Opens.map jU.base).obj ((Opens.map f.hom.base).obj V) = ⊤ := by
    ext q
    exact iff_true_intro (hUV (eU.inv.base q).2)
  have hleft : (g ≫ jV).c.app (op V) ≫ (Spf B).presheaf.map (eqToHom (congrArg op hpreB)) ≫
      gB.hom = (sectionsIsoOfIsoSpf eV).hom ≫ CommRingCat.ofHom (Spf.sectionsHom g) := by
    have hnat := g.c.naturality (eqToHom (congrArg op hpreV))
    have hc := LocallyRingedSpace.comp_c_app g jV (op V)
    have hchartV := chartImmersion_c_app (X := Y) (le_refl V) eV
    dsimp only at hchartV
    have hidV : Y.presheaf.map (homOfLE (le_refl V)).op = 𝟙 _ := Y.presheaf.map_id _
    rw [hidV, Category.id_comp] at hchartV
    have hmid : g.c.app (op ((Opens.map jV.base).obj V)) ≫
        (Spf B).presheaf.map (eqToHom (congrArg op hpreB)) =
        (Spf A).presheaf.map (eqToHom (congrArg op hpreV)) ≫ g.c.app (op ⊤) := by
      have hm : (Spf B).presheaf.map (eqToHom (congrArg op hpreB)) =
          ((TopCat.Presheaf.pushforward CommRingCat g.base).obj (Spf B).presheaf).map
            (eqToHom (congrArg op hpreV)) :=
        congrArg (Spf B).presheaf.map (Quiver.Hom.unop_inj (Subsingleton.elim _ _))
      exact (congrArg (g.c.app _ ≫ ·) hm).trans hnat.symm
    calc (g ≫ jV).c.app (op V) ≫ (Spf B).presheaf.map (eqToHom (congrArg op hpreB)) ≫ gB.hom
        = jV.c.app (op V) ≫
            (g.c.app (op ((Opens.map jV.base).obj V)) ≫
              (Spf B).presheaf.map (eqToHom (congrArg op hpreB))) ≫ gB.hom := by
          rw [hc]
          -- `erw`: `pushforward` presheaf matches at default transparency.
          erw [Category.assoc, Category.assoc]
      _ = jV.c.app (op V) ≫ (Spf A).presheaf.map (eqToHom (congrArg op hpreV)) ≫
            g.c.app (op ⊤) ≫ gB.hom := by
          -- `erw`: `pushforward` presheaf matches at default transparency.
          erw [hmid, Category.assoc]
      _ = jV.c.app (op V) ≫ (Spf A).presheaf.map (eqToHom (congrArg op hpreV)) ≫
            gA.hom ≫ CommRingCat.ofHom (Spf.sectionsHom g) :=
          congrArg (fun m ↦ jV.c.app (op V) ≫
            (Spf A).presheaf.map (eqToHom (congrArg op hpreV)) ≫ m)
            (Spf.c_app_top_comp_globalSectionsIso_hom g)
      _ = (jV.c.app (op V) ≫ (Spf A).presheaf.map (eqToHom (congrArg op hpreV)) ≫ gA.hom) ≫
            CommRingCat.ofHom (Spf.sectionsHom g) := by
          simp only [Category.assoc]
      _ = (sectionsIsoOfIsoSpf eV).hom ≫ CommRingCat.ofHom (Spf.sectionsHom g) := by
          rw [hchartV]
  have hright : (jU ≫ f.hom).c.app (op V) ≫ (Spf B).presheaf.map (eqToHom (congrArg op hpreU)) ≫
      gB.hom =
      (f.hom.c.app (op V) ≫ X.presheaf.map (homOfLE hUV).op) ≫ (sectionsIsoOfIsoSpf eU).hom := by
    have hc := LocallyRingedSpace.comp_c_app jU f.hom (op V)
    have hchartU := chartImmersion_c_app (X := X) hUV eU
    dsimp only at hchartU
    calc (jU ≫ f.hom).c.app (op V) ≫
            (Spf B).presheaf.map (eqToHom (congrArg op hpreU)) ≫ gB.hom
        = f.hom.c.app (op V) ≫ jU.c.app (op ((Opens.map f.hom.base).obj V)) ≫
            (Spf B).presheaf.map (eqToHom (congrArg op hpreU)) ≫ gB.hom := by
          rw [hc]
          -- `erw`: `pushforward` presheaf matches at default transparency.
          erw [Category.assoc]
      _ = f.hom.c.app (op V) ≫ X.presheaf.map (homOfLE hUV).op ≫ (sectionsIsoOfIsoSpf eU).hom := by
          rw [hchartU]
      _ = (f.hom.c.app (op V) ≫ X.presheaf.map (homOfLE hUV).op) ≫
            (sectionsIsoOfIsoSpf eU).hom := (Category.assoc _ _ _).symm
  have hcomm : (f.hom.c.app (op V) ≫ X.presheaf.map (homOfLE hUV).op) ≫
      (sectionsIsoOfIsoSpf eU).hom =
      (sectionsIsoOfIsoSpf eV).hom ≫ CommRingCat.ofHom (Spf.sectionsHom g) := by
    have hcongr := PresheafedSpace.congr_app (congrArg LocallyRingedSpace.Hom.toHom hg) (op V)
    have heq : (g ≫ jV).c.app (op V) ≫ (Spf B).presheaf.map (eqToHom (congrArg op hpreB)) =
        (jU ≫ f.hom).c.app (op V) ≫ (Spf B).presheaf.map (eqToHom (congrArg op hpreU)) := by
      rw [hcongr, Category.assoc, ← (Spf B).presheaf.map_comp]
      exact congrArg ((jU ≫ f.hom).c.app (op V) ≫ ·)
        (congrArg (Spf B).presheaf.map (Quiver.Hom.unop_inj (Subsingleton.elim _ _)))
    rw [← hright, ← hleft]
    calc (jU ≫ f.hom).c.app (op V) ≫ (Spf B).presheaf.map (eqToHom (congrArg op hpreU)) ≫ gB.hom
        = ((jU ≫ f.hom).c.app (op V) ≫ (Spf B).presheaf.map (eqToHom (congrArg op hpreU))) ≫
            gB.hom := (Category.assoc _ _ _).symm
      _ = ((g ≫ jV).c.app (op V) ≫ (Spf B).presheaf.map (eqToHom (congrArg op hpreB))) ≫ gB.hom :=
          congrArg (· ≫ gB.hom) heq.symm
      _ = (g ≫ jV).c.app (op V) ≫ (Spf B).presheaf.map (eqToHom (congrArg op hpreB)) ≫ gB.hom :=
          Category.assoc _ _ _
  let _ : TopologicalSpace (Y.presheaf.obj (op V)) := sectionsTopology Y V hV
  let _ : TopologicalSpace (X.presheaf.obj (op U)) := sectionsTopology X U hU
  have hhomeoV := isHomeomorph_sectionsIsoOfIsoSpf hV eV
  have hhomeoU := isHomeomorph_sectionsIsoOfIsoSpf hU eU
  rw [hhomeoU.isInducing.continuous_iff]
  have hfun : ((sectionsIsoOfIsoSpf eU).hom : _ → _) ∘
      (f.hom.c.app (op V) ≫ X.presheaf.map (homOfLE hUV).op) =
      (Spf.sectionsHom g) ∘ (sectionsIsoOfIsoSpf eV).hom := by
    ext s
    exact ConcreteCategory.congr_hom hcomm s
  rw [hfun]
  exact (Spf.continuous_sectionsHom g).comp hhomeoV.continuous

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
  have := (IsAdicRing.ideal_spec B).2.2
  let _ : TopologicalSpace (X.presheaf.obj (op U)) := sectionsTopology X U hU
  rw [(isHomeomorph_sectionsIsoOfIsoSpf hU eU).isInducing.continuous_iff]
  let g : Spf B ⟶ Y.toLocallyRingedSpace :=
    (eU.inv ≫ X.toLocallyRingedSpace.ofRestrict U.isOpenEmbedding) ≫ f.hom
  have hg_pre : (Opens.map g.base).obj V = ⊤ := by
    ext q
    exact iff_true_intro (hUV (eU.inv.base q).2)
  let gB : (Spf B).presheaf.obj (op ⊤) ≅ CommRingCat.of B :=
    @Spf.globalSectionsIso B _ _ _ _ (IsAdicRing.ideal_spec B).2.2 (IsAdicRing.ideal_spec B).2.1
  let k : Y.presheaf.obj (op V) → (Spf B).presheaf.obj (op ⊤) :=
    g.c.app (op V) ≫ (Spf B).presheaf.map (eqToHom (congrArg op hg_pre))
  have hfun : ((sectionsIsoOfIsoSpf eU).hom : _ → _) ∘
      ((X.presheaf.map (homOfLE hUV).op) ∘ (f.hom.c.app (op V))) = gB.hom ∘ k := by
    have hchartU := chartImmersion_c_app (X := X) hUV eU
    dsimp only at hchartU
    have hc := LocallyRingedSpace.comp_c_app
      (eU.inv ≫ X.toLocallyRingedSpace.ofRestrict U.isOpenEmbedding) f.hom (op V)
    ext s
    have h1 := ConcreteCategory.congr_hom hchartU (f.hom.c.app (op V) s)
    have h2 := ConcreteCategory.congr_hom hc s
    change (sectionsIsoOfIsoSpf eU).hom (X.presheaf.map (homOfLE hUV).op (f.hom.c.app (op V) s)) =
      gB.hom ((Spf B).presheaf.map (eqToHom (congrArg op hg_pre)) (g.c.app (op V) s))
    rw [h2]
    exact h1.symm
  rw [hfun]
  let tTop : TopologicalSpace ((Spf B).presheaf.obj (op ⊤)) :=
    Spf.quotientSectionsTopology (IsAdicRing.ideal_spec B).2.1 ⊤
  have hglob : @Continuous _ _ tTop _ gB.hom :=
    @IsHomeomorph.continuous _ _ tTop _ _
      (Spf.isHomeomorph_globalSectionsIso (IsAdicRing.ideal_spec B).2.1)
  refine @Continuous.comp _ _ _ (sheafSectionsTopology Y V) tTop inferInstance _ _ hglob ?_
  have hnbhd : ∀ q : Spf.carrier B,
      ∃ W : Opens Y, Y.IsAffineOpen W ∧ W ≤ V ∧
        ∃ b : B, q ∈ Spf.basicOpen b ∧ Spf.basicOpen b ≤ (Opens.map g.base).obj W := by
    intro q
    have hqV : g.base q ∈ V := hUV (eU.inv.base q).2
    obtain ⟨W, hW, hqW, hWV⟩ := (Opens.isBasis_iff_nbhd.mp Y.isBasis_affineOpens) hqV
    have hqW' : q ∈ (Opens.map g.base).obj W := hqW
    obtain ⟨_, ⟨b, rfl⟩, hqb, hbW⟩ :=
      (Opens.isBasis_iff_nbhd.mp Spf.isBasis_basicOpen) hqW'
    exact ⟨W, hW, hWV, b, hqb, hbW⟩
  choose W hW hWV b hqb hbW using hnbhd
  have hcov : (⊤ : Opens (Spf.carrier B)) ≤ ⨆ q : Spf.carrier B, Spf.basicOpen (b q) := by
    intro q _
    exact Opens.mem_iSup.mpr ⟨q, hqb q⟩
  let _ : TopologicalSpace
      ((Spf.structureSheaf (IsAdicRing.ideal_spec B).2.1).obj.obj (op ⊤)) :=
    Spf.quotientSectionsTopology (IsAdicRing.ideal_spec B).2.1 ⊤
  let _ (q : Spf.carrier B) : TopologicalSpace
      ((Spf.structureSheaf (IsAdicRing.ideal_spec B).2.1).obj.obj (op (Spf.basicOpen (b q)))) :=
    Spf.quotientSectionsTopology (IsAdicRing.ideal_spec B).2.1 (Spf.basicOpen (b q))
  have hind := (Spf.quotientSectionsTopology_glue (IsAdicRing.ideal_spec B).2.1
    (U := ⊤) (V := fun q ↦ Spf.basicOpen (b q)) (fun _ ↦ le_top) hcov).isInducing
  let k' : Y.presheaf.obj (op V) →
      (Spf.structureSheaf (IsAdicRing.ideal_spec B).2.1).obj.obj (op ⊤) := k
  refine (hind.continuous_iff (f := k')).mpr ?_
  refine continuous_pi fun q ↦ ?_
  have hcoord : (fun s : Y.presheaf.obj (op V) ↦
        (Spf B).presheaf.map (homOfLE (le_top : Spf.basicOpen (b q) ≤ ⊤)).op (k s)) =
      (g.c.app (op (W q)) ≫ (Spf B).presheaf.map (homOfLE (hbW q)).op) ∘
        (Y.presheaf.map (homOfLE (hWV q)).op) := by
    ext s
    have hnat := g.c.naturality (homOfLE (hWV q)).op
    have hcomp : g.c.app (op V) ≫ (Spf B).presheaf.map (eqToHom (congrArg op hg_pre)) ≫
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
      calc g.c.app (op V) ≫ (Spf B).presheaf.map (eqToHom (congrArg op hg_pre)) ≫
              (Spf B).presheaf.map (homOfLE (le_top : Spf.basicOpen (b q) ≤ ⊤)).op
          = (g.c.app (op V) ≫
              ((TopCat.Presheaf.pushforward CommRingCat g.base).obj (Spf B).presheaf).map
                (homOfLE (hWV q)).op) ≫ (Spf B).presheaf.map (homOfLE (hbW q)).op := by
            rw [hm, Category.assoc]
        _ = (Y.presheaf.map (homOfLE (hWV q)).op ≫ g.c.app (op (W q))) ≫
              (Spf B).presheaf.map (homOfLE (hbW q)).op := by
            rw [← hnat]
        _ = Y.presheaf.map (homOfLE (hWV q)).op ≫ g.c.app (op (W q)) ≫
              (Spf B).presheaf.map (homOfLE (hbW q)).op := Category.assoc _ _ _
    exact ConcreteCategory.congr_hom hcomp s
  change @Continuous _ _ (sheafSectionsTopology Y V)
    (Spf.quotientSectionsTopology (IsAdicRing.ideal_spec B).2.1 (Spf.basicOpen (b q)))
    (fun s : Y.presheaf.obj (op V) ↦
      (Spf B).presheaf.map (homOfLE (le_top : Spf.basicOpen (b q) ≤ ⊤)).op (k s))
  rw [hcoord]
  have hstep1 : @Continuous _ _ (sheafSectionsTopology Y V) (sectionsTopology Y (W q) (hW q))
      (Y.presheaf.map (homOfLE (hWV q)).op) := by
    rw [← sheafSectionsTopology_eq_sectionsTopology Y (W q) (hW q)]
    exact sheafSectionsTopology_restrict Y (hWV q)
  have hstep2 : @Continuous _ _ (sectionsTopology Y (W q) (hW q))
      (Spf.quotientSectionsTopology (IsAdicRing.ideal_spec B).2.1 (Spf.basicOpen (b q)))
      (g.c.app (op (W q)) ≫ (Spf B).presheaf.map (homOfLE (hbW q)).op) := by
    rw [← sectionsTopology_ofSpf_basicOpen B (b q)]
    exact continuous_c_app_of_isAffineOpen (InducedCategory.homMk g : ofSpf B ⟶ Y)
      (hW q) (isAffineOpen_basicOpen B (b q)) (hbW q)
  exact @Continuous.comp _ _ _ (sheafSectionsTopology Y V) (sectionsTopology Y (W q) (hW q)) _
    _ _ hstep2 hstep1

end AutomaticContinuity

end TauCeti.FormalScheme
