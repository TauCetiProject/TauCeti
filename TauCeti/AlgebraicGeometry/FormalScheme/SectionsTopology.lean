/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.FormalScheme.Basic
public import TauCeti.AlgebraicGeometry.FormalScheme.Spf.HomEquiv
public import TauCeti.Geometry.RingedSpace.LocallyRingedSpace.Restrict

import TauCeti.Topology.Algebra.Ring.Basic
import TauCeti.Topology.Discrete
import TauCeti.Topology.Sheaves.Presheaf

/-!
# Canonical section topologies on formal schemes

For an affine formal open `U` of a formal scheme `X`, any chart `e : X|_U ≅ Spf B` identifies
`Γ(X, U) ≅ B` (`chartSectionsIso`), inducing a chart-independent complete separated adic topology
`X.sectionsTopology U hU` (packaged on `hU.Sections`, with `hU.isoSpf : X.restrict U ≅ ofSpf _`;
EGA I, Ch. I, 10.4.5). Topologically nilpotent sections are cut out by residue vanishing on `U`,
affine section maps are continuous (`sectionMap_continuous`), and for arbitrary opens `W ⊆ X`,
`X.openSectionsTopology W` makes `Γ(X, W)` a topological ring
(`openSectionsTopology_isTopologicalRing`), is tested on open covers
(`openSectionsTopology_isInducing_pi`), agrees with `Spf.quotientSectionsTopology` on formal
spectra (`openSectionsTopology_ofSpf`, `sectionsTopology_ofSpf`), and makes every morphism
continuous on sections (`continuous_c_app_openSectionsTopology`; EGA I, Ch. I, 10.4.6).
-/

public section
open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry
universe u
namespace TauCeti.FormalScheme
section ChartTopology
private structure ChosenChart (X : FormalScheme.{u}) (U : Opens X) where
  B : Type u
  [commRing : CommRing B] [topSpace : TopologicalSpace B]
  [isTopRing : IsTopologicalRing B] [isAdic : IsAdicRing B]
  iso : X.toLocallyRingedSpace.restrict U.isOpenEmbedding ≅ Spf B

attribute [instance] ChosenChart.commRing ChosenChart.topSpace ChosenChart.isTopRing
  ChosenChart.isAdic

private noncomputable def chosenChart {X : FormalScheme.{u}} {U : Opens X}
    (hU : X.IsAffineOpen U) : ChosenChart X U :=
  let h := (X.isAffineOpen_iff U).mp hU
  let _ := h.choose_spec.choose; let _ := h.choose_spec.choose_spec.choose
  let _ := h.choose_spec.choose_spec.choose_spec.choose
  let _ := h.choose_spec.choose_spec.choose_spec.choose_spec.choose
  { B := h.choose, iso := h.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.some }

variable (X : FormalScheme.{u}) (U : Opens X)

section ChartSections
variable {B : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsAdicRing B]
  (e : X.toLocallyRingedSpace.restrict U.isOpenEmbedding ≅ Spf B)

/-- For any affine formal chart `e : X|_U ≅ Spf B`, the induced ring isomorphism `Γ(X, U) ≅ B`. -/
noncomputable def chartSectionsIso : X.presheaf.obj (op U) ≅ CommRingCat.of B :=
  X.toLocallyRingedSpace.restrictTopSectionsIso U ≪≫
    (LocallyRingedSpace.Γ.mapIso e.symm.op : _ ≅ (Spf B).presheaf.obj (op ⊤)) ≪≫
    Spf.topSectionsIso B

theorem chartSectionsIso_hom_apply (s : X.presheaf.obj (op U)) :
    (chartSectionsIso X U e).hom s = (Spf.topSectionsIso B).hom
      (e.inv.c.app (op ⊤) ((X.toLocallyRingedSpace.restrictTopSectionsIso U).hom s)) := (rfl)
theorem chartSectionsIso_inv_apply (b : B) : (chartSectionsIso X U e).inv b =
    (X.toLocallyRingedSpace.restrictTopSectionsIso U).inv
      (e.hom.c.app (op ⊤) ((Spf.topSectionsIso B).inv b)) := (rfl)
end ChartSections

/-- Global-section map `f.c.app (op ⊤)` typed without `pushforward` for clean rewriting. -/
private abbrev topApp {Y₁ Y₂ : LocallyRingedSpace.{u}} (f : Y₁ ⟶ Y₂) :
    Y₂.presheaf.obj (op ⊤) ⟶ Y₁.presheaf.obj (op ⊤) := f.c.app (op ⊤)

/-- Changing the affine formal chart `X|_U ≅ Spf B` composes `chartSectionsIso` with the topological
ring isomorphism `Spf.isoToRingEquiv` of the transition isomorphism. -/
theorem chartSectionsIso_hom_comp_isoToRingEquiv {B₁ B₂ : Type u} [CommRing B₁]
    [TopologicalSpace B₁] [IsTopologicalRing B₁] [IsAdicRing B₁] [CommRing B₂]
    [TopologicalSpace B₂] [IsTopologicalRing B₂] [IsAdicRing B₂]
    (e₁ : X.toLocallyRingedSpace.restrict U.isOpenEmbedding ≅ Spf B₁)
    (e₂ : X.toLocallyRingedSpace.restrict U.isOpenEmbedding ≅ Spf B₂) :
    (chartSectionsIso X U e₁).hom ≫
        CommRingCat.ofHom (Spf.isoToRingEquiv (e₂.symm ≪≫ e₁)).toRingHom =
      (chartSectionsIso X U e₂).hom := by
  have hmid : (Spf.topSectionsIso B₁).hom ≫
        CommRingCat.ofHom (Spf.isoToRingEquiv (e₂.symm ≪≫ e₁)).toRingHom =
      topApp e₁.hom ≫ topApp e₂.inv ≫ (Spf.topSectionsIso B₂).hom := by
    rw [RingEquiv.toRingHom_eq_coe, Spf.isoToRingEquiv_toRingHom,
      ← Spf.c_app_top_comp_topSectionsIso_hom (e₂.symm ≪≫ e₁).hom]; exact Category.assoc _ _ _
  have h1 : (chartSectionsIso X U e₁).hom = (X.toLocallyRingedSpace.restrictTopSectionsIso U).hom ≫
      topApp e₁.inv ≫ (Spf.topSectionsIso B₁).hom := rfl
  have h2 : (chartSectionsIso X U e₂).hom = (X.toLocallyRingedSpace.restrictTopSectionsIso U).hom ≫
      topApp e₂.inv ≫ (Spf.topSectionsIso B₂).hom := rfl
  have he₁ : topApp e₁.inv ≫ topApp e₁.hom = 𝟙 _ := LocallyRingedSpace.iso_inv_c_app_top_comp_hom e₁
  rw [h1, h2, Category.assoc, Category.assoc, hmid, reassoc_of% he₁]

private theorem induced_chartSectionsIso_eq {B₁ B₂ : Type u} [CommRing B₁]
    [t₁ : TopologicalSpace B₁] [IsTopologicalRing B₁] [IsAdicRing B₁] [CommRing B₂]
    [t₂ : TopologicalSpace B₂] [IsTopologicalRing B₂] [IsAdicRing B₂]
    (e₁ : X.toLocallyRingedSpace.restrict U.isOpenEmbedding ≅ Spf B₁)
    (e₂ : X.toLocallyRingedSpace.restrict U.isOpenEmbedding ≅ Spf B₂) :
    TopologicalSpace.induced (chartSectionsIso X U e₁).hom t₁ =
      TopologicalSpace.induced (chartSectionsIso X U e₂).hom t₂ := by
  have hfun : ((chartSectionsIso X U e₂).hom : X.presheaf.obj (op U) → B₂) =
      Spf.isoToRingEquiv (e₂.symm ≪≫ e₁) ∘ (chartSectionsIso X U e₁).hom := funext fun s ↦
    (ConcreteCategory.congr_hom (chartSectionsIso_hom_comp_isoToRingEquiv X U e₁ e₂) s).symm
  rw [hfun, ← induced_compose,
    ← (Spf.isHomeomorph_isoToRingEquiv (e₂.symm ≪≫ e₁)).isInducing.eq_induced]

variable (hU : X.IsAffineOpen U)

/-- The canonical chart-independent adic topology on `Γ(X, U)` over an affine formal open `U ⊆ X`
(EGA I, Ch. I, 10.4.5). -/
@[instance_reducible] noncomputable def sectionsTopology :
    TopologicalSpace (X.presheaf.obj (op U)) :=
  TopologicalSpace.induced (chartSectionsIso X U (chosenChart hU).iso).hom inferInstance

/-- `X.sectionsTopology U hU` is induced along `chartSectionsIso X U e` for every chart `e`. -/
theorem sectionsTopology_eq_induced {B : Type u} [CommRing B] [tB : TopologicalSpace B]
    [IsTopologicalRing B] [IsAdicRing B]
    (e : X.toLocallyRingedSpace.restrict U.isOpenEmbedding ≅ Spf B) :
    X.sectionsTopology U hU = TopologicalSpace.induced (chartSectionsIso X U e).hom tB :=
  induced_chartSectionsIso_eq X U (chosenChart hU).iso e

/-- For every chart `e : X|_U ≅ Spf B`, `chartSectionsIso X U e` is a homeomorphism. -/
theorem isHomeomorph_chartSectionsIso {B : Type u} [CommRing B] [TopologicalSpace B]
    [IsTopologicalRing B] [IsAdicRing B]
    (e : X.toLocallyRingedSpace.restrict U.isOpenEmbedding ≅ Spf B) :
    @IsHomeomorph _ _ (X.sectionsTopology U hU) ‹TopologicalSpace B›
      (chartSectionsIso X U e).hom := by
  let _ := X.sectionsTopology U hU
  exact ((chartSectionsIso X U e).commRingCatIsoToRingEquiv.toEquiv.toHomeomorphOfIsInducing
    ⟨sectionsTopology_eq_induced X U hU e⟩).isHomeomorph

/-- Equipped with `X.sectionsTopology U hU`, `Γ(X, U)` is a topological ring. -/
theorem sectionsTopology_isTopologicalRing :
    @IsTopologicalRing (X.presheaf.obj (op U)) (X.sectionsTopology U hU) _ := by
  obtain ⟨B, _, _, _, _, ⟨e⟩⟩ := (X.isAffineOpen_iff U).mp hU
  exact sectionsTopology_eq_induced X U hU e ▸
    TauCeti.isTopologicalRing_induced (chartSectionsIso X U e).hom.hom

/-- Equipped with `X.sectionsTopology U hU`, `Γ(X, U)` is a complete separated adic ring of finite
ideal type (EGA I, Ch. I, 10.4.5). -/
theorem sectionsTopology_isAdicRing :
    @IsAdicRing (X.presheaf.obj (op U)) _ (X.sectionsTopology U hU)
      (X.sectionsTopology_isTopologicalRing U hU) := by
  obtain ⟨B, _, _, _, _, ⟨e⟩⟩ := (X.isAffineOpen_iff U).mp hU; let _ := X.sectionsTopology U hU
  have := X.sectionsTopology_isTopologicalRing U hU
  let φ := (chartSectionsIso X U e).commRingCatIsoToRingEquiv
  obtain ⟨I, hIfg, hIadic, hIcomp⟩ := IsAdicRing.exists_isAdic (A := B)
  exact ⟨⟨I.map φ.symm.toRingHom, hIfg.map φ.symm.toRingHom,
    (Ideal.map_symm φ).symm ▸ hIadic.comap φ ⟨sectionsTopology_eq_induced X U hU e⟩,
    (IsAdicComplete.congr_ringEquiv I φ.symm).mpr hIcomp⟩⟩

/-- `s ∈ Γ(X, U)` is topologically nilpotent for `X.sectionsTopology U hU` iff its residue vanishes
at every point of `U` (EGA I, Ch. I, 10.4.5). -/
theorem isTopologicallyNilpotent_iff_forall_evaluation_eq_zero (s : X.presheaf.obj (op U)) :
    @IsTopologicallyNilpotent _ _ (X.sectionsTopology U hU) s ↔
      ∀ x : U, X.toLocallyRingedSpace.evaluation x s = 0 := by
  obtain ⟨B, _, _, _, _, ⟨e⟩⟩ := (X.isAffineOpen_iff U).mp hU
  let _ := X.sectionsTopology U hU; have := X.sectionsTopology_isTopologicalRing U hU
  let φ := (chartSectionsIso X U e).commRingCatIsoToRingEquiv
  obtain ⟨hφ₁, hφ₂⟩ := φ.toEquiv.isHomeomorph_iff.mp (isHomeomorph_chartSectionsIso X U hU e)
  obtain ⟨-, hIB, -⟩ := IsAdicRing.ideal_spec B
  rw [show IsTopologicallyNilpotent s ↔ IsTopologicallyNilpotent (φ s) from
      ⟨fun hs ↦ hs.map (φ := φ.toRingHom) hφ₁,
        fun hs ↦ by simpa using hs.map (φ := φ.symm.toRingHom) hφ₂⟩,
    hIB.isTopologicallyNilpotent_iff_mem_radical, Ideal.radical_eq_sInf, Ideal.mem_sInf,
    show (∀ p ∈ {p : Ideal B | IsAdicRing.ideal B ≤ p ∧ p.IsPrime}, φ s ∈ p) ↔
      ∀ p : Spf.carrier B, (Spf B).Γevaluation p ((Spf.topSectionsIso B).inv (φ s)) = 0 from
      ⟨fun h p ↦ (Spf.Γevaluation_topSectionsIso_inv_eq_zero_iff p _).mpr
        (h _ ⟨(Spf.mem_carrier_iff_le hIB).mp p.2, p.1.isPrime⟩),
       fun h q hq ↦ (Spf.Γevaluation_topSectionsIso_inv_eq_zero_iff
        ⟨⟨q, hq.2⟩, (Spf.mem_carrier_iff_le hIB).mpr hq.1⟩ _).mp (h _)⟩]
  have hsec₂ : (Spf.topSectionsIso B).inv (φ s) = e.inv.c.app (op ⊤)
      ((X.toLocallyRingedSpace.restrictTopSectionsIso U).hom s) :=
    ConcreteCategory.congr_hom (Spf.topSectionsIso B).hom_inv_id _
  have hsec₁ : e.hom.c.app (op ⊤) ((Spf.topSectionsIso B).inv (φ s)) =
      (X.toLocallyRingedSpace.restrictTopSectionsIso U).hom s := by
    rw [hsec₂]; exact ConcreteCategory.congr_hom (LocallyRingedSpace.iso_inv_c_app_top_comp_hom e) _
  refine ⟨fun h x ↦ ?_, fun h (p : Spf B) ↦ ?_⟩
  · rw [X.toLocallyRingedSpace.evaluation_eq_zero_iff_restrict_Γevaluation_eq_zero, ← hsec₁,
      ← LocallyRingedSpace.Γevaluation_naturality_apply e.hom x, h (e.hom.base x), map_zero]
  · rw [hsec₂, ← LocallyRingedSpace.Γevaluation_naturality_apply e.inv p,
      (X.toLocallyRingedSpace.evaluation_eq_zero_iff_restrict_Γevaluation_eq_zero U _ _).mp
        (h (e.inv.base p)), map_zero]

end ChartTopology

section CanonicalChart
variable {X : FormalScheme.{u}} {U : Opens X}

/-- A finitely generated ideal `J` of `Γ(X, U)` over an affine formal open `U` defines
`X.sectionsTopology U hU` whenever its radical consists of the sections vanishing in every residue
field on `U` (EGA I, Ch. I, 10.4.5). -/
theorem sectionsTopology_eq_adic (hU : X.IsAffineOpen U) {J : Ideal (X.presheaf.obj (op U))}
    (hJfg : J.FG) (hJrad : ∀ s : X.presheaf.obj (op U),
      s ∈ J.radical ↔ ∀ x : U, X.toLocallyRingedSpace.evaluation x s = 0) :
    @IsAdic _ _ (X.sectionsTopology U hU) J := by
  let _ := X.sectionsTopology U hU; have := X.sectionsTopology_isTopologicalRing U hU
  have := X.sectionsTopology_isAdicRing U hU
  obtain ⟨hIfg, hIadic, -⟩ := IsAdicRing.ideal_spec (X.presheaf.obj (op U))
  exact hIadic.of_radical_eq hIfg hJfg <| Ideal.ext fun s ↦
    hIadic.isTopologicallyNilpotent_iff_mem_radical.symm.trans <|
      (isTopologicallyNilpotent_iff_forall_evaluation_eq_zero X U hU s).trans (hJrad s).symm

namespace IsAffineOpen
/-- Type synonym for `Γ(X, U)` over an affine formal open `U ⊆ X`, carrying its canonical
chart-independent adic ring structure (`FormalScheme.sectionsTopology`). The body is exposed so
ring homomorphisms and sections over `U` apply directly to `hU.Sections`. -/
@[expose] def Sections (_ : X.IsAffineOpen U) : Type u := X.presheaf.obj (op U)

instance (hU : X.IsAffineOpen U) : CommRing hU.Sections :=
  inferInstanceAs (CommRing (X.presheaf.obj (op U)))
noncomputable instance (hU : X.IsAffineOpen U) : TopologicalSpace hU.Sections :=
  X.sectionsTopology U hU
instance (hU : X.IsAffineOpen U) : IsTopologicalRing hU.Sections :=
  X.sectionsTopology_isTopologicalRing U hU
instance (hU : X.IsAffineOpen U) : IsAdicRing hU.Sections := X.sectionsTopology_isAdicRing U hU

/-- Every affine formal open `U ⊆ X` is canonically isomorphic as a formal scheme to the formal
spectrum of `hU.Sections` (EGA I, Ch. I, 10.4.5). -/
noncomputable def isoSpf (hU : X.IsAffineOpen U) : X.restrict U ≅ ofSpf hU.Sections :=
  let φ : hU.Sections ≃+* (chosenChart hU).B :=
    (chartSectionsIso X U (chosenChart hU).iso).commRingCatIsoToRingEquiv
  let hφ := φ.toEquiv.isHomeomorph_iff.mp (isHomeomorph_chartSectionsIso X U hU _)
  InducedCategory.isoMk ((chosenChart hU).iso ≪≫ Spf.mapIso φ hφ.1 hφ.2)
end IsAffineOpen

/-- On global sections, `hU.isoSpf.hom` identifies `Spf.topSectionsIso` with
`X.toLocallyRingedSpace.restrictTopSectionsIso U`, independently of any chosen chart. -/
@[reassoc (attr := simp)] theorem topSectionsIso_inv_isoSpf_hom_c_app_top (hU : X.IsAffineOpen U) :
    (Spf.topSectionsIso hU.Sections).inv ≫
      ((forgetToLocallyRingedSpace.map hU.isoSpf.hom).c.app (op ⊤) :
        (Spf hU.Sections).presheaf.obj (op ⊤) ⟶
          (X.toLocallyRingedSpace.restrict U.isOpenEmbedding).presheaf.obj (op ⊤)) =
      (X.toLocallyRingedSpace.restrictTopSectionsIso U).hom := by
  let e := (chosenChart hU).iso; let rU := X.toLocallyRingedSpace.restrictTopSectionsIso U
  let φ : hU.Sections ≃+* (chosenChart hU).B := (chartSectionsIso X U e).commRingCatIsoToRingEquiv
  let hφ := φ.toEquiv.isHomeomorph_iff.mp (isHomeomorph_chartSectionsIso X U hU e)
  have hm : (Spf.topSectionsIso hU.Sections).inv ≫ topApp (Spf.map φ.toRingHom hφ.1) =
      rU.hom ≫ topApp e.inv := by
    -- Unfold `topApp` and `chartSectionsIso` to cancel `topSectionsIso`.
    erw [Spf.topSectionsIso_inv_comp_c_app_top, Spf.sectionsHom_map]
    change (rU.hom ≫ topApp e.inv ≫ (Spf.topSectionsIso (chosenChart hU).B).hom) ≫
      (Spf.topSectionsIso (chosenChart hU).B).inv = _
    rw [Category.assoc, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hcomp : ((forgetToLocallyRingedSpace.map hU.isoSpf.hom).c.app (op ⊤) :
        (Spf hU.Sections).presheaf.obj (op ⊤) ⟶
          (X.toLocallyRingedSpace.restrict U.isOpenEmbedding).presheaf.obj (op ⊤)) =
      topApp (Spf.map φ.toRingHom hφ.1) ≫ topApp e.hom := by
    -- Unfold `hU.isoSpf.hom` to `e.hom ≫ (Spf.mapIso φ _ _).hom` as `LocallyRingedSpace.Γ.map`.
    change LocallyRingedSpace.Γ.map (e.hom ≫ (Spf.mapIso φ hφ.1 hφ.2).hom).op = _
    erw [Spf.mapIso_hom, op_comp, Functor.map_comp]; rfl
  rw [hcomp]
  -- Unfold `hU.Sections` to `X.presheaf.obj (op U)` across `rU.hom`.
  erw [← Category.assoc, hm, Category.assoc,
    LocallyRingedSpace.iso_inv_c_app_top_comp_hom e, Category.comp_id]

/-- Dual form of `topSectionsIso_inv_isoSpf_hom_c_app_top` for `hU.isoSpf.inv`. -/
@[reassoc (attr := simp)]
theorem isoSpf_inv_c_app_top_comp_topSectionsIso_hom (hU : X.IsAffineOpen U) :
    ((forgetToLocallyRingedSpace.map hU.isoSpf.inv).c.app (op ⊤) :
        (X.toLocallyRingedSpace.restrict U.isOpenEmbedding).presheaf.obj (op ⊤) ⟶
          (Spf hU.Sections).presheaf.obj (op ⊤)) ≫ (Spf.topSectionsIso hU.Sections).hom =
      (X.toLocallyRingedSpace.restrictTopSectionsIso U).inv := by
  let rU := X.toLocallyRingedSpace.restrictTopSectionsIso U
  have step (α β) (h1 : (Spf.topSectionsIso hU.Sections).inv ≫ α = rU.hom) (h2 : α ≫ β = 𝟙 _) :
      β ≫ (Spf.topSectionsIso hU.Sections).hom = rU.inv := by
    refine (cancel_epi rU.hom).mp ?_
    -- Unfold `hU.Sections` to `X.presheaf.obj (op U)`.
    erw [Iso.hom_inv_id, ← h1, Category.assoc, reassoc_of% h2, Iso.inv_hom_id]
  exact step _ _ (topSectionsIso_inv_isoSpf_hom_c_app_top hU)
    (LocallyRingedSpace.iso_hom_c_app_top_comp_inv (forgetToLocallyRingedSpace.mapIso hU.isoSpf))

/-- **Automatic continuity on affine opens** (EGA I, Ch. I, 10.4.6): for `f : X ⟶ Y` and affine
opens `U ⊆ X`, `V ⊆ Y` with `U ≤ f ⁻¹' V`, `Γ(Y, V) →+* Γ(X, U)` is continuous. -/
theorem sectionMap_continuous {X Y : FormalScheme.{u}} (f : X ⟶ Y) {V : Opens Y}
    (hV : Y.IsAffineOpen V) {U : Opens X} (hU : X.IsAffineOpen U)
    (hUV : U ≤ (Opens.map (forgetToLocallyRingedSpace.map f).base).obj V) :
    @Continuous _ _ (Y.sectionsTopology V hV) (X.sectionsTopology U hU)
      ((forgetToLocallyRingedSpace.map f).c.app (op V) ≫ X.presheaf.map (homOfLE hUV).op) := by
  let fL := forgetToLocallyRingedSpace.map f
  let jU := X.toLocallyRingedSpace.ofRestrict U.isOpenEmbedding
  let jV := Y.toLocallyRingedSpace.ofRestrict V.isOpenEmbedding
  have hsub : Set.range (jU ≫ fL).base ⊆ Set.range jV.base :=
    fun _ ⟨x, hx⟩ ↦ hx ▸ ⟨⟨fL.base x.1, hUV x.2⟩, rfl⟩
  let fUV := LocallyRingedSpace.IsOpenImmersion.lift jV (jU ≫ fL) hsub
  let g : Spf hU.Sections ⟶ Spf hV.Sections :=
    (forgetToLocallyRingedSpace.map hU.isoSpf.inv ≫ fUV) ≫
      forgetToLocallyRingedSpace.map hV.isoSpf.hom
  let rU := X.toLocallyRingedSpace.restrictTopSectionsIso U
  let rV := Y.toLocallyRingedSpace.restrictTopSectionsIso V
  have hg : CommRingCat.ofHom (Spf.sectionsHom g) =
      fL.c.app (op V) ≫ X.presheaf.map (homOfLE hUV).op := by
    have step (eV fM eU) (hV_eq : (Spf.topSectionsIso hV.Sections).inv ≫ eV = rV.hom)
        (hU_eq : eU ≫ (Spf.topSectionsIso hU.Sections).hom = rU.inv)
        (hF_eq : rV.hom ≫ fM = fL.c.app (op V) ≫ X.presheaf.map (homOfLE hUV).op ≫ rU.hom) :
        (Spf.topSectionsIso hV.Sections).inv ≫ (eV ≫ fM ≫ eU) ≫
            (Spf.topSectionsIso hU.Sections).hom =
          fL.c.app (op V) ≫ X.presheaf.map (homOfLE hUV).op := by
      -- Unfold `hU.Sections` / `hV.Sections` to `presheaf.obj`.
      simp only [Category.assoc]; erw [hU_eq, reassoc_of% hV_eq, reassoc_of% hF_eq, Category.assoc,
        Category.assoc, Iso.hom_inv_id, Category.comp_id]; rfl
    exact (Spf.ofHom_sectionsHom g).trans <| step _ _ _ (topSectionsIso_inv_isoSpf_hom_c_app_top hV)
      (isoSpf_inv_c_app_top_comp_topSectionsIso_hom hU)
      (LocallyRingedSpace.restrictTopSectionsIso_hom_c_app_top_of_fac fL hUV fUV
        (LocallyRingedSpace.IsOpenImmersion.lift_fac jV (jU ≫ fL) hsub))
  exact (Spf.continuous_sectionsHom g).congr (ConcreteCategory.congr_hom hg)

end CanonicalChart

section SpecialCasesAndOpenTopology

/-- Over an affine open `U` of a scheme `X`, `(ofScheme.obj X).sectionsTopology U _` is discrete. -/
theorem sectionsTopology_ofScheme {X : Scheme.{u}} {U : X.Opens}
    (hU : AlgebraicGeometry.IsAffineOpen U) :
    (ofScheme.obj X).sectionsTopology U (isAffineOpen_ofScheme hU) = ⊥ := by
  let R : Type u := X.presheaf.obj (op U)
  let _ : TopologicalSpace R := ⊥; have : DiscreteTopology R := ⟨rfl⟩
  let e : (ofScheme.obj X).toLocallyRingedSpace.restrict U.isOpenEmbedding ≅ Spf R :=
    Scheme.forgetToLocallyRingedSpace.mapIso hU.isoSpec ≪≫ (Spf.discreteIsoSpec R).symm
  exact (sectionsTopology_eq_induced (ofScheme.obj X) U (isAffineOpen_ofScheme hU) e).trans
    (TauCeti.induced_bot_of_injective
      (ConcreteCategory.bijective_of_isIso (chartSectionsIso (ofScheme.obj X) U e).hom).injective)

/-- Projective-limit topology on `Γ(X, W)` for an open `W ⊆ X`, induced from `sectionsTopology` on
affine formal opens `U ≤ W` (EGA I, Ch. I, 10.4.5). -/
@[instance_reducible] noncomputable def openSectionsTopology (X : FormalScheme.{u}) (W : Opens X) :
    TopologicalSpace (X.presheaf.obj (op W)) :=
  ⨅ (U : Opens X) (hU : X.IsAffineOpen U) (hUW : U ≤ W),
    TopologicalSpace.induced (X.presheaf.map (homOfLE hUW).op) (X.sectionsTopology U hU)

/-- Continuity into `X.openSectionsTopology W` is tested on affine formal opens `U ≤ W`. -/
theorem continuous_iff_openSectionsTopology {T : Type*} [TopologicalSpace T] (X : FormalScheme.{u})
    (W : Opens X) (g : T → X.presheaf.obj (op W)) :
    @Continuous _ _ ‹TopologicalSpace T› (X.openSectionsTopology W) g ↔
      ∀ (U : Opens X) (hU : X.IsAffineOpen U) (hUW : U ≤ W),
        @Continuous _ _ ‹TopologicalSpace T› (X.sectionsTopology U hU)
          (X.presheaf.map (homOfLE hUW).op ∘ g) := by
  let _ := X.openSectionsTopology W; simp only [continuous_iInf_rng, continuous_induced_rng]

/-- On an affine formal open `W ⊆ X`, `X.openSectionsTopology W = X.sectionsTopology W hW`. -/
theorem openSectionsTopology_eq_sectionsTopology (X : FormalScheme.{u}) (W : Opens X)
    (hW : X.IsAffineOpen W) : X.openSectionsTopology W = X.sectionsTopology W hW := by
  refine le_antisymm (iInf_le_of_le W <| iInf_le_of_le hW <| iInf_le_of_le (le_refl W) ?_)
    (le_iInf fun U ↦ le_iInf fun hU ↦ le_iInf fun hUW ↦ ?_)
  · rw [TopCat.Presheaf.map_eq_id]; exact le_of_eq (induced_id (t := X.sectionsTopology W hW))
  · let _ := X.sectionsTopology W hW; let _ := X.sectionsTopology U hU
    exact continuous_iff_le_induced.mp ((sectionMap_continuous (𝟙 X) hW hU hUW).congr fun _ ↦ rfl)

/-- Restriction maps `Γ(X, W₂) → Γ(X, W₁)` are continuous for `openSectionsTopology`. -/
theorem continuous_restrict_openSectionsTopology (X : FormalScheme.{u}) {W₁ W₂ : Opens X}
    (h : W₁ ≤ W₂) : @Continuous _ _ (X.openSectionsTopology W₂) (X.openSectionsTopology W₁)
      (X.presheaf.map (homOfLE h).op) := by
  let _ := X.openSectionsTopology W₂; rw [continuous_iff_openSectionsTopology]; intro U hU hUW₁
  let _ := X.sectionsTopology U hU
  exact ((continuous_iff_openSectionsTopology X W₂ id).mp continuous_id U hU
    (hUW₁.trans h)).congr fun s ↦ ConcreteCategory.congr_hom (X.presheaf.map_comp _ _) s

/-- Equipped with `X.openSectionsTopology W`, `Γ(X, W)` is a topological ring. -/
theorem openSectionsTopology_isTopologicalRing (X : FormalScheme.{u}) (W : Opens X) :
    @IsTopologicalRing (X.presheaf.obj (op W)) (X.openSectionsTopology W) _ :=
  TauCeti.isTopologicalRing_iInf fun U ↦ TauCeti.isTopologicalRing_iInf fun hU ↦
    TauCeti.isTopologicalRing_iInf fun _ ↦
      let _ := X.sectionsTopology U hU; have := X.sectionsTopology_isTopologicalRing U hU
      TauCeti.isTopologicalRing_induced (X.presheaf.map (homOfLE _).op).hom

section OfSpf
variable (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsAdicRing A]

private theorem quotientSectionsTopology_le_openSectionsTopology (W : Opens (ofSpf A)) :
    Spf.quotientSectionsTopology (IsAdicRing.ideal_spec A).2.1 W ≤
      (ofSpf A).openSectionsTopology W := by
  let hIA := (IsAdicRing.ideal_spec A).2.1
  refine le_iInf fun U ↦ le_iInf fun hU ↦ le_iInf fun hUW ↦ ?_
  let e := forgetToLocallyRingedSpace.mapIso hU.isoSpf
  let k : Spf hU.Sections ⟶ Spf A := e.inv ≫ (Spf A).ofRestrict U.isOpenEmbedding
  have hle : (⊤ : Opens (Spf.carrier hU.Sections)) ≤ (Opens.map k.base).obj W :=
    fun z _ ↦ hUW (e.inv.base z).2
  have hcomp : k.c.app (op W) ≫ (Spf hU.Sections).presheaf.map (homOfLE hle).op ≫
        (Spf.topSectionsIso hU.Sections).hom = (Spf A).presheaf.map (homOfLE hUW).op := by
    -- Unfold `ofSpf A` / `Spf A` and `hU.Sections` to `presheaf.obj (op U)`.
    erw [← Category.assoc, LocallyRingedSpace.comp_ofRestrict_c_app_le hUW e.inv hle,
      Category.assoc, Category.assoc, isoSpf_inv_c_app_top_comp_topSectionsIso_hom hU,
      Iso.hom_inv_id, Category.comp_id]; rfl
  let hIU := (IsAdicRing.ideal_spec hU.Sections).2.1
  let _ := Spf.quotientSectionsTopology hIA W; let _ := Spf.quotientSectionsTopology hIU ⊤
  let _ := Spf.quotientSectionsTopology hIU ((Opens.map k.base).obj W)
  exact continuous_iff_le_induced.mp <| ((Spf.isHomeomorph_topSectionsIso hU.Sections).continuous
    |>.comp ((Spf.quotientSectionsTopology_restrict hIU hle).comp (Spf.continuous_c_app k W))).congr
      (ConcreteCategory.congr_hom hcomp)

private theorem sectionsTopology_basicOpen_le (f : A) :
    (ofSpf A).sectionsTopology (Spf.basicOpen f) (isAffineOpen_basicOpen A f) ≤
      Spf.quotientSectionsTopology (IsAdicRing.ideal_spec A).2.1 (Spf.basicOpen f) := by
  let B := AdicRing.CompletedAway A f; let U := Spf.basicOpen f; let e := Spf.restrictBasicOpenIso f
  let hIAfg := (IsAdicRing.ideal_spec A).1; let hIA := (IsAdicRing.ideal_spec A).2.1
  let hIBfg := (IsAdicRing.ideal_spec B).1; let hIB := (IsAdicRing.ideal_spec B).2.1
  have hpre : (Opens.map (Spf.basicOpenι f).base).obj U = ⊤ :=
    Opens.ext (Set.eq_univ_of_forall fun p ↦ (Spf.range_basicOpenι f).le ⟨p, rfl⟩)
  have hff : Spf.basicOpen (f * f) = U := by rw [Spf.basicOpen_mul, inf_idem]
  have hsplit : (Spf B).presheaf.map (eqToHom (congrArg op
        (Spf.basicOpenι_preimage_basicOpen f f))) =
      (Spf B).presheaf.map (homOfLE hpre.ge).op ≫ (Spf B).presheaf.map (homOfLE le_top).op := by
    -- Unfold `(Spf B).presheaf` carrier to `Spf.carrier B`.
    erw [← Functor.map_comp]
    exact congrArg (Spf B).presheaf.map (Quiver.Hom.unop_inj (Subsingleton.elim _ _))
  have hres : (Spf.basicOpenι f).c.app (op U) ≫ (Spf B).presheaf.map (homOfLE hpre.ge).op =
      (chartSectionsIso (ofSpf A) U e).hom ≫ (Spf.topSectionsIso B).inv := by
    have hpre' : (⊤ : Opens _) ≤ (Opens.map (e.inv ≫
        (Spf A).ofRestrict (U : Opens (Spf A).toTopCat).isOpenEmbedding).base).obj U :=
      (Spf.restrictBasicOpenIso_inv_ofRestrict f).symm ▸ hpre.ge
    have hsub {k₁ k₂ : Spf B ⟶ Spf A} (hk : k₁ = k₂)
        (h₁ : (⊤ : Opens _) ≤ (Opens.map k₁.base).obj U) (h₂) : k₁.c.app (op U) ≫
          (Spf B).presheaf.map (homOfLE h₁).op = k₂.c.app (op U) ≫
          (Spf B).presheaf.map (homOfLE h₂).op := by subst hk; rfl
    rw [← hsub (Spf.restrictBasicOpenIso_inv_ofRestrict f) hpre' hpre.ge,
      LocallyRingedSpace.comp_ofRestrict_c_app_le (le_refl U) e.inv hpre']
    -- Unfold `(Spf A).presheaf` carrier to `Spf.carrier A` and `chartSectionsIso`.
    erw [TopCat.Presheaf.map_eq_id, Category.id_comp]
    exact (Iso.eq_comp_inv (Spf.topSectionsIso B)).mpr (Category.assoc _ _ _)
  have hι := Spf.basicOpenι_c_app f f
  -- Reassociate and substitute `hres` past `Spf.basicOpenι`.
  erw [hsplit, Category.assoc, reassoc_of% hres, Category.assoc] at hι
  let _ := (ofSpf A).sectionsTopology U (isAffineOpen_basicOpen A f)
  let _ := Spf.quotientSectionsTopology hIB ⊤
  let _ := Spf.quotientSectionsTopology hIB (Spf.basicOpen (algebraMap A B f))
  have htop_inv : @Continuous _ _ _ (Spf.quotientSectionsTopology hIB ⊤)
      (Spf.topSectionsIso B).inv :=
    ((@Equiv.isHomeomorph_iff _ _ (Spf.quotientSectionsTopology hIB ⊤) _
      (Spf.topSectionsIso B).commRingCatIsoToRingEquiv.toEquiv).mp
      (Spf.isHomeomorph_topSectionsIso B)).2
  have hcont : Continuous ((chartSectionsIso (ofSpf A) U e).hom ≫ (Spf.topSectionsIso B).inv ≫
      (Spf B).presheaf.map (homOfLE (le_top : Spf.basicOpen (algebraMap A B f) ≤ ⊤)).op ≫
      (Spf.basicOpenSectionsIso hIB hIBfg (algebraMap A B f)).hom) :=
    (Spf.quotientSectionsTopology_basic hIB hIBfg _).continuous.comp <|
      (Spf.quotientSectionsTopology_restrict hIB le_top).comp <| htop_inv.comp
        (isHomeomorph_chartSectionsIso (ofSpf A) U (isAffineOpen_basicOpen A f) e).continuous
  have hres_ind : @Topology.IsInducing _ _ (Spf.quotientSectionsTopology hIA U)
      (Spf.quotientSectionsTopology hIA (Spf.basicOpen (f * f)))
      ((Spf A).presheaf.map (homOfLE ((Spf.basicOpen_mul f f).le.trans inf_le_right)).op) := by
    generalize_proofs hle; revert hle; rw [hff]; intro hle
    -- Unfold `(Spf A).presheaf` carrier to `Spf.carrier A` for `map_eq_id`.
    let _ := Spf.quotientSectionsTopology hIA U; erw [TopCat.Presheaf.map_eq_id]; exact .id
  have hind : Spf.quotientSectionsTopology hIA U = TopologicalSpace.induced
      ((Spf A).presheaf.map (homOfLE ((Spf.basicOpen_mul f f).le.trans inf_le_right)).op ≫
        (Spf.basicOpenSectionsIso hIA hIAfg (f * f)).hom ≫
        (AdicRing.CompletedAway.iterateEquiv f f).symm.toCommRingCatIso.hom) inferInstance := by
    let _ := Spf.quotientSectionsTopology hIA U
    let _ := Spf.quotientSectionsTopology hIA (Spf.basicOpen (f * f))
    exact ((Homeomorph.mk (AdicRing.CompletedAway.iterateEquiv f f).symm.toEquiv
      (AdicRing.CompletedAway.continuous_iterateEquiv_symm f f)
      (AdicRing.CompletedAway.continuous_iterateEquiv f f)).isInducing.comp
      ((Spf.quotientSectionsTopology_basic hIA hIAfg _).isInducing.comp hres_ind)).eq_induced
  exact hind.symm ▸ continuous_iff_le_induced.mp (hcont.congr (ConcreteCategory.congr_hom hι))

/-- On an affine formal spectrum `ofSpf A`, the general `openSectionsTopology` agrees with
`Spf.quotientSectionsTopology` on every open `W` (EGA I, Ch. I, 10.4.5). -/
theorem openSectionsTopology_ofSpf (W : Opens (ofSpf A)) : (ofSpf A).openSectionsTopology W =
    Spf.quotientSectionsTopology (IsAdicRing.ideal_spec A).2.1 W := by
  refine le_antisymm ?_ (quotientSectionsTopology_le_openSectionsTopology A W)
  -- Unfold `ofSpf A` carrier to `Spf.carrier A` for `quotientSectionsTopology_def`.
  erw [Spf.quotientSectionsTopology_def]; refine le_iInf₂ fun f hf ↦ ?_
  rw [← Spf.quotientSectionsTopology_basicOpen (IsAdicRing.ideal_spec A).2.1 f]
  exact iInf_le_of_le (Spf.basicOpen f) <| iInf_le_of_le (isAffineOpen_basicOpen A f) <|
    iInf_le_of_le hf (induced_mono (sectionsTopology_basicOpen_le A f))

/-- On an affine formal open `U` of `ofSpf A`, `sectionsTopology` agrees with
`Spf.quotientSectionsTopology` (EGA I, Ch. I, 10.4.5). -/
theorem sectionsTopology_ofSpf {U : Opens (ofSpf A)} (hU : (ofSpf A).IsAffineOpen U) :
    (ofSpf A).sectionsTopology U hU =
      Spf.quotientSectionsTopology (IsAdicRing.ideal_spec A).2.1 U := by
  rw [← openSectionsTopology_eq_sectionsTopology (ofSpf A) U hU, openSectionsTopology_ofSpf]

/-- `Spf.topSectionsIso A` is a homeomorphism from `(Γ(ofSpf A, ⊤), sectionsTopology ⊤)` to `A`. -/
theorem isHomeomorph_topSectionsIso :
    @IsHomeomorph _ _ ((ofSpf A).sectionsTopology ⊤ (isAffineOpen_top_ofSpf A))
      ‹TopologicalSpace A› (Spf.topSectionsIso A).hom :=
  sectionsTopology_ofSpf A (isAffineOpen_top_ofSpf A) ▸ Spf.isHomeomorph_topSectionsIso A

end OfSpf

/-- When `D(a) ⊆ Spf hU.Sections` maps into an affine open `V ≤ W`, the section map
`Γ(Y, W) → Γ(X, U) → CompletedAway _ a` factors through `Γ(Y, V)` via `Spf.sectionsHom`. -/
private theorem exists_sectionsHom_eq_basicOpen_res {X Y : FormalScheme.{u}} (f : X ⟶ Y)
    {W : Opens Y} {U : Opens X} (hU : X.IsAffineOpen U)
    (hUW : U ≤ (Opens.map (forgetToLocallyRingedSpace.map f).base).obj W)
    {V : Opens Y} (hV : Y.IsAffineOpen V) (hVW : V ≤ W) (a : hU.Sections)
    (ha_le : Spf.basicOpen a ≤ (Opens.map (forgetToLocallyRingedSpace.map hU.isoSpf.inv ≫
      X.toLocallyRingedSpace.ofRestrict U.isOpenEmbedding ≫
      forgetToLocallyRingedSpace.map f).base).obj V) :
    ∃ g : Spf (AdicRing.CompletedAway hU.Sections a) ⟶ Spf hV.Sections,
      ∀ s : Y.presheaf.obj (op W), Spf.sectionsHom g (Y.presheaf.map (homOfLE hVW).op s) =
        (Spf.basicOpenSectionsIso (IsAdicRing.ideal_spec hU.Sections).2.1
          (IsAdicRing.ideal_spec hU.Sections).1 a).hom
          ((Spf hU.Sections).presheaf.map (homOfLE (le_top : Spf.basicOpen a ≤ ⊤)).op
            ((Spf.topSectionsIso hU.Sections).inv (X.presheaf.map (homOfLE hUW).op
              ((forgetToLocallyRingedSpace.map f).c.app (op W) s)))) := by
  let A := hU.Sections; obtain ⟨hIAfg, hIA, _⟩ := IsAdicRing.ideal_spec A
  let fL := forgetToLocallyRingedSpace.map f; let e := forgetToLocallyRingedSpace.mapIso hU.isoSpf
  let jU := X.toLocallyRingedSpace.ofRestrict U.isOpenEmbedding
  let jV := Y.toLocallyRingedSpace.ofRestrict V.isOpenEmbedding
  let rU := X.toLocallyRingedSpace.restrictTopSectionsIso U
  let m := Spf.map (algebraMap A _) (AdicRing.CompletedAway.continuous_algebraMap A a)
  have hsub : Set.range ((m ≫ e.inv) ≫ jU ≫ fL).base ⊆ Set.range jV.base := by
    rintro _ ⟨p, rfl⟩
    exact ⟨⟨_, ha_le (SetLike.mem_coe.mp ((by rw [Spf.map_base, ← Spf.basicOpenι_base,
      Spf.range_basicOpenι] : Set.range m.base = (Spf.basicOpen a : Set (Spf.carrier A))) ▸
      Set.mem_range_self p))⟩, rfl⟩
  let l := LocallyRingedSpace.IsOpenImmersion.lift jV ((m ≫ e.inv) ≫ jU ≫ fL) hsub
  let g : Spf _ ⟶ Spf hV.Sections := l ≫ forgetToLocallyRingedSpace.map hV.isoSpf.hom
  refine ⟨g, fun s ↦ ?_⟩
  have he_inv (t : X.presheaf.obj (op U)) :
      e.inv.c.app (op ⊤) (rU.hom t) = (Spf.topSectionsIso A).inv t :=
    (ConcreteCategory.bijective_of_isIso (Spf.topSectionsIso A).hom).injective <| by
      -- Unfold `A := hU.Sections` to `X.presheaf.obj (op U)`.
      erw [ConcreteCategory.congr_hom (isoSpf_inv_c_app_top_comp_topSectionsIso_hom hU),
        ConcreteCategory.congr_hom rU.hom_inv_id,
        ConcreteCategory.congr_hom (Spf.topSectionsIso A).inv_hom_id]; rfl
  let π := (Spf.topSectionsIso (AdicRing.CompletedAway A a)).hom
  have hm2 (t : A) : π (m.c.app (op ⊤) ((Spf.topSectionsIso A).inv t)) =
      (Spf.basicOpenSectionsIso hIA hIAfg a).hom ((Spf A).presheaf.map
        (homOfLE (le_top : Spf.basicOpen a ≤ ⊤)).op ((Spf.topSectionsIso A).inv t)) := by
    rw [← Spf.sectionsHom_apply, Spf.sectionsHom_map]
    exact ConcreteCategory.congr_hom
      ((Iso.comp_inv_eq _).mp (Spf.algebraMap_comp_basicOpenSectionsIso_inv a)) t
  have h1 : Spf.sectionsHom g (Y.presheaf.map (homOfLE hVW).op s) =
      π (l.c.app (op ⊤) ((Y.toLocallyRingedSpace.restrictTopSectionsIso V).hom
        (Y.presheaf.map (homOfLE hVW).op s))) :=
    (Spf.sectionsHom_apply g _).trans <| congrArg (fun x ↦ π (l.c.app (op ⊤) x))
      (ConcreteCategory.congr_hom (topSectionsIso_inv_isoSpf_hom_c_app_top hV) _)
  exact h1.trans <| (congrArg π <| ConcreteCategory.congr_hom
    (LocallyRingedSpace.restrictTopSectionsIso_hom_c_app_top_of_fac_le fL hVW hUW l
      (m ≫ e.inv) (LocallyRingedSpace.IsOpenImmersion.lift_fac jV _ hsub)) s).trans <|
    (congrArg (π ∘ m.c.app (op ⊤)) (he_inv _)).trans (hm2 _)

private theorem continuous_of_basicOpen_glue {T : Type*} [TopologicalSpace T]
    {X : FormalScheme.{u}} {U : Opens X} (hU : X.IsAffineOpen U) (g : T → hU.Sections)
    (hcover : ∀ p : Spf.carrier hU.Sections, ∃ a : hU.Sections, p ∈ Spf.basicOpen a ∧
      @Continuous _ _ ‹TopologicalSpace T› inferInstance
        (fun t ↦ (Spf.basicOpenSectionsIso (IsAdicRing.ideal_spec hU.Sections).2.1
            (IsAdicRing.ideal_spec hU.Sections).1 a).hom
          ((Spf hU.Sections).presheaf.map (homOfLE (le_top : Spf.basicOpen a ≤ ⊤)).op
            ((Spf.topSectionsIso hU.Sections).inv (g t))))) :
    @Continuous _ _ ‹TopologicalSpace T› (X.sectionsTopology U hU) g := by
  let A := hU.Sections; obtain ⟨hIAfg, hIA, _⟩ := IsAdicRing.ideal_spec A
  choose a ha_mem ha_cont using hcover; let _ := Spf.quotientSectionsTopology hIA ⊤
  let _ (p) := Spf.quotientSectionsTopology hIA (Spf.basicOpen (a p))
  let _ := X.sectionsTopology U hU
  have hcont : @Continuous _ _ ‹TopologicalSpace T› (Spf.quotientSectionsTopology hIA ⊤)
      ((Spf.topSectionsIso A).inv ∘ g) :=
    (Spf.quotientSectionsTopology_glue hIA (fun _ ↦ le_top)
        fun p _ ↦ Opens.mem_iSup.mpr ⟨p, ha_mem p⟩).isInducing.continuous_iff.mpr <|
      continuous_pi_iff.mpr fun p ↦ (Spf.quotientSectionsTopology_basic hIA hIAfg
        (a p)).isInducing.continuous_iff.mpr (ha_cont p)
  exact (@Continuous.comp _ _ _ ‹TopologicalSpace T› (Spf.quotientSectionsTopology hIA ⊤)
    (X.sectionsTopology U hU) _ _ (Spf.isHomeomorph_topSectionsIso A).continuous hcont).congr
    fun t ↦ ConcreteCategory.congr_hom (Spf.topSectionsIso A).inv_hom_id (g t)

/-- **Automatic continuity on all opens** (EGA I, Ch. I, 10.4.6): every morphism of formal schemes
`f : X ⟶ Y` is continuous on rings of sections over arbitrary opens `W ⊆ Y`, equipped with
`openSectionsTopology`. -/
theorem continuous_c_app_openSectionsTopology {X Y : FormalScheme.{u}} (f : X ⟶ Y) (W : Opens Y) :
    @Continuous _ _ (Y.openSectionsTopology W)
      (X.openSectionsTopology ((Opens.map (forgetToLocallyRingedSpace.map f).base).obj W))
      ((forgetToLocallyRingedSpace.map f).c.app (op W)) := by
  let _ := Y.openSectionsTopology W; let fL := forgetToLocallyRingedSpace.map f
  refine (continuous_iff_openSectionsTopology X _ _).mpr fun U hU hUW ↦
    continuous_of_basicOpen_glue hU _ fun p ↦ ?_
  obtain ⟨V, hV, hxV, hVW⟩ := Y.exists_isAffineOpen_mem_le
    (hUW ((forgetToLocallyRingedSpace.map hU.isoSpf.inv).base p).2)
  obtain ⟨_, ⟨a, rfl⟩, ha_mem, ha_le⟩ := Opens.isBasis_iff_nbhd.mp Spf.isBasis_basicOpen
    (show p ∈ (Opens.map (forgetToLocallyRingedSpace.map hU.isoSpf.inv ≫
      X.toLocallyRingedSpace.ofRestrict U.isOpenEmbedding ≫ fL).base).obj V from hxV)
  obtain ⟨g, hg⟩ := exists_sectionsHom_eq_basicOpen_res f hU hUW hV hVW a ha_le
  exact ⟨a, ha_mem, ((Spf.continuous_sectionsHom g).comp
    ((continuous_iff_openSectionsTopology Y W id).mp continuous_id V hV hVW)).congr hg⟩

/-- For any open cover `W ≤ ⨆ i, V i` by opens `V i ≤ W`, the restriction map from
`Γ(X, W)` (with `X.openSectionsTopology W`) into `∏ i, Γ(X, V i)` (with
`X.openSectionsTopology (V i)`) is a topological embedding (`IsInducing`). -/
theorem openSectionsTopology_isInducing_pi {ι : Type*} (X : FormalScheme.{u}) {W : Opens X}
    {V : ι → Opens X} (hV : ∀ i, V i ≤ W) (hcov : W ≤ ⨆ i, V i) :
    @Topology.IsInducing (X.presheaf.obj (op W)) (∀ i : ι, X.presheaf.obj (op (V i)))
      (X.openSectionsTopology W)
      (@Pi.topologicalSpace ι _ fun i ↦ X.openSectionsTopology (V i))
      (fun s i ↦ X.presheaf.map (homOfLE (hV i)).op s) := by
  let _ := X.openSectionsTopology W; let _ (i : ι) := X.openSectionsTopology (V i)
  let Φ : X.presheaf.obj (op W) → ∀ i : ι, X.presheaf.obj (op (V i)) :=
    fun s i ↦ X.presheaf.map (homOfLE (hV i)).op s
  refine ⟨le_antisymm (continuous_iff_le_induced.mp (continuous_pi fun i ↦
    continuous_restrict_openSectionsTopology X (hV i)))
    (le_iInf fun U ↦ le_iInf fun hU ↦ le_iInf fun hUW ↦ continuous_iff_le_induced.mp ?_)⟩
  let _ := TopologicalSpace.induced Φ Pi.topologicalSpace
  refine continuous_of_basicOpen_glue hU _ fun p ↦ ?_
  let A := hU.Sections; let e := forgetToLocallyRingedSpace.mapIso hU.isoSpf
  let jU := X.toLocallyRingedSpace.ofRestrict U.isOpenEmbedding
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (hcov (hUW (e.inv.base p).2))
  obtain ⟨_, ⟨a, rfl⟩, ha_mem, ha_le⟩ := Opens.isBasis_iff_nbhd.mp Spf.isBasis_basicOpen
    (show p ∈ (Opens.map (e.inv ≫ jU).base).obj (V i) from hi)
  let l := Spf.basicOpenι a ≫ e.inv ≫ jU
  have hl : LocallyRingedSpace.IsOpenImmersion l := @LocallyRingedSpace.IsOpenImmersion.comp _ _ _
    (Spf.basicOpenι a) (Spf.isOpenImmersion_basicOpenι a) _
    (@LocallyRingedSpace.IsOpenImmersion.comp _ _ _ e.inv
      (LocallyRingedSpace.IsOpenImmersion.of_isIso e.inv) jU
      (show LocallyRingedSpace.IsOpenImmersion (X.toLocallyRingedSpace.ofRestrict U.isOpenEmbedding)
        from inferInstance))
  let Up : Opens X := ⟨Set.range l.base, hl.base_open.isOpen_range⟩
  have hUp : X.IsAffineOpen Up := (X.isAffineOpen_iff Up).mpr
    ⟨AdicRing.CompletedAway A a, inferInstance, inferInstance, inferInstance, inferInstance,
      ⟨(LocallyRingedSpace.isoOfSheafedSpaceIso <| SheafedSpace.isoMk <|
        PresheafedSpace.IsOpenImmersion.isoOfRangeEq l.toHom (X.toLocallyRingedSpace.ofRestrict
          Up.isOpenEmbedding).toHom Subtype.range_coe.symm).symm⟩⟩
  have hUpV : Up ≤ V i := fun _ ⟨q, hq⟩ ↦ hq ▸ ha_le ((Spf.range_basicOpenι a).le ⟨q, rfl⟩)
  have hUp_le : Spf.basicOpen a ≤ (Opens.map (forgetToLocallyRingedSpace.map hU.isoSpf.inv ≫
      X.toLocallyRingedSpace.ofRestrict U.isOpenEmbedding ≫
      forgetToLocallyRingedSpace.map (𝟙 X)).base).obj Up := fun q hq ↦
    let ⟨r, hr⟩ := (Spf.range_basicOpenι a).ge hq; ⟨r, hr ▸ rfl⟩
  obtain ⟨g, hg⟩ :=
    exists_sectionsHom_eq_basicOpen_res (𝟙 X) hU hUW hUp (hUpV.trans (hV i)) a hUp_le
  refine ⟨a, ha_mem, ((Spf.continuous_sectionsHom g).comp ((continuous_iInf_dom (i := Up) <|
    continuous_iInf_dom (i := hUp) <| continuous_iInf_dom (i := hUpV) <|
    continuous_induced_dom (t := X.sectionsTopology Up hUp)).comp ((@continuous_apply _
      (fun i ↦ X.presheaf.obj (op (V i))) (fun i ↦ X.openSectionsTopology (V i)) i).comp
      (@continuous_induced_dom _ _ Φ Pi.topologicalSpace)))).congr fun s ↦ ?_⟩
  have hΦ : (X.presheaf.map (homOfLE hUpV).op : _ → hUp.Sections) (Φ s i) =
      X.presheaf.map (homOfLE (hUpV.trans (hV i))).op s := by
    simp only [Φ, ← ConcreteCategory.comp_apply, ← X.presheaf.map_comp, ← op_comp, homOfLE_comp]
  -- Unfold `hUp.Sections` across `X.presheaf.map` before rewriting by `hΦ` and `hg s`.
  change Spf.sectionsHom g (X.presheaf.map (homOfLE hUpV).op (Φ s i)) = _
  erw [hΦ, hg s]; rfl
end SpecialCasesAndOpenTopology
end TauCeti.FormalScheme
