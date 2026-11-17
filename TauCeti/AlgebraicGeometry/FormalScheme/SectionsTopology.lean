/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.FormalScheme.Basic
public import TauCeti.AlgebraicGeometry.FormalScheme.Spf.HomEquiv
public import TauCeti.Geometry.RingedSpace.LocallyRingedSpace.Restrict

import TauCeti.Topology.Discrete
import TauCeti.Topology.Sheaves.Presheaf

/-!
# Canonical section topologies on formal schemes

For an affine formal open `U` of a formal scheme `X`, any chart `e : X|_U ≅ Spf B` identifies
`Γ(X, U) ≅ B` (`chartSectionsIso`), inducing a chart-independent complete separated adic topology
`X.sectionsTopology U hU` (packaged on `hU.Sections`, with `hU.isoSpf : X.restrict U ≅ ofSpf _`;
EGA I, Ch. I, 10.4.5). Topologically nilpotent sections are cut out by residue vanishing on `U`,
affine section maps are continuous (`sectionMap_continuous`), and for arbitrary opens `W ⊆ X`,
`X.openSectionsTopology W` makes every morphism continuous on sections
(`continuous_c_app_openSectionsTopology`; EGA I, Ch. I, 10.4.6).
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
    (chartSectionsIso X U e).hom s =
      (Spf.topSectionsIso B).hom
        (e.inv.c.app (op ⊤) ((X.toLocallyRingedSpace.restrictTopSectionsIso U).hom s)) := (rfl)

theorem chartSectionsIso_inv_apply (b : B) :
    (chartSectionsIso X U e).inv b =
      (X.toLocallyRingedSpace.restrictTopSectionsIso U).inv
        (e.hom.c.app (op ⊤) ((Spf.topSectionsIso B).inv b)) := (rfl)

end ChartSections

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
      (e₁.hom.c.app (op ⊤) : (Spf B₁).presheaf.obj (op ⊤) ⟶ _) ≫
        e₂.inv.c.app (op ⊤) ≫ (Spf.topSectionsIso B₂).hom := by
    rw [RingEquiv.toRingHom_eq_coe, Spf.isoToRingEquiv_toRingHom,
      ← Spf.c_app_top_comp_topSectionsIso_hom (e₂.symm ≪≫ e₁).hom]
    exact Category.assoc _ _ _
  exact (Category.assoc _ _ _).trans <| congrArg (_ ≫ ·) <|
    (Category.assoc _ _ _).trans <| (congrArg (_ ≫ ·) hmid).trans <|
      (Category.assoc _ _ _).symm.trans <|
        (congrArg (· ≫ _) (LocallyRingedSpace.iso_inv_c_app_top_comp_hom e₁)).trans
          (Category.id_comp _)

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
@[instance_reducible]
noncomputable def sectionsTopology : TopologicalSpace (X.presheaf.obj (op U)) :=
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
  let _ := X.sectionsTopology U hU; let φ := (chartSectionsIso X U e).commRingCatIsoToRingEquiv
  have he : Topology.IsInducing φ := ⟨sectionsTopology_eq_induced X U hU e⟩
  exact IsTopologicalSemiring.toIsTopologicalRing
    { toContinuousAdd := he.continuousAdd φ, toContinuousMul := he.continuousMul φ }

/-- Equipped with `X.sectionsTopology U hU`, `Γ(X, U)` is a complete separated adic ring of finite
ideal type (EGA I, Ch. I, 10.4.5). -/
theorem sectionsTopology_isAdicRing :
    @IsAdicRing (X.presheaf.obj (op U)) _ (X.sectionsTopology U hU)
      (X.sectionsTopology_isTopologicalRing U hU) := by
  obtain ⟨B, _, _, _, _, ⟨e⟩⟩ := (X.isAffineOpen_iff U).mp hU
  let _ := X.sectionsTopology U hU; have := X.sectionsTopology_isTopologicalRing U hU
  let φ : (X.presheaf.obj (op U) : Type u) ≃+* B :=
    (chartSectionsIso X U e).commRingCatIsoToRingEquiv
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
  let φ : (X.presheaf.obj (op U) : Type u) ≃+* B :=
    (chartSectionsIso X U e).commRingCatIsoToRingEquiv
  obtain ⟨hφ₁, hφ₂⟩ := φ.toEquiv.isHomeomorph_iff.mp (isHomeomorph_chartSectionsIso X U hU e)
  have hnilp : IsTopologicallyNilpotent s ↔ IsTopologicallyNilpotent (φ s) :=
    ⟨fun hs ↦ hs.map (φ := φ.toRingHom) hφ₁,
      fun hs ↦ by simpa using hs.map (φ := φ.symm.toRingHom) hφ₂⟩
  obtain ⟨-, hIB, -⟩ := IsAdicRing.ideal_spec B
  rw [hnilp, hIB.isTopologicallyNilpotent_iff_mem_radical, Ideal.radical_eq_sInf, Ideal.mem_sInf]
  have hrad : (∀ p ∈ {p : Ideal B | IsAdicRing.ideal B ≤ p ∧ p.IsPrime}, φ s ∈ p) ↔
      ∀ p : Spf.carrier B, (Spf B).Γevaluation p ((Spf.topSectionsIso B).inv (φ s)) = 0 :=
    ⟨fun h p ↦ (Spf.Γevaluation_topSectionsIso_inv_eq_zero_iff p (φ s)).mpr
      (h _ ⟨(Spf.mem_carrier_iff_le hIB).mp p.2, p.1.isPrime⟩),
     fun h q hq ↦ (Spf.Γevaluation_topSectionsIso_inv_eq_zero_iff
      ⟨⟨q, hq.2⟩, (Spf.mem_carrier_iff_le hIB).mpr hq.1⟩ (φ s)).mp (h _)⟩
  rw [hrad]
  have hsec₂ : (Spf.topSectionsIso B).inv (φ s) =
      e.inv.c.app (op ⊤) ((X.toLocallyRingedSpace.restrictTopSectionsIso U).hom s) :=
    ConcreteCategory.congr_hom (Spf.topSectionsIso B).hom_inv_id _
  have hsec₁ : e.hom.c.app (op ⊤) ((Spf.topSectionsIso B).inv (φ s)) =
      (X.toLocallyRingedSpace.restrictTopSectionsIso U).hom s :=
    (congrArg (e.hom.c.app (op ⊤)) hsec₂).trans
      (ConcreteCategory.congr_hom (LocallyRingedSpace.iso_inv_c_app_top_comp_hom e) _)
  refine ⟨fun h x ↦ ?_, fun h p ↦ ?_⟩
  · rw [X.toLocallyRingedSpace.evaluation_eq_zero_iff_restrict_Γevaluation_eq_zero, ← hsec₁,
      ← LocallyRingedSpace.Γevaluation_naturality_apply e.hom x, h (e.hom.base x), map_zero]
  · let p' : Spf B := p
    rw [hsec₂, ← LocallyRingedSpace.Γevaluation_naturality_apply e.inv p',
      (X.toLocallyRingedSpace.evaluation_eq_zero_iff_restrict_Γevaluation_eq_zero U
        (e.inv.base p') s).mp (h (e.inv.base p')), map_zero]

end ChartTopology

section CanonicalChart

variable {X : FormalScheme.{u}} {U : Opens X}

/-- A finitely generated ideal `J` of `Γ(X, U)` over an affine formal open `U` defines
`X.sectionsTopology U hU` whenever its radical consists of the sections vanishing in every residue
field on `U` (EGA I, Ch. I, 10.4.5). -/
theorem sectionsTopology_eq_adic (hU : X.IsAffineOpen U)
    {J : Ideal (X.presheaf.obj (op U))} (hJfg : J.FG)
    (hJrad : ∀ s : X.presheaf.obj (op U),
      s ∈ J.radical ↔ ∀ x : U, X.toLocallyRingedSpace.evaluation x s = 0) :
    @IsAdic _ _ (X.sectionsTopology U hU) J := by
  let _ := X.sectionsTopology U hU
  have := X.sectionsTopology_isTopologicalRing U hU
  have := X.sectionsTopology_isAdicRing U hU
  obtain ⟨hIfg, hIadic, -⟩ := IsAdicRing.ideal_spec (X.presheaf.obj (op U))
  refine hIadic.of_radical_eq hIfg hJfg (Ideal.ext fun s ↦ ?_)
  exact hIadic.isTopologicallyNilpotent_iff_mem_radical.symm.trans <|
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

instance (hU : X.IsAffineOpen U) : IsAdicRing hU.Sections :=
  X.sectionsTopology_isAdicRing U hU

/-- Every affine formal open `U ⊆ X` is canonically isomorphic as a formal scheme to the formal
spectrum of `hU.Sections` (EGA I, Ch. I, 10.4.5). -/
noncomputable def isoSpf (hU : X.IsAffineOpen U) : X.restrict U ≅ ofSpf hU.Sections :=
  let φ : hU.Sections ≃+* (chosenChart hU).B :=
    (chartSectionsIso X U (chosenChart hU).iso).commRingCatIsoToRingEquiv
  let hφ := φ.toEquiv.isHomeomorph_iff.mp
    (isHomeomorph_chartSectionsIso X U hU (chosenChart hU).iso)
  InducedCategory.isoMk ((chosenChart hU).iso ≪≫ Spf.mapIso φ hφ.1 hφ.2)

end IsAffineOpen

/-- On global sections, `hU.isoSpf.hom` identifies `Spf.topSectionsIso` with
`X.toLocallyRingedSpace.restrictTopSectionsIso U`, independently of any chosen chart. -/
@[reassoc (attr := simp)]
theorem topSectionsIso_inv_isoSpf_hom_c_app_top (hU : X.IsAffineOpen U) :
    (Spf.topSectionsIso hU.Sections).inv ≫
      ((forgetToLocallyRingedSpace.map hU.isoSpf.hom).c.app (op ⊤) :
        (Spf hU.Sections).presheaf.obj (op ⊤) ⟶
          (X.toLocallyRingedSpace.restrict U.isOpenEmbedding).presheaf.obj (op ⊤)) =
      (X.toLocallyRingedSpace.restrictTopSectionsIso U).hom := by
  let e := (chosenChart hU).iso
  let φ : hU.Sections ≃+* (chosenChart hU).B := (chartSectionsIso X U e).commRingCatIsoToRingEquiv
  let hφ := φ.toEquiv.isHomeomorph_iff.mp (isHomeomorph_chartSectionsIso X U hU e)
  have hφ₁ : Continuous φ.toRingHom := hφ.1
  have hm : (Spf.topSectionsIso hU.Sections).inv ≫ (Spf.map φ.toRingHom hφ₁).c.app (op ⊤) =
      (X.toLocallyRingedSpace.restrictTopSectionsIso U).hom ≫ e.inv.c.app (op ⊤) := by
    have h1 : (Spf.topSectionsIso hU.Sections).inv ≫ (Spf.map φ.toRingHom hφ₁).c.app (op ⊤) =
        (chartSectionsIso X U e).hom ≫ (Spf.topSectionsIso (chosenChart hU).B).inv := by
      rw [Spf.topSectionsIso_inv_comp_c_app_top, Spf.sectionsHom_map]; rfl
    exact h1.trans <| (Category.assoc _ _ _).trans <| congrArg (_ ≫ ·) <|
      (Category.assoc _ _ _).trans <|
        (congrArg (_ ≫ ·) (Iso.hom_inv_id _)).trans (Category.comp_id _)
  have hmap : forgetToLocallyRingedSpace.map hU.isoSpf.hom = e.hom ≫ Spf.map φ.toRingHom hφ₁ :=
    congrArg (e.hom ≫ ·) (Spf.mapIso_hom φ hφ₁ hφ.2)
  have hcomp : (forgetToLocallyRingedSpace.map hU.isoSpf.hom).c.app (op ⊤) =
      (Spf.map φ.toRingHom hφ₁).c.app (op ⊤) ≫ e.hom.c.app (op ⊤) :=
    (congrArg (fun k : X.toLocallyRingedSpace.restrict U.isOpenEmbedding ⟶ Spf hU.Sections ↦
      LocallyRingedSpace.Γ.map k.op) hmap).trans
      (LocallyRingedSpace.Γ.map_comp (Spf.map φ.toRingHom hφ₁).op e.hom.op)
  exact (congrArg (_ ≫ ·) hcomp).trans <| (Category.assoc _ _ _).symm.trans <|
    (congrArg (· ≫ _) hm).trans <| (Category.assoc _ _ _).trans <|
      (congrArg (_ ≫ ·) (LocallyRingedSpace.iso_inv_c_app_top_comp_hom e)).trans
        (Category.comp_id _)

/-- Dual form of `topSectionsIso_inv_isoSpf_hom_c_app_top` for `hU.isoSpf.inv`. -/
@[reassoc (attr := simp)]
theorem isoSpf_inv_c_app_top_comp_topSectionsIso_hom (hU : X.IsAffineOpen U) :
    ((forgetToLocallyRingedSpace.map hU.isoSpf.inv).c.app (op ⊤) :
        (X.toLocallyRingedSpace.restrict U.isOpenEmbedding).presheaf.obj (op ⊤) ⟶
          (Spf hU.Sections).presheaf.obj (op ⊤)) ≫
      (Spf.topSectionsIso hU.Sections).hom =
      (X.toLocallyRingedSpace.restrictTopSectionsIso U).inv :=
  (cancel_epi (X.toLocallyRingedSpace.restrictTopSectionsIso U).hom).mp <|
    (congrArg (· ≫ _) (topSectionsIso_inv_isoSpf_hom_c_app_top hU).symm).trans <|
      (Category.assoc _ _ _).trans <|
        (congrArg (_ ≫ ·) <| (Category.assoc _ _ _).symm.trans <|
          (congrArg (· ≫ _) (LocallyRingedSpace.iso_hom_c_app_top_comp_inv
            (forgetToLocallyRingedSpace.mapIso hU.isoSpf))).trans (Category.id_comp _)).trans <|
          (Iso.inv_hom_id _).trans (Iso.hom_inv_id _).symm

/-- **Automatic continuity on affine opens** (EGA I, Ch. I, 10.4.6): for `f : X ⟶ Y` and affine
opens `U ⊆ X`, `V ⊆ Y` with `U ≤ f ⁻¹' V`, `Γ(Y, V) →+* Γ(X, U)` is continuous. -/
theorem sectionMap_continuous {X Y : FormalScheme.{u}} (f : X ⟶ Y) {V : Opens Y}
    (hV : Y.IsAffineOpen V) {U : Opens X} (hU : X.IsAffineOpen U)
    (hUV : U ≤ (Opens.map (forgetToLocallyRingedSpace.map f).base).obj V) :
    @Continuous _ _ (Y.sectionsTopology V hV) (X.sectionsTopology U hU)
      ((forgetToLocallyRingedSpace.map f).c.app (op V) ≫ X.presheaf.map (homOfLE hUV).op) := by
  let jU := X.toLocallyRingedSpace.ofRestrict U.isOpenEmbedding
  let jV := Y.toLocallyRingedSpace.ofRestrict V.isOpenEmbedding
  have hsub : Set.range (jU ≫ forgetToLocallyRingedSpace.map f).base ⊆ Set.range jV.base := by
    rintro _ ⟨x, rfl⟩; exact ⟨⟨(forgetToLocallyRingedSpace.map f).base x.1, hUV x.2⟩, rfl⟩
  let fUV := LocallyRingedSpace.IsOpenImmersion.lift jV (jU ≫ forgetToLocallyRingedSpace.map f) hsub
  have hfac := LocallyRingedSpace.IsOpenImmersion.lift_fac jV
    (jU ≫ forgetToLocallyRingedSpace.map f) hsub
  let g : Spf hU.Sections ⟶ Spf hV.Sections :=
    (forgetToLocallyRingedSpace.map hU.isoSpf.inv ≫ fUV) ≫
      forgetToLocallyRingedSpace.map hV.isoSpf.hom
  have hg : CommRingCat.ofHom (Spf.sectionsHom g) =
      (forgetToLocallyRingedSpace.map f).c.app (op V) ≫ X.presheaf.map (homOfLE hUV).op := by
    have hR : g.c.app (op ⊤) ≫ (Spf.topSectionsIso hU.Sections).hom =
        (forgetToLocallyRingedSpace.map hV.isoSpf.hom).c.app (op ⊤) ≫ fUV.c.app (op ⊤) ≫
          (X.toLocallyRingedSpace.restrictTopSectionsIso U).inv :=
      (Category.assoc _ _ _).trans <| congrArg (_ ≫ ·) <|
        (Category.assoc _ _ _).trans
          (congrArg (_ ≫ ·) (isoSpf_inv_c_app_top_comp_topSectionsIso_hom hU))
    exact (Spf.ofHom_sectionsHom g).trans <| (congrArg (_ ≫ ·) hR).trans <|
      (Category.assoc _ _ _).symm.trans <|
        (congrArg (· ≫ _) (topSectionsIso_inv_isoSpf_hom_c_app_top hV)).trans <|
          (Category.assoc _ _ _).symm.trans <|
            (congrArg (· ≫ _) (LocallyRingedSpace.restrictTopSectionsIso_hom_c_app_top_of_fac
              (forgetToLocallyRingedSpace.map f) hUV fUV hfac)).trans <|
              (Category.assoc _ _ _).trans <| congrArg (_ ≫ ·) <|
                (Category.assoc _ _ _).trans <|
                  (congrArg (_ ≫ ·) (Iso.hom_inv_id _)).trans (Category.comp_id _)
  exact (Spf.continuous_sectionsHom g).congr (ConcreteCategory.congr_hom hg)

end CanonicalChart

section SpecialCasesAndOpenTopology

/-- `Spf.topSectionsIso A` is a homeomorphism from `(Γ(ofSpf A, ⊤), sectionsTopology ⊤)` to `A`. -/
theorem isHomeomorph_topSectionsIso (A : Type u) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [IsAdicRing A] :
    @IsHomeomorph _ _ ((ofSpf A).sectionsTopology ⊤ (isAffineOpen_top_ofSpf A))
      ‹TopologicalSpace A› (Spf.topSectionsIso A).hom := by
  let eTop : (ofSpf A).toLocallyRingedSpace.restrict (⊤ : Opens (ofSpf A)).isOpenEmbedding ≅
      Spf A := (ofSpf A).toLocallyRingedSpace.restrictTopIso
  suffices h : (chartSectionsIso (ofSpf A) ⊤ eTop).hom = (Spf.topSectionsIso A).hom from
    h ▸ isHomeomorph_chartSectionsIso (ofSpf A) ⊤ (isAffineOpen_top_ofSpf A) eTop
  have hhom : (eTop.hom.c.app (op ⊤) : (Spf A).presheaf.obj (op ⊤) ⟶
        ((ofSpf A).toLocallyRingedSpace.restrict (⊤ : Opens (ofSpf A)).isOpenEmbedding).presheaf.obj
          (op ⊤)) =
      ((ofSpf A).toLocallyRingedSpace.restrictTopSectionsIso ⊤).hom := by
    have h := (ofSpf A).toLocallyRingedSpace.ofRestrict_c_app_top ⊤
    rwa [TopCat.Presheaf.map_eq_id, Category.id_comp] at h
  exact (congrArg (· ≫ _) hhom.symm).trans <| (Category.assoc _ _ _).symm.trans <|
    (congrArg (· ≫ _) (LocallyRingedSpace.iso_hom_c_app_top_comp_inv eTop)).trans
      (Category.id_comp _)

/-- `(ofSpf A).sectionsTopology ⊤ _` agrees with `Spf.quotientSectionsTopology _ ⊤`. -/
theorem sectionsTopology_ofSpf_top (A : Type u) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [IsAdicRing A] :
    (ofSpf A).sectionsTopology ⊤ (isAffineOpen_top_ofSpf A) =
      Spf.quotientSectionsTopology (IsAdicRing.ideal_spec A).2.1 ⊤ := by
  let t₁ := (ofSpf A).sectionsTopology ⊤ (isAffineOpen_top_ofSpf A)
  let t₂ := Spf.quotientSectionsTopology (IsAdicRing.ideal_spec A).2.1 ⊤
  exact (@IsHomeomorph.isInducing _ _ t₁ _ _ (isHomeomorph_topSectionsIso A)).eq_induced.trans
    (@IsHomeomorph.isInducing _ _ t₂ _ _ (Spf.isHomeomorph_topSectionsIso A)).eq_induced.symm

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
@[instance_reducible]
noncomputable def openSectionsTopology (X : FormalScheme.{u}) (W : Opens X) :
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
  let _ := X.openSectionsTopology W
  simp only [continuous_iInf_rng, continuous_induced_rng]

/-- On an affine formal open `W ⊆ X`, `X.openSectionsTopology W = X.sectionsTopology W hW`. -/
theorem openSectionsTopology_eq_sectionsTopology (X : FormalScheme.{u}) (W : Opens X)
    (hW : X.IsAffineOpen W) :
    X.openSectionsTopology W = X.sectionsTopology W hW := by
  refine le_antisymm
    (iInf_le_of_le W <| iInf_le_of_le hW <| iInf_le_of_le (le_refl W) ?_)
    (le_iInf fun U ↦ le_iInf fun hU ↦ le_iInf fun hUW ↦ ?_)
  · rw [TopCat.Presheaf.map_eq_id]; exact le_of_eq (induced_id (t := X.sectionsTopology W hW))
  · let _ := X.sectionsTopology W hW; let _ := X.sectionsTopology U hU
    exact continuous_iff_le_induced.mp ((sectionMap_continuous (𝟙 X) hW hU hUW).congr fun _ ↦ rfl)

/-- Restriction maps `Γ(X, W₂) → Γ(X, W₁)` are continuous for `openSectionsTopology`. -/
theorem continuous_restrict_openSectionsTopology (X : FormalScheme.{u}) {W₁ W₂ : Opens X}
    (h : W₁ ≤ W₂) :
    @Continuous _ _ (X.openSectionsTopology W₂) (X.openSectionsTopology W₁)
      (X.presheaf.map (homOfLE h).op) := by
  let _ := X.openSectionsTopology W₂
  rw [continuous_iff_openSectionsTopology]; intro U hU hUW₁
  have hcomp : ((X.presheaf.map (homOfLE hUW₁).op : _ → _) ∘ X.presheaf.map (homOfLE h).op) =
      X.presheaf.map (homOfLE (hUW₁.trans h)).op :=
    funext (ConcreteCategory.congr_hom (X.presheaf.map_comp (homOfLE h).op (homOfLE hUW₁).op).symm)
  rw [hcomp]
  exact (continuous_iff_openSectionsTopology X W₂ id).mp continuous_id U hU (hUW₁.trans h)

/-- Every point of `Spf hU.Sections` over `U ≤ f⁻¹ W` has a basic open mapping into an affine
formal open `V ≤ W` of `Y`. -/
private theorem exists_basicOpen_le_preimage_affine {X Y : FormalScheme.{u}} (f : X ⟶ Y)
    {W : Opens Y} {U : Opens X} (hU : X.IsAffineOpen U)
    (hUW : U ≤ (Opens.map (forgetToLocallyRingedSpace.map f).base).obj W)
    (p : Spf.carrier hU.Sections) :
    ∃ (V : Opens Y) (_ : Y.IsAffineOpen V) (_ : V ≤ W) (a : hU.Sections),
      p ∈ Spf.basicOpen a ∧
        Spf.basicOpen a ≤ (Opens.map (forgetToLocallyRingedSpace.map hU.isoSpf.inv ≫
          X.toLocallyRingedSpace.ofRestrict U.isOpenEmbedding ≫
          forgetToLocallyRingedSpace.map f).base).obj V := by
  obtain ⟨V, hV, hxV, hVW⟩ := Y.exists_isAffineOpen_mem_le
    (hUW ((forgetToLocallyRingedSpace.map hU.isoSpf.inv).base p).2)
  have hpV : p ∈ (Opens.map (forgetToLocallyRingedSpace.map hU.isoSpf.inv ≫
      X.toLocallyRingedSpace.ofRestrict U.isOpenEmbedding ≫
      forgetToLocallyRingedSpace.map f).base).obj V := hxV
  obtain ⟨_, ⟨a, rfl⟩, ha_mem, ha_le⟩ := Opens.isBasis_iff_nbhd.mp Spf.isBasis_basicOpen hpV
  exact ⟨V, hV, hVW, a, ha_mem, ha_le⟩

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
  let fL := forgetToLocallyRingedSpace.map f
  let e : X.toLocallyRingedSpace.restrict U.isOpenEmbedding ≅ Spf A :=
    forgetToLocallyRingedSpace.mapIso hU.isoSpf
  let jU := X.toLocallyRingedSpace.ofRestrict U.isOpenEmbedding
  let jV := Y.toLocallyRingedSpace.ofRestrict V.isOpenEmbedding
  let m := Spf.map (algebraMap A _) (AdicRing.CompletedAway.continuous_algebraMap A a)
  -- Lift `Spf (CompletedAway A a) → Spf A ≅ X|_U → X → Y` through `Y|_V → Y`.
  have hsub : Set.range ((m ≫ e.inv) ≫ jU ≫ fL).base ⊆ Set.range jV.base := by
    rintro _ ⟨p, rfl⟩
    have hr : Set.range m.base = (Spf.basicOpen a : Set (Spf.carrier A)) := by
      rw [Spf.map_base, ← Spf.basicOpenι_base, Spf.range_basicOpenι]
    exact ⟨⟨_, ha_le (SetLike.mem_coe.mp (hr ▸ Set.mem_range_self p))⟩, rfl⟩
  let l := LocallyRingedSpace.IsOpenImmersion.lift jV ((m ≫ e.inv) ≫ jU ≫ fL) hsub
  have hfac := LocallyRingedSpace.IsOpenImmersion.lift_fac jV ((m ≫ e.inv) ≫ jU ≫ fL) hsub
  let g := l ≫ forgetToLocallyRingedSpace.map hV.isoSpf.hom; refine ⟨g, fun s ↦ ?_⟩
  -- Identify `Γ(Y, W) → Γ(Y, V) → CompletedAway A a` via `restrictTopSectionsIso`.
  have he_inv (t : A) :
      e.inv.c.app (op ⊤) ((X.toLocallyRingedSpace.restrictTopSectionsIso U).hom t) =
        (Spf.topSectionsIso A).inv t :=
    (congrArg (e.inv.c.app (op ⊤))
      (ConcreteCategory.congr_hom (topSectionsIso_inv_isoSpf_hom_c_app_top hU) t).symm).trans
      (ConcreteCategory.congr_hom (LocallyRingedSpace.iso_hom_c_app_top_comp_inv e) _)
  let π := (Spf.topSectionsIso (AdicRing.CompletedAway A a)).hom
  have hm2 (t : A) : π (m.c.app (op ⊤) ((Spf.topSectionsIso A).inv t)) =
      (Spf.basicOpenSectionsIso hIA hIAfg a).hom
        ((Spf A).presheaf.map (homOfLE (le_top : Spf.basicOpen a ≤ ⊤)).op
          ((Spf.topSectionsIso A).inv t)) := by
    rw [← Spf.sectionsHom_apply, Spf.sectionsHom_map]
    exact ConcreteCategory.congr_hom
      ((Iso.comp_inv_eq _).mp (Spf.algebraMap_comp_basicOpenSectionsIso_inv a)) t
  calc Spf.sectionsHom g (Y.presheaf.map (homOfLE hVW).op s)
      = π (l.c.app (op ⊤) ((Y.toLocallyRingedSpace.restrictTopSectionsIso V).hom
          (Y.presheaf.map (homOfLE hVW).op s))) :=
        (Spf.sectionsHom_apply g _).trans (congrArg π (congrArg (l.c.app (op ⊤))
          (ConcreteCategory.congr_hom (topSectionsIso_inv_isoSpf_hom_c_app_top hV) _)))
    _ = π (m.c.app (op ⊤) (e.inv.c.app (op ⊤) ((X.toLocallyRingedSpace.restrictTopSectionsIso U).hom
          (X.presheaf.map (homOfLE hUW).op (fL.c.app (op W) s))))) :=
        congrArg π (ConcreteCategory.congr_hom
          (LocallyRingedSpace.restrictTopSectionsIso_hom_c_app_top_of_fac_le
            fL hVW hUW l (m ≫ e.inv) hfac) s)
    _ = π (m.c.app (op ⊤) ((Spf.topSectionsIso A).inv
          (X.presheaf.map (homOfLE hUW).op (fL.c.app (op W) s)))) :=
        congrArg π (congrArg _ (he_inv _))
    _ = _ := hm2 _

/-- **Automatic continuity on all opens** (EGA I, Ch. I, 10.4.6): every morphism of formal schemes
`f : X ⟶ Y` is continuous on rings of sections over arbitrary opens `W ⊆ Y`, equipped with
`openSectionsTopology`. -/
theorem continuous_c_app_openSectionsTopology {X Y : FormalScheme.{u}} (f : X ⟶ Y) (W : Opens Y) :
    @Continuous _ _ (Y.openSectionsTopology W)
      (X.openSectionsTopology ((Opens.map (forgetToLocallyRingedSpace.map f).base).obj W))
      ((forgetToLocallyRingedSpace.map f).c.app (op W)) := by
  let _ := Y.openSectionsTopology W; let fL := forgetToLocallyRingedSpace.map f
  -- Test continuity after restricting to each affine formal open `U ≤ f⁻¹ W`.
  refine (continuous_iff_openSectionsTopology X _ _).mpr fun U hU hUW ↦ ?_
  let A := hU.Sections; obtain ⟨hIAfg, hIA, _⟩ := IsAdicRing.ideal_spec A
  -- Cover `Spf A` by basic opens `D(a p)` each mapping into an affine formal open `V p ≤ W`.
  choose V hV hVW a ha_mem ha_le using exists_basicOpen_le_preimage_affine f hU hUW
  have hcov : (⊤ : Opens (Spf.carrier A)) ≤ ⨆ p, Spf.basicOpen (a p) :=
    fun p _ ↦ Opens.mem_iSup.mpr ⟨p, ha_mem p⟩
  -- Transport continuity to `Γ(Spf A, ⊤)` with its quotient-sections topology and glue on `D(a p)`.
  let _ := Spf.quotientSectionsTopology hIA ⊤
  let _ (p) := Spf.quotientSectionsTopology hIA (Spf.basicOpen (a p))
  let gW : Y.presheaf.obj (op W) → A := fun s ↦ X.presheaf.map (homOfLE hUW).op (fL.c.app (op W) s)
  suffices hcont : @Continuous _ _ (Y.openSectionsTopology W) (Spf.quotientSectionsTopology hIA ⊤)
      ((Spf.topSectionsIso A).inv ∘ gW) from
    (@Continuous.comp _ _ _ (Y.openSectionsTopology W) (Spf.quotientSectionsTopology hIA ⊤) _ _ _
      (Spf.isHomeomorph_topSectionsIso A).continuous hcont).congr fun s ↦
        ConcreteCategory.congr_hom (Spf.topSectionsIso A).inv_hom_id _
  refine (Spf.quotientSectionsTopology_glue hIA (fun _ ↦ le_top) hcov).isInducing.continuous_iff.mpr
    (continuous_pi_iff.mpr fun p ↦
      (Spf.quotientSectionsTopology_basic hIA hIAfg (a p)).isInducing.continuous_iff.mpr ?_)
  -- On `D(a p)`, the section map factors through `Γ(Y, W) → Γ(Y, V p) → CompletedAway A (a p)`.
  obtain ⟨g, hg⟩ := exists_sectionsHom_eq_basicOpen_res f hU hUW (hV p) (hVW p) (a p) (ha_le p)
  exact ((Spf.continuous_sectionsHom g).comp
    ((continuous_iff_openSectionsTopology Y W id).mp continuous_id (V p) (hV p) (hVW p))).congr hg

end SpecialCasesAndOpenTopology

end TauCeti.FormalScheme
