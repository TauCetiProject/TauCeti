/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.FormalScheme.Basic
public import TauCeti.AlgebraicGeometry.FormalScheme.Spf.HomEquiv
public import TauCeti.Geometry.RingedSpace.LocallyRingedSpace.ResidueField

import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import TauCeti.Geometry.RingedSpace.LocallyRingedSpace.Basic
import TauCeti.RingTheory.Finiteness.Ideal
import TauCeti.Topology.Algebra.Ring.Basic
import TauCeti.Topology.Discrete
import TauCeti.Topology.Sheaves.Presheaf

/-!
# Canonical section topologies on formal schemes

For an affine formal open `U` of a formal scheme `X`, any chart `e : X|_U ≅ Spf B` identifies
`Γ(X, U) ≅ B` (`chartSectionsIso`), inducing a chart-independent complete separated adic topology
`X.sectionsTopology U hU` (packaged on `hU.Sections`, with `hU.isoSpf : X.restrict U ≅ ofSpf _`;
EGA I, Ch. I, 10.4.5). Topologically nilpotent sections are cut out by residue vanishing on `U`
(`X.vanishingIdeal U`), affine section maps are continuous (`continuous_appLE_sectionsTopology`),
and for arbitrary opens `W ⊆ X`, `X.openSectionsTopology W` makes `Γ(X, W)` a topological ring
(`openSectionsTopology_isTopologicalRing`), is tested on open covers
(`isEmbedding_pi_restrict_openSectionsTopology`), agrees with `Spf.quotientSectionsTopology` on
formal spectra (`openSectionsTopology_ofSpf`, `sectionsTopology_ofSpf`), and makes every morphism
continuous on sections (`continuous_c_app_openSectionsTopology`; EGA I, Ch. I, 10.4.6). On any
ordinary scheme `Y`, every affine formal open of `Y.toFormalScheme` carries the discrete section
topology and is an affine scheme open of `Y`
(`AlgebraicGeometry.Scheme.isAffineOpen_toFormalScheme_iff`), so `ofSpf A` lies in the essential
image of `Scheme.toFormalScheme` if and only if `A` is discrete
(`exists_ofSpf_iso_toFormalScheme_iff`).
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
  let h := (X.isAffineOpen_iff U).mp hU; let h1 := h.choose_spec; let h2 := h1.choose_spec
  let _ := h1.choose; let _ := h2.choose; let h3 := h2.choose_spec; let _ := h3.choose
  let _ := h3.choose_spec.choose; { B := h.choose, iso := h3.choose_spec.choose_spec.some }

variable (X : FormalScheme.{u}) (U : Opens X)

section ChartSections
variable {B : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsAdicRing B]
  (e : X.toLocallyRingedSpace.restrict U.isOpenEmbedding ≅ Spf B)

/-- For any affine formal chart `e : X|_U ≅ Spf B`, the induced ring isomorphism `Γ(X, U) ≅ B`. -/
noncomputable def chartSectionsIso : X.presheaf.obj (op U) ≅ CommRingCat.of B :=
  X.toPresheafedSpace.restrictTopSectionsIso U ≪≫
    (LocallyRingedSpace.Γ.mapIso e.symm.op : _ ≅ (Spf B).presheaf.obj (op ⊤)) ≪≫
    Spf.topSectionsIso B

/-- The forward map of `chartSectionsIso` factors through `restrictTopSectionsIso`, `e.inv`, and
`Spf.topSectionsIso`. -/
theorem chartSectionsIso_hom : (chartSectionsIso X U e).hom =
    (X.toPresheafedSpace.restrictTopSectionsIso U).hom ≫
      (e.inv.c.app (op ⊤) :
        (X.toLocallyRingedSpace.restrict U.isOpenEmbedding).presheaf.obj (op ⊤) ⟶
          (Spf B).presheaf.obj (op ⊤)) ≫
      (Spf.topSectionsIso B).hom := (rfl)

theorem chartSectionsIso_hom_apply (s : X.presheaf.obj (op U)) :
    (chartSectionsIso X U e).hom s = (Spf.topSectionsIso B).hom
      (e.inv.c.app (op ⊤) ((X.toPresheafedSpace.restrictTopSectionsIso U).hom s)) := (rfl)
theorem chartSectionsIso_inv_apply (b : B) : (chartSectionsIso X U e).inv b =
    (X.toPresheafedSpace.restrictTopSectionsIso U).inv
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
  have hcomp : ((e₂.symm ≪≫ e₁).hom.c.app (op ⊤) :
        (Spf B₁).presheaf.obj (op ⊤) ⟶ (Spf B₂).presheaf.obj (op ⊤)) =
      (e₁.hom.c.app (op ⊤) : (Spf B₁).presheaf.obj (op ⊤) ⟶ _) ≫
        (e₂.inv.c.app (op ⊤) : _ ⟶ (Spf B₂).presheaf.obj (op ⊤)) :=
    LocallyRingedSpace.Γ.map_comp e₁.hom.op e₂.inv.op
  have hsec : CommRingCat.ofHom (Spf.isoToRingEquiv (e₂.symm ≪≫ e₁)).toRingHom =
      CommRingCat.ofHom (Spf.sectionsHom (e₂.symm ≪≫ e₁).hom) :=
    congrArg CommRingCat.ofHom (RingHom.ext (Spf.isoToRingEquiv_apply _))
  have h1 : (Spf.topSectionsIso B₁).hom ≫
        CommRingCat.ofHom (Spf.isoToRingEquiv (e₂.symm ≪≫ e₁)).toRingHom =
      (e₁.hom.c.app (op ⊤) : (Spf B₁).presheaf.obj (op ⊤) ⟶ _) ≫
        (e₂.inv.c.app (op ⊤) : _ ⟶ (Spf B₂).presheaf.obj (op ⊤)) ≫
        (Spf.topSectionsIso B₂).hom :=
    (congrArg ((Spf.topSectionsIso B₁).hom ≫ ·) hsec).trans <|
      (Spf.c_app_top_comp_topSectionsIso_hom (e₂.symm ≪≫ e₁).hom).symm.trans <|
      (congrArg (· ≫ (Spf.topSectionsIso B₂).hom) hcomp).trans (Category.assoc _ _ _)
  have h2 : (e₁.inv.c.app (op ⊤) : _ ⟶ (Spf B₁).presheaf.obj (op ⊤)) ≫
        (Spf.topSectionsIso B₁).hom ≫
        CommRingCat.ofHom (Spf.isoToRingEquiv (e₂.symm ≪≫ e₁)).toRingHom =
      (e₂.inv.c.app (op ⊤) : _ ⟶ (Spf B₂).presheaf.obj (op ⊤)) ≫
        (Spf.topSectionsIso B₂).hom :=
    (congrArg (_ ≫ ·) h1).trans <| (Category.assoc _ _ _).symm.trans <|
      (congrArg (· ≫ _) (LocallyRingedSpace.iso_inv_c_app_top_comp_hom e₁)).trans
        (Category.id_comp _)
  exact (congrArg (· ≫ _) (chartSectionsIso_hom X U e₁)).trans <|
    (Category.assoc _ _ _).trans <|
    (congrArg (_ ≫ ·) ((Category.assoc _ _ _).trans h2)).trans
      (chartSectionsIso_hom X U e₂).symm

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
  obtain ⟨B, _, _, _, _, ⟨e⟩⟩ := (X.isAffineOpen_iff U).mp hU
  let _ := X.sectionsTopology U hU; have := X.sectionsTopology_isTopologicalRing U hU
  let φ := (chartSectionsIso X U e).commRingCatIsoToRingEquiv
  obtain ⟨I, hIfg, hIadic, hIcomp⟩ := IsAdicRing.exists_isAdic (A := B)
  exact ⟨⟨I.map φ.symm.toRingHom, hIfg.map φ.symm.toRingHom, (Ideal.map_symm φ).symm ▸
    hIadic.comap φ ⟨sectionsTopology_eq_induced X U hU e⟩,
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
  have hnil : IsTopologicallyNilpotent s ↔ IsTopologicallyNilpotent (φ s) :=
    ⟨fun hs ↦ hs.map (φ := φ.toRingHom) hφ₁,
      fun hs ↦ by simpa using hs.map (φ := φ.symm.toRingHom) hφ₂⟩
  have hmem : (∀ p ∈ {p : Ideal B | IsAdicRing.ideal B ≤ p ∧ p.IsPrime}, φ s ∈ p) ↔
      ∀ p : Spf.carrier B, (Spf B).Γevaluation p ((Spf.topSectionsIso B).inv (φ s)) = 0 :=
    ⟨fun h p ↦ (Spf.Γevaluation_topSectionsIso_inv_eq_zero_iff p _).mpr
      (h _ ⟨(Spf.mem_carrier_iff_le hIB).mp p.property, p.val.isPrime⟩),
     fun h q hq ↦ (Spf.Γevaluation_topSectionsIso_inv_eq_zero_iff
      ⟨⟨q, hq.2⟩, (Spf.mem_carrier_iff_le hIB).mpr hq.1⟩ _).mp (h _)⟩
  rw [hnil, hIB.isTopologicallyNilpotent_iff_mem_radical, Ideal.radical_eq_sInf, Ideal.mem_sInf,
    hmem]
  have hsec₂ : (Spf.topSectionsIso B).inv (φ s) = e.inv.c.app (op ⊤)
      ((X.toPresheafedSpace.restrictTopSectionsIso U).hom s) :=
    ConcreteCategory.congr_hom (Spf.topSectionsIso B).hom_inv_id _
  have hsec₁ : e.hom.c.app (op ⊤) ((Spf.topSectionsIso B).inv (φ s)) =
      (X.toPresheafedSpace.restrictTopSectionsIso U).hom s :=
    hsec₂ ▸ ConcreteCategory.congr_hom (LocallyRingedSpace.iso_inv_c_app_top_comp_hom e) _
  refine ⟨fun h x ↦ ?_, fun h (p : Spf B) ↦ ?_⟩
  · rw [X.toLocallyRingedSpace.evaluation_eq_zero_iff_restrict_Γevaluation_eq_zero, ← hsec₁,
      ← LocallyRingedSpace.Γevaluation_naturality_apply e.hom x, h (e.hom.base x), map_zero]
  · have hval := LocallyRingedSpace.Γevaluation_naturality_apply e.inv p
      ((X.toPresheafedSpace.restrictTopSectionsIso U).hom s)
    have heval : (X.toLocallyRingedSpace.restrict U.isOpenEmbedding).Γevaluation (e.inv.base p)
        ((X.toPresheafedSpace.restrictTopSectionsIso U).hom s) = 0 :=
      (X.toLocallyRingedSpace.evaluation_eq_zero_iff_restrict_Γevaluation_eq_zero U
        (e.inv.base p) s).mp (h (e.inv.base p))
    exact (congrArg ((Spf B).Γevaluation p) hsec₂).trans <|
      hval.symm.trans <| (congrArg (LocallyRingedSpace.residueFieldMap e.inv p) heval).trans
        (map_zero _)

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

private theorem forgetToLocallyRingedSpace_map_isoSpf_hom (hU : X.IsAffineOpen U) :
    let φ : hU.Sections ≃+* (chosenChart hU).B :=
      (chartSectionsIso X U (chosenChart hU).iso).commRingCatIsoToRingEquiv
    let hφ := φ.toEquiv.isHomeomorph_iff.mp (isHomeomorph_chartSectionsIso X U hU _)
    forgetToLocallyRingedSpace.map hU.isoSpf.hom =
      (chosenChart hU).iso.hom ≫ Spf.map φ.toRingHom hφ.1 :=
  congrArg ((chosenChart hU).iso.hom ≫ ·) (Spf.mapIso_hom _ _ _)

/-- On global sections, `hU.isoSpf.hom` identifies `Spf.topSectionsIso` with
`X.toPresheafedSpace.restrictTopSectionsIso U`, independently of any chosen chart. -/
@[reassoc (attr := simp)] theorem topSectionsIso_inv_isoSpf_hom_c_app_top (hU : X.IsAffineOpen U) :
    (Spf.topSectionsIso hU.Sections).inv ≫
      ((forgetToLocallyRingedSpace.map hU.isoSpf.hom).c.app (op ⊤) :
        (Spf hU.Sections).presheaf.obj (op ⊤) ⟶
          (X.toLocallyRingedSpace.restrict U.isOpenEmbedding).presheaf.obj (op ⊤)) =
      (X.toPresheafedSpace.restrictTopSectionsIso U).hom := by
  let e := (chosenChart hU).iso
  let φ : hU.Sections ≃+* (chosenChart hU).B :=
    (chartSectionsIso X U e).commRingCatIsoToRingEquiv
  let hφ := φ.toEquiv.isHomeomorph_iff.mp (isHomeomorph_chartSectionsIso X U hU e)
  have hφcont : Continuous φ.toRingHom := hφ.1
  have hcomp : ((forgetToLocallyRingedSpace.map hU.isoSpf.hom).c.app (op ⊤) :
        (Spf hU.Sections).presheaf.obj (op ⊤) ⟶
          (X.toLocallyRingedSpace.restrict U.isOpenEmbedding).presheaf.obj (op ⊤)) =
      ((Spf.map φ.toRingHom hφcont).c.app (op ⊤) :
        (Spf hU.Sections).presheaf.obj (op ⊤) ⟶ (Spf (chosenChart hU).B).presheaf.obj (op ⊤)) ≫
        (e.hom.c.app (op ⊤) :
          (Spf (chosenChart hU).B).presheaf.obj (op ⊤) ⟶
            (X.toLocallyRingedSpace.restrict U.isOpenEmbedding).presheaf.obj (op ⊤)) :=
    (congrArg (fun k : X.toLocallyRingedSpace.restrict U.isOpenEmbedding ⟶ Spf hU.Sections ↦
      LocallyRingedSpace.Γ.map k.op) (forgetToLocallyRingedSpace_map_isoSpf_hom hU)).trans
      (LocallyRingedSpace.Γ.map_comp (Spf.map φ.toRingHom hφcont).op e.hom.op)
  have h1 : (Spf.topSectionsIso hU.Sections).inv ≫
        ((Spf.map φ.toRingHom hφcont).c.app (op ⊤) :
          (Spf hU.Sections).presheaf.obj (op ⊤) ⟶ (Spf (chosenChart hU).B).presheaf.obj (op ⊤)) =
      (chartSectionsIso X U e).hom ≫ (Spf.topSectionsIso (chosenChart hU).B).inv := by
    rw [Spf.topSectionsIso_inv_comp_c_app_top, Spf.sectionsHom_map]
    -- `hU.Sections` is definitionally `X.presheaf.obj (op U)`, so `CommRingCat.ofHom φ.toRingHom`
    -- agrees definitionally with `(chartSectionsIso X U e).hom`
    -- (`Iso.commRingCatIsoToRingEquiv_toRingHom`, `CommRingCat.ofHom_hom`), preventing `rw` at
    -- `implicit` transparency.
    rfl
  have h2 : ((chartSectionsIso X U e).hom ≫ (Spf.topSectionsIso (chosenChart hU).B).inv) ≫
        (e.hom.c.app (op ⊤) : (Spf (chosenChart hU).B).presheaf.obj (op ⊤) ⟶ _) =
      (X.toPresheafedSpace.restrictTopSectionsIso U).hom :=
    (congrArg (· ≫ (Spf.topSectionsIso (chosenChart hU).B).inv ≫
        (e.hom.c.app (op ⊤) : (Spf (chosenChart hU).B).presheaf.obj (op ⊤) ⟶ _))
      (chartSectionsIso_hom X U e)).trans <|
      (Category.assoc _ _ _).trans <| (Category.assoc _ _ _).trans <|
      (congrArg ((X.toPresheafedSpace.restrictTopSectionsIso U).hom ≫ ·) <|
        (Category.assoc _ _ _).trans <|
        (congrArg ((e.inv.c.app (op ⊤) : _ ⟶ _) ≫ ·) <|
          (Category.assoc _ _ _).symm.trans <|
          (congrArg (· ≫ _) (Spf.topSectionsIso (chosenChart hU).B).hom_inv_id).trans
            (Category.id_comp _)).trans
          (LocallyRingedSpace.iso_inv_c_app_top_comp_hom e)).trans
        (Category.comp_id _)
  exact (congrArg ((Spf.topSectionsIso hU.Sections).inv ≫ ·) hcomp).trans <|
    (Category.assoc _ _ _).symm.trans <|
    (congrArg (· ≫ (e.hom.c.app (op ⊤) : (Spf (chosenChart hU).B).presheaf.obj (op ⊤) ⟶ _))
      h1).trans h2

/-- Chart-inclusion form of `topSectionsIso_inv_isoSpf_hom_c_app_top` for `hU.isoSpf.inv`. -/
@[reassoc (attr := simp)]
theorem restrictTopSectionsIso_hom_isoSpf_inv_c_app_top (hU : X.IsAffineOpen U) :
    (X.toPresheafedSpace.restrictTopSectionsIso U).hom ≫
      ((forgetToLocallyRingedSpace.map hU.isoSpf.inv).c.app (op ⊤) :
        (X.toLocallyRingedSpace.restrict U.isOpenEmbedding).presheaf.obj (op ⊤) ⟶
          (Spf hU.Sections).presheaf.obj (op ⊤)) =
      (Spf.topSectionsIso hU.Sections).inv := by
  have h1 := congrArg (· ≫ ((forgetToLocallyRingedSpace.map hU.isoSpf.inv).c.app (op ⊤) :
      _ ⟶ (Spf hU.Sections).presheaf.obj (op ⊤)))
    (topSectionsIso_inv_isoSpf_hom_c_app_top hU).symm
  have h2 := congrArg ((Spf.topSectionsIso hU.Sections).inv ≫ ·)
    (LocallyRingedSpace.iso_hom_c_app_top_comp_inv (forgetToLocallyRingedSpace.mapIso hU.isoSpf))
  exact h1.trans <| (Category.assoc _ _ _).trans <| h2.trans (Category.comp_id _)

/-- Dual form of `topSectionsIso_inv_isoSpf_hom_c_app_top` for `hU.isoSpf.inv`. -/
@[reassoc (attr := simp)]
theorem isoSpf_inv_c_app_top_comp_topSectionsIso_hom (hU : X.IsAffineOpen U) :
    ((forgetToLocallyRingedSpace.map hU.isoSpf.inv).c.app (op ⊤) :
        (X.toLocallyRingedSpace.restrict U.isOpenEmbedding).presheaf.obj (op ⊤) ⟶
          (Spf hU.Sections).presheaf.obj (op ⊤)) ≫ (Spf.topSectionsIso hU.Sections).hom =
      (X.toPresheafedSpace.restrictTopSectionsIso U).inv := by
  refine (cancel_epi (X.toPresheafedSpace.restrictTopSectionsIso U).hom).mp ?_
  have h1 := congrArg (· ≫ (Spf.topSectionsIso hU.Sections).hom)
    (restrictTopSectionsIso_hom_isoSpf_inv_c_app_top hU)
  exact (Category.assoc _ _ _).symm.trans <| h1.trans <|
    (Spf.topSectionsIso hU.Sections).inv_hom_id.trans
      (X.toPresheafedSpace.restrictTopSectionsIso U).hom_inv_id.symm

namespace IsAffineOpen
private noncomputable def basicOpenImmersion (hU : X.IsAffineOpen U) (a : hU.Sections) :
    Spf (AdicRing.CompletedAway hU.Sections a) ⟶ X.toLocallyRingedSpace :=
  Spf.basicOpenι a ≫ forgetToLocallyRingedSpace.map hU.isoSpf.inv ≫
    X.toLocallyRingedSpace.ofRestrict U.isOpenEmbedding

private instance isOpenImmersion_basicOpenImmersion (hU : X.IsAffineOpen U) (a : hU.Sections) :
    LocallyRingedSpace.IsOpenImmersion (basicOpenImmersion hU a) :=
  let h1 : LocallyRingedSpace.IsOpenImmersion (forgetToLocallyRingedSpace.map hU.isoSpf.inv) :=
    LocallyRingedSpace.IsOpenImmersion.of_isIso (forgetToLocallyRingedSpace.mapIso hU.isoSpf).inv
  let jU : forgetToLocallyRingedSpace.obj (X.restrict U) ⟶ X.toLocallyRingedSpace :=
    X.toLocallyRingedSpace.ofRestrict U.isOpenEmbedding
  have _ : LocallyRingedSpace.IsOpenImmersion jU :=
    LocallyRingedSpace.IsOpenImmersion.ofRestrict X.toLocallyRingedSpace U.isOpenEmbedding
  let j2 : Spf hU.Sections ⟶ X.toLocallyRingedSpace :=
    forgetToLocallyRingedSpace.map hU.isoSpf.inv ≫ jU
  have _ : LocallyRingedSpace.IsOpenImmersion j2 :=
    LocallyRingedSpace.IsOpenImmersion.comp
      (f := forgetToLocallyRingedSpace.map hU.isoSpf.inv) (H := h1) jU
  LocallyRingedSpace.IsOpenImmersion.comp (f := Spf.basicOpenι a) (H := inferInstance) j2

/-- Pulling back the ringed-space basic open `D(a) ⊆ X` along the chart inclusion
`Spf hU.Sections ⟶ X` gives `Spf.basicOpen a`. -/
theorem preimage_basicOpen (hU : X.IsAffineOpen U) (a : hU.Sections) :
    (Opens.map (forgetToLocallyRingedSpace.map hU.isoSpf.inv ≫
      X.toLocallyRingedSpace.ofRestrict U.isOpenEmbedding).base).obj
        (X.toLocallyRingedSpace.toRingedSpace.basicOpen a) = Spf.basicOpen a := by
  let l := forgetToLocallyRingedSpace.map hU.isoSpf.inv ≫
    X.toLocallyRingedSpace.ofRestrict U.isOpenEmbedding
  have hle : (⊤ : Opens (Spf hU.Sections)) ≤ (Opens.map l.base).obj U :=
    fun z _ ↦ ((forgetToLocallyRingedSpace.map hU.isoSpf.inv).base z).property
  have heq : (Opens.map l.base).obj U = ⊤ := le_antisymm le_top hle
  have hsec : (Spf hU.Sections).presheaf.map (eqToHom (congrArg op heq)) (l.c.app (op U) a) =
      (Spf.topSectionsIso hU.Sections).inv a := by
    have hl : l.toHom.appLE U ⊤ hle = (Spf.topSectionsIso hU.Sections).inv :=
      (PresheafedSpace.comp_ofRestrict_appLE (le_refl U)
        (forgetToLocallyRingedSpace.map hU.isoSpf.inv).toHom hle).trans <|
        (congrArg (· ≫ _) (TopCat.Presheaf.map_eq_id _ _)).trans <|
        (Category.id_comp _).trans (restrictTopSectionsIso_hom_isoSpf_inv_c_app_top hU)
    have hsub : eqToHom (congrArg op heq) = (homOfLE hle).op := Subsingleton.elim _ _
    exact (congrArg (fun i ↦ (Spf hU.Sections).presheaf.map i (l.c.app (op U) a)) hsub).trans <|
      (ConcreteCategory.comp_apply (l.c.app (op U))
        ((Spf hU.Sections).presheaf.map (homOfLE hle).op) a).symm.trans <|
      ConcreteCategory.congr_hom ((PresheafedSpace.Hom.appLE_def l.toHom U ⊤ hle).symm.trans hl) a
  exact (LocallyRingedSpace.preimage_basicOpen l a).trans <|
    (RingedSpace.basicOpen_res_eq (X := (Spf hU.Sections).toRingedSpace)
      (eqToHom (congrArg op heq)) (l.c.app (op U) a)).symm.trans <|
    (congrArg (RingedSpace.basicOpen (X := (Spf hU.Sections).toRingedSpace) (U := ⊤)) hsec).trans
      (Spf.basicOpen_topSectionsIso_inv a)

private theorem range_basicOpenImmersion (hU : X.IsAffineOpen U) (a : hU.Sections) :
    Set.range (basicOpenImmersion hU a).base =
      (X.toLocallyRingedSpace.toRingedSpace.basicOpen a).carrier := by
  let e := forgetToLocallyRingedSpace.mapIso hU.isoSpf
  let jU := X.toLocallyRingedSpace.ofRestrict U.isOpenEmbedding
  ext x
  constructor
  · rintro ⟨p, rfl⟩
    exact (congrArg (((Spf.basicOpenι a).base p : Spf.carrier hU.Sections) ∈ ·)
      (preimage_basicOpen hU a)).mpr ((Spf.range_basicOpenι a).le (Set.mem_range_self p))
  · intro hx
    have hxU : x ∈ U := X.toLocallyRingedSpace.toRingedSpace.basicOpen_le a hx
    let q : Spf.carrier hU.Sections := e.hom.base ⟨x, hxU⟩
    have hqx : (e.inv ≫ jU).base q = x :=
      (congrArg (fun k : X.toLocallyRingedSpace.restrict U.isOpenEmbedding ⟶ _ ↦
        jU.base (k.base ⟨x, hxU⟩)) e.hom_inv_id).trans rfl
    have hqmem : q ∈ Spf.basicOpen a :=
      (congrArg (q ∈ ·) (preimage_basicOpen hU a)).mp (Opens.mem_map.mpr (hqx.symm ▸ hx))
    obtain ⟨p, hp⟩ := (Spf.range_basicOpenι a).ge hqmem
    exact ⟨p, (congrArg (e.inv ≫ jU).base hp).trans hqx⟩

/-- For an affine formal open `U ⊆ X` and a section `a ∈ Γ(X, U)`, the ringed-space basic open
`X.toLocallyRingedSpace.toRingedSpace.basicOpen a` is an affine formal open of `X`. -/
theorem basicOpen (hU : X.IsAffineOpen U) (a : hU.Sections) :
    X.IsAffineOpen (X.toLocallyRingedSpace.toRingedSpace.basicOpen a) := by
  let V := X.toLocallyRingedSpace.toRingedSpace.basicOpen a
  have : LocallyRingedSpace.IsOpenImmersion (basicOpenImmersion hU a) :=
    isOpenImmersion_basicOpenImmersion hU a
  have : LocallyRingedSpace.IsOpenImmersion (X.toLocallyRingedSpace.ofRestrict V.isOpenEmbedding) :=
    inferInstance
  refine (X.isAffineOpen_iff V).mpr
    ⟨AdicRing.CompletedAway hU.Sections a, inferInstance, inferInstance, inferInstance,
      inferInstance, ⟨(LocallyRingedSpace.isoOfSheafedSpaceIso <| SheafedSpace.isoMk <|
        PresheafedSpace.IsOpenImmersion.isoOfRangeEq (basicOpenImmersion hU a).toHom
          (X.toLocallyRingedSpace.ofRestrict V.isOpenEmbedding).toHom
          ((range_basicOpenImmersion hU a).trans Subtype.range_coe.symm)).symm⟩⟩

/-- `X.toLocallyRingedSpace.toRingedSpace.basicOpen a ≤ W'` iff `Spf.basicOpen a` maps into `W'`
under `hU.isoSpf.inv`. -/
theorem basicOpen_le_iff (hU : X.IsAffineOpen U) (a : hU.Sections) (W' : Opens X) :
    X.toLocallyRingedSpace.toRingedSpace.basicOpen a ≤ W' ↔
      Spf.basicOpen a ≤ (Opens.map (forgetToLocallyRingedSpace.map hU.isoSpf.inv ≫
        X.toLocallyRingedSpace.ofRestrict U.isOpenEmbedding).base).obj W' := by
  constructor
  · intro h p hp
    rw [← preimage_basicOpen hU a] at hp
    exact h hp
  · intro h x hx
    obtain ⟨p, hp⟩ := (range_basicOpenImmersion hU a).ge hx
    rw [← hp]
    exact h ((Spf.range_basicOpenι a).le (Set.mem_range_self p))
end IsAffineOpen

private theorem sectionsHom_isoSpf_inv_comp_hom_of_fac {X Y : FormalScheme.{u}} (f : X ⟶ Y)
    {V : Opens Y} (hV : Y.IsAffineOpen V) {U : Opens X} (hU : X.IsAffineOpen U)
    (hUV : U ≤ (Opens.map (forgetToLocallyRingedSpace.map f).base).obj V)
    (fUV : X.toLocallyRingedSpace.restrict U.isOpenEmbedding ⟶
      Y.toLocallyRingedSpace.restrict V.isOpenEmbedding)
    (hfac : fUV ≫ Y.toLocallyRingedSpace.ofRestrict V.isOpenEmbedding =
      X.toLocallyRingedSpace.ofRestrict U.isOpenEmbedding ≫ forgetToLocallyRingedSpace.map f) :
    Spf.sectionsHom ((forgetToLocallyRingedSpace.map hU.isoSpf.inv ≫ fUV) ≫
        forgetToLocallyRingedSpace.map hV.isoSpf.hom) =
      ((forgetToLocallyRingedSpace.map f).toHom.appLE V U hUV).hom := by
  refine congrArg CommRingCat.Hom.hom <| (Spf.ofHom_sectionsHom _).trans ?_
  have hcomp : ((forgetToLocallyRingedSpace.map hU.isoSpf.inv ≫ fUV) ≫
        forgetToLocallyRingedSpace.map hV.isoSpf.hom).c.app (op ⊤) =
      ((forgetToLocallyRingedSpace.map hV.isoSpf.hom).c.app (op ⊤) :
          (Spf hV.Sections).presheaf.obj (op ⊤) ⟶ _) ≫
        (fUV.c.app (op ⊤) :
          _ ⟶ (X.toLocallyRingedSpace.restrict U.isOpenEmbedding).presheaf.obj (op ⊤)) ≫
        ((forgetToLocallyRingedSpace.map hU.isoSpf.inv).c.app (op ⊤) :
          _ ⟶ (Spf hU.Sections).presheaf.obj (op ⊤)) :=
    (LocallyRingedSpace.Γ.map_comp (forgetToLocallyRingedSpace.map hV.isoSpf.hom).op
      (forgetToLocallyRingedSpace.map hU.isoSpf.inv ≫ fUV).op).trans <|
      congrArg ((forgetToLocallyRingedSpace.map hV.isoSpf.hom).c.app (op ⊤) ≫ ·)
        (LocallyRingedSpace.Γ.map_comp fUV.op (forgetToLocallyRingedSpace.map hU.isoSpf.inv).op)
  let invU : _ ⟶ (Spf hU.Sections).presheaf.obj (op ⊤) :=
    (forgetToLocallyRingedSpace.map hU.isoSpf.inv).c.app (op ⊤)
  let fUVtop : _ ⟶ (X.toLocallyRingedSpace.restrict U.isOpenEmbedding).presheaf.obj (op ⊤) :=
    fUV.c.app (op ⊤)
  let T := (Spf.topSectionsIso hU.Sections).hom
  have h1 := congrArg (fun m ↦ (Spf.topSectionsIso hV.Sections).inv ≫ m ≫ T) hcomp
  have h2 := congrArg (· ≫ fUVtop ≫ invU ≫ T) (topSectionsIso_inv_isoSpf_hom_c_app_top hV)
  have h3 := congrArg (· ≫ invU ≫ T)
    (PresheafedSpace.restrictTopSectionsIso_hom_c_app_top_of_fac
      (forgetToLocallyRingedSpace.map f).toHom hUV fUV.toHom
      (congrArg LocallyRingedSpace.Hom.toHom hfac))
  have h4 := (congrArg (· ≫ T) (restrictTopSectionsIso_hom_isoSpf_inv_c_app_top hU)).trans
    (Spf.topSectionsIso hU.Sections).inv_hom_id
  have h5 := (congrArg ((forgetToLocallyRingedSpace.map f).toHom.appLE V U hUV ≫ ·)
    ((Category.assoc _ invU T).symm.trans h4)).trans (Category.comp_id _)
  exact h1.trans <| (Category.assoc _ _ T).symm.trans <| (Category.assoc _ _ _).trans <|
    h2.trans <| (Category.assoc _ _ _).symm.trans <| h3.trans <| (Category.assoc _ _ _).trans h5

/-- **Automatic continuity on affine opens** (EGA I, Ch. I, 10.4.6): for `f : X ⟶ Y` and affine
opens `U ⊆ X`, `V ⊆ Y` with `U ≤ f ⁻¹' V`, `Γ(Y, V) →+* Γ(X, U)` is continuous. -/
theorem continuous_appLE_sectionsTopology {X Y : FormalScheme.{u}} (f : X ⟶ Y)
    {V : Opens Y} (hV : Y.IsAffineOpen V) {U : Opens X} (hU : X.IsAffineOpen U)
    (hUV : U ≤ (Opens.map (forgetToLocallyRingedSpace.map f).base).obj V) :
    @Continuous _ _ (Y.sectionsTopology V hV) (X.sectionsTopology U hU)
      ((forgetToLocallyRingedSpace.map f).toHom.appLE V U hUV) := by
  let jU := X.toLocallyRingedSpace.ofRestrict U.isOpenEmbedding
  let jV := Y.toLocallyRingedSpace.ofRestrict V.isOpenEmbedding
  have hsub : Set.range (jU ≫ forgetToLocallyRingedSpace.map f).base ⊆ Set.range jV.base :=
    fun _ ⟨x, hx⟩ ↦ hx ▸ ⟨⟨(forgetToLocallyRingedSpace.map f).base x.val, hUV x.property⟩, rfl⟩
  exact (Spf.continuous_sectionsHom ((forgetToLocallyRingedSpace.map hU.isoSpf.inv ≫
    LocallyRingedSpace.IsOpenImmersion.lift jV _ hsub) ≫
    forgetToLocallyRingedSpace.map hV.isoSpf.hom)).congr <| DFunLike.congr_fun <|
    sectionsHom_isoSpf_inv_comp_hom_of_fac f hV hU hUV _
      (LocallyRingedSpace.IsOpenImmersion.lift_fac jV _ hsub)

/-- Transporting a restricted morphism `fUV : X.restrict U ⟶ Y.restrict V` (satisfying
`fUV ≫ Y.ofRestrict V = X.ofRestrict U ≫ f`) through the canonical charts `hU.isoSpf` and
`hV.isoSpf` gives `ofSpfMap` of the restricted section homomorphism `Γ(Y, V) →+* Γ(X, U)`. -/
@[reassoc]
theorem isoSpf_inv_comp_hom_of_fac {X Y : FormalScheme.{u}} (f : X ⟶ Y) {V : Opens Y}
    (hV : Y.IsAffineOpen V) {U : Opens X} (hU : X.IsAffineOpen U)
    (hUV : U ≤ (Opens.map (forgetToLocallyRingedSpace.map f).base).obj V)
    (fUV : X.restrict U ⟶ Y.restrict V) (hfac : fUV ≫ Y.ofRestrict V = X.ofRestrict U ≫ f) :
    hU.isoSpf.inv ≫ fUV ≫ hV.isoSpf.hom =
      ofSpfMap (A := hV.Sections) (B := hU.Sections)
        ((forgetToLocallyRingedSpace.map f).toHom.appLE V U hUV).hom
        (continuous_appLE_sectionsTopology f hV hU hUV) := by
  let g := (forgetToLocallyRingedSpace.map hU.isoSpf.inv ≫ forgetToLocallyRingedSpace.map fUV) ≫
    forgetToLocallyRingedSpace.map hV.isoSpf.hom
  have hfac' : forgetToLocallyRingedSpace.map fUV ≫
        Y.toLocallyRingedSpace.ofRestrict V.isOpenEmbedding =
      X.toLocallyRingedSpace.ofRestrict U.isOpenEmbedding ≫ forgetToLocallyRingedSpace.map f := by
    have h := congrArg forgetToLocallyRingedSpace.map hfac
    simp only [Functor.map_comp, forgetToLocallyRingedSpace_map_ofRestrict] at h
    exact h
  have hsec := sectionsHom_isoSpf_inv_comp_hom_of_fac f hV hU hUV
    (forgetToLocallyRingedSpace.map fUV) hfac'
  refine fullyFaithfulForgetToLocallyRingedSpace.map_injective ?_
  have hmap : Spf.map (A := hU.Sections) (B := hV.Sections)
        ((forgetToLocallyRingedSpace.map f).toHom.appLE V U hUV).hom
      (continuous_appLE_sectionsTopology f hV hU hUV) =
      Spf.map (Spf.sectionsHom g) (Spf.continuous_sectionsHom g) := by
    congr 1; exact hsec.symm
  simp only [Functor.map_comp, ← Category.assoc]
  exact (Spf.map_sectionsHom g).symm.trans <| hmap.symm.trans
    (forgetToLocallyRingedSpace_map_ofSpfMap _ _).symm

/-- Commuting square for a restricted morphism `fUV : X.restrict U ⟶ Y.restrict V` and the
canonical affine charts `hU.isoSpf` and `hV.isoSpf`. -/
@[reassoc]
theorem comp_isoSpf_hom_of_fac {X Y : FormalScheme.{u}} (f : X ⟶ Y) {V : Opens Y}
    (hV : Y.IsAffineOpen V) {U : Opens X} (hU : X.IsAffineOpen U)
    (hUV : U ≤ (Opens.map (forgetToLocallyRingedSpace.map f).base).obj V)
    (fUV : X.restrict U ⟶ Y.restrict V) (hfac : fUV ≫ Y.ofRestrict V = X.ofRestrict U ≫ f) :
    fUV ≫ hV.isoSpf.hom =
      hU.isoSpf.hom ≫ ofSpfMap (A := hV.Sections) (B := hU.Sections)
        ((forgetToLocallyRingedSpace.map f).toHom.appLE V U hUV).hom
        (continuous_appLE_sectionsTopology f hV hU hUV) :=
  (Iso.inv_comp_eq hU.isoSpf).mp (isoSpf_inv_comp_hom_of_fac f hV hU hUV fUV hfac)

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

/-- `X.openSectionsTopology W` is the infimum over affine formal opens `U ≤ W` of the topologies
induced from `X.sectionsTopology U hU` along restriction. -/
theorem openSectionsTopology_def (X : FormalScheme.{u}) (W : Opens X) :
    X.openSectionsTopology W =
      ⨅ (U : Opens X) (hU : X.IsAffineOpen U) (hUW : U ≤ W),
        TopologicalSpace.induced (X.presheaf.map (homOfLE hUW).op) (X.sectionsTopology U hU) := by
  rfl

/-- Continuity into `X.openSectionsTopology W` is tested on affine formal opens `U ≤ W`. -/
theorem continuous_iff_openSectionsTopology {T : Type*} [TopologicalSpace T] (X : FormalScheme.{u})
    (W : Opens X) (g : T → X.presheaf.obj (op W)) :
    @Continuous _ _ ‹TopologicalSpace T› (X.openSectionsTopology W) g ↔
      ∀ (U : Opens X) (hU : X.IsAffineOpen U) (hUW : U ≤ W),
        @Continuous _ _ ‹TopologicalSpace T› (X.sectionsTopology U hU)
          (X.presheaf.map (homOfLE hUW).op ∘ g) := by
  let _ := X.openSectionsTopology W; simp only [continuous_iInf_rng, continuous_induced_rng]

private theorem appLE_forgetToLocallyRingedSpace_id (X : FormalScheme.{u})
    {U V : Opens X} (hUV : U ≤ (Opens.map (forgetToLocallyRingedSpace.map (𝟙 X)).base).obj V) :
    ((forgetToLocallyRingedSpace.map (𝟙 X)).toHom.appLE V U hUV :
      X.presheaf.obj (op V) ⟶ X.presheaf.obj (op U)) =
      X.presheaf.map (homOfLE hUV).op :=
  (PresheafedSpace.Hom.congr_appLE
      (congrArg LocallyRingedSpace.Hom.toHom (forgetToLocallyRingedSpace.map_id X)) hUV _).trans
    (PresheafedSpace.Hom.id_appLE X.toPresheafedSpace _)

/-- On an affine formal open `W ⊆ X`, `X.openSectionsTopology W = X.sectionsTopology W hW`. -/
theorem openSectionsTopology_eq_sectionsTopology (X : FormalScheme.{u}) (W : Opens X)
    (hW : X.IsAffineOpen W) : X.openSectionsTopology W = X.sectionsTopology W hW := by
  refine le_antisymm (iInf_le_of_le W <| iInf_le_of_le hW <| iInf_le_of_le (le_refl W) ?_)
    (le_iInf fun U ↦ le_iInf fun hU ↦ le_iInf fun hUW ↦ ?_)
  · rw [TopCat.Presheaf.map_eq_id]; exact le_of_eq (induced_id (t := X.sectionsTopology W hW))
  · let _ := X.sectionsTopology W hW; let _ := X.sectionsTopology U hU
    exact continuous_iff_le_induced.mp <|
      (continuous_appLE_sectionsTopology (𝟙 X) hW hU hUW).congr <|
        ConcreteCategory.congr_hom (appLE_forgetToLocallyRingedSpace_id X hUW)

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
  refine le_iInf fun U ↦ le_iInf fun hU ↦ le_iInf fun hUW ↦ ?_
  let e := forgetToLocallyRingedSpace.mapIso hU.isoSpf
  let k : Spf hU.Sections ⟶ Spf A := e.inv ≫ (Spf A).ofRestrict U.isOpenEmbedding
  have hle : (⊤ : Opens (Spf.carrier hU.Sections)) ≤ (Opens.map k.base).obj W :=
    fun z _ ↦ hUW (e.inv.base z).property
  have h1 : k.toHom.appLE W ⊤ hle ≫ (Spf.topSectionsIso hU.Sections).hom =
      (Spf A).presheaf.map (homOfLE hUW).op ≫
        ((ofSpf A).toPresheafedSpace.restrictTopSectionsIso U).hom ≫
        (e.inv.c.app (op ⊤) ≫ (Spf.topSectionsIso hU.Sections).hom) :=
    (congrArg (· ≫ (Spf.topSectionsIso hU.Sections).hom)
      (PresheafedSpace.comp_ofRestrict_appLE hUW e.inv.toHom hle)).trans
      (Category.assoc _ _ _)
  have h2 := (congrArg (((ofSpf A).toPresheafedSpace.restrictTopSectionsIso U).hom ≫ ·)
    (isoSpf_inv_c_app_top_comp_topSectionsIso_hom hU)).trans
    ((ofSpf A).toPresheafedSpace.restrictTopSectionsIso U).hom_inv_id
  have h3 := (congrArg ((Spf A).presheaf.map (homOfLE hUW).op ≫ ·) h2).trans
    (Category.comp_id _)
  have hcomp : k.toHom.appLE W ⊤ hle ≫ (Spf.topSectionsIso hU.Sections).hom =
      (Spf A).presheaf.map (homOfLE hUW).op := h1.trans h3
  let hIU := (IsAdicRing.ideal_spec hU.Sections).2.1
  let _ := Spf.quotientSectionsTopology (IsAdicRing.ideal_spec A).2.1 W
  let _ := Spf.quotientSectionsTopology hIU ⊤
  let _ := Spf.quotientSectionsTopology hIU ((Opens.map k.base).obj W)
  exact continuous_iff_le_induced.mp <| ((Spf.isHomeomorph_topSectionsIso hU.Sections).continuous
    |>.comp ((Spf.quotientSectionsTopology_restrict hIU hle).comp (Spf.continuous_c_app k W))).congr
      fun s ↦
        (congrArg (Spf.topSectionsIso hU.Sections).hom
          ((ConcreteCategory.comp_apply (k.c.app (op W))
            ((Spf hU.Sections).presheaf.map (homOfLE hle).op) s).symm.trans
            (ConcreteCategory.congr_hom (PresheafedSpace.Hom.appLE_def k.toHom W ⊤ hle).symm
              s))).trans <|
        (ConcreteCategory.comp_apply (k.toHom.appLE W ⊤ hle)
          (Spf.topSectionsIso hU.Sections).hom s).symm.trans
          (ConcreteCategory.congr_hom hcomp s)

private theorem basicOpenι_c_app_comp_res (f : A)
    (hpre : (Opens.map (Spf.basicOpenι f).base).obj (Spf.basicOpen f) = ⊤) :
    (Spf.basicOpenι f).c.app (op (Spf.basicOpen f)) ≫
        (Spf (AdicRing.CompletedAway A f)).presheaf.map (homOfLE hpre.ge).op =
      (chartSectionsIso (ofSpf A) (Spf.basicOpen f) (Spf.restrictBasicOpenIso f)).hom ≫
        (Spf.topSectionsIso (AdicRing.CompletedAway A f)).inv := by
  let B := AdicRing.CompletedAway A f; let U := Spf.basicOpen f; let e := Spf.restrictBasicOpenIso f
  have hpre' : (⊤ : Opens _) ≤ (Opens.map (e.inv ≫
      (Spf A).ofRestrict (U : Opens (Spf A).toTopCat).isOpenEmbedding).base).obj U :=
    (Spf.restrictBasicOpenIso_inv_ofRestrict f).symm ▸ hpre.ge
  have h1 := PresheafedSpace.Hom.congr_appLE
    (congrArg LocallyRingedSpace.Hom.toHom (Spf.restrictBasicOpenIso_inv_ofRestrict f))
    hpre' hpre.ge
  have h2 := (PresheafedSpace.comp_ofRestrict_appLE (le_refl U) e.inv.toHom hpre').trans <|
    (congrArg (· ≫ _) (TopCat.Presheaf.map_eq_id _ _)).trans (Category.id_comp _)
  have h3 : ((ofSpf A).toPresheafedSpace.restrictTopSectionsIso U).hom ≫ e.inv.c.app (op ⊤) =
      (chartSectionsIso (ofSpf A) U e).hom ≫ (Spf.topSectionsIso B).inv :=
    (Iso.eq_comp_inv (Spf.topSectionsIso B)).mpr (Category.assoc _ _ _)
  exact (PresheafedSpace.Hom.appLE_def (Spf.basicOpenι f).toHom U ⊤ hpre.ge).symm.trans <|
    h1.symm.trans <| h2.trans h3

private theorem isInducing_presheaf_map_basicOpen_mul_self (f : A) :
    @Topology.IsInducing _ _
      (Spf.quotientSectionsTopology (IsAdicRing.ideal_spec A).2.1 (Spf.basicOpen f))
      (Spf.quotientSectionsTopology (IsAdicRing.ideal_spec A).2.1 (Spf.basicOpen (f * f)))
      ((Spf A).presheaf.map (homOfLE ((Spf.basicOpen_mul f f).le.trans inf_le_right)).op) := by
  let hIA := (IsAdicRing.ideal_spec A).2.1
  let hle₁ : Spf.basicOpen (f * f) ≤ Spf.basicOpen f :=
    (Spf.basicOpen_mul f f).le.trans inf_le_right
  let hle₂ : Spf.basicOpen f ≤ Spf.basicOpen (f * f) :=
    (le_inf le_rfl le_rfl).trans (Spf.basicOpen_mul f f).ge
  let _ : TopologicalSpace ((Spf A).presheaf.obj (op (Spf.basicOpen f))) :=
    Spf.quotientSectionsTopology hIA (Spf.basicOpen f)
  let _ : TopologicalSpace ((Spf A).presheaf.obj (op (Spf.basicOpen (f * f)))) :=
    Spf.quotientSectionsTopology hIA (Spf.basicOpen (f * f))
  let h : (Spf A).presheaf.obj (op (Spf.basicOpen f)) ≃ₜ
      (Spf A).presheaf.obj (op (Spf.basicOpen (f * f))) :=
    { toFun := (Spf A).presheaf.map (homOfLE hle₁).op
      invFun := (Spf A).presheaf.map (homOfLE hle₂).op
      left_inv s := (ConcreteCategory.comp_apply _ _ s).symm.trans <|
        (ConcreteCategory.congr_hom
          ((TopCat.Presheaf.map_comp_map_eq (Spf A).presheaf (homOfLE hle₁).op (homOfLE hle₂).op
            (𝟙 _)).trans (TopCat.Presheaf.map_eq_id _ _)) s).trans
        (ConcreteCategory.id_apply s)
      right_inv s := (ConcreteCategory.comp_apply _ _ s).symm.trans <|
        (ConcreteCategory.congr_hom
          ((TopCat.Presheaf.map_comp_map_eq (Spf A).presheaf (homOfLE hle₂).op (homOfLE hle₁).op
            (𝟙 _)).trans (TopCat.Presheaf.map_eq_id _ _)) s).trans
        (ConcreteCategory.id_apply s)
      continuous_toFun := Spf.quotientSectionsTopology_restrict hIA hle₁
      continuous_invFun := Spf.quotientSectionsTopology_restrict hIA hle₂ }
  exact h.isInducing

private theorem quotientSectionsTopology_basicOpen_eq_induced_iterate (f : A) :
    Spf.quotientSectionsTopology (IsAdicRing.ideal_spec A).2.1 (Spf.basicOpen f) =
      TopologicalSpace.induced
        ((Spf A).presheaf.map (homOfLE ((Spf.basicOpen_mul f f).le.trans inf_le_right)).op ≫
          (Spf.basicOpenSectionsIso (IsAdicRing.ideal_spec A).2.1
            (IsAdicRing.ideal_spec A).1 (f * f)).hom ≫
          (AdicRing.CompletedAway.iterateEquiv f f).symm.toCommRingCatIso.hom) inferInstance := by
  let hIA := (IsAdicRing.ideal_spec A).2.1
  let hIAfg := (IsAdicRing.ideal_spec A).1
  let _ := Spf.quotientSectionsTopology hIA (Spf.basicOpen f)
  let _ := Spf.quotientSectionsTopology hIA (Spf.basicOpen (f * f))
  exact ((Homeomorph.mk (AdicRing.CompletedAway.iterateEquiv f f).symm.toEquiv
    (AdicRing.CompletedAway.continuous_iterateEquiv_symm f f)
    (AdicRing.CompletedAway.continuous_iterateEquiv f f)).isInducing.comp
    ((Spf.quotientSectionsTopology_basic hIA hIAfg (f * f)).isInducing.comp
      (isInducing_presheaf_map_basicOpen_mul_self A f))).eq_induced

private theorem chartSectionsIso_basicOpen_comp_iterateEquiv (f : A) :
    (chartSectionsIso (ofSpf A) (Spf.basicOpen f) (Spf.restrictBasicOpenIso f)).hom ≫
        (Spf.topSectionsIso (AdicRing.CompletedAway A f)).inv ≫
        (Spf (AdicRing.CompletedAway A f)).presheaf.map
          (homOfLE (le_top : Spf.basicOpen (algebraMap A _ f) ≤ ⊤)).op ≫
        (Spf.basicOpenSectionsIso (IsAdicRing.ideal_spec (AdicRing.CompletedAway A f)).2.1
          (IsAdicRing.ideal_spec (AdicRing.CompletedAway A f)).1 (algebraMap A _ f)).hom =
      (Spf A).presheaf.map (homOfLE ((Spf.basicOpen_mul f f).le.trans inf_le_right)).op ≫
        (Spf.basicOpenSectionsIso (IsAdicRing.ideal_spec A).2.1
          (IsAdicRing.ideal_spec A).1 (f * f)).hom ≫
        (AdicRing.CompletedAway.iterateEquiv f f).symm.toCommRingCatIso.hom := by
  let B := AdicRing.CompletedAway A f
  have hpre : (Opens.map (Spf.basicOpenι f).base).obj (Spf.basicOpen f) = ⊤ :=
    Opens.ext (Set.eq_univ_of_forall fun p ↦ (Spf.range_basicOpenι f).le ⟨p, rfl⟩)
  have h1 := congrArg (· ≫ (Spf B).presheaf.map
        (homOfLE (le_top : Spf.basicOpen (algebraMap A B f) ≤ ⊤)).op ≫
      (Spf.basicOpenSectionsIso (IsAdicRing.ideal_spec B).2.1
        (IsAdicRing.ideal_spec B).1 (algebraMap A B f)).hom)
    (basicOpenι_c_app_comp_res A f hpre).symm
  have h2 := congrArg ((Spf.basicOpenι f).c.app (op (Spf.basicOpen f)) ≫ ·)
    (TopCat.Presheaf.map_comp_map_eq (Spf B).presheaf (homOfLE hpre.ge).op
      (homOfLE (le_top : Spf.basicOpen (algebraMap A B f) ≤ ⊤)).op
      (eqToHom (congrArg op (Spf.basicOpenι_preimage_basicOpen f f))))
  have h3 := (congrArg (· ≫ (Spf.basicOpenSectionsIso (IsAdicRing.ideal_spec B).2.1
      (IsAdicRing.ideal_spec B).1 (algebraMap A B f)).hom)
    ((Category.assoc _ _ _).symm.trans h2)).trans <|
    (Category.assoc _ _ _).trans (Spf.basicOpenι_c_app f f)
  exact (Category.assoc _ _ _).symm.trans <|
    (congrArg (· ≫ _) (Category.assoc _ _ _).symm).trans <|
    h1.trans h3

private theorem sectionsTopology_basicOpen_le (f : A) :
    (ofSpf A).sectionsTopology (Spf.basicOpen f) (isAffineOpen_basicOpen A f) ≤
      Spf.quotientSectionsTopology (IsAdicRing.ideal_spec A).2.1 (Spf.basicOpen f) := by
  let B := AdicRing.CompletedAway A f; let U := Spf.basicOpen f; let e := Spf.restrictBasicOpenIso f
  obtain ⟨hIAfg, hIA, _⟩ := IsAdicRing.ideal_spec A
  obtain ⟨hIBfg, hIB, _⟩ := IsAdicRing.ideal_spec B
  let _ := (ofSpf A).sectionsTopology U (isAffineOpen_basicOpen A f)
  let _ := Spf.quotientSectionsTopology hIB ⊤; let _ := Spf.quotientSectionsTopology hIA U
  let _ := Spf.quotientSectionsTopology hIB (Spf.basicOpen (algebraMap A B f))
  have htop_inv : @Continuous _ _ _ (Spf.quotientSectionsTopology hIB ⊤)
      (Spf.topSectionsIso B).inv :=
    ((@Equiv.isHomeomorph_iff _ _ (Spf.quotientSectionsTopology hIB ⊤) _
      (Spf.topSectionsIso B).commRingCatIsoToRingEquiv.toEquiv).mp
      (Spf.isHomeomorph_topSectionsIso B)).2
  exact (quotientSectionsTopology_basicOpen_eq_induced_iterate A f).symm ▸
    continuous_iff_le_induced.mp (((Spf.quotientSectionsTopology_basic hIB hIBfg
      _).continuous.comp <| (Spf.quotientSectionsTopology_restrict hIB le_top).comp <| htop_inv.comp
      (isHomeomorph_chartSectionsIso (ofSpf A) U (isAffineOpen_basicOpen A f) e).continuous).congr
      (ConcreteCategory.congr_hom (chartSectionsIso_basicOpen_comp_iterateEquiv A f)))

/-- On an affine formal spectrum `ofSpf A`, the general `openSectionsTopology` agrees with
`Spf.quotientSectionsTopology` on every open `W` (EGA I, Ch. I, 10.4.5). -/
theorem openSectionsTopology_ofSpf (W : Opens (ofSpf A)) : (ofSpf A).openSectionsTopology W =
    Spf.quotientSectionsTopology (IsAdicRing.ideal_spec A).2.1 W := by
  refine le_antisymm ?_ (quotientSectionsTopology_le_openSectionsTopology A W)
  refine (Spf.quotientSectionsTopology_def (IsAdicRing.ideal_spec A).2.1 W).symm ▸
    le_iInf₂ (a := (ofSpf A).openSectionsTopology W) fun f hf ↦ ?_
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
theorem isHomeomorph_topSectionsIso_sectionsTopology :
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
    (ha_le : X.toLocallyRingedSpace.toRingedSpace.basicOpen a ≤
      (Opens.map (forgetToLocallyRingedSpace.map f).base).obj V) :
    ∃ g : Spf (AdicRing.CompletedAway hU.Sections a) ⟶ Spf hV.Sections,
      ∀ s : Y.presheaf.obj (op W), Spf.sectionsHom g (Y.presheaf.map (homOfLE hVW).op s) =
        algebraMap hU.Sections (AdicRing.CompletedAway hU.Sections a)
          ((forgetToLocallyRingedSpace.map f).toHom.appLE W U hUW s) := by
  let A := hU.Sections
  let fL := forgetToLocallyRingedSpace.map f; let e := forgetToLocallyRingedSpace.mapIso hU.isoSpf
  let jU := X.toLocallyRingedSpace.ofRestrict U.isOpenEmbedding
  let jV := Y.toLocallyRingedSpace.ofRestrict V.isOpenEmbedding
  let m := Spf.map (algebraMap A _) (AdicRing.CompletedAway.continuous_algebraMap A a)
  have ha_le' := (hU.basicOpen_le_iff a ((Opens.map fL.base).obj V)).mp ha_le
  have hsub : Set.range ((m ≫ e.inv) ≫ jU ≫ fL).base ⊆ Set.range jV.base := by
    rintro _ ⟨p, rfl⟩
    exact ⟨⟨_, ha_le' (SetLike.mem_coe.mp ((by rw [Spf.map_base, ← Spf.basicOpenι_base,
      Spf.range_basicOpenι] : Set.range m.base = (Spf.basicOpen a : Set (Spf.carrier A))) ▸
      Set.mem_range_self p))⟩, rfl⟩
  let l := LocallyRingedSpace.IsOpenImmersion.lift jV ((m ≫ e.inv) ≫ jU ≫ fL) hsub
  refine ⟨l ≫ forgetToLocallyRingedSpace.map hV.isoSpf.hom, fun s ↦ ?_⟩
  let π := (Spf.topSectionsIso (AdicRing.CompletedAway A a)).hom
  have hm2 (t : A) : π (m.c.app (op ⊤) ((Spf.topSectionsIso A).inv t)) =
      algebraMap A (AdicRing.CompletedAway A a) t := by
    rw [← Spf.sectionsHom_apply, Spf.sectionsHom_map]
  refine (Spf.sectionsHom_apply _ _).trans <| (congrArg (fun x ↦ π (l.c.app (op ⊤) x))
    (ConcreteCategory.congr_hom (topSectionsIso_inv_isoSpf_hom_c_app_top hV) _)).trans <|
    (congrArg π <| ConcreteCategory.congr_hom
      (PresheafedSpace.restrictTopSectionsIso_hom_c_app_top_of_fac_le fL.toHom hVW hUW l.toHom
        (m ≫ e.inv).toHom (congrArg LocallyRingedSpace.Hom.toHom
          (LocallyRingedSpace.IsOpenImmersion.lift_fac jV _ hsub))) s).trans <|
    (congrArg (π ∘ m.c.app (op ⊤))
      (ConcreteCategory.congr_hom (restrictTopSectionsIso_hom_isoSpf_inv_c_app_top hU) _)).trans
      (hm2 _)

private theorem continuous_of_basicOpen_glue {T : Type*} [TopologicalSpace T]
    {X : FormalScheme.{u}} {U : Opens X} (hU : X.IsAffineOpen U) (g : T → hU.Sections)
    (hcover : ∀ p : Spf.carrier hU.Sections, ∃ a : hU.Sections, p ∈ Spf.basicOpen a ∧
      @Continuous _ _ ‹TopologicalSpace T› inferInstance
        (fun t ↦ algebraMap hU.Sections (AdicRing.CompletedAway hU.Sections a) (g t))) :
    @Continuous _ _ ‹TopologicalSpace T› (X.sectionsTopology U hU) g := by
  let A := hU.Sections; obtain ⟨hIAfg, hIA, _⟩ := IsAdicRing.ideal_spec A
  choose a ha_mem ha_cont using hcover
  let _ := Spf.quotientSectionsTopology hIA ⊤; let _ := X.sectionsTopology U hU
  let _ (p) := Spf.quotientSectionsTopology hIA (Spf.basicOpen (a p))
  have hcomp (p) (t) :
      (Spf.basicOpenSectionsIso hIA hIAfg (a p)).hom
        ((Spf A).presheaf.map (homOfLE (le_top : Spf.basicOpen (a p) ≤ ⊤)).op
          ((Spf.topSectionsIso A).inv (g t))) =
        algebraMap A (AdicRing.CompletedAway A (a p)) (g t) :=
    (ConcreteCategory.congr_hom
      ((Iso.comp_inv_eq _).mp (Spf.algebraMap_comp_basicOpenSectionsIso_inv (a p))) (g t)).symm
  have hcont : @Continuous _ _ ‹TopologicalSpace T› (Spf.quotientSectionsTopology hIA ⊤)
      ((Spf.topSectionsIso A).inv ∘ g) :=
    (Spf.quotientSectionsTopology_glue hIA (fun _ ↦ le_top)
        fun p _ ↦ Opens.mem_iSup.mpr ⟨p, ha_mem p⟩).isInducing.continuous_iff.mpr <|
      continuous_pi_iff.mpr fun p ↦ (Spf.quotientSectionsTopology_basic hIA hIAfg
        (a p)).isInducing.continuous_iff.mpr ((ha_cont p).congr fun t ↦ (hcomp p t).symm)
  exact ((Spf.isHomeomorph_topSectionsIso A).continuous.comp hcont).congr fun t ↦
    ConcreteCategory.congr_hom (Spf.topSectionsIso A).inv_hom_id (g t)

private theorem continuous_appLE_of_cover {X Y : FormalScheme.{u}} (f : X ⟶ Y)
    {W : Opens Y} (tW : TopologicalSpace (Y.presheaf.obj (op W)))
    {U : Opens X} (hU : X.IsAffineOpen U)
    (hUW : U ≤ (Opens.map (forgetToLocallyRingedSpace.map f).base).obj W)
    (hcov : ∀ x ∈ U, ∃ (V : Opens Y) (hV : Y.IsAffineOpen V) (hVW : V ≤ W),
      (forgetToLocallyRingedSpace.map f).base x ∈ V ∧
      @Continuous _ _ tW (Y.sectionsTopology V hV) (Y.presheaf.map (homOfLE hVW).op)) :
    @Continuous _ _ tW (X.sectionsTopology U hU)
      ((forgetToLocallyRingedSpace.map f).toHom.appLE W U hUW) := by
  let fL := forgetToLocallyRingedSpace.map f
  refine continuous_of_basicOpen_glue hU _ fun p ↦ ?_
  obtain ⟨V, hV, hVW, hxV, hcontV⟩ :=
    hcov _ ((forgetToLocallyRingedSpace.map hU.isoSpf.inv).base p).property
  have hpV : p ∈ (Opens.map (forgetToLocallyRingedSpace.map hU.isoSpf.inv ≫
      X.toLocallyRingedSpace.ofRestrict U.isOpenEmbedding ≫ fL).base).obj V := hxV
  obtain ⟨_, ⟨a, rfl⟩, ha_mem, ha_le⟩ := Opens.isBasis_iff_nbhd.mp Spf.isBasis_basicOpen hpV
  obtain ⟨g, hg⟩ := exists_sectionsHom_eq_basicOpen_res f hU hUW hV hVW a
    ((hU.basicOpen_le_iff a ((Opens.map fL.base).obj V)).mpr ha_le)
  exact ⟨a, ha_mem, ((Spf.continuous_sectionsHom g).comp hcontV).congr fun s ↦ hg s⟩

/-- **Automatic continuity on all opens** (EGA I, Ch. I, 10.4.6): every morphism of formal schemes
`f : X ⟶ Y` is continuous on rings of sections over arbitrary opens `W ⊆ Y`, equipped with
`openSectionsTopology`. -/
theorem continuous_c_app_openSectionsTopology {X Y : FormalScheme.{u}} (f : X ⟶ Y) (W : Opens Y) :
    @Continuous _ _ (Y.openSectionsTopology W)
      (X.openSectionsTopology ((Opens.map (forgetToLocallyRingedSpace.map f).base).obj W))
      ((forgetToLocallyRingedSpace.map f).c.app (op W)) := by
  let _ := Y.openSectionsTopology W; let fL := forgetToLocallyRingedSpace.map f
  refine (continuous_iff_openSectionsTopology X _ _).mpr fun U hU hUW ↦ ?_
  let _ := X.sectionsTopology U hU
  refine (continuous_appLE_of_cover f (Y.openSectionsTopology W) hU hUW fun x hx ↦ ?_).congr
    fun s ↦ (ConcreteCategory.congr_hom (PresheafedSpace.Hom.appLE_def fL.toHom W U hUW) s).trans
      (ConcreteCategory.comp_apply _ _ s)
  obtain ⟨V, hV, hxV, hVW⟩ := Y.exists_isAffineOpen_mem_le (hUW hx)
  exact ⟨V, hV, hVW, hxV, (continuous_iff_openSectionsTopology Y W id).mp continuous_id V hV hVW⟩

/-- For any open cover `W ≤ ⨆ i, V i` by opens `V i ≤ W`, the restriction map from
`Γ(X, W)` (with `X.openSectionsTopology W`) into `∏ i, Γ(X, V i)` (with
`X.openSectionsTopology (V i)`) is a topological embedding (`Topology.IsEmbedding`). -/
theorem isEmbedding_pi_restrict_openSectionsTopology {ι : Type*} (X : FormalScheme.{u})
    {W : Opens X} {V : ι → Opens X} (hV : ∀ i, V i ≤ W) (hcov : W ≤ ⨆ i, V i) :
    @Topology.IsEmbedding (X.presheaf.obj (op W)) (∀ i : ι, X.presheaf.obj (op (V i)))
      (X.openSectionsTopology W)
      (@Pi.topologicalSpace ι _ fun i ↦ X.openSectionsTopology (V i))
      (fun s i ↦ X.presheaf.map (homOfLE (hV i)).op s) := by
  let _ := X.openSectionsTopology W; let _ (i : ι) := X.openSectionsTopology (V i)
  let Φ : X.presheaf.obj (op W) → ∀ i : ι, X.presheaf.obj (op (V i)) :=
    fun s i ↦ X.presheaf.map (homOfLE (hV i)).op s
  refine ⟨⟨le_antisymm (continuous_iff_le_induced.mp (continuous_pi fun i ↦
      continuous_restrict_openSectionsTopology X (hV i)))
    (le_iInf fun U ↦ le_iInf fun hU ↦ le_iInf fun hUW ↦ continuous_iff_le_induced.mp ?_)⟩,
    fun s t hst ↦ X.sheaf.eq_of_locally_eq' V W (fun i ↦ homOfLE (hV i)) hcov s t (congrFun hst)⟩
  let tInd := TopologicalSpace.induced Φ Pi.topologicalSpace
  let _ := X.sectionsTopology U hU
  have hUW' : U ≤ (Opens.map (forgetToLocallyRingedSpace.map (𝟙 X)).base).obj W := by
    rw [forgetToLocallyRingedSpace.map_id]; exact hUW
  refine (continuous_appLE_of_cover (𝟙 X) tInd hU hUW' fun x hx ↦ ?_).congr
    (ConcreteCategory.congr_hom (appLE_forgetToLocallyRingedSpace_id X hUW'))
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (hcov (show (x : X) ∈ W from hUW hx))
  obtain ⟨Up, hUp, hxUp, hUpV⟩ := X.exists_isAffineOpen_mem_le hi
  let _ := X.sectionsTopology Up hUp
  refine ⟨Up, hUp, hUpV.trans (hV i), ?_,
    (((continuous_iff_openSectionsTopology X (V i) id).mp continuous_id Up hUp hUpV).comp
      ((@continuous_apply _ (fun i ↦ X.presheaf.obj (op (V i)))
        (fun i ↦ X.openSectionsTopology (V i)) i).comp
        (@continuous_induced_dom _ _ Φ Pi.topologicalSpace))).congr fun s ↦
      (ConcreteCategory.comp_apply (X.presheaf.map (homOfLE (hV i)).op)
        (X.presheaf.map (homOfLE hUpV).op) s).symm.trans <| ConcreteCategory.congr_hom
        (TopCat.Presheaf.map_comp_map_eq X.presheaf (homOfLE (hV i)).op (homOfLE hUpV).op
          (homOfLE (hUpV.trans (hV i))).op) s⟩
  rw [forgetToLocallyRingedSpace.map_id]; exact hxUp
end SpecialCasesAndOpenTopology

section VanishingIdealAndFromSpf

/-- An isomorphism `e : X ≅ Y` of formal schemes pulls `X.vanishingIdeal ⊤` back to
`Y.vanishingIdeal ⊤` along `globalSectionsIsoOfIso e`. -/
theorem comap_vanishingIdeal_top_globalSectionsIsoOfIso_hom {X Y : FormalScheme.{u}} (e : X ≅ Y) :
    (X.vanishingIdeal ⊤).comap (globalSectionsIsoOfIso e).hom.hom = Y.vanishingIdeal ⊤ := by
  rw [globalSectionsIsoOfIso_hom]
  exact LocallyRingedSpace.comap_vanishingIdeal_top_of_iso (forgetToLocallyRingedSpace.mapIso e)

/-- On `ofSpf A`, the preimage of `vanishingIdeal ⊤` along `(Spf.topSectionsIso A).inv` is the
radical of every ideal of definition. -/
theorem comap_vanishingIdeal_ofSpf_topSectionsIso_inv {A : Type u} [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] [IsAdicRing A] {I : Ideal A} (hI : IsAdic I) :
    ((ofSpf A).vanishingIdeal ⊤).comap
        (CommRingCat.Hom.hom (R := CommRingCat.of A) (S := (ofSpf A).presheaf.obj (op ⊤))
          (Spf.topSectionsIso A).inv) = I.radical := by
  rw [← PrimeSpectrum.vanishingIdeal_zeroLocus_eq_radical I, ← Spf.carrier_eq_zeroLocus hI]
  refine Ideal.ext fun a ↦ Ideal.mem_comap.trans <|
    LocallyRingedSpace.mem_vanishingIdeal_top.trans
    ⟨fun h ↦ (PrimeSpectrum.mem_vanishingIdeal (Spf.carrier A) a).mpr fun p hp ↦
        (Spf.Γevaluation_topSectionsIso_inv_eq_zero_iff ⟨p, hp⟩ a).mp (h ⟨p, hp⟩),
      fun h p ↦ (Spf.Γevaluation_topSectionsIso_inv_eq_zero_iff p a).mpr
        ((PrimeSpectrum.mem_vanishingIdeal (Spf.carrier A) a).mp h p.val p.property)⟩

/-- On an affine formal open `U`, `X.sectionsTopology U hU` equals `J.adicTopology` for every
finitely generated ideal `J ⊆ Γ(U, O_X)` whose radical is `X.vanishingIdeal U`. -/
theorem sectionsTopology_eq_adic_of_vanishingIdeal (X : FormalScheme.{u}) (U : Opens X)
    (hU : X.IsAffineOpen U) {J : Ideal (X.presheaf.obj (op U))} (hJfg : J.FG)
    (hJrad : J.radical = X.vanishingIdeal U) :
    X.sectionsTopology U hU = J.adicTopology :=
  X.sectionsTopology_eq_adic hU hJfg fun s ↦ by
    rw [hJrad, LocallyRingedSpace.mem_vanishingIdeal]

/-- Every affine formal open `U` admits a finitely generated ideal `J ⊆ Γ(U, O_X)` with
`J.radical = X.vanishingIdeal U`. -/
theorem exists_fg_radical_eq_vanishingIdeal (X : FormalScheme.{u}) (U : Opens X)
    (hU : X.IsAffineOpen U) :
    ∃ J : Ideal (X.presheaf.obj (op U)), J.FG ∧ J.radical = X.vanishingIdeal U := by
  let _ := X.sectionsTopology U hU
  have := X.sectionsTopology_isTopologicalRing U hU
  have := X.sectionsTopology_isAdicRing U hU
  obtain ⟨hIfg, hIadic, -⟩ := IsAdicRing.ideal_spec (X.presheaf.obj (op U))
  refine ⟨IsAdicRing.ideal (X.presheaf.obj (op U)), hIfg, Ideal.ext fun s ↦ ?_⟩
  rw [← hIadic.isTopologicallyNilpotent_iff_mem_radical,
    isTopologicallyNilpotent_iff_forall_evaluation_eq_zero X U hU s,
    LocallyRingedSpace.mem_vanishingIdeal]

/-- If `φ : Γ(U, O_X) ≃+* R` pulls back a finitely generated ideal of definition `I` of `R` to an
ideal with radical `X.vanishingIdeal U`, then `X.sectionsTopology U hU` is induced by `φ`. -/
theorem sectionsTopology_eq_induced_of_isAdic {X : FormalScheme.{u}} {U : Opens X}
    (hU : X.IsAffineOpen U) {R : Type*} [CommRing R] [TopologicalSpace R]
    (φ : X.presheaf.obj (op U) ≃+* R) {I : Ideal R} (hIfg : I.FG) (hI : IsAdic I)
    (hrad : (I.comap φ).radical = X.vanishingIdeal U) :
    X.sectionsTopology U hU = TopologicalSpace.induced φ ‹TopologicalSpace R› := by
  let tU : TopologicalSpace (X.presheaf.obj (op U)) :=
    TopologicalSpace.induced φ ‹TopologicalSpace R›
  have hadic : @IsAdic _ _ tU (I.comap φ) := IsAdic.comap hI φ ⟨rfl⟩
  rw [X.sectionsTopology_eq_adic_of_vanishingIdeal U hU (hIfg.comap_of_equiv φ) hrad]
  exact hadic.symm

/-- If `φ : Γ(U, O_X) ≃+* R` pulls back a finitely generated ideal of definition `I` of `R` to an
ideal with radical `X.vanishingIdeal U`, then `φ` is a homeomorphism from `(Γ(U, O_X),
sectionsTopology)` onto `R`. -/
theorem isHomeomorph_sectionsTopology_of_isAdic {X : FormalScheme.{u}} {U : Opens X}
    (hU : X.IsAffineOpen U) {R : Type*} [CommRing R] [TopologicalSpace R]
    (φ : X.presheaf.obj (op U) ≃+* R) {I : Ideal R} (hIfg : I.FG) (hI : IsAdic I)
    (hrad : (I.comap φ).radical = X.vanishingIdeal U) :
    @IsHomeomorph _ _ (X.sectionsTopology U hU) ‹TopologicalSpace R› φ := by
  have htop := sectionsTopology_eq_induced_of_isAdic hU φ hIfg hI hrad
  let _ := X.sectionsTopology U hU
  exact (φ.toEquiv.toHomeomorphOfIsInducing ⟨htop⟩).isHomeomorph

/-- Any ring equivalence `φ : Γ(V, O_Y) ≃+* Γ(U, O_X)` between sections over affine formal opens
that pulls `X.vanishingIdeal U` back to `Y.vanishingIdeal V` induces `Y.sectionsTopology V hV` from
`X.sectionsTopology U hU`. -/
theorem sectionsTopology_eq_induced_of_comap_vanishingIdeal {X Y : FormalScheme.{u}}
    {U : Opens X} {V : Opens Y} (hU : X.IsAffineOpen U) (hV : Y.IsAffineOpen V)
    (φ : Y.presheaf.obj (op V) ≃+* X.presheaf.obj (op U))
    (hvan : (X.vanishingIdeal U).comap φ = Y.vanishingIdeal V) :
    Y.sectionsTopology V hV = TopologicalSpace.induced φ (X.sectionsTopology U hU) := by
  obtain ⟨J, hJfg, hJrad⟩ := X.exists_fg_radical_eq_vanishingIdeal U hU
  let tU : TopologicalSpace (X.presheaf.obj (op U)) := X.sectionsTopology U hU
  have hJadic : @IsAdic _ _ tU J := X.sectionsTopology_eq_adic_of_vanishingIdeal U hU hJfg hJrad
  have hKrad : (J.comap φ).radical = Y.vanishingIdeal V := by
    rw [← Ideal.comap_radical, hJrad, hvan]
  exact sectionsTopology_eq_induced_of_isAdic hV φ hJfg hJadic hKrad

/-- Any ring equivalence `φ : Γ(V, O_Y) ≃+* Γ(U, O_X)` between sections over affine formal opens
that pulls `X.vanishingIdeal U` back to `Y.vanishingIdeal V` is a homeomorphism for
`sectionsTopology`. -/
theorem isHomeomorph_sectionsTopology_of_comap_vanishingIdeal {X Y : FormalScheme.{u}}
    {U : Opens X} {V : Opens Y} (hU : X.IsAffineOpen U) (hV : Y.IsAffineOpen V)
    (φ : Y.presheaf.obj (op V) ≃+* X.presheaf.obj (op U))
    (hvan : (X.vanishingIdeal U).comap φ = Y.vanishingIdeal V) :
    @IsHomeomorph _ _ (Y.sectionsTopology V hV) (X.sectionsTopology U hU) φ := by
  have htop := sectionsTopology_eq_induced_of_comap_vanishingIdeal hU hV φ hvan
  let _ := Y.sectionsTopology V hV
  let _ := X.sectionsTopology U hU
  exact (φ.toEquiv.toHomeomorphOfIsInducing ⟨htop⟩).isHomeomorph

/-- On the empty open `⊥`, `sectionsTopology` is the discrete topology `⊥`. -/
@[simp]
theorem sectionsTopology_bot (X : FormalScheme.{u}) (h : X.IsAffineOpen ⊥) :
    X.sectionsTopology ⊥ h = ⊥ := by
  have hsub : Subsingleton (X.presheaf.obj (op (⊥ : Opens X))) := inferInstance
  let _ := X.sectionsTopology ⊥ h
  exact (@Subsingleton.discreteTopology _ _ hsub).eq_bot

/-- `PresheafedSpace.restrictTopSectionsIso` is a homeomorphism between
`(Γ(U, O_X), sectionsTopology)` and `(Γ(⊤, O_{X|_U}), sectionsTopology)`. -/
theorem isHomeomorph_restrictTopSectionsIso {X : FormalScheme.{u}} {U : Opens X}
    (hU : X.IsAffineOpen U) :
    @IsHomeomorph _ _ (X.sectionsTopology U hU)
      ((X.restrict U).sectionsTopology ⊤ hU.top_restrict)
      (X.toPresheafedSpace.restrictTopSectionsIso U).hom :=
  isHomeomorph_sectionsTopology_of_comap_vanishingIdeal hU.top_restrict hU
    (X.toPresheafedSpace.restrictTopSectionsIso U).commRingCatIsoToRingEquiv
    (X.toLocallyRingedSpace.comap_vanishingIdeal_restrictTopSectionsIso_hom U)

/-- For an isomorphism `e : X ≅ Y` between affine formal schemes, the induced global-sections map
`Γ(Y, O_Y) → Γ(X, O_X)` is a homeomorphism for `sectionsTopology`. -/
theorem isHomeomorph_globalSections_of_iso {X Y : FormalScheme.{u}} (e : X ≅ Y)
    (hX : X.IsAffineOpen ⊤) (hY : Y.IsAffineOpen ⊤) :
    @IsHomeomorph _ _ (Y.sectionsTopology ⊤ hY) (X.sectionsTopology ⊤ hX)
      (globalSectionsIsoOfIso e).hom :=
  isHomeomorph_sectionsTopology_of_comap_vanishingIdeal hX hY
    (globalSectionsIsoOfIso e).commRingCatIsoToRingEquiv
    (comap_vanishingIdeal_top_globalSectionsIsoOfIso_hom e)

namespace IsAffineOpen

/-- The canonical open immersion `ofSpf hU.Sections ⟶ X` with image `U`. -/
noncomputable def fromSpf {X : FormalScheme.{u}} {U : Opens X} (hU : X.IsAffineOpen U) :
    ofSpf hU.Sections ⟶ X :=
  hU.isoSpf.inv ≫ X.ofRestrict U

-- Keep `isoSpf_inv_ofRestrict` explicit so `@[simp]` lemmas on `fromSpf` remain in simp normal
-- form.
theorem isoSpf_inv_ofRestrict {X : FormalScheme.{u}} {U : Opens X} (hU : X.IsAffineOpen U) :
    hU.isoSpf.inv ≫ X.ofRestrict U = hU.fromSpf :=
  (rfl)

/-- Composing `hU.isoSpf.hom` with `hU.fromSpf` recovers the open inclusion `X.ofRestrict U`. -/
@[reassoc (attr := simp)]
theorem isoSpf_hom_fromSpf {X : FormalScheme.{u}} {U : Opens X} (hU : X.IsAffineOpen U) :
    hU.isoSpf.hom ≫ hU.fromSpf = X.ofRestrict U :=
  Iso.hom_inv_id_assoc hU.isoSpf (X.ofRestrict U)

/-- On global sections, `hU.fromSpf` followed by `Spf.topSectionsIso` is the presheaf restriction
from `⊤` to `U`. -/
@[reassoc (attr := simp)]
theorem fromSpf_c_app_top_comp_topSectionsIso_hom {X : FormalScheme.{u}} {U : Opens X}
    (hU : X.IsAffineOpen U) :
    ((forgetToLocallyRingedSpace.map hU.fromSpf).c.app (op ⊤) :
        X.presheaf.obj (op ⊤) ⟶ (Spf hU.Sections).presheaf.obj (op ⊤)) ≫
      (Spf.topSectionsIso hU.Sections).hom =
      X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op := by
  ext s
  have h1 : (forgetToLocallyRingedSpace.map hU.fromSpf).c.app (op ⊤) s =
      (forgetToLocallyRingedSpace.map hU.isoSpf.inv).c.app (op ⊤)
        ((forgetToLocallyRingedSpace.map (X.ofRestrict U)).c.app (op ⊤) s) := by
    rw [← isoSpf_inv_ofRestrict, Functor.map_comp]
    exact (ConcreteCategory.congr_hom
      (LocallyRingedSpace.Γ.map_comp
        (forgetToLocallyRingedSpace.map (X.ofRestrict U)).op
        (forgetToLocallyRingedSpace.map hU.isoSpf.inv).op) s).trans
      (ConcreteCategory.comp_apply _ _ s)
  have h2 := ConcreteCategory.congr_hom (isoSpf_inv_c_app_top_comp_topSectionsIso_hom hU)
    ((forgetToLocallyRingedSpace.map (X.ofRestrict U)).c.app (op ⊤) s)
  have h3 : (forgetToLocallyRingedSpace.map (X.ofRestrict U)).c.app (op ⊤) s =
      (X.toPresheafedSpace.restrictTopSectionsIso U).hom
        (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op s) := by
    rw [forgetToLocallyRingedSpace_map_ofRestrict]
    exact ConcreteCategory.congr_hom (X.toPresheafedSpace.ofRestrict_c_app_top U) s
  have h4 := Iso.hom_inv_id_apply (X.toPresheafedSpace.restrictTopSectionsIso U)
    (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op s)
  exact (congrArg (Spf.topSectionsIso hU.Sections).hom h1).trans <|
    h2.trans <| (congrArg (X.toPresheafedSpace.restrictTopSectionsIso U).inv h3).trans h4

instance isOpenImmersion_fromSpf {X : FormalScheme.{u}} {U : Opens X} (hU : X.IsAffineOpen U) :
    LocallyRingedSpace.IsOpenImmersion (forgetToLocallyRingedSpace.map hU.fromSpf) := by
  rw [← isoSpf_inv_ofRestrict, Functor.map_comp]
  have : IsIso (forgetToLocallyRingedSpace.map hU.isoSpf.inv) :=
    Functor.map_isIso forgetToLocallyRingedSpace hU.isoSpf.inv
  infer_instance

@[simp]
theorem range_fromSpf {X : FormalScheme.{u}} {U : Opens X} (hU : X.IsAffineOpen U) :
    Set.range (forgetToLocallyRingedSpace.map hU.fromSpf).base = (U : Set X) := by
  rw [← isoSpf_inv_ofRestrict, Functor.map_comp]
  exact (LocallyRingedSpace.range_iso_inv_comp
    (forgetToLocallyRingedSpace.mapIso hU.isoSpf)
    (forgetToLocallyRingedSpace.map (X.ofRestrict U))).trans (range_ofRestrict X U)

end IsAffineOpen

end VanishingIdealAndFromSpf

end TauCeti.FormalScheme

namespace AlgebraicGeometry.Scheme

open TauCeti TauCeti.FormalScheme

/-- On an ordinary scheme `Y`, every affine formal open of `Y.toFormalScheme` carries the discrete
intrinsic section topology (`⊥`). -/
@[simp]
theorem sectionsTopology_toFormalScheme_eq_bot (Y : Scheme.{u})
    (U : TopologicalSpace.Opens Y.toFormalScheme) (hU : Y.toFormalScheme.IsAffineOpen U) :
    Y.toFormalScheme.sectionsTopology U hU = ⊥ := by
  have hrad : (⊥ : Ideal (Y.toFormalScheme.presheaf.obj (op U))).radical =
      Y.toFormalScheme.vanishingIdeal U := by
    ext s
    rw [Ideal.mem_radical_iff, LocallyRingedSpace.mem_vanishingIdeal]
    simp only [Ideal.mem_bot]
    exact (Scheme.isNilpotent_iff_basicOpen_eq_bot_of_isCompact (X := Y) (U := U)
      hU.isCompact s).trans (Y.basicOpen_eq_bot_iff_forall_evaluation_eq_zero s)
  rw [Y.toFormalScheme.sectionsTopology_eq_adic_of_vanishingIdeal U hU Submodule.fg_bot hrad]
  let : TopologicalSpace (Y.toFormalScheme.presheaf.obj (op U)) :=
    (⊥ : Ideal (Y.toFormalScheme.presheaf.obj (op U))).adicTopology
  have : DiscreteTopology (Y.toFormalScheme.presheaf.obj (op U)) := is_bot_adic_iff.mp rfl
  exact DiscreteTopology.eq_bot

/-- On an ordinary scheme `Y`, the section ring over every affine formal open is discrete for
`sectionsTopology`. -/
theorem discreteTopology_sectionsTopology_toFormalScheme (Y : Scheme.{u})
    (U : TopologicalSpace.Opens Y.toFormalScheme) (hU : Y.toFormalScheme.IsAffineOpen U) :
    @DiscreteTopology _ (Y.toFormalScheme.sectionsTopology U hU) :=
  @DiscreteTopology.mk _ (Y.toFormalScheme.sectionsTopology U hU)
    (Y.sectionsTopology_toFormalScheme_eq_bot U hU)

end AlgebraicGeometry.Scheme

namespace TauCeti.FormalScheme

instance IsAffineOpen.discreteTopology_sections_toFormalScheme {Y : Scheme.{u}}
    {U : Opens Y.toFormalScheme} (hU : Y.toFormalScheme.IsAffineOpen U) :
    DiscreteTopology hU.Sections :=
  Y.discreteTopology_sectionsTopology_toFormalScheme U hU

end TauCeti.FormalScheme

namespace AlgebraicGeometry.Scheme

open TauCeti TauCeti.FormalScheme

/-- An open subset of an ordinary scheme `Y` is an affine formal open of `Y.toFormalScheme` if and
only if it is an affine open of `Y` as a scheme. -/
@[simp]
theorem isAffineOpen_toFormalScheme_iff (Y : Scheme.{u}) (U : Y.Opens) :
    Y.toFormalScheme.IsAffineOpen U ↔ AlgebraicGeometry.IsAffineOpen U := by
  refine ⟨fun hU ↦ ?_, FormalScheme.isAffineOpen_ofScheme⟩
  let U' : TopologicalSpace.Opens Y.toFormalScheme := U
  have hU' : Y.toFormalScheme.IsAffineOpen U' := hU
  let eLRS : U.toScheme.toLocallyRingedSpace ≅
      (Spec (CommRingCat.of hU'.Sections)).toLocallyRingedSpace :=
    FormalScheme.forgetToLocallyRingedSpace.mapIso hU'.isoSpf ≪≫ Spf.discreteIsoSpec hU'.Sections
  let e : U.toScheme ≅ Spec (CommRingCat.of hU'.Sections) :=
    Scheme.fullyFaithfulForgetToLocallyRingedSpace.preimageIso eLRS
  exact AlgebraicGeometry.IsAffine.of_isIso e.hom

end AlgebraicGeometry.Scheme

namespace TauCeti.FormalScheme

/-- If an affine formal scheme `ofSpf A` is isomorphic in `FormalScheme` to `Y.toFormalScheme` for
an ordinary scheme `Y`, then `A` carries the discrete topology. -/
theorem discreteTopology_of_ofSpf_iso_toFormalScheme {A : Type u} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [IsAdicRing A] {Y : Scheme.{u}} (e : ofSpf A ≅ Y.toFormalScheme) :
    DiscreteTopology A := by
  have hA : (ofSpf A).IsAffineOpen ⊤ := isAffineOpen_top_ofSpf A
  have hY : Y.toFormalScheme.IsAffineOpen ⊤ := isAffineOpen_top_of_iso e hA
  let _ := (ofSpf A).sectionsTopology ⊤ hA
  let _ := Y.toFormalScheme.sectionsTopology ⊤ hY
  have hdY : DiscreteTopology (Y.toFormalScheme.presheaf.obj (op ⊤)) :=
    Y.discreteTopology_sectionsTopology_toFormalScheme ⊤ hY
  have hdA : DiscreteTopology ((ofSpf A).presheaf.obj (op ⊤)) :=
    (isHomeomorph_globalSections_of_iso e hA hY).homeomorph.discreteTopology_iff.mp hdY
  exact (isHomeomorph_topSectionsIso_sectionsTopology A).homeomorph.discreteTopology_iff.mp hdA

/-- An affine formal scheme `ofSpf A` lies in the essential image of `Scheme.toFormalScheme`
(`ofScheme`) if and only if `A` carries the discrete topology. -/
@[simp]
theorem exists_ofSpf_iso_toFormalScheme_iff (A : Type u) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [IsAdicRing A] :
    (∃ Y : Scheme.{u}, Nonempty (ofSpf A ≅ Y.toFormalScheme)) ↔ DiscreteTopology A :=
  ⟨fun ⟨_, ⟨e⟩⟩ ↦ discreteTopology_of_ofSpf_iso_toFormalScheme e,
    fun _ ↦ ⟨Spec (CommRingCat.of A), ⟨(ofSchemeSpecIso A).symm⟩⟩⟩

end TauCeti.FormalScheme
