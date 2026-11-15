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

For an affine formal open `U` of a formal scheme `X` of finite ideal type, any chart
`e : X|_U ≅ Spf B` identifies `Γ(X, U) ≅ B` via `chartSectionsIso`. Since any `Spf B₁ ≅ Spf B₂`
induces a homeomorphism `B₂ ≃+* B₁` (`TauCeti.FormalScheme.Spf.isHomeomorph_isoToRingEquiv`), the
induced topology `X.sectionsTopology U hU` on `Γ(X, U)` is chart-independent (EGA I, Ch. I, 10.4.5),
makes `Γ(X, U)` (packaged with its adic ring instances as `hU.Sections`) an adic ring with
`X.restrict U ≅ ofSpf hU.Sections` (`IsAffineOpen.isoSpf`), has topologically nilpotent elements cut
out by residue vanishing on `U`, and makes affine section maps continuous (`sectionMap_continuous`).
For arbitrary opens `W ⊆ X`, `X.openSectionsTopology W` is the projective-limit topology over affine
opens `U ≤ W`, and every morphism of formal schemes `f : X ⟶ Y` is continuous on rings of sections
over arbitrary opens (`continuous_c_app_openSectionsTopology`; EGA I, Ch. I, 10.4.6).
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

/-- For any affine formal chart `e : X|_U ≅ Spf B`, the induced ring isomorphism `Γ(X, U) ≅ B`. -/
noncomputable def chartSectionsIso (X : FormalScheme.{u}) (U : Opens X) {B : Type u} [CommRing B]
    [TopologicalSpace B] [IsTopologicalRing B] [IsAdicRing B]
    (e : X.toLocallyRingedSpace.restrict U.isOpenEmbedding ≅ Spf B) :
    X.presheaf.obj (op U) ≅ CommRingCat.of B :=
  X.toLocallyRingedSpace.restrictTopSectionsIso U ≪≫
    (LocallyRingedSpace.Γ.mapIso e.symm.op : _ ≅ (Spf B).presheaf.obj (op ⊤)) ≪≫
    Spf.topSectionsIso B

theorem chartSectionsIso_hom_apply (X : FormalScheme.{u}) (U : Opens X) {B : Type u} [CommRing B]
    [TopologicalSpace B] [IsTopologicalRing B] [IsAdicRing B]
    (e : X.toLocallyRingedSpace.restrict U.isOpenEmbedding ≅ Spf B)
    (s : X.presheaf.obj (op U)) :
    (chartSectionsIso X U e).hom s =
      (Spf.topSectionsIso B).hom
        (e.inv.c.app (op ⊤) ((X.toLocallyRingedSpace.restrictTopSectionsIso U).hom s)) := (rfl)

theorem chartSectionsIso_inv_apply (X : FormalScheme.{u}) (U : Opens X) {B : Type u} [CommRing B]
    [TopologicalSpace B] [IsTopologicalRing B] [IsAdicRing B]
    (e : X.toLocallyRingedSpace.restrict U.isOpenEmbedding ≅ Spf B) (b : B) :
    (chartSectionsIso X U e).inv b =
      (X.toLocallyRingedSpace.restrictTopSectionsIso U).inv
        (e.hom.c.app (op ⊤) ((Spf.topSectionsIso B).inv b)) := (rfl)

/-- Changing the affine formal chart `X|_U ≅ Spf B` composes `chartSectionsIso` with the topological
ring isomorphism `Spf.isoToRingEquiv` of the transition isomorphism. -/
theorem chartSectionsIso_hom_comp_isoToRingEquiv (X : FormalScheme.{u}) (U : Opens X)
    {B₁ B₂ : Type u} [CommRing B₁] [TopologicalSpace B₁] [IsTopologicalRing B₁] [IsAdicRing B₁]
    [CommRing B₂] [TopologicalSpace B₂] [IsTopologicalRing B₂] [IsAdicRing B₂]
    (e₁ : X.toLocallyRingedSpace.restrict U.isOpenEmbedding ≅ Spf B₁)
    (e₂ : X.toLocallyRingedSpace.restrict U.isOpenEmbedding ≅ Spf B₂) :
    (chartSectionsIso X U e₁).hom ≫
        CommRingCat.ofHom (Spf.isoToRingEquiv (e₂.symm ≪≫ e₁)).toRingHom =
      (chartSectionsIso X U e₂).hom := by
  have h1 : (chartSectionsIso X U e₁).hom =
      (X.toLocallyRingedSpace.restrictTopSectionsIso U).hom ≫
        (e₁.inv.c.app (op ⊤) :
          (X.toLocallyRingedSpace.restrict U.isOpenEmbedding).presheaf.obj (op ⊤) ⟶
            (Spf B₁).presheaf.obj (op ⊤)) ≫
        (Spf.topSectionsIso B₁).hom := rfl
  have h2 : (chartSectionsIso X U e₂).hom =
      (X.toLocallyRingedSpace.restrictTopSectionsIso U).hom ≫
        (e₂.inv.c.app (op ⊤) :
          (X.toLocallyRingedSpace.restrict U.isOpenEmbedding).presheaf.obj (op ⊤) ⟶
            (Spf B₂).presheaf.obj (op ⊤)) ≫
        (Spf.topSectionsIso B₂).hom := rfl
  have hmid : (Spf.topSectionsIso B₁).hom ≫
        CommRingCat.ofHom (Spf.isoToRingEquiv (e₂.symm ≪≫ e₁)).toRingHom =
      (e₁.hom.c.app (op ⊤) :
          (Spf B₁).presheaf.obj (op ⊤) ⟶
            (X.toLocallyRingedSpace.restrict U.isOpenEmbedding).presheaf.obj (op ⊤)) ≫
        (e₂.inv.c.app (op ⊤) :
          (X.toLocallyRingedSpace.restrict U.isOpenEmbedding).presheaf.obj (op ⊤) ⟶
            (Spf B₂).presheaf.obj (op ⊤)) ≫
        (Spf.topSectionsIso B₂).hom := by
    rw [Spf.isoToRingEquiv_toRingHom, ← Spf.c_app_top_comp_topSectionsIso_hom (e₂.symm ≪≫ e₁).hom]
    exact Category.assoc _ _ _
  exact (congrArg (· ≫ _) h1).trans <| (Category.assoc _ _ _).trans <|
    (congrArg (_ ≫ ·) <| (Category.assoc _ _ _).trans <| (congrArg (_ ≫ ·) hmid).trans <|
      (Category.assoc _ _ _).symm.trans <|
        (congrArg (· ≫ _) (LocallyRingedSpace.iso_inv_c_app_top_comp_hom e₁)).trans
          (Category.id_comp _)).trans h2.symm

private theorem induced_chartSectionsIso_eq (X : FormalScheme.{u}) (U : Opens X)
    {B₁ B₂ : Type u} [CommRing B₁] [t₁ : TopologicalSpace B₁] [IsTopologicalRing B₁]
    [IsAdicRing B₁] [CommRing B₂] [t₂ : TopologicalSpace B₂] [IsTopologicalRing B₂]
    [IsAdicRing B₂]
    (e₁ : X.toLocallyRingedSpace.restrict U.isOpenEmbedding ≅ Spf B₁)
    (e₂ : X.toLocallyRingedSpace.restrict U.isOpenEmbedding ≅ Spf B₂) :
    TopologicalSpace.induced (chartSectionsIso X U e₁).hom t₁ =
      TopologicalSpace.induced (chartSectionsIso X U e₂).hom t₂ := by
  have hfun : ((chartSectionsIso X U e₂).hom : X.presheaf.obj (op U) → B₂) =
      Spf.isoToRingEquiv (e₂.symm ≪≫ e₁) ∘ (chartSectionsIso X U e₁).hom :=
    funext fun s ↦
      (ConcreteCategory.congr_hom (chartSectionsIso_hom_comp_isoToRingEquiv X U e₁ e₂) s).symm
  rw [hfun, ← induced_compose,
    ← (Spf.isHomeomorph_isoToRingEquiv (e₂.symm ≪≫ e₁)).isInducing.eq_induced]

/-- The canonical chart-independent adic topology on `Γ(X, U)` over an affine formal open `U ⊆ X`
(EGA I, Ch. I, 10.4.5). -/
@[instance_reducible]
noncomputable def sectionsTopology (X : FormalScheme.{u}) (U : Opens X) (hU : X.IsAffineOpen U) :
    TopologicalSpace (X.presheaf.obj (op U)) :=
  TopologicalSpace.induced (chartSectionsIso X U (chosenChart hU).iso).hom inferInstance

/-- `X.sectionsTopology U hU` is the topology induced along `chartSectionsIso X U e` for every
affine formal chart `e : X|_U ≅ Spf B`. -/
theorem sectionsTopology_eq_induced (X : FormalScheme.{u}) (U : Opens X) (hU : X.IsAffineOpen U)
    {B : Type u} [CommRing B] [tB : TopologicalSpace B] [IsTopologicalRing B] [IsAdicRing B]
    (e : X.toLocallyRingedSpace.restrict U.isOpenEmbedding ≅ Spf B) :
    X.sectionsTopology U hU = TopologicalSpace.induced (chartSectionsIso X U e).hom tB :=
  induced_chartSectionsIso_eq X U (chosenChart hU).iso e

/-- For every affine formal chart `e : X|_U ≅ Spf B`, `chartSectionsIso X U e` is a homeomorphism
from `(Γ(X, U), X.sectionsTopology U hU)` onto `B`. -/
theorem isHomeomorph_chartSectionsIso (X : FormalScheme.{u}) (U : Opens X) (hU : X.IsAffineOpen U)
    {B : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsAdicRing B]
    (e : X.toLocallyRingedSpace.restrict U.isOpenEmbedding ≅ Spf B) :
    @IsHomeomorph _ _ (X.sectionsTopology U hU) ‹TopologicalSpace B›
      (chartSectionsIso X U e).hom := by
  let _ := X.sectionsTopology U hU
  exact ((chartSectionsIso X U e).commRingCatIsoToRingEquiv.toEquiv.toHomeomorphOfIsInducing
    ⟨sectionsTopology_eq_induced X U hU e⟩).isHomeomorph

/-- Equipped with `X.sectionsTopology U hU`, the section ring `Γ(X, U)` over an affine formal open
is a topological ring. -/
theorem sectionsTopology_isTopologicalRing (X : FormalScheme.{u}) (U : Opens X)
    (hU : X.IsAffineOpen U) :
    @IsTopologicalRing (X.presheaf.obj (op U)) (X.sectionsTopology U hU) _ := by
  obtain ⟨B, _, _, _, _, ⟨e⟩⟩ := (X.isAffineOpen_iff U).mp hU
  let _ := X.sectionsTopology U hU
  let φ := (chartSectionsIso X U e).commRingCatIsoToRingEquiv
  have he : Topology.IsInducing φ := ⟨sectionsTopology_eq_induced X U hU e⟩
  exact IsTopologicalSemiring.toIsTopologicalRing
    { toContinuousAdd := he.continuousAdd φ, toContinuousMul := he.continuousMul φ }

/-- Equipped with `X.sectionsTopology U hU`, the section ring `Γ(X, U)` over an affine formal open
is a complete separated adic ring of finite ideal type (EGA I, Ch. I, 10.4.5). -/
theorem sectionsTopology_isAdicRing (X : FormalScheme.{u}) (U : Opens X) (hU : X.IsAffineOpen U) :
    @IsAdicRing (X.presheaf.obj (op U)) _ (X.sectionsTopology U hU)
      (X.sectionsTopology_isTopologicalRing U hU) := by
  obtain ⟨B, _, _, _, _, ⟨e⟩⟩ := (X.isAffineOpen_iff U).mp hU
  let _ := X.sectionsTopology U hU
  have := X.sectionsTopology_isTopologicalRing U hU
  let φ : (X.presheaf.obj (op U) : Type u) ≃+* B :=
    (chartSectionsIso X U e).commRingCatIsoToRingEquiv
  obtain ⟨I, hIfg, hIadic, hIcomp⟩ := IsAdicRing.exists_isAdic (A := B)
  exact ⟨⟨I.map φ.symm.toRingHom, hIfg.map φ.symm.toRingHom,
    (Ideal.map_symm φ).symm ▸ hIadic.comap φ ⟨sectionsTopology_eq_induced X U hU e⟩,
    (IsAdicComplete.congr_ringEquiv I φ.symm).mpr hIcomp⟩⟩

end ChartTopology

section ResidueCharacterization

/-- Over an affine formal open `U ⊆ X`, a section `s ∈ Γ(X, U)` is topologically nilpotent for
`X.sectionsTopology U hU` if and only if its image in the residue field vanishes at every point of
`U` (EGA I, Ch. I, 10.4.5). -/
theorem isTopologicallyNilpotent_iff_forall_evaluation_eq_zero (X : FormalScheme.{u}) (U : Opens X)
    (hU : X.IsAffineOpen U) (s : X.presheaf.obj (op U)) :
    @IsTopologicallyNilpotent _ _ (X.sectionsTopology U hU) s ↔
      ∀ x : U, X.toLocallyRingedSpace.evaluation x s = 0 := by
  obtain ⟨B, _, _, _, _, ⟨e⟩⟩ := (X.isAffineOpen_iff U).mp hU
  let _ := X.sectionsTopology U hU
  have := X.sectionsTopology_isTopologicalRing U hU
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
    exact (congrArg ((Spf B).Γevaluation p') hsec₂).trans <|
      (LocallyRingedSpace.Γevaluation_naturality_apply e.inv p' _).symm.trans <|
        (congrArg (LocallyRingedSpace.residueFieldMap e.inv p')
          ((X.toLocallyRingedSpace.evaluation_eq_zero_iff_restrict_Γevaluation_eq_zero U
            (e.inv.base p') s).mp (h (e.inv.base p')))).trans (map_zero _)

/-- A finitely generated ideal `J` of `Γ(X, U)` over an affine formal open `U` defines
`X.sectionsTopology U hU` whenever its radical consists of the sections vanishing in every residue
field on `U` (EGA I, Ch. I, 10.4.5). -/
theorem sectionsTopology_eq_adic {X : FormalScheme.{u}} {U : Opens X} (hU : X.IsAffineOpen U)
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

end ResidueCharacterization

section CanonicalChart

namespace IsAffineOpen

/-- Type synonym for `Γ(X, U)` over an affine formal open `U ⊆ X`, carrying its canonical
chart-independent adic ring structure (`FormalScheme.sectionsTopology`). The body is exposed so
ring homomorphisms and sections over `U` apply directly to `hU.Sections`. -/
@[expose] def Sections {X : FormalScheme.{u}} {U : Opens X} (_ : X.IsAffineOpen U) : Type u :=
  X.presheaf.obj (op U)

instance {X : FormalScheme.{u}} {U : Opens X} (hU : X.IsAffineOpen U) : CommRing hU.Sections :=
  inferInstanceAs (CommRing (X.presheaf.obj (op U)))

noncomputable instance {X : FormalScheme.{u}} {U : Opens X} (hU : X.IsAffineOpen U) :
    TopologicalSpace hU.Sections :=
  X.sectionsTopology U hU

instance {X : FormalScheme.{u}} {U : Opens X} (hU : X.IsAffineOpen U) :
    IsTopologicalRing hU.Sections :=
  X.sectionsTopology_isTopologicalRing U hU

instance {X : FormalScheme.{u}} {U : Opens X} (hU : X.IsAffineOpen U) : IsAdicRing hU.Sections :=
  X.sectionsTopology_isAdicRing U hU

/-- Every affine formal open `U ⊆ X` is canonically isomorphic as a formal scheme to the formal
spectrum of `hU.Sections` (EGA I, Ch. I, 10.4.5). -/
noncomputable def isoSpf {X : FormalScheme.{u}} {U : Opens X} (hU : X.IsAffineOpen U) :
    X.restrict U ≅ ofSpf hU.Sections :=
  let φ : hU.Sections ≃+* (chosenChart hU).B :=
    (chartSectionsIso X U (chosenChart hU).iso).commRingCatIsoToRingEquiv
  let hφ := φ.toEquiv.isHomeomorph_iff.mp
    (isHomeomorph_chartSectionsIso X U hU (chosenChart hU).iso)
  InducedCategory.isoMk ((chosenChart hU).iso ≪≫ Spf.mapIso φ hφ.1 hφ.2)

end IsAffineOpen

/-- On global sections, `hU.isoSpf.hom` identifies `Spf.topSectionsIso` with
`X.toLocallyRingedSpace.restrictTopSectionsIso U`, independently of any chosen chart. -/
@[reassoc (attr := simp)]
theorem topSectionsIso_inv_isoSpf_hom_c_app_top {X : FormalScheme.{u}} {U : Opens X}
    (hU : X.IsAffineOpen U) :
    (Spf.topSectionsIso hU.Sections).inv ≫
      ((forgetToLocallyRingedSpace.map hU.isoSpf.hom).c.app (op ⊤) :
        (Spf hU.Sections).presheaf.obj (op ⊤) ⟶
          (X.toLocallyRingedSpace.restrict U.isOpenEmbedding).presheaf.obj (op ⊤)) =
      (X.toLocallyRingedSpace.restrictTopSectionsIso U).hom := by
  let e := (chosenChart hU).iso
  let φ : hU.Sections ≃+* (chosenChart hU).B := (chartSectionsIso X U e).commRingCatIsoToRingEquiv
  let hφ := φ.toEquiv.isHomeomorph_iff.mp (isHomeomorph_chartSectionsIso X U hU e)
  have hφ₁ : Continuous φ.toRingHom := hφ.1
  have hm : (Spf.topSectionsIso hU.Sections).inv ≫
        ((Spf.map φ.toRingHom hφ₁).c.app (op ⊤) :
          (Spf hU.Sections).presheaf.obj (op ⊤) ⟶ (Spf (chosenChart hU).B).presheaf.obj (op ⊤)) =
      (chartSectionsIso X U e).hom ≫ (Spf.topSectionsIso (chosenChart hU).B).inv := by
    rw [Spf.topSectionsIso_inv_comp_c_app_top, Spf.sectionsHom_map]; rfl
  have hmap : ((Spf.mapIso φ hφ.1 hφ.2).hom.c.app (op ⊤) :
        (Spf hU.Sections).presheaf.obj (op ⊤) ⟶ (Spf (chosenChart hU).B).presheaf.obj (op ⊤)) =
      (Spf.map φ.toRingHom hφ₁).c.app (op ⊤) := by
    have h : ∀ {Z₁ Z₂ : LocallyRingedSpace.{u}} {f₁ f₂ : Z₁ ⟶ Z₂}, f₁ = f₂ →
        (f₁.c.app (op ⊤) : Z₂.presheaf.obj (op ⊤) ⟶ Z₁.presheaf.obj (op ⊤)) = f₂.c.app (op ⊤) := by
      rintro _ _ _ _ rfl; rfl
    exact h (Spf.mapIso_hom φ hφ.1 hφ.2)
  let isoHomTop : (Spf hU.Sections).presheaf.obj (op ⊤) ⟶
      (X.toLocallyRingedSpace.restrict U.isOpenEmbedding).presheaf.obj (op ⊤) :=
    (forgetToLocallyRingedSpace.map hU.isoSpf.hom).c.app (op ⊤)
  let mTop : (Spf hU.Sections).presheaf.obj (op ⊤) ⟶
      (Spf (chosenChart hU).B).presheaf.obj (op ⊤) := (Spf.map φ.toRingHom hφ₁).c.app (op ⊤)
  let eHomTop : (Spf (chosenChart hU).B).presheaf.obj (op ⊤) ⟶
      (X.toLocallyRingedSpace.restrict U.isOpenEmbedding).presheaf.obj (op ⊤) := e.hom.c.app (op ⊤)
  let eInvTop : (X.toLocallyRingedSpace.restrict U.isOpenEmbedding).presheaf.obj (op ⊤) ⟶
      (Spf (chosenChart hU).B).presheaf.obj (op ⊤) := e.inv.c.app (op ⊤)
  let rUHom : CommRingCat.of hU.Sections ⟶
      (X.toLocallyRingedSpace.restrict U.isOpenEmbedding).presheaf.obj (op ⊤) :=
    (X.toLocallyRingedSpace.restrictTopSectionsIso U).hom
  let chHom : CommRingCat.of hU.Sections ⟶ CommRingCat.of (chosenChart hU).B :=
    (chartSectionsIso X U e).hom
  have hch : chHom = rUHom ≫ eInvTop ≫ (Spf.topSectionsIso (chosenChart hU).B).hom := rfl
  have hcomp : isoHomTop = mTop ≫ eHomTop := congrArg (· ≫ eHomTop) hmap
  calc
    (Spf.topSectionsIso hU.Sections).inv ≫ isoHomTop
      = ((Spf.topSectionsIso hU.Sections).inv ≫ mTop) ≫ eHomTop := by
        rw [hcomp, Category.assoc]
    _ = (chHom ≫ (Spf.topSectionsIso (chosenChart hU).B).inv) ≫ eHomTop := by
        rw [show (Spf.topSectionsIso hU.Sections).inv ≫ mTop =
            chHom ≫ (Spf.topSectionsIso (chosenChart hU).B).inv from hm]
    _ = rUHom ≫ (eInvTop ≫ eHomTop) := by
        simp only [hch, Category.assoc, Iso.hom_inv_id_assoc]
    _ = rUHom := by
        rw [show eInvTop ≫ eHomTop = 𝟙 _ from LocallyRingedSpace.iso_inv_c_app_top_comp_hom e,
          Category.comp_id]

/-- Dual form of `topSectionsIso_inv_isoSpf_hom_c_app_top` for `hU.isoSpf.inv`. -/
@[reassoc (attr := simp)]
theorem isoSpf_inv_c_app_top_comp_topSectionsIso_hom {X : FormalScheme.{u}} {U : Opens X}
    (hU : X.IsAffineOpen U) :
    ((forgetToLocallyRingedSpace.map hU.isoSpf.inv).c.app (op ⊤) :
        (X.toLocallyRingedSpace.restrict U.isOpenEmbedding).presheaf.obj (op ⊤) ⟶
          (Spf hU.Sections).presheaf.obj (op ⊤)) ≫
      (Spf.topSectionsIso hU.Sections).hom =
      (X.toLocallyRingedSpace.restrictTopSectionsIso U).inv := by
  refine (cancel_epi (X.toLocallyRingedSpace.restrictTopSectionsIso U).hom).mp ?_
  let rUHom : CommRingCat.of hU.Sections ⟶
      (X.toLocallyRingedSpace.restrict U.isOpenEmbedding).presheaf.obj (op ⊤) :=
    (X.toLocallyRingedSpace.restrictTopSectionsIso U).hom
  let rUInv : (X.toLocallyRingedSpace.restrict U.isOpenEmbedding).presheaf.obj (op ⊤) ⟶
      CommRingCat.of hU.Sections :=
    (X.toLocallyRingedSpace.restrictTopSectionsIso U).inv
  let isoHomTop : (Spf hU.Sections).presheaf.obj (op ⊤) ⟶
      (X.toLocallyRingedSpace.restrict U.isOpenEmbedding).presheaf.obj (op ⊤) :=
    (forgetToLocallyRingedSpace.map hU.isoSpf.hom).c.app (op ⊤)
  let isoInvTop : (X.toLocallyRingedSpace.restrict U.isOpenEmbedding).presheaf.obj (op ⊤) ⟶
      (Spf hU.Sections).presheaf.obj (op ⊤) :=
    (forgetToLocallyRingedSpace.map hU.isoSpf.inv).c.app (op ⊤)
  calc
    rUHom ≫ isoInvTop ≫ (Spf.topSectionsIso hU.Sections).hom
      = ((Spf.topSectionsIso hU.Sections).inv ≫ isoHomTop) ≫
          isoInvTop ≫ (Spf.topSectionsIso hU.Sections).hom := by
        rw [show rUHom = (Spf.topSectionsIso hU.Sections).inv ≫ isoHomTop from
          (topSectionsIso_inv_isoSpf_hom_c_app_top hU).symm]
    _ = (Spf.topSectionsIso hU.Sections).inv ≫ (Spf.topSectionsIso hU.Sections).hom := by
        rw [Category.assoc, show isoHomTop ≫ isoInvTop ≫ (Spf.topSectionsIso hU.Sections).hom =
              (Spf.topSectionsIso hU.Sections).hom from
            (LocallyRingedSpace.iso_hom_c_app_top_comp_inv_assoc
              (forgetToLocallyRingedSpace.mapIso hU.isoSpf)
              (Spf.topSectionsIso hU.Sections).hom).trans (Category.id_comp _)]
    _ = rUHom ≫ rUInv := by
        rw [Iso.inv_hom_id, show rUHom ≫ rUInv = 𝟙 _ from
          (X.toLocallyRingedSpace.restrictTopSectionsIso U).hom_inv_id]

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
    let fUVTop : (Y.toLocallyRingedSpace.restrict V.isOpenEmbedding).presheaf.obj (op ⊤) ⟶
        (X.toLocallyRingedSpace.restrict U.isOpenEmbedding).presheaf.obj (op ⊤) := fUV.c.app (op ⊤)
    let isoVTop : (Spf hV.Sections).presheaf.obj (op ⊤) ⟶
        (Y.toLocallyRingedSpace.restrict V.isOpenEmbedding).presheaf.obj (op ⊤) :=
      (forgetToLocallyRingedSpace.map hV.isoSpf.hom).c.app (op ⊤)
    let isoUTop : (X.toLocallyRingedSpace.restrict U.isOpenEmbedding).presheaf.obj (op ⊤) ⟶
        (Spf hU.Sections).presheaf.obj (op ⊤) :=
      (forgetToLocallyRingedSpace.map hU.isoSpf.inv).c.app (op ⊤)
    let rVHom : CommRingCat.of hV.Sections ⟶
        (Y.toLocallyRingedSpace.restrict V.isOpenEmbedding).presheaf.obj (op ⊤) :=
      (Y.toLocallyRingedSpace.restrictTopSectionsIso V).hom
    let rUHom : CommRingCat.of hU.Sections ⟶
        (X.toLocallyRingedSpace.restrict U.isOpenEmbedding).presheaf.obj (op ⊤) :=
      (X.toLocallyRingedSpace.restrictTopSectionsIso U).hom
    let rUInv : (X.toLocallyRingedSpace.restrict U.isOpenEmbedding).presheaf.obj (op ⊤) ⟶
        CommRingCat.of hU.Sections :=
      (X.toLocallyRingedSpace.restrictTopSectionsIso U).inv
    let fMap : CommRingCat.of hV.Sections ⟶ CommRingCat.of hU.Sections :=
      (forgetToLocallyRingedSpace.map f).c.app (op V) ≫ X.presheaf.map (homOfLE hUV).op
    calc
      CommRingCat.ofHom (Spf.sectionsHom g)
        = ((Spf.topSectionsIso hV.Sections).inv ≫ isoVTop) ≫ fUVTop ≫
            (isoUTop ≫ (Spf.topSectionsIso hU.Sections).hom) := by
          rw [Spf.ofHom_sectionsHom]
          exact (congrArg (_ ≫ ·) ((Category.assoc _ _ _).trans
            (congrArg (_ ≫ ·) (Category.assoc _ _ _)))).trans (Category.assoc _ _ _).symm
      _ = (rVHom ≫ fUVTop) ≫ rUInv := by
          rw [show (Spf.topSectionsIso hV.Sections).inv ≫ isoVTop = rVHom from
              topSectionsIso_inv_isoSpf_hom_c_app_top hV,
            show isoUTop ≫ (Spf.topSectionsIso hU.Sections).hom = rUInv from
              isoSpf_inv_c_app_top_comp_topSectionsIso_hom hU,
            ← Category.assoc]
      _ = fMap := by
          rw [show rVHom ≫ fUVTop = fMap ≫ rUHom from
              (LocallyRingedSpace.restrictTopSectionsIso_hom_c_app_top_of_fac
                (forgetToLocallyRingedSpace.map f) hUV fUV hfac).trans (Category.assoc _ _ _).symm,
            Category.assoc,
            show rUHom ≫ rUInv = 𝟙 _ from
              (X.toLocallyRingedSpace.restrictTopSectionsIso U).hom_inv_id,
            Category.comp_id]
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
  have hhom : (eTop.hom.c.app (op ⊤) :
        (ofSpf A).presheaf.obj (op ⊤) ⟶
          ((ofSpf A).toLocallyRingedSpace.restrict
            (⊤ : Opens (ofSpf A)).isOpenEmbedding).presheaf.obj (op ⊤)) =
      ((ofSpf A).toLocallyRingedSpace.restrictTopSectionsIso ⊤).hom := by
    have h := (ofSpf A).toLocallyRingedSpace.ofRestrict_c_app_top ⊤
    rwa [TopCat.Presheaf.map_eq_id, Category.id_comp] at h
  have hinv : ((ofSpf A).toLocallyRingedSpace.restrictTopSectionsIso ⊤).hom ≫
        (eTop.inv.c.app (op ⊤) :
          ((ofSpf A).toLocallyRingedSpace.restrict
            (⊤ : Opens (ofSpf A)).isOpenEmbedding).presheaf.obj (op ⊤) ⟶
          (ofSpf A).presheaf.obj (op ⊤)) = 𝟙 _ :=
    (congrArg (· ≫ _) hhom.symm).trans (LocallyRingedSpace.iso_hom_c_app_top_comp_inv eTop)
  exact ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) hinv)).trans (Category.id_comp _)

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

/-- **Automatic continuity on all opens** (EGA I, Ch. I, 10.4.6): every morphism of formal schemes
`f : X ⟶ Y` is continuous on rings of sections over arbitrary opens `W ⊆ Y`, equipped with
`openSectionsTopology`. -/
theorem continuous_c_app_openSectionsTopology {X Y : FormalScheme.{u}} (f : X ⟶ Y) (W : Opens Y) :
    @Continuous _ _ (Y.openSectionsTopology W)
      (X.openSectionsTopology ((Opens.map (forgetToLocallyRingedSpace.map f).base).obj W))
      ((forgetToLocallyRingedSpace.map f).c.app (op W)) := by
  let _ := Y.openSectionsTopology W
  let fL := forgetToLocallyRingedSpace.map f
  refine (continuous_iff_openSectionsTopology X _ _).mpr fun U hU hUW ↦ ?_
  let A := hU.Sections
  obtain ⟨hIAfg, hIA, _⟩ := IsAdicRing.ideal_spec A
  let e : X.toLocallyRingedSpace.restrict U.isOpenEmbedding ≅ Spf A :=
    forgetToLocallyRingedSpace.mapIso hU.isoSpf
  let jU := X.toLocallyRingedSpace.ofRestrict U.isOpenEmbedding
  have hcover_aux (x : U) : ∃ (V : Opens Y) (_ : Y.IsAffineOpen V) (_ : V ≤ W) (a : A),
      e.hom.base x ∈ Spf.basicOpen a ∧
        Spf.basicOpen a ≤ (Opens.map (e.inv ≫ jU ≫ fL).base).obj V := by
    obtain ⟨V, hV, hxV, hVW⟩ := Y.exists_isAffineOpen_mem_le (hUW x.2)
    have hmem : e.hom.base x ∈ (Opens.map (e.inv ≫ jU ≫ fL).base).obj V := by
      have hinv : e.inv.base (e.hom.base x) = x :=
        ConcreteCategory.congr_hom (congrArg
          (fun k : X.toLocallyRingedSpace.restrict U.isOpenEmbedding ⟶
            X.toLocallyRingedSpace.restrict U.isOpenEmbedding ↦ k.base) e.hom_inv_id) x
      have hpt : (e.inv ≫ jU ≫ fL).base (e.hom.base x) = fL.base x.1 :=
        congrArg (fun z : U ↦ fL.base (jU.base z)) hinv
      exact Opens.mem_map.mpr (hpt.symm ▸ hxV)
    obtain ⟨_, ⟨a, rfl⟩, ha_mem, ha_le⟩ :=
      Opens.isBasis_iff_nbhd.mp Spf.isBasis_basicOpen hmem
    exact ⟨V, hV, hVW, a, ha_mem, ha_le⟩
  choose V hV hVW a ha_mem ha_le using hcover_aux
  have hcov : (⊤ : Opens (Spf.carrier A)) ≤ ⨆ x : U, Spf.basicOpen (a x) := fun p _ ↦ by
    refine Opens.mem_iSup.mpr ⟨e.inv.base p, ?_⟩
    have hinv : e.hom.base (e.inv.base p) = p :=
      ConcreteCategory.congr_hom (congrArg (fun k : Spf A ⟶ Spf A ↦ k.base) e.inv_hom_id) p
    have hp := ha_mem (e.inv.base p)
    rwa [hinv] at hp
  let _ : TopologicalSpace ((Spf.structureSheaf hIA).obj.obj (op ⊤)) :=
    Spf.quotientSectionsTopology hIA ⊤
  let _ (x : U) : TopologicalSpace ((Spf.structureSheaf hIA).obj.obj (op (Spf.basicOpen (a x)))) :=
    Spf.quotientSectionsTopology hIA (Spf.basicOpen (a x))
  let gW : Y.presheaf.obj (op W) → A := fun s ↦ X.presheaf.map (homOfLE hUW).op (fL.c.app (op W) s)
  suffices hcont : @Continuous _ _ (Y.openSectionsTopology W) (Spf.quotientSectionsTopology hIA ⊤)
      ((Spf.topSectionsIso A).inv ∘ gW) from
    (@Continuous.comp _ _ _ (Y.openSectionsTopology W) (Spf.quotientSectionsTopology hIA ⊤) _ _ _
      (Spf.isHomeomorph_topSectionsIso A).continuous hcont).congr fun s ↦
        ConcreteCategory.congr_hom (Spf.topSectionsIso A).inv_hom_id _
  refine (Spf.quotientSectionsTopology_glue hIA (fun _ ↦ le_top) hcov).isInducing.continuous_iff.mpr
    (continuous_pi_iff.mpr fun x ↦ ?_)
  refine (Spf.quotientSectionsTopology_basic hIA hIAfg (a x)).isInducing.continuous_iff.mpr ?_
  let m : Spf (AdicRing.CompletedAway A (a x)) ⟶ Spf A :=
    Spf.map (algebraMap A (AdicRing.CompletedAway A (a x)))
      (AdicRing.CompletedAway.continuous_algebraMap A (a x))
  let jV := Y.toLocallyRingedSpace.ofRestrict (V x).isOpenEmbedding
  have hsub : Set.range ((m ≫ e.inv) ≫ jU ≫ fL).base ⊆ Set.range jV.base := by
    rintro _ ⟨p, rfl⟩
    have hp : m.base p ∈ Spf.basicOpen (a x) := by
      have hr : Set.range m.base = (Spf.basicOpen (a x) : Set (Spf.carrier A)) := by
        rw [Spf.map_base, ← Spf.basicOpenι_base, Spf.range_basicOpenι]
      exact SetLike.mem_coe.mp (hr ▸ Set.mem_range_self p)
    exact ⟨⟨(e.inv ≫ jU ≫ fL).base (m.base p), ha_le x hp⟩, rfl⟩
  let l := LocallyRingedSpace.IsOpenImmersion.lift jV ((m ≫ e.inv) ≫ jU ≫ fL) hsub
  have hfac := LocallyRingedSpace.IsOpenImmersion.lift_fac jV ((m ≫ e.inv) ≫ jU ≫ fL) hsub
  let g : Spf (AdicRing.CompletedAway A (a x)) ⟶ Spf (hV x).Sections :=
    l ≫ forgetToLocallyRingedSpace.map (hV x).isoSpf.hom
  let resV : Y.presheaf.obj (op W) → (hV x).Sections := Y.presheaf.map (homOfLE (hVW x)).op
  have hc1 : Continuous resV :=
    (continuous_iff_openSectionsTopology Y W id).mp continuous_id (V x) (hV x) (hVW x)
  have hc2 : Continuous (Spf.sectionsHom g) := Spf.continuous_sectionsHom g
  refine (hc2.comp hc1).congr fun s ↦ ?_
  have he_inv : (X.toLocallyRingedSpace.restrictTopSectionsIso U).hom ≫
        (e.inv.c.app (op ⊤) :
          (X.toLocallyRingedSpace.restrict U.isOpenEmbedding).presheaf.obj (op ⊤) ⟶
            (Spf A).presheaf.obj (op ⊤)) = (Spf.topSectionsIso A).inv :=
    (congrArg (· ≫ _) (topSectionsIso_inv_isoSpf_hom_c_app_top hU).symm).trans <|
      (Category.assoc _ _ _).trans <|
        (congrArg (_ ≫ ·) (LocallyRingedSpace.iso_hom_c_app_top_comp_inv e)).trans
          (Category.comp_id _)
  have hm1 : (Spf.topSectionsIso A).inv ≫
        (m.c.app (op ⊤) : (Spf A).presheaf.obj (op ⊤) ⟶
          (Spf (AdicRing.CompletedAway A (a x))).presheaf.obj (op ⊤)) ≫
        (Spf.topSectionsIso (AdicRing.CompletedAway A (a x))).hom =
      CommRingCat.ofHom (algebraMap A (AdicRing.CompletedAway A (a x))) :=
    (Spf.ofHom_sectionsHom m).symm.trans <| congrArg CommRingCat.ofHom <|
      Spf.sectionsHom_map _ (AdicRing.CompletedAway.continuous_algebraMap A (a x))
  let φg := Spf.sectionsHom g
  let resVHom : Y.presheaf.obj (op W) ⟶ CommRingCat.of (hV x).Sections :=
    Y.presheaf.map (homOfLE (hVW x)).op
  let lTop : (Y.toLocallyRingedSpace.restrict (V x).isOpenEmbedding).presheaf.obj (op ⊤) ⟶
      (Spf (AdicRing.CompletedAway A (a x))).presheaf.obj (op ⊤) := l.c.app (op ⊤)
  let meTop : (X.toLocallyRingedSpace.restrict U.isOpenEmbedding).presheaf.obj (op ⊤) ⟶
      (Spf (AdicRing.CompletedAway A (a x))).presheaf.obj (op ⊤) := (m ≫ e.inv).c.app (op ⊤)
  let fLW : Y.presheaf.obj (op W) ⟶ X.presheaf.obj (op ((Opens.map fL.base).obj W)) :=
    fL.c.app (op W)
  let rVHom : CommRingCat.of (hV x).Sections ⟶
      (Y.toLocallyRingedSpace.restrict (V x).isOpenEmbedding).presheaf.obj (op ⊤) :=
    (Y.toLocallyRingedSpace.restrictTopSectionsIso (V x)).hom
  have hmid : resVHom ≫ CommRingCat.ofHom φg =
      fLW ≫ X.presheaf.map (homOfLE hUW).op ≫
        CommRingCat.ofHom (algebraMap A (AdicRing.CompletedAway A (a x))) := by
    calc
      resVHom ≫ CommRingCat.ofHom φg
        = (resVHom ≫ rVHom ≫ lTop) ≫
            (Spf.topSectionsIso (AdicRing.CompletedAway A (a x))).hom :=
          (congrArg (_ ≫ ·) <| (Spf.ofHom_sectionsHom g).trans <|
            (congrArg (_ ≫ ·) (Category.assoc _ _ _)).trans <|
            (Category.assoc _ _ _).symm.trans <|
              (topSectionsIso_inv_isoSpf_hom_c_app_top_assoc (hV x) _).trans
                (Category.assoc _ _ _).symm).trans (Category.assoc _ _ _).symm
      _ = (fLW ≫ X.presheaf.map (homOfLE hUW).op ≫
            (X.toLocallyRingedSpace.restrictTopSectionsIso U).hom ≫ meTop) ≫
            (Spf.topSectionsIso (AdicRing.CompletedAway A (a x))).hom :=
          congrArg (· ≫ (Spf.topSectionsIso (AdicRing.CompletedAway A (a x))).hom)
            (LocallyRingedSpace.restrictTopSectionsIso_hom_c_app_top_of_fac_le
              fL (hVW x) hUW l (m ≫ e.inv) hfac)
      _ = fLW ≫ X.presheaf.map (homOfLE hUW).op ≫
            (((X.toLocallyRingedSpace.restrictTopSectionsIso U).hom ≫
              (e.inv.c.app (op ⊤) :
                (X.toLocallyRingedSpace.restrict U.isOpenEmbedding).presheaf.obj (op ⊤) ⟶
                  (Spf A).presheaf.obj (op ⊤))) ≫
              (m.c.app (op ⊤) : (Spf A).presheaf.obj (op ⊤) ⟶
                (Spf (AdicRing.CompletedAway A (a x))).presheaf.obj (op ⊤)) ≫
              (Spf.topSectionsIso (AdicRing.CompletedAway A (a x))).hom) := by
          simp only [meTop, LocallyRingedSpace.comp_c_app, unop_op, Opens.map_top,
            Category.assoc]; rfl
      _ = fLW ≫ X.presheaf.map (homOfLE hUW).op ≫
            CommRingCat.ofHom (algebraMap A (AdicRing.CompletedAway A (a x))) :=
          congrArg (fLW ≫ X.presheaf.map (homOfLE hUW).op ≫ ·)
            ((congrArg (· ≫ _) he_inv).trans hm1)
  have hbasic : CommRingCat.ofHom (algebraMap A (AdicRing.CompletedAway A (a x))) =
      (Spf.topSectionsIso A).inv ≫
        (Spf A).presheaf.map (homOfLE (le_top : Spf.basicOpen (a x) ≤ ⊤)).op ≫
        (Spf.basicOpenSectionsIso hIA hIAfg (a x)).hom :=
    ((Iso.comp_inv_eq _).mp (Spf.algebraMap_comp_basicOpenSectionsIso_inv (a x))).trans
      (Category.assoc _ _ _)
  exact ConcreteCategory.congr_hom (hmid.trans (congrArg (_ ≫ _ ≫ ·) hbasic)) s

end SpecialCasesAndOpenTopology

end TauCeti.FormalScheme
