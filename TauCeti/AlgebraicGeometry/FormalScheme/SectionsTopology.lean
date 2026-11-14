/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.FormalScheme.Basic
public import TauCeti.AlgebraicGeometry.FormalScheme.Spf.HomEquiv
public import TauCeti.Geometry.RingedSpace.LocallyRingedSpace.Restrict
public import Mathlib.AlgebraicGeometry.AffineScheme

import TauCeti.Topology.Discrete

/-!
# Canonical section topologies on formal schemes

Let `X` be a formal scheme of finite ideal type and `U ⊆ X` an affine formal open. Choosing an
affine formal chart `e : X|_U ≅ Spf B` identifies `Γ(X, U)` with `B` as a commutative ring via
`chartSectionsIso`. Because every isomorphism `Spf B₁ ≅ Spf B₂` of locally ringed spaces induces a
topological ring isomorphism `B₂ ≃+* B₁` (`TauCeti.FormalScheme.Spf.isHomeomorph_isoToRingEquiv`),
the topology on `Γ(X, U)` pulled back from `B` is independent of the chosen chart
(EGA I, Ch. I, 10.4.5).

Equipped with `X.sectionsTopology U hU`, the ring `Γ(X, U)` is a complete separated adic ring of
finite ideal type (`sectionsTopology_isAdicRing`), and `X.restrict U` is canonically isomorphic to
`ofSpf Γ(X, U)` (`IsAffineOpen.isoSpf`). Topologically nilpotent elements of `Γ(X, U)` are precisely
the sections vanishing in every residue field on `U`, so any finitely generated ideal of `Γ(X, U)`
whose radical is cut out by residue vanishing on `U` is an ideal of definition
(`sectionsTopology_eq_adic`). Consequently, every morphism `f : X ⟶ Y` of formal schemes induces
continuous ring homomorphisms between affine section rings (`sectionMap_continuous`).

For an arbitrary open `W ⊆ X`, `X.openSectionsTopology W` equips `Γ(X, W)` with the initial topology
of the restrictions to affine formal opens `U ≤ W`, recovering `X.sectionsTopology W hW` when `W` is
affine.

## Main definitions

* `TauCeti.FormalScheme.chartSectionsIso`: the ring isomorphism `Γ(X, U) ≅ B` attached to an affine
  chart `X|_U ≅ Spf B`.
* `TauCeti.FormalScheme.sectionsTopology`: the chart-independent adic topology on `Γ(X, U)` for an
  affine formal open `U ⊆ X`.
* `TauCeti.FormalScheme.IsAffineOpen.isoSpf`: the canonical isomorphism
  `X.restrict U ≅ ofSpf Γ(X, U)` for an affine formal open `U ⊆ X`.
* `TauCeti.FormalScheme.openSectionsTopology`: the projective-limit topology on `Γ(X, W)` induced by
  restrictions to affine formal opens `U ≤ W`.

## Main results

* `TauCeti.FormalScheme.sectionsTopology_eq_induced`,
  `TauCeti.FormalScheme.isHomeomorph_chartSectionsIso`: `sectionsTopology` is induced by any affine
  chart and makes `chartSectionsIso` a homeomorphism.
* `TauCeti.FormalScheme.sectionsTopology_isTopologicalRing`,
  `TauCeti.FormalScheme.sectionsTopology_isAdicRing`: `(Γ(X, U), sectionsTopology)` is an adic ring
  of finite ideal type.
* `TauCeti.FormalScheme.sectionsTopology_eq_adic`: a finitely generated ideal of `Γ(X, U)` whose
  radical consists of sections vanishing in every residue field on `U` defines `sectionsTopology`.
* `TauCeti.FormalScheme.sectionMap_continuous`: morphisms of formal schemes induce continuous maps
  between affine section rings.
* `TauCeti.FormalScheme.sectionsTopology_ofScheme`: every affine open of an ordinary scheme `X` is
  an affine formal open of `ofScheme.obj X` with discrete `sectionsTopology`.

## References

* A. Grothendieck and J. Dieudonné, *Éléments de géométrie algébrique I*, Ch. I, 10.4.5–10.4.6.
* [Stacks Project, Tag 0AHY](https://stacks.math.columbia.edu/tag/0AHY).
-/

public section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry

universe u

namespace TauCeti.FormalScheme

section ChartTopology

/-- For any affine formal chart `e : X|_U ≅ Spf B`, the induced ring isomorphism `Γ(X, U) ≅ B`. -/
noncomputable def chartSectionsIso (X : FormalScheme.{u}) (U : Opens X) {B : Type u} [CommRing B]
    [TopologicalSpace B] [IsTopologicalRing B] [IsAdicRing B]
    (e : X.toLocallyRingedSpace.restrict U.isOpenEmbedding ≅ Spf B) :
    X.presheaf.obj (op U) ≅ CommRingCat.of B :=
  X.toLocallyRingedSpace.restrictTopSectionsIso U ≪≫
    (LocallyRingedSpace.Γ.mapIso e.symm.op :
      (X.toLocallyRingedSpace.restrict U.isOpenEmbedding).presheaf.obj (op ⊤) ≅
        (Spf B).presheaf.obj (op ⊤)) ≪≫
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

/-- Helper: evaluate `Spf.sectionsHom g` on an element `a : A` via `Spf.topSectionsIso`. -/
private theorem sectionsHom_apply {A B : Type u} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [IsAdicRing A] [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
    [IsAdicRing B] (g : Spf B ⟶ Spf A) (a : A) :
    Spf.sectionsHom g a =
      (Spf.topSectionsIso B).hom (g.c.app (op ⊤) ((Spf.topSectionsIso A).inv a)) := by
  have h := ConcreteCategory.congr_hom (Spf.globalSectionsIso_inv_comp_c_app_top g) a
  have hinv := ConcreteCategory.congr_hom (Spf.topSectionsIso B).inv_hom_id (Spf.sectionsHom g a)
  exact hinv.symm.trans (congrArg (Spf.topSectionsIso B).hom h).symm

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
  refine (cancel_epi (chartSectionsIso X U e₁).inv).mp ?_
  rw [Iso.inv_hom_id_assoc]
  ext b
  have hsec := sectionsHom_apply (e₂.symm ≪≫ e₁).hom b
  have hcomp : (e₂.symm ≪≫ e₁).hom.c.app (op ⊤) ((Spf.topSectionsIso B₁).inv b) =
      e₂.inv.c.app (op ⊤) (e₁.hom.c.app (op ⊤) ((Spf.topSectionsIso B₁).inv b)) := rfl
  have hmid := ConcreteCategory.congr_hom
    (X.toLocallyRingedSpace.restrictTopSectionsIso U).inv_hom_id
    (e₁.hom.c.app (op ⊤) ((Spf.topSectionsIso B₁).inv b))
  simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply,
    Spf.isoToRingEquiv_toRingHom]
  rw [hsec, hcomp]
  exact (congrArg (fun t ↦ (Spf.topSectionsIso B₂).hom (e₂.inv.c.app (op ⊤) t)) hmid.symm).trans
    rfl

/-- Two affine formal charts on `U` induce the same topology on `Γ(X, U)`. -/
private theorem induced_chartSectionsIso_eq (X : FormalScheme.{u}) (U : Opens X)
    {B₁ B₂ : Type u} [CommRing B₁] [t₁ : TopologicalSpace B₁] [IsTopologicalRing B₁]
    [IsAdicRing B₁] [CommRing B₂] [t₂ : TopologicalSpace B₂] [IsTopologicalRing B₂]
    [IsAdicRing B₂]
    (e₁ : X.toLocallyRingedSpace.restrict U.isOpenEmbedding ≅ Spf B₁)
    (e₂ : X.toLocallyRingedSpace.restrict U.isOpenEmbedding ≅ Spf B₂) :
    TopologicalSpace.induced (chartSectionsIso X U e₁).hom t₁ =
      TopologicalSpace.induced (chartSectionsIso X U e₂).hom t₂ := by
  have hhom := Spf.isHomeomorph_isoToRingEquiv (e₂.symm ≪≫ e₁)
  have hfun : ((chartSectionsIso X U e₂).hom : X.presheaf.obj (op U) → B₂) =
      Spf.isoToRingEquiv (e₂.symm ≪≫ e₁) ∘ (chartSectionsIso X U e₁).hom := by
    ext s
    exact (ConcreteCategory.congr_hom (chartSectionsIso_hom_comp_isoToRingEquiv X U e₁ e₂) s).symm
  rw [hfun, ← induced_compose, ← hhom.isInducing.eq_induced]

/-- The canonical adic topology on the ring of sections `Γ(X, U)` over an affine formal open
`U ⊆ X`, pulled back from the coordinate ring of an affine formal chart `X|_U ≅ Spf B`
(EGA I, Ch. I, 10.4.5). By `sectionsTopology_eq_induced`, this topology does not depend on the
chosen chart. -/
@[instance_reducible]
noncomputable def sectionsTopology (X : FormalScheme.{u}) (U : Opens X) (hU : X.IsAffineOpen U) :
    TopologicalSpace (X.presheaf.obj (op U)) :=
  let h := (X.isAffineOpen_iff U).mp hU
  let B := h.choose
  let _ : CommRing B := h.choose_spec.choose
  let tB : TopologicalSpace B := h.choose_spec.choose_spec.choose
  let _ : IsTopologicalRing B := h.choose_spec.choose_spec.choose_spec.choose
  let _ : IsAdicRing B := h.choose_spec.choose_spec.choose_spec.choose_spec.choose
  let e := h.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.some
  TopologicalSpace.induced (chartSectionsIso X U e).hom tB

/-- `X.sectionsTopology U hU` is the topology induced along `chartSectionsIso X U e` for every
affine formal chart `e : X|_U ≅ Spf B`. -/
theorem sectionsTopology_eq_induced (X : FormalScheme.{u}) (U : Opens X) (hU : X.IsAffineOpen U)
    {B : Type u} [CommRing B] [tB : TopologicalSpace B] [IsTopologicalRing B] [IsAdicRing B]
    (e : X.toLocallyRingedSpace.restrict U.isOpenEmbedding ≅ Spf B) :
    X.sectionsTopology U hU = TopologicalSpace.induced (chartSectionsIso X U e).hom tB := by
  let h := (X.isAffineOpen_iff U).mp hU
  let B₀ := h.choose
  let _ : CommRing B₀ := h.choose_spec.choose
  let _ : TopologicalSpace B₀ := h.choose_spec.choose_spec.choose
  let _ : IsTopologicalRing B₀ := h.choose_spec.choose_spec.choose_spec.choose
  let _ : IsAdicRing B₀ := h.choose_spec.choose_spec.choose_spec.choose_spec.choose
  let e₀ := h.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.some
  exact induced_chartSectionsIso_eq X U e₀ e

/-- For every affine formal chart `e : X|_U ≅ Spf B`, `chartSectionsIso X U e` is a homeomorphism
from `(Γ(X, U), X.sectionsTopology U hU)` onto `B`. -/
theorem isHomeomorph_chartSectionsIso (X : FormalScheme.{u}) (U : Opens X) (hU : X.IsAffineOpen U)
    {B : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsAdicRing B]
    (e : X.toLocallyRingedSpace.restrict U.isOpenEmbedding ≅ Spf B) :
    @IsHomeomorph _ _ (X.sectionsTopology U hU) ‹TopologicalSpace B›
      (chartSectionsIso X U e).hom := by
  let _ := X.sectionsTopology U hU
  let φ := (chartSectionsIso X U e).commRingCatIsoToRingEquiv.toEquiv
  exact (φ.toHomeomorphOfIsInducing ⟨sectionsTopology_eq_induced X U hU e⟩).isHomeomorph

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
  have he : Topology.IsInducing φ := ⟨sectionsTopology_eq_induced X U hU e⟩
  obtain ⟨I, hIfg, hIadic, hIcomp⟩ := IsAdicRing.exists_isAdic (A := B)
  exact ⟨⟨I.map φ.symm.toRingHom, hIfg.map φ.symm.toRingHom,
    (Ideal.map_symm φ).symm ▸ hIadic.comap φ he,
    (IsAdicComplete.congr_ringEquiv I φ.symm).mpr hIcomp⟩⟩

end ChartTopology

section ResidueCharacterization

/-- Evaluating a section `s ∈ Γ(X, U)` at `x ∈ U` vanishes if and only if the corresponding global
section of `X|_U` vanishes at `x`. -/
private theorem evaluation_eq_zero_iff_restrict_Γevaluation_eq_zero (X : FormalScheme.{u})
    (U : Opens X) (x : U) (s : X.presheaf.obj (op U)) :
    X.toLocallyRingedSpace.evaluation x s = 0 ↔
      (X.toLocallyRingedSpace.restrict U.isOpenEmbedding).Γevaluation x
        ((X.toLocallyRingedSpace.restrictTopSectionsIso U).hom s) = 0 := by
  let j := X.toLocallyRingedSpace.ofRestrict U.isOpenEmbedding
  let x' : (Opens.map j.base).obj U := ⟨x, x.2⟩
  have hnat := LocallyRingedSpace.evaluation_naturality_apply j x' s
  have hres : (X.toLocallyRingedSpace.restrict U.isOpenEmbedding).evaluation x' (j.c.app (op U) s) =
      (X.toLocallyRingedSpace.restrict U.isOpenEmbedding).Γevaluation x
        ((X.toLocallyRingedSpace.restrictTopSectionsIso U).hom s) := by
    have hidU : X.presheaf.map (homOfLE (le_refl U)).op = 𝟙 _ :=
      (congrArg X.presheaf.map (Quiver.Hom.unop_inj (Subsingleton.elim _ (𝟙 U)))).trans
        (X.presheaf.map_id _)
    have hsec := ConcreteCategory.congr_hom
      ((X.toLocallyRingedSpace.ofRestrict_c_app_le (le_refl U)).trans
        ((congrArg (· ≫ _) hidU).trans (Category.id_comp _))) s
    have hle : (⊤ : Opens (X.toLocallyRingedSpace.restrict U.isOpenEmbedding)) ≤
        (Opens.map j.base).obj U := fun y _ ↦ y.2
    have hgerm := TopCat.Presheaf.germ_res_apply
      (X.toLocallyRingedSpace.restrict U.isOpenEmbedding).presheaf (homOfLE hle) x trivial
      (j.c.app (op U) s)
    -- `Γevaluation` and `evaluation` are `residue` applied to the germs over `⊤` and `j ⁻¹' U`.
    exact (congrArg
      ((X.toLocallyRingedSpace.restrict U.isOpenEmbedding).residue x) hgerm).symm.trans
      (congrArg ((X.toLocallyRingedSpace.restrict U.isOpenEmbedding).Γevaluation x) hsec)
  exact ((LocallyRingedSpace.residueFieldMap j x'.1).hom.map_eq_zero_iff).symm.trans
    (congrArg (· = 0) (hnat.trans hres)).to_iff

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
  rw [hnilp, hIB.isTopologicallyNilpotent_iff_mem_radical]
  have hrad : φ s ∈ (IsAdicRing.ideal B).radical ↔
      ∀ p : Spf.carrier B, (Spf B).Γevaluation p ((Spf.topSectionsIso B).inv (φ s)) = 0 := by
    rw [Ideal.radical_eq_sInf, Ideal.mem_sInf]
    refine ⟨fun h p ↦ (Spf.Γevaluation_topSectionsIso_inv_eq_zero_iff p (φ s)).mpr
      (h ⟨(Spf.mem_carrier_iff_le hIB).mp p.2, p.1.isPrime⟩),
      fun h q hq ↦ (Spf.Γevaluation_topSectionsIso_inv_eq_zero_iff
        ⟨⟨q, hq.2⟩, (Spf.mem_carrier_iff_le hIB).mpr hq.1⟩ (φ s)).mp (h _)⟩
  rw [hrad]
  have hsec₁ : e.hom.c.app (op ⊤) ((Spf.topSectionsIso B).inv (φ s)) =
      (X.toLocallyRingedSpace.restrictTopSectionsIso U).hom s := by
    have h := ConcreteCategory.congr_hom
      ((LocallyRingedSpace.Γ.map_comp e.inv.op e.hom.op).symm.trans <|
        (congrArg LocallyRingedSpace.Γ.map (congrArg Quiver.Hom.op e.hom_inv_id)).trans
          (LocallyRingedSpace.Γ.map_id _))
      ((X.toLocallyRingedSpace.restrictTopSectionsIso U).hom s)
    exact (congrArg (e.hom.c.app (op ⊤))
      (ConcreteCategory.congr_hom (Spf.topSectionsIso B).hom_inv_id _)).trans h
  have hsec₂ : (Spf.topSectionsIso B).inv (φ s) =
      e.inv.c.app (op ⊤) ((X.toLocallyRingedSpace.restrictTopSectionsIso U).hom s) :=
    ConcreteCategory.congr_hom (Spf.topSectionsIso B).hom_inv_id
      (e.inv.c.app (op ⊤) ((X.toLocallyRingedSpace.restrictTopSectionsIso U).hom s))
  refine ⟨fun h x ↦ ?_, fun h p ↦ ?_⟩
  · rw [evaluation_eq_zero_iff_restrict_Γevaluation_eq_zero, ← hsec₁,
      ← LocallyRingedSpace.Γevaluation_naturality_apply e.hom x, h (e.hom.base x), map_zero]
  · let p' : Spf B := p
    have hx := (evaluation_eq_zero_iff_restrict_Γevaluation_eq_zero X U (e.inv.base p') s).mp
      (h (e.inv.base p'))
    exact (congrArg ((Spf B).Γevaluation p') hsec₂).trans <|
      (LocallyRingedSpace.Γevaluation_naturality_apply e.inv p' _).symm.trans <|
        (congrArg (LocallyRingedSpace.residueFieldMap e.inv p') hx).trans (map_zero _)

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
  refine hIadic.of_radical_eq hIfg hJfg ?_
  ext s
  exact hIadic.isTopologicallyNilpotent_iff_mem_radical.symm.trans <|
    (isTopologicallyNilpotent_iff_forall_evaluation_eq_zero X U hU s).trans (hJrad s).symm

end ResidueCharacterization

section CanonicalChart

/-- Every affine formal open `U ⊆ X` is canonically isomorphic as a formal scheme to the formal
spectrum of `(Γ(X, U), X.sectionsTopology U hU)` (EGA I, Ch. I, 10.4.5). -/
noncomputable def IsAffineOpen.isoSpf {X : FormalScheme.{u}} {U : Opens X}
    (hU : X.IsAffineOpen U) :
    X.restrict U ≅
      @ofSpf (X.presheaf.obj (op U)) _ (X.sectionsTopology U hU)
        (X.sectionsTopology_isTopologicalRing U hU) (X.sectionsTopology_isAdicRing U hU) :=
  let h := (X.isAffineOpen_iff U).mp hU
  let B := h.choose
  let _ : CommRing B := h.choose_spec.choose
  let _ : TopologicalSpace B := h.choose_spec.choose_spec.choose
  let _ : IsTopologicalRing B := h.choose_spec.choose_spec.choose_spec.choose
  let _ : IsAdicRing B := h.choose_spec.choose_spec.choose_spec.choose_spec.choose
  let e := h.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.some
  let _ := X.sectionsTopology U hU
  let _ := X.sectionsTopology_isTopologicalRing U hU
  let _ := X.sectionsTopology_isAdicRing U hU
  let φ : (X.presheaf.obj (op U) : Type u) ≃+* B :=
    (chartSectionsIso X U e).commRingCatIsoToRingEquiv
  let hφ := φ.toEquiv.isHomeomorph_iff.mp (isHomeomorph_chartSectionsIso X U hU e)
  InducedCategory.isoMk (e ≪≫ Spf.mapIso φ hφ.1 hφ.2)

/-- On global sections, `hU.isoSpf.hom` identifies `Spf.topSectionsIso` with
`X.toLocallyRingedSpace.restrictTopSectionsIso U`, independently of any chosen chart. -/
@[reassoc (attr := simp)]
theorem topSectionsIso_inv_isoSpf_hom_c_app_top {X : FormalScheme.{u}} {U : Opens X}
    (hU : X.IsAffineOpen U) :
    (@Spf.topSectionsIso (X.presheaf.obj (op U)) _ (X.sectionsTopology U hU)
        (X.sectionsTopology_isTopologicalRing U hU)
        (X.sectionsTopology_isAdicRing U hU)).inv ≫
      ((forgetToLocallyRingedSpace.map hU.isoSpf.hom).c.app (op ⊤) :
        (@Spf (X.presheaf.obj (op U)) _ (X.sectionsTopology U hU)
          (X.sectionsTopology_isTopologicalRing U hU)
          (X.sectionsTopology_isAdicRing U hU)).presheaf.obj (op ⊤) ⟶
          (X.toLocallyRingedSpace.restrict U.isOpenEmbedding).presheaf.obj (op ⊤)) =
      (X.toLocallyRingedSpace.restrictTopSectionsIso U).hom := by
  let h := (X.isAffineOpen_iff U).mp hU
  let B := h.choose
  let _ : CommRing B := h.choose_spec.choose
  let _ : TopologicalSpace B := h.choose_spec.choose_spec.choose
  let _ : IsTopologicalRing B := h.choose_spec.choose_spec.choose_spec.choose
  let _ : IsAdicRing B := h.choose_spec.choose_spec.choose_spec.choose_spec.choose
  let e := h.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.some
  let _ := X.sectionsTopology U hU
  have := X.sectionsTopology_isTopologicalRing U hU
  have := X.sectionsTopology_isAdicRing U hU
  let φ : (X.presheaf.obj (op U) : Type u) ≃+* B :=
    (chartSectionsIso X U e).commRingCatIsoToRingEquiv
  let hφ := φ.toEquiv.isHomeomorph_iff.mp (isHomeomorph_chartSectionsIso X U hU e)
  let m := Spf.map φ.toRingHom hφ.1
  have hiso_hom : forgetToLocallyRingedSpace.map hU.isoSpf.hom = e.hom ≫ m :=
    congrArg (e.hom ≫ ·) (Spf.mapIso_hom φ hφ.1 hφ.2)
  have hm := (Spf.globalSectionsIso_inv_comp_c_app_top m).trans
    (congrArg (fun ψ ↦ CommRingCat.ofHom ψ ≫ (Spf.topSectionsIso B).inv)
      (Spf.sectionsHom_map φ.toRingHom hφ.1))
  have he_inv_hom : ∀ t, e.hom.c.app (op ⊤) (e.inv.c.app (op ⊤) t) = t := fun t ↦
    ConcreteCategory.congr_hom
      ((LocallyRingedSpace.Γ.map_comp e.inv.op e.hom.op).symm.trans <|
        (congrArg LocallyRingedSpace.Γ.map (congrArg Quiver.Hom.op e.hom_inv_id)).trans
          (LocallyRingedSpace.Γ.map_id _)) t
  ext s
  have hc_eval : (forgetToLocallyRingedSpace.map hU.isoSpf.hom).c.app (op ⊤)
        ((Spf.topSectionsIso (X.presheaf.obj (op U))).inv s) =
      e.hom.c.app (op ⊤) (m.c.app (op ⊤)
        ((Spf.topSectionsIso (X.presheaf.obj (op U))).inv s)) :=
    ConcreteCategory.congr_hom
      ((congrArg LocallyRingedSpace.Γ.map (congrArg Quiver.Hom.op hiso_hom)).trans
        (LocallyRingedSpace.Γ.map_comp m.op e.hom.op)) _
  have hm_app := ConcreteCategory.congr_hom hm s
  have hmid := ConcreteCategory.congr_hom (Spf.topSectionsIso B).hom_inv_id
    (e.inv.c.app (op ⊤) ((X.toLocallyRingedSpace.restrictTopSectionsIso U).hom s))
  exact (hc_eval.trans (congrArg (e.hom.c.app (op ⊤)) hm_app)).trans
    ((congrArg (e.hom.c.app (op ⊤)) hmid).trans (he_inv_hom _))

/-- Dual form of `topSectionsIso_inv_isoSpf_hom_c_app_top` for `hU.isoSpf.inv`. -/
@[reassoc (attr := simp)]
theorem isoSpf_inv_c_app_top_comp_topSectionsIso_hom {X : FormalScheme.{u}} {U : Opens X}
    (hU : X.IsAffineOpen U) :
    ((forgetToLocallyRingedSpace.map hU.isoSpf.inv).c.app (op ⊤) :
        (X.toLocallyRingedSpace.restrict U.isOpenEmbedding).presheaf.obj (op ⊤) ⟶
          (@Spf (X.presheaf.obj (op U)) _ (X.sectionsTopology U hU)
            (X.sectionsTopology_isTopologicalRing U hU)
            (X.sectionsTopology_isAdicRing U hU)).presheaf.obj (op ⊤)) ≫
      (@Spf.topSectionsIso (X.presheaf.obj (op U)) _ (X.sectionsTopology U hU)
        (X.sectionsTopology_isTopologicalRing U hU)
        (X.sectionsTopology_isAdicRing U hU)).hom =
      (X.toLocallyRingedSpace.restrictTopSectionsIso U).inv := by
  let topU := @Spf.topSectionsIso (X.presheaf.obj (op U)) _ (X.sectionsTopology U hU)
    (X.sectionsTopology_isTopologicalRing U hU) (X.sectionsTopology_isAdicRing U hU)
  let fHom := forgetToLocallyRingedSpace.map hU.isoSpf.hom
  let fInv := forgetToLocallyRingedSpace.map hU.isoSpf.inv
  have hf_inv_hom : fInv ≫ fHom = 𝟙 _ :=
    (forgetToLocallyRingedSpace.map_comp hU.isoSpf.inv hU.isoSpf.hom).symm.trans <|
      (congrArg forgetToLocallyRingedSpace.map hU.isoSpf.inv_hom_id).trans
        (forgetToLocallyRingedSpace.map_id _)
  have hhom_inv : ∀ t, fInv.c.app (op ⊤) (fHom.c.app (op ⊤) t) = t := fun t ↦
    ConcreteCategory.congr_hom
      ((LocallyRingedSpace.Γ.map_comp fHom.op fInv.op).symm.trans <|
        (congrArg LocallyRingedSpace.Γ.map (congrArg Quiver.Hom.op hf_inv_hom)).trans
          (LocallyRingedSpace.Γ.map_id _)) t
  refine (cancel_epi (X.toLocallyRingedSpace.restrictTopSectionsIso U).hom).mp ?_
  ext s
  have htop := ConcreteCategory.congr_hom (topSectionsIso_inv_isoSpf_hom_c_app_top hU).symm s
  have hid₁ := ConcreteCategory.congr_hom topU.inv_hom_id s
  have hid₂ := ConcreteCategory.congr_hom
    (X.toLocallyRingedSpace.restrictTopSectionsIso U).hom_inv_id s
  exact (congrArg (fun t ↦ topU.hom (fInv.c.app (op ⊤) t)) htop).trans <|
    (congrArg topU.hom (hhom_inv (topU.inv s))).trans (hid₁.trans hid₂.symm)

/-- If `fUV : X|_U ⟶ Y|_V` commutes with the open-subspace inclusions into `X` and `Y` along
`f : X ⟶ Y`, then under `restrictTopSectionsIso` its global-section map is `f.c.app (op V)`
followed by restriction to `U`. -/
private theorem restrictTopSectionsIso_hom_c_app_top_of_fac {X Y : LocallyRingedSpace.{u}}
    (f : X ⟶ Y) {V : Opens Y} {U : Opens X} (hUV : U ≤ (Opens.map f.base).obj V)
    (fUV : X.restrict U.isOpenEmbedding ⟶ Y.restrict V.isOpenEmbedding)
    (hfac : fUV ≫ Y.ofRestrict V.isOpenEmbedding = X.ofRestrict U.isOpenEmbedding ≫ f)
    (s : Y.presheaf.obj (op V)) :
    fUV.c.app (op ⊤) ((Y.restrictTopSectionsIso V).hom s) =
      (X.restrictTopSectionsIso U).hom (X.presheaf.map (homOfLE hUV).op (f.c.app (op V) s)) := by
  let jU := X.ofRestrict U.isOpenEmbedding
  let jV := Y.ofRestrict V.isOpenEmbedding
  have hleU₁ : (⊤ : Opens (X.restrict U.isOpenEmbedding)) ≤
      (Opens.map (fUV ≫ jV).base).obj V := by
    rw [hfac]
    exact fun x _ ↦ hUV x.2
  have hleU₂ : (⊤ : Opens (X.restrict U.isOpenEmbedding)) ≤
      (Opens.map (jU ≫ f).base).obj V := fun x _ ↦ hUV x.2
  have hleV : (⊤ : Opens (Y.restrict V.isOpenEmbedding)) ≤
      (Opens.map jV.base).obj V := fun y _ ↦ y.2
  have hlhs : (X.restrict U.isOpenEmbedding).presheaf.map (homOfLE hleU₁).op
        ((fUV ≫ jV).c.app (op V) s) =
      fUV.c.app (op ⊤) ((Y.restrictTopSectionsIso V).hom s) := by
    have hnat := ConcreteCategory.congr_hom (fUV.c.naturality (homOfLE hleV).op).symm
      (jV.c.app (op V) s)
    have hidV : Y.presheaf.map (homOfLE (le_refl V)).op = 𝟙 _ :=
      (congrArg Y.presheaf.map (Quiver.Hom.unop_inj (Subsingleton.elim _ (𝟙 V)))).trans
        (Y.presheaf.map_id _)
    have hjV := ConcreteCategory.congr_hom
      ((Y.ofRestrict_c_app_le (le_refl V)).trans
        ((congrArg (· ≫ _) hidV).trans (Category.id_comp _))) s
    have hmap : (X.restrict U.isOpenEmbedding).presheaf.map (homOfLE hleU₁).op =
        ((TopCat.Presheaf.pushforward CommRingCat fUV.base).obj
          (X.restrict U.isOpenEmbedding).presheaf).map (homOfLE hleV).op :=
      congrArg (X.restrict U.isOpenEmbedding).presheaf.map
        (Quiver.Hom.unop_inj (Subsingleton.elim _ _))
    exact (ConcreteCategory.congr_hom hmap _).trans
      (hnat.trans (congrArg (fUV.c.app (op ⊤)) hjV))
  have hrhs : (X.restrict U.isOpenEmbedding).presheaf.map (homOfLE hleU₂).op
        ((jU ≫ f).c.app (op V) s) =
      (X.restrictTopSectionsIso U).hom (X.presheaf.map (homOfLE hUV).op (f.c.app (op V) s)) := by
    have hjU := ConcreteCategory.congr_hom
      (X.ofRestrict_c_app_le (W := (Opens.map f.base).obj V) hUV) (f.c.app (op V) s)
    have hmap : (X.restrict U.isOpenEmbedding).presheaf.map (homOfLE hleU₂).op =
        (X.restrict U.isOpenEmbedding).presheaf.map
          (homOfLE (fun x _ ↦ hUV x.2 :
            (⊤ : Opens _) ≤ (Opens.map jU.base).obj ((Opens.map f.base).obj V))).op :=
      congrArg (X.restrict U.isOpenEmbedding).presheaf.map
        (Quiver.Hom.unop_inj (Subsingleton.elim _ _))
    exact (ConcreteCategory.congr_hom hmap _).trans hjU
  have hmid_gen {k₁ k₂ : X.restrict U.isOpenEmbedding ⟶ Y} (hk : k₁ = k₂)
      (h₁ : (⊤ : Opens (X.restrict U.isOpenEmbedding)) ≤ (Opens.map k₁.base).obj V)
      (h₂ : (⊤ : Opens (X.restrict U.isOpenEmbedding)) ≤ (Opens.map k₂.base).obj V) :
      (X.restrict U.isOpenEmbedding).presheaf.map (homOfLE h₁).op (k₁.c.app (op V) s) =
        (X.restrict U.isOpenEmbedding).presheaf.map (homOfLE h₂).op (k₂.c.app (op V) s) := by
    subst hk
    rfl
  exact hlhs.symm.trans ((hmid_gen hfac hleU₁ hleU₂).trans hrhs)

/-- **Automatic continuity on affine opens** (EGA I, Ch. I, 10.4.6): for any morphism of formal
schemes `f : X ⟶ Y` and affine formal opens `U ⊆ X`, `V ⊆ Y` with `U ≤ f ⁻¹' V`, the induced
homomorphism `Γ(Y, V) →+* Γ(X, U)` is continuous from `Y.sectionsTopology V hV` to
`X.sectionsTopology U hU`. -/
theorem sectionMap_continuous {X Y : FormalScheme.{u}} (f : X ⟶ Y) {V : Opens Y}
    (hV : Y.IsAffineOpen V) {U : Opens X} (hU : X.IsAffineOpen U)
    (hUV : U ≤ (Opens.map (forgetToLocallyRingedSpace.map f).base).obj V) :
    @Continuous _ _ (Y.sectionsTopology V hV) (X.sectionsTopology U hU)
      ((forgetToLocallyRingedSpace.map f).c.app (op V) ≫ X.presheaf.map (homOfLE hUV).op) := by
  let jU := X.toLocallyRingedSpace.ofRestrict U.isOpenEmbedding
  let jV := Y.toLocallyRingedSpace.ofRestrict V.isOpenEmbedding
  have hsub : Set.range (jU ≫ forgetToLocallyRingedSpace.map f).base ⊆ Set.range jV.base := by
    rintro _ ⟨x, rfl⟩
    exact ⟨⟨(forgetToLocallyRingedSpace.map f).base x.1, hUV x.2⟩, rfl⟩
  let fUV := LocallyRingedSpace.IsOpenImmersion.lift jV (jU ≫ forgetToLocallyRingedSpace.map f) hsub
  have hfac := LocallyRingedSpace.IsOpenImmersion.lift_fac jV
    (jU ≫ forgetToLocallyRingedSpace.map f) hsub
  let tU := X.sectionsTopology U hU
  let trU := X.sectionsTopology_isTopologicalRing U hU
  let adU := X.sectionsTopology_isAdicRing U hU
  let tV := Y.sectionsTopology V hV
  let trV := Y.sectionsTopology_isTopologicalRing V hV
  let adV := Y.sectionsTopology_isAdicRing V hV
  let g : @Spf (X.presheaf.obj (op U)) _ tU trU adU ⟶
      @Spf (Y.presheaf.obj (op V)) _ tV trV adV :=
    forgetToLocallyRingedSpace.map hU.isoSpf.inv ≫ fUV ≫
      forgetToLocallyRingedSpace.map hV.isoSpf.hom
  refine (@Spf.continuous_sectionsHom _ _ _ tV trV adV _ tU trU adU g).congr fun s ↦ ?_
  have hsec := @sectionsHom_apply _ _ _ tV trV adV _ tU trU adU g s
  have hV_app := ConcreteCategory.congr_hom (topSectionsIso_inv_isoSpf_hom_c_app_top hV) s
  have hU_app := ConcreteCategory.congr_hom (isoSpf_inv_c_app_top_comp_topSectionsIso_hom hU)
  have heq := restrictTopSectionsIso_hom_c_app_top_of_fac (forgetToLocallyRingedSpace.map f)
    hUV fUV hfac s
  have hc_eval : g.c.app (op ⊤)
        ((@Spf.topSectionsIso (Y.presheaf.obj (op V)) _ tV trV adV).inv s) =
      (forgetToLocallyRingedSpace.map hU.isoSpf.inv).c.app (op ⊤)
        (fUV.c.app (op ⊤) ((Y.toLocallyRingedSpace.restrictTopSectionsIso V).hom s)) :=
    congrArg (fun t ↦ (forgetToLocallyRingedSpace.map hU.isoSpf.inv).c.app (op ⊤)
      (fUV.c.app (op ⊤) t)) hV_app
  refine hsec.trans <| (congrArg _ hc_eval).trans <| (hU_app _).trans <|
    (congrArg (X.toLocallyRingedSpace.restrictTopSectionsIso U).inv heq).trans ?_
  exact ConcreteCategory.congr_hom (X.toLocallyRingedSpace.restrictTopSectionsIso U).hom_inv_id _

end CanonicalChart

section SpecialCasesAndOpenTopology

/-- On `ofSpf A`, `Spf.topSectionsIso A` is a homeomorphism from
`((ofSpf A).presheaf.obj (op ⊤), (ofSpf A).sectionsTopology ⊤ _)` onto `A`. -/
theorem isHomeomorph_topSectionsIso (A : Type u) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [IsAdicRing A] :
    @IsHomeomorph _ _ ((ofSpf A).sectionsTopology ⊤ (isAffineOpen_top_ofSpf A))
      ‹TopologicalSpace A› (Spf.topSectionsIso A).hom := by
  let eTop : (ofSpf A).toLocallyRingedSpace.restrict (⊤ : Opens (ofSpf A)).isOpenEmbedding ≅
      Spf A := (ofSpf A).toLocallyRingedSpace.restrictTopIso
  have hchart := isHomeomorph_chartSectionsIso (ofSpf A) ⊤ (isAffineOpen_top_ofSpf A) eTop
  suffices h : (chartSectionsIso (ofSpf A) ⊤ eTop).hom = (Spf.topSectionsIso A).hom from
    h ▸ hchart
  have hhom : (eTop.hom.c.app (op ⊤) :
        (ofSpf A).presheaf.obj (op ⊤) ⟶
          ((ofSpf A).toLocallyRingedSpace.restrict
            (⊤ : Opens (ofSpf A)).isOpenEmbedding).presheaf.obj (op ⊤)) =
      ((ofSpf A).toLocallyRingedSpace.restrictTopSectionsIso ⊤).hom := by
    have hle := (ofSpf A).toLocallyRingedSpace.ofRestrict_c_app_le
      (le_refl (⊤ : Opens (ofSpf A)))
    have hid₁ : (ofSpf A).presheaf.map (homOfLE (le_refl (⊤ : Opens (ofSpf A)))).op = 𝟙 _ :=
      (congrArg (ofSpf A).presheaf.map (Quiver.Hom.unop_inj (Subsingleton.elim _ (𝟙 _)))).trans
        ((ofSpf A).presheaf.map_id _)
    have hid₂ : ((ofSpf A).toLocallyRingedSpace.restrict
          (⊤ : Opens (ofSpf A)).isOpenEmbedding).presheaf.map
          (homOfLE (fun x _ ↦ trivial : (⊤ : Opens _) ≤
            (Opens.map ((ofSpf A).toLocallyRingedSpace.ofRestrict
              (⊤ : Opens (ofSpf A)).isOpenEmbedding).base).obj ⊤)).op =
        𝟙 _ :=
      (congrArg _ (Quiver.Hom.unop_inj (Subsingleton.elim _ (𝟙 _)))).trans
        (((ofSpf A).toLocallyRingedSpace.restrict
          (⊤ : Opens (ofSpf A)).isOpenEmbedding).presheaf.map_id _)
    exact (Category.comp_id _).symm.trans <|
      (congrArg _ hid₂.symm).trans <| hle.trans <|
        (congrArg (· ≫ _) hid₁).trans (Category.id_comp _)
  ext s
  have hinv : eTop.inv.c.app (op ⊤)
        (((ofSpf A).toLocallyRingedSpace.restrictTopSectionsIso ⊤).hom s) = s := by
    have h := congrArg (eTop.inv.c.app (op ⊤)) (ConcreteCategory.congr_hom hhom.symm s)
    exact h.trans <| ConcreteCategory.congr_hom
      ((LocallyRingedSpace.Γ.map_comp eTop.hom.op eTop.inv.op).symm.trans <|
        (congrArg LocallyRingedSpace.Γ.map (congrArg Quiver.Hom.op eTop.inv_hom_id)).trans
          (LocallyRingedSpace.Γ.map_id _)) s
  exact (chartSectionsIso_hom_apply (ofSpf A) ⊤ eTop s).trans
    (congrArg (Spf.topSectionsIso A).hom hinv)

/-- On `ofSpf A`, `(ofSpf A).sectionsTopology ⊤ _` agrees with
`Spf.quotientSectionsTopology _ ⊤`. -/
theorem sectionsTopology_ofSpf_top (A : Type u) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [IsAdicRing A] :
    (ofSpf A).sectionsTopology ⊤ (isAffineOpen_top_ofSpf A) =
      Spf.quotientSectionsTopology (IsAdicRing.ideal_spec A).2.1 ⊤ := by
  let t₁ := (ofSpf A).sectionsTopology ⊤ (isAffineOpen_top_ofSpf A)
  let t₂ := Spf.quotientSectionsTopology (IsAdicRing.ideal_spec A).2.1 ⊤
  have h₁ := (@IsHomeomorph.isInducing _ _ t₁ _ _ (isHomeomorph_topSectionsIso A)).eq_induced
  have h₂ := (@IsHomeomorph.isInducing _ _ t₂ _ _ (Spf.isHomeomorph_topSectionsIso A)).eq_induced
  exact h₁.trans h₂.symm

/-- Every affine open of an ordinary scheme `X` is an affine formal open of `ofScheme.obj X`. -/
theorem isAffineOpen_ofScheme {X : Scheme.{u}} {U : X.Opens}
    (hU : AlgebraicGeometry.IsAffineOpen U) :
    (ofScheme.obj X).IsAffineOpen U := by
  let R : Type u := X.presheaf.obj (op U)
  let _ : TopologicalSpace R := ⊥
  have : DiscreteTopology R := ⟨rfl⟩
  let e : (ofScheme.obj X).toLocallyRingedSpace.restrict U.isOpenEmbedding ≅ Spf R :=
    Scheme.forgetToLocallyRingedSpace.mapIso hU.isoSpec ≪≫ (Spf.discreteIsoSpec R).symm
  exact ((ofScheme.obj X).isAffineOpen_iff U).mpr ⟨R, inferInstance, ⊥, inferInstance,
    inferInstance, ⟨e⟩⟩

/-- Over any affine open `U` of an ordinary scheme `X`, `(ofScheme.obj X).sectionsTopology U _` is
the discrete topology. -/
theorem sectionsTopology_ofScheme {X : Scheme.{u}} {U : X.Opens}
    (hU : AlgebraicGeometry.IsAffineOpen U) :
    (ofScheme.obj X).sectionsTopology U (isAffineOpen_ofScheme hU) = ⊥ := by
  let R : Type u := X.presheaf.obj (op U)
  let _ : TopologicalSpace R := ⊥
  have : DiscreteTopology R := ⟨rfl⟩
  let e : (ofScheme.obj X).toLocallyRingedSpace.restrict U.isOpenEmbedding ≅ Spf R :=
    Scheme.forgetToLocallyRingedSpace.mapIso hU.isoSpec ≪≫ (Spf.discreteIsoSpec R).symm
  exact (sectionsTopology_eq_induced (ofScheme.obj X) U (isAffineOpen_ofScheme hU) e).trans
    (TauCeti.induced_bot_of_injective
      (ConcreteCategory.bijective_of_isIso (chartSectionsIso (ofScheme.obj X) U e).hom).injective)

/-- The projective-limit topology on `Γ(X, W)` for an arbitrary open `W ⊆ X`, defined as the
coarsest topology making the restriction map `Γ(X, W) → Γ(X, U)` continuous into
`X.sectionsTopology U hU` for every affine formal open `U ≤ W` (EGA I, Ch. I, 10.4.5). -/
@[instance_reducible]
noncomputable def openSectionsTopology (X : FormalScheme.{u}) (W : Opens X) :
    TopologicalSpace (X.presheaf.obj (op W)) :=
  ⨅ (U : Opens X) (hU : X.IsAffineOpen U) (hUW : U ≤ W),
    TopologicalSpace.induced (X.presheaf.map (homOfLE hUW).op) (X.sectionsTopology U hU)

/-- Continuity into `X.openSectionsTopology W` is tested on restrictions to affine formal opens
`U ≤ W`. -/
theorem continuous_iff_openSectionsTopology {T : Type*} [TopologicalSpace T] (X : FormalScheme.{u})
    (W : Opens X) (g : T → X.presheaf.obj (op W)) :
    @Continuous _ _ ‹TopologicalSpace T› (X.openSectionsTopology W) g ↔
      ∀ (U : Opens X) (hU : X.IsAffineOpen U) (hUW : U ≤ W),
        @Continuous _ _ ‹TopologicalSpace T› (X.sectionsTopology U hU)
          (X.presheaf.map (homOfLE hUW).op ∘ g) := by
  let _ := X.openSectionsTopology W
  simp only [continuous_iInf_rng, continuous_induced_rng]

/-- On an affine formal open `W ⊆ X`, `X.openSectionsTopology W` coincides with
`X.sectionsTopology W hW`. -/
theorem openSectionsTopology_eq_sectionsTopology (X : FormalScheme.{u}) (W : Opens X)
    (hW : X.IsAffineOpen W) :
    X.openSectionsTopology W = X.sectionsTopology W hW := by
  refine le_antisymm ?_ ?_
  · refine iInf_le_of_le W <| iInf_le_of_le hW <| iInf_le_of_le (le_refl W) ?_
    have hidW : X.presheaf.map (homOfLE (le_refl W)).op = 𝟙 _ :=
      (congrArg X.presheaf.map (Quiver.Hom.unop_inj (Subsingleton.elim _ (𝟙 W)))).trans
        (X.presheaf.map_id _)
    rw [hidW]
    exact le_of_eq (induced_id (t := X.sectionsTopology W hW))
  · refine le_iInf fun U ↦ le_iInf fun hU ↦ le_iInf fun hUW ↦ ?_
    let _ := X.sectionsTopology W hW
    let _ := X.sectionsTopology U hU
    have hcont := sectionMap_continuous (𝟙 X) hW hU hUW
    exact continuous_iff_le_induced.mp (hcont.congr fun _ ↦ rfl)

/-- Restriction maps `Γ(X, W₂) → Γ(X, W₁)` are continuous for `openSectionsTopology`. -/
theorem continuous_restrict_openSectionsTopology (X : FormalScheme.{u}) {W₁ W₂ : Opens X}
    (h : W₁ ≤ W₂) :
    @Continuous _ _ (X.openSectionsTopology W₂) (X.openSectionsTopology W₁)
      (X.presheaf.map (homOfLE h).op) := by
  let _ := X.openSectionsTopology W₂
  rw [continuous_iff_openSectionsTopology]
  intro U hU hUW₁
  have hcomp : ((X.presheaf.map (homOfLE hUW₁).op : _ → _) ∘ X.presheaf.map (homOfLE h).op) =
      X.presheaf.map (homOfLE (hUW₁.trans h)).op := by
    ext s
    exact ConcreteCategory.congr_hom (X.presheaf.map_comp (homOfLE h).op (homOfLE hUW₁).op).symm s
  rw [hcomp]
  exact (continuous_iff_openSectionsTopology X W₂ id).mp continuous_id U hU (hUW₁.trans h)

end SpecialCasesAndOpenTopology

end TauCeti.FormalScheme
