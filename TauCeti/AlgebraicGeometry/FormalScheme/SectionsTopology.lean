/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.FormalScheme.Basic
public import TauCeti.AlgebraicGeometry.FormalScheme.Spf.HomEquiv
public import TauCeti.Geometry.RingedSpace.LocallyRingedSpace.GlueMorphisms

import TauCeti.Geometry.RingedSpace.LocallyRingedSpace.Sections
import TauCeti.Topology.Algebra.Ring.Basic

/-!
# Topologies on rings of sections of a formal scheme

Every affine formal open `U` of a formal scheme `X` of finite ideal type admits a chart
`e : X|_U ≅ Spf A`, inducing `sectionsIsoOfIsoSpf e : Γ(U, O_X) ≅ A` and pulling back the adic
topology of `A` to the chart-independent topology `sectionsTopology X U hU` (via
`Spf.isHomeomorph_sectionsHom_of_iso`). For an arbitrary open `U`, `sheafSectionsTopology X U` is
the initial topology for restrictions `Γ(U, O_X) → Γ(W, O_X)` to affine formal opens `W ⊆ U`
(EGA I, Ch. 0, 3.8.1; Ch. I, 10.4.5), agreeing with `sectionsTopology` on affine formal opens and
with `Spf.quotientSectionsTopology` on `ofSpf A`.

## Main definitions

* `TauCeti.FormalScheme.sectionsIsoOfIsoSpf`: `Γ(U, O_X) ≅ A` induced by `X|_U ≅ Spf A`.
* `TauCeti.FormalScheme.sectionsTopology`: intrinsic adic topology on `Γ(U, O_X)` for affine `U`.
* `TauCeti.FormalScheme.sheafSectionsTopology`: initial topology on `Γ(U, O_X)` for arbitrary `U`.

## Main results

* `TauCeti.FormalScheme.isHomeomorph_sectionsIsoOfIsoSpf`,
  `TauCeti.FormalScheme.sectionsTopology_isTopologicalRing`,
  `TauCeti.FormalScheme.sectionsTopology_isAdicRing`,
  `TauCeti.FormalScheme.continuous_restrict_of_isAffineOpen`: chart independence and adic structure.
* `TauCeti.FormalScheme.sheafSectionsTopology_restrict`,
  `TauCeti.FormalScheme.sheafSectionsTopology_isTopologicalRing`,
  `TauCeti.FormalScheme.sheafSectionsTopology_eq_sectionsTopology`,
  `TauCeti.FormalScheme.sheafSectionsTopology_ofSpf`: sheaf topology properties and comparison.

## References

* A. Grothendieck and J. Dieudonné, *Éléments de géométrie algébrique I*, Ch. 0, 3.8.1 and
  Ch. I, 10.4.5.
* [Stacks Project, Tag 0AHY](https://stacks.math.columbia.edu/tag/0AHY).
-/

public section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry Topology

namespace TauCeti.FormalScheme

universe u

private noncomputable abbrev globalIso (A : Type u) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [IsAdicRing A] : (Spf A).presheaf.obj (op ⊤) ≅ CommRingCat.of A :=
  @Spf.globalSectionsIso A _ _ _ _ (IsAdicRing.ideal_spec A).2.2 (IsAdicRing.ideal_spec A).2.1

section ChartIsomorphism

/-- The ring isomorphism `Γ(U, O_X) ≅ A` induced by an affine formal chart `e : X|_U ≅ Spf A`. -/
noncomputable def sectionsIsoOfIsoSpf {X : FormalScheme.{u}} {U : Opens X}
    {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsAdicRing A]
    (e : X.toLocallyRingedSpace.restrict U.isOpenEmbedding ≅ Spf A) :
    X.presheaf.obj (op U) ≅ CommRingCat.of A :=
  X.toLocallyRingedSpace.restrictTopSectionsIso U ≪≫ LocallyRingedSpace.Γ.mapIso e.symm.op ≪≫
    globalIso A

/-- For nested affine formal opens `W ≤ U` with charts `X|_U ≅ Spf A` and `X|_W ≅ Spf B`, the
restriction map `Γ(U, O_X) → Γ(W, O_X)` corresponds under the chart isomorphisms to
`Spf.sectionsHom` of the induced morphism `Spf B ⟶ Spf A`. -/
theorem sectionsIsoOfIsoSpf_comp_eq_sectionsHom {X : FormalScheme.{u}} {W U : Opens X}
    (hWU : W ≤ U)
    {A B : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsAdicRing A]
    [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsAdicRing B]
    (eU : X.toLocallyRingedSpace.restrict U.isOpenEmbedding ≅ Spf A)
    (eW : X.toLocallyRingedSpace.restrict W.isOpenEmbedding ≅ Spf B) :
    (sectionsIsoOfIsoSpf eU).inv ≫ X.presheaf.map (homOfLE hWU).op ≫
        (sectionsIsoOfIsoSpf eW).hom =
      CommRingCat.ofHom
        (Spf.sectionsHom (eW.inv ≫ X.toLocallyRingedSpace.restrictHomOfLE hWU ≫ eU.hom)) := by
  let X₀ := X.toLocallyRingedSpace
  have hres : (X₀.restrictTopSectionsIso U).inv ≫ X.presheaf.map (homOfLE hWU).op ≫
      (X₀.restrictTopSectionsIso W).hom = (X₀.restrictHomOfLE hWU).c.app (op ⊤) := by
    rw [LocallyRingedSpace.restrictHomOfLE_c_app]
    -- `erw`: `X.presheaf.mapIso` and `Opens.functor` match at default transparency.
    erw [← X.presheaf.map_comp, ← X.presheaf.map_comp]
    exact congrArg X.presheaf.map (Quiver.Hom.unop_inj (Subsingleton.elim _ _))
  have h1 : (sectionsIsoOfIsoSpf eU).inv ≫ X.presheaf.map (homOfLE hWU).op ≫
      (sectionsIsoOfIsoSpf eW).hom = (globalIso A).inv ≫
        (eW.inv ≫ X₀.restrictHomOfLE hWU ≫ eU.hom).c.app (op ⊤) ≫ (globalIso B).hom :=
    CommRingCat.hom_ext <| RingHom.ext fun a ↦
      congrArg (fun t ↦ (globalIso B).hom (eW.inv.c.app (op ⊤) t))
        (ConcreteCategory.congr_hom hres (eU.hom.c.app (op ⊤) ((globalIso A).inv a)))
  exact h1.trans ((congrArg ((globalIso A).inv ≫ ·)
    (Spf.c_app_top_comp_globalSectionsIso_hom _)).trans (Iso.inv_hom_id_assoc (globalIso A) _))

/-- Two affine formal charts on the same open differ on sections by `Spf.sectionsHom` of the
transition isomorphism. -/
theorem sectionsIsoOfIsoSpf_trans {X : FormalScheme.{u}} {U : Opens X}
    {A B : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsAdicRing A]
    [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsAdicRing B]
    (e₁ : X.toLocallyRingedSpace.restrict U.isOpenEmbedding ≅ Spf A)
    (e₂ : X.toLocallyRingedSpace.restrict U.isOpenEmbedding ≅ Spf B) :
    (sectionsIsoOfIsoSpf e₁).inv ≫ (sectionsIsoOfIsoSpf e₂).hom =
      CommRingCat.ofHom (Spf.sectionsHom (e₂.inv ≫ e₁.hom)) := by
  have h := sectionsIsoOfIsoSpf_comp_eq_sectionsHom (le_refl U) e₁ e₂
  have hid : X.presheaf.map (homOfLE (le_refl U)).op = 𝟙 _ := X.presheaf.map_id (op U)
  rwa [LocallyRingedSpace.restrictHomOfLE_refl, Category.id_comp, hid, Category.id_comp] at h

/-- For an affine formal open `W ≤ U` with chart `e : X|_W ≅ Spf B`, the sheaf component at `U` of
the open immersion `j = e.inv ≫ X.ofRestrict W : Spf B ⟶ X` agrees with restriction `Γ(U) → Γ(W)`
followed by `sectionsIsoOfIsoSpf e`. -/
theorem chartImmersion_c_app {X : FormalScheme.{u}} {W U : Opens X} (hWU : W ≤ U)
    {B : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsAdicRing B]
    (e : X.toLocallyRingedSpace.restrict W.isOpenEmbedding ≅ Spf B) :
    let j : Spf B ⟶ X.toLocallyRingedSpace :=
      e.inv ≫ X.toLocallyRingedSpace.ofRestrict W.isOpenEmbedding
    have hj : (Opens.map j.base).obj U = ⊤ := by ext q; exact iff_true_intro (hWU (e.inv.base q).2)
    j.c.app (op U) ≫ (Spf B).presheaf.map (eqToHom (congrArg op hj)) ≫
        (@Spf.globalSectionsIso B _ _ _ _ (IsAdicRing.ideal_spec B).2.2
          (IsAdicRing.ideal_spec B).2.1).hom =
      X.presheaf.map (homOfLE hWU).op ≫ (sectionsIsoOfIsoSpf e).hom := by
  intro j hj
  let iW := X.toLocallyRingedSpace.ofRestrict W.isOpenEmbedding
  have hpreW : (Opens.map iW.base).obj U = ⊤ := by ext x; exact iff_true_intro (hWU x.2)
  have hcomp := LocallyRingedSpace.comp_c_app_comp_eqToHom_of_map_eq_top e.inv iW hpreW hj
  have hres := X.toLocallyRingedSpace.ofRestrict_c_app_comp_eqToHom hWU hpreW
  -- `erw`: `(Spf B).presheaf` unfolds to `(Spf.structureSheaf _).obj`, matching `globalIso B`.
  erw [← Category.assoc, hcomp]
  exact CommRingCat.hom_ext <| RingHom.ext fun s ↦
    congrArg (fun t ↦ (globalIso B).hom (e.inv.c.app (op ⊤) t)) (ConcreteCategory.congr_hom hres s)

/-- Specialisation of `chartImmersion_c_app` to global sections (`U = ⊤`). -/
theorem chartImmersion_c_app_top {X : FormalScheme.{u}} {W : Opens X}
    {B : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsAdicRing B]
    (e : X.toLocallyRingedSpace.restrict W.isOpenEmbedding ≅ Spf B) :
    (e.inv ≫ X.toLocallyRingedSpace.ofRestrict W.isOpenEmbedding).c.app (op ⊤) ≫
        (@Spf.globalSectionsIso B _ _ _ _ (IsAdicRing.ideal_spec B).2.2
          (IsAdicRing.ideal_spec B).2.1).hom =
      X.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op ≫ (sectionsIsoOfIsoSpf e).hom := by
  have hchart := chartImmersion_c_app (X := X) (le_top : W ≤ ⊤) e
  dsimp only at hchart
  -- `erw`: `(Opens.map _).obj ⊤` is defeq to `⊤` (`Opens.map_top`).
  erw [(Spf B).presheaf.map_id (op ⊤), Category.id_comp] at hchart
  exact hchart

end ChartIsomorphism

section AffineSectionsTopology

private noncomputable def affineRing {X : FormalScheme.{u}} {U : Opens X}
    (hU : X.IsAffineOpen U) : Type u :=
  Classical.choose ((X.isAffineOpen_iff U).mp hU)

private noncomputable instance {X : FormalScheme.{u}} {U : Opens X} (hU : X.IsAffineOpen U) :
    CommRing (affineRing hU) :=
  Classical.choose (Classical.choose_spec ((X.isAffineOpen_iff U).mp hU))

private noncomputable instance {X : FormalScheme.{u}} {U : Opens X} (hU : X.IsAffineOpen U) :
    TopologicalSpace (affineRing hU) :=
  Classical.choose (Classical.choose_spec (Classical.choose_spec ((X.isAffineOpen_iff U).mp hU)))

private instance {X : FormalScheme.{u}} {U : Opens X} (hU : X.IsAffineOpen U) :
    IsTopologicalRing (affineRing hU) :=
  Classical.choose (Classical.choose_spec (Classical.choose_spec
    (Classical.choose_spec ((X.isAffineOpen_iff U).mp hU))))

private instance {X : FormalScheme.{u}} {U : Opens X} (hU : X.IsAffineOpen U) :
    IsAdicRing (affineRing hU) :=
  Classical.choose (Classical.choose_spec (Classical.choose_spec
    (Classical.choose_spec (Classical.choose_spec ((X.isAffineOpen_iff U).mp hU)))))

private noncomputable def affineChart {X : FormalScheme.{u}} {U : Opens X} (hU : X.IsAffineOpen U) :
    X.toLocallyRingedSpace.restrict U.isOpenEmbedding ≅ Spf (affineRing hU) :=
  Classical.choice (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
    (Classical.choose_spec (Classical.choose_spec ((X.isAffineOpen_iff U).mp hU))))))

/-- The intrinsic adic topology on the ring of sections `Γ(U, O_X)` over an affine formal open `U`,
defined by pulling back the topology of `A` along any chart `X|_U ≅ Spf A`. It is independent of
the chosen chart (`isHomeomorph_sectionsIsoOfIsoSpf`). -/
@[instance_reducible]
noncomputable def sectionsTopology (X : FormalScheme.{u}) (U : Opens X) (hU : X.IsAffineOpen U) :
    TopologicalSpace (X.presheaf.obj (op U)) :=
  TopologicalSpace.induced (sectionsIsoOfIsoSpf (affineChart hU)).hom inferInstance

/-- **Chart independence of `sectionsTopology`.** For every affine formal chart `e : X|_U ≅ Spf A`,
the induced ring isomorphism `Γ(U, O_X) ≅ A` is a homeomorphism for `sectionsTopology X U hU`. -/
theorem isHomeomorph_sectionsIsoOfIsoSpf {X : FormalScheme.{u}} {U : Opens X}
    (hU : X.IsAffineOpen U)
    {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsAdicRing A]
    (e : X.toLocallyRingedSpace.restrict U.isOpenEmbedding ≅ Spf A) :
    @IsHomeomorph _ _ (sectionsTopology X U hU) _ (sectionsIsoOfIsoSpf e).hom := by
  let _ : TopologicalSpace (X.presheaf.obj (op U)) := sectionsTopology X U hU
  let e₀ := affineChart hU
  have hbij := (sectionsIsoOfIsoSpf e₀).commRingCatIsoToRingEquiv.bijective
  have h₀ : IsHomeomorph (sectionsIsoOfIsoSpf e₀).hom :=
    isHomeomorph_iff_isEmbedding_surjective.mpr ⟨⟨IsInducing.induced _, hbij.1⟩, hbij.2⟩
  have hcomp : ((sectionsIsoOfIsoSpf e).hom : _ → _) =
      (Spf.sectionsHom (e.inv ≫ e₀.hom)) ∘ (sectionsIsoOfIsoSpf e₀).hom := by
    ext s
    have h := ConcreteCategory.congr_hom (sectionsIsoOfIsoSpf_trans e₀ e)
      ((sectionsIsoOfIsoSpf e₀).hom s)
    have hinv := ConcreteCategory.congr_hom (sectionsIsoOfIsoSpf e₀).hom_inv_id s
    simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply,
      CommRingCat.hom_ofHom, CommRingCat.hom_id] at h hinv ⊢
    rw [← h, hinv]; rfl
  rw [hcomp]; exact (Spf.isHomeomorph_sectionsHom_of_iso (e.symm ≪≫ e₀)).comp h₀

/-- For an affine formal open `U`, `sectionsTopology X U hU` is a ring topology on `Γ(U, O_X)`. -/
theorem sectionsTopology_isTopologicalRing (X : FormalScheme.{u}) (U : Opens X)
    (hU : X.IsAffineOpen U) :
    @IsTopologicalRing (X.presheaf.obj (op U)) (sectionsTopology X U hU) _ :=
  TauCeti.isTopologicalRing_induced (sectionsIsoOfIsoSpf (affineChart hU)).hom.hom

/-- For an affine formal open `U`, `Γ(U, O_X)` equipped with `sectionsTopology X U hU` is an adic
ring of finite ideal type. -/
theorem sectionsTopology_isAdicRing (X : FormalScheme.{u}) (U : Opens X) (hU : X.IsAffineOpen U) :
    @IsAdicRing (X.presheaf.obj (op U)) _ (sectionsTopology X U hU)
      (sectionsTopology_isTopologicalRing X U hU) := by
  let _ : TopologicalSpace (X.presheaf.obj (op U)) := sectionsTopology X U hU
  have _ : IsTopologicalRing (X.presheaf.obj (op U)) := sectionsTopology_isTopologicalRing X U hU
  let eqv := (sectionsIsoOfIsoSpf (affineChart hU)).commRingCatIsoToRingEquiv
  let I := IsAdicRing.ideal (affineRing hU)
  obtain ⟨hIfg, hIadic, hIcomp⟩ := IsAdicRing.ideal_spec (affineRing hU)
  have hmap : I.comap eqv.toRingHom = I.map eqv.symm.toRingHom := le_antisymm
    (fun s (hs : eqv s ∈ I) ↦ by simpa using Ideal.mem_map_of_mem eqv.symm.toRingHom hs)
    (Ideal.map_le_iff_le_comap.mpr fun a ha ↦ by
      rw [Ideal.mem_comap, Ideal.mem_comap]; simpa using ha)
  exact ⟨⟨I.comap eqv.toRingHom, hmap ▸ hIfg.map eqv.symm.toRingHom,
    IsAdic.comap hIadic eqv (IsInducing.induced _),
    hmap ▸ (IsAdicComplete.congr_ringEquiv I eqv.symm).mpr hIcomp⟩⟩

/-- Restriction between nested affine formal opens is continuous for `sectionsTopology`. -/
theorem continuous_restrict_of_isAffineOpen {X : FormalScheme.{u}} {W U : Opens X}
    (hW : X.IsAffineOpen W) (hU : X.IsAffineOpen U) (hWU : W ≤ U) :
    @Continuous _ _ (sectionsTopology X U hU) (sectionsTopology X W hW)
      (X.presheaf.map (homOfLE hWU).op) := by
  let eU := affineChart hU; let eW := affineChart hW
  let _ : TopologicalSpace (X.presheaf.obj (op U)) := sectionsTopology X U hU
  let _ : TopologicalSpace (X.presheaf.obj (op W)) := sectionsTopology X W hW
  rw [(isHomeomorph_sectionsIsoOfIsoSpf hW eW).isInducing.continuous_iff]
  have hcomp : ((sectionsIsoOfIsoSpf eW).hom : _ → _) ∘ (X.presheaf.map (homOfLE hWU).op) =
      (Spf.sectionsHom (eW.inv ≫ X.toLocallyRingedSpace.restrictHomOfLE hWU ≫ eU.hom)) ∘
        (sectionsIsoOfIsoSpf eU).hom := by
    ext s
    have h := ConcreteCategory.congr_hom (sectionsIsoOfIsoSpf_comp_eq_sectionsHom hWU eU eW)
      ((sectionsIsoOfIsoSpf eU).hom s)
    have hinv := ConcreteCategory.congr_hom (sectionsIsoOfIsoSpf eU).hom_inv_id s
    simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply,
      CommRingCat.hom_ofHom, CommRingCat.hom_id] at h hinv ⊢
    rw [← h, hinv]; rfl
  rw [hcomp]
  exact (Spf.continuous_sectionsHom _).comp (isHomeomorph_sectionsIsoOfIsoSpf hU eU).continuous

private theorem continuous_c_app_comp_globalSectionsIso {A B : Type u} [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] [IsAdicRing A]
    [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsAdicRing B]
    {U : Opens (Spf.carrier A)} (j : Spf B ⟶ Spf A) (hj : (Opens.map j.base).obj U = ⊤) :
    @Continuous _ _ (Spf.quotientSectionsTopology (IsAdicRing.ideal_spec A).2.1 U) _
      (j.c.app (op U) ≫ (Spf B).presheaf.map (eqToHom (congrArg op hj)) ≫
        (globalIso B).hom) := by
  have := (IsAdicRing.ideal_spec B).2.2
  let tA := Spf.quotientSectionsTopology (IsAdicRing.ideal_spec A).2.1 U
  let tBU := Spf.quotientSectionsTopology (IsAdicRing.ideal_spec B).2.1 ((Opens.map j.base).obj U)
  let tB := Spf.quotientSectionsTopology (IsAdicRing.ideal_spec B).2.1 ⊤
  have h2 : @Continuous _ _ tBU tB ((Spf B).presheaf.map (eqToHom (congrArg op hj))) := by
    rw [(Quiver.Hom.unop_inj (Subsingleton.elim _ _) :
      eqToHom (congrArg op hj) = (homOfLE (le_of_eq hj.symm)).op)]
    exact Spf.quotientSectionsTopology_restrict (IsAdicRing.ideal_spec B).2.1 _
  have h3 : @Continuous _ _ tB _ (globalIso B).hom :=
    @IsHomeomorph.continuous _ _ tB _ _
      (Spf.isHomeomorph_globalSectionsIso (IsAdicRing.ideal_spec B).2.1)
  exact @Continuous.comp _ _ _ tA tB _ _ _ h3
    (@Continuous.comp _ _ _ tA tBU tB _ _ h2 (Spf.continuous_c_app j U))

private theorem continuous_map_comp_sectionsIsoOfIsoSpf {A B : Type u} [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] [IsAdicRing A]
    [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsAdicRing B]
    {W U : Opens (ofSpf A)} (hWU : W ≤ U)
    (e : (ofSpf A).toLocallyRingedSpace.restrict W.isOpenEmbedding ≅ Spf B) :
    @Continuous _ _ (Spf.quotientSectionsTopology (IsAdicRing.ideal_spec A).2.1 U) _
      ((ofSpf A).presheaf.map (homOfLE hWU).op ≫ (sectionsIsoOfIsoSpf e).hom) := by
  let j : Spf B ⟶ Spf A := e.inv ≫ (ofSpf A).toLocallyRingedSpace.ofRestrict W.isOpenEmbedding
  have hj : (Opens.map j.base).obj U = ⊤ := by ext q; exact iff_true_intro (hWU (e.inv.base q).2)
  have hchart := chartImmersion_c_app (X := ofSpf A) hWU e; dsimp only at hchart
  have hfun : (((ofSpf A).presheaf.map (homOfLE hWU).op ≫ (sectionsIsoOfIsoSpf e).hom) : _ → _) =
      (j.c.app (op U) ≫ (Spf B).presheaf.map (eqToHom (congrArg op hj)) ≫ (globalIso B).hom) :=
    funext fun s ↦ (ConcreteCategory.congr_hom hchart s).symm
  rw [hfun]; exact continuous_c_app_comp_globalSectionsIso j hj

private theorem algebraMap_eq_basicOpenSectionsIso_inv_comp_sectionsIsoOfIsoSpf (A : Type u)
    [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsAdicRing A] (f : A) :
    let _ := (IsAdicRing.ideal_spec A).2.2
    let _ := (IsAdicRing.ideal_spec (AdicRing.CompletedAway A f)).2.2
    let iso₁ := sectionsIsoOfIsoSpf (X := ofSpf A) (U := Spf.basicOpen f)
      (Spf.restrictBasicOpenIso f)
    let iso₂ : (ofSpf A).presheaf.obj (op (Spf.basicOpen f)) ≅
        CommRingCat.of (AdicRing.CompletedAway A f) :=
      Spf.basicOpenSectionsIso (IsAdicRing.ideal_spec A).2.1 (IsAdicRing.ideal_spec A).1 f
    CommRingCat.ofHom (algebraMap A (AdicRing.CompletedAway A f)) ≫ (iso₂.inv ≫ iso₁.hom) =
      CommRingCat.ofHom (algebraMap A (AdicRing.CompletedAway A f)) := by
  intro _ _ iso₁ iso₂
  let Uf : Opens (ofSpf A) := Spf.basicOpen f
  let e := Spf.restrictBasicOpenIso f
  let j : Spf (AdicRing.CompletedAway A f) ⟶ Spf A :=
    e.inv ≫ (Spf A).ofRestrict (Spf.basicOpen f).isOpenEmbedding
  have hg : (globalIso A).inv ≫ (ofSpf A).presheaf.map (homOfLE (le_top : Uf ≤ ⊤)).op ≫
      iso₂.hom = CommRingCat.ofHom (algebraMap A (AdicRing.CompletedAway A f)) :=
    Spf.globalSectionsIso_inv_comp_basicOpenSectionsIso_hom (IsAdicRing.ideal_spec A).2.1
      (IsAdicRing.ideal_spec A).1 f
  have h1 : CommRingCat.ofHom (algebraMap A (AdicRing.CompletedAway A f)) ≫ (iso₂.inv ≫ iso₁.hom) =
      (globalIso A).inv ≫ (ofSpf A).presheaf.map (homOfLE (le_top : Uf ≤ ⊤)).op ≫ iso₁.hom := by
    refine CommRingCat.hom_ext <| RingHom.ext fun a ↦ ?_
    have hga := ConcreteCategory.congr_hom hg a
    dsimp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at hga ⊢
    rw [← hga]
    exact congrArg iso₁.hom (ConcreteCategory.congr_hom iso₂.hom_inv_id _)
  have h2 : (globalIso A).inv ≫ (ofSpf A).presheaf.map (homOfLE (le_top : Uf ≤ ⊤)).op ≫
      iso₁.hom = CommRingCat.ofHom (algebraMap A (AdicRing.CompletedAway A f)) := by
    have hchart := chartImmersion_c_app_top (X := ofSpf A) (W := Uf) e
    have h3 : (globalIso A).inv ≫ j.c.app (op ⊤) ≫ (globalIso (AdicRing.CompletedAway A f)).hom =
        CommRingCat.ofHom (algebraMap A (AdicRing.CompletedAway A f)) :=
      (congrArg ((globalIso A).inv ≫ ·) (Spf.c_app_top_comp_globalSectionsIso_hom j)).trans
        ((Iso.inv_hom_id_assoc (globalIso A) _).trans (by
          dsimp only [j, e]
          rw [Spf.restrictBasicOpenIso_inv_ofRestrict f, Spf.sectionsHom_basicOpenι f]))
    refine CommRingCat.hom_ext <| RingHom.ext fun a ↦ ?_
    exact (ConcreteCategory.congr_hom hchart ((globalIso A).inv a)).symm.trans
      (ConcreteCategory.congr_hom h3 a)
  exact h1.trans h2

/-- On `ofSpf A`, the chart isomorphism induced by `Spf.restrictBasicOpenIso f` coincides with
`Spf.basicOpenSectionsIso`. -/
theorem sectionsIsoOfIsoSpf_restrictBasicOpenIso (A : Type u) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [IsAdicRing A] (f : A) :
    sectionsIsoOfIsoSpf (X := ofSpf A) (U := Spf.basicOpen f) (Spf.restrictBasicOpenIso f) =
      Spf.basicOpenSectionsIso (IsAdicRing.ideal_spec A).2.1 (IsAdicRing.ideal_spec A).1 f := by
  have := (IsAdicRing.ideal_spec A).2.2
  have := (IsAdicRing.ideal_spec (AdicRing.CompletedAway A f)).2.2
  let Uf : Opens (ofSpf A) := Spf.basicOpen f
  let iso₁ := sectionsIsoOfIsoSpf (X := ofSpf A) (U := Uf) (Spf.restrictBasicOpenIso f)
  let iso₂ : (ofSpf A).presheaf.obj (op Uf) ≅ CommRingCat.of (AdicRing.CompletedAway A f) :=
    Spf.basicOpenSectionsIso (IsAdicRing.ideal_spec A).2.1 (IsAdicRing.ideal_spec A).1 f
  let _ : TopologicalSpace ((ofSpf A).presheaf.obj (op Uf)) :=
    Spf.quotientSectionsTopology (IsAdicRing.ideal_spec A).2.1 (Spf.basicOpen f)
  have hcont₁ : Continuous iso₁.hom := by
    have hcont := continuous_map_comp_sectionsIsoOfIsoSpf (le_refl Uf) (Spf.restrictBasicOpenIso f)
    have hid : (ofSpf A).presheaf.map (homOfLE (le_refl Uf)).op = 𝟙 _ := (ofSpf A).presheaf.map_id _
    rwa [hid, Category.id_comp] at hcont
  have hhomeo₂ : IsHomeomorph iso₂.hom :=
    Spf.quotientSectionsTopology_basic (IsAdicRing.ideal_spec A).2.1 (IsAdicRing.ideal_spec A).1 f
  have hinv : (iso₂.inv : _ → _) = hhomeo₂.homeomorph.symm := funext fun x ↦ hhomeo₂.injective
    ((ConcreteCategory.congr_hom iso₂.inv_hom_id x).trans
      (hhomeo₂.homeomorph.apply_symm_apply x).symm)
  have hψ_id : iso₂.inv ≫ iso₁.hom = 𝟙 _ := CommRingCat.hom_ext <|
    AdicRing.CompletedAway.ringHom_ext A f (hcont₁.comp (hinv ▸ hhomeo₂.homeomorph.symm.continuous))
      continuous_id (congrArg CommRingCat.Hom.hom
        (algebraMap_eq_basicOpenSectionsIso_inv_comp_sectionsIsoOfIsoSpf A f))
  exact Iso.ext <| (Category.id_comp iso₁.hom).symm.trans
    (iso₂.hom_inv_id ▸ (by rw [Category.assoc, hψ_id, Category.comp_id]))

/-- On a basic open `D(f)` of `ofSpf A`, `sectionsTopology` coincides with
`Spf.quotientSectionsTopology`. -/
theorem sectionsTopology_ofSpf_basicOpen (A : Type u) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [IsAdicRing A] (f : A) :
    sectionsTopology (ofSpf A) (Spf.basicOpen f) (isAffineOpen_basicOpen A f) =
      Spf.quotientSectionsTopology (IsAdicRing.ideal_spec A).2.1 (Spf.basicOpen f) := by
  let t₁ := sectionsTopology (ofSpf A) (Spf.basicOpen f) (isAffineOpen_basicOpen A f)
  let t₂ := Spf.quotientSectionsTopology (IsAdicRing.ideal_spec A).2.1 (Spf.basicOpen f)
  have h₁ := isHomeomorph_sectionsIsoOfIsoSpf (X := ofSpf A) (isAffineOpen_basicOpen A f)
    (Spf.restrictBasicOpenIso f)
  rw [sectionsIsoOfIsoSpf_restrictBasicOpenIso] at h₁
  have h₂ := Spf.quotientSectionsTopology_basic (IsAdicRing.ideal_spec A).2.1
    (IsAdicRing.ideal_spec A).1 f
  exact (@IsInducing.eq_induced _ _ t₁ _ _ (@IsHomeomorph.isInducing _ _ t₁ _ _ h₁)).trans
    (@IsInducing.eq_induced _ _ t₂ _ _ (@IsHomeomorph.isInducing _ _ t₂ _ _ h₂)).symm

end AffineSectionsTopology

section SheafSectionsTopology

/-- **The sheaf topology on sections over an arbitrary open of a formal scheme** (EGA I, Ch. 0,
3.8.1; Ch. I, 10.4.5): the initial topology on `Γ(U, O_X)` for the restriction maps to all affine
formal opens `W ⊆ U`, each carrying its intrinsic adic topology `sectionsTopology`. -/
@[instance_reducible]
noncomputable def sheafSectionsTopology (X : FormalScheme.{u}) (U : Opens X) :
    TopologicalSpace (X.presheaf.obj (op U)) :=
  ⨅ (W : Opens X) (hWU : W ≤ U) (hW : X.IsAffineOpen W),
    TopologicalSpace.induced (X.presheaf.map (homOfLE hWU).op) (sectionsTopology X W hW)

/-- A map into `Γ(U, O_X)` is continuous for `sheafSectionsTopology` if and only if its composite
with every restriction to an affine formal open `W ⊆ U` is continuous for `sectionsTopology`. -/
theorem continuous_iff_sheafSectionsTopology {Z : Type*} [TopologicalSpace Z]
    (X : FormalScheme.{u}) (U : Opens X) (g : Z → X.presheaf.obj (op U)) :
    @Continuous _ _ _ (sheafSectionsTopology X U) g ↔
      ∀ (W : Opens X) (hWU : W ≤ U) (hW : X.IsAffineOpen W),
        @Continuous _ _ _ (sectionsTopology X W hW) ((X.presheaf.map (homOfLE hWU).op) ∘ g) := by
  rw [sheafSectionsTopology, continuous_iInf_rng]
  simp_rw [continuous_iInf_rng, continuous_induced_rng]

/-- Every restriction map `Γ(U, O_X) → Γ(V, O_X)` is continuous for `sheafSectionsTopology`. -/
theorem sheafSectionsTopology_restrict (X : FormalScheme.{u}) {U V : Opens X} (hVU : V ≤ U) :
    @Continuous _ _ (sheafSectionsTopology X U) (sheafSectionsTopology X V)
      (X.presheaf.map (homOfLE hVU).op) := by
  let _ : TopologicalSpace (X.presheaf.obj (op U)) := sheafSectionsTopology X U
  refine (continuous_iff_sheafSectionsTopology X V _).mpr fun W hWV hW ↦ ?_
  have hcomp : (X.presheaf.map (homOfLE hWV).op) ∘ (X.presheaf.map (homOfLE hVU).op) =
      (X.presheaf.map (homOfLE (hWV.trans hVU)).op) := funext fun s ↦
    (ConcreteCategory.congr_hom (X.presheaf.map_comp (homOfLE hVU).op (homOfLE hWV).op) s).symm
  rw [hcomp]
  exact (continuous_iff_le_induced (t₁ := sheafSectionsTopology X U)
    (t₂ := sectionsTopology X W hW)).mpr
    (iInf_le_of_le W (iInf_le_of_le (hWV.trans hVU) (iInf_le _ hW)))

/-- For every open `U`, `sheafSectionsTopology X U` is a ring topology on `Γ(U, O_X)`. -/
theorem sheafSectionsTopology_isTopologicalRing (X : FormalScheme.{u}) (U : Opens X) :
    @IsTopologicalRing (X.presheaf.obj (op U)) (sheafSectionsTopology X U) _ :=
  TauCeti.isTopologicalRing_iInf fun W ↦ TauCeti.isTopologicalRing_iInf fun hWU ↦
    TauCeti.isTopologicalRing_iInf fun hW ↦ by
      let _ := sectionsTopology X W hW
      have _ := sectionsTopology_isTopologicalRing X W hW
      exact TauCeti.isTopologicalRing_induced (X.presheaf.map (homOfLE hWU).op).hom

/-- On an affine formal open `U`, `sheafSectionsTopology X U` coincides with
`sectionsTopology X U hU`. -/
theorem sheafSectionsTopology_eq_sectionsTopology (X : FormalScheme.{u}) (U : Opens X)
    (hU : X.IsAffineOpen U) :
    sheafSectionsTopology X U = sectionsTopology X U hU := by
  apply le_antisymm
  · refine iInf_le_of_le U (iInf_le_of_le (le_refl U) (iInf_le_of_le hU ?_))
    have hid : ((X.presheaf.map (homOfLE (le_refl U)).op) : _ → _) = id :=
      funext fun s ↦ ConcreteCategory.congr_hom (X.presheaf.map_id (op U)) s
    rw [hid, @induced_id _ (sectionsTopology X U hU)]
  · exact le_iInf fun W ↦ le_iInf fun hWU ↦ le_iInf fun hW ↦
      (continuous_iff_le_induced (t₁ := sectionsTopology X U hU)
        (t₂ := sectionsTopology X W hW)).mp (continuous_restrict_of_isAffineOpen hW hU hWU)

/-- On an affine formal scheme `ofSpf A`, `sheafSectionsTopology` agrees with
`Spf.quotientSectionsTopology` on every open subset `U` (EGA I, Ch. 0, 3.8.1; Ch. I, 10.4.5). -/
theorem sheafSectionsTopology_ofSpf (A : Type u) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [IsAdicRing A] (U : Opens (ofSpf A)) :
    sheafSectionsTopology (ofSpf A) U =
      Spf.quotientSectionsTopology (IsAdicRing.ideal_spec A).2.1 U := by
  let U' : Opens (Spf.carrier A) := U
  apply le_antisymm
  · rw [Spf.quotientSectionsTopology_def (U := U')]
    refine le_iInf fun f ↦ le_iInf fun hf ↦ iInf_le_of_le (Spf.basicOpen f)
      (iInf_le_of_le hf (iInf_le_of_le (isAffineOpen_basicOpen A f) ?_))
    rw [sectionsTopology_ofSpf_basicOpen, Spf.quotientSectionsTopology_basicOpen]; rfl
  · refine le_iInf fun W ↦ le_iInf fun hWU ↦ le_iInf fun hW ↦ ?_
    obtain ⟨B, _, _, _, _, ⟨e⟩⟩ := ((ofSpf A).isAffineOpen_iff W).mp hW
    let tU : TopologicalSpace ((ofSpf A).presheaf.obj (op U)) :=
      Spf.quotientSectionsTopology (IsAdicRing.ideal_spec A).2.1 U'
    let tW := sectionsTopology (ofSpf A) W hW
    let _ := tU; let _ := tW
    refine (continuous_iff_le_induced (t₁ := tU) (t₂ := tW)).mp ?_
    rw [(@IsHomeomorph.isInducing _ _ tW _ _
      (isHomeomorph_sectionsIsoOfIsoSpf (X := ofSpf A) hW e)).continuous_iff]
    exact continuous_map_comp_sectionsIsoOfIsoSpf hWU e

/-- On the global open `⊤` of `ofSpf A`, `sectionsTopology` coincides with
`Spf.quotientSectionsTopology`. -/
theorem sectionsTopology_ofSpf_top (A : Type u) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [IsAdicRing A] :
    sectionsTopology (ofSpf A) ⊤ (isAffineOpen_top_ofSpf A) =
      Spf.quotientSectionsTopology (IsAdicRing.ideal_spec A).2.1 ⊤ :=
  (sheafSectionsTopology_eq_sectionsTopology (ofSpf A) ⊤ (isAffineOpen_top_ofSpf A)).symm.trans
    (sheafSectionsTopology_ofSpf A ⊤)

end SheafSectionsTopology

end TauCeti.FormalScheme
