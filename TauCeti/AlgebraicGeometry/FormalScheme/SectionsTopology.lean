/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.FormalScheme.Basic
public import TauCeti.AlgebraicGeometry.FormalScheme.Spf.HomEquiv
public import TauCeti.Geometry.RingedSpace.LocallyRingedSpace.GlueMorphisms

import TauCeti.Topology.Algebra.Ring.Basic

/-!
# Topologies on rings of sections of a formal scheme

Let `X` be a formal scheme of finite ideal type. Every affine formal open `U` of `X` admits an
isomorphism `e : X|_U ≅ Spf A` for an adic ring `A` of finite ideal type, inducing a ring
isomorphism `Γ(U, O_X) ≅ A` (`FormalScheme.sectionsIsoOfIsoSpf`). Pulling back the adic topology of
`A` equips `Γ(U, O_X)` with a complete separated adic ring topology
(`FormalScheme.sectionsTopology`). Because every isomorphism `Spf B ≅ Spf A` induces a homeomorphic
ring equivalence `A ≃+* B` (`Spf.isHomeomorph_sectionsHom_of_iso`), this topology does not depend
on the choice of affine formal chart `e` (`FormalScheme.isHomeomorph_sectionsIsoOfIsoSpf`).

For an arbitrary open subset `U` of `X`, the sheaf topology `FormalScheme.sheafSectionsTopology`
on `Γ(U, O_X)` is the initial topology for the restriction maps `Γ(U, O_X) → Γ(W, O_X)` to all
affine formal opens `W ⊆ U` (EGA I, Ch. 0, 3.8.1; Ch. I, 10.4.5). On an affine formal open `U`, it
agrees with `FormalScheme.sectionsTopology`
(`FormalScheme.sheafSectionsTopology_eq_sectionsTopology`), and on an affine formal scheme
`ofSpf A` it coincides over every open `U` with `Spf.quotientSectionsTopology`
(`FormalScheme.sheafSectionsTopology_ofSpf`).

## Main definitions

* `TauCeti.FormalScheme.sectionsIsoOfIsoSpf`: the ring isomorphism `Γ(U, O_X) ≅ A` induced by an
  affine formal chart `e : X|_U ≅ Spf A`.
* `TauCeti.FormalScheme.sectionsTopology`: the intrinsic adic topology on `Γ(U, O_X)` for an affine
  formal open `U` of `X`.
* `TauCeti.FormalScheme.sheafSectionsTopology`: the initial topology on `Γ(U, O_X)` for the
  restrictions to all affine formal opens contained in `U`.

## Main results

* `TauCeti.FormalScheme.isHomeomorph_sectionsIsoOfIsoSpf`: every affine formal chart `X|_U ≅ Spf A`
  induces a homeomorphism `(Γ(U, O_X), sectionsTopology) ≃ₜ A`.
* `TauCeti.FormalScheme.sectionsTopology_isTopologicalRing`,
  `TauCeti.FormalScheme.sectionsTopology_isAdicRing`: on an affine formal open `U`, `Γ(U, O_X)` is
  an adic ring of finite ideal type.
* `TauCeti.FormalScheme.continuous_restrict_of_isAffineOpen`: restrictions between affine formal
  opens are continuous.
* `TauCeti.FormalScheme.sheafSectionsTopology_restrict`,
  `TauCeti.FormalScheme.sheafSectionsTopology_isTopologicalRing`: `sheafSectionsTopology` makes
  every `Γ(U, O_X)` a topological ring with continuous restriction maps.
* `TauCeti.FormalScheme.sheafSectionsTopology_eq_sectionsTopology`: on an affine formal open,
  `sheafSectionsTopology` coincides with `sectionsTopology`.
* `TauCeti.FormalScheme.sheafSectionsTopology_ofSpf`: on `ofSpf A`, `sheafSectionsTopology` agrees
  with `Spf.quotientSectionsTopology` on every open subset.

## References

* A. Grothendieck and J. Dieudonné, *Éléments de géométrie algébrique I*, Ch. 0, 3.8.1 and
  Ch. I, 10.4.5.
* [Stacks Project, Tag 0AHY](https://stacks.math.columbia.edu/tag/0AHY).
-/

public section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry Topology

namespace TauCeti.FormalScheme

universe u

section ChartIsomorphism

/-- The image of the top open of `U` under `U.isOpenEmbedding` is `U`. -/
private theorem isOpenEmbedding_functor_top (X : LocallyRingedSpace.{u}) (U : Opens X) :
    U.isOpenEmbedding.functor.obj ⊤ = U := by
  ext x
  simp

/-- The canonical isomorphism `Γ(U, O_X) ≅ Γ(⊤, O_{X|_U})`. -/
private noncomputable def restrictTopSectionsIso (X : LocallyRingedSpace.{u}) (U : Opens X) :
    X.presheaf.obj (op U) ≅ (X.restrict U.isOpenEmbedding).presheaf.obj (op ⊤) :=
  X.presheaf.mapIso (eqToIso (congrArg op (isOpenEmbedding_functor_top X U).symm))

/-- An isomorphism `e : Y ≅ Z` of locally ringed spaces induces an isomorphism on global sections
`Γ(⊤, O_Y) ≅ Γ(⊤, O_Z)`. -/
private noncomputable def globalSectionsIsoOfIso {Y Z : LocallyRingedSpace.{u}} (e : Y ≅ Z) :
    Y.presheaf.obj (op ⊤) ≅ Z.presheaf.obj (op ⊤) where
  hom := e.inv.c.app (op ⊤)
  inv := e.hom.c.app (op ⊤)
  hom_inv_id := by
    have h := (LocallyRingedSpace.comp_c_app e.hom e.inv (op ⊤)).symm
    rw [e.hom_inv_id] at h
    exact h
  inv_hom_id := by
    have h := (LocallyRingedSpace.comp_c_app e.inv e.hom (op ⊤)).symm
    rw [e.inv_hom_id] at h
    exact h

/-- The ring isomorphism `Γ(U, O_X) ≅ A` induced by an affine formal chart `e : X|_U ≅ Spf A`. -/
noncomputable def sectionsIsoOfIsoSpf {X : FormalScheme.{u}} {U : Opens X}
    {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsAdicRing A]
    (e : X.toLocallyRingedSpace.restrict U.isOpenEmbedding ≅ Spf A) :
    X.presheaf.obj (op U) ≅ CommRingCat.of A :=
  restrictTopSectionsIso X.toLocallyRingedSpace U ≪≫ globalSectionsIsoOfIso e ≪≫
    (@Spf.globalSectionsIso A _ _ _ _ (IsAdicRing.ideal_spec A).2.2 (IsAdicRing.ideal_spec A).2.1)

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
  have hres : (restrictTopSectionsIso X.toLocallyRingedSpace U).inv ≫
      X.presheaf.map (homOfLE hWU).op ≫ (restrictTopSectionsIso X.toLocallyRingedSpace W).hom =
      (X.toLocallyRingedSpace.restrictHomOfLE hWU).c.app (op ⊤) := by
    rw [LocallyRingedSpace.restrictHomOfLE_c_app]
    -- `erw`: `X.presheaf.mapIso` and `Opens.functor` match at default transparency.
    erw [← X.presheaf.map_comp, ← X.presheaf.map_comp]
    exact congrArg X.presheaf.map (Quiver.Hom.unop_inj (Subsingleton.elim _ _))
  have hmid : eU.hom.c.app (op ⊤) ≫ (X.toLocallyRingedSpace.restrictHomOfLE hWU).c.app (op ⊤) ≫
      eW.inv.c.app (op ⊤) =
      (eW.inv ≫ X.toLocallyRingedSpace.restrictHomOfLE hWU ≫ eU.hom).c.app (op ⊤) :=
    CommRingCat.hom_ext <| RingHom.ext fun _ ↦ rfl
  let gA : (Spf A).presheaf.obj (op ⊤) ≅ CommRingCat.of A :=
    @Spf.globalSectionsIso A _ _ _ _ (IsAdicRing.ideal_spec A).2.2 (IsAdicRing.ideal_spec A).2.1
  let gB : (Spf B).presheaf.obj (op ⊤) ≅ CommRingCat.of B :=
    @Spf.globalSectionsIso B _ _ _ _ (IsAdicRing.ideal_spec B).2.2 (IsAdicRing.ideal_spec B).2.1
  calc (sectionsIsoOfIsoSpf eU).inv ≫ X.presheaf.map (homOfLE hWU).op ≫
          (sectionsIsoOfIsoSpf eW).hom
      = gA.inv ≫ eU.hom.c.app (op ⊤) ≫
          ((restrictTopSectionsIso X.toLocallyRingedSpace U).inv ≫
            X.presheaf.map (homOfLE hWU).op ≫
            (restrictTopSectionsIso X.toLocallyRingedSpace W).hom) ≫
          eW.inv.c.app (op ⊤) ≫ gB.hom := by
        simp only [sectionsIsoOfIsoSpf, Iso.trans_inv, Iso.trans_hom, Category.assoc]
        rfl
    _ = gA.inv ≫
          (eU.hom.c.app (op ⊤) ≫ (X.toLocallyRingedSpace.restrictHomOfLE hWU).c.app (op ⊤) ≫
            eW.inv.c.app (op ⊤)) ≫ gB.hom := by
        refine CommRingCat.hom_ext <| RingHom.ext fun a ↦ ?_
        have h := ConcreteCategory.congr_hom hres (eU.hom.c.app (op ⊤) (gA.inv a))
        exact congrArg (fun t ↦ gB.hom (eW.inv.c.app (op ⊤) t)) h
    _ = gA.inv ≫ (eW.inv ≫ X.toLocallyRingedSpace.restrictHomOfLE hWU ≫ eU.hom).c.app (op ⊤) ≫
          gB.hom := by
        rw [hmid]
        rfl
    _ = CommRingCat.ofHom
          (Spf.sectionsHom (eW.inv ≫ X.toLocallyRingedSpace.restrictHomOfLE hWU ≫ eU.hom)) :=
        (congrArg (gA.inv ≫ ·) (Spf.c_app_top_comp_globalSectionsIso_hom _)).trans
          (Iso.inv_hom_id_assoc gA _)

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
  rw [LocallyRingedSpace.restrictHomOfLE_refl, Category.id_comp] at h
  have hid : X.presheaf.map (homOfLE (le_refl U)).op = 𝟙 _ := X.presheaf.map_id (op U)
  rwa [hid, Category.id_comp] at h

/-- For an affine formal open `W ≤ U` with chart `e : X|_W ≅ Spf B`, the sheaf component at `U` of
the open immersion `j = e.inv ≫ X.ofRestrict W : Spf B ⟶ X` agrees with restriction `Γ(U) → Γ(W)`
followed by `sectionsIsoOfIsoSpf e`. -/
theorem chartImmersion_c_app {X : FormalScheme.{u}} {W U : Opens X} (hWU : W ≤ U)
    {B : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsAdicRing B]
    (e : X.toLocallyRingedSpace.restrict W.isOpenEmbedding ≅ Spf B) :
    let j : Spf B ⟶ X.toLocallyRingedSpace :=
      e.inv ≫ X.toLocallyRingedSpace.ofRestrict W.isOpenEmbedding
    have hj : (Opens.map j.base).obj U = ⊤ := by
      ext q
      exact iff_true_intro (hWU (e.inv.base q).2)
    j.c.app (op U) ≫ (Spf B).presheaf.map (eqToHom (congrArg op hj)) ≫
        (@Spf.globalSectionsIso B _ _ _ _ (IsAdicRing.ideal_spec B).2.2
          (IsAdicRing.ideal_spec B).2.1).hom =
      X.presheaf.map (homOfLE hWU).op ≫ (sectionsIsoOfIsoSpf e).hom := by
  intro j hj
  have hpreW :
      (Opens.map (X.toLocallyRingedSpace.ofRestrict W.isOpenEmbedding).base).obj U = ⊤ := by
    ext x
    exact iff_true_intro (hWU x.2)
  have hj' : (Opens.map e.inv.base).obj
      ((Opens.map (X.toLocallyRingedSpace.ofRestrict W.isOpenEmbedding).base).obj U) = ⊤ := hj
  have hnat := e.inv.c.naturality (eqToHom (congrArg op hpreW))
  have hcomp : j.c.app (op U) ≫ (Spf B).presheaf.map (eqToHom (congrArg op hj)) =
      (X.toLocallyRingedSpace.ofRestrict W.isOpenEmbedding).c.app (op U) ≫
        (X.toLocallyRingedSpace.restrict W.isOpenEmbedding).presheaf.map
          (eqToHom (congrArg op hpreW)) ≫
        e.inv.c.app (op ⊤) := by
    have hc : j.c.app (op U) =
        (X.toLocallyRingedSpace.ofRestrict W.isOpenEmbedding).c.app (op U) ≫
          e.inv.c.app (op ((Opens.map
            (X.toLocallyRingedSpace.ofRestrict W.isOpenEmbedding).base).obj U)) :=
      LocallyRingedSpace.comp_c_app e.inv (X.toLocallyRingedSpace.ofRestrict W.isOpenEmbedding)
        (op U)
    rw [hc]
    -- `erw`: pushforward presheaf on `op U` matches `restrict.presheaf` at default transparency.
    erw [Category.assoc]
    have hstep : e.inv.c.app (op ((Opens.map
          (X.toLocallyRingedSpace.ofRestrict W.isOpenEmbedding).base).obj U)) ≫
          (Spf B).presheaf.map (eqToHom (congrArg op hj')) =
        (X.toLocallyRingedSpace.restrict W.isOpenEmbedding).presheaf.map
          (eqToHom (congrArg op hpreW)) ≫ e.inv.c.app (op ⊤) := by
      have hm : (Spf B).presheaf.map (eqToHom (congrArg op hj')) =
          ((TopCat.Presheaf.pushforward CommRingCat e.inv.base).obj (Spf B).presheaf).map
            (eqToHom (congrArg op hpreW)) :=
        congrArg (Spf B).presheaf.map (Quiver.Hom.unop_inj (Subsingleton.elim _ _))
      exact (congrArg (e.inv.c.app _ ≫ ·) hm).trans hnat.symm
    exact congrArg ((X.toLocallyRingedSpace.ofRestrict W.isOpenEmbedding).c.app (op U) ≫ ·) hstep
  have hres : (X.toLocallyRingedSpace.ofRestrict W.isOpenEmbedding).c.app (op U) ≫
      (X.toLocallyRingedSpace.restrict W.isOpenEmbedding).presheaf.map
        (eqToHom (congrArg op hpreW)) =
      X.presheaf.map (homOfLE hWU).op ≫ (restrictTopSectionsIso X.toLocallyRingedSpace W).hom := by
    -- `erw`: `ofRestrict.c.app` and `restrict.presheaf.map` both unfold to `X.presheaf.map`.
    erw [← X.presheaf.map_comp, ← X.presheaf.map_comp]
    exact congrArg X.presheaf.map (Quiver.Hom.unop_inj (Subsingleton.elim _ _))
  let gB := (@Spf.globalSectionsIso B _ _ _ _ (IsAdicRing.ideal_spec B).2.2
    (IsAdicRing.ideal_spec B).2.1).hom
  calc j.c.app (op U) ≫ (Spf B).presheaf.map (eqToHom (congrArg op hj)) ≫ gB
      = (j.c.app (op U) ≫ (Spf B).presheaf.map (eqToHom (congrArg op hj))) ≫ gB :=
        (Category.assoc _ _ _).symm
    _ = ((X.toLocallyRingedSpace.ofRestrict W.isOpenEmbedding).c.app (op U) ≫
          (X.toLocallyRingedSpace.restrict W.isOpenEmbedding).presheaf.map
            (eqToHom (congrArg op hpreW)) ≫ e.inv.c.app (op ⊤)) ≫ gB :=
        congrArg (· ≫ gB) hcomp
    _ = ((X.toLocallyRingedSpace.ofRestrict W.isOpenEmbedding).c.app (op U) ≫
          (X.toLocallyRingedSpace.restrict W.isOpenEmbedding).presheaf.map
            (eqToHom (congrArg op hpreW))) ≫ e.inv.c.app (op ⊤) ≫ gB := by
        exact (Category.assoc _ _ _).trans ((Category.assoc _ _ _).symm)
    _ = (X.presheaf.map (homOfLE hWU).op ≫ (restrictTopSectionsIso X.toLocallyRingedSpace W).hom) ≫
          e.inv.c.app (op ⊤) ≫ gB :=
        congrArg (· ≫ e.inv.c.app (op ⊤) ≫ gB) hres
    _ = X.presheaf.map (homOfLE hWU).op ≫ (sectionsIsoOfIsoSpf e).hom := by
        simp only [sectionsIsoOfIsoSpf, Iso.trans_hom, Category.assoc]
        rfl

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
  have htop_id : (Spf B).presheaf.map (eqToHom (congrArg op (by
      ext q; exact iff_true_intro trivial :
        (Opens.map (e.inv ≫ X.toLocallyRingedSpace.ofRestrict W.isOpenEmbedding).base).obj ⊤ =
          ⊤))) = 𝟙 _ :=
    (Spf B).presheaf.map_id _
  -- `erw`: `(Opens.map _).obj ⊤` is defeq to `⊤` at default transparency.
  erw [htop_id, Category.id_comp] at hchart
  exact hchart

end ChartIsomorphism

section AffineSectionsTopology

/-- The chosen adic ring witnessing `X.IsAffineOpen U`. -/
private noncomputable def affineRing {X : FormalScheme.{u}} {U : Opens X} (hU : X.IsAffineOpen U) :
    Type u :=
  Classical.choose ((X.isAffineOpen_iff U).mp hU)

private noncomputable instance affineRingCommRing {X : FormalScheme.{u}} {U : Opens X}
    (hU : X.IsAffineOpen U) : CommRing (affineRing hU) :=
  Classical.choose (Classical.choose_spec ((X.isAffineOpen_iff U).mp hU))

private noncomputable instance affineRingTop {X : FormalScheme.{u}} {U : Opens X}
    (hU : X.IsAffineOpen U) : TopologicalSpace (affineRing hU) :=
  Classical.choose (Classical.choose_spec (Classical.choose_spec ((X.isAffineOpen_iff U).mp hU)))

private instance affineRingIsTopRing {X : FormalScheme.{u}} {U : Opens X} (hU : X.IsAffineOpen U) :
    IsTopologicalRing (affineRing hU) :=
  Classical.choose (Classical.choose_spec (Classical.choose_spec
    (Classical.choose_spec ((X.isAffineOpen_iff U).mp hU))))

private instance affineRingIsAdicRing {X : FormalScheme.{u}} {U : Opens X} (hU : X.IsAffineOpen U) :
    IsAdicRing (affineRing hU) :=
  Classical.choose (Classical.choose_spec (Classical.choose_spec
    (Classical.choose_spec (Classical.choose_spec ((X.isAffineOpen_iff U).mp hU)))))

private noncomputable def affineChart {X : FormalScheme.{u}} {U : Opens X}
    (hU : X.IsAffineOpen U) :
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
    isHomeomorph_iff_isEmbedding_surjective.mpr
      ⟨⟨IsInducing.induced _, hbij.injective⟩, hbij.surjective⟩
  have htr : IsHomeomorph (Spf.sectionsHom (e.inv ≫ e₀.hom)) :=
    Spf.isHomeomorph_sectionsHom_of_iso (e.symm ≪≫ e₀)
  have hcomp : ((sectionsIsoOfIsoSpf e).hom : _ → _) =
      (Spf.sectionsHom (e.inv ≫ e₀.hom)) ∘ (sectionsIsoOfIsoSpf e₀).hom := by
    ext s
    have h := ConcreteCategory.congr_hom (sectionsIsoOfIsoSpf_trans e₀ e)
      ((sectionsIsoOfIsoSpf e₀).hom s)
    simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply,
      CommRingCat.hom_ofHom] at h
    dsimp only [Function.comp_apply]
    rw [← h]
    have hid := ConcreteCategory.congr_hom (sectionsIsoOfIsoSpf e₀).hom_inv_id s
    simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply,
      CommRingCat.hom_id, RingHom.id_apply] at hid
    exact congrArg (sectionsIsoOfIsoSpf e).hom hid.symm
  rw [hcomp]
  exact htr.comp h₀

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
  let eqv : X.presheaf.obj (op U) ≃+* affineRing hU :=
    (sectionsIsoOfIsoSpf (affineChart hU)).commRingCatIsoToRingEquiv
  let I : Ideal (affineRing hU) := IsAdicRing.ideal (affineRing hU)
  obtain ⟨hIfg, hIadic, hIcomp⟩ := IsAdicRing.ideal_spec (affineRing hU)
  have hmap : I.comap eqv.toRingHom = I.map eqv.symm.toRingHom := by
    refine le_antisymm (fun s hs ↦ ?_) (Ideal.map_le_iff_le_comap.mpr fun a ha ↦ ?_)
    · have h : eqv.symm (eqv s) ∈ I.map eqv.symm.toRingHom :=
        Ideal.mem_map_of_mem eqv.symm.toRingHom hs
      rwa [eqv.symm_apply_apply] at h
    · change eqv (eqv.symm a) ∈ I
      rwa [eqv.apply_symm_apply]
  refine ⟨⟨I.comap eqv.toRingHom, ?_, ?_, ?_⟩⟩
  · rw [hmap]
    exact hIfg.map eqv.symm.toRingHom
  · exact IsAdic.comap hIadic eqv (IsInducing.induced _)
  · rw [hmap]
    exact (IsAdicComplete.congr_ringEquiv I eqv.symm).mpr hIcomp

/-- Restriction between nested affine formal opens is continuous for `sectionsTopology`. -/
theorem continuous_restrict_of_isAffineOpen {X : FormalScheme.{u}} {W U : Opens X}
    (hW : X.IsAffineOpen W) (hU : X.IsAffineOpen U) (hWU : W ≤ U) :
    @Continuous _ _ (sectionsTopology X U hU) (sectionsTopology X W hW)
      (X.presheaf.map (homOfLE hWU).op) := by
  let eU := affineChart hU
  let eW := affineChart hW
  let _ : TopologicalSpace (X.presheaf.obj (op U)) := sectionsTopology X U hU
  let _ : TopologicalSpace (X.presheaf.obj (op W)) := sectionsTopology X W hW
  have hhomeoU := isHomeomorph_sectionsIsoOfIsoSpf hU eU
  have hhomeoW := isHomeomorph_sectionsIsoOfIsoSpf hW eW
  rw [hhomeoW.isInducing.continuous_iff]
  have hcomp : ((sectionsIsoOfIsoSpf eW).hom : _ → _) ∘ (X.presheaf.map (homOfLE hWU).op) =
      (Spf.sectionsHom (eW.inv ≫ X.toLocallyRingedSpace.restrictHomOfLE hWU ≫ eU.hom)) ∘
        (sectionsIsoOfIsoSpf eU).hom := by
    ext s
    have h := ConcreteCategory.congr_hom (sectionsIsoOfIsoSpf_comp_eq_sectionsHom hWU eU eW)
      ((sectionsIsoOfIsoSpf eU).hom s)
    simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply,
      CommRingCat.hom_ofHom] at h
    dsimp only [Function.comp_apply]
    rw [← h]
    have hid := ConcreteCategory.congr_hom (sectionsIsoOfIsoSpf eU).hom_inv_id s
    simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply,
      CommRingCat.hom_id, RingHom.id_apply] at hid
    exact congrArg (fun t ↦ (sectionsIsoOfIsoSpf eW).hom (X.presheaf.map (homOfLE hWU).op t))
      hid.symm
  rw [hcomp]
  exact (Spf.continuous_sectionsHom _).comp hhomeoU.continuous

/-- On `ofSpf A`, the chart isomorphism induced by `Spf.restrictBasicOpenIso f` coincides with
`Spf.basicOpenSectionsIso`. -/
theorem sectionsIsoOfIsoSpf_restrictBasicOpenIso (A : Type u) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [IsAdicRing A] (f : A) :
    sectionsIsoOfIsoSpf (X := ofSpf A) (U := Spf.basicOpen f) (Spf.restrictBasicOpenIso f) =
      Spf.basicOpenSectionsIso (IsAdicRing.ideal_spec A).2.1 (IsAdicRing.ideal_spec A).1 f := by
  have := (IsAdicRing.ideal_spec A).2.2
  have := (IsAdicRing.ideal_spec (AdicRing.CompletedAway A f)).2.2
  let Uf : Opens (ofSpf A) := Spf.basicOpen f
  let e : (ofSpf A).toLocallyRingedSpace.restrict Uf.isOpenEmbedding ≅
      Spf (AdicRing.CompletedAway A f) := Spf.restrictBasicOpenIso f
  let j : Spf (AdicRing.CompletedAway A f) ⟶ Spf A :=
    e.inv ≫ (ofSpf A).toLocallyRingedSpace.ofRestrict Uf.isOpenEmbedding
  have hj_eq : j = Spf.basicOpenι f := Spf.restrictBasicOpenIso_inv_ofRestrict f
  let iso₁ : (ofSpf A).presheaf.obj (op Uf) ≅ CommRingCat.of (AdicRing.CompletedAway A f) :=
    sectionsIsoOfIsoSpf (X := ofSpf A) (U := Uf) e
  let iso₂ : (ofSpf A).presheaf.obj (op Uf) ≅ CommRingCat.of (AdicRing.CompletedAway A f) :=
    Spf.basicOpenSectionsIso (IsAdicRing.ideal_spec A).2.1 (IsAdicRing.ideal_spec A).1 f
  let gA : (ofSpf A).presheaf.obj (op ⊤) ≅ CommRingCat.of A :=
    Spf.globalSectionsIso (IsAdicRing.ideal_spec A).2.1
  let tUf : TopologicalSpace ((ofSpf A).presheaf.obj (op Uf)) :=
    Spf.quotientSectionsTopology (IsAdicRing.ideal_spec A).2.1 (Spf.basicOpen f)
  have hchart := chartImmersion_c_app (X := ofSpf A) (le_refl Uf) e
  dsimp only at hchart
  have hid : (ofSpf A).presheaf.map (homOfLE (le_refl Uf)).op = 𝟙 _ := (ofSpf A).presheaf.map_id _
  rw [hid, Category.id_comp] at hchart
  have hcont₁ : @Continuous _ _ tUf _ iso₁.hom := by
    let Uf' : Opens (Spf.carrier A) := Spf.basicOpen f
    have htop_j : (Opens.map j.base).obj Uf' = ⊤ := by
      ext q
      exact iff_true_intro (e.inv.base q).2
    let tMid : TopologicalSpace
        ((Spf (AdicRing.CompletedAway A f)).presheaf.obj (op ((Opens.map j.base).obj Uf'))) :=
      Spf.quotientSectionsTopology (IsAdicRing.ideal_spec (AdicRing.CompletedAway A f)).2.1
        ((Opens.map j.base).obj Uf')
    let tTop : TopologicalSpace ((Spf (AdicRing.CompletedAway A f)).presheaf.obj (op ⊤)) :=
      Spf.quotientSectionsTopology (IsAdicRing.ideal_spec (AdicRing.CompletedAway A f)).2.1 ⊤
    have hj_cont : @Continuous _ _ tUf tMid (j.c.app (op Uf)) := Spf.continuous_c_app j Uf'
    have hglob : @Continuous _ _ tTop _
        ((Spf.globalSectionsIso (IsAdicRing.ideal_spec (AdicRing.CompletedAway A f)).2.1).hom) :=
      @IsHomeomorph.continuous _ _ tTop _ _ (Spf.isHomeomorph_globalSectionsIso _)
    have heq_cont : @Continuous _ _ tMid tTop
        ((Spf (AdicRing.CompletedAway A f)).presheaf.map (eqToHom (congrArg op htop_j))) := by
      have h := Spf.quotientSectionsTopology_restrict
        (IsAdicRing.ideal_spec (AdicRing.CompletedAway A f)).2.1 (le_of_eq htop_j.symm)
      have heq : (eqToHom (congrArg op htop_j) : op ((Opens.map j.base).obj Uf') ⟶ op ⊤) =
          (homOfLE (le_of_eq htop_j.symm)).op :=
        Quiver.Hom.unop_inj (Subsingleton.elim _ _)
      rw [heq]
      exact h
    have hfun : (iso₁.hom : _ → _) =
        ((Spf.globalSectionsIso (IsAdicRing.ideal_spec (AdicRing.CompletedAway A f)).2.1).hom) ∘
        ((Spf (AdicRing.CompletedAway A f)).presheaf.map (eqToHom (congrArg op htop_j))) ∘
        (j.c.app (op Uf)) := by
      ext s
      exact (ConcreteCategory.congr_hom hchart s).symm
    rw [hfun]
    exact @Continuous.comp _ _ _ tUf tTop inferInstance _ _ hglob
      (@Continuous.comp _ _ _ tUf tMid tTop _ _ heq_cont hj_cont)
  have hψ_cont : Continuous (iso₂.inv ≫ iso₁.hom).hom := by
    let _ : TopologicalSpace ((ofSpf A).presheaf.obj (op Uf)) := tUf
    have hhomeo₂ : IsHomeomorph iso₂.hom :=
      Spf.quotientSectionsTopology_basic (IsAdicRing.ideal_spec A).2.1 (IsAdicRing.ideal_spec A).1 f
    have hinv : (iso₂.inv : _ → _) = hhomeo₂.homeomorph.symm := by
      ext x
      apply hhomeo₂.injective
      have h1 := ConcreteCategory.congr_hom iso₂.inv_hom_id x
      have h2 := hhomeo₂.homeomorph.apply_symm_apply x
      exact h1.trans h2.symm
    have hcont₂ : Continuous iso₂.inv := by
      rw [hinv]
      exact hhomeo₂.homeomorph.symm.continuous
    exact hcont₁.comp hcont₂
  have hψ_eq : (iso₂.inv ≫ iso₁.hom).hom = RingHom.id (AdicRing.CompletedAway A f) := by
    refine AdicRing.CompletedAway.ringHom_ext A f hψ_cont continuous_id ?_
    have hgb : gA.inv ≫ (ofSpf A).presheaf.map (homOfLE (le_top : Uf ≤ ⊤)).op ≫ iso₂.hom =
        CommRingCat.ofHom (algebraMap A (AdicRing.CompletedAway A f)) :=
      Spf.globalSectionsIso_inv_comp_basicOpenSectionsIso_hom
        (IsAdicRing.ideal_spec A).2.1 (IsAdicRing.ideal_spec A).1 f
    have h1 : CommRingCat.ofHom (algebraMap A (AdicRing.CompletedAway A f)) ≫
        (iso₂.inv ≫ iso₁.hom) =
        gA.inv ≫ (ofSpf A).presheaf.map (homOfLE (le_top : Uf ≤ ⊤)).op ≫ iso₁.hom := by
      rw [← hgb, Category.assoc, Category.assoc, Iso.hom_inv_id_assoc]
    have h2 : gA.inv ≫ (ofSpf A).presheaf.map (homOfLE (le_top : Uf ≤ ⊤)).op ≫ iso₁.hom =
        CommRingCat.ofHom (algebraMap A (AdicRing.CompletedAway A f)) := by
      have hchart_top := chartImmersion_c_app (X := ofSpf A) (le_top : Uf ≤ ⊤) e
      dsimp only at hchart_top
      rw [← hchart_top]
      have htop_id : (Spf (AdicRing.CompletedAway A f)).presheaf.map (eqToHom (congrArg op
          (by ext q; exact iff_true_intro trivial :
            (Opens.map j.base).obj ⊤ = ⊤))) = 𝟙 _ :=
        (Spf (AdicRing.CompletedAway A f)).presheaf.map_id _
      have hc_eq : j.c.app (op ⊤) ≫
          (Spf (AdicRing.CompletedAway A f)).presheaf.map (eqToHom (congrArg op
            (by ext q; exact iff_true_intro trivial :
              (Opens.map j.base).obj ⊤ = ⊤))) ≫
          (Spf.globalSectionsIso (IsAdicRing.ideal_spec (AdicRing.CompletedAway A f)).2.1).hom =
          gA.hom ≫ CommRingCat.ofHom (Spf.sectionsHom j) := by
        -- `erw`: `(Opens.map j.base).obj ⊤` is defeq to `⊤` at default transparency.
        erw [htop_id, Category.id_comp]
        exact Spf.c_app_top_comp_globalSectionsIso_hom j
      exact (congrArg (gA.inv ≫ ·) hc_eq).trans
        ((Iso.inv_hom_id_assoc gA _).trans (by rw [hj_eq, Spf.sectionsHom_basicOpenι f]))
    exact congrArg CommRingCat.Hom.hom (h1.trans h2)
  have hhom : iso₁.hom = iso₂.hom := by
    have h : iso₂.inv ≫ iso₁.hom = 𝟙 _ := CommRingCat.hom_ext hψ_eq
    rw [← Category.id_comp iso₁.hom, ← iso₂.hom_inv_id, Category.assoc, h, Category.comp_id]
  exact Iso.ext hhom

/-- On a basic open `D(f)` of `ofSpf A`, `sectionsTopology` coincides with
`Spf.quotientSectionsTopology`. -/
theorem sectionsTopology_ofSpf_basicOpen (A : Type u) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [IsAdicRing A] (f : A) :
    sectionsTopology (ofSpf A) (Spf.basicOpen f) (isAffineOpen_basicOpen A f) =
      Spf.quotientSectionsTopology (IsAdicRing.ideal_spec A).2.1 (Spf.basicOpen f) := by
  have h₁ := isHomeomorph_sectionsIsoOfIsoSpf (X := ofSpf A) (isAffineOpen_basicOpen A f)
    (Spf.restrictBasicOpenIso f)
  rw [sectionsIsoOfIsoSpf_restrictBasicOpenIso] at h₁
  have h₂ := Spf.quotientSectionsTopology_basic (IsAdicRing.ideal_spec A).2.1
    (IsAdicRing.ideal_spec A).1 f
  let t₁ := sectionsTopology (ofSpf A) (Spf.basicOpen f) (isAffineOpen_basicOpen A f)
  let t₂ : TopologicalSpace ((ofSpf A).presheaf.obj (op (Spf.basicOpen f))) :=
    Spf.quotientSectionsTopology (IsAdicRing.ideal_spec A).2.1 (Spf.basicOpen f)
  have hi₁ : @IsInducing _ _ t₁ _ _ := @IsHomeomorph.isInducing _ _ t₁ _ _ h₁
  have hi₂ : @IsInducing _ _ t₂ _ _ := @IsHomeomorph.isInducing _ _ t₂ _ _ h₂
  exact (@IsInducing.eq_induced _ _ t₁ _ _ hi₁).trans (@IsInducing.eq_induced _ _ t₂ _ _ hi₂).symm

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
  have hcomp : ((X.presheaf.map (homOfLE hWV).op) ∘ (X.presheaf.map (homOfLE hVU).op)) =
      (X.presheaf.map (homOfLE (hWV.trans hVU)).op) := by
    ext s
    exact (ConcreteCategory.congr_hom
      (X.presheaf.map_comp (homOfLE hVU).op (homOfLE hWV).op) s).symm
  rw [hcomp]
  exact (continuous_iff_le_induced (t₁ := sheafSectionsTopology X U)
    (t₂ := sectionsTopology X W hW)).mpr
    (iInf_le_of_le W (iInf_le_of_le (hWV.trans hVU) (iInf_le _ hW)))

/-- For every open `U`, `sheafSectionsTopology X U` is a ring topology on `Γ(U, O_X)`. -/
theorem sheafSectionsTopology_isTopologicalRing (X : FormalScheme.{u}) (U : Opens X) :
    @IsTopologicalRing (X.presheaf.obj (op U)) (sheafSectionsTopology X U) _ := by
  refine TauCeti.isTopologicalRing_iInf fun W ↦
    TauCeti.isTopologicalRing_iInf fun hWU ↦ TauCeti.isTopologicalRing_iInf fun hW ↦ ?_
  let _ : TopologicalSpace (X.presheaf.obj (op W)) := sectionsTopology X W hW
  have _ : IsTopologicalRing (X.presheaf.obj (op W)) := sectionsTopology_isTopologicalRing X W hW
  exact TauCeti.isTopologicalRing_induced (X.presheaf.map (homOfLE hWU).op).hom

/-- On an affine formal open `U`, `sheafSectionsTopology X U` coincides with
`sectionsTopology X U hU`. -/
theorem sheafSectionsTopology_eq_sectionsTopology (X : FormalScheme.{u}) (U : Opens X)
    (hU : X.IsAffineOpen U) :
    sheafSectionsTopology X U = sectionsTopology X U hU := by
  apply le_antisymm
  · refine iInf_le_of_le U (iInf_le_of_le (le_refl U) (iInf_le_of_le hU ?_))
    have hid : ((X.presheaf.map (homOfLE (le_refl U)).op) : _ → _) = id := by
      ext s
      exact ConcreteCategory.congr_hom (X.presheaf.map_id (op U)) s
    rw [hid, @induced_id _ (sectionsTopology X U hU)]
  · refine le_iInf fun W ↦ le_iInf fun hWU ↦ le_iInf fun hW ↦ ?_
    exact (continuous_iff_le_induced (t₁ := sectionsTopology X U hU)
      (t₂ := sectionsTopology X W hW)).mp (continuous_restrict_of_isAffineOpen hW hU hWU)

/-- On an affine formal scheme `ofSpf A`, `sheafSectionsTopology` agrees with
`Spf.quotientSectionsTopology` on every open subset `U` (EGA I, Ch. 0, 3.8.1; Ch. I, 10.4.5). -/
theorem sheafSectionsTopology_ofSpf (A : Type u) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [IsAdicRing A] (U : Opens (ofSpf A)) :
    sheafSectionsTopology (ofSpf A) U =
      Spf.quotientSectionsTopology (IsAdicRing.ideal_spec A).2.1 U := by
  let U' : Opens (Spf.carrier A) := U
  apply le_antisymm
  · change sheafSectionsTopology (ofSpf A) U ≤
      Spf.quotientSectionsTopology (IsAdicRing.ideal_spec A).2.1 U'
    rw [Spf.quotientSectionsTopology_def]
    refine le_iInf fun f ↦ le_iInf fun hf ↦ ?_
    refine iInf_le_of_le (Spf.basicOpen f)
      (iInf_le_of_le hf (iInf_le_of_le (isAffineOpen_basicOpen A f) ?_))
    rw [sectionsTopology_ofSpf_basicOpen, Spf.quotientSectionsTopology_basicOpen]
    exact le_rfl
  · refine le_iInf fun W ↦ le_iInf fun hWU ↦ le_iInf fun hW ↦ ?_
    obtain ⟨B, _, _, _, _, ⟨e⟩⟩ := ((ofSpf A).isAffineOpen_iff W).mp hW
    have := (IsAdicRing.ideal_spec B).2.2
    let j : Spf B ⟶ Spf A := e.inv ≫ (Spf A).ofRestrict W.isOpenEmbedding
    have hj : (Opens.map j.base).obj U = ⊤ := by
      ext q
      exact iff_true_intro (hWU (e.inv.base q).2)
    have hchart := chartImmersion_c_app (X := ofSpf A) hWU e
    dsimp only at hchart
    have hhomeo := isHomeomorph_sectionsIsoOfIsoSpf (X := ofSpf A) hW e
    let tU : TopologicalSpace ((ofSpf A).presheaf.obj (op U)) :=
      Spf.quotientSectionsTopology (IsAdicRing.ideal_spec A).2.1 U'
    let tW : TopologicalSpace ((ofSpf A).presheaf.obj (op W)) := sectionsTopology (ofSpf A) W hW
    refine (continuous_iff_le_induced (t₁ := tU) (t₂ := tW)).mp ?_
    let _ : TopologicalSpace ((ofSpf A).presheaf.obj (op U)) := tU
    let _ : TopologicalSpace ((ofSpf A).presheaf.obj (op W)) := tW
    rw [hhomeo.isInducing.continuous_iff]
    have hj' : (Opens.map j.base).obj U' = ⊤ := hj
    have hfun : ((sectionsIsoOfIsoSpf e).hom : _ → _) ∘ ((ofSpf A).presheaf.map (homOfLE hWU).op) =
        ((Spf.globalSectionsIso (IsAdicRing.ideal_spec B).2.1).hom) ∘
        ((Spf B).presheaf.map (eqToHom (congrArg op hj'))) ∘ (j.c.app (op U)) := by
      ext s
      exact (ConcreteCategory.congr_hom hchart s).symm
    rw [hfun]
    let tMid : TopologicalSpace ((Spf B).presheaf.obj (op ((Opens.map j.base).obj U'))) :=
      Spf.quotientSectionsTopology (IsAdicRing.ideal_spec B).2.1 ((Opens.map j.base).obj U')
    let tTop : TopologicalSpace ((Spf B).presheaf.obj (op ⊤)) :=
      Spf.quotientSectionsTopology (IsAdicRing.ideal_spec B).2.1 ⊤
    have h1 : @Continuous _ _ tU tMid (j.c.app (op U)) := Spf.continuous_c_app j U'
    have h2 : @Continuous _ _ tMid tTop ((Spf B).presheaf.map (eqToHom (congrArg op hj'))) := by
      have h := Spf.quotientSectionsTopology_restrict (IsAdicRing.ideal_spec B).2.1
        (le_of_eq hj'.symm)
      have heq : (eqToHom (congrArg op hj') : op ((Opens.map j.base).obj U') ⟶ op ⊤) =
          (homOfLE (le_of_eq hj'.symm)).op :=
        Quiver.Hom.unop_inj (Subsingleton.elim _ _)
      rw [heq]
      exact h
    have h3 : @Continuous _ _ tTop _
        (Spf.globalSectionsIso (IsAdicRing.ideal_spec B).2.1).hom :=
      @IsHomeomorph.continuous _ _ tTop _ _
        (Spf.isHomeomorph_globalSectionsIso (IsAdicRing.ideal_spec B).2.1)
    exact @Continuous.comp _ _ _ tU tTop inferInstance _ _ h3
      (@Continuous.comp _ _ _ tU tMid tTop _ _ h2 h1)

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
