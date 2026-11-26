/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Twisted.HomotopyInvariance.Basic
import TauCeti.AlgebraicTopology.Singular.Twisted.Coefficients

/-!
# Twisted chains of spaces over a space

Let `M` be a local coefficient system on a space `X`. A map `g : A ⟶ B` with `g ≫ b = a` induces a
map of twisted chains with coefficients in the pullbacks `a*M` and `b*M`
(`overTwistedChainComplexMap`), functorially in `g`. So twisted chains and twisted homology are
functors on the category `Over X` (`overTwistedChainComplexFunctor`, `overTwistedHomologyFunctor`),
with a cocone to `Hₖ(X; M)` (`overTwistedHomologyCocone`). All declarations of this file are in the
namespace `TauCeti.LocalCoefficientSystem`.

With local coefficients a homotopy acts on coefficients by transport along the paths it traces
(`TopCat.Homotopy.twistedHomologyMap_eq_comp`). Consider maps `ρ : A ⟶ B` and `g : A ⟶ Y` over `X`
and a map `e : B ⟶ Y`, with a homotopy `G` from `e ≫ y` to `b` and a homotopy `H` from `ρ ≫ e` to
`g`, which agree over `X`: at every point of `A` the image under `y` of the path traced by `H` is
homotopic to the path traced by `G`. Transport along `H` and along `G` then identify the
coefficients in the same way, so the triangle commutes on twisted homology
(`homologyMap_overTwistedChainComplexMap_eq_comp`).

## Main definitions

* `overTwistedChainComplexMap`: the map of twisted chains induced by a map of spaces over `X`.
* `overTwistedChainComplexFunctor`, `overTwistedHomologyFunctor`: twisted chains and twisted
  homology of spaces over `X`.
* `overTwistedHomologyCocone`: their maps to `Hₖ(X; M)`.

## Main results

* `homologyMap_overTwistedChainComplexMap_eq_comp`: triangles over `X` that commute up to coherent
  homotopies commute on twisted homology.

## References

* A. Hatcher, *Algebraic Topology*, Section 3.H, for homology with local coefficients.
-/

public section

noncomputable section

open CategoryTheory Limits

universe u v w

namespace TauCeti.LocalCoefficientSystem

variable {R : Type u} [Ring R] {X : TopCat.{v}} (L : LocalCoefficientSystem.{u, v, max v w} R X)

variable {A B C : TopCat.{v}} {a : A ⟶ X} {b : B ⟶ X} {c : C ⟶ X}

/-- The map of twisted chains induced by a map `g : A ⟶ B` of spaces over `X`, with coefficients
in the pullbacks of `L` along the maps `a : A ⟶ X` and `b : B ⟶ X`, where `g ≫ b = a`. -/
def overTwistedChainComplexMap (g : A ⟶ B) (h : g ≫ b = a) :
    ((pullback a.hom).obj L).twistedChainComplex ⟶
      ((pullback b.hom).obj L).twistedChainComplex :=
  twistedChainComplexCoefficientMap
      (eqToIso (congrArg (fun k : A ⟶ X ↦ (pullback k.hom).obj L) h.symm) ≪≫
        (pullbackCompIso g.hom b.hom).app L).hom ≫
    twistedChainComplexMap g ((pullback b.hom).obj L)

/-- A map of spaces over `X` followed by the map of its target to `X` is the map of its source to
`X`, on twisted chains. -/
@[reassoc (attr := simp)]
lemma overTwistedChainComplexMap_twistedChainComplexMap (g : A ⟶ B) (h : g ≫ b = a) :
    overTwistedChainComplexMap L g h ≫ twistedChainComplexMap b L =
      twistedChainComplexMap a L := by
  subst h
  rw [twistedChainComplexMap_comp, overTwistedChainComplexMap, Category.assoc, Iso.trans_hom,
    twistedChainComplexCoefficientMap_comp, Category.assoc]
  simp only [TopCat.hom_comp, eqToIso_refl, Iso.refl_hom, twistedChainComplexCoefficientMap_id,
    Functor.comp_obj, Iso.app_hom, Category.id_comp]

/-- The identity of a space over `X` induces the identity of twisted chains. -/
@[simp]
lemma overTwistedChainComplexMap_id (h : 𝟙 A ≫ a = a) :
    overTwistedChainComplexMap L (𝟙 A) h = 𝟙 _ := by
  rw [overTwistedChainComplexMap, twistedChainComplexMap_id,
    ← twistedChainComplexCoefficientMap_comp]
  refine (congrArg twistedChainComplexCoefficientMap (?_ : _ = 𝟙 _)).trans
    (twistedChainComplexCoefficientMap_id _)
  ext x : 2
  simp only [pullback_obj_obj, Functor.id_obj, TopCat.hom_id, Functor.comp_obj, TopCat.hom_comp,
    Iso.trans_hom, eqToIso.hom, Iso.app_hom, Category.assoc, NatTrans.comp_app, eqToHom_app,
    pullbackCompIso_hom_app_app, pullbackIdIso_hom_app_app, NatTrans.id_app]
  -- Both components are identities of fibres of `L` at points that agree only by unfolding
  -- `FundamentalGroupoid.map`, so the two sides are equal by definition.
  rfl

/-- A composite of maps of spaces over `X` induces the composite of the two maps of twisted
chains. -/
lemma overTwistedChainComplexMap_comp (g : A ⟶ B) (g' : B ⟶ C) (h : g ≫ b = a)
    (h' : g' ≫ c = b) :
    overTwistedChainComplexMap L (g ≫ g') (by rw [Category.assoc, h', h]) =
      overTwistedChainComplexMap L g h ≫ overTwistedChainComplexMap L g' h' := by
  subst h' h
  rw [overTwistedChainComplexMap, twistedChainComplexMap_comp, overTwistedChainComplexMap,
    overTwistedChainComplexMap]
  simp only [Category.assoc, twistedChainComplexMap_naturality_assoc]
  simp only [← Category.assoc]
  congr 2
  rw [← twistedChainComplexCoefficientMap_comp, ← twistedChainComplexCoefficientMap_comp]
  congr 1
  ext x : 2
  simp only [TopCat.hom_comp, ContinuousMap.comp_assoc, pullback_obj_obj, Functor.comp_obj,
    eqToIso_refl, Iso.refl_trans, Iso.app_hom, NatTrans.comp_app, pullbackCompIso_hom_app_app,
    pullback_map_app]
  -- As in `overTwistedChainComplexMap_id`, both sides are identities of fibres of `L`.
  rfl

/-- On twisted homology, a map of spaces over `X` followed by the map of its target to `X` is the
map of its source to `X`. -/
@[reassoc (attr := simp)]
lemma homologyMap_overTwistedChainComplexMap_twistedHomologyMap (g : A ⟶ B) (h : g ≫ b = a)
    (k : ℕ) :
    HomologicalComplex.homologyMap (overTwistedChainComplexMap L g h) k ≫
        twistedHomologyMap b L k =
      twistedHomologyMap a L k := by
  rw [← HomologicalComplex.homologyMap_comp, overTwistedChainComplexMap_twistedChainComplexMap]

/-- For a map `g` over `X` whose map to `X` is the composite `g ≫ b`, the map of twisted chains over
`X` is the map induced by `g`, after identifying the two pullbacks of `L` along `g ≫ b`. -/
@[reassoc]
lemma twistedChainComplexCoefficientMap_comp_overTwistedChainComplexMap (g : A ⟶ B) :
    twistedChainComplexCoefficientMap ((pullbackCompIso g.hom b.hom).inv.app L) ≫
        overTwistedChainComplexMap L g rfl =
      twistedChainComplexMap g ((pullback b.hom).obj L) := by
  rw [overTwistedChainComplexMap, ← Category.assoc, ← twistedChainComplexCoefficientMap_comp]
  refine (congrArg (· ≫ _) ((congrArg twistedChainComplexCoefficientMap (?_ : _ = 𝟙 _)).trans
    (twistedChainComplexCoefficientMap_id _))).trans (Category.id_comp _)
  ext x : 2
  simp only [Functor.comp_obj, pullback_obj_obj, TopCat.hom_comp, eqToIso_refl, Iso.refl_trans,
    Iso.app_hom, Iso.inv_hom_id_app, NatTrans.id_app]

/-- The homology form of `twistedChainComplexCoefficientMap_comp_overTwistedChainComplexMap`. -/
@[reassoc]
lemma twistedHomologyCoefficientMap_comp_homologyMap_overTwistedChainComplexMap (g : A ⟶ B)
    (k : ℕ) :
    twistedHomologyCoefficientMap ((pullbackCompIso g.hom b.hom).inv.app L) k ≫
        HomologicalComplex.homologyMap (overTwistedChainComplexMap L g rfl) k =
      twistedHomologyMap g ((pullback b.hom).obj L) k := by
  rw [← HomologicalComplex.homologyMap_comp,
    twistedChainComplexCoefficientMap_comp_overTwistedChainComplexMap]

/-- The map of twisted chains induced by an inclusion `S ⊆ T` of subsets of `X` is the map over
`X` induced by the inclusion. -/
lemma subsetTwistedChainComplexMap_eq_overTwistedChainComplexMap {S T : Set X} (h : S ⊆ T) :
    subsetTwistedChainComplexMap L h =
      overTwistedChainComplexMap (a := TopCat.ofHom (ContinuousMap.subtypeVal S))
        (b := TopCat.ofHom (ContinuousMap.subtypeVal T)) L
        (TopCat.ofHom (ContinuousMap.inclusion h)) rfl := by
  simp only [subsetTwistedChainComplexMap_def, overTwistedChainComplexMap]
  -- The remaining `eqToIso` is along an equation between definitionally equal pullbacks, so it is
  -- the identity by `rfl`; `eqToIso_refl` does not fire because the two sides are not syntactically
  -- equal.
  congr 2

/-- The coefficient comparisons of `homologyMap_overTwistedChainComplexMap_eq_comp`: transporting
along `H` and then along `G` identifies the two pullbacks of `L` to `A` as the canonical
comparison, when the two homotopies agree over `X`. -/
private lemma pullbackHomotopyIso_coherent {Y : TopCat.{v}} {y : Y ⟶ X} (ρ : A ⟶ B) (g : A ⟶ Y)
    (hg : g ≫ y = ρ ≫ b) (e : B ⟶ Y) (G : TopCat.Homotopy (e ≫ y) b)
    (H : TopCat.Homotopy (ρ ≫ e) g)
    (hGH : ∀ x : A, ((H.evalAt x).map y.hom.continuous).Homotopic
      ((G.evalAt (ρ x)).cast rfl (ConcreteCategory.congr_hom hg x))) :
    (eqToIso (congrArg (fun k : A ⟶ X ↦ (pullback k.hom).obj L) hg.symm) ≪≫
      (pullbackCompIso g.hom y.hom).app L).hom ≫
    (pullbackHomotopyIso H).inv.app ((pullback y.hom).obj L) ≫
    (pullbackCompIso ρ.hom e.hom).hom.app ((pullback y.hom).obj L) ≫
    (pullback ρ.hom).map
      (((pullbackCompIso e.hom y.hom).app L).symm ≪≫ (pullbackHomotopyIso G).app L).hom =
    (eqToIso (congrArg (fun k : A ⟶ X ↦ (pullback k.hom).obj L) (rfl : ρ ≫ b = ρ ≫ b)) ≪≫
      (pullbackCompIso ρ.hom b.hom).app L).hom := by
  -- At a point, both sides are transports in `L`; the coherence identifies the two paths.
  have aux : ∀ {p q r : X} (hpq : p = q) (P : Path.Homotopic.Quotient r p)
      (Q : Path.Homotopic.Quotient r q), P = Q.cast rfl hpq →
      eqToHom (congrArg L.obj (congrArg FundamentalGroupoid.mk hpq.symm)) ≫
        L.map (P.symm : FundamentalGroupoid.mk p ⟶ FundamentalGroupoid.mk r) ≫
        L.map (Q : FundamentalGroupoid.mk r ⟶ FundamentalGroupoid.mk q) = 𝟙 _ := by
    intro p q r hpq P Q hPQ
    subst hpq hPQ
    rw [Path.Homotopic.Quotient.cast_rfl_rfl, eqToHom_refl, Category.id_comp, ← L.map_comp]
    exact (congrArg L.map (Groupoid.inv_comp Q)).trans (L.map_id _)
  ext x : 2
  have hq : (Path.Homotopic.Quotient.mk (H.evalAt x.as)).map y.hom =
      (Path.Homotopic.Quotient.mk (G.evalAt (ρ x.as))).cast rfl
        (ConcreteCategory.congr_hom hg x.as) :=
    Quotient.sound (hGH x.as)
  simp only [TopCat.hom_comp, pullback_obj_obj, Functor.comp_obj, Iso.trans_hom, eqToIso.hom,
    Iso.app_hom, Iso.symm_hom, Iso.app_inv, Functor.map_comp, Category.assoc, NatTrans.comp_app,
    eqToHom_app, pullbackCompIso_hom_app_app, pullbackHomotopyIso_inv_app_app,
    ContinuousMap.comp_apply, Path.Homotopic.Quotient.mk''_eq_mk, Path.Homotopic.Quotient.mk_symm,
    pullback_obj_map, FundamentalGroupoid.map_map, pullback_map_app, pullbackCompIso_inv_app_app,
    pullbackHomotopyIso_hom_app_app, eqToIso_refl, Iso.refl_trans]
  exact aux _ _ _ hq

/-- **Homotopy-coherent triangles over `X` commute on twisted homology.** Let `ρ : A ⟶ B` and
`g : A ⟶ Y` be maps of spaces over `X`, and let `e : B ⟶ Y` be a map over `X` up to a homotopy `G`
from `e ≫ y` to `b`, with a homotopy `H` from `ρ ≫ e` to `g`. Suppose the two homotopies agree over
`X`: at every point `x` of `A`, the image under `y` of the path traced by `H` is homotopic to the
path traced by `G` at `ρ x`. Then on twisted homology the map induced by `g` is the map induced by
`ρ` followed by the map induced by `e`, with coefficients identified along `G`. -/
theorem homologyMap_overTwistedChainComplexMap_eq_comp {Y : TopCat.{v}} {y : Y ⟶ X}
    (ρ : A ⟶ B) (hρ : ρ ≫ b = a) (g : A ⟶ Y) (hg : g ≫ y = a) (e : B ⟶ Y)
    (G : TopCat.Homotopy (e ≫ y) b) (H : TopCat.Homotopy (ρ ≫ e) g)
    (hGH : ∀ x : A, ((H.evalAt x).map y.hom.continuous).Homotopic
      ((G.evalAt (ρ x)).cast rfl (ConcreteCategory.congr_hom (hg.trans hρ.symm) x)))
    (k : ℕ) :
    HomologicalComplex.homologyMap (overTwistedChainComplexMap L g hg) k =
      HomologicalComplex.homologyMap (overTwistedChainComplexMap L ρ hρ) k ≫
        twistedHomologyCoefficientMap
          (((pullbackCompIso e.hom y.hom).app L).symm ≪≫ (pullbackHomotopyIso G).app L).inv k ≫
        twistedHomologyMap e ((pullback y.hom).obj L) k := by
  subst hρ
  have hH := TopCat.Homotopy.twistedHomologyMap_eq_comp H ((pullback y.hom).obj L) k
  rw [twistedHomologyMap_comp] at hH
  have hρβ := twistedHomologyMap_naturality ρ
    (((pullbackCompIso e.hom y.hom).app L).symm ≪≫ (pullbackHomotopyIso G).app L).hom k
  have key := pullbackHomotopyIso_coherent L ρ g hg e G H hGH
  have hg' : twistedHomologyMap g ((pullback y.hom).obj L) k =
      twistedHomologyCoefficientMap ((pullbackHomotopyIso H).inv.app ((pullback y.hom).obj L)) k ≫
        twistedHomologyCoefficientMap
          ((pullbackCompIso ρ.hom e.hom).hom.app ((pullback y.hom).obj L)) k ≫
        twistedHomologyMap ρ ((pullback e.hom).obj ((pullback y.hom).obj L)) k ≫
        twistedHomologyMap e ((pullback y.hom).obj L) k := by
    rw [hH, ← Iso.app_inv, ← Iso.app_hom, twistedHomologyCoefficientMap_inv_hom_id_assoc]
  have hρ' : twistedHomologyMap ρ ((pullback e.hom).obj ((pullback y.hom).obj L)) k =
      twistedHomologyCoefficientMap ((pullback ρ.hom).map
          (((pullbackCompIso e.hom y.hom).app L).symm ≪≫ (pullbackHomotopyIso G).app L).hom) k ≫
        twistedHomologyMap ρ ((pullback b.hom).obj L) k ≫
        twistedHomologyCoefficientMap
          (((pullbackCompIso e.hom y.hom).app L).symm ≪≫ (pullbackHomotopyIso G).app L).inv k := by
    rw [← reassoc_of% hρβ, twistedHomologyCoefficientMap_hom_inv_id, Category.comp_id]
  rw [overTwistedChainComplexMap, overTwistedChainComplexMap, HomologicalComplex.homologyMap_comp,
    HomologicalComplex.homologyMap_comp]
  -- Fold the homology maps back into the abbreviations `twistedHomologyCoefficientMap` and
  -- `twistedHomologyMap`, the form in which `hg'` and `hρ'` are stated.
  change twistedHomologyCoefficientMap _ k ≫ twistedHomologyMap g _ k =
    (twistedHomologyCoefficientMap _ k ≫ twistedHomologyMap ρ _ k) ≫ _
  rw [hg', hρ', ← key]
  simp only [twistedHomologyCoefficientMap_comp, Category.assoc]

/-- The twisted chains of the spaces over `X`, with coefficients in the pullbacks of `L`. -/
-- Its object part must compute, so that the legs of `overTwistedHomologyCocone` typecheck.
@[expose, simps]
def overTwistedChainComplexFunctor : Over X ⥤ ChainComplex (ModuleCat.{max v w} R) ℕ where
  obj A := ((pullback A.hom.hom).obj L).twistedChainComplex
  map φ := overTwistedChainComplexMap L φ.left (Over.w φ)
  map_id _ := overTwistedChainComplexMap_id L _
  map_comp φ ψ := overTwistedChainComplexMap_comp L _ _ (Over.w φ) (Over.w ψ)

/-- The twisted homology of the spaces over `X`, with coefficients in the pullbacks of `L`. -/
abbrev overTwistedHomologyFunctor (k : ℕ) : Over X ⥤ ModuleCat.{max v w} R :=
  overTwistedChainComplexFunctor L ⋙ HomologicalComplex.homologyFunctor _ _ k

/-- The maps from the twisted homology of the spaces over `X` to the twisted homology of `X`. -/
@[expose, simps]
def overTwistedHomologyCocone (k : ℕ) : Cocone (overTwistedHomologyFunctor L k) where
  pt := L.twistedHomology k
  ι :=
    { app A := twistedHomologyMap A.hom L k
      naturality _ _ φ :=
        (homologyMap_overTwistedChainComplexMap_twistedHomologyMap L φ.left (Over.w φ) k).trans
          (Category.comp_id _).symm }

end TauCeti.LocalCoefficientSystem
