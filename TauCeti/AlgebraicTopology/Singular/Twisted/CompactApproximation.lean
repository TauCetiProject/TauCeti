/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Twisted.CompactSupport.Basic
public import TauCeti.AlgebraicTopology.Singular.Twisted.HomotopyInvariance.Basic
public import TauCeti.Algebra.Category.ModuleCat.FilteredColimits

/-!
# Twisted homology of a space approximated on compact sets

Let `F` be a diagram of spaces with a cocone `gⱼ : Fⱼ → X`, for instance the spaces `𝓛ʳQ` of closed
broken geodesics with `r` breaks in a closed Riemannian manifold `Q`, mapped into the free loop
space `X = 𝓛Q` by the broken-geodesic maps `geoʳ`, and let `M` be a local coefficient system on
`X`. This file proves that the twisted homology `Hₖ(X; M)` is the colimit of the twisted homology
groups `Hₖ(Fⱼ; gⱼ*M)` when the diagram approximates `X` on compact sets, coherently up to homotopy
(`isColimitWhiskerOverTwistedHomologyCoconeOfCompactApprox`; all declarations of this file are in
the namespace `TauCeti.LocalCoefficientSystem`). It is the local-coefficient form of
`TauCeti.isColimitMapCoconeSingularHomologyOfCompactApprox`.

**Spaces over `X`.** A map `g : A ⟶ B` with `g ≫ b = a` induces a map of twisted chains with
coefficients in the pullbacks `a*M` and `b*M` (`overTwistedChainComplexMap`), functorially in `g`.
So twisted chains and twisted homology are functors on the category `Over X`
(`overTwistedChainComplexFunctor`, `overTwistedHomologyFunctor`), with a cocone to `Hₖ(X; M)`
(`overTwistedHomologyCocone`). The diagram `j ↦ Hₖ(Fⱼ; gⱼ*M)` is this functor read through
`F.toOver X g _ : J ⥤ Over X`.

**The two halves.** As for constant coefficients, a class of `X` lives on a compact set, and so
does a vanishing class:

* if every compact subset `K` of `X` maps to some `Fⱼ` by a map `e` with `gⱼ ∘ e` homotopic to the
  inclusion of `K`, every class of `Hₖ(X; M)` comes from some `Fⱼ`
  (`exists_twistedHomologyMap_eq_of_homotopic`);
* under the coherence condition below, a class of `Fⱼ` vanishing in `X` vanishes in some `Fᵢ`
  (`exists_homologyMap_overTwistedChainComplexMap_eq_zero_of_homotopic`).

With local coefficients a homotopy acts on coefficients by transport along the paths it traces
(`TopCat.Homotopy.twistedHomologyMap_eq_comp`), so the second half needs more than for constant
coefficients. For a compact `K ⊆ Fⱼ` and a compact `K' ⊆ X` containing `gⱼ(K)`, it asks for a map
`e : K' → Fᵢ` with a homotopy `G` from `gᵢ ∘ e` to the inclusion of `K'` and a homotopy `H` on `K`
from `e ∘ gⱼ` to the map `Fⱼ → Fᵢ` of the diagram, which agree over `X`: at every point of `K` the
image under `gᵢ` of the path traced by `H` is homotopic to the path traced by `G`. Transport along
`H` and along `G` then identify the coefficients in the same way. This is the content of
`homologyMap_overTwistedChainComplexMap_eq_comp`: a triangle of spaces over `X` that commutes up to
such coherent homotopies commutes on twisted homology. With constant coefficients transport is
trivial, and `TauCeti.isColimitMapCoconeSingularHomologyOfCompactApprox` needs no such condition.

For broken geodesics, `e` is the sampling of a loop at equally spaced times, `G` straightens its
arcs into geodesic segments, and `H` slides the vertices of a broken geodesic along it.

## Main definitions

* `overTwistedChainComplexMap`: the map of twisted chains induced by a map of spaces over `X`.
* `overTwistedChainComplexFunctor`, `overTwistedHomologyFunctor`: twisted chains and twisted
  homology of spaces over `X`.
* `overTwistedHomologyCocone`: their maps to `Hₖ(X; M)`.

## Main results

* `homologyMap_overTwistedChainComplexMap_eq_comp`: triangles over `X` that commute up to coherent
  homotopies commute on twisted homology.
* `exists_twistedHomologyMap_eq_of_homotopic`: every class of `X` comes from the diagram.
* `exists_homologyMap_overTwistedChainComplexMap_eq_zero_of_homotopic`: a class of the diagram
  vanishing in `X` vanishes further along the diagram.
* `isColimitWhiskerOverTwistedHomologyCoconeOfCompactApprox`: for a filtered diagram, `Hₖ(X; M)` is
  the colimit of the `Hₖ(Fⱼ; gⱼ*M)`.

## References

* M. Abouzaid, *Symplectic cohomology and Viterbo's theorem*, in *Free loop spaces in geometry
  and topology*, IRMA Lect. Math. Theor. Phys. 24 (2015), §11.2, Proposition 11.2.4.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §4.3.
* A. Hatcher, *Algebraic Topology*, Section 3.H, for homology with local coefficients.
-/

public section

noncomputable section

open CategoryTheory Limits

universe u v w

namespace TauCeti.LocalCoefficientSystem

variable {R : Type u} [Ring R] {X : TopCat.{v}} (L : LocalCoefficientSystem.{u, v, max v w} R X)

/-! ### Twisted chains of spaces over `X` -/

section Over

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
  simp only [subsetTwistedChainComplexMap_def, overTwistedChainComplexMap, Iso.trans_hom,
    twistedChainComplexCoefficientMap_comp, Category.assoc]
  rw [← Category.assoc, ← twistedChainComplexCoefficientMap_comp]
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
    rw [hH, ← Category.assoc, ← twistedHomologyCoefficientMap_comp, Iso.inv_hom_id_app,
      twistedHomologyCoefficientMap_id, Category.id_comp]
  have hρ' : twistedHomologyMap ρ ((pullback e.hom).obj ((pullback y.hom).obj L)) k =
      twistedHomologyCoefficientMap ((pullback ρ.hom).map
          (((pullbackCompIso e.hom y.hom).app L).symm ≪≫ (pullbackHomotopyIso G).app L).hom) k ≫
        twistedHomologyMap ρ ((pullback b.hom).obj L) k ≫
        twistedHomologyCoefficientMap
          (((pullbackCompIso e.hom y.hom).app L).symm ≪≫ (pullbackHomotopyIso G).app L).inv k := by
    rw [← reassoc_of% hρβ, ← twistedHomologyCoefficientMap_comp, Iso.hom_inv_id,
      twistedHomologyCoefficientMap_id, Category.comp_id]
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

end Over

/-! ### Spaces approximated on compact sets -/

section Approximation

variable {J : Type*} [Category J] {F : J ⥤ TopCat.{v}} (c : Cocone F)
  (M : LocalCoefficientSystem.{u, v, max v w} R c.pt)

/-- **Twisted classes of an approximated space come from the approximations.** Let `c` be a
cocone over a diagram of spaces such that every compact subset `K` of its apex maps to some space
`F j` of the diagram by a map `e` whose composite with the leg `c.ι.app j` is homotopic to the
inclusion of `K`. Then every class of the twisted homology of the apex, with coefficients in a
local system `M`, is the image of a class of some `F j`, with coefficients in the pullback of
`M`. -/
theorem exists_twistedHomologyMap_eq_of_homotopic
    (happrox : ∀ K : Set c.pt, IsCompact K → ∃ (j : J) (e : C(K, F.obj j)),
      ((c.ι.app j).hom.comp e).Homotopic (ContinuousMap.subtypeVal K))
    {k : ℕ} (x : M.twistedHomology k) :
    ∃ (j : J) (y : ((pullback (c.ι.app j).hom).obj M).twistedHomology k),
      twistedHomologyMap (c.ι.app j) M k y = x := by
  obtain ⟨K, hK, y, rfl⟩ := exists_isCompact_twistedHomologyMap_subtypeVal_eq M x
  obtain ⟨j, e, ⟨H⟩⟩ := happrox K hK
  -- Transport `y` along the homotopy to the coefficients of `e ≫ c.ι.app j`, then push it to `F j`.
  refine ⟨j, twistedHomologyMap (TopCat.ofHom e) ((pullback (c.ι.app j).hom).obj M) k
    (twistedHomologyCoefficientMap
      ((pullbackCompIso (TopCat.ofHom e).hom (c.ι.app j).hom).hom.app M) k
      (twistedHomologyCoefficientMap ((pullbackHomotopyIso H).inv.app M) k y)), ?_⟩
  have hH := TopCat.Homotopy.twistedHomologyMap_eq_comp
    (f := TopCat.ofHom e ≫ c.ι.app j) (g := TopCat.ofHom (ContinuousMap.subtypeVal K)) H M k
  rw [twistedHomologyMap_comp] at hH
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
    hH, ← Category.assoc, ← twistedHomologyCoefficientMap_comp, Iso.inv_hom_id_app,
    twistedHomologyCoefficientMap_id, Category.id_comp]

/-- **Twisted classes vanishing in an approximated space vanish in the approximations.** Let `c`
be a cocone over a diagram of spaces. Suppose that for every compact subset `K` of a space `F j`
of the diagram and every compact subset `K'` of the apex containing the image of `K` under the leg
`c.ι.app j`, there are a morphism `f : j ⟶ i` and a map `e : K' → F i` with a homotopy `G` from
`c.ι.app i ∘ e` to the inclusion of `K'`, and a homotopy `H` on `K` from `e ∘ c.ι.app j` to
`F.map f`, such that at every point `x` of `K` the image of the path traced by `H` in the apex is
homotopic to the path traced by `G`. Then a class of the twisted homology of `F j`, with
coefficients in the pullback of a local system `M` on the apex, which vanishes in the apex already
vanishes in some `F i`. -/
theorem exists_homologyMap_overTwistedChainComplexMap_eq_zero_of_homotopic
    (hcompat : ∀ (j : J) (K : Set (F.obj j)) (K' : Set c.pt), IsCompact K → IsCompact K' →
      ∀ hKK' : Set.MapsTo (c.ι.app j) K K', ∃ (i : J) (f : j ⟶ i) (e : C(K', F.obj i))
        (G : ((c.ι.app i).hom.comp e).Homotopy (ContinuousMap.subtypeVal K'))
        (H : (e.comp ⟨hKK'.restrict, (c.ι.app j).hom.continuous.restrict hKK'⟩).Homotopy
          ((F.map f).hom.comp (ContinuousMap.subtypeVal K))),
        ∀ x : K, ((H.evalAt x).map (c.ι.app i).hom.continuous).Homotopic
          ((G.evalAt ⟨c.ι.app j x, hKK' x.property⟩).cast rfl
            (ConcreteCategory.congr_hom (c.w f) x.val)))
    {k : ℕ} {j : J} (z : ((pullback (c.ι.app j).hom).obj M).twistedHomology k)
    (hz : twistedHomologyMap (c.ι.app j) M k z = 0) :
    ∃ (i : J) (f : j ⟶ i),
      HomologicalComplex.homologyMap (overTwistedChainComplexMap M (F.map f) (c.w f)) k z = 0 := by
  obtain ⟨K, hK, y, rfl⟩ :=
    exists_isCompact_twistedHomologyMap_subtypeVal_eq ((pullback (c.ι.app j).hom).obj M) z
  -- Read `y` as a class of `K` over the apex.
  set y' := twistedHomologyCoefficientMap
    ((pullbackCompIso (TopCat.ofHom (ContinuousMap.subtypeVal K)).hom (c.ι.app j).hom).inv.app M) k
      y
  have hyz : HomologicalComplex.homologyMap
      (overTwistedChainComplexMap M (TopCat.ofHom (ContinuousMap.subtypeVal K)) rfl) k y' =
      twistedHomologyMap (TopCat.ofHom (ContinuousMap.subtypeVal K))
        ((pullback (c.ι.app j).hom).obj M) k y :=
    ConcreteCategory.congr_hom
      (twistedHomologyCoefficientMap_comp_homologyMap_overTwistedChainComplexMap M _ k) y
  -- Its image in the compact set `c.ι.app j '' K` vanishes in the apex.
  have hK₀ : Set.MapsTo (c.ι.app j) K (c.ι.app j '' K) := Set.mapsTo_image _ _
  obtain ⟨K', hK', hK₀K', hw⟩ := exists_isCompact_homologyMap_subsetTwistedChainComplexMap_eq_zero
    M (hK.image (c.ι.app j).hom.continuous)
    (HomologicalComplex.homologyMap (overTwistedChainComplexMap M
      (TopCat.ofHom ⟨hK₀.restrict, (c.ι.app j).hom.continuous.restrict hK₀⟩) rfl) k y')
    (by
      refine (ConcreteCategory.congr_hom
        (homologyMap_overTwistedChainComplexMap_twistedHomologyMap M _ _ k) y').trans ?_
      exact (ConcreteCategory.congr_hom (homologyMap_overTwistedChainComplexMap_twistedHomologyMap M
        (TopCat.ofHom (ContinuousMap.subtypeVal K)) rfl k) y').symm.trans
          ((congrArg _ hyz).trans hz))
  have hKK' : Set.MapsTo (c.ι.app j) K K' := hK₀.mono_right hK₀K'
  obtain ⟨i, f, e, G, H, hGH⟩ := hcompat j K K' hK hK' hKK'
  refine ⟨i, f, ?_⟩
  -- The class `y'` vanishes in `K'`, and the coherent homotopies carry this to `F i`.
  let ρ₀ : TopCat.of K ⟶ TopCat.of ↥(c.ι.app j '' K) :=
    TopCat.ofHom ⟨hK₀.restrict, (c.ι.app j).hom.continuous.restrict hK₀⟩
  let ι₀ : TopCat.of ↥(c.ι.app j '' K) ⟶ TopCat.of K' :=
    TopCat.ofHom (ContinuousMap.inclusion hK₀K')
  have hρ : HomologicalComplex.homologyMap (overTwistedChainComplexMap M
      (a := TopCat.ofHom (ContinuousMap.subtypeVal K) ≫ c.ι.app j)
      (b := TopCat.ofHom (ContinuousMap.subtypeVal K')) (ρ₀ ≫ ι₀) rfl) k y' = 0 := by
    rw [subsetTwistedChainComplexMap_eq_overTwistedChainComplexMap] at hw
    rw [overTwistedChainComplexMap_comp M
      (a := TopCat.ofHom (ContinuousMap.subtypeVal K) ≫ c.ι.app j)
      (b := TopCat.ofHom (ContinuousMap.subtypeVal (c.ι.app j '' K))) ρ₀ ι₀ rfl rfl,
      HomologicalComplex.homologyMap_comp]
    exact hw
  rw [← hyz]
  refine (ConcreteCategory.congr_hom ((HomologicalComplex.homologyMap_comp _ _ k).symm.trans
    (congrArg (HomologicalComplex.homologyMap · k)
      (overTwistedChainComplexMap_comp M (TopCat.ofHom (ContinuousMap.subtypeVal K)) (F.map f)
        rfl (c.w f)).symm)) y').trans ?_
  rw [homologyMap_overTwistedChainComplexMap_eq_comp M
    (a := TopCat.ofHom (ContinuousMap.subtypeVal K) ≫ c.ι.app j)
    (b := TopCat.ofHom (ContinuousMap.subtypeVal K')) (ρ₀ ≫ ι₀) rfl
    (TopCat.ofHom (ContinuousMap.subtypeVal K) ≫ F.map f) _ (TopCat.ofHom e) G H hGH]
  rw [ConcreteCategory.comp_apply, hρ, map_zero]

/-- **Twisted homology of a space approximated on compact sets.** Let `c` be a cocone over a
filtered diagram of spaces which approximates its apex on compact sets, coherently up to homotopy:
the hypotheses of `exists_twistedHomologyMap_eq_of_homotopic` and of
`exists_homologyMap_overTwistedChainComplexMap_eq_zero_of_homotopic`. Then the twisted homology of
the apex, with coefficients in a local system `M`, is the colimit of the twisted homology of the
spaces of the diagram, with coefficients in the pullbacks of `M` along the legs. -/
def isColimitWhiskerOverTwistedHomologyCoconeOfCompactApprox [IsFiltered J]
    (happrox : ∀ K : Set c.pt, IsCompact K → ∃ (j : J) (e : C(K, F.obj j)),
      ((c.ι.app j).hom.comp e).Homotopic (ContinuousMap.subtypeVal K))
    (hcompat : ∀ (j : J) (K : Set (F.obj j)) (K' : Set c.pt), IsCompact K → IsCompact K' →
      ∀ hKK' : Set.MapsTo (c.ι.app j) K K', ∃ (i : J) (f : j ⟶ i) (e : C(K', F.obj i))
        (G : ((c.ι.app i).hom.comp e).Homotopy (ContinuousMap.subtypeVal K'))
        (H : (e.comp ⟨hKK'.restrict, (c.ι.app j).hom.continuous.restrict hKK'⟩).Homotopy
          ((F.map f).hom.comp (ContinuousMap.subtypeVal K))),
        ∀ x : K, ((H.evalAt x).map (c.ι.app i).hom.continuous).Homotopic
          ((G.evalAt ⟨c.ι.app j x, hKK' x.property⟩).cast rfl
            (ConcreteCategory.congr_hom (c.w f) x.val)))
    (k : ℕ) :
    IsColimit ((overTwistedHomologyCocone M k).whisker (F.toOver c.pt c.ι.app c.w)) :=
  ModuleCat.isColimitOfJointlySurjective _
    (fun x ↦ exists_twistedHomologyMap_eq_of_homotopic c M happrox x)
    fun i j xi xj hij ↦ by
      -- Compare the two classes at a common later stage, where their difference vanishes in the
      -- apex.
      let a := IsFiltered.leftToMax i j
      let b := IsFiltered.rightToMax i j
      have hab : twistedHomologyMap (c.ι.app (IsFiltered.max i j)) M k
          (HomologicalComplex.homologyMap (overTwistedChainComplexMap M (F.map a) (c.w a)) k xi -
            HomologicalComplex.homologyMap (overTwistedChainComplexMap M (F.map b) (c.w b)) k xj) =
          0 := by
        rw [map_sub, sub_eq_zero]
        refine ((ConcreteCategory.congr_hom
          (homologyMap_overTwistedChainComplexMap_twistedHomologyMap M _ _ k) xi).trans ?_).trans
            (ConcreteCategory.congr_hom
              (homologyMap_overTwistedChainComplexMap_twistedHomologyMap M _ _ k) xj).symm
        exact hij
      obtain ⟨l, f, hf⟩ :=
        exists_homologyMap_overTwistedChainComplexMap_eq_zero_of_homotopic c M hcompat _ hab
      refine ⟨l, a ≫ f, b ≫ f, ?_⟩
      rw [map_sub, sub_eq_zero] at hf
      rw [Functor.map_comp, Functor.map_comp]
      exact hf

end Approximation

end TauCeti.LocalCoefficientSystem
