/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Cohomology.Pullback
public import TauCeti.CategoryTheory.Sites.SheafCohomology.Pullback.Comp
import TauCeti.AlgebraicGeometry.Modules.Pullback.Basic

/-!
# Pullback on the cohomology of opens along a composite

Let `a : Z ⟶ W` and `b : W ⟶ X` be morphisms of schemes and `M` a sheaf of modules on `X`. This
file proves that pullback on the cohomology of opens
(`AlgebraicGeometry.Scheme.Hom.cohomologyOnPullback`) is functorial: pulling back `Hⁿ(U, M)`
along `a ≫ b` is pulling back along `b` and then along `a`, followed by the isomorphism
`a^* b^* M ≅ (a ≫ b)^* M` of `Scheme.Modules.pullbackComp`.

At the level of underlying abelian sheaves this is the compatibility of the comparison
`g⁻¹ M ⟶ g^* M` (`AlgebraicGeometry.Scheme.Hom.toSheafPullbackComparison`) with composition, and
the functoriality of pullback of cohomology over objects of a site
(`CategoryTheory.Sheaf.H'.pullback_comp_pullback_sheafPullback`).

## Main declarations

* `AlgebraicGeometry.Scheme.Hom.toSheafPullbackComparison_comp`: the comparison `g⁻¹ M ⟶ g^* M`
  for `a ≫ b` is that for `b` followed by that for `a`;
* `AlgebraicGeometry.Scheme.Hom.cohomologyOnPullback_comp`: pullback on cohomology along a
  composite;
* `AlgebraicGeometry.Scheme.Hom.cohomologyOnPullback_comp_cohomologyOnPullback_of_comp_eq`:
  pullback on cohomology around a commutative square `a ≫ b = a' ≫ b'`, with the restriction
  along `AlgebraicGeometry.Scheme.Hom.preimage_eq_of_comp_eq`;
* `AlgebraicGeometry.Scheme.Hom.cohomologyOnPullback_cohomologyOnRes_cohomologyOnPullback_ι`:
  the case of the square `g.resLE U U' hle ≫ U.ι = U'.ι ≫ g` of open subschemes, comparing
  pullback along `g` with pullback along its restriction `U' ⟶ U`.
-/

public section

open CategoryTheory Limits TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules

universe u

noncomputable section

namespace AlgebraicGeometry.Scheme.Hom

variable {X W Z : Scheme.{u}}

/-- The unit of `(a ≫ b)^* ⊣ (a ≫ b)_*` on underlying abelian sheaves, written through the units of
the inverse images along `b` and `a` and the comparisons `g⁻¹ ⟶ g^*` for `b` and `a`. -/
private lemma toSheaf_map_unit_comp (a : Z ⟶ W) (b : W ⟶ X) (M : X.Modules) :
    (toSheaf X).map ((Scheme.Modules.pullbackPushforwardAdjunction (a ≫ b)).unit.app M) =
      ((Opens.map b.base).sheafAdjunctionContinuous AddCommGrpCat.{u}
          (Opens.grothendieckTopology X) (Opens.grothendieckTopology W)).unit.app
          ((toSheaf X).obj M) ≫
        ((Opens.map b.base).sheafPushforwardContinuous AddCommGrpCat.{u}
          (Opens.grothendieckTopology X) (Opens.grothendieckTopology W)).map
          (((Opens.map a.base).sheafAdjunctionContinuous AddCommGrpCat.{u}
            (Opens.grothendieckTopology W) (Opens.grothendieckTopology Z)).unit.app
            (((Opens.map b.base).sheafPullback AddCommGrpCat.{u}
              (Opens.grothendieckTopology X) (Opens.grothendieckTopology W)).obj
              ((toSheaf X).obj M))) ≫
        ((Opens.map a.base).sheafPushforwardContinuous AddCommGrpCat.{u}
            (Opens.grothendieckTopology W) (Opens.grothendieckTopology Z) ⋙
          (Opens.map b.base).sheafPushforwardContinuous AddCommGrpCat.{u}
            (Opens.grothendieckTopology X) (Opens.grothendieckTopology W)).map
          (((Opens.map a.base).sheafPullback AddCommGrpCat.{u} (Opens.grothendieckTopology W)
            (Opens.grothendieckTopology Z)).map ((toSheafPullbackComparison b).app M) ≫
          (toSheafPullbackComparison a).app ((Scheme.Modules.pullback b).obj M) ≫
          (toSheaf Z).map ((Scheme.Modules.pullbackComp a b).hom.app M)) := by
  have ha := toSheafPullbackComparison_unit a ((Scheme.Modules.pullback b).obj M)
  have hb := toSheafPullbackComparison_unit b M
  have hc := Scheme.Modules.unit_comp_pushforward_map_pullbackComp_inv_app a b M
  have hu : (Scheme.Modules.pullbackPushforwardAdjunction (a ≫ b)).unit.app M =
      (Scheme.Modules.pullbackPushforwardAdjunction b).unit.app M ≫
        (Scheme.Modules.pushforward b).map
          ((Scheme.Modules.pullbackPushforwardAdjunction a).unit.app
            ((Scheme.Modules.pullback b).obj M)) ≫
        (Scheme.Modules.pushforwardComp a b).hom.app _ ≫
        (Scheme.Modules.pushforward (a ≫ b)).map
          ((Scheme.Modules.pullbackComp a b).hom.app M) := by
    rw [← reassoc_of% hc, ← Functor.map_comp, Iso.inv_hom_id_app]
    simp
  rw [hu]
  simp only [Functor.map_comp]
  rw [reassoc_of% hb]
  refine (Category.assoc _ _ _).trans (congrArg
    (((Opens.map b.base).sheafAdjunctionContinuous AddCommGrpCat.{u}
      (Opens.grothendieckTopology X) (Opens.grothendieckTopology W)).unit.app
        ((toSheaf X).obj M) ≫ ·) ?_)
  have nat := congrArg ((Opens.map b.base).sheafPushforwardContinuous AddCommGrpCat.{u}
    (Opens.grothendieckTopology X) (Opens.grothendieckTopology W)).map
    (((Opens.map a.base).sheafAdjunctionContinuous AddCommGrpCat.{u}
      (Opens.grothendieckTopology W) (Opens.grothendieckTopology Z)).unit.naturality
        ((toSheafPullbackComparison b).app M))
  simp only [Functor.comp_map, Functor.id_map, Functor.map_comp] at nat
  simp only [Functor.comp_map]
  rw [← reassoc_of% nat]
  refine congrArg (((Opens.map b.base).sheafPushforwardContinuous AddCommGrpCat.{u}
    (Opens.grothendieckTopology X) (Opens.grothendieckTopology W)).map
      ((toSheafPullbackComparison b).app M) ≫ ·) ?_
  -- The pushforward along `a ≫ b` is the composite of the pushforwards, definitionally.
  have e : (toSheaf X).map ((Scheme.Modules.pushforward b).map
        ((Scheme.Modules.pullbackPushforwardAdjunction a).unit.app
          ((Scheme.Modules.pullback b).obj M)) ≫
        (Scheme.Modules.pushforwardComp a b).hom.app _) =
      ((Opens.map b.base).sheafPushforwardContinuous AddCommGrpCat.{u}
        (Opens.grothendieckTopology X) (Opens.grothendieckTopology W)).map
        ((toSheaf W).map ((Scheme.Modules.pullbackPushforwardAdjunction a).unit.app
          ((Scheme.Modules.pullback b).obj M))) :=
    congrArg (toSheaf X).map (Category.comp_id _)
  refine (congrArg (· ≫ _) e).trans ?_
  rw [ha]
  have h0 : (toSheaf X).map ((Scheme.Modules.pushforwardComp a b).hom.app
      ((Scheme.Modules.pullback a).obj ((Scheme.Modules.pullback b).obj M))) = 𝟙 _ :=
    CategoryTheory.Functor.map_id _ _
  refine (congrArg (_ ≫ ·) ((congrArg (· ≫ _) h0).trans (Category.id_comp _))).trans ?_
  refine (congrArg (· ≫ _) (Functor.map_comp _ _ _)).trans ((Category.assoc _ _ _).trans ?_)
  refine congrArg (_ ≫ _ ≫ ·) ?_
  ext U x
  rfl

/-- The comparison `g⁻¹ M ⟶ g^* M` for `a ≫ b`, after the isomorphism `a⁻¹ b⁻¹ ≅ (a ≫ b)⁻¹` of
inverse images of abelian sheaves, is the comparison for `b` followed by the comparison for `a`
and the isomorphism `a^* b^* M ≅ (a ≫ b)^* M`. -/
lemma toSheafPullbackComparison_comp (a : Z ⟶ W) (b : W ⟶ X) (M : X.Modules) :
    (Functor.sheafPullbackComp (Opens.map b.base) (Opens.map a.base) AddCommGrpCat.{u}
        (Opens.grothendieckTopology X) (Opens.grothendieckTopology W)
        (Opens.grothendieckTopology Z)).hom.app ((toSheaf X).obj M) ≫
      (toSheafPullbackComparison (a ≫ b)).app M =
    ((Opens.map a.base).sheafPullback AddCommGrpCat.{u} (Opens.grothendieckTopology W)
        (Opens.grothendieckTopology Z)).map ((toSheafPullbackComparison b).app M) ≫
      (toSheafPullbackComparison a).app ((Scheme.Modules.pullback b).obj M) ≫
      (toSheaf Z).map ((Scheme.Modules.pullbackComp a b).hom.app M) := by
  let adj := ((Opens.map b.base).sheafAdjunctionContinuous AddCommGrpCat.{u}
    (Opens.grothendieckTopology X) (Opens.grothendieckTopology W)).comp
    ((Opens.map a.base).sheafAdjunctionContinuous AddCommGrpCat.{u}
      (Opens.grothendieckTopology W) (Opens.grothendieckTopology Z))
  apply (adj.homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Adjunction.comp_unit_app]
  have hL := Functor.sheafAdjunctionContinuous_comp_unit_app (Opens.grothendieckTopology X)
    (Opens.grothendieckTopology W) (Opens.grothendieckTopology Z) (Opens.map b.base)
    (Opens.map a.base) AddCommGrpCat.{u} ((toSheaf X).obj M)
  have hab := toSheafPullbackComparison_unit (a ≫ b) M
  refine (?_ : _ = (toSheaf X).map
    ((Scheme.Modules.pullbackPushforwardAdjunction (a ≫ b)).unit.app M)).trans ?_
  · rw [hab]
    refine Eq.trans ?_ (congrArg (· ≫ _) hL.symm)
    simp only [Functor.map_comp, Category.assoc]
    rfl
  · exact toSheaf_map_unit_comp a b M

private lemma cohomologyOnPullback_eq (g : W ⟶ X) (M : X.Modules) (n : ℕ) (U : X.Opens) :
    g.cohomologyOnPullback M n U =
      (CategoryTheory.Sheaf.H'.pullback
        ((Opens.map g.base).sheafPullback AddCommGrpCat.{u}
          (Opens.grothendieckTopology X) (Opens.grothendieckTopology W))
        ((Opens.map g.base).freeYonedaSheafToSheafPullback _ _) ((toSheaf X).obj M) n (𝟙 _) ≫
      ((CategoryTheory.Sheaf.cohomologyPresheafFunctor _ n).map
        ((toSheafPullbackComparison g).app M)).app (op (g ⁻¹ᵁ U)) :
        cohomologyOn M n U ⟶ cohomologyOn ((Scheme.Modules.pullback g).obj M) n (g ⁻¹ᵁ U)) :=
  AddCommGrpCat.ext fun x ↦ g.cohomologyOnPullback_apply M n U x

/-- **Pullback on cohomology along a composite.** Pulling back the cohomology of an open along
`a ≫ b` is pulling back along `b` and then along `a`, followed by the isomorphism
`a^* b^* M ≅ (a ≫ b)^* M` on coefficients. -/
@[reassoc]
theorem cohomologyOnPullback_comp (a : Z ⟶ W) (b : W ⟶ X) (M : X.Modules) (n : ℕ)
    (U : X.Opens) :
    (a ≫ b).cohomologyOnPullback M n U =
      b.cohomologyOnPullback M n U ≫
        a.cohomologyOnPullback ((Scheme.Modules.pullback b).obj M) n (b ⁻¹ᵁ U) ≫
          cohomologyOnMap ((Scheme.Modules.pullbackComp a b).hom.app M) n (a ⁻¹ᵁ b ⁻¹ᵁ U) := by
  rw [cohomologyOnPullback_eq, cohomologyOnPullback_eq, cohomologyOnPullback_eq]
  refine (congrArg (· ≫ _) (CategoryTheory.Sheaf.H'.pullback_comp_pullback_sheafPullback
    (J := Opens.grothendieckTopology X) (K := Opens.grothendieckTopology W)
    (L := Opens.grothendieckTopology Z) (Opens.map b.base) (Opens.map a.base)
    ((toSheaf X).obj M) n (𝟙 _) (𝟙 _)).symm).trans ?_
  -- Read every factor through the packaged forgetful functors, so that the composite is
  -- well typed and the naturality lemmas apply.
  change (_ ≫ _ ≫ _) ≫ _ = CategoryTheory.Sheaf.H'.pullback
      ((Opens.map b.base).sheafPullback AddCommGrpCat.{u}
        (Opens.grothendieckTopology X) (Opens.grothendieckTopology W))
      ((Opens.map b.base).freeYonedaSheafToSheafPullback _ _) ((toSheaf X).obj M) n (𝟙 _) ≫
    ((CategoryTheory.Sheaf.cohomologyPresheafFunctor _ n).map
      ((toSheafPullbackComparison b).app M)).app (op (b ⁻¹ᵁ U)) ≫
    CategoryTheory.Sheaf.H'.pullback
      ((Opens.map a.base).sheafPullback AddCommGrpCat.{u}
        (Opens.grothendieckTopology W) (Opens.grothendieckTopology Z))
      ((Opens.map a.base).freeYonedaSheafToSheafPullback _ _)
      ((Scheme.Modules.pullback b ⋙ toSheaf W).obj M) n (𝟙 _) ≫
    ((CategoryTheory.Sheaf.cohomologyPresheafFunctor _ n).map
      ((toSheafPullbackComparison a).app ((Scheme.Modules.pullback b).obj M))).app
        (op (a ⁻¹ᵁ b ⁻¹ᵁ U)) ≫
    ((CategoryTheory.Sheaf.cohomologyPresheafFunctor _ n).map
      ((toSheaf Z).map ((Scheme.Modules.pullbackComp a b).hom.app M))).app
        (op (a ⁻¹ᵁ b ⁻¹ᵁ U))
  rw [CategoryTheory.Sheaf.H'.pullback_naturality_assoc]
  erw [Category.assoc, Category.assoc, ← NatTrans.comp_app, ← Functor.map_comp,
    toSheafPullbackComparison_comp, Functor.map_comp, Functor.map_comp, NatTrans.comp_app,
    NatTrans.comp_app]
  rfl

/-- Pullback on cohomology along equal morphisms `f = g`: pulling back along `f`, identifying
`f^* M` with `g^* M` and restricting from `f⁻¹ U` to `g⁻¹ U = f⁻¹ U` is pulling back along `g`. -/
lemma cohomologyOnPullback_congr {f g : Z ⟶ X} (h : f = g) (M : X.Modules) (n : ℕ)
    (U : X.Opens) :
    f.cohomologyOnPullback M n U ≫
        cohomologyOnMap ((Scheme.Modules.pullbackCongr h).hom.app M) n _ ≫
          cohomologyOnRes _ n (congrArg (· ⁻¹ᵁ U) h).ge =
      g.cohomologyOnPullback M n U := by
  subst h
  simp [Scheme.Modules.pullbackCongr]

/-- Maps of coefficients commute with restriction. -/
@[reassoc]
private lemma cohomologyOnRes_comp_cohomologyOnMap {Y : Scheme.{u}} {M N : Y.Modules}
    (f : M ⟶ N) (n : ℕ) {U V : Y.Opens} (h : U ≤ V) :
    cohomologyOnRes M n h ≫ cohomologyOnMap f n U =
      cohomologyOnMap f n V ≫ cohomologyOnRes N n h :=
  AddCommGrpCat.ext fun x ↦ cohomologyOnMap_cohomologyOnRes f n h x

/-- For a commutative square `g' ≫ f = f' ≫ g`, preimages of opens along its two sides agree. -/
lemma preimage_eq_of_comp_eq {X' Y Y' : Scheme.{u}} {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'}
    {g' : X' ⟶ X} (h : g' ≫ f = f' ≫ g) (V : Y.Opens) : f' ⁻¹ᵁ g ⁻¹ᵁ V = g' ⁻¹ᵁ f ⁻¹ᵁ V :=
  (congrArg (fun φ : X' ⟶ Y ↦ φ ⁻¹ᵁ V) h).symm

/-- **Pullback on cohomology around a commutative square.** For `a ≫ b = a' ≫ b'`, pulling back
along `b` and then `a`, identifying `a^* b^* M` with `a'^* b'^* M` and restricting to
`a'⁻¹ b'⁻¹ U = a⁻¹ b⁻¹ U` is pulling back along `b'` and then `a'`. -/
@[reassoc]
theorem cohomologyOnPullback_comp_cohomologyOnPullback_of_comp_eq {W' : Scheme.{u}}
    {a : Z ⟶ W} {b : W ⟶ X} {a' : Z ⟶ W'} {b' : W' ⟶ X} (h : a ≫ b = a' ≫ b')
    (M : X.Modules) (n : ℕ) (U : X.Opens) :
    b.cohomologyOnPullback M n U ≫
        a.cohomologyOnPullback ((Scheme.Modules.pullback b).obj M) n (b ⁻¹ᵁ U) ≫
          cohomologyOnMap ((Scheme.Modules.pullbackComp a b).hom.app M ≫
            (Scheme.Modules.pullbackCongr h).hom.app M ≫
              (Scheme.Modules.pullbackComp a' b').inv.app M) n (a ⁻¹ᵁ b ⁻¹ᵁ U) ≫
            cohomologyOnRes _ n (preimage_eq_of_comp_eq h U).le =
      b'.cohomologyOnPullback M n U ≫
        a'.cohomologyOnPullback ((Scheme.Modules.pullback b').obj M) n (b' ⁻¹ᵁ U) := by
  have hres := (cohomologyOnRes_comp_cohomologyOnMap
    ((Scheme.Modules.pullbackComp a' b').inv.app M) n (preimage_eq_of_comp_eq h U).le).symm
  have hc : ((a ≫ b).cohomologyOnPullback M n U ≫
      cohomologyOnMap ((Scheme.Modules.pullbackCongr h).hom.app M) n (a ⁻¹ᵁ b ⁻¹ᵁ U)) ≫
        cohomologyOnRes _ n (preimage_eq_of_comp_eq h U).le =
      (a' ≫ b').cohomologyOnPullback M n U :=
    (Category.assoc _ _ _).trans (cohomologyOnPullback_congr h M n U)
  calc _ = (b.cohomologyOnPullback M n U ≫
        a.cohomologyOnPullback ((Scheme.Modules.pullback b).obj M) n (b ⁻¹ᵁ U) ≫
          cohomologyOnMap ((Scheme.Modules.pullbackComp a b).hom.app M) n (a ⁻¹ᵁ b ⁻¹ᵁ U)) ≫
        cohomologyOnMap ((Scheme.Modules.pullbackCongr h).hom.app M) n (a ⁻¹ᵁ b ⁻¹ᵁ U) ≫
          cohomologyOnMap ((Scheme.Modules.pullbackComp a' b').inv.app M) n
            (a ⁻¹ᵁ b ⁻¹ᵁ U) ≫ cohomologyOnRes _ n (preimage_eq_of_comp_eq h U).le := by
        simp only [cohomologyOnMap_comp, Category.assoc]
    _ = (((a ≫ b).cohomologyOnPullback M n U ≫
        cohomologyOnMap ((Scheme.Modules.pullbackCongr h).hom.app M) n (a ⁻¹ᵁ b ⁻¹ᵁ U)) ≫
          cohomologyOnRes _ n (preimage_eq_of_comp_eq h U).le) ≫
            cohomologyOnMap ((Scheme.Modules.pullbackComp a' b').inv.app M) n
              (a' ⁻¹ᵁ b' ⁻¹ᵁ U) := by
        rw [← cohomologyOnPullback_comp, hres]
        exact ((Category.assoc _ _ _).trans (Category.assoc _ _ _)).symm
    _ = _ := by
        rw [hc, cohomologyOnPullback_comp, Category.assoc, Category.assoc,
          ← cohomologyOnMap_comp, Iso.hom_inv_id_app, cohomologyOnMap_id]
        erw [Category.comp_id]

/-- **Pullback on cohomology and open subschemes.** Let `g : X' ⟶ X`, and let `U'` and `U` be
opens of `X'` and `X` with `U' ≤ g⁻¹ U`, so that `g` restricts to `g.resLE U U' hle : U' ⟶ U`.
Pulling back from `U` to `g⁻¹ U` along `g`, restricting to `U'` and pulling back to the open
subscheme `U'` is pulling back to the open subscheme `U` and then along `g.resLE U U' hle`,
followed by the identification `(g.resLE U U' hle)^* (M|_U) ≅ (g^* M)|_{U'}`. -/
theorem cohomologyOnPullback_cohomologyOnRes_cohomologyOnPullback_ι {X' : Scheme.{u}}
    (g : X' ⟶ X) (M : X.Modules) (n : ℕ) (U : X.Opens) (U' : X'.Opens) (hle : U' ≤ g ⁻¹ᵁ U) :
    g.cohomologyOnPullback M n U ≫ cohomologyOnRes _ n hle ≫
        U'.ι.cohomologyOnPullback ((Scheme.Modules.pullback g).obj M) n U' ≫
          cohomologyOnRes _ n U'.ι_preimage_self.ge =
      U.ι.cohomologyOnPullback M n U ≫ cohomologyOnRes _ n U.ι_preimage_self.ge ≫
        (g.resLE U U' hle).cohomologyOnPullback ((Scheme.Modules.pullback U.ι).obj M) n ⊤ ≫
          cohomologyOnMap ((Scheme.Modules.pullbackComp (g.resLE U U' hle) U.ι).hom.app M ≫
            (Scheme.Modules.pullbackCongr (g.resLE_comp_ι hle)).hom.app M ≫
              (Scheme.Modules.pullbackComp U'.ι g).inv.app M) n ((g.resLE U U' hle) ⁻¹ᵁ ⊤) ≫
            cohomologyOnRes _ n (g.resLE U U' hle).preimage_top.ge := by
  rw [cohomologyOnRes_comp_cohomologyOnPullback_assoc,
    cohomologyOnRes_comp_cohomologyOnPullback_assoc,
    ← cohomologyOnPullback_comp_cohomologyOnPullback_of_comp_eq_assoc (g.resLE_comp_ι hle)]
  rw [cohomologyOnRes_comp_cohomologyOnMap_assoc]
  simp only [cohomologyOnRes_comp]
  rfl

end AlgebraicGeometry.Scheme.Hom
