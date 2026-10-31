/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.ConcreteCategory
public import Mathlib.Topology.Separation.Hausdorff
public import TauCeti.Topology.Sheaves.Stalks

/-!
# Stalks of a direct image and the stalks over a fiber

Let `f : X ⟶ Y` be a continuous map and `F` a presheaf on `X`. For every point `y : Y` there is a
canonical map `fiberStalkMap C f F y : (f_* F)_y ⟶ ∏_{f x = y} F_x` from the stalk of the direct
image at `y` to the product of the stalks of `F` at the points of the fiber over `y`. Its
coordinate at `x` is Mathlib's pushforward stalk map `TopCat.Presheaf.stalkPushforward`, so it
sends the germ at `y` of a section of `F` over `f⁻¹(V)` to the family of its germs at the points of
the fiber (`TopCat.Presheaf.germ_fiberStalkMap_π`). The map needs no hypothesis on `f`.

For a sheaf `F` valued in a concrete category with the usual stalk hypotheses (for example sheaves
of modules or of abelian groups):

* if `f` is a closed map, the map is injective: two germs at `y` that agree at every point of the
  fiber are represented by sections agreeing on an open set `W` containing the fiber, and
  `Y \ f(X \ W)` is an open neighbourhood of `y` whose preimage lies in `W`;
* if moreover `X` is Hausdorff and the fiber over `y` is finite, the map is surjective: finitely
  many germs at the fiber points are represented on pairwise disjoint neighbourhoods, glue to a
  section over their union `W`, and restrict to the preimage of `Y \ f(X \ W)`.

Hence the map is an isomorphism for a closed map with finite fibers from a Hausdorff space, and in
particular for a proper map with finite fibers from a Hausdorff space, since proper maps are closed
(`IsProperMap.isClosedMap`). No separation or local compactness of `Y`, and no local compactness of
`X`, is needed. Hausdorffness of `X` cannot be dropped: for the line with two origins folded onto
the real line and the constant sheaf, the map at `0` is the diagonal `ℤ ⟶ ℤ²`.

## Main definitions and results

* `TopCat.Presheaf.fiberStalkMap C f F y`: the canonical map `(f_* F)_y ⟶ ∏_{f x = y} F_x`.
* `TopCat.Presheaf.germ_fiberStalkMap_π`: its coordinates on germs.
* `TopCat.Presheaf.fiberStalkMap_naturality`: naturality in the presheaf.
* `TopCat.Presheaf.fiberStalkMap_injective`: injectivity for closed maps.
* `TopCat.Presheaf.fiberStalkMap_surjective`: surjectivity for closed maps from a Hausdorff space
  at points with finite fibers.
* `TopCat.Presheaf.isIso_fiberStalkMap`: under both sets of hypotheses the map is an isomorphism.

## References

* J. Pardon, *An algebraic approach to virtual fundamental cycles on moduli spaces of
  pseudo-holomorphic curves*, Geom. Topol. 20 (2016), arXiv:1309.2370v6, Appendix A, Lemma A.3.2
  and the proof of Lemma A.4.8 (stated there for locally compact Hausdorff spaces).
-/

public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

open scoped AlgebraicGeometry

universe v u

noncomputable section

namespace TopCat.Presheaf

variable (C : Type u) [Category.{v} C] [HasColimits.{v} C] [HasProducts.{v} C]
  {X Y : TopCat.{v}}

/-- The canonical map from the stalk at `y` of the direct image `f_* F` to the product of the
stalks of `F` at the points of the fiber of `f` over `y`. Its coordinate at `x` is the pushforward
stalk map `(f_* F)_{f x} ⟶ F_x`, transported along `f x = y`. -/
def fiberStalkMap (f : X ⟶ Y) (F : X.Presheaf C) (y : Y) :
    (f _* F).stalk y ⟶ ∏ᶜ fun x : { x : X // f x = y } ↦ F.stalk x.1 :=
  Pi.lift fun x ↦ eqToHom (congrArg (f _* F).stalk x.2.symm) ≫ F.stalkPushforward C f x.1

variable {C}

/-- The coordinate of `fiberStalkMap` at a point `x` of the fiber is the pushforward stalk map,
transported along `f x = y`. -/
@[reassoc]
theorem fiberStalkMap_π (f : X ⟶ Y) (F : X.Presheaf C) (y : Y) (x : { x : X // f x = y }) :
    fiberStalkMap C f F y ≫ Pi.π _ x =
      eqToHom (congrArg (f _* F).stalk x.2.symm) ≫ F.stalkPushforward C f x.1 := by
  simp [fiberStalkMap]

/-- `fiberStalkMap` sends the germ at `y` of a section of `f_* F` over `U`, that is, of a section
of `F` over `f⁻¹(U)`, to its germs at the points of the fiber over `y`. -/
@[reassoc (attr := simp), elementwise (attr := simp)]
theorem germ_fiberStalkMap_π (f : X ⟶ Y) (F : X.Presheaf C) {y : Y} (U : Opens Y) (hy : y ∈ U)
    (x : { x : X // f x = y }) :
    (f _* F).germ U y hy ≫ fiberStalkMap C f F y ≫ Pi.π _ x =
      F.germ ((Opens.map f).obj U) x.1 (by simpa [x.2] using hy) := by
  obtain ⟨x, rfl⟩ := x
  simp [fiberStalkMap_π]

/-- `fiberStalkMap` is natural in the presheaf. -/
@[reassoc]
theorem fiberStalkMap_naturality (f : X ⟶ Y) {F G : X.Presheaf C} (α : F ⟶ G) (y : Y) :
    (stalkFunctor C y).map ((pushforward C f).map α) ≫ fiberStalkMap C f G y =
      fiberStalkMap C f F y ≫ Limits.Pi.map fun x ↦ (stalkFunctor C x.1).map α := by
  refine Pi.hom_ext _ _ fun x ↦ ?_
  obtain ⟨x, rfl⟩ := x
  have hF := fiberStalkMap_π f F (f x) ⟨x, rfl⟩
  have hG := fiberStalkMap_π f G (f x) ⟨x, rfl⟩
  simp only [eqToHom_refl, Category.id_comp] at hF hG
  -- These composites pass through both `P.stalk x` and `(stalkFunctor C x).obj P`, which agree
  -- only after unfolding `stalkFunctor`, so `rw` and `simp` cannot reassociate them; the
  -- associativity steps are therefore chained as terms.
  refine ((Category.assoc _ _ _).trans (congrArg _ hG)).trans
    ((TauCeti.Topology.stalkPushforward_naturality f α x).trans ?_)
  exact ((Category.assoc _ _ _).trans ((congrArg _
    (Pi.map_π (fun x' : { x' : X // f x' = f x } ↦ (stalkFunctor C x'.1).map α) ⟨x, rfl⟩)).trans
    ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ (stalkFunctor C x).map α) hF)))).symm

section Concrete

variable {FC : C → C → Type*} {CC : C → Type v} [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)]
  [instCC : ConcreteCategory.{v} C FC] [PreservesFilteredColimits (forget C)] [HasLimits C]
  [PreservesLimits (forget C)] [(forget C).ReflectsIsomorphisms]

/-- For a closed map `f`, two germs at `y` of the direct image of a sheaf that agree at every point
of the fiber over `y` are equal. -/
theorem fiberStalkMap_injective (F : X.Sheaf C) {f : X ⟶ Y} (hf : IsClosedMap f) (y : Y) :
    Function.Injective (fiberStalkMap C f F.presheaf y) := by
  intro a b hab
  obtain ⟨U, hyU, s, rfl⟩ := (f _* F.presheaf).exists_germ_eq a
  obtain ⟨V, hyV, t, rfl⟩ := (f _* F.presheaf).exists_germ_eq b
  -- At each point `x` of the fiber the two sections agree on a neighbourhood `W x` of `x`.
  have hgerm (x : { x : X // f x = y }) :
      F.presheaf.germ ((Opens.map f).obj U) x.1 (by simpa [x.2] using hyU) s =
        F.presheaf.germ ((Opens.map f).obj V) x.1 (by simpa [x.2] using hyV) t := by
    simpa using congrArg
      (ConcreteCategory.hom (Pi.π (fun x : { x : X // f x = y } ↦ F.presheaf.stalk x.1) x)) hab
  choose W hxW iU iV heq using fun x ↦ F.presheaf.germ_eq x.1 _ _ s t (hgerm x)
  -- Since `f` is closed, `y` has an open neighbourhood `V'` whose preimage lies in `⨆ x, W x`.
  obtain ⟨V', hV', hV'o, hyV'⟩ := eventually_nhds_iff.mp <| hf.eventually_nhds_fiber
    (p := (· ∈ ⨆ x, W x)) y fun x hx ↦ (⨆ x, W x).isOpen.mem_nhds <|
      Opens.mem_iSup.mpr ⟨⟨x, hx⟩, hxW ⟨x, hx⟩⟩
  let N := U ⊓ V ⊓ ⟨V', hV'o⟩
  have hyN : y ∈ N := ⟨⟨hyU, hyV⟩, hyV'⟩
  rw [← (f _* F.presheaf).germ_res_apply (homOfLE (inf_le_left.trans inf_le_left)) y hyN s,
    ← (f _* F.presheaf).germ_res_apply (homOfLE (inf_le_left.trans inf_le_right)) y hyN t]
  congr 1
  refine section_ext F ((Opens.map f).obj N) _ _ fun z hz ↦ ?_
  obtain ⟨x, hzx⟩ := Opens.mem_iSup.mp (hV' _ hz.2 z rfl)
  simpa using congrArg (F.presheaf.germ (W x) z hzx) (heq x)

/-- For a closed map `f` from a Hausdorff space, every family of germs of a sheaf at the finitely
many points of a fiber over `y` is the image of a germ of the direct image at `y`. -/
theorem fiberStalkMap_surjective [T2Space X] (F : X.Sheaf C) {f : X ⟶ Y} (hf : IsClosedMap f)
    {y : Y} (hfin : (f ⁻¹' {y}).Finite) :
    Function.Surjective (fiberStalkMap C f F.presheaf y) := by
  intro g
  -- Represent each coordinate of `g` by a section over a neighbourhood of its point, and choose
  -- pairwise disjoint open neighbourhoods `D x` of the fiber points.
  choose W hxW t ht using fun x : { x : X // f x = y } ↦
    F.presheaf.exists_germ_eq (Pi.π (fun x : { x : X // f x = y } ↦ F.presheaf.stalk x.1) x g)
  obtain ⟨D, hD, hdisj⟩ := hfin.t2_separation
  let O (x : { x : X // f x = y }) : Opens X := W x ⊓ ⟨D x, (hD x).2⟩
  have hxO (x : { x : X // f x = y }) : x.1 ∈ O x := ⟨hxW x, (hD x).1⟩
  let t' (x : { x : X // f x = y }) := F.presheaf.map (homOfLE inf_le_left : O x ⟶ W x).op (t x)
  -- Sections over pairwise disjoint opens are compatible, so they glue over `⨆ x, O x`.
  have hcompat : IsCompatible F.presheaf O t' := by
    intro i j
    obtain rfl | hij := eq_or_ne i j
    · rfl
    have hD : Disjoint (D i) (D j) := hdisj i.2 j.2 fun h ↦ hij (Subtype.ext h)
    exact section_ext F _ _ _ fun z hz ↦ (Set.disjoint_left.mp hD hz.1.2 hz.2.2).elim
  obtain ⟨s, hs, -⟩ := F.existsUnique_gluing O t' hcompat
  -- Since `f` is closed, `y` has an open neighbourhood `V` whose preimage lies in `⨆ x, O x`.
  obtain ⟨V, hV, hVo, hyV⟩ := eventually_nhds_iff.mp <| hf.eventually_nhds_fiber
    (p := (· ∈ ⨆ x, O x)) y fun x hx ↦ (⨆ x, O x).isOpen.mem_nhds <|
      Opens.mem_iSup.mpr ⟨⟨x, hx⟩, hxO ⟨x, hx⟩⟩
  have hVO : (Opens.map f).obj ⟨V, hVo⟩ ≤ ⨆ x, O x := fun z hz ↦ hV _ hz z rfl
  refine ⟨(f _* F.presheaf).germ ⟨V, hVo⟩ y hyV (F.presheaf.map (homOfLE hVO).op s), ?_⟩
  refine (Concrete.productEquiv _).injective (funext fun x ↦ ?_)
  rw [Concrete.productEquiv_apply_apply, Concrete.productEquiv_apply_apply, ← ht x,
    germ_fiberStalkMap_π_apply, germ_res_apply]
  simpa [t'] using congrArg (F.presheaf.germ (O x) x.1 (hxO x)) (hs x)

include instCC in
/-- For a closed map `f` from a Hausdorff space with finite fiber over `y`, the canonical map from
the stalk at `y` of the direct image of a sheaf to the product of the stalks over the fiber is an
isomorphism. This applies to proper maps with finite fibers, by `IsProperMap.isClosedMap`. -/
theorem isIso_fiberStalkMap [T2Space X] (F : X.Sheaf C) {f : X ⟶ Y} (hf : IsClosedMap f)
    {y : Y} (hfin : (f ⁻¹' {y}).Finite) :
    IsIso (fiberStalkMap C f F.presheaf y) :=
  (ConcreteCategory.isIso_iff_bijective _).mpr
    ⟨fiberStalkMap_injective F hf y, fiberStalkMap_surjective F hf hfin⟩

end Concrete

end TopCat.Presheaf
