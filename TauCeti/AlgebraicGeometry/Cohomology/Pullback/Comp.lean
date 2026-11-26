/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Cohomology.Pullback
public import TauCeti.AlgebraicGeometry.Scheme.Opens
public import TauCeti.CategoryTheory.Sites.SheafCohomology.Pullback.Comp
public import TauCeti.AlgebraicGeometry.Cohomology.Pullback.Opens

/-!
# Pullback on the cohomology of opens along a composite

Let `a : Z ⟶ W` and `b : W ⟶ X` be morphisms of schemes and `M` a sheaf of modules on `X`. This
file proves that pullback on the cohomology of opens
(`AlgebraicGeometry.Scheme.Hom.cohomologyOnPullback`) is functorial: pulling back `Hⁿ(U, M)`
along `a ≫ b` is pulling back along `b` and then along `a`, followed by the isomorphism
`a^* b^* M ≅ (a ≫ b)^* M` of `Scheme.Modules.pullbackComp`.

It also transports a scalar relation on `U` along the restricted morphism
`g.resLE U U' hle`.

At the level of underlying abelian sheaves this is the compatibility of the comparison
`g⁻¹ M ⟶ g^* M` with composition (`AlgebraicGeometry.Scheme.Hom.toSheafPullbackComparison_comp`),
and the functoriality of pullback of cohomology over objects of a site
(`CategoryTheory.Sheaf.H'.pullback_comp_pullback_sheafPullback`).

## Main declarations

* `AlgebraicGeometry.Scheme.Hom.cohomologyOnPullback_comp`: pullback on cohomology along a
  composite;
* `AlgebraicGeometry.Scheme.Hom.cohomologyOnPullback_comp_cohomologyOnPullback_of_comp_eq`:
  pullback on cohomology around a commutative square `a ≫ b = a' ≫ b'`, with the restriction
  along `TauCeti.AlgebraicGeometry.preimage_preimage_eq_of_comp_eq`;
* `AlgebraicGeometry.Scheme.Hom.cohomologyOnPullback_cohomologyOnRes_cohomologyOnPullback_ι`:
  the case of the square `g.resLE U U' hle ≫ U.ι = U'.ι ≫ g` of open subschemes, comparing
  pullback along `g` with pullback along its restriction `U' ⟶ U`;
* `AlgebraicGeometry.Scheme.Hom.cohomologyOnPullbackι_cohomologyOnPullback_smul`:
  scalar compatibility through the restricted morphism `U' ⟶ U`.
-/

public section

open CategoryTheory Limits TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules
open TauCeti.AlgebraicGeometry (preimage_preimage_eq_of_comp_eq)

universe u

noncomputable section

namespace AlgebraicGeometry.Scheme.Hom

variable {X W Z : Scheme.{u}}

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
  rw [cohomologyOnPullback_def, cohomologyOnPullback_def, cohomologyOnPullback_def]
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
  -- The rest needs `erw`: on the left the last two factors are evaluated at `a⁻¹ b⁻¹ U` and at
  -- `(a ≫ b)⁻¹ U`, and on the right the pullback along `a` takes `(toSheaf X ⋙ b⁻¹).obj M` for
  -- `b⁻¹ ((toSheaf X).obj M)` and evaluates at `a⁻¹ (b⁻¹ U)`. These agree only up to unfolding
  -- `Functor.comp_obj` and `Opens.map`, so `rw` cannot reassociate or regroup the evaluated maps,
  -- and the closing `rfl` identifies the two sides after `toSheafPullbackComparison_comp`.
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
            cohomologyOnRes _ n (preimage_preimage_eq_of_comp_eq h U).le =
      b'.cohomologyOnPullback M n U ≫
        a'.cohomologyOnPullback ((Scheme.Modules.pullback b').obj M) n (b' ⁻¹ᵁ U) := by
  have hres := (cohomologyOnRes_comp_cohomologyOnMap
    ((Scheme.Modules.pullbackComp a' b').inv.app M) n (preimage_preimage_eq_of_comp_eq h U).le).symm
  have hc : ((a ≫ b).cohomologyOnPullback M n U ≫
      cohomologyOnMap ((Scheme.Modules.pullbackCongr h).hom.app M) n (a ⁻¹ᵁ b ⁻¹ᵁ U)) ≫
        cohomologyOnRes _ n (preimage_preimage_eq_of_comp_eq h U).le =
      (a' ≫ b').cohomologyOnPullback M n U :=
    (Category.assoc _ _ _).trans (cohomologyOnPullback_congr h M n U)
  calc _ = (b.cohomologyOnPullback M n U ≫
        a.cohomologyOnPullback ((Scheme.Modules.pullback b).obj M) n (b ⁻¹ᵁ U) ≫
          cohomologyOnMap ((Scheme.Modules.pullbackComp a b).hom.app M) n (a ⁻¹ᵁ b ⁻¹ᵁ U)) ≫
        cohomologyOnMap ((Scheme.Modules.pullbackCongr h).hom.app M) n (a ⁻¹ᵁ b ⁻¹ᵁ U) ≫
          cohomologyOnMap ((Scheme.Modules.pullbackComp a' b').inv.app M) n
            (a ⁻¹ᵁ b ⁻¹ᵁ U) ≫ cohomologyOnRes _ n (preimage_preimage_eq_of_comp_eq h U).le := by
        simp only [cohomologyOnMap_comp, Category.assoc]
    _ = (((a ≫ b).cohomologyOnPullback M n U ≫
        cohomologyOnMap ((Scheme.Modules.pullbackCongr h).hom.app M) n (a ⁻¹ᵁ b ⁻¹ᵁ U)) ≫
          cohomologyOnRes _ n (preimage_preimage_eq_of_comp_eq h U).le) ≫
            cohomologyOnMap ((Scheme.Modules.pullbackComp a' b').inv.app M) n
              (a' ⁻¹ᵁ b' ⁻¹ᵁ U) := by
        rw [← cohomologyOnPullback_comp, hres]
        exact ((Category.assoc _ _ _).trans (Category.assoc _ _ _)).symm
    _ = _ := by
        rw [hc, cohomologyOnPullback_comp, Category.assoc, Category.assoc,
          ← cohomologyOnMap_comp, Iso.hom_inv_id_app, cohomologyOnMap_id]
        -- The identity is on `Hⁿ(a'⁻¹ b'⁻¹ U)` while the composite ends at `Hⁿ((a' ≫ b')⁻¹ U)`;
        -- these opens agree definitionally but not syntactically.
        erw [Category.comp_id]

/-- **Pullback on cohomology and open subschemes.** Let `g : X' ⟶ X`, and let `U'` and `U` be
opens of `X'` and `X` with `U' ≤ g⁻¹ U`, so that `g` restricts to `g.resLE U U' hle : U' ⟶ U`.
Pulling back from `U` to `g⁻¹ U` along `g`, restricting to `U'` and pulling back to the open
subscheme `U'` is pulling back to the open subscheme `U` and then along `g.resLE U U' hle`,
followed by the identification `(g.resLE U U' hle)^* (M|_U) ≅ (g^* M)|_{U'}`. -/
@[reassoc]
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
  simp only [cohomologyOnRes_comp, Functor.comp_obj]

/-- Pullback on the cohomology of opens respects a scalar relation computed in the open
subschemes. The scalar on `U` is transported along the restricted morphism `U' ⟶ U`; no global
extension of this function is required. -/
lemma cohomologyOnPullbackι_cohomologyOnPullback_smul {X' : Scheme.{u}}
    (g : X' ⟶ X) (M : X.Modules) (n : ℕ) (U : X.Opens) (U' : X'.Opens)
    (hle : U' ≤ g ⁻¹ᵁ U) (r : Γ(U.toScheme, ⊤)) (x y : cohomologyOn M n U)
    (hxy : U.cohomologyOnPullbackι M n x = r • U.cohomologyOnPullbackι M n y) :
    U'.cohomologyOnPullbackι ((Scheme.Modules.pullback g).obj M) n
        (cohomologyOnRes _ n hle (g.cohomologyOnPullback M n U x)) =
      (g.resLE U U' hle).appTop r •
        U'.cohomologyOnPullbackι ((Scheme.Modules.pullback g).obj M) n
          (cohomologyOnRes _ n hle (g.cohomologyOnPullback M n U y)) := by
  let ψ := (Scheme.Modules.pullbackComp (g.resLE U U' hle) U.ι).hom.app M ≫
    (Scheme.Modules.pullbackCongr (g.resLE_comp_ι hle)).hom.app M ≫
      (Scheme.Modules.pullbackComp U'.ι g).inv.app M
  have hd (z : cohomologyOn M n U) :
      U'.cohomologyOnPullbackι ((Scheme.Modules.pullback g).obj M) n
          (cohomologyOnRes _ n hle (g.cohomologyOnPullback M n U z)) =
        cohomologyOnRes _ n (g.resLE U U' hle).preimage_top.ge
          (cohomologyOnMap ψ n ((g.resLE U U' hle) ⁻¹ᵁ ⊤)
            ((g.resLE U U' hle).cohomologyOnPullback ((Scheme.Modules.pullback U.ι).obj M)
              n ⊤ (U.cohomologyOnPullbackι M n z))) := by
    rw [Scheme.Opens.cohomologyOnPullbackι_def,
      Scheme.Opens.cohomologyOnPullbackι_def]
    exact ConcreteCategory.congr_hom
      (g.cohomologyOnPullback_cohomologyOnRes_cohomologyOnPullback_ι M n U U' hle) z
  rw [hd, hd, hxy, cohomologyOnPullback_smul, ← cohomologyOnMapLinear_apply,
    LinearMap.map_smul, cohomologyOnMapLinear_apply, ← cohomologyOnResLinear_apply,
    LinearMap.map_smul, cohomologyOnResLinear_apply]

end AlgebraicGeometry.Scheme.Hom
