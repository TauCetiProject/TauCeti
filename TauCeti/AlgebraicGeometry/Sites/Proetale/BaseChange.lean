/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Morphisms.WeaklyEtale
public import TauCeti.AlgebraicGeometry.Sites.Etale.Over.Basic
public import TauCeti.AlgebraicGeometry.Sites.Proetale.EtaleComparison

/-!
# Base change of small pro-étale sites, and naturality of `ν`

For a morphism of schemes `f : X ⟶ Y`, weakly étale morphisms are stable under base change, so
base change along `f` defines a functor `AlgebraicGeometry.Scheme.Hom.smallProEtBaseChange f :
Y.ProEt ⥤ X.ProEt` sending a weakly étale `V ⟶ Y` to `V ×_Y X ⟶ X`, as
`AlgebraicGeometry.Scheme.Hom.smallEtaleBaseChange f` does for étale `Y`-schemes.

The inclusion `AlgebraicGeometry.Scheme.toProEt` of the small étale site into the small pro-étale
site, which defines the morphism of sites `ν : X_proét → X_ét`, is natural in the scheme: base
change of an étale `Y`-scheme followed by the inclusion is the inclusion followed by base change
of the weakly étale `Y`-scheme (`AlgebraicGeometry.Scheme.Hom.smallEtaleBaseChangeCompToProEtIso`).
Both functors send `V` to `V ×_Y X ⟶ X`, so the isomorphism has identity components.

## Main declarations

* `AlgebraicGeometry.Scheme.Hom.smallProEtBaseChange`: base change `Y.ProEt ⥤ X.ProEt` along
  `f : X ⟶ Y`.
* `AlgebraicGeometry.Scheme.Hom.smallEtaleBaseChangeCompToProEtIso`: the isomorphism
  `f.smallEtaleBaseChange ⋙ toProEt X ≅ toProEt Y ⋙ f.smallProEtBaseChange`.

## References

* B. Bhatt and P. Scholze, *The pro-étale topology for schemes*, §5.1.
-/

public section

universe u

open CategoryTheory Limits MorphismProperty

namespace AlgebraicGeometry

namespace Scheme.Hom

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- Base change along `f : X ⟶ Y`, from weakly étale `Y`-schemes to weakly étale `X`-schemes: a
weakly étale `V ⟶ Y` is sent to `V ×_Y X ⟶ X`. -/
-- Exposed so `(f.smallProEtBaseChange.obj V).left` and `.hom` reduce in dependent types.
@[expose]
noncomputable def smallProEtBaseChange : Y.ProEt ⥤ X.ProEt :=
  MorphismProperty.Over.pullback @WeaklyEtale ⊤ f

@[simp]
lemma smallProEtBaseChange_obj_left (V : Y.ProEt) :
    (f.smallProEtBaseChange.obj V).left = pullback V.hom f := (rfl)

@[simp]
lemma smallProEtBaseChange_obj_hom (V : Y.ProEt) :
    (f.smallProEtBaseChange.obj V).hom = pullback.snd V.hom f := (rfl)

@[simp]
lemma smallProEtBaseChange_map_left {V W : Y.ProEt} (g : V ⟶ W) :
    (f.smallProEtBaseChange.map g).left =
      pullback.lift (pullback.fst V.hom f ≫ g.left) (pullback.snd V.hom f)
        (by simp [pullback.condition]) := (rfl)

/-- On underlying schemes, `f.smallProEtBaseChange.map g` is `pullback.map` along `g.left` and
`𝟙 X`. -/
lemma smallProEtBaseChange_map_left_eq_pullback_map {V W : Y.ProEt} (g : V ⟶ W) :
    (f.smallProEtBaseChange.map g).left =
      pullback.map V.hom f W.hom f g.left (𝟙 X) (𝟙 Y) (by simp) (by simp) :=
  MorphismProperty.Over.pullback_map_left_eq_pullback_map _ _ f g

/-- **Naturality of `ν`**: base change of étale `Y`-schemes along `f`
followed by the inclusion into weakly étale `X`-schemes is the inclusion of étale `Y`-schemes
followed by base change of weakly étale `Y`-schemes. Both send `V` to `V ×_Y X ⟶ X`. -/
noncomputable def smallEtaleBaseChangeCompToProEtIso :
    f.smallEtaleBaseChange ⋙ toProEt X ≅ toProEt Y ⋙ f.smallProEtBaseChange :=
  Iso.refl _

@[simp]
lemma smallEtaleBaseChangeCompToProEtIso_hom_app_left (V : Y.Etale) :
    (f.smallEtaleBaseChangeCompToProEtIso.hom.app V).left = 𝟙 (pullback V.hom f) := (rfl)

@[simp]
lemma smallEtaleBaseChangeCompToProEtIso_inv_app_left (V : Y.Etale) :
    (f.smallEtaleBaseChangeCompToProEtIso.inv.app V).left = 𝟙 (pullback V.hom f) := (rfl)

end Scheme.Hom

end AlgebraicGeometry
