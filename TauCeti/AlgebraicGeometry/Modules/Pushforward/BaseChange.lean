/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Pullback.Sections

/-!
# The base change morphism for the pushforward of modules

Consider a commutative square of schemes `g' ≫ f = f' ≫ g`, with `g' : X' ⟶ X`, `f : X ⟶ S`,
`f' : X' ⟶ S'` and `g : S' ⟶ S`. The base change morphism `g^* f_* M ⟶ f'_* g'^* M` of sheaves of
modules (`Scheme.Modules.pushforwardBaseChange`) is the mate, under the pullback-pushforward
adjunctions of `g` and `g'`, of the identification `g_* f'_* = (f' ≫ g)_* = (g' ≫ f)_* = f_* g'_*`.
On sections it sends the pullback along `g` of a section `s` of `f_* M` over an open `W` of `S`,
restricted to an open `W' ⊆ g⁻¹ W`, to the pullback of `s` along `g'` restricted to `f'⁻¹ W'`
(`Scheme.Modules.pushforwardBaseChange_app_app_pullbackSectionsLE`).

That the base change morphism is an isomorphism for quasi-coherent sheaves, a cartesian square,
quasi-compact quasi-separated `f` and flat `g` is
`Scheme.Modules.isIso_pushforwardBaseChange_app`, in
`TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Pushforward.BaseChange`.

## Main declarations

* `AlgebraicGeometry.Scheme.Modules.pushforwardBaseChange`: the base change morphism
  `g^* f_* ⟶ f'_* g'^*` of a commutative square;
* `AlgebraicGeometry.Scheme.Modules.unit_comp_pushforward_map_pushforwardBaseChange_app`: its
  characterization through the units of the adjunctions, and
  `AlgebraicGeometry.Scheme.Modules.pushforwardBaseChange_app_app_pullbackSectionsLE`, its effect on
  pulled-back sections.

## References

* R. Hartshorne, *Algebraic Geometry*, Proposition III.9.3.
* [The Stacks Project, Lemma 30.5.2](https://stacks.math.columbia.edu/tag/02KH).
-/

public section

open CategoryTheory AlgebraicGeometry Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X X' S S' : Scheme.{u}} {f : X ⟶ S} {f' : X' ⟶ S'} {g : S' ⟶ S} {g' : X' ⟶ X}

/-- The **base change morphism** `g^* f_* M ⟶ f'_* g'^* M` of a commutative square of schemes
`g' ≫ f = f' ≫ g`: the mate, under the pullback-pushforward adjunctions of `g` and `g'`, of the
identification `f_* g'_* = (g' ≫ f)_* = (f' ≫ g)_* = g_* f'_*`. It is an isomorphism on
quasi-coherent sheaves when the square is cartesian, `f` is quasi-compact and quasi-separated and
`g` is flat (`Scheme.Modules.isIso_pushforwardBaseChange_app`). -/
def pushforwardBaseChange (w : CommSq g' f' f g) :
    pushforward f ⋙ pullback g ⟶ pullback g' ⋙ pushforward f' :=
  (mateEquiv (pullbackPushforwardAdjunction g') (pullbackPushforwardAdjunction g)).symm
    ((pushforwardComp g' f).hom ≫ (pushforwardCongr w.w).hom ≫ (pushforwardComp f' g).inv)

/-- The base change morphism is characterized by its adjunct: the unit of `g^* ⊣ g_*` followed by
`g_*` of the base change morphism is `f_*` of the unit of `g'^* ⊣ g'_*`, followed by the
identification `f_* g'_* = g_* f'_*`. -/
@[reassoc]
lemma unit_comp_pushforward_map_pushforwardBaseChange_app (w : CommSq g' f' f g) (M : X.Modules) :
    (pullbackPushforwardAdjunction g).unit.app ((pushforward f).obj M) ≫
      (pushforward g).map ((pushforwardBaseChange w).app M) =
    (pushforward f).map ((pullbackPushforwardAdjunction g').unit.app M) ≫
      ((pushforwardComp g' f).hom ≫ (pushforwardCongr w.w).hom ≫
        (pushforwardComp f' g).inv).app ((pullback g').obj M) :=
  (unit_mateEquiv_symm (G := pushforward f) (H := pushforward f')
    (pullbackPushforwardAdjunction g') (pullbackPushforwardAdjunction g)
    ((pushforwardComp g' f).hom ≫ (pushforwardCongr w.w).hom ≫ (pushforwardComp f' g).inv) M).symm

/-- On sections over the preimage of an open `W` of `S`, the base change morphism sends the
pullback along `g` of a section `s` of `f_* M` over `W` to the pullback of `s` along `g'`, read
over `(f' ≫ g)⁻¹ W = (g' ≫ f)⁻¹ W`. -/
lemma pushforwardBaseChange_app_app_pullbackSections (w : CommSq g' f' f g) (M : X.Modules)
    (W : S.Opens) (s : Γ((pushforward f).obj M, W)) :
    ((pushforwardBaseChange w).app M).app (g ⁻¹ᵁ W)
        (g.pullbackSections ((pushforward f).obj M) W s) =
      ((pullback g').obj M).presheaf.map (eqToHom (by rw [← Scheme.Hom.comp_preimage, ← w.w,
        Scheme.Hom.comp_preimage])).op (g'.pullbackSections M (f ⁻¹ᵁ W) s) := by
  have h := congr($(unit_comp_pushforward_map_pushforwardBaseChange_app w M).app W s)
  simp only [Functor.comp_obj, pushforward_obj_obj, Hom.comp_app, pushforward_map_app,
    NatTrans.comp_app, pushforwardComp_hom_app_app, pushforwardCongr_hom_app_app,
    pushforwardComp_inv_app_app] at h
  -- `h` evaluates composites of morphisms of abelian groups, some of them identities, at `s`;
  -- the pushforward types block rewriting with `comp_apply`, and `h` is the goal after unfolding
  -- the composites and `pullbackSections`.
  exact (congrArg _ (Scheme.Hom.pullbackSections_apply g _ W s)).trans
    (h.trans (congrArg _ (Scheme.Hom.pullbackSections_apply g' M (f ⁻¹ᵁ W) s).symm))

/-- The base change morphism sends the pullback along `g` of a section `s` of `f_* M` over an open
`W` of `S`, restricted to an open `W' ⊆ g⁻¹ W` of `S'`, to the pullback of `s` along `g'` restricted
to `f'⁻¹ W'`. -/
lemma pushforwardBaseChange_app_app_pullbackSectionsLE (w : CommSq g' f' f g) (M : X.Modules)
    (W : S.Opens) (W' : S'.Opens) (h : W' ≤ g ⁻¹ᵁ W) (s : Γ((pushforward f).obj M, W)) :
    ((pushforwardBaseChange w).app M).app W'
        (g.pullbackSectionsLE ((pushforward f).obj M) W W' h s) =
      g'.pullbackSectionsLE M (f ⁻¹ᵁ W) (f' ⁻¹ᵁ W')
        (by rw [← Scheme.Hom.comp_preimage, w.w, Scheme.Hom.comp_preimage];
            exact f'.preimage_mono h) s := by
  have hn := PresheafOfModules.naturality_apply ((pushforwardBaseChange w).app M).val
    (homOfLE h).op (g.pullbackSections ((pushforward f).obj M) W s)
  refine ((congrArg _ (Scheme.Hom.pullbackSectionsLE_apply g _ W W' h s)).trans hn).trans ?_
  refine (congrArg _ (pushforwardBaseChange_app_app_pullbackSections w M W s)).trans ?_
  refine Eq.trans ?_ (Scheme.Hom.pullbackSectionsLE_apply g' M _ _ _ s).symm
  exact (((pullback g').obj M).presheaf.map_comp_apply _ _ _).symm

end AlgebraicGeometry.Scheme.Modules
