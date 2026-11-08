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
  pulled-back sections;
* `AlgebraicGeometry.Scheme.Modules.pullback_map_unit_comp_pushforwardBaseChange_app`: on a pullback
  `f^* N`, it turns the pullback of the unit of `f^* ⊣ f_*` into the unit of `f'^* ⊣ f'_*` followed
  by the identification `f'^* g^* N ≅ g'^* f^* N`. This is how it enters descent theory.

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

/-- The base change morphism on a pullback `f^* N` of a module on `S`: the pullback along `g` of the
unit `N ⟶ f_* f^* N`, followed by the base change morphism, is the unit `g^* N ⟶ f'_* f'^* g^* N`
followed by `f'_*` of the identification `f'^* g^* N ≅ (f' ≫ g)^* N = (g' ≫ f)^* N ≅ g'^* f^* N`. -/
lemma pullback_map_unit_comp_pushforwardBaseChange_app (w : CommSq g' f' f g) (N : S.Modules) :
    (pullback g).map ((pullbackPushforwardAdjunction f).unit.app N) ≫
      (pushforwardBaseChange w).app ((pullback f).obj N) =
    (pullbackPushforwardAdjunction f').unit.app ((pullback g).obj N) ≫
      (pushforward f').map ((pullbackComp f' g).hom.app N ≫
        (pullbackCongr w.w.symm).hom.app N ≫ (pullbackComp g' f).inv.app N) := by
  -- Both sides send the pullback of a section `s` of `N` over `U` to `g'^* f^* s`.
  refine pullback_hom_ext fun U s ↦ ?_
  rw [Hom.comp_app, Hom.comp_app, ConcreteCategory.comp_apply, ConcreteCategory.comp_apply,
    ← Scheme.Hom.pullbackSectionsLE_self g, Scheme.Hom.pullbackSectionsLE_naturality,
    ← Scheme.Hom.pullbackSections_apply, ← Scheme.Hom.pullbackSectionsLE_self f]
  -- The sections of `f_* f^* N` over `U` are those of `f^* N` over `f⁻¹ U`; `rw` does not see
  -- this, so the base change formula is applied by `Eq.trans`.
  refine (pushforwardBaseChange_app_app_pullbackSectionsLE w ((pullback f).obj N) U (g ⁻¹ᵁ U)
    le_rfl (f.pullbackSectionsLE N U (f ⁻¹ᵁ U) le_rfl s)).trans ?_
  rw [pushforward_map_app, ← Scheme.Hom.pullbackSections_apply,
    ← Scheme.Hom.pullbackSectionsLE_self f', Hom.comp_app, Hom.comp_app]
  have h₁ := Scheme.Hom.pullbackSectionsLE_comp_hom g N U f' (g ⁻¹ᵁ U) le_rfl
    (W := f' ⁻¹ᵁ g ⁻¹ᵁ U) le_rfl s
  have h₂ := Scheme.Hom.pullbackSectionsLE_congr (f' ≫ g) N U (f' ⁻¹ᵁ g ⁻¹ᵁ U) le_rfl
    w.w.symm s
  have h₃ := Scheme.Hom.pullbackSectionsLE_comp f N U g' (f ⁻¹ᵁ U) le_rfl (W := f' ⁻¹ᵁ g ⁻¹ᵁ U)
    (by rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, w.w]) s
  -- The goal is typed by sections of `f'_* g'^* f^* N` over `g⁻¹ U`, while `h₁`, `h₂` and `h₃` are
  -- stated for sections of `g'^* f^* N` over `f'⁻¹ g⁻¹ U`. They agree only up to unfolding, so
  -- `rw` and `simp` do not see the composites, and the chain is closed by `Eq.trans` instead.
  refine Eq.symm ((ConcreteCategory.comp_apply _ _ _).trans ?_)
  refine (congrArg _ h₁).trans ((ConcreteCategory.comp_apply _ _ _).trans ?_)
  exact (congrArg _ h₂).trans h₃

end AlgebraicGeometry.Scheme.Modules
