/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Pullback.BaseChange
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import TauCeti.AlgebraicGeometry.AffineScheme
import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Pushforward.QuasiSeparated
import TauCeti.AlgebraicGeometry.Modules.Sheaf
import TauCeti.RingTheory.TensorProduct.IsBaseChange

/-!
# Flat base change for the pushforward of quasi-coherent sheaves

Consider a commutative square of schemes `g' ≫ f = f' ≫ g`, with `g' : X' ⟶ X`, `f : X ⟶ S`,
`f' : X' ⟶ S'` and `g : S' ⟶ S`. The base change morphism `g^* f_* M ⟶ f'_* g'^* M` of sheaves of
modules (`Scheme.Modules.pushforwardBaseChange`) is the mate, under the pullback-pushforward
adjunctions of `g` and `g'`, of the identification `g_* f'_* = (f' ≫ g)_* = (g' ≫ f)_* = f_* g'_*`.
On sections it sends the pullback along `g` of a section `s` of `f_* M` over an open `W` of `S`,
restricted to an open `W' ⊆ g⁻¹ W`, to the pullback of `s` along `g'` restricted to `f'⁻¹ W'`
(`Scheme.Modules.pushforwardBaseChange_app_app_pullbackSectionsLE`).

When the square is cartesian, `f` is quasi-compact and quasi-separated, `g` is flat and `M` is
quasi-coherent, the base change morphism is an isomorphism
(`Scheme.Modules.isIso_pushforwardBaseChange_app`). This is flat base change for the direct image
in degree zero. It suffices to check bijectivity on sections over the affine opens `W'` of `S'`
lying over affine opens `W` of `S`, since these form a basis
(`Scheme.Hom.isBasis_range_affineOpens_le_preimage`). There both sides are base changes of
`Γ(f⁻¹ W, M)` from `Γ(S, W)` to `Γ(S', W')`: the source because `f_* M` is quasi-coherent and
`W`, `W'` are affine (`Scheme.Hom.isBaseChange_pullbackSectionsLEBaseLinear` for the
identity square on `g`), and the target by flat base change of sections over the quasi-compact
quasi-separated open `f⁻¹ W`
(`Scheme.Hom.isBaseChange_pullbackSectionsLEBaseLinear_of_isQuasiSeparated`). The base change
morphism is compatible with both identifications, so it is bijective
(`IsBaseChange.bijective_of_comp_eq`).

## Main declarations

* `AlgebraicGeometry.Scheme.Modules.pushforwardBaseChange`: the base change morphism
  `g^* f_* ⟶ f'_* g'^*` of a commutative square;
* `AlgebraicGeometry.Scheme.Modules.unit_comp_pushforward_map_pushforwardBaseChange_app`: its
  characterization through the units of the adjunctions, and
  `AlgebraicGeometry.Scheme.Modules.pushforwardBaseChange_app_app_pullbackSectionsLE`, its effect on
  pulled-back sections;
* `AlgebraicGeometry.Scheme.Modules.bijective_pushforwardBaseChange_app_app`: flat base change on
  the sections over an affine open lying over an affine open;
* `AlgebraicGeometry.Scheme.Modules.isIso_pushforwardBaseChange_app`: **flat base change**, the
  base change morphism `g^* f_* M ⟶ f'_* g'^* M` is an isomorphism for quasi-compact
  quasi-separated `f`, flat `g` and quasi-coherent `M`.

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

/-- **Flat base change on sections over affine opens.** For a cartesian square
`g' ≫ f = f' ≫ g` with `f` quasi-compact and quasi-separated and `g` flat, a quasi-coherent sheaf
`M` on `X`, and affine opens `W` of `S` and `W' ⊆ g⁻¹ W` of `S'`, the base change morphism is
bijective on the sections over `W'`. -/
theorem bijective_pushforwardBaseChange_app_app (H : IsPullback g' f' f g) [QuasiCompact f]
    [QuasiSeparated f] [Flat g] (M : X.Modules) [M.IsQuasicoherent] {W : S.Opens}
    (hW : IsAffineOpen W) {W' : S'.Opens} (hW' : IsAffineOpen W') (h : W' ≤ g ⁻¹ᵁ W) :
    Function.Bijective (((pushforwardBaseChange H.toCommSq).app M).app W') := by
  -- Both sides are base changes of `Γ(f⁻¹ W, M) = Γ(W, f_* M)` from `Γ(S, W)` to `Γ(S', W')`,
  -- and the base change morphism is compatible with the two base-change maps. First the
  -- source, through the identity square on `g`, whose rings act through identities.
  let N := (pushforward f).obj M
  let : Algebra Γ(S, W) Γ(S', W') := (g.appLE W W' h).hom.toAlgebra
  let : Module Γ(S, W) Γ((pullback g).obj N, W') := Module.compHom _ (algebraMap Γ(S, W) Γ(S', W'))
  have : IsScalarTower Γ(S, W) Γ(S', W') Γ((pullback g).obj N, W') :=
    .of_algebraMap_smul fun _ _ ↦ rfl
  let alg₁ : Algebra Γ(S, W) Γ(S, W) := (Scheme.Hom.appLE (𝟙 S) W W le_rfl).hom.toAlgebra
  have hid (Y : Scheme.{u}) (V : Y.Opens) : Scheme.Hom.appLE (𝟙 Y) V V le_rfl = 𝟙 _ :=
    (Scheme.Hom.appLE_eq_app (𝟙 Y)).trans (Scheme.Hom.id_app V)
  have t₁ : @IsScalarTower Γ(S, W) Γ(S, W) Γ(N, W) alg₁.toSMul _ _ :=
    @IsScalarTower.of_algebraMap_smul _ _ _ _ _ alg₁ _ _ fun r n ↦ by
      rw [RingHom.algebraMap_toAlgebra, hid]
      rfl
  let alg₂ : Algebra Γ(S', W') Γ(S', W') := (Scheme.Hom.appLE (𝟙 S') W' W' le_rfl).hom.toAlgebra
  have t₂ : @IsScalarTower Γ(S', W') Γ(S', W') Γ((pullback g).obj N, W') alg₂.toSMul _ _ :=
    @IsScalarTower.of_algebraMap_smul _ _ _ _ _ alg₂ _ _ fun r n ↦ by
      rw [RingHom.algebraMap_toAlgebra, hid]
      rfl
  have hα := Scheme.Hom.isBaseChange_pullbackSectionsLEBaseLinear g N
    (IsPullback.id_vert g) hW hW' h (UX := W) le_rfl hW (UY := W') (by simpa using h)
  -- Then the target, the sections of `f'_* g'^* M` over `W'`, by flat base change over
  -- `W' ⟶ W`.
  have hUY : f' ⁻¹ᵁ W' = g' ⁻¹ᵁ (f ⁻¹ᵁ W) ⊓ f' ⁻¹ᵁ W' := by
    refine (inf_eq_right.mpr ?_).symm
    rw [← Scheme.Hom.comp_preimage, H.w, Scheme.Hom.comp_preimage]
    exact f'.preimage_mono h
  let : Module Γ(S, W) Γ(M, f ⁻¹ᵁ W) := (inferInstance : Module Γ(S, W) Γ(N, W))
  let : Algebra Γ(S, W) Γ(X, f ⁻¹ᵁ W) := (f.appLE W (f ⁻¹ᵁ W) le_rfl).hom.toAlgebra
  have : IsScalarTower Γ(S, W) Γ(X, f ⁻¹ᵁ W) Γ(M, f ⁻¹ᵁ W) := .of_algebraMap_smul fun r m ↦ by
    rw [RingHom.algebraMap_toAlgebra, Scheme.Hom.appLE_eq_app]
    rfl
  let : Module Γ(S', W') Γ((pullback g').obj M, f' ⁻¹ᵁ W') :=
    (inferInstance : Module Γ(S', W') Γ((pushforward f').obj ((pullback g').obj M), W'))
  let : Algebra Γ(S', W') Γ(X', f' ⁻¹ᵁ W') := (f'.appLE W' (f' ⁻¹ᵁ W') le_rfl).hom.toAlgebra
  have : IsScalarTower Γ(S', W') Γ(X', f' ⁻¹ᵁ W') Γ((pullback g').obj M, f' ⁻¹ᵁ W') :=
    .of_algebraMap_smul fun r m ↦ by
      rw [RingHom.algebraMap_toAlgebra, Scheme.Hom.appLE_eq_app]
      rfl
  let : Module Γ(S, W) Γ((pullback g').obj M, f' ⁻¹ᵁ W') :=
    Module.compHom _ (algebraMap Γ(S, W) Γ(S', W'))
  have : IsScalarTower Γ(S, W) Γ(S', W') Γ((pullback g').obj M, f' ⁻¹ᵁ W') :=
    .of_algebraMap_smul fun _ _ ↦ rfl
  have hβ := Scheme.Hom.isBaseChange_pullbackSectionsLEBaseLinear_of_isQuasiSeparated g' M H
    hW hW' h (UX := f ⁻¹ᵁ W) le_rfl (f.isCompact_preimage hW.isCompact)
    (f.isQuasiSeparated_preimage hW.isQuasiSeparated) hUY
  -- The base change map on sections over `W'` is linear over `Γ(S', W')` and compatible with
  -- the two pullbacks of sections.
  let φ : Γ((pullback g).obj N, W') →ₗ[Γ(S', W')]
      Γ((pushforward f').obj ((pullback g').obj M), W') :=
    { toFun := ((pushforwardBaseChange H.toCommSq).app M).app W'
      map_add' := map_add _
      map_smul' := Hom.app_smul _ }
  exact IsBaseChange.bijective_of_comp_eq hα hβ φ fun s ↦
    (congrArg φ (Scheme.Hom.pullbackSectionsLEBaseLinear_apply g N _ h _ _ _ s)).trans
      ((pushforwardBaseChange_app_app_pullbackSectionsLE H.toCommSq M W W' h s).trans
        (Scheme.Hom.pullbackSectionsLEBaseLinear_apply g' M _ h _ _ _ s).symm)


/-- **Flat base change for the direct image of a quasi-coherent sheaf.** For a cartesian square
of schemes `g' ≫ f = f' ≫ g`, with `f : X ⟶ S` quasi-compact and quasi-separated and `g : S' ⟶ S`
flat, and a quasi-coherent sheaf `M` on `X`, the base change morphism
`g^* f_* M ⟶ f'_* g'^* M` is an isomorphism. -/
theorem isIso_pushforwardBaseChange_app (H : IsPullback g' f' f g) [QuasiCompact f]
    [QuasiSeparated f] [Flat g] (M : X.Modules) [M.IsQuasicoherent] :
    IsIso ((pushforwardBaseChange H.toCommSq).app M) :=
  Hom.isIso_of_isBasis _ g.isBasis_range_affineOpens_le_preimage fun i ↦
    (ConcreteCategory.isIso_iff_bijective _).mpr
      (bijective_pushforwardBaseChange_app_app H M i.1.2.2 i.1.1.2 i.2)

end AlgebraicGeometry.Scheme.Modules
