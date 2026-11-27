/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Neron.Model
public import TauCeti.CategoryTheory.Comma.Over.Pullback

/-!
# Smooth base change of Néron models

Let `j : η ⟶ S` be a morphism of schemes, `g : S' ⟶ S` a smooth morphism, and let
`j' : η' ⟶ S'`, `g' : η' ⟶ η` exhibit `η'` as the pullback `η ×_S S'`. If an `S`-scheme `X` has
the Néron mapping property relative to `j`, then its base change `X ×_S S'` has the Néron mapping
property relative to `j'`. Consequently the base change of a Néron model of `A` is a Néron model
of `A ×_η η'`.

The arithmetic instances are étale base change of Dedekind schemes, an unramified extension of
discrete valuation rings, and the restriction of a Néron model to an open subscheme of the base:
étale morphisms and open immersions are smooth. The proof uses only that a smooth `S'`-scheme is
smooth over `S` when `g` is smooth. Arbitrary base change does not preserve Néron models: after
a ramified extension of discrete valuation rings the component group of a Tate curve grows, so
the smoothness of `g` cannot be dropped.

## Main results

* `TauCeti.AlgebraicGeometry.Neron.bijective_pullback_map_iff_of_isPullback`: restriction to a
  test object over `S'` is restriction to the same object viewed over `S`.
* `TauCeti.AlgebraicGeometry.Neron.NeronMappingProperty.pullback`: the Néron mapping property
  is stable under smooth base change.
* `TauCeti.AlgebraicGeometry.Neron.NeronModel.baseChange`: the base change of a Néron model of
  `A` along a smooth morphism, as a Néron model of the base change of `A`.
* `TauCeti.AlgebraicGeometry.Neron.NeronModel.pullback_map_extendHom`: base change commutes with
  the extension of morphisms to Néron models.

## References

* S. Bosch, W. Lütkebohmert, M. Raynaud, *Néron Models*, Ergebnisse der Mathematik und ihrer
  Grenzgebiete (3) 21, Springer, 1990, §1.2, Proposition 2(c).
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry.Neron

universe u

variable {η S η' S' : Scheme.{u}} {j : η ⟶ S} {g : S' ⟶ S} {j' : η' ⟶ S'} {g' : η' ⟶ η}

/-- Restriction to a test object over `S'` is restriction to the same object viewed over `S`:
if `j' : η' ⟶ S'`, `g' : η' ⟶ η` exhibit `η'` as the pullback of `j : η ⟶ S` along
`g : S' ⟶ S`, then for an `S'`-scheme `Y` and an `S`-scheme `X`, base change along `j'` is
bijective on `S'`-morphisms `Y ⟶ X ×_S S'` exactly when base change along `j` is bijective on
`S`-morphisms from `Y`, viewed as an `S`-scheme, to `X`. -/
theorem bijective_pullback_map_iff_of_isPullback (sq : IsPullback j' g' g j) (X : Over S)
    (Y : Over S') :
    Function.Bijective ((Over.pullback j').map : (Y ⟶ (Over.pullback g).obj X) → _) ↔
      Function.Bijective ((Over.pullback j).map : ((Over.map g).obj Y ⟶ X) → _) := by
  rw [bijective_pullback_map_iff_bijective_counit_comp,
    bijective_pullback_map_iff_bijective_counit_comp]
  -- Pushed forward along `g`, the counit for `j'` at `Y` is the counit for `j` at `Y` viewed
  -- over `S`, up to the Beck–Chevalley isomorphism of the square.
  obtain ⟨e, he⟩ : ∃ e : (Over.map g).obj ((Over.map j').obj ((Over.pullback j').obj Y)) ≅
      (Over.map j).obj ((Over.pullback j).obj ((Over.map g).obj Y)),
      e.hom ≫ (Over.mapPullbackAdj j).counit.app ((Over.map g).obj Y) =
        (Over.map g).map ((Over.mapPullbackAdj j').counit.app Y) :=
    ⟨Over.isoMk ((Over.forget _).mapIso (sq.overPullbackCompMapIso.app Y))
      (by simp [sq.w]), by ext1; simp⟩
  -- Under the adjunction `Over.map g ⊣ Over.pullback g`, precomposition with the counit for `j'`
  -- becomes precomposition with `e.hom` and the counit for `j`.
  have key : ((Over.mapPullbackAdj g).homEquiv _ _).symm ∘
      (fun f : Y ⟶ (Over.pullback g).obj X ↦ (Over.mapPullbackAdj j').counit.app Y ≫ f) =
      (fun f ↦ e.hom ≫ f) ∘
        ((fun f ↦ (Over.mapPullbackAdj j).counit.app ((Over.map g).obj Y) ≫ f) ∘
          ((Over.mapPullbackAdj g).homEquiv _ _).symm) := by
    ext1 f
    rw [Function.comp_apply, Adjunction.homEquiv_naturality_left_symm, ← he, Category.assoc]
    -- The two sides differ only by `(𝟭 (Over S')).obj Y = Y` in an implicit argument of
    -- `homEquiv`, which `rw` cannot reach.
    rfl
  have he' : Function.Bijective fun f : (Over.map j).obj ((Over.pullback j).obj
      ((Over.map g).obj Y)) ⟶ X ↦ e.hom ≫ f :=
    ⟨fun a b hab ↦ (cancel_epi _).1 hab, fun b ↦ ⟨e.inv ≫ b, by simp⟩⟩
  rw [← (Equiv.bijective ((Over.mapPullbackAdj g).homEquiv _ _).symm).of_comp_iff', key,
    he'.of_comp_iff', (Equiv.bijective _).of_comp_iff]
  -- As in `key`, the two sides differ only by an identity functor in an implicit argument.
  exact Iff.rfl

/-- The Néron mapping property is stable under smooth base change: if `X` has the property
relative to `j : η ⟶ S`, `g : S' ⟶ S` is smooth and `j' : η' ⟶ S'`, `g' : η' ⟶ η` exhibit `η'`
as the pullback of `j` along `g`, then `X ×_S S'` has the property relative to `j'`
(Bosch–Lütkebohmert–Raynaud, *Néron Models*, §1.2, Proposition 2(c), for étale `g`). -/
theorem NeronMappingProperty.pullback [Smooth g] (sq : IsPullback j' g' g j) {X : Over S}
    (h : NeronMappingProperty j X) : NeronMappingProperty j' ((Over.pullback g).obj X) where
  bijective Y (_ : Smooth Y.hom) := by
    have : Smooth ((Over.map g).obj Y).hom := by dsimp; infer_instance
    exact (bijective_pullback_map_iff_of_isPullback sq X Y).2 (h.bijective _ this)

namespace NeronModel

variable {A B : Over η}

/-- The base change of a Néron model of `A` along a smooth morphism `g : S' ⟶ S`: its total space
is `M.model ×_S S'`, and its marking identifies the base change of `M.model` along `j'` with the
base change `A ×_η η'` of `A` along `g'`, through the marking of `M`. The body is exposed so
that `(M.baseChange sq).model` is definitionally `(Over.pullback g).obj M.model`, and base changes
of morphisms into `M.model` are morphisms into the base-changed model. -/
@[expose]
def baseChange [Smooth g] (sq : IsPullback j' g' g j) (M : NeronModel j A) :
    NeronModel j' ((Over.pullback g').obj A) where
  model := (Over.pullback g).obj M.model
  genericIso := (Over.pullbackPullbackIsoOfComm sq.w).app M.model ≪≫
    (Over.pullback g').mapIso M.genericIso
  smooth := by dsimp; infer_instance
  isSeparated := by dsimp; infer_instance
  quasiCompact := by dsimp; infer_instance
  mappingProperty := NeronMappingProperty.pullback sq M.mappingProperty

@[simp]
theorem baseChange_model [Smooth g] (sq : IsPullback j' g' g j) (M : NeronModel j A) :
    (M.baseChange sq).model = (Over.pullback g).obj M.model :=
  (rfl)

@[simp]
theorem baseChange_genericIso_hom [Smooth g] (sq : IsPullback j' g' g j) (M : NeronModel j A) :
    (M.baseChange sq).genericIso.hom =
      (Over.pullbackPullbackIsoOfComm sq.w).hom.app M.model ≫
        (Over.pullback g').map M.genericIso.hom :=
  (rfl)

/-- Base change commutes with extension of morphisms to Néron models: the base change of the
extension of `φ : A ⟶ B` is the extension of the base change of `φ`. -/
theorem pullback_map_extendHom [Smooth g] (sq : IsPullback j' g' g j) (M : NeronModel j A)
    (N : NeronModel j B) (φ : A ⟶ B) :
    (Over.pullback g).map (M.extendHom N φ) =
      (M.baseChange sq).extendHom (N.baseChange sq) ((Over.pullback g').map φ) := by
  refine ((M.baseChange sq).eq_extendHom_iff (N := N.baseChange sq)).2 ?_
  simp only [baseChange_genericIso_hom]
  -- The objects of the left side are `(M.baseChange sq).model` and `(N.baseChange sq).model`,
  -- which `rw` does not unfold to base changes, so naturality is applied by unification.
  refine (NatTrans.naturality_assoc (F := Over.pullback g ⋙ Over.pullback j') _
    (M.extendHom N φ) _).trans ((Category.assoc _ _ _).trans ?_).symm
  simp [← Functor.map_comp]

end NeronModel

end TauCeti.AlgebraicGeometry.Neron
