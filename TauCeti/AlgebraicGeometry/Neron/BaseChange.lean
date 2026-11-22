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

/-- The Néron mapping property is stable under smooth base change: if `X` has the property
relative to `j : η ⟶ S`, `g : S' ⟶ S` is smooth and `j' : η' ⟶ S'`, `g' : η' ⟶ η` exhibit `η'`
as the pullback of `j` along `g`, then `X ×_S S'` has the property relative to `j'`
(Bosch–Lütkebohmert–Raynaud, *Néron Models*, §1.2, Proposition 2(c), for étale `g`). -/
theorem NeronMappingProperty.pullback [Smooth g] (sq : IsPullback j' g' g j) {X : Over S}
    (h : NeronMappingProperty j X) : NeronMappingProperty j' ((Over.pullback g).obj X) := by
  rw [neronMappingProperty_iff_bijective_counit_comp] at h ⊢
  intro Y _
  have : Smooth ((Over.map g).obj Y).hom := by dsimp; infer_instance
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
        (fun f ↦ (Over.mapPullbackAdj j).counit.app ((Over.map g).obj Y) ≫ f) ∘
          ((Over.mapPullbackAdj g).homEquiv _ _).symm := by
    ext1 f
    rw [Function.comp_apply, Adjunction.homEquiv_naturality_left_symm, ← he, Category.assoc]
    -- The two sides differ only by `(𝟭 (Over S')).obj Y = Y` in an implicit argument of
    -- `homEquiv`, which `rw` cannot reach.
    rfl
  rw [← (Equiv.bijective ((Over.mapPullbackAdj g).homEquiv _ _).symm).of_comp_iff', key]
  refine Function.Bijective.comp ?_ ((h ((Over.map g).obj Y)).comp (Equiv.bijective _))
  exact ⟨fun a b hab ↦ (cancel_epi _).1 hab, fun b ↦ ⟨e.inv ≫ b, by simp⟩⟩

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
  genericIso := ((Over.pullbackComp j' g).symm ≪≫ eqToIso (by simp only [sq.w]) ≪≫
    Over.pullbackComp g' j).app M.model ≪≫ (Over.pullback g').mapIso M.genericIso
  smooth := by dsimp; infer_instance
  isSeparated := by dsimp; infer_instance
  quasiCompact := by dsimp; infer_instance
  mappingProperty := M.mappingProperty.pullback sq

@[simp]
theorem baseChange_model [Smooth g] (sq : IsPullback j' g' g j) (M : NeronModel j A) :
    (M.baseChange sq).model = (Over.pullback g).obj M.model :=
  (rfl)

/-- Base change commutes with extension of morphisms to Néron models: the base change of the
extension of `φ : A ⟶ B` is the extension of the base change of `φ`. -/
theorem pullback_map_extendHom [Smooth g] (sq : IsPullback j' g' g j) (M : NeronModel j A)
    (N : NeronModel j B) (φ : A ⟶ B) :
    (Over.pullback g).map (M.extendHom N φ) =
      (M.baseChange sq).extendHom (N.baseChange sq) ((Over.pullback g').map φ) := by
  refine ((M.baseChange sq).eq_extendHom_iff (N := N.baseChange sq)).2 ?_
  simp only [baseChange, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom]
  rw [← Functor.comp_map, NatTrans.naturality_assoc]
  simp [← Functor.map_comp]

end NeronModel

end TauCeti.AlgebraicGeometry.Neron
