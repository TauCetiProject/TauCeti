/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import TauCeti.AlgebraicGeometry.Frobenius.Basic

/-!
# The relative Frobenius of a scheme over a base of characteristic `p`

Let `p` be a prime, `S` a scheme in which `p` vanishes, with absolute Frobenius `F_S : S ⟶ S`,
and `π : X ⟶ S` a scheme over `S`. The *Frobenius twist* of `X` is the base change
`X^{(p)} = X ×_{S, F_S} S`, a scheme over `S` through its second projection. Since the absolute
Frobenius commutes with `π`, the absolute Frobenius `F_X` and `π` define the *relative
Frobenius*

`F_{X/S} : X ⟶ X^{(p)}`,

a morphism over `S` whose composite with the first projection `X^{(p)} ⟶ X` is `F_X`.

Unlike `F_X`, the relative Frobenius is a morphism over `S`, natural in `X` over `S`
(`AlgebraicGeometry.Scheme.Hom.relativeFrobenius_naturality`), and both the Frobenius twist and
the relative Frobenius commute with base change along any `T ⟶ S`
(`AlgebraicGeometry.Scheme.Hom.isPullback_frobeniusTwistMap` and
`AlgebraicGeometry.Scheme.Hom.isPullback_relativeFrobenius`). It is a natural transformation from
the identity of `Over S` to the base change functor `Over.pullback F_S`. Since both of these
functors preserve finite products, it lifts to group objects, so it carries every group scheme `G`
over `S` to a homomorphism of group schemes `G ⟶ G^{(p)}`
(`AlgebraicGeometry.Scheme.relativeFrobeniusGrpHom`).

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.relativeFrobenius π p hS`: the relative Frobenius
  `F_{X/S} : X ⟶ X ×_{S, F_S} S` of `π : X ⟶ S`.
* `AlgebraicGeometry.Scheme.Hom.frobeniusTwistMap π p hS f`: the projection from the Frobenius
  twist of the base change of `X` along `f : T ⟶ S` to the Frobenius twist of `X`.
* `AlgebraicGeometry.Scheme.relativeFrobeniusNatTrans S p hS`: the relative Frobenius as a
  natural transformation `𝟭 (Over S) ⟶ Over.pullback F_S`.
* `AlgebraicGeometry.Scheme.relativeFrobeniusGrpHom S p hS G` and
  `AlgebraicGeometry.Scheme.relativeFrobeniusCommGrpHom S p hS G`: the relative Frobenius of a
  (commutative) group scheme `G` over `S`, as a homomorphism of group schemes `G ⟶ G^{(p)}`.

## Main results

* `AlgebraicGeometry.Scheme.Hom.relativeFrobenius_fst` and
  `AlgebraicGeometry.Scheme.Hom.relativeFrobenius_snd`: `F_{X/S}` followed by the projections
  of `X^{(p)}` is `F_X` and `π`.
* `AlgebraicGeometry.Scheme.Hom.relativeFrobenius_naturality`: `F_{X/S}` is natural in `X` over
  `S`.
* `AlgebraicGeometry.Scheme.Hom.isPullback_frobeniusTwistMap`: the Frobenius twist of `X ×_S T`
  over `T` is the base change of the Frobenius twist of `X` along `T ⟶ S`.
* `AlgebraicGeometry.Scheme.Hom.isPullback_relativeFrobenius`: the relative Frobenius of
  `X ×_S T` over `T` is the base change of the relative Frobenius of `X` along `T ⟶ S`.

## References

* The Stacks Project, chapter Varieties, section Frobenii, for the relative Frobenius morphism
  and its compatibility with base change.
-/

public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme

namespace Hom

variable {X Y S T : Scheme.{u}} (π : X ⟶ S) (p : ℕ) [Fact p.Prime] (hS : (p : Γ(S, ⊤)) = 0)

/-- The **relative Frobenius** `F_{X/S} : X ⟶ X^{(p)} = X ×_{S, F_S} S` of a scheme `π : X ⟶ S`
over a scheme `S` in which the prime `p` vanishes: the morphism to the Frobenius twist whose
components are the absolute Frobenius `F_X` and `π`. -/
noncomputable def relativeFrobenius : X ⟶ pullback π (S.frobenius p hS) :=
  pullback.lift (X.frobenius p (natCast_eq_zero_of_hom π hS)) π (frobenius_naturality _ _ π)

/-- The relative Frobenius followed by the projection `X^{(p)} ⟶ X` is the absolute Frobenius. -/
@[reassoc (attr := simp)]
theorem relativeFrobenius_fst :
    π.relativeFrobenius p hS ≫ pullback.fst _ _ = X.frobenius p (natCast_eq_zero_of_hom π hS) :=
  pullback.lift_fst _ _ _

/-- The relative Frobenius is a morphism over `S`. -/
@[reassoc (attr := simp)]
theorem relativeFrobenius_snd : π.relativeFrobenius p hS ≫ pullback.snd _ _ = π :=
  pullback.lift_snd _ _ _

/-- The projection from the Frobenius twist `(X ×_S T)^{(p)}` of the base change of `X` along
`f : T ⟶ S` to the Frobenius twist `X^{(p)}` of `X`, induced by the projection `X ×_S T ⟶ X`
and by `f`. -/
noncomputable def frobeniusTwistMap (f : T ⟶ S) :
    pullback (pullback.snd π f) (T.frobenius p (natCast_eq_zero_of_hom f hS)) ⟶
      pullback π (S.frobenius p hS) :=
  pullback.map _ _ _ _ (pullback.fst π f) f f pullback.condition.symm
    (frobenius_naturality _ hS f)

/-- The projection between Frobenius twists, followed by the projection `X^{(p)} ⟶ X`, is the
projection `(X ×_S T)^{(p)} ⟶ X ×_S T` followed by the projection `X ×_S T ⟶ X`. -/
@[reassoc (attr := simp)]
theorem frobeniusTwistMap_fst (f : T ⟶ S) :
    π.frobeniusTwistMap p hS f ≫ pullback.fst _ _ = pullback.fst _ _ ≫ pullback.fst π f :=
  pullback.lift_fst _ _ _

/-- The projection between Frobenius twists lies over `f : T ⟶ S`. -/
@[reassoc (attr := simp)]
theorem frobeniusTwistMap_snd (f : T ⟶ S) :
    π.frobeniusTwistMap p hS f ≫ pullback.snd _ _ = pullback.snd _ _ ≫ f :=
  pullback.lift_snd _ _ _

variable {π p}

/-- **The relative Frobenius is natural** in the scheme over `S`: for a morphism `g : X ⟶ Y` over
`S`, the relative Frobenius of `Y` after `g` is the relative Frobenius of `X` followed by the
morphism `X^{(p)} ⟶ Y^{(p)}` induced by `g`. -/
@[reassoc]
theorem relativeFrobenius_naturality (πY : Y ⟶ S) (g : X ⟶ Y) (hg : g ≫ πY = π) :
    π.relativeFrobenius p hS ≫
        pullback.map π _ πY _ g (𝟙 _) (𝟙 _) (by simp [hg]) (by simp) =
      g ≫ πY.relativeFrobenius p hS := by
  ext <;> simp [frobenius_naturality _ (natCast_eq_zero_of_hom πY hS) g, hg]

/-- **The Frobenius twist commutes with base change.** For `f : T ⟶ S`, the Frobenius twist of
`X ×_S T` over `T` is the base change of the Frobenius twist `X^{(p)}` of `X` along `f`. -/
theorem isPullback_frobeniusTwistMap (f : T ⟶ S) :
    IsPullback (π.frobeniusTwistMap p hS f) (pullback.snd _ _) (pullback.snd _ _) f := by
  refine IsPullback.of_right ?_ (by simp) (IsPullback.of_hasPullback π _)
  -- the composite of the two squares is the composite of the pullback squares defining
  -- `X ×_S T` and its Frobenius twist, since `F_T ≫ f = f ≫ F_S`
  have h := (IsPullback.of_hasPullback (pullback.snd π f)
    (T.frobenius p (natCast_eq_zero_of_hom f hS))).paste_horiz (IsPullback.of_hasPullback π f)
  rw [frobenius_naturality _ hS f] at h
  simpa using h

/-- The relative Frobenius of the base change `X ×_S T` over `T`, followed by the projection to
the Frobenius twist of `X`, is the projection `X ×_S T ⟶ X` followed by the relative Frobenius of
`X`. -/
@[reassoc (attr := simp)]
theorem relativeFrobenius_frobeniusTwistMap (f : T ⟶ S) :
    (pullback.snd π f).relativeFrobenius p (natCast_eq_zero_of_hom f hS) ≫
        π.frobeniusTwistMap p hS f =
      pullback.fst π f ≫ π.relativeFrobenius p hS := by
  ext <;> simp [frobenius_naturality _ (natCast_eq_zero_of_hom π hS) (pullback.fst π f),
    pullback.condition]

/-- **The relative Frobenius commutes with base change.** For `f : T ⟶ S`, the relative
Frobenius of `X ×_S T` over `T` is the base change along `f` of the relative Frobenius of `X`
over `S`. -/
theorem isPullback_relativeFrobenius (f : T ⟶ S) :
    IsPullback ((pullback.snd π f).relativeFrobenius p (natCast_eq_zero_of_hom f hS))
      (pullback.fst π f) (π.frobeniusTwistMap p hS f) (π.relativeFrobenius p hS) := by
  refine IsPullback.of_right ?_ (relativeFrobenius_frobeniusTwistMap hS f)
    (isPullback_frobeniusTwistMap hS f).flip
  simpa using (IsPullback.of_hasPullback π f).flip

end Hom

variable (S : Scheme.{u}) (p : ℕ) [Fact p.Prime] (hS : (p : Γ(S, ⊤)) = 0)

/-- The relative Frobenius as a natural transformation from the identity of `Over S` to the
Frobenius twist, that is, the base change functor `Over.pullback F_S` along the absolute
Frobenius of `S`. -/
noncomputable def relativeFrobeniusNatTrans : 𝟭 (Over S) ⟶ Over.pullback (S.frobenius p hS) where
  app X := Over.homMk (X.hom.relativeFrobenius p hS) (Hom.relativeFrobenius_snd _ _ _)
  naturality X Y g := by
    ext
    exact (Hom.relativeFrobenius_naturality hS Y.hom g.left (Over.w g)).symm

@[simp]
theorem relativeFrobeniusNatTrans_app_left (X : Over S) :
    ((relativeFrobeniusNatTrans S p hS).app X).left = X.hom.relativeFrobenius p hS :=
  (rfl)

/-- **The relative Frobenius of a group scheme is a homomorphism.** For a group scheme `G` over
`S`, the relative Frobenius `F_{G/S} : G ⟶ G^{(p)}` is a homomorphism to the Frobenius twist of
`G` with its group structure as a base change. -/
noncomputable def relativeFrobeniusGrpHom (G : Grp (Over S)) :
    G ⟶ (Over.pullback (S.frobenius p hS)).mapGrp.obj G :=
  Functor.mapGrpIdIso.inv.app G ≫ (Functor.mapGrpNatTrans (relativeFrobeniusNatTrans S p hS)).app G

-- `rfl`: the component of `Functor.mapGrpIdIso.inv` at `G` has underlying morphism `𝟙 G.X`, and
-- `(𝟙 _ ≫ g).left` reduces definitionally to `g.left` for morphisms `g` in `Over S`.
@[simp]
theorem relativeFrobeniusGrpHom_hom_hom_left (G : Grp (Over S)) :
    (relativeFrobeniusGrpHom S p hS G).hom.hom.left = G.X.hom.relativeFrobenius p hS :=
  (rfl)

/-- The relative Frobenius of a commutative group scheme `G` over `S`, as a homomorphism of
commutative group schemes `G ⟶ G^{(p)}`. -/
noncomputable def relativeFrobeniusCommGrpHom (G : CommGrp (Over S)) :
    G ⟶ (Over.pullback (S.frobenius p hS)).mapCommGrp.obj G :=
  Functor.mapCommGrpIdIso.inv.app G ≫
    (Functor.mapCommGrpNatTrans (relativeFrobeniusNatTrans S p hS)).app G

-- `rfl`: the component of `Functor.mapCommGrpIdIso.inv` at `G` has underlying morphism `𝟙 G.X`,
-- and `(𝟙 _ ≫ g).left` reduces definitionally to `g.left` for morphisms `g` in `Over S`.
@[simp]
theorem relativeFrobeniusCommGrpHom_hom_hom_hom_left (G : CommGrp (Over S)) :
    (relativeFrobeniusCommGrpHom S p hS G).hom.hom.hom.left = G.X.hom.relativeFrobenius p hS :=
  (rfl)

end AlgebraicGeometry.Scheme
