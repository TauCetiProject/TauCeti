/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Frobenius.Iterate
public import TauCeti.AlgebraicGeometry.Frobenius.Relative

/-!
# Iterated Frobenius twists and the iterated relative Frobenius

Let `p` be a prime, `S` a scheme in which `p` vanishes, `F_S^n : S ⟶ S` the `n`-fold absolute
Frobenius of `S`, and `π : X ⟶ S` a scheme over `S`. The `n`-th *Frobenius twist* of `X` is the
base change `X^{(p^n)} = X ×_{S, F_S^n} S`, a scheme over `S` through its second projection.
Since `F_X^n` commutes with `π`, the `n`-fold absolute Frobenius `F_X^n` and `π` define the
*iterated relative Frobenius*

`F^n_{X/S} : X ⟶ X^{(p^n)}`,

a morphism over `S` whose composite with the first projection `X^{(p^n)} ⟶ X` is `F_X^n`. For
`n = 1` it is the relative Frobenius `F_{X/S}` of
`TauCeti.AlgebraicGeometry.Frobenius.Relative`.

The twists are compatible with the exponents: the zeroth twist is `X`, and twisting the `m`-th
twist `X^{(p^m)}` (as a scheme over `S` through its second projection) once more by `F_S^n` gives
the `(m + n)`-th twist. Under these identifications the zeroth iterated relative Frobenius is the
identity, and the iterated relative Frobenius of `X` for `m + n` is that of `X` for `m` followed
by that of `X^{(p^m)}` for `n`. In particular `F^{n+1}_{X/S}` is `F^n_{X/S}` followed by the
relative Frobenius of the `n`-th twist. As in the case `n = 1`, the iterated relative Frobenius is
natural in `X` over `S`, commutes with every base change `T ⟶ S`, and lifts to a homomorphism of
group schemes `G ⟶ G^{(p^n)}` for every group scheme `G` over `S`.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.iterateRelativeFrobenius π p hS n`: the iterated relative
  Frobenius `F^n_{X/S} : X ⟶ X ×_{S, F_S^n} S`.
* `AlgebraicGeometry.Scheme.Hom.iterateFrobeniusTwistZeroIso`: the zeroth twist is `X`.
* `AlgebraicGeometry.Scheme.Hom.iterateFrobeniusTwistSuccIso`: the Frobenius twist of the `n`-th
  twist is the `(n + 1)`-th twist.
* `AlgebraicGeometry.Scheme.Hom.iterateFrobeniusTwistAddIso`: the `n`-th twist of the `m`-th twist
  is the `(m + n)`-th twist.
* `AlgebraicGeometry.Scheme.Hom.iterateFrobeniusTwistMap π p hS n f`: the projection from the
  `n`-th twist of the base change of `X` along `f : T ⟶ S` to the `n`-th twist of `X`.
* `AlgebraicGeometry.Scheme.iterateRelativeFrobeniusNatTrans S p hS n`: the iterated relative
  Frobenius as a natural transformation `𝟭 (Over S) ⟶ Over.pullback F_S^n`, and
  `AlgebraicGeometry.Scheme.iterateRelativeFrobeniusGrpHom` its value on group schemes.

## Main results

* `AlgebraicGeometry.Scheme.Hom.iterateRelativeFrobenius_zero`,
  `AlgebraicGeometry.Scheme.Hom.iterateRelativeFrobenius_one`,
  `AlgebraicGeometry.Scheme.Hom.iterateRelativeFrobenius_succ` and
  `AlgebraicGeometry.Scheme.Hom.iterateRelativeFrobenius_add`: the iteration laws.
* `AlgebraicGeometry.Scheme.Hom.iterateRelativeFrobenius_naturality`: `F^n_{X/S}` is natural in
  `X` over `S`.
* `AlgebraicGeometry.Scheme.Hom.isPullback_iterateFrobeniusTwistMap` and
  `AlgebraicGeometry.Scheme.Hom.isPullback_iterateRelativeFrobenius`: the `n`-th twist and the
  iterated relative Frobenius commute with base change.

## References

* The Stacks Project, chapter Varieties, section Frobenii, Remark 33.36.11, for the iterated
  relative Frobenius.
-/

public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme

namespace Hom

variable {X Y S T : Scheme.{u}} (π : X ⟶ S) (p : ℕ) [Fact p.Prime] (hS : (p : Γ(S, ⊤)) = 0)

/-- The **iterated relative Frobenius** `F^n_{X/S} : X ⟶ X^{(p^n)} = X ×_{S, F_S^n} S` of a scheme
`π : X ⟶ S` over a scheme `S` in which the prime `p` vanishes: the morphism to the `n`-th
Frobenius twist whose components are the `n`-fold absolute Frobenius `F_X^n` and `π`. -/
noncomputable def iterateRelativeFrobenius (n : ℕ) :
    X ⟶ pullback π (S.iterateFrobenius p hS n) :=
  pullback.lift (X.iterateFrobenius p (natCast_eq_zero_of_hom π hS) n) π
    (iterateFrobenius_naturality _ hS π n)

/-- The iterated relative Frobenius followed by the projection `X^{(p^n)} ⟶ X` is the `n`-fold
absolute Frobenius. -/
@[reassoc (attr := simp)]
theorem iterateRelativeFrobenius_fst (n : ℕ) :
    π.iterateRelativeFrobenius p hS n ≫ pullback.fst _ _ =
      X.iterateFrobenius p (natCast_eq_zero_of_hom π hS) n :=
  pullback.lift_fst _ _ _

/-- The iterated relative Frobenius is a morphism over `S`. -/
@[reassoc (attr := simp)]
theorem iterateRelativeFrobenius_snd (n : ℕ) :
    π.iterateRelativeFrobenius p hS n ≫ pullback.snd _ _ = π :=
  pullback.lift_snd _ _ _

/-- The projection `X^{(p^n)} ⟶ X` from the `n`-th Frobenius twist, followed by the iterated
relative Frobenius, is the `n`-fold absolute Frobenius of the twist. -/
@[reassoc (attr := simp)]
theorem fst_iterateRelativeFrobenius (n : ℕ) :
    pullback.fst π (S.iterateFrobenius p hS n) ≫ π.iterateRelativeFrobenius p hS n =
      (pullback π (S.iterateFrobenius p hS n)).iterateFrobenius p
        (natCast_eq_zero_of_hom (pullback.snd _ _) hS) n := by
  ext
  · rw [Category.assoc, iterateRelativeFrobenius_fst,
      iterateFrobenius_naturality _ (natCast_eq_zero_of_hom π hS)]
  · rw [Category.assoc, iterateRelativeFrobenius_snd, pullback.condition,
      iterateFrobenius_naturality _ hS]

/-- The zeroth Frobenius twist `X ×_{S, F_S^0} S` of `X` is `X`, through the first projection. -/
noncomputable def iterateFrobeniusTwistZeroIso :
    pullback π (S.iterateFrobenius p hS 0) ≅ X :=
  pullback.congrHom rfl (iterateFrobenius_zero hS) ≪≫ asIso (pullback.fst π (𝟙 S))

@[simp]
theorem iterateFrobeniusTwistZeroIso_hom :
    (π.iterateFrobeniusTwistZeroIso p hS).hom = pullback.fst _ _ := by
  simp [iterateFrobeniusTwistZeroIso]

/-- The Frobenius twist `X^{(p^n)} ×_{S, F_S} S` of the `n`-th Frobenius twist of `X`, a scheme
over `S` through its second projection, is the `(n + 1)`-th Frobenius twist of `X`. -/
noncomputable def iterateFrobeniusTwistSuccIso (n : ℕ) :
    pullback (pullback.snd π (S.iterateFrobenius p hS n)) (S.frobenius p hS) ≅
      pullback π (S.iterateFrobenius p hS (n + 1)) :=
  pullbackLeftPullbackSndIso _ _ _ ≪≫
    pullback.congrHom rfl (by rw [← iterateFrobenius_one hS, ← iterateFrobenius_add, add_comm])

@[reassoc (attr := simp)]
theorem iterateFrobeniusTwistSuccIso_hom_fst (n : ℕ) :
    (π.iterateFrobeniusTwistSuccIso p hS n).hom ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ pullback.fst _ _ := by
  simp [iterateFrobeniusTwistSuccIso]

@[reassoc (attr := simp)]
theorem iterateFrobeniusTwistSuccIso_hom_snd (n : ℕ) :
    (π.iterateFrobeniusTwistSuccIso p hS n).hom ≫ pullback.snd _ _ = pullback.snd _ _ := by
  simp [iterateFrobeniusTwistSuccIso]

/-- The `n`-th Frobenius twist `X^{(p^m)} ×_{S, F_S^n} S` of the `m`-th Frobenius twist of `X`, a
scheme over `S` through its second projection, is the `(m + n)`-th Frobenius twist of `X`. -/
noncomputable def iterateFrobeniusTwistAddIso (m n : ℕ) :
    pullback (pullback.snd π (S.iterateFrobenius p hS m)) (S.iterateFrobenius p hS n) ≅
      pullback π (S.iterateFrobenius p hS (m + n)) :=
  pullbackLeftPullbackSndIso _ _ _ ≪≫
    pullback.congrHom rfl (by rw [← iterateFrobenius_add, add_comm])

@[reassoc (attr := simp)]
theorem iterateFrobeniusTwistAddIso_hom_fst (m n : ℕ) :
    (π.iterateFrobeniusTwistAddIso p hS m n).hom ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ pullback.fst _ _ := by
  simp [iterateFrobeniusTwistAddIso]

@[reassoc (attr := simp)]
theorem iterateFrobeniusTwistAddIso_hom_snd (m n : ℕ) :
    (π.iterateFrobeniusTwistAddIso p hS m n).hom ≫ pullback.snd _ _ = pullback.snd _ _ := by
  simp [iterateFrobeniusTwistAddIso]

/-- The zeroth iterated relative Frobenius is the identity, under the identification of the
zeroth Frobenius twist of `X` with `X`. -/
@[reassoc]
theorem iterateRelativeFrobenius_zero :
    π.iterateRelativeFrobenius p hS 0 ≫ (π.iterateFrobeniusTwistZeroIso p hS).hom = 𝟙 X := by
  simp

/-- The first iterated relative Frobenius is the relative Frobenius, under the identification of
`X ×_{S, F_S^1} S` with the Frobenius twist `X ×_{S, F_S} S`. -/
@[reassoc]
theorem iterateRelativeFrobenius_one :
    π.iterateRelativeFrobenius p hS 1 ≫ (pullback.congrHom rfl (iterateFrobenius_one hS)).hom =
      π.relativeFrobenius p hS := by
  ext <;> simp

/-- The `(n + 1)`-th iterated relative Frobenius of `X` is the `n`-th iterated relative Frobenius
`X ⟶ X^{(p^n)}` followed by the relative Frobenius of the `n`-th Frobenius twist `X^{(p^n)}` over
`S`. -/
theorem iterateRelativeFrobenius_succ (n : ℕ) :
    π.iterateRelativeFrobenius p hS (n + 1) =
      π.iterateRelativeFrobenius p hS n ≫
        (pullback.snd π (S.iterateFrobenius p hS n)).relativeFrobenius p hS ≫
          (π.iterateFrobeniusTwistSuccIso p hS n).hom := by
  ext
  · simp [iterateFrobenius_succ, frobenius_naturality _ (natCast_eq_zero_of_hom π hS)]
  · simp

/-- The `(m + n)`-th iterated relative Frobenius of `X` is the `m`-th iterated relative
Frobenius `X ⟶ X^{(p^m)}` followed by the `n`-th iterated relative Frobenius of the `m`-th
Frobenius twist `X^{(p^m)}` over `S`. -/
theorem iterateRelativeFrobenius_add (m n : ℕ) :
    π.iterateRelativeFrobenius p hS (m + n) =
      π.iterateRelativeFrobenius p hS m ≫
        (pullback.snd π (S.iterateFrobenius p hS m)).iterateRelativeFrobenius p hS n ≫
          (π.iterateFrobeniusTwistAddIso p hS m n).hom := by
  ext
  · simp only [Category.assoc, iterateFrobeniusTwistAddIso_hom_fst,
      iterateRelativeFrobenius_fst_assoc]
    rw [iterateFrobenius_naturality _ (natCast_eq_zero_of_hom π hS)]
    simp [iterateFrobenius_add]
  · simp

variable {π p}

/-- **The iterated relative Frobenius is natural** in the scheme over `S`: for a morphism
`g : X ⟶ Y` over `S`, the iterated relative Frobenius of `Y` after `g` is the iterated relative
Frobenius of `X` followed by the morphism `X^{(p^n)} ⟶ Y^{(p^n)}` induced by `g`. -/
@[reassoc]
theorem iterateRelativeFrobenius_naturality (πY : Y ⟶ S) (g : X ⟶ Y) (hg : g ≫ πY = π)
    (n : ℕ) :
    π.iterateRelativeFrobenius p hS n ≫
        pullback.map π _ πY _ g (𝟙 _) (𝟙 _) (by simp [hg]) (by simp) =
      g ≫ πY.iterateRelativeFrobenius p hS n := by
  ext <;> simp [iterateFrobenius_naturality _ (natCast_eq_zero_of_hom πY hS) g, hg]

variable (π p)

/-- The projection from the `n`-th Frobenius twist `(X ×_S T)^{(p^n)}` of the base change of `X`
along `f : T ⟶ S` to the `n`-th Frobenius twist `X^{(p^n)}` of `X`, induced by the projection
`X ×_S T ⟶ X` and by `f`. -/
noncomputable def iterateFrobeniusTwistMap (n : ℕ) (f : T ⟶ S) :
    pullback (pullback.snd π f) (T.iterateFrobenius p (natCast_eq_zero_of_hom f hS) n) ⟶
      pullback π (S.iterateFrobenius p hS n) :=
  pullback.map _ _ _ _ (pullback.fst π f) f f pullback.condition.symm
    (iterateFrobenius_naturality _ hS f n)

/-- The projection between `n`-th Frobenius twists, followed by the projection
`X^{(p^n)} ⟶ X`, is the projection `(X ×_S T)^{(p^n)} ⟶ X ×_S T` followed by the projection
`X ×_S T ⟶ X`. -/
@[reassoc (attr := simp)]
theorem iterateFrobeniusTwistMap_fst (n : ℕ) (f : T ⟶ S) :
    π.iterateFrobeniusTwistMap p hS n f ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ pullback.fst π f :=
  pullback.lift_fst _ _ _

/-- The projection between `n`-th Frobenius twists lies over `f : T ⟶ S`. -/
@[reassoc (attr := simp)]
theorem iterateFrobeniusTwistMap_snd (n : ℕ) (f : T ⟶ S) :
    π.iterateFrobeniusTwistMap p hS n f ≫ pullback.snd _ _ = pullback.snd _ _ ≫ f :=
  pullback.lift_snd _ _ _

variable {π p}

/-- **The iterated Frobenius twist commutes with base change.** For `f : T ⟶ S`, the `n`-th
Frobenius twist of `X ×_S T` over `T` is the base change of the `n`-th Frobenius twist
`X^{(p^n)}` of `X` along `f`. -/
theorem isPullback_iterateFrobeniusTwistMap (n : ℕ) (f : T ⟶ S) :
    IsPullback (π.iterateFrobeniusTwistMap p hS n f) (pullback.snd _ _) (pullback.snd _ _) f := by
  refine IsPullback.of_right ?_ (by simp) (IsPullback.of_hasPullback π _)
  -- the composite of the two squares is the composite of the pullback squares defining
  -- `X ×_S T` and its `n`-th Frobenius twist, since `F_T^n ≫ f = f ≫ F_S^n`
  have h := (IsPullback.of_hasPullback (pullback.snd π f)
    (T.iterateFrobenius p (natCast_eq_zero_of_hom f hS) n)).paste_horiz
      (IsPullback.of_hasPullback π f)
  rw [iterateFrobenius_naturality _ hS f n] at h
  simpa using h

/-- The iterated relative Frobenius of the base change `X ×_S T` over `T`, followed by the
projection to the `n`-th Frobenius twist of `X`, is the projection `X ×_S T ⟶ X` followed by the
iterated relative Frobenius of `X`. -/
@[reassoc (attr := simp)]
theorem iterateRelativeFrobenius_iterateFrobeniusTwistMap (n : ℕ) (f : T ⟶ S) :
    (pullback.snd π f).iterateRelativeFrobenius p (natCast_eq_zero_of_hom f hS) n ≫
        π.iterateFrobeniusTwistMap p hS n f =
      pullback.fst π f ≫ π.iterateRelativeFrobenius p hS n := by
  ext <;> simp [iterateFrobenius_naturality _ (natCast_eq_zero_of_hom π hS) (pullback.fst π f),
    pullback.condition]

/-- **The iterated relative Frobenius commutes with base change.** For `f : T ⟶ S`, the `n`-th
iterated relative Frobenius of `X ×_S T` over `T` is the base change along `f` of the `n`-th
iterated relative Frobenius of `X` over `S`. -/
theorem isPullback_iterateRelativeFrobenius (n : ℕ) (f : T ⟶ S) :
    IsPullback ((pullback.snd π f).iterateRelativeFrobenius p (natCast_eq_zero_of_hom f hS) n)
      (pullback.fst π f) (π.iterateFrobeniusTwistMap p hS n f)
      (π.iterateRelativeFrobenius p hS n) := by
  refine IsPullback.of_right ?_ (iterateRelativeFrobenius_iterateFrobeniusTwistMap hS n f)
    (isPullback_iterateFrobeniusTwistMap hS n f).flip
  simpa using (IsPullback.of_hasPullback π f).flip

end Hom

variable (S : Scheme.{u}) (p : ℕ) [Fact p.Prime] (hS : (p : Γ(S, ⊤)) = 0) (n : ℕ)

/-- The iterated relative Frobenius as a natural transformation from the identity of `Over S` to
the `n`-th Frobenius twist, that is, the base change functor `Over.pullback F_S^n` along the
`n`-fold absolute Frobenius of `S`. -/
noncomputable def iterateRelativeFrobeniusNatTrans :
    𝟭 (Over S) ⟶ Over.pullback (S.iterateFrobenius p hS n) where
  app X := Over.homMk (X.hom.iterateRelativeFrobenius p hS n)
    (Hom.iterateRelativeFrobenius_snd _ _ _ _)
  naturality X Y g := by
    ext
    exact (Hom.iterateRelativeFrobenius_naturality hS Y.hom g.left (Over.w g) n).symm

@[simp]
theorem iterateRelativeFrobeniusNatTrans_app_left (X : Over S) :
    ((iterateRelativeFrobeniusNatTrans S p hS n).app X).left =
      X.hom.iterateRelativeFrobenius p hS n :=
  (rfl)

/-- **The iterated relative Frobenius of a group scheme is a homomorphism.** For a group scheme
`G` over `S`, the iterated relative Frobenius `F^n_{G/S} : G ⟶ G^{(p^n)}` is a homomorphism to the
`n`-th Frobenius twist of `G` with its group structure as a base change. -/
noncomputable def iterateRelativeFrobeniusGrpHom (G : Grp (Over S)) :
    G ⟶ (Over.pullback (S.iterateFrobenius p hS n)).mapGrp.obj G :=
  Functor.mapGrpIdIso.inv.app G ≫
    (Functor.mapGrpNatTrans (iterateRelativeFrobeniusNatTrans S p hS n)).app G

-- `rfl`: the component of `Functor.mapGrpIdIso.inv` at `G` has underlying morphism `𝟙 G.X`, and
-- `(𝟙 _ ≫ g).left` reduces definitionally to `g.left` for morphisms `g` in `Over S`.
@[simp]
theorem iterateRelativeFrobeniusGrpHom_hom_hom_left (G : Grp (Over S)) :
    (iterateRelativeFrobeniusGrpHom S p hS n G).hom.hom.left =
      G.X.hom.iterateRelativeFrobenius p hS n :=
  (rfl)

/-- The iterated relative Frobenius of a commutative group scheme `G` over `S`, as a homomorphism
of commutative group schemes `G ⟶ G^{(p^n)}`. -/
noncomputable def iterateRelativeFrobeniusCommGrpHom (G : CommGrp (Over S)) :
    G ⟶ (Over.pullback (S.iterateFrobenius p hS n)).mapCommGrp.obj G :=
  Functor.mapCommGrpIdIso.inv.app G ≫
    (Functor.mapCommGrpNatTrans (iterateRelativeFrobeniusNatTrans S p hS n)).app G

-- `rfl`: the component of `Functor.mapCommGrpIdIso.inv` at `G` has underlying morphism `𝟙 G.X`,
-- and `(𝟙 _ ≫ g).left` reduces definitionally to `g.left` for morphisms `g` in `Over S`.
@[simp]
theorem iterateRelativeFrobeniusCommGrpHom_hom_hom_hom_left (G : CommGrp (Over S)) :
    (iterateRelativeFrobeniusCommGrpHom S p hS n G).hom.hom.hom.left =
      G.X.hom.iterateRelativeFrobenius p hS n :=
  (rfl)

end AlgebraicGeometry.Scheme
