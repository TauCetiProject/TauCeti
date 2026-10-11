/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.RelativeFrobenius.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.BaseChange.Basic

/-!
# Naturality of relative Frobenius

For an isogeny `φ : W₁ → W₂`, relative Frobenius satisfies the commuting square
`F_{W₂/F} ∘ φ = φ⁽ᵖ⁾ ∘ F_{W₁/F}`, where `φ⁽ᵖ⁾` is the transport of `φ` along the
Frobenius of the ground field. The same identity holds for every iterate. In particular, the
twist on the right cannot be omitted over an imperfect field: relative Frobenius has target
the Frobenius twist rather than the original curve.

Relative Frobenius also commutes with arbitrary field base change. The two possible target
curves are identified by the fact that field homomorphisms commute with Frobenius.

These identities allow compositions involving inseparable isogenies to be compared with
their Frobenius-twisted counterparts, as needed when assembling a dual from a separable
factor and a Frobenius factor. They hold for all affine Weierstrass curves, with no
ellipticity or perfectness assumption, and include exponential characteristic `1`.

## Main results

* `TauCeti.Isogeny.iterateRelativeFrobeniusIsogeny_map` and
  `TauCeti.Isogeny.relativeFrobeniusIsogeny_map`: compatibility with field base change.
* `TauCeti.Isogeny.degree_relativeFrobeniusIsogeny_map` and
  `TauCeti.Isogeny.separableDegree_relativeFrobeniusIsogeny_map`: after any base change, relative
  Frobenius still has degree `p` and separable degree `1`.
* `TauCeti.Isogeny.iterateRelativeFrobeniusIsogeny_comp`: the iterated naturality square.
* `TauCeti.Isogeny.relativeFrobeniusIsogeny_comp`: the one-step naturality square.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], II.2.11–12 and III.6.1.
-/

public section

open Polynomial WeierstrassCurve.Affine

namespace TauCeti.Isogeny

variable {F : Type*} [Field F] (p : ℕ) [ExpChar F p]
  {W₁ W₂ : WeierstrassCurve.Affine F}

/-- Iterated relative Frobenius commutes with arbitrary field base change, under the
canonical equality between the base change of the twist and the twist of the base change. -/
@[simp]
theorem iterateRelativeFrobeniusIsogeny_map {K : Type*} [Field K]
    (W : WeierstrassCurve.Affine F) (n : ℕ) (f : F →+* K) :
    let := expChar_of_injective_ringHom f.injective p
    let e : (W.map (iterateFrobenius F p n)).map f =
        (W.map f).map (iterateFrobenius K p n) :=
      congrArg W.map (f.iterateFrobenius_comm p n)
    (e ▸ (iterateRelativeFrobeniusIsogeny p W n).map f) =
      iterateRelativeFrobeniusIsogeny p (W.map f) n := by
  let := expChar_of_injective_ringHom f.injective p
  apply eq_of_pullback_coords
  · simp [iterateRelativeFrobeniusPullback_apply, CoordinateRing.iterateRelativeFrobenius_of]
  · simp [iterateRelativeFrobeniusPullback_apply]

/-- Relative Frobenius commutes with arbitrary field base change. The target curves are
identified by the fact that field homomorphisms commute with Frobenius. -/
@[simp]
theorem relativeFrobeniusIsogeny_map {K : Type*} [Field K]
    (W : WeierstrassCurve.Affine F) (f : F →+* K) :
    let := expChar_of_injective_ringHom f.injective p
    let e : (W.map (frobenius F p)).map f = (W.map f).map (frobenius K p) :=
      congrArg W.map (f.frobenius_comm p)
    (e ▸ (relativeFrobeniusIsogeny p W).map f) =
      relativeFrobeniusIsogeny p (W.map f) := by
  let := expChar_of_injective_ringHom f.injective p
  have h := iterateRelativeFrobeniusIsogeny_map p W 1 f
  simp only [iterateRelativeFrobeniusIsogeny_one] at h
  have eF := iterateFrobenius_one (R := F) p
  have eK := iterateFrobenius_one (R := K) p
  have c := f.iterateFrobenius_comm p 1
  -- Name the equalities in the target casts before generalizing the two Frobenius maps.
  -- A direct rewrite cannot change the maps without also transporting these proofs.
  change (congrArg W.map c ▸
    (congrArg W.map eF.symm ▸ relativeFrobeniusIsogeny p W).map f) =
      (congrArg (W.map f).map eK.symm ▸ relativeFrobeniusIsogeny p (W.map f)) at h
  generalize hF : iterateFrobenius F p 1 = g at eF c h
  generalize hK : iterateFrobenius K p 1 = k at eK c h
  cases eF
  cases eK
  exact h

/-- **Relative Frobenius has degree `p` after any base change**: its base change is relative
Frobenius of the base-changed curve, up to the identification of target curves in
`relativeFrobeniusIsogeny_map`, and transport along that identification keeps the degree. -/
@[simp↓]
theorem degree_relativeFrobeniusIsogeny_map {K : Type*} [Field K]
    (W : WeierstrassCurve.Affine F) (f : F →+* K) :
    ((relativeFrobeniusIsogeny p W).map f).degree = p := by
  let := expChar_of_injective_ringHom f.injective p
  -- Transport along an equality of target curves keeps the degree.
  have key : ∀ {V : WeierstrassCurve.Affine K} (e : (W.map (frobenius F p)).map f = V)
      (ψ : Isogeny (W.map f) V), e ▸ (relativeFrobeniusIsogeny p W).map f = ψ →
        ((relativeFrobeniusIsogeny p W).map f).degree = ψ.degree := by
    rintro V rfl ψ rfl
    rfl
  exact (key _ _ (relativeFrobeniusIsogeny_map p W f)).trans
    (degree_relativeFrobeniusIsogeny p (W.map f))

/-- **Relative Frobenius stays purely inseparable after any base change**: the separable degree
of its base change is `1`, by the same identification as `degree_relativeFrobeniusIsogeny_map`. -/
@[simp]
theorem separableDegree_relativeFrobeniusIsogeny_map {K : Type*} [Field K]
    (W : WeierstrassCurve.Affine F) (f : F →+* K) :
    ((relativeFrobeniusIsogeny p W).map f).separableDegree = 1 := by
  let := expChar_of_injective_ringHom f.injective p
  -- Transport along an equality of target curves keeps the separable degree.
  have key : ∀ {V : WeierstrassCurve.Affine K} (e : (W.map (frobenius F p)).map f = V)
      (ψ : Isogeny (W.map f) V), e ▸ (relativeFrobeniusIsogeny p W).map f = ψ →
        ((relativeFrobeniusIsogeny p W).map f).separableDegree = ψ.separableDegree := by
    rintro V rfl ψ rfl
    rfl
  exact (key _ _ (relativeFrobeniusIsogeny_map p W f)).trans
    (separableDegree_relativeFrobeniusIsogeny p (W.map f))

/-- Iterated relative Frobenius is natural in the isogeny: its square commutes with
the isogeny obtained by applying the iterated Frobenius to the coefficients. -/
@[simp]
theorem iterateRelativeFrobeniusIsogeny_comp (φ : Isogeny W₁ W₂) (n : ℕ) :
    (iterateRelativeFrobeniusIsogeny p W₂ n).comp φ =
      (φ.map (iterateFrobenius F p n)).comp (iterateRelativeFrobeniusIsogeny p W₁ n) := by
  apply Isogeny.ext
  apply CoordinateRing.algHom_ext
  · simp [comp_pullback, iterateRelativeFrobeniusPullback_apply,
      CoordinateRing.iterateRelativeFrobenius_of]
  · simp [comp_pullback, iterateRelativeFrobeniusPullback_apply]

/-- Relative Frobenius is natural in the isogeny. Over an imperfect field the
isogeny on the right is Frobenius-twisted, rather than the original isogeny. -/
@[simp]
theorem relativeFrobeniusIsogeny_comp (φ : Isogeny W₁ W₂) :
    (relativeFrobeniusIsogeny p W₂).comp φ =
      (φ.map (frobenius F p)).comp (relativeFrobeniusIsogeny p W₁) := by
  have h := iterateRelativeFrobeniusIsogeny_comp p φ 1
  simp only [iterateRelativeFrobeniusIsogeny_one] at h
  have e := iterateFrobenius_one (R := F) p
  -- Name the equality in both target casts so it can be generalized with the Frobenius
  -- map; a direct rewrite would leave the casts with their old endpoint.
  change (congrArg W₂.map e.symm ▸ relativeFrobeniusIsogeny p W₂).comp φ =
    (φ.map (iterateFrobenius F p 1)).comp
      (congrArg W₁.map e.symm ▸ relativeFrobeniusIsogeny p W₁) at h
  generalize hf : iterateFrobenius F p 1 = f at e h
  cases e
  exact h

end TauCeti.Isogeny

end
