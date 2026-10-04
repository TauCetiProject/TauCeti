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
* `TauCeti.Isogeny.fieldPullback_iterateRelativeFrobeniusIsogeny_map`: the coefficient
  Frobenius followed by the relative pullback is the power map on the whole function field.
* `TauCeti.Isogeny.iterateRelativeFrobeniusIsogeny_comp`: the iterated naturality square.
* `TauCeti.Isogeny.relativeFrobeniusIsogeny_comp`: the one-step naturality square.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], II.2.11–12 and III.6.1.

No material is copied from an external formalisation.
-/

public section

open Polynomial WeierstrassCurve.Affine

namespace TauCeti.Isogeny

variable {F : Type*} [Field F] (p : ℕ) [ExpChar F p]
  {W₁ W₂ : WeierstrassCurve.Affine F}

-- Compare the two coordinate values before transporting the target curve. This avoids
-- unfolding coordinate rings or pullbacks through a dependent equality cast.
private theorem eq_of_pullback_coords {K : Type*} [Field K]
    {U V V' : WeierstrassCurve.Affine K} (e : V = V')
    (φ : Isogeny U V) (ψ : Isogeny U V')
    (hx : φ.pullback (AdjoinRoot.of V.polynomial X) =
      ψ.pullback (AdjoinRoot.of V'.polynomial X))
    (hy : φ.pullback (AdjoinRoot.root V.polynomial) =
      ψ.pullback (AdjoinRoot.root V'.polynomial)) :
    (e ▸ φ) = ψ := by
  subst V'
  exact Isogeny.ext (CoordinateRing.algHom_ext hx hy)

/-- Iterated relative Frobenius commutes with arbitrary field base change, under the
canonical equality between the base change of the twist and the twist of the base change. -/
@[simp]
theorem iterateRelativeFrobeniusIsogeny_map {K : Type*} [Field K] [ExpChar K p]
    (W : WeierstrassCurve.Affine F) (n : ℕ) (f : F →+* K) :
    let e : (W.map (iterateFrobenius F p n)).map f =
        (W.map f).map (iterateFrobenius K p n) :=
      congrArg W.map (f.iterateFrobenius_comm p n)
    (e ▸ (iterateRelativeFrobeniusIsogeny p W n).map f) =
      iterateRelativeFrobeniusIsogeny p (W.map f) n := by
  apply eq_of_pullback_coords
  · simp [iterateRelativeFrobeniusPullback_apply, CoordinateRing.iterateRelativeFrobenius_of]
  · simp [iterateRelativeFrobeniusPullback_apply]

/-- Relative Frobenius commutes with arbitrary field base change. The target curves are
identified by the fact that field homomorphisms commute with Frobenius. -/
@[simp]
theorem relativeFrobeniusIsogeny_map {K : Type*} [Field K] [ExpChar K p]
    (W : WeierstrassCurve.Affine F) (f : F →+* K) :
    let e : (W.map (frobenius F p)).map f = (W.map f).map (frobenius K p) :=
      congrArg W.map (f.frobenius_comm p)
    (e ▸ (relativeFrobeniusIsogeny p W).map f) =
      relativeFrobeniusIsogeny p (W.map f) := by
  apply eq_of_pullback_coords
  · simp [relativeFrobeniusPullback_apply, CoordinateRing.relativeFrobenius_of]
  · simp [relativeFrobeniusPullback_apply]

/-- The coefficient Frobenius followed by the iterated relative Frobenius pullback is
the `p ^ n`-power map on the function field, including its rational functions. -/
@[simp]
theorem fieldPullback_iterateRelativeFrobeniusIsogeny_map
    (W : WeierstrassCurve.Affine F) (n : ℕ) (z : W.FunctionField) :
    (iterateRelativeFrobeniusIsogeny p W n).fieldPullback
        (FunctionField.map W (iterateFrobenius F p n) z) = z ^ p ^ n := by
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := W.CoordinateRing) z
  simp [div_pow]

/-- The coefficient Frobenius followed by relative Frobenius is the `p`-power map on
the function field. -/
@[simp]
theorem fieldPullback_relativeFrobeniusIsogeny_map
    (W : WeierstrassCurve.Affine F) (z : W.FunctionField) :
    (relativeFrobeniusIsogeny p W).fieldPullback
        (FunctionField.map W (frobenius F p) z) = z ^ p := by
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := W.CoordinateRing) z
  simp [div_pow]

/-- Iterated relative Frobenius is natural in the isogeny: its square commutes with
the isogeny obtained by applying the iterated Frobenius to the coefficients. -/
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
theorem relativeFrobeniusIsogeny_comp (φ : Isogeny W₁ W₂) :
    (relativeFrobeniusIsogeny p W₂).comp φ =
      (φ.map (frobenius F p)).comp (relativeFrobeniusIsogeny p W₁) := by
  apply Isogeny.ext
  apply CoordinateRing.algHom_ext
  · simp [comp_pullback, relativeFrobeniusPullback_apply, CoordinateRing.relativeFrobenius_of]
  · simp [comp_pullback, relativeFrobeniusPullback_apply]

end TauCeti.Isogeny

end
