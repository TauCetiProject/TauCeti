/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Hom.BaseChange
-- Proof-only: the dual isogeny, with `φ̂ ∘ φ = [deg φ]` on points.
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Dual.Basic
-- Proof-only: the action of a morphism on points as an additive homomorphism.
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Hom.Ring

/-!
# Isogenies and quadratic relations of a field endomorphism

Let `φ : W₁ → W₂` be an isogeny of elliptic curves over a field `F`, and let `σ` be an
`F`-algebra endomorphism of an extension `K` of `F`, acting on the points of both curves over `K`.
Suppose that `σ` satisfies a quadratic relation `σ (σ P) = a₁ • σ P - q • P` at a point `P` of
`W₁(K)`, and `σ (σ Q) = a₂ • σ Q - q • Q` at its image `Q = φ P`. Since `φ` is defined over `F`,
it commutes with `σ`, so applying `φ` to the first relation and comparing with the second gives
`(a₁ - a₂) • Q = 0`. Applying the dual isogeny, `φ̂ ∘ φ = [deg φ]`, then shows that
`deg φ · (a₁ - a₂)` kills `P`.

For a Frobenius element the coefficients are the Frobenius traces of the two curves, and a point
`P` of large prime order then forces the traces to agree
(`TauCeti.Isogeny.frobeniusTrace_reduction_eq`).

## Main results

* `TauCeti.Isogeny.degree_mul_sub_zsmul_eq_zero`: `deg φ · (a₁ - a₂)` kills `P`.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.6.1 and V.2.3.1.
-/

public section

open WeierstrassCurve

namespace TauCeti.Isogeny

variable {F K : Type*} [Field F] [Field K] [Algebra F K] [DecidableEq K]
  {W₁ W₂ : WeierstrassCurve.Affine F} [W₁.IsElliptic] [W₂.IsElliptic]

/-- **Isogenies compare quadratic relations of an endomorphism of the field.** Let `φ : W₁ → W₂`
be an isogeny over `F`, let `σ` be an `F`-algebra endomorphism of an extension `K` of `F`, and let
`Q = φ P` for a point `P` of `W₁(K)`. If `σ (σ P) = a₁ • σ P - q • P` and
`σ (σ Q) = a₂ • σ Q - q • Q`, then `deg φ · (a₁ - a₂)` kills `P`. Applied to a Frobenius element,
whose quadratic relations have the Frobenius traces as coefficients, this compares the traces of
isogenous curves. -/
theorem degree_mul_sub_zsmul_eq_zero (φ : Isogeny W₁ W₂) {σ : K →ₐ[F] K} {a₁ a₂ : ℤ} {q : ℕ}
    {P : (W₁⁄K).toAffine.Point} {Q : (W₂⁄K).toAffine.Point}
    (hQ : ((Hom.ofIsogeny φ).map (algebraMap F K)).pointMap P = Q)
    (h₁ : Affine.Point.map σ (Affine.Point.map σ P) = a₁ • Affine.Point.map σ P - q • P)
    (h₂ : Affine.Point.map σ (Affine.Point.map σ Q) = a₂ • Affine.Point.map σ Q - q • Q) :
    ((φ.degree : ℤ) * (a₁ - a₂)) • P = 0 := by
  -- `φ` and its dual, as maps between the points of `W₁⁄K` and `W₂⁄K`
  set f := (Hom.ofIsogeny φ).map (algebraMap F K)
  let g : (W₁⁄K).toAffine.Point →+ (W₂⁄K).toAffine.Point := f.pointMapHom
  let g' : (W₂⁄K).toAffine.Point →+ (W₁⁄K).toAffine.Point := f.dual.pointMapHom
  have hgP : g P = Q := (Hom.pointMapHom_apply f P).trans hQ
  have hg' (R : (W₁⁄K).toAffine.Point) : g' (g R) = φ.degree • R := by
    have hd := f.dual_pointMap_pointMap R
    rw [Hom.degree_map, Hom.degree_ofIsogeny] at hd
    exact (Hom.pointMapHom_apply f.dual _).trans
      ((congrArg f.dual.pointMap (Hom.pointMapHom_apply f R)).trans hd)
  -- `φ` is defined over `F`, so it commutes with `σ`
  have hg (R : (W₁⁄K).toAffine.Point) : g (Affine.Point.map σ R) = Affine.Point.map σ (g R) :=
    (Hom.pointMapHom_apply f _).trans
      ((Hom.pointMap_map_algebraMap_map (Hom.ofIsogeny φ) σ R).trans
        (congrArg _ (Hom.pointMapHom_apply f R).symm))
  -- applying `φ` to the relation at `P` gives the relation at `Q` with `a₁` in place of `a₂`
  have hQ₀ : (a₁ - a₂) • Q = 0 := by
    apply Affine.Point.map_injective σ
    have e₁ := congrArg g h₁
    rw [hg, hg, map_sub, map_zsmul, map_nsmul, hg, hgP, h₂] at e₁
    rw [map_zsmul, _root_.map_zero, sub_zsmul, ← sub_eq_add_neg, sub_eq_zero]
    exact (sub_left_inj.mp e₁).symm
  -- so `deg φ · (a₁ - a₂)` kills `P`, through the dual of `φ`
  have hd := hg' ((a₁ - a₂) • P)
  rw [map_zsmul, hgP, hQ₀, _root_.map_zero, ← natCast_zsmul, smul_smul] at hd
  exact hd.symm

end TauCeti.Isogeny

end
