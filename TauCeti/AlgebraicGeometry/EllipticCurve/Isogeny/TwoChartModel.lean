/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.TwoChartModel.Restrict
public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionField.PointPlace
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.InfinityPlace

/-!
# Isogenies as morphisms of the curves of their function fields

Let `W₁` and `W₂` be affine Weierstrass curves over a field `F`. The function field `F(Wᵢ)` is
an algebraic function field over `F` in which the coordinate `x` is transcendental, so it has a
two-chart model `Xᵢ`, a regular proper curve over `F`, glued from the normalizations of `F[x]` and
`F[x⁻¹]` in `F(Wᵢ)`. Its codimension-one points are the places of `F(Wᵢ)`, and the point `Oᵢ`
of the place at infinity of `Wᵢ` is the point at infinity.

Every `F`-embedding `σ : F(W₂) → F(W₁)` induces a dominant `F`-morphism `X₁ ⟶ X₂` whose pullback
of rational functions is `σ`, and a dominant `F`-morphism `X₁ ⟶ X₂` is determined by its pullback
of rational functions (`TauCeti.AlgebraicGeometry.twoChartModel.eq_homOfAlgHom_iff`). This file
proves that **the morphism induced by `σ` sends `O₁` to `O₂` exactly when the coordinate pullback
restricted from `σ` maps infinity to infinity**, that is, exactly when `σ` is the function-field
pullback of an isogeny `W₁ → W₂` (`TauCeti.Isogeny.fieldPullback_unique`). The morphism acts on
points by restricting places along `σ`
(`TauCeti.AlgebraicGeometry.twoChartModel.homOfAlgHom_equivPlace_symm_eq_iff`), so it sends `O₁` to
`O₂` exactly when the place at infinity of `W₁` restricts to the place at infinity of `W₂`, which
is the place-level form of pointedness
(`TauCeti.CoordinatePullback.mapsInfinity_iff_isEquiv_comap_infinityPlace`). Thus, among the
morphisms of curves `X₁ ⟶ X₂` induced by embeddings of function fields, the ones preserving the
points at infinity are exactly those induced by isogenies.

No ellipticity is assumed: the statements hold for every affine Weierstrass curve over a field.

## Main results

* `TauCeti.CoordinatePullback.mapsInfinity_iff_homOfAlgHom_equivPlace_symm_infinity`: the
  coordinate pullback restricted from `σ` maps infinity to infinity exactly when the morphism of
  two-chart models induced by `σ` sends `O₁` to `O₂`.
* `TauCeti.Isogeny.homOfAlgHom_fieldPullback_equivPlace_symm_infinity`: the morphism of two-chart
  models induced by an isogeny sends `O₁` to `O₂`.

## References

* J. Silverman, *The Arithmetic of Elliptic Curves*, 2nd ed., GTM 106, Springer, 2009,
  Section II.2 and Definition III.4.1.
* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Appendix B.
-/

public section

open _root_.WeierstrassCurve.Affine TauCeti.AlgebraicGeometry

namespace TauCeti

universe u

variable {F : Type u} [Field F] {W₁ W₂ : WeierstrassCurve.Affine F}

namespace CoordinatePullback

/-- **Pointedness is preservation of the points at infinity of the two-chart models.** For an
embedding `σ : F(W₂) → F(W₁)`, the coordinate pullback restricted from `σ` maps infinity to
infinity exactly when the morphism of two-chart models induced by `σ`, built from the coordinates
`x`, sends the point at infinity of `W₁` to the point at infinity of `W₂`. -/
theorem mapsInfinity_iff_homOfAlgHom_equivPlace_symm_infinity
    (σ : W₂.FunctionField →ₐ[F] W₁.FunctionField) :
    MapsInfinity (σ.comp (IsScalarTower.toAlgHom F W₂.CoordinateRing W₂.FunctionField)) ↔
      twoChartModel.homOfAlgHom W₂.isFunctionField W₁.isFunctionField
          (transcendental_genericX W₂).ne_zero (transcendental_genericX W₁).ne_zero
          (transcendental_genericX W₂) (transcendental_genericX W₁) σ
          ((twoChartModel.equivPlace (transcendental_genericX W₁)).symm (Place.infinity W₁) :
            twoChartModel W₁.isFunctionField (transcendental_genericX W₁).ne_zero) =
        ((twoChartModel.equivPlace (transcendental_genericX W₂)).symm (Place.infinity W₂) :
          twoChartModel W₂.isFunctionField (transcendental_genericX W₂).ne_zero) := by
  -- View `F(W₁)` as an algebraic extension of `F(W₂)` through `σ`.
  let : Algebra W₂.FunctionField W₁.FunctionField := σ.toRingHom.toAlgebra
  have : IsScalarTower F W₂.FunctionField W₁.FunctionField :=
    IsScalarTower.of_algebraMap_eq fun c ↦ (σ.commutes c).symm
  have : Algebra.IsAlgebraic W₂.FunctionField W₁.FunctionField :=
    W₂.isFunctionField.isAlgebraic_of_isFunctionField W₁.isFunctionField
  have hσ : IsScalarTower.toAlgHom F W₂.FunctionField W₁.FunctionField = σ :=
    AlgHom.ext fun z ↦ by simp [RingHom.algebraMap_toAlgebra]
  rw [mapsInfinity_iff_isEquiv_comap_infinityPlace, ← hσ,
    twoChartModel.homOfAlgHom_equivPlace_symm_eq_iff, Place.restrict_eq_iff_isEquiv_comap,
    Place.valuation_infinity, Place.valuation_infinity, AlgHom.toRingHom_eq_coe,
    IsScalarTower.coe_toAlgHom]

end CoordinatePullback

namespace Isogeny

/-- **An isogeny preserves the points at infinity of the two-chart models**: the morphism of
two-chart models induced by the function-field pullback of an isogeny `W₁ → W₂` sends the point at
infinity of `W₁` to the point at infinity of `W₂`. -/
theorem homOfAlgHom_fieldPullback_equivPlace_symm_infinity (φ : Isogeny W₁ W₂) :
    twoChartModel.homOfAlgHom W₂.isFunctionField W₁.isFunctionField
        (transcendental_genericX W₂).ne_zero (transcendental_genericX W₁).ne_zero
        (transcendental_genericX W₂) (transcendental_genericX W₁) φ.fieldPullback
        ((twoChartModel.equivPlace (transcendental_genericX W₁)).symm (Place.infinity W₁) :
          twoChartModel W₁.isFunctionField (transcendental_genericX W₁).ne_zero) =
      ((twoChartModel.equivPlace (transcendental_genericX W₂)).symm (Place.infinity W₂) :
        twoChartModel W₂.isFunctionField (transcendental_genericX W₂).ne_zero) := by
  refine (CoordinatePullback.mapsInfinity_iff_homOfAlgHom_equivPlace_symm_infinity _).mp ?_
  rw [show φ.fieldPullback.comp (IsScalarTower.toAlgHom F W₂.CoordinateRing W₂.FunctionField) =
    φ.pullback from AlgHom.ext fun c ↦ fieldPullback_algebraMap φ c]
  exact φ.mapsInfinity

end Isogeny

end TauCeti
