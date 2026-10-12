/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionField.GenericPoint.Basic
public import Mathlib.RingTheory.Valuation.IsTrivialOn
-- Proof-only: `moduleFinite_coordinateRing`, the finiteness that makes the coordinate ring
-- integral over `F[x]`.
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionField.Finrank
-- Proof-only: `Valuation.aeval_le_one`, bounding a valuation on every polynomial in `x`.
import TauCeti.RingTheory.Valuation.Polynomial
-- Proof-only: `Valuation.Integers.isIntegral_iff_v_le_one`, the integrality criterion.
import Mathlib.RingTheory.Valuation.Integral

/-!
# Valuations of a Weierstrass function field that are integral on the coordinate ring

For a valuation of `F(W)` trivial on `F`, having no pole at the coordinate `x` forces the valuation
to be at most `1` on the whole coordinate ring: `W.CoordinateRing` is integral over `F[x]`, and a
valuation is at most `1` exactly on what is integral over its integers. This bounds those elements;
it does not compute their values.

This is the affine-chart half of the classification of such valuations. The other half is
`WeierstrassCurve.Affine.isEquiv_infinityPlace_of_one_lt`, which settles the case `1 < v x`: there
the valuation is the place at infinity. Neither half needs any `Place` packaging — no
normalization, no surjectivity, no Dedekind hypothesis and no ellipticity — which is why they are
stated for a bare valuation.

## Main results

* `Valuation.algebraMap_coordinateRing_le_one`: a valuation trivial on `F` with `v x ≤ 1` is at
  most `1` on the whole coordinate ring.

## References

* [H. Stichtenoth, *Algebraic Function Fields and Codes*][stichtenoth2009], I.1.
-/

public section

open Polynomial WeierstrassCurve.Affine

namespace Valuation

variable {F : Type*} [Field F] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
  {W : WeierstrassCurve.Affine F} (v : Valuation W.FunctionField Γ₀) [v.IsTrivialOn F]

/-- **A valuation of the function field with no pole at `x` is integral on the coordinate ring.**
For `v` trivial on `F` with `v x ≤ 1`, every element of `W.CoordinateRing` has value at most `1`
in `F(W)`. -/
theorem algebraMap_coordinateRing_le_one
    (hx : v (algebraMap F[X] W.FunctionField Polynomial.X) ≤ 1) (r : W.CoordinateRing) :
    v (algebraMap W.CoordinateRing W.FunctionField r) ≤ 1 := by
  -- every polynomial in `x` is integral, then every element of the coordinate ring is integral
  -- over those, and a valuation is `≤ 1` exactly on the elements integral over its integers
  have hpoly : ∀ q : F[X], v (algebraMap F[X] W.FunctionField q) ≤ 1 := fun q ↦ by
    rw [algebraMap_eq_aeval_genericX]
    have hx' : v W.genericX ≤ 1 := by rwa [genericX_eq_algebraMap]
    exact v.aeval_le_one (Valuation.IsTrivialOn.valuation_algebraMap_le_one v) hx' q
  let _ : Algebra F[X] v.integer :=
    ((algebraMap F[X] W.FunctionField).codRestrict _ fun q ↦ hpoly q).toAlgebra
  -- `codRestrict` keeps the underlying function and `toAlgebra` takes that function as the algebra
  -- map, so going `F[X] → v.integer → F(W)` and going `F[X] → F(W)` are the same map by
  -- construction. Naming the equality keeps the tower from resting on an unstated unfolding.
  have halgebraMap : ∀ q : F[X],
      algebraMap v.integer W.FunctionField (algebraMap F[X] v.integer q)
        = algebraMap F[X] W.FunctionField q := fun _ ↦ rfl
  have _ : IsScalarTower F[X] v.integer W.FunctionField :=
    IsScalarTower.of_algebraMap_eq halgebraMap
  have : Algebra.IsIntegral F[X] W.CoordinateRing := Algebra.IsIntegral.of_finite _ _
  have hint : _root_.IsIntegral F[X] (algebraMap W.CoordinateRing W.FunctionField r) :=
    (Algebra.IsIntegral.isIntegral r).map
      (IsScalarTower.toAlgHom F[X] W.CoordinateRing W.FunctionField)
  exact (Valuation.Integers.isIntegral_iff_v_le_one (Valuation.integer.integers v)).1
    hint.tower_top

end Valuation

end
