/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.Place
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.IntermediateRing.Rank
-- Proof-only: the extension of a height one prime to an overring, read off its valuation.
import TauCeti.RingTheory.DedekindDomain.Overring
-- Proof-only: a valuation with no pole at `x` is at most `1` on the coordinate ring.
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionField.CoordinateRingIntegral
-- Proof-only: the valuation of a point is that of a place, hence trivial on the constants.
import TauCeti.FieldTheory.FunctionField.AffineModel.Prime
-- Proof-only: `Valuation.Integers.isIntegral_iff_v_le_one`, the integrality criterion.
import Mathlib.RingTheory.Valuation.Integral
-- Proof-only: `Valuation.IsTrivialOn.comap`, triviality on `F` restricted along the pullback.
import TauCeti.RingTheory.Valuation.IsTrivialOn

/-!
# The ideal of a point in the intermediate ring of an isogeny

Let `φ : W₁ → W₂` be an isogeny, and `P = (x, y)` an affine point of `W₁`, with ideal
`⟨X - x, Y - y⟩` of `W₁.CoordinateRing`. The intermediate ring of `φ` sits between that coordinate
ring and `W₁.FunctionField`; geometrically it is the ring of functions regular away from the fibre
`φ⁻¹(O₂)`. Extending the ideal of `P` into it therefore depends only on whether `P` lies in that
fibre:

* if `P` lies over `O₂` — the pulled-back coordinate `φ^* x₂` has a pole at `P` — the extended
  ideal is the unit ideal, since the intermediate ring contains `φ^* x₂`;
* otherwise the whole intermediate ring lies in the valuation ring of `P`, so the valuation of `P`
  is that of a height one prime of the intermediate ring, and the extended ideal is that prime.

These are the two cases of the ideal extension that `TauCeti.Isogeny.pushClass` performs before
taking the relative norm down to `W₂.CoordinateRing`, which is how the class-group point map
`TauCeti.Isogeny.toPointHom` evaluates at `P`.

## Main results

* `TauCeti.Isogeny.map_XYIdeal_eq_top_of_one_lt_valuation`: the ideal of a point over `O₂` extends
  to the unit ideal.
* `TauCeti.Isogeny.valuation_le_one_of_valuation_pullback_X_le_one`: the intermediate ring lies in
  the valuation ring of any other point.
* `TauCeti.Isogeny.map_XYIdeal_eq_asIdeal_of_valuation_eq`: the ideal of such a point extends to the
  prime of the intermediate ring carrying its valuation.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], II.2 and III.3.
-/

public section

open Polynomial WeierstrassCurve.Affine IsDedekindDomain

namespace TauCeti

namespace Isogeny

variable {F : Type*} [Field F] {W₁ W₂ : WeierstrassCurve.Affine F} (φ : Isogeny W₁ W₂)

/-- The source coordinate ring, the intermediate ring and the source function field form a scalar
tower, for the algebra structure `toIntermediateRing` induces. -/
private theorem isScalarTower_toIntermediateRing :
    letI := φ.toIntermediateRing.toAlgebra
    IsScalarTower W₁.CoordinateRing φ.intermediateRing W₁.FunctionField :=
  letI := φ.toIntermediateRing.toAlgebra
  .of_algebraMap_eq fun r ↦ (φ.coe_toIntermediateRing r).symm

variable [IsIntegrallyClosed W₁.CoordinateRing]

local instance : IsDedekindDomain W₁.CoordinateRing :=
  W₁.isDedekindDomain_coordinateRing_of_isIntegrallyClosed

/-- **The ideal of a point over `O₂` extends to the unit ideal of the intermediate ring.** If the
pulled-back coordinate `φ^* x₂` has a pole at the affine point `(x, y)` of `W₁`, that is, if the
point lies in the fibre of `φ` over the point at infinity of `W₂`, then `⟨X - x, Y - y⟩` generates
the unit ideal, the intermediate ring containing `φ^* x₂`. -/
theorem map_XYIdeal_eq_top_of_one_lt_valuation {x y : F} (h : W₁.Equation x y)
    (hP : 1 < (CoordinateRing.pointPlace h).valuation W₁.FunctionField
      (φ.pullback (algebraMap F[X] W₂.CoordinateRing X))) :
    (CoordinateRing.XYIdeal W₁ x (C y)).map φ.toIntermediateRing = ⊤ := by
  let _ := φ.toIntermediateRing.toAlgebra
  have := φ.isScalarTower_toIntermediateRing
  have hb : 1 < (CoordinateRing.pointPlace h).valuation W₁.FunctionField
      (algebraMap φ.intermediateRing W₁.FunctionField
        (φ.pullbackToIntermediateRing (algebraMap F[X] W₂.CoordinateRing X))) := by
    rwa [Algebra.algebraMap_ofSubsemiring_apply, coe_pullbackToIntermediateRing]
  have key := (CoordinateRing.pointPlace h).map_asIdeal_eq_top_of_one_lt_valuation hb
  rwa [CoordinateRing.pointPlace_asIdeal, RingHom.algebraMap_toAlgebra] at key

/-- **The intermediate ring lies in the valuation ring of a point off the fibre over `O₂`.** If
`φ^* x₂` has no pole at the affine point `(x, y)` of `W₁`, then neither has any function pulled
back from `W₂`, the coordinate ring of `W₂` being integral over `F[x₂]`; nor, by integrality, has
any element of the intermediate ring. -/
theorem valuation_le_one_of_valuation_pullback_X_le_one {x y : F} (h : W₁.Equation x y)
    (hP : (CoordinateRing.pointPlace h).valuation W₁.FunctionField
      (φ.pullback (algebraMap F[X] W₂.CoordinateRing X)) ≤ 1) (b : φ.intermediateRing) :
    (CoordinateRing.pointPlace h).valuation W₁.FunctionField
      (algebraMap φ.intermediateRing W₁.FunctionField b) ≤ 1 := by
  -- the valuation of a point is that of a place, so it is trivial on the constants
  have : ((CoordinateRing.pointPlace h).valuation W₁.FunctionField).IsTrivialOn F := by
    rw [← Place.valuation_ofPrime F]
    infer_instance
  set w := (CoordinateRing.pointPlace h).valuation W₁.FunctionField
  -- the restriction of `w` to `W₂` has no pole at `x₂`, so none on the coordinate ring of `W₂`
  have hpull (r : W₂.CoordinateRing) : w (φ.pullback r) ≤ 1 := by
    have hr := (w.comap φ.fieldPullback.toRingHom).algebraMap_coordinateRing_le_one
      (by rwa [Valuation.comap_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        IsScalarTower.algebraMap_apply F[X] W₂.CoordinateRing W₂.FunctionField,
        fieldPullback_algebraMap]) r
    rwa [Valuation.comap_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      fieldPullback_algebraMap] at hr
  -- `b` is integral over the pulled-back coordinate ring, which lies in the valuation ring of `w`,
  -- and that ring is integrally closed
  let _ : Algebra W₂.CoordinateRing W₁.FunctionField := φ.pullback.toRingHom.toAlgebra
  let _ : Algebra W₂.CoordinateRing w.integer :=
    (φ.pullback.toRingHom.codRestrict _ hpull).toAlgebra
  have : IsScalarTower W₂.CoordinateRing w.integer W₁.FunctionField :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have hint : IsIntegral w.integer (algebraMap φ.intermediateRing W₁.FunctionField b) :=
    ((φ.mem_intermediateRing_iff _).mp b.2).tower_top
  exact (Valuation.Integers.isIntegral_iff_v_le_one (Valuation.integer.integers w)).mp hint

/-- **The ideal of a point extends to the prime of the intermediate ring at that point.** If the
height one prime `𝔓` of the intermediate ring has the valuation of the affine point `(x, y)` of
`W₁` — so the point does not lie over `O₂` — then `⟨X - x, Y - y⟩` extends to `𝔓` exactly, with
no ramification. Every point off the fibre over `O₂` has such a prime, by
`valuation_le_one_of_valuation_pullback_X_le_one` and
`Valuation.existsUnique_heightOneSpectrum_valuation_eq`. -/
theorem map_XYIdeal_eq_asIdeal_of_valuation_eq [IsDedekindDomain φ.intermediateRing] {x y : F}
    (h : W₁.Equation x y) (𝔓 : HeightOneSpectrum φ.intermediateRing)
    (h𝔓 : 𝔓.valuation W₁.FunctionField =
      (CoordinateRing.pointPlace h).valuation W₁.FunctionField) :
    (CoordinateRing.XYIdeal W₁ x (C y)).map φ.toIntermediateRing = 𝔓.asIdeal := by
  let _ := φ.toIntermediateRing.toAlgebra
  have := φ.isScalarTower_toIntermediateRing
  have key := (CoordinateRing.pointPlace h).map_asIdeal_eq_asIdeal_of_valuation_eq 𝔓 h𝔓
  rwa [CoordinateRing.pointPlace_asIdeal, RingHom.algebraMap_toAlgebra] at key

end Isogeny

end TauCeti
