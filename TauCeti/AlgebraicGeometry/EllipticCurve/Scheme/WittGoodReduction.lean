/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.BaseChange
public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Smooth
public import TauCeti.AlgebraicGeometry.GoodReduction.Witt

/-!
# Witt good reduction of elliptic curves with an integral model

Let `E` be a Weierstrass equation with integer coefficients and `p` a prime not dividing its
discriminant. The projective model of `E` over `ℤₚ` is then smooth and proper, and its generic
fibre is the base change to `ℚₚ` of the projective model of `E` over `ℚ`. Hence the projective
model of `E` over `ℚ` has Witt good reduction at `p`
(`WeierstrassCurve.hasWittGoodReductionAt_projModelOver_map`).

For `y² = x³ - x`, whose discriminant is `64`, this gives Witt good reduction at every odd prime,
for instance at `3`. At `2` the curve has no Witt good reduction, but that requires the
Néron–Ogg–Shafarevich criterion and is not shown here.

## References

* J.-M. Fontaine, *Schémas propres et lisses sur Z*, Proceedings of the Indo-French Conference on
  Geometry (Bombay, 1989), Hindustan Book Agency (1993), 43–56; Theorem 1 and Remark (a).
-/

public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TauCeti.AlgebraicGeometry

namespace WeierstrassCurve

/-- **An integral Weierstrass equation with discriminant prime to `p` has Witt good reduction at
`p`.** If `E` has integer coefficients and `p` does not divide its discriminant, then the
projective model of `E` over `ℚ` has Witt good reduction at `p`: the projective model of `E` over
`ℤₚ` is a smooth proper model. -/
theorem hasWittGoodReductionAt_projModelOver_map (E : WeierstrassCurve ℤ) (p : ℕ) [Fact p.Prime]
    (hp : ¬ (p : ℤ) ∣ E.Δ) :
    HasWittGoodReductionAt (E.map (algebraMap ℤ ℚ)).projModelOver p := by
  -- the discriminant of `E` is a unit in `ℤₚ`, so `E` is elliptic over `ℤₚ`
  have : (E.map (algebraMap ℤ ℤ_[p])).IsElliptic := ⟨by
    simp only [map_Δ, algebraMap_int_eq, eq_intCast]
    rw [PadicInt.isUnit_iff]
    exact le_antisymm (PadicInt.norm_le_one _)
      (not_lt.1 ((PadicInt.norm_int_lt_one_iff_dvd _).not.2 hp))⟩
  -- both base changes of `E` to `ℚₚ` are the same curve
  have hE : (E.map (algebraMap ℤ ℚ)).map (algebraMap ℚ ℚ_[p]) =
      (E.map (algebraMap ℤ ℤ_[p])).map (algebraMap ℤ_[p] ℚ_[p]) := by
    simp only [map_map, RingHom.ext_int ((algebraMap ℚ ℚ_[p]).comp (algebraMap ℤ ℚ))
      ((algebraMap ℤ_[p] ℚ_[p]).comp (algebraMap ℤ ℤ_[p]))]
  refine .of_padicInt (E.map (algebraMap ℤ ℤ_[p])).projModelOver
    ((E.map (algebraMap ℤ ℚ)).projModelBaseChange (algebraMap ℚ ℚ_[p]))
    (eqToHom (congrArg projModel hE) ≫
      (E.map (algebraMap ℤ ℤ_[p])).projModelBaseChange (algebraMap ℤ_[p] ℚ_[p]))
    _ (isPullback_projModelBaseChange _ _) ?_
  exact (isPullback_projModelBaseChange _ _).of_iso (eqToIso (congrArg projModel hE).symm)
    (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp)
    (by simpa using (eqToHom_projModelOver hE.symm).symm) (by simp) (by simp)

/-- The curve `y² = x³ - x` has discriminant `64`, so it has Witt good reduction at `3`. -/
example : HasWittGoodReductionAt
    ((⟨0, 0, 0, -1, 0⟩ : WeierstrassCurve ℤ).map (algebraMap ℤ ℚ)).projModelOver 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine hasWittGoodReductionAt_projModelOver_map _ 3 ?_
  simp only [Δ, b₂, b₄, b₆, b₈]
  norm_num

end WeierstrassCurve
