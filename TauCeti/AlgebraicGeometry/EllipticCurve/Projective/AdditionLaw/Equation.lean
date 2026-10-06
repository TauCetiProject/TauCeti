/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Projective.AdditionLaw.Basic
import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Point
import TauCeti.AlgebraicGeometry.EllipticCurve.Projective.Nonsingular
import TauCeti.AlgebraicGeometry.EllipticCurve.Projective.Prime
import TauCeti.AlgebraicGeometry.EllipticCurve.Universal

/-!
# The Bosma–Lenstra addition laws land on the curve over any ring

Let `W'` be a Weierstrass curve in projective coordinates over a commutative ring `R`, and let `P`
and `Q` be solutions of its homogeneous equation. This file shows that the two Bosma–Lenstra
addition laws attached to the lines `Z = 0` and `Y = 0`, namely Mathlib's
`WeierstrassCurve.Projective.addXYZ` and Tau Ceti's `WeierstrassCurve.Projective.dblAddXYZ`, take
`P` and `Q` to solutions of the equation again. The curve `W'` is arbitrary, possibly singular, and
`P` and `Q` are arbitrary solutions, not necessarily nonsingular and not necessarily with
coordinates generating the unit ideal.

## Main results

* `WeierstrassCurve.Projective.Equation.addXYZ`: if `P` and `Q` satisfy the equation of `W'`, so
  does `W'.addXYZ P Q`.
* `WeierstrassCurve.Projective.Equation.dblAddXYZ`: if `P` and `Q` satisfy the equation of `W'`,
  so does `W'.dblAddXYZ P Q`.

## References

* W. Bosma and H. W. Lenstra, Jr., *Complete systems of two addition laws for elliptic curves*,
  J. Number Theory 53 (1995), 229–240.

## Provenance

New in Tau Ceti; no code was ported. AINTLIB (`github.com/CBirkbeck/AINTLIB`, Apache-2.0, commit
`c3415f32a313e19ace43e05479aeaa0d56ca287a`, file
`projects/ModularCurves/ModularCurves/EllipticCurve/AdditionLawOnCurve.lean`) has the two
statements as `equation_addXYZ_of_isJacobsonRing` and `equation_dblAddXYZ_of_isJacobsonRing`, for
curves with unit discriminant over reduced Jacobson rings.
-/

public section

noncomputable section

namespace WeierstrassCurve.Projective

open MvPolynomial

variable {R S : Type*} [CommRing R] [CommRing S]

-- Over a field, `addXYZ` takes two nonsingular point representatives to a solution: it is
-- `add` unless they are equivalent, in which case it vanishes.
private theorem equation_addXYZ_of_nonsingular {F : Type*} [Field F] {W : Projective F}
    {P Q : Fin 3 → F} (hP : W.Nonsingular P) (hQ : W.Nonsingular Q) :
    W.Equation (W.addXYZ P Q) := by
  by_cases hPQ : P ≈ Q
  · obtain ⟨u, rfl⟩ := hPQ
    have h : W.addXYZ (u • Q) Q = ![0, 0, 0] := by
      simpa [Units.smul_def, addXYZ_self] using W.addXYZ_smul Q Q u 1
    simp [h, equation_iff]
  · exact (add_of_not_equiv hPQ ▸ nonsingular_add hP hQ).left

/-! ### The universal pair of solutions -/

-- Both statements are proved once for a universal pair of solutions and then specialized. Over
-- `ℤ[A₁, A₂, A₃, A₄, A₆]` the homogeneous coordinate ring `Ring₁` of the universal curve is a
-- domain, and so is the homogeneous coordinate ring `Ring₂` of the universal curve over `Ring₁`
-- (`instIsDomainCoordinateRing`). Over the fraction field of `Ring₂` the universal curve has
-- nonzero discriminant and the two universal solutions are nonzero, hence nonsingular, so the
-- field statements apply there and descend to `Ring₂` by injectivity.

-- The universal Weierstrass curve over `ℤ[A₁, A₂, A₃, A₄, A₆]`, in projective coordinates.
private abbrev curve₀ : Projective (MvPolynomial Coeff ℤ) := Universal.curve.toProjective

-- The universal ring of one solution of the equation, and the universal curve over it.
private abbrev Ring₁ : Type := curve₀.CoordinateRing

private abbrev curve₁ : Projective Ring₁ := curve₀.map (algebraMap _ Ring₁)

-- The universal ring of two solutions of the equation, the universal curve over it, and the two
-- universal solutions.
private abbrev Ring₂ : Type := curve₁.CoordinateRing

private abbrev curve₂ : Projective Ring₂ := curve₁.map (algebraMap _ Ring₂)

private abbrev point₁ : Fin 3 → Ring₂ := algebraMap Ring₁ Ring₂ ∘ curve₀.coord

private abbrev point₂ : Fin 3 → Ring₂ := curve₁.coord

-- Over the fraction field of `Ring₂`, the universal curve has nonzero discriminant, so a nonzero
-- solution over `Ring₂` becomes nonsingular.
private theorem nonsingular_fractionRing_of_ne_zero {P : Fin 3 → Ring₂} (hP : curve₂.Equation P)
    (hP₀ : P ≠ 0) : (curve₂.map (algebraMap Ring₂ (FractionRing Ring₂))).Nonsingular
      (algebraMap Ring₂ (FractionRing Ring₂) ∘ P) := by
  refine (equation_iff_nonsingular_of_Δ_ne_zero_of_ne_zero ?_
    ((Function.comp_ne_zero_iff _ (IsFractionRing.injective _ _) (map_zero _)).mpr hP₀)).mp
    (hP.map _)
  simpa [map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective _ _)] using Universal.curve_Δ_ne_zero

-- Over the fraction field of `Ring₂`, both universal solutions are nonsingular.
private theorem nonsingular_point₁_point₂ :
    (curve₂.map (algebraMap Ring₂ (FractionRing Ring₂))).Nonsingular
        (algebraMap Ring₂ (FractionRing Ring₂) ∘ point₁) ∧
      (curve₂.map (algebraMap Ring₂ (FractionRing Ring₂))).Nonsingular
        (algebraMap Ring₂ (FractionRing Ring₂) ∘ point₂) :=
  ⟨nonsingular_fractionRing_of_ne_zero ((equation_coord curve₀).map _)
      ((Function.comp_ne_zero_iff _ (FaithfulSMul.algebraMap_injective _ _) (map_zero _)).mpr
        (coord_ne_zero _)),
    nonsingular_fractionRing_of_ne_zero (equation_coord curve₁) (coord_ne_zero _)⟩

-- Any two solutions over any ring are the image of the universal pair.
private theorem exists_specialization {W' : Projective R} {P Q : Fin 3 → R} (hP : W'.Equation P)
    (hQ : W'.Equation Q) :
    ∃ f : Ring₂ →+* R, curve₂.map f = W' ∧ f ∘ point₁ = P ∧ f ∘ point₂ = Q := by
  -- `W'` is a specialization of the universal curve
  obtain ⟨g, rfl⟩ : ∃ g, curve₀.map g = W' := ⟨_, map_specialize W'⟩
  refine ⟨curve₁.evalHom (curve₀.evalHom g hP) (by rwa [map_evalHom]),
    by rw [map_evalHom, map_evalHom], ?_, evalHom_comp_coord ..⟩
  rw [← Function.comp_assoc, ← RingHom.coe_comp, evalHom_comp_algebraMap, evalHom_comp_coord]

/-! ### The addition laws on the curve -/

variable {W' : Projective R} {P Q : Fin 3 → R}

/-- Mathlib's addition law `addXYZ`, attached to the line `Z = 0`, takes two solutions of the
projective Weierstrass equation to a solution of the equation. This holds for every Weierstrass
curve over every commutative ring, singular or not, and for all solutions `P` and `Q`. -/
theorem Equation.addXYZ (hP : W'.Equation P) (hQ : W'.Equation Q) :
    W'.Equation (W'.addXYZ P Q) := by
  obtain ⟨f, rfl, rfl, rfl⟩ := exists_specialization hP hQ
  have h := equation_addXYZ_of_nonsingular nonsingular_point₁_point₂.1 nonsingular_point₁_point₂.2
  rw [map_addXYZ, map_equation _ (IsFractionRing.injective _ _)] at h
  simpa using h.map f

/-- The addition law `dblAddXYZ`, attached to the line `Y = 0`, takes two solutions of the
projective Weierstrass equation to a solution of the equation. This holds for every Weierstrass
curve over every commutative ring, singular or not, and for all solutions `P` and `Q`. -/
theorem Equation.dblAddXYZ (hP : W'.Equation P) (hQ : W'.Equation Q) :
    W'.Equation (W'.dblAddXYZ P Q) := by
  obtain ⟨f, rfl, rfl, rfl⟩ := exists_specialization hP hQ
  have h :=
    equation_dblAddXYZ_of_nonsingular nonsingular_point₁_point₂.1 nonsingular_point₁_point₂.2
  rw [map_dblAddXYZ, map_equation _ (IsFractionRing.injective _ _)] at h
  simpa using h.map f

end WeierstrassCurve.Projective
