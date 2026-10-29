/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Padics.Measure.PhiPsi
public import TauCeti.NumberTheory.Padics.Measure.InverseWeight
public import TauCeti.NumberTheory.Padics.Measure.Moments

/-!
# Psi and unit-supported Mahler primitives

Transporting the operators on integral measures through Mathlib's `amiceTransformEquiv` gives
the linear operator `psiSeries` and the inverse Mahler operator `inverseMahler` on `ℤ_p⟦X⟧`.
The former is a left inverse of substitution by `(1 + X) ^ p - 1`; its kernel consists of the
Amice transforms of unit-supported measures. The latter divides those measures by the coordinate.

For the Mahler derivation `∂ = (1 + X) d/dX` and `H = inverseMahler p`, both `∂ H` and `H ∂`
are the unit projector
`F ↦ F - (psiSeries p F).subst ((1 + X) ^ p - 1)`. Consequently every series killed by psi has a
unique primitive killed by psi. This support condition is essential: `∂` kills constants, whereas
psi fixes them. All primes, including two, are allowed. No topology on measures is installed.

## References

* J. Rodrigues Jacinto and C. Williams, *An introduction to p-adic L-functions*, §3.5.5,
  equation (4-3), and Proposition 12.5, equation (12-3).
* P. Colmez, *Fonctions d'une variable p-adique*, §II.2.

The constructions use Mathlib's Amice equivalence and `LinearEquiv.conj`, and the measure
operators `AbstractMeasure.psiMeasure` and `AbstractMeasure.inverseWeight`.
-/

public noncomputable section

open AbstractMeasure PowerSeries
open scoped AbstractMeasure

namespace TauCeti

variable {p : ℕ} [Fact p.Prime]

variable (p)

/-- Psi on integral power series, obtained from restriction to `pℤ_p` followed by pushforward
along `x ↦ x / p` through the integral Amice equivalence. It is a linear map. -/
def psiSeries : ℤ_[p]⟦X⟧ →ₗ[ℤ_[p]] ℤ_[p]⟦X⟧ :=
  amiceTransformEquiv.conj psiMeasure

variable {p}

/-- Series psi is the transport of measure psi through the integral Amice equivalence. -/
theorem psiSeries_eq_transport :
    psiSeries p = amiceTransformEquiv.toLinearMap ∘ₗ psiMeasure ∘ₗ
      amiceTransformEquiv.symm.toLinearMap := (rfl)

/-- The measure-theoretic description of series psi. -/
theorem psiSeries_apply (F : ℤ_[p]⟦X⟧) :
    psiSeries p F = amiceTransform (psiMeasure (amiceTransformEquiv.symm F)) := by
  simp only [psiSeries, LinearEquiv.conj_apply_apply, amiceTransformEquiv_apply]

/-- The Amice transform intertwines measure psi and series psi. -/
@[simp↓]
theorem psiSeries_amiceTransform (μ : D(ℤ_[p], ℤ_[p])) :
    psiSeries p μ.amiceTransform = (psiMeasure μ).amiceTransform := by
  simp only [psiSeries, LinearEquiv.conj_apply_apply, ← amiceTransformEquiv_apply,
    LinearEquiv.symm_apply_apply]

/-- Series psi is a left inverse of Frobenius substitution. -/
@[simp]
theorem psiSeries_phi (F : ℤ_[p]⟦X⟧) :
    psiSeries p (F.subst ((1 + X) ^ p - 1)) = F := by
  obtain ⟨μ, rfl⟩ := amiceTransformEquiv.surjective F
  rw [amiceTransformEquiv_apply, ← amiceTransform_phiMeasure,
    psiSeries_amiceTransform, psiMeasure_phiMeasure]

/-- Frobenius after psi is the Amice transform of restriction to `pℤ_p`. -/
theorem subst_psiSeries_amiceTransform (μ : D(ℤ_[p], ℤ_[p])) :
    (psiSeries p μ.amiceTransform).subst ((1 + X) ^ p - 1) =
      (restrictMultiples μ).amiceTransform := by
  rw [psiSeries_amiceTransform, ← amiceTransform_phiMeasure, phiMeasure_psiMeasure]

/-- Series psi kills the Amice transform of `μ` iff `μ` is supported on `ℤ_pˣ`,
i.e. its restriction to `pℤ_p` vanishes. -/
theorem psiSeries_amiceTransform_eq_zero_iff (μ : D(ℤ_[p], ℤ_[p])) :
    psiSeries p μ.amiceTransform = 0 ↔ restrictMultiples μ = 0 := by
  rw [psiSeries_amiceTransform, map_eq_zero_iff _ injective_amiceTransform]
  constructor
  · intro h
    rw [← phiMeasure_psiMeasure, h, map_zero]
  · intro h
    rw [← psiMeasure_phiMeasure (psiMeasure μ), phiMeasure_psiMeasure, h, map_zero]

/-- Psi fixes the constant series one. -/
@[simp]
theorem psiSeries_one : psiSeries p 1 = 1 := by
  have h0 : psiMeasure (dirac ℤ_[p] (0 : ℤ_[p])) = dirac ℤ_[p] 0 := by
    simpa using psiMeasure_dirac_mul (R := ℤ_[p]) (p := p) 0
  simpa only [h0, amiceTransform_dirac, binomialSeries_zero] using
    psiSeries_amiceTransform (dirac ℤ_[p] (0 : ℤ_[p]))

/-- Psi kills `1 + X`, the transform of the Dirac mass at the unit one. -/
@[simp]
theorem psiSeries_one_add_X : psiSeries p (1 + X) = 0 := by
  have hunit : ¬ (p : ℤ_[p]) ∣ 1 := fun h ↦ PadicInt.p_nonunit (isUnit_of_dvd_one h)
  have h := psiSeries_amiceTransform (dirac ℤ_[p] ((1 : ℕ) : ℤ_[p]))
  rw [amiceTransform_dirac_natCast] at h
  simpa only [Nat.cast_one, pow_one, psiMeasure_dirac_of_not_dvd hunit, map_zero] using h

variable (p)

/-- The inverse Mahler operator: divide an integral measure by the coordinate on the units,
extend by zero on nonunits, and take its Amice transform. -/
def inverseMahler : ℤ_[p]⟦X⟧ →ₗ[ℤ_[p]] ℤ_[p]⟦X⟧ :=
  amiceTransformEquiv.conj inverseWeight

variable {p}

/-- The inverse Mahler operator is the transport of division by the coordinate. -/
theorem inverseMahler_eq_transport :
    inverseMahler p = amiceTransformEquiv.toLinearMap ∘ₗ inverseWeight ∘ₗ
      amiceTransformEquiv.symm.toLinearMap := (rfl)

/-- The measure-theoretic description of the inverse Mahler operator. -/
theorem inverseMahler_apply (F : ℤ_[p]⟦X⟧) :
    inverseMahler p F = amiceTransform (inverseWeight (amiceTransformEquiv.symm F)) := by
  simp only [inverseMahler, LinearEquiv.conj_apply_apply, amiceTransformEquiv_apply]

/-- The inverse Mahler operator is the Amice transform of division by the coordinate. -/
@[simp↓]
theorem inverseMahler_amiceTransform (μ : D(ℤ_[p], ℤ_[p])) :
    inverseMahler p μ.amiceTransform = (inverseWeight μ).amiceTransform := by
  simp only [inverseMahler, LinearEquiv.conj_apply_apply, ← amiceTransformEquiv_apply,
    LinearEquiv.symm_apply_apply]

/-- The inverse Mahler operator always produces a series killed by psi. -/
@[simp]
theorem psiSeries_inverseMahler (F : ℤ_[p]⟦X⟧) :
    psiSeries p (inverseMahler p F) = 0 := by
  obtain ⟨μ, rfl⟩ := amiceTransformEquiv.surjective F
  rw [amiceTransformEquiv_apply, inverseMahler_amiceTransform,
    psiSeries_amiceTransform_eq_zero_iff]
  exact restrictMultiples_inverseWeight μ

/-- The Mahler derivative of `H F` is the unit projection of `F`. -/
theorem mahlerDerivation_inverseMahler (F : ℤ_[p]⟦X⟧) :
    mahlerDerivation ℤ_[p] (inverseMahler p F) =
      F - (psiSeries p F).subst ((1 + X) ^ p - 1) := by
  obtain ⟨μ, rfl⟩ := amiceTransformEquiv.surjective F
  rw [amiceTransformEquiv_apply, inverseMahler_amiceTransform,
    ← amiceTransform_weight_id_smul_one, weight_id_smul_one_inverseWeight,
    subst_psiSeries_amiceTransform, unitRestriction_eq_sub, LinearMap.sub_apply,
    LinearMap.id_apply, map_sub]

/-- Applying `H` after the Mahler derivative also gives the unit projection. -/
theorem inverseMahler_mahlerDerivation (F : ℤ_[p]⟦X⟧) :
    inverseMahler p (mahlerDerivation ℤ_[p] F) =
      F - (psiSeries p F).subst ((1 + X) ^ p - 1) := by
  obtain ⟨μ, rfl⟩ := amiceTransformEquiv.surjective F
  rw [amiceTransformEquiv_apply, ← amiceTransform_weight_id_smul_one,
    inverseMahler_amiceTransform, inverseWeight_weight_id_smul_one,
    subst_psiSeries_amiceTransform, unitRestriction_eq_sub, LinearMap.sub_apply,
    LinearMap.id_apply, map_sub]

private theorem zero_subst_phi :
    (0 : ℤ_[p]⟦X⟧).subst ((1 + X : ℤ_[p]⟦X⟧) ^ p - 1) = 0 := by
  simpa only [map_zero] using (subst_C (a := (1 + X : ℤ_[p]⟦X⟧) ^ p - 1) (0 : ℤ_[p]))

/-- An integral series killed by psi has a unique Mahler primitive killed by psi,
namely its image under `inverseMahler`. -/
theorem existsUnique_unitSupported_mahlerPrimitive (F : ℤ_[p]⟦X⟧)
    (hF : psiSeries p F = 0) :
    ∃! G : ℤ_[p]⟦X⟧, psiSeries p G = 0 ∧ mahlerDerivation ℤ_[p] G = F := by
  refine ⟨inverseMahler p F, ⟨psiSeries_inverseMahler F, ?_⟩, ?_⟩
  · rw [mahlerDerivation_inverseMahler, hF, zero_subst_phi, sub_zero]
  · rintro G ⟨hG, hGF⟩
    simpa only [hGF, hG, zero_subst_phi, sub_zero] using (inverseMahler_mahlerDerivation G).symm

/-- The inverse Mahler operator kills constants. -/
@[simp]
theorem inverseMahler_one : inverseMahler p 1 = 0 := by
  have h := inverseMahler_amiceTransform (dirac ℤ_[p] (0 : ℤ_[p]))
  simpa only [amiceTransform_dirac, binomialSeries_zero,
    inverseWeight_dirac_of_dvd (dvd_zero (p : ℤ_[p])), map_zero] using h

/-- The inverse Mahler operator fixes `1 + X`. -/
@[simp]
theorem inverseMahler_one_add_X : inverseMahler p (1 + X) = 1 + X := by
  have h := inverseMahler_mahlerDerivation (p := p) (1 + X)
  rw [Derivation.map_add, Derivation.map_one_eq_zero, mahlerDerivation_X, zero_add,
    psiSeries_one_add_X, zero_subst_phi, sub_zero] at h
  exact h

-- Psi divides the exponent by the prime on atoms in pℤ_p; it does not average their mass.
example : psiSeries 3 ((1 + X) ^ 3) = 1 + X := by
  have h := psiSeries_amiceTransform (phiMeasure (dirac ℤ_[3] (1 : ℤ_[3])))
  rw [psiMeasure_phiMeasure, phiMeasure_dirac, mul_one,
    amiceTransform_dirac_natCast, ← Nat.cast_one (R := ℤ_[3]),
    amiceTransform_dirac_natCast, pow_one] at h
  exact h

-- A nonzero unit-supported input has a nonzero primitive. A zero operator fails this check.
example : inverseMahler 3 (1 + X) = 1 + X := by simp

-- Division by the coordinate at the unit two supplies the inverse factor, not the factor two.
example : (2 : ℤ_[3]) • inverseMahler 3 ((1 + X) ^ 2) = (1 + X) ^ 2 := by
  have h := inverseMahler_amiceTransform (dirac ℤ_[3] (2 : ℤ_[3]))
  have hu : IsUnit (2 : ℤ_[3]) :=
    PadicInt.isUnit_natCast_of_coprime (p := 3) (n := 2) (by decide)
  obtain ⟨u, hu⟩ := hu
  rw [← hu, inverseWeight_dirac_unit] at h
  rw [map_smul, hu, ← Nat.cast_ofNat (R := ℤ_[3]), amiceTransform_dirac_natCast] at h
  rw [h, smul_smul, ← hu]
  simp

end TauCeti
