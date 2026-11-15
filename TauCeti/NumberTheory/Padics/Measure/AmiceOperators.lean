/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Padics.Measure.PhiPsi
public import TauCeti.NumberTheory.Padics.Measure.InverseWeight
public import TauCeti.RingTheory.PowerSeries.Substitution

/-!
# Unit-supported Mahler primitives

Transporting division by the coordinate on integral measures through Mathlib's
`amiceTransformEquiv` gives the inverse Mahler operator `inverseMahler` on `ℤ_p⟦X⟧`.
It takes values in the kernel of `psiSeries`, the series psi operator from
`TauCeti.NumberTheory.Padics.Measure.PhiPsi`. This kernel consists of the Amice transforms of
unit-supported measures.

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

/-- The inverse Mahler operator divides a binomial series with unit exponent by that unit. -/
@[simp]
theorem inverseMahler_binomialSeries_unit (u : ℤ_[p]ˣ) :
    inverseMahler p (binomialSeries ℤ_[p] (u : ℤ_[p])) =
      (↑u⁻¹ : ℤ_[p]) • binomialSeries ℤ_[p] (u : ℤ_[p]) := by
  rw [← amiceTransform_dirac, inverseMahler_amiceTransform, inverseWeight_dirac_unit,
    map_smul, Algebra.algebraMap_self_apply]

/-- The inverse Mahler operator kills binomial series with exponent in `pℤ_p`. -/
@[simp]
theorem inverseMahler_binomialSeries_of_dvd {x : ℤ_[p]} (hx : (p : ℤ_[p]) ∣ x) :
    inverseMahler p (binomialSeries ℤ_[p] x) = 0 := by
  rw [← amiceTransform_dirac, inverseMahler_amiceTransform, inverseWeight_dirac_of_dvd hx,
    map_zero]

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
    amiceTransform_unitRestriction]

/-- Applying `H` after the Mahler derivative also gives the unit projection. -/
theorem inverseMahler_mahlerDerivation (F : ℤ_[p]⟦X⟧) :
    inverseMahler p (mahlerDerivation ℤ_[p] F) =
      F - (psiSeries p F).subst ((1 + X) ^ p - 1) := by
  obtain ⟨μ, rfl⟩ := amiceTransformEquiv.surjective F
  rw [amiceTransformEquiv_apply, ← amiceTransform_weight_id_smul_one,
    inverseMahler_amiceTransform, inverseWeight_weight_id_smul_one,
    amiceTransform_unitRestriction]

/-- An integral series killed by psi has a unique Mahler primitive killed by psi,
namely its image under `inverseMahler`. -/
theorem existsUnique_unitSupported_mahlerPrimitive (F : ℤ_[p]⟦X⟧)
    (hF : psiSeries p F = 0) :
    ∃! G : ℤ_[p]⟦X⟧, psiSeries p G = 0 ∧ mahlerDerivation ℤ_[p] G = F := by
  refine ⟨inverseMahler p F, ⟨psiSeries_inverseMahler F, ?_⟩, ?_⟩
  · rw [mahlerDerivation_inverseMahler, hF, subst_zero, sub_zero]
  · rintro G ⟨hG, hGF⟩
    simpa only [hGF, hG, subst_zero, sub_zero] using (inverseMahler_mahlerDerivation G).symm

/-- The inverse Mahler operator kills constants. -/
@[simp]
theorem inverseMahler_one : inverseMahler p 1 = 0 := by
  simpa only [binomialSeries_zero] using
    inverseMahler_binomialSeries_of_dvd (p := p) (dvd_zero _)

/-- The inverse Mahler operator fixes `1 + X`. -/
@[simp]
theorem inverseMahler_one_add_X : inverseMahler p (1 + X) = 1 + X := by
  have h := inverseMahler_mahlerDerivation (p := p) (1 + X)
  rw [Derivation.map_add, Derivation.map_one_eq_zero, mahlerDerivation_X, zero_add,
    psiSeries_one_add_X, subst_zero, sub_zero] at h
  exact h

-- A nonzero unit-supported input has a nonzero primitive. A zero operator fails this check.
example : inverseMahler 3 (1 + X) = 1 + X := by simp

-- Division by the coordinate at the unit two supplies the inverse factor, not the factor two.
example : (2 : ℤ_[3]) • inverseMahler 3 ((1 + X) ^ 2) = (1 + X) ^ 2 := by
  have hu : IsUnit (2 : ℤ_[3]) :=
    PadicInt.isUnit_natCast_of_coprime (p := 3) (n := 2) (by decide)
  obtain ⟨u, hu⟩ := hu
  have h := inverseMahler_binomialSeries_unit u
  rw [hu, ← Nat.cast_ofNat (R := ℤ_[3]), binomialSeries_nat] at h
  rw [h, smul_smul, ← hu]
  simp

end TauCeti
