/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Padics.BinomialSeries
public import TauCeti.NumberTheory.Padics.Measure.AmiceOperators

/-!
# Dilation and unit-supported Mahler primitives

Pushforward of a measure by multiplication by a p-adic integer `a` substitutes
`binomialSeries R a - 1` into its Amice transform. The substitution depends continuously on `a`
for the coefficientwise topology, even when `a` is zero or a nonunit.

For a unit `a`, the inverse Mahler operator satisfies
`H(F((1 + X)^a - 1)) = a⁻¹ • (H F)((1 + X)^a - 1)`.
This transports the covariance of division by the coordinate on unit-supported measures to
formal power series. Unit dilation also preserves the kernel of psi; dilation by a nonunit
need not do so, since it can move a unit atom off the units. All primes, including two, are allowed.

## References

J. Rodrigues Jacinto and C. Williams, *An introduction to p-adic L-functions*, §3.5.5 and
Proposition 12.5. We use Mathlib's Amice transform and the existing measure-theoretic
`AbstractMeasure.inverseWeight_map_mulLeft_unit`.
-/

public section

open AbstractMeasure PowerSeries
open scoped AbstractMeasure PowerSeries.WithPiTopology

variable {p : ℕ} [Fact p.Prime]

namespace AbstractMeasure

/-- Dilation by any p-adic integer acts on Amice transforms by binomial substitution.
The coefficient ring is any Hausdorff topological p-adic algebra with continuous scalar action. -/
theorem amiceTransform_map_mulLeft {R : Type*} [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] [T2Space R] [Algebra ℤ_[p] R] [ContinuousSMul ℤ_[p] R]
    (μ : D(ℤ_[p], R)) (a : ℤ_[p]) :
    amiceTransform (map (ContinuousMap.mulLeft a) μ) =
      μ.amiceTransform.subst (binomialSeries R a - 1) := by
  have hmul : Continuous (ContinuousMap.mulLeft : ℤ_[p] → C(ℤ_[p], ℤ_[p])) :=
    ContinuousMap.continuous_of_continuous_uncurry _ continuous_mul
  have hleft : Continuous fun a : ℤ_[p] ↦ amiceTransform (map (ContinuousMap.mulLeft a) μ) := by
    refine continuous_iff_continuousAt.mpr fun a ↦
      (WithPiTopology.tendsto_iff_coeff_tendsto _ _ _ _).mpr fun n ↦ ?_
    simp only [coeff_amiceTransform, map_apply]
    exact ((map_continuous μ).comp (continuous_const.compCM hmul)).continuousAt
  have hright : Continuous fun a : ℤ_[p] ↦
      μ.amiceTransform.subst (binomialSeries R a - 1) :=
    continuous_const.powerSeries_subst_binomialSeries_sub_one continuous_id
  exact congrFun (PadicInt.denseRange_natCast.equalizer hleft hright (funext fun m ↦ by
    simpa only [Function.comp_apply, binomialSeries_nat] using
      amiceTransform_map_mulLeft_natCast m μ)) a

end AbstractMeasure

namespace TauCeti

/-- Inverse Mahler differentiation is covariant under binomial substitution by a unit, with
the inverse unit as scalar factor. -/
theorem inverseMahler_subst_binomialSeries (F : ℤ_[p]⟦X⟧) (a : ℤ_[p]ˣ) :
    inverseMahler p (F.subst (binomialSeries ℤ_[p] (a : ℤ_[p]) - 1)) =
      (↑a⁻¹ : ℤ_[p]) • (inverseMahler p F).subst
        (binomialSeries ℤ_[p] (a : ℤ_[p]) - 1) := by
  obtain ⟨μ, rfl⟩ := amiceTransformEquiv.surjective F
  rw [amiceTransformEquiv_apply]
  calc
    inverseMahler p (μ.amiceTransform.subst (binomialSeries ℤ_[p] (a : ℤ_[p]) - 1)) =
        (inverseWeight (map (ContinuousMap.mulLeft (a : ℤ_[p])) μ)).amiceTransform := by
      rw [← amiceTransform_map_mulLeft, inverseMahler_amiceTransform]
    _ = (↑a⁻¹ : ℤ_[p]) •
        (map (ContinuousMap.mulLeft (a : ℤ_[p])) (inverseWeight μ)).amiceTransform := by
      simp only [inverseWeight_map_mulLeft_unit, Algebra.algebraMap_self_apply, map_smul]
    _ = (↑a⁻¹ : ℤ_[p]) • (inverseMahler p μ.amiceTransform).subst
        (binomialSeries ℤ_[p] (a : ℤ_[p]) - 1) := by
      rw [amiceTransform_map_mulLeft, inverseMahler_amiceTransform]

-- The inverse factor is visible at the unit two, not just at the identity exponent.
example (F : ℤ_[3]⟦X⟧) :
    (2 : ℤ_[3]) • inverseMahler 3 (F.subst ((1 + X) ^ 2 - 1)) =
      (inverseMahler 3 F).subst ((1 + X) ^ 2 - 1) := by
  obtain ⟨u, hu⟩ := PadicInt.isUnit_natCast_of_coprime (p := 3) (n := 2) (by decide)
  have h := inverseMahler_subst_binomialSeries F u
  rw [hu, binomialSeries_nat] at h
  have hu' : (u : ℤ_[3]) = 2 := by simpa using hu
  rw [h, smul_smul, ← hu']
  simp

-- The inverse factor also appears at a negative exponent, including at the prime two.
example (F : ℤ_[2]⟦X⟧) :
    inverseMahler 2 (F.subst (binomialSeries ℤ_[2] (-1 : ℤ_[2]) - 1)) =
      -(inverseMahler 2 F).subst (binomialSeries ℤ_[2] (-1 : ℤ_[2]) - 1) := by
  simpa using inverseMahler_subst_binomialSeries F (-1 : ℤ_[2]ˣ)

-- A nonunit dilation does not preserve unit support.
example : psiMeasure (map (ContinuousMap.mulLeft (2 : ℤ_[2])) (dirac ℤ_[2] 1)) ≠ 0 := by
  have hpsi : psiMeasure (map (ContinuousMap.mulLeft (2 : ℤ_[2])) (dirac ℤ_[2] 1)) =
      dirac ℤ_[2] 1 := by
    simpa only [map_dirac, ContinuousMap.coe_mulLeft, Nat.cast_ofNat] using
      psiMeasure_dirac_mul (p := 2) (R := ℤ_[2]) 1
  rw [hpsi]
  intro h
  have heval := DFunLike.congr_fun (congrArg toCLMEquiv h) 1
  simp at heval

-- Dilation by zero sends every measure to its total mass at zero.
example (μ : D(ℤ_[2], ℤ_[2])) :
    (map (ContinuousMap.mulLeft (0 : ℤ_[2])) μ).amiceTransform =
      C (constantCoeff μ.amiceTransform) := by
  rw [amiceTransform_map_mulLeft]
  simp [subst_zero_eq_C_constantCoeff, C_apply]

end TauCeti
