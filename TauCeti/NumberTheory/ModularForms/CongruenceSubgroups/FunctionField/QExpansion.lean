/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.CongruenceSubgroups.FunctionField.Fricke
import TauCeti.NumberTheory.ModularForms.EisensteinSeries.WeightTwo.QExpansion
import TauCeti.NumberTheory.ModularForms.LevelOne.QExpansion

/-!
# Cyclotomic Fourier coefficients of Fricke functions

The Fricke functions belong to the arithmetic modular function field `F_N`. More generally,
their Laurent expansions at infinity have coefficients in any subfield of `ℂ` containing the
`N`-th roots of unity. The normalized weight-two division values have coefficients in this
field, and the remaining factor `E₄ E₆ / Δ` has rational coefficients.

This supplies arithmetic generators for the complex function field of `X(N)`. The coefficient
condition is proved for every positive level, including level two.

## References

* Goro Shimura, *Introduction to the Arithmetic Theory of Automorphic Functions*, Princeton
  University Press, 1971, §6.1.
-/

public noncomputable section

open Complex CongruenceSubgroup
open UpperHalfPlane hiding I
open Subgroup.CompactifiedQuotient TauCeti.RiemannSurface
open scoped Real MatrixGroups

namespace TauCeti

variable {N : ℕ} [NeZero N]

/-- The Laurent expansion of a Fricke function is the product of the expansions of
`E₄ E₆ / Δ` and the normalized weight-two division value. -/
theorem laurentQExpansion_frickeMeromorphicFunction (a : Fin 2 → ZMod N) :
    laurentQExpansion (cuspDatumInftyGamma N) (frickeMeromorphicFunction a) =
      (qExpansion N ModularForm.E₄ : LaurentSeries ℂ) * qExpansion N ModularForm.E₆ /
        qExpansion N _root_.ModularForm.discriminant *
          (((2 * π * I : ℂ) ^ 2)⁻¹ •
            (qExpansion N (EisensteinSeries.weightedG2MF (Pi.single a (1 : ℂ))) :
              LaurentSeries ℂ)) := by
  have hpullback : laurentQExpansion (cuspDatumInftyGamma N) (frickeMeromorphicFunction a) =
      UpperHalfPlane.laurentQExpansion N (frickeFunction a) := by
    rw [laurentQExpansion_apply, cuspDatumInftyGamma_width]
    congr 1
    funext z
    simp
  rw [hpullback]
  have hN : (0 : ℝ) < N := Nat.cast_pos.mpr (NeZero.pos N)
  have hperiod : (N : ℝ) ∈ (Gamma N : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
    simp [strictPeriods_Gamma]
  have hperiodSL : (N : ℝ) ∈ (𝒮ℒ).strictPeriods := by
    rw [Subgroup.strictPeriods_SL2Z]
    exact ⟨N, by simp⟩
  have h₄ := ModularFormClass.analyticAt_cuspFunction_zero ModularForm.E₄ hN hperiodSL
  have h₆ := ModularFormClass.analyticAt_cuspFunction_zero ModularForm.E₆ hN hperiodSL
  have hΔ : AnalyticAt ℂ (cuspFunction N _root_.ModularForm.discriminant) 0 := by
    simpa only [CuspForm.coe_discriminant] using
      ModularFormClass.analyticAt_cuspFunction_zero CuspForm.discriminant hN hperiodSL
  have hG := ModularFormClass.analyticAt_cuspFunction_zero
    (EisensteinSeries.weightedG2MF (Pi.single a (1 : ℂ))) hN hperiod
  have hGscaled : AnalyticAt ℂ (cuspFunction N
      (((2 * π * I : ℂ) ^ 2)⁻¹ • EisensteinSeries.weightedG2MF (Pi.single a (1 : ℂ)))) 0 := by
    rw [_root_.UpperHalfPlane.cuspFunction_smul hG.continuousAt]
    exact hG.const_smul
  have hfun : frickeFunction a =
      ((ModularForm.E₄ : ℍ → ℂ) * ModularForm.E₆ / _root_.ModularForm.discriminant) *
        (((2 * π * I : ℂ) ^ 2)⁻¹ • EisensteinSeries.weightedG2MF (Pi.single a (1 : ℂ))) := by
    funext z
    simp only [frickeFunction_def, Pi.mul_apply, Pi.smul_apply,
      smul_eq_mul, EisensteinSeries.coe_weightedG2MF, div_eq_mul_inv, Pi.inv_apply]
    ring
  rw [hfun, UpperHalfPlane.laurentQExpansion_mul
    (UpperHalfPlane.meromorphicAt_cuspFunction_div
      (UpperHalfPlane.meromorphicAt_cuspFunction_mul h₄.meromorphicAt h₆.meromorphicAt)
      hΔ.meromorphicAt)
    hGscaled.meromorphicAt,
    UpperHalfPlane.laurentQExpansion_div
      (UpperHalfPlane.meromorphicAt_cuspFunction_mul h₄.meromorphicAt h₆.meromorphicAt)
      hΔ.meromorphicAt,
    UpperHalfPlane.laurentQExpansion_mul h₄.meromorphicAt h₆.meromorphicAt,
    UpperHalfPlane.laurentQExpansion_smul hG.meromorphicAt,
    UpperHalfPlane.laurentQExpansion_of_analyticAt h₄,
    UpperHalfPlane.laurentQExpansion_of_analyticAt h₆,
    UpperHalfPlane.laurentQExpansion_of_analyticAt hΔ,
    UpperHalfPlane.laurentQExpansion_of_analyticAt hG]

/-- Every Laurent coefficient of a Fricke function at infinity lies in any subfield
containing the `N`-th roots of unity. -/
theorem laurentQExpansion_frickeMeromorphicFunction_coeff_mem {K : Subfield ℂ}
    (hK : ∀ ζ : ℂ, ζ ^ N = 1 → ζ ∈ K) (a : Fin 2 → ZMod N) (n : ℤ) :
    (laurentQExpansion (cuspDatumInftyGamma N) (frickeMeromorphicFunction a)).coeff n ∈ K := by
  classical
  let L : Subfield (LaurentSeries ℂ) := (HahnSeries.mapRingHom K.subtype).fieldRange
  have hL (F : LaurentSeries ℂ) : F ∈ L ↔ ∀ j, F.coeff j ∈ K := by
    simp only [L, RingHom.mem_fieldRange, ← RingHom.mem_rangeS, HahnSeries.mem_map_rangeS]
    simp
  have hGcoeff (j : ℕ) :
      (qExpansion N (EisensteinSeries.weightedG2MF (Pi.single a (1 : ℂ)))).coeff j /
        (2 * π * I) ^ 2 ∈ K :=
    EisensteinSeries.qExpansion_weightedG2MF_coeff_div_mem hK
      (fun b ↦ by simp only [Pi.single_apply]; split_ifs <;> simp) j
  have hEL {k : ℕ} (hk : 3 ≤ k) :
      (qExpansion N (ModularForm.E hk) : LaurentSeries ℂ) ∈ L := by
    refine (hL _).mpr fun j ↦ ?_
    rw [PowerSeries.coeff_coe]
    split_ifs
    · exact K.zero_mem
    · exact ModularForm.qExpansion_natCast_E_coeff_mem (N := N) hk _
  have hΔL : (qExpansion N _root_.ModularForm.discriminant : LaurentSeries ℂ) ∈ L := by
    refine (hL _).mpr fun j ↦ ?_
    rw [PowerSeries.coeff_coe]
    split_ifs
    · exact K.zero_mem
    · exact ModularForm.qExpansion_natCast_discriminant_coeff_mem
        (N := N) (R := K.toSubring) _
  have hGL : ((2 * π * I : ℂ) ^ 2)⁻¹ •
      (qExpansion N (EisensteinSeries.weightedG2MF (Pi.single a (1 : ℂ))) :
        LaurentSeries ℂ) ∈ L := by
    refine (hL _).mpr fun j ↦ ?_
    rw [HahnSeries.coeff_smul, PowerSeries.coeff_coe]
    split_ifs
    · simp
    · simpa only [smul_eq_mul, div_eq_mul_inv, mul_comm] using hGcoeff j.natAbs
  rw [laurentQExpansion_frickeMeromorphicFunction]
  exact (hL _).mp (L.mul_mem (L.div_mem
    (L.mul_mem (hEL (by norm_num : 3 ≤ 4)) (hEL (by norm_num : 3 ≤ 6))) hΔL) hGL) n

/-- The Fricke functions are elements of the arithmetic modular function field `F_N`. -/
theorem frickeMeromorphicFunction_mem_modularFunctionField (a : Fin 2 → ZMod N) :
    frickeMeromorphicFunction a ∈ modularFunctionField N :=
  mem_modularFunctionField.mpr fun n ↦
    laurentQExpansion_frickeMeromorphicFunction_coeff_mem
      (fun _ hζ ↦ Subfield.subset_closure hζ) a n

end TauCeti
