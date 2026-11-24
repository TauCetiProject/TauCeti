/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.CongruenceSubgroups.FunctionField.QExpansion
public import TauCeti.NumberTheory.ModularForms.EisensteinSeries.WeightTwo.Galois
import TauCeti.NumberTheory.ModularForms.LevelOne.QExpansion

/-!
# Cyclotomic conjugation of Fricke expansions

The coefficient map `ζ_N ↦ ζ_N^d` sends the Laurent expansion at infinity of the Fricke
function indexed by `(a,b)` to that indexed by `(a,db)`. Thus it gives the diagonal
matrix `diag(1,d)` on the arithmetic generators of the modular function field.
The coefficient map need not be continuous: all uses of it are algebraic operations
on formal series, with the constant coefficient of the division value evaluated by
a finite Bernoulli sum.

## References

* Goro Shimura, *Introduction to the Arithmetic Theory of Automorphic Functions*, §6.1.
-/

public noncomputable section

open Complex CongruenceSubgroup ZMod
open UpperHalfPlane hiding I
open Subgroup.CompactifiedQuotient
open scoped Real Matrix

namespace TauCeti

variable {N : ℕ} [NeZero N]

/-- Applying `ζ_N ↦ ζ_N^d` coefficientwise to a Fricke expansion gives the expansion
with its second residue coordinate multiplied by `d`. Here `ζ_N = stdAddChar 1`,
and the coefficient map is an arbitrary complex field embedding with that value. -/
theorem map_laurentQExpansion_frickeMeromorphicFunction {σ : ℂ →+* ℂ} {d : (ZMod N)ˣ}
    (hσ : σ (stdAddChar (1 : ZMod N)) = stdAddChar (d : ZMod N))
    (a : Fin 2 → ZMod N) :
    HahnSeries.mapRingHom σ
      (laurentQExpansion (cuspDatumInftyGamma N) (frickeMeromorphicFunction a)) =
      laurentQExpansion (cuspDatumInftyGamma N)
        (frickeMeromorphicFunction ![a 0, (d : ZMod N) * a 1]) := by
  have hchar (j : ZMod N) : σ (stdAddChar j) = stdAddChar ((d : ZMod N) * j) := by
    have hj : stdAddChar j = stdAddChar (1 : ZMod N) ^ j.val := by
      rw [← AddChar.map_nsmul_eq_pow]
      simp [nsmul_eq_mul]
    rw [hj, map_pow, hσ, ← AddChar.map_nsmul_eq_pow]
    simp [nsmul_eq_mul, mul_comm]
  have hE {k : ℕ} (hk : 3 ≤ k) :
      HahnSeries.mapRingHom σ (qExpansion N (ModularForm.E hk) : LaurentSeries ℂ) =
        (qExpansion N (ModularForm.E hk) : LaurentSeries ℂ) := by
    ext j
    rw [HahnSeries.coeff_mapRingHom, PowerSeries.coeff_coe]
    split_ifs
    · simp
    · exact ModularForm.qExpansion_natCast_E_coeff_mem
        (N := N) (K := σ.eqLocusField (RingHom.id ℂ)) hk _
  have hΔ : HahnSeries.mapRingHom σ
      (qExpansion N _root_.ModularForm.discriminant : LaurentSeries ℂ) =
        (qExpansion N _root_.ModularForm.discriminant : LaurentSeries ℂ) := by
    ext j
    rw [HahnSeries.coeff_mapRingHom, PowerSeries.coeff_coe]
    split_ifs
    · simp
    · exact ModularForm.qExpansion_natCast_discriminant_coeff_mem
        (N := N) (R := σ.eqLocus (RingHom.id ℂ)) _
  have hG : HahnSeries.mapRingHom σ
      (((2 * π * I : ℂ) ^ 2)⁻¹ •
        (qExpansion N (EisensteinSeries.weightedG2MF (Pi.single a (1 : ℂ))) :
          LaurentSeries ℂ)) =
      ((2 * π * I : ℂ) ^ 2)⁻¹ •
        (qExpansion N (EisensteinSeries.weightedG2MF
          (Pi.single ![a 0, (d : ZMod N) * a 1] (1 : ℂ))) : LaurentSeries ℂ) := by
    ext j
    simp only [HahnSeries.coeff_mapRingHom, HahnSeries.coeff_smul, PowerSeries.coeff_coe]
    split_ifs
    · simp
    · simpa only [smul_eq_mul, div_eq_mul_inv, mul_comm] using
        EisensteinSeries.map_qExpansion_single_weightedG2MF_coeff_div hchar a j.natAbs
  rw [laurentQExpansion_frickeMeromorphicFunction,
    laurentQExpansion_frickeMeromorphicFunction, map_mul, map_div₀, map_mul,
    hE, hE, hΔ, hG]

end TauCeti
