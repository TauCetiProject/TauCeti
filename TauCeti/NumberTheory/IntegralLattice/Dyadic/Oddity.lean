/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.Characteristic.Basic
public import TauCeti.LinearAlgebra.IntegralLattice.Discriminant.Bilinear
public import TauCeti.LinearAlgebra.IntegralLattice.Signature
import TauCeti.LinearAlgebra.FiniteBilinearModule.Comparison
import TauCeti.LinearAlgebra.FiniteBilinearModule.Primary.Component
import TauCeti.LinearAlgebra.FiniteBilinearModule.Primary.GaussSum
import TauCeti.LinearAlgebra.IntegralLattice.Characteristic.VanDerBlij
import TauCeti.LinearAlgebra.IntegralLattice.Discriminant.Cardinality
import TauCeti.LinearAlgebra.IntegralLattice.Discriminant.Quadratic
import TauCeti.NumberTheory.IntegralLattice.Localization.Discriminant.Form
import TauCeti.NumberTheory.IntegralLattice.Localization.Sublattice

/-!
# Oddity invariance for lattices of odd discriminant

For a nondegenerate integral lattice `L` of odd discriminant, any characteristic vector `w` has
`L.integralNorm w mod 8` determined by `L.sigPos - L.sigNeg mod 8` and `b_L`: passing to
`L.evenSublattice` preserves odd-prime localizations (`[L : N] ≤ 2`), and Milgram's theorem equates
`sigPos L - sigNeg L mod 8` with `(w² mod 8)` plus the odd-prime Gauss-sum invariants from `b_L`.

## Main results

* `TauCeti.IntegralLattice.integralNorm_modEq_eight_of_odd_discriminant`: for nondegenerate
  lattices of odd discriminant with congruent signature differences mod 8 and isometric discriminant
  bilinear modules, characteristic vectors have congruent norms mod 8.

## References

* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, Chapter 15, §7.
* V. V. Nikulin, *Integral symmetric bilinear forms and some of their applications*, §1.16.
-/

public section

open AddCommGroup

namespace TauCeti.IntegralLattice

variable {V W : Type*} [AddCommGroup V] [Module ℚ V] [AddCommGroup W] [Module ℚ W]

private theorem gaussSign_restrict_primaryComponent_evenSublattice_eq_of_odd
    (L : IntegralLattice V) (M : IntegralLattice W) [L.IsNondegenerate] [M.IsNondegenerate]
    {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    (e : FiniteBilinearModule.Isometry
      (L.discriminantBilinearModule.restrict (primaryComponent L.discriminantBilinearModule p))
      (M.discriminantBilinearModule.restrict (primaryComponent M.discriminantBilinearModule p))) :
    ((L.evenSublattice.discriminantQuadraticModule L.isEven_evenSublattice).restrict
      (primaryComponent
        (L.evenSublattice.discriminantQuadraticModule L.isEven_evenSublattice) p)).gaussSign =
    ((M.evenSublattice.discriminantQuadraticModule M.isEven_evenSublattice).restrict
      (primaryComponent
        (M.evenSublattice.discriminantQuadraticModule M.isEven_evenSublattice) p)).gaussSign :=
  FiniteQuadraticModule.gaussSign_eq_of_bilinear_isometry_of_odd
    ((L.evenSublattice.discriminantQuadraticModule
      L.isEven_evenSublattice).odd_natCard_restrict_primaryComponent Fact.out hp)
    ((primaryDiscriminantBilinearIsometry (L.evenSublattice.localInclusionIsometryEquiv L p
        L.evenSublattice_form L.evenSublattice_carrier_le
        (L.not_dvd_relIndex_evenSublattice_of_ne_two Fact.out hp))).trans
      (e.trans (primaryDiscriminantBilinearIsometry (M.evenSublattice.localInclusionIsometryEquiv
        M p M.evenSublattice_form M.evenSublattice_carrier_le
        (M.not_dvd_relIndex_evenSublattice_of_ne_two Fact.out hp))).symm))

/-- **Oddity invariance for odd discriminant.** If two nondegenerate integral lattices `L` and `M`
with `L.discriminant` odd have signature differences `sigPos - sigNeg` congruent modulo eight and
isometric discriminant bilinear modules, then any characteristic vectors `w` of `L` and `w'` of `M`
have equal integral norms modulo eight. -/
theorem integralNorm_modEq_eight_of_odd_discriminant
    {L : IntegralLattice V} {M : IntegralLattice W} [L.IsNondegenerate] [M.IsNondegenerate]
    (hL : Odd L.discriminant)
    (hsig : ((L.sigPos : ℤ) - L.sigNeg) ≡ ((M.sigPos : ℤ) - M.sigNeg) [ZMOD 8])
    (e : FiniteBilinearModule.Isometry L.discriminantBilinearModule M.discriminantBilinearModule)
    {w : L} {w' : M} (hw : L.IsCharacteristicVector w) (hw' : M.IsCharacteristicVector w') :
    L.integralNorm w ≡ M.integralNorm w' [ZMOD 8] := by
  classical
  have hdisc_eq := discriminant_eq_of_isometry_discriminantBilinearModule e
  let P : Finset ℕ := L.discriminant.primeFactors
  have h2P : 2 ∉ P := fun hmem ↦ hL.not_two_dvd_nat (Nat.dvd_of_mem_primeFactors hmem)
  have hP_prime p (hp : p ∈ insert 2 P) : p.Prime :=
    (Finset.mem_insert.mp hp).elim (· ▸ Nat.prime_two) Nat.prime_of_mem_primeFactors
  let AL := L.evenSublattice.discriminantQuadraticModule L.isEven_evenSublattice
  let AM := M.evenSublattice.discriminantQuadraticModule M.isEven_evenSublattice
  have hsumL := FiniteQuadraticModule.gaussSign_eq_sum_of_primeFactors_subset
    (L.evenSublattice.isNondegenerate_discriminantQuadraticModule L.isEven_evenSublattice)
    hP_prime (by
      rw [L.evenSublattice.natCard_discriminantQuadraticModule L.isEven_evenSublattice,
        L.evenSublattice.natCard_discriminantGroup]
      exact L.primeFactors_discriminant_evenSublattice_subset)
  have hsumM := FiniteQuadraticModule.gaussSign_eq_sum_of_primeFactors_subset
    (M.evenSublattice.isNondegenerate_discriminantQuadraticModule M.isEven_evenSublattice)
    hP_prime (by
      rw [M.evenSublattice.natCard_discriminantQuadraticModule M.isEven_evenSublattice,
        M.evenSublattice.natCard_discriminantGroup]
      simpa only [P, hdisc_eq] using M.primeFactors_discriminant_evenSublattice_subset)
  rw [Finset.sum_insert h2P,
    L.gaussSign_restrict_primaryComponent_two_evenSublattice hL hw] at hsumL
  rw [Finset.sum_insert h2P,
    M.gaussSign_restrict_primaryComponent_two_evenSublattice (hdisc_eq ▸ hL) hw'] at hsumM
  have hAL_eq_AM : AL.gaussSign = AM.gaussSign := by
    rw [L.gaussSign_evenSublattice_eq_sigPos_sub_sigNeg,
      M.gaussSign_evenSublattice_eq_sigPos_sub_sigNeg]
    simpa only [Int.cast_sub, Int.cast_natCast] using (ZMod.intCast_eq_intCast_iff _ _ 8).mpr hsig
  have hodd_sum : ∑ p ∈ P, (AL.restrict (primaryComponent AL p)).gaussSign =
      ∑ p ∈ P, (AM.restrict (primaryComponent AM p)).gaussSign :=
    Finset.sum_congr rfl fun p hp ↦
      let _ : Fact p.Prime := ⟨Nat.prime_of_mem_primeFactors hp⟩
      gaussSign_restrict_primaryComponent_evenSublattice_eq_of_odd L M
        (fun h2 ↦ h2P (h2 ▸ hp)) (e.restrictPrimaryComponent p)
  have h := (hsumL.symm.trans hAL_eq_AM).trans (hodd_sum ▸ hsumM)
  exact (ZMod.intCast_eq_intCast_iff _ _ 8).mp (add_right_cancel h)

end TauCeti.IntegralLattice
