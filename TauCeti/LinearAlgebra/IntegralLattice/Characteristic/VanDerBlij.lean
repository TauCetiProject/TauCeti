/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wentao Li
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.Characteristic.Unimodular
public import TauCeti.LinearAlgebra.IntegralLattice.Characteristic.EvenSublattice
public import TauCeti.LinearAlgebra.IntegralLattice.Milgram
import TauCeti.LinearAlgebra.FiniteBilinearModule.GaussSum.AffineLagrangian
import TauCeti.LinearAlgebra.IntegralLattice.Characteristic.HalfCharacteristic
import TauCeti.LinearAlgebra.IntegralLattice.Overlattice.Metabolic

/-!
# Van der Blij's characteristic-norm congruence

In a unimodular integral lattice, every characteristic vector has integral norm
congruent to the signature difference modulo eight. The statement applies to all signatures
and to both even and odd lattices.

For the canonical even sublattice `N`, the original lattice determines a bilinear Lagrangian
`H = L/N` in the discriminant form of `N`. A characteristic vector `w` gives a dual vector
`w/2`; the quadratic form is constant on its class plus `H`, with value `w²/8`. Character
averaging therefore evaluates the normalized Gauss sum as `expCircle (w²/8)`. Milgram's
theorem identifies the same phase with the signature of `N`, which is the signature of `L`.
When `L` is even and `w = 0`, the congruence gives divisibility of the signature by eight.
Reducing modulo two shows that `w² ≡ rank(L) (mod 2)` and hence that unimodular lattices of odd
rank cannot be even.

## References

* F. van der Blij, *An invariant of quadratic forms mod 8*, Indag. Math. 21 (1959), 291–293.
* J. Milnor and D. Husemoller, *Symmetric Bilinear Forms*, Appendix 4.
-/

public section

open scoped Real

namespace TauCeti.IntegralLattice

universe u
variable {V : Type u} [AddCommGroup V] [Module ℚ V] (L : IntegralLattice V)

private theorem gaussSum_evenSublattice_of_characteristic [L.IsNondegenerate]
    (hL : L.IsUnimodular) {w : L} (hw : L.IsCharacteristicVector w) :
    (L.evenSublattice.discriminantQuadraticModule L.isEven_evenSublattice).gaussSum =
      √(Nat.card L.evenSublattice.DiscriminantGroup) *
        expCircle (ZMod.toRatAddCircle 8 (L.integralNorm w : ZMod 8)) := by
  let A := L.evenSublattice.discriminantQuadraticModule L.isEven_evenSublattice
  have hI := L.isIntegral_toIntermediateCarrier L.evenSublattice_form.symm
    L.evenSublattice_carrier_le
  let H : AddSubgroup A := L.evenSublattice.discriminantSubgroup
    (L.toIntermediateCarrier L.evenSublattice_form.symm L.evenSublattice_carrier_le)
  let a : A := L.halfCharacteristicClass hw
  have hM : hI.toIntegralLattice.IsUnimodular := by
    rw [L.toIntegralLattice_toIntermediateCarrier]
    exact hL
  have hH : A.toFiniteBilinearModule.IsLagrangian H := by
    simpa only [A, H, L.evenSublattice.discriminantQuadraticModule_toFiniteBilinearModule
      L.isEven_evenSublattice] using
      hI.isUnimodular_toIntegralLattice_iff_isLagrangian.mp hM
  have ha (h : H) : A.quadratic (a + h) = A.quadratic a :=
    L.discriminantQuadraticMap_halfCharacteristicClass_add hw h
  have hqa : A.quadratic a = ZMod.toRatAddCircle 8 (L.integralNorm w : ZMod 8) :=
    L.discriminantQuadraticMap_halfCharacteristicClass hw
  have hcard : (Nat.card H) ^ 2 = Nat.card L.evenSublattice.DiscriminantGroup :=
    FiniteBilinearModule.IsLagrangian.card_sq A.toFiniteBilinearModule hH
      (L.evenSublattice.isNondegenerate_discriminantQuadraticModule L.isEven_evenSublattice)
  rw [FiniteQuadraticModule.gaussSum_eq_natCard_mul_expCircle_of_bilinear_isLagrangian a hH ha,
    hqa, ← hcard,
    Nat.cast_pow, Real.sqrt_sq (Nat.cast_nonneg _), Complex.ofReal_natCast]

/-- **Van der Blij's congruence:** the signature difference of a unimodular
integral lattice is congruent modulo eight to the norm of any characteristic vector. -/
theorem vanDerBlij (hL : L.IsUnimodular) {w : L}
    (hw : L.IsCharacteristicVector w) :
    ((L.sigPos : ℤ) - L.sigNeg) ≡ L.integralNorm w [ZMOD 8] := by
  have : L.IsNondegenerate := ⟨hL.nondegenerate⟩
  have := L.finiteDimensional
  have hg := FiniteQuadraticModule.gaussSign_eq_of_gaussSum_eq
    (L.evenSublattice.discriminantQuadraticModule L.isEven_evenSublattice)
    (gaussSum_evenSublattice_of_characteristic L hL hw)
  have hm := L.evenSublattice.gaussSign_discriminantQuadraticModule_eq_sigPos_sub_sigNeg
    L.isEven_evenSublattice
  have hs := L.evenSublattice_signature
  simp only [signature, Prod.mk.injEq] at hs
  rw [hs.1, hs.2.2] at hm
  apply (ZMod.intCast_eq_intCast_iff _ _ 8).mp
  simpa only [Int.cast_sub, Int.cast_natCast] using hm.symm.trans hg

omit L in
/-- **Characteristic-norm parity modulo two:** for any unimodular lattice, `w² ≡ rank(L) (mod 2)`,
derived directly from van der Blij's congruence modulo `8`. -/
theorem IsUnimodular.integralNorm_characteristicVector_modEq_finrank {L : IntegralLattice V}
    (hLu : L.IsUnimodular) {w : L} (hw : L.IsCharacteristicVector w) :
    L.integralNorm w ≡ Module.finrank ℤ L [ZMOD 2] := by
  have hnull : L.sigNull = 0 := L.radical_eq_bot_iff_sigNull_eq_zero.mp
    ((Submodule.eq_bot_iff _).mpr fun x hx ↦ hLu.nondegenerate.1 x ((L.mem_radical_iff x).mp hx))
  have hsum : L.sigPos + L.sigNeg = Module.finrank ℤ L := by
    rw [L.finrank_carrier, ← L.signature_sum_eq_finrank, hnull, add_zero]
  have h2 : ((L.sigPos : ℤ) - L.sigNeg) ≡ L.integralNorm w [ZMOD 2] :=
    (L.vanDerBlij hLu hw).of_dvd (by decide)
  exact h2.symm.trans (Int.modEq_iff_dvd.mpr ⟨L.sigNeg, by omega⟩)

omit L in
/-- A unimodular lattice of odd rank cannot be even. -/
theorem IsUnimodular.not_isEven_of_odd_finrank {L : IntegralLattice V} (hLu : L.IsUnimodular)
    (hodd : Odd (Module.finrank ℤ L)) : ¬ L.IsEven := fun hLe ↦ by
  have hmod := hLu.integralNorm_characteristicVector_modEq_finrank
    (L.isEven_iff_isCharacteristicVector_zero.mp hLe)
  rw [L.integralNorm_zero] at hmod
  exact Int.not_even_iff_odd.mpr hodd.natCast
    (even_iff_two_dvd.mpr (Int.modEq_zero_iff_dvd.mp hmod.symm))

end TauCeti.IntegralLattice
