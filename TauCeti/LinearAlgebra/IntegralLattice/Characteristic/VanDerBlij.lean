/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wentao Li, The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.Characteristic.Unimodular
public import TauCeti.LinearAlgebra.IntegralLattice.Characteristic.EvenSublattice.Basic
public import TauCeti.LinearAlgebra.IntegralLattice.Milgram
import TauCeti.LinearAlgebra.FiniteBilinearModule.GaussSum.AffineLagrangian
import TauCeti.LinearAlgebra.FiniteBilinearModule.Primary.GaussSum
import TauCeti.LinearAlgebra.IntegralLattice.Characteristic.EvenSublattice.Discriminant

/-!
# Van der Blij's characteristic-norm congruence

In a nondegenerate integral lattice `L` of odd discriminant, every characteristic vector `w` has
integral norm modulo eight equal to the signature difference of `L` minus the odd-prime Gauss-sum
invariants of the canonical even sublattice `N = L.evenSublattice`
(`TauCeti.IntegralLattice.integralNorm_cast_zmod_eight_eq_of_odd_discriminant`). Specializing to
unimodular lattices (`L.discriminant = 1`, with no odd prime factors) recovers van der Blij's
theorem (`TauCeti.IntegralLattice.vanDerBlij`): every characteristic vector has integral norm
congruent to the signature difference modulo eight.

For the canonical even sublattice `N`, the subgroup `H = L / N` has order `[L : N] ∈ {1, 2}` and
lies in the `2`-primary component `(A_N)_2`, which has order `[L : N]²` because `L.discriminant` is
odd; thus `H` is a bilinear Lagrangian in `(A_N)_2`. A characteristic vector `w` gives a dual vector
`w / 2` of `N` whose class lies in `(A_N)_2`, and `q_N` is constant on its coset modulo `H` with
value `w² / 8`. Character averaging evaluates the `2`-primary Gauss sign as `w² mod 8`, while
Milgram's theorem on `N` identifies the total Gauss sign of `A_N` with the signature difference of
`N`, which equals that of `L`.

## Main declarations

* `TauCeti.IntegralLattice.gaussSign_primaryComponent_two_evenSublattice`: at odd discriminant, the
  `2`-primary Gauss sign of `L.evenSublattice` equals `(L.integralNorm w : ZMod 8)`.
* `TauCeti.IntegralLattice.integralNorm_cast_zmod_eight_eq_of_odd_discriminant`: generalized
  van der Blij identity at odd discriminant.
* `TauCeti.IntegralLattice.vanDerBlij`: van der Blij's congruence modulo `8` for unimodular
  lattices.

## References

* F. van der Blij, *An invariant of quadratic forms mod 8*, Indag. Math. 21 (1959), 291–293.
* J. Milnor and D. Husemoller, *Symmetric Bilinear Forms*, Appendix 4.
-/

public section

open scoped Real

namespace TauCeti.IntegralLattice

universe u
variable {V : Type u} [AddCommGroup V] [Module ℚ V] (L : IntegralLattice V)

/-- For a nondegenerate lattice `L` of odd discriminant and a characteristic vector `w`, the
`2`-primary component of the discriminant quadratic module of `L.evenSublattice` has Gauss-sum
invariant `(L.integralNorm w : ZMod 8)`. -/
theorem gaussSign_primaryComponent_two_evenSublattice [L.IsNondegenerate]
    (hodd : Odd L.discriminant) {w : L} (hw : L.IsCharacteristicVector w) :
    ((L.evenSublattice.discriminantQuadraticModule L.isEven_evenSublattice).restrict
      (AddCommGroup.primaryComponent
        (L.evenSublattice.discriminantQuadraticModule L.isEven_evenSublattice) 2)).gaussSign =
      (L.integralNorm w : ZMod 8) := by
  let N := L.evenSublattice
  let A := N.discriminantQuadraticModule L.isEven_evenSublattice
  let A₂ := A.restrict (AddCommGroup.primaryComponent A 2)
  let H : AddSubgroup A := N.discriminantSubgroup
    (L.toIntermediateCarrier L.evenSublattice_form.symm L.evenSublattice_carrier_le)
  let H₂ : AddSubgroup A₂ := H.addSubgroupOf (AddCommGroup.primaryComponent A 2)
  have hH2_lag : A₂.toFiniteBilinearModule.IsLagrangian H₂ :=
    L.isLagrangian_evenSublattice_primaryComponent_two hodd
  let a₂ : A₂ :=
    ⟨Submodule.Quotient.mk (L.halfCharacteristicDual hw),
      L.halfCharacteristicDual_mk_mem_primaryComponent_two hw⟩
  have hqa : A₂.quadratic a₂ = ZMod.toRatAddCircle 8 (L.integralNorm w : ZMod 8) := by
    rw [FiniteQuadraticModule.restrict_quadratic, discriminantQuadraticModule_quadratic]
    exact L.discriminantQuadraticMap_mk_halfCharacteristicDual hw
  have ha_const (h : H₂) : A₂.quadratic (a₂ + h) = A₂.quadratic a₂ := by
    have h1 : A₂.quadratic (a₂ + h) =
        N.discriminantQuadraticMap L.isEven_evenSublattice (a₂.val + h.val.val) :=
      (A.restrict_quadratic _ (a₂ + (h : A₂))).trans
        ((congrArg A.quadratic
          (AddSubgroup.coe_add (AddCommGroup.primaryComponent A 2) a₂ (h : A₂))).trans
          (N.discriminantQuadraticModule_quadratic L.isEven_evenSublattice _))
    have h2 : A₂.quadratic a₂ = N.discriminantQuadraticMap L.isEven_evenSublattice a₂.val :=
      (A.restrict_quadratic _ a₂).trans
        (N.discriminantQuadraticModule_quadratic L.isEven_evenSublattice _)
    rw [h1, h2]
    exact L.discriminantQuadraticMap_mk_halfCharacteristicDual_add hw ⟨h.val.val, h.property⟩
  have hG := FiniteQuadraticModule.gaussSum_eq_natCard_mul_expCircle_of_bilinear_isLagrangian
    a₂ hH2_lag ha_const
  have hsq : Nat.card H₂ ^ 2 = Nat.card A₂ :=
    FiniteBilinearModule.IsLagrangian.card_sq A₂.toFiniteBilinearModule hH2_lag
      (A.isNondegenerate_restrict_primaryComponent
        (N.isNondegenerate_discriminantQuadraticModule L.isEven_evenSublattice) Nat.prime_two)
  refine FiniteQuadraticModule.gaussSign_eq_of_gaussSum_eq A₂ ?_
  rw [hG, hqa, ← hsq, Nat.cast_pow, Real.sqrt_sq (Nat.cast_nonneg _), Complex.ofReal_natCast]

/-- **Generalized van der Blij identity at odd discriminant.** For a nondegenerate lattice `L` of
odd discriminant and a characteristic vector `w`, the norm of `w` modulo `8` equals the signature
difference of `L` minus the odd-prime Gauss-sum invariants of `L.evenSublattice`. -/
theorem integralNorm_cast_zmod_eight_eq_of_odd_discriminant [L.IsNondegenerate]
    (hodd : Odd L.discriminant) {w : L} (hw : L.IsCharacteristicVector w) :
    (L.integralNorm w : ZMod 8) = ((L.sigPos : ZMod 8) - L.sigNeg) -
      ∑ p ∈ L.discriminant.primeFactors,
        ((L.evenSublattice.discriminantQuadraticModule L.isEven_evenSublattice).restrict
          (AddCommGroup.primaryComponent
            (L.evenSublattice.discriminantQuadraticModule L.isEven_evenSublattice) p)).gaussSign :=
  by
  classical
  let N := L.evenSublattice
  have hNe : N.IsEven := L.isEven_evenSublattice
  let A := N.discriminantQuadraticModule hNe
  have hdisc_N : Nat.card A =
      L.discriminant * N.carrier.toAddSubgroup.relIndex L.carrier.toAddSubgroup ^ 2 := by
    rw [N.natCard_discriminantQuadraticModule, N.natCard_discriminantGroup,
      N.discriminant_eq_mul_relIndex_sq L L.evenSublattice_form L.evenSublattice_carrier_le]
  have h2_notMem : 2 ∉ L.discriminant.primeFactors := fun hm ↦
    Nat.not_even_iff_odd.mpr hodd (even_iff_two_dvd.mpr (Nat.dvd_of_mem_primeFactors hm))
  have hsub : (Nat.card A).primeFactors ⊆ insert 2 L.discriminant.primeFactors := by
    intro p hp
    have hp_prime := Nat.prime_of_mem_primeFactors hp
    have hdvd := Nat.dvd_of_mem_primeFactors hp
    rw [hdisc_N] at hdvd
    rcases hp_prime.dvd_mul.mp hdvd with hdL | hdI
    · exact Finset.mem_insert_of_mem
        (Nat.mem_primeFactors.mpr ⟨hp_prime, hdL, hodd.pos.ne'⟩)
    · have hdI' : p ∣ N.carrier.toAddSubgroup.relIndex L.carrier.toAddSubgroup :=
        hp_prime.dvd_of_dvd_pow hdI
      have hp_le : p ≤ 2 :=
        (Nat.le_of_dvd L.relIndex_evenSublattice_pos hdI').trans L.relIndex_evenSublattice_le_two
      simp [le_antisymm hp_le hp_prime.two_le]
  have hprime_S : ∀ p ∈ insert 2 L.discriminant.primeFactors, p.Prime := by
    intro p hp
    rcases Finset.mem_insert.mp hp with rfl | hp'
    · exact Nat.prime_two
    · exact Nat.prime_of_mem_primeFactors hp'
  have hsum := A.gaussSign_eq_sum_primaryComponent
    (N.isNondegenerate_discriminantQuadraticModule hNe)
    (insert 2 L.discriminant.primeFactors) hprime_S hsub
  rw [Finset.sum_insert h2_notMem,
    L.gaussSign_primaryComponent_two_evenSublattice hodd hw] at hsum
  have hmilgram : A.gaussSign = (L.sigPos : ZMod 8) - L.sigNeg := by
    have hm := N.gaussSign_discriminantQuadraticModule_eq_sigPos_sub_sigNeg hNe
    have hsig := L.evenSublattice_signature
    simp only [signature, Prod.mk.injEq] at hsig
    rwa [hsig.1, hsig.2.2] at hm
  rw [hmilgram] at hsum
  exact eq_sub_of_add_eq hsum.symm

/-- **Van der Blij's congruence:** the signature difference of a unimodular
integral lattice is congruent modulo eight to the norm of any characteristic vector. -/
theorem vanDerBlij (hL : L.IsUnimodular) {w : L}
    (hw : L.IsCharacteristicVector w) :
    ((L.sigPos : ℤ) - L.sigNeg) ≡ L.integralNorm w [ZMOD 8] := by
  have : L.IsNondegenerate := ⟨hL.nondegenerate⟩
  have hdisc : L.discriminant = 1 := L.isUnimodular_iff_discriminant_eq_one.mp hL
  have h := L.integralNorm_cast_zmod_eight_eq_of_odd_discriminant (hdisc ▸ odd_one) hw
  rw [hdisc, Nat.primeFactors_one, Finset.sum_empty, sub_zero] at h
  apply (ZMod.intCast_eq_intCast_iff _ _ 8).mp
  simpa only [Int.cast_sub, Int.cast_natCast] using h.symm

end TauCeti.IntegralLattice
