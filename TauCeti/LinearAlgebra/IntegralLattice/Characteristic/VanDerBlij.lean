/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wentao Li, The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.Characteristic.Unimodular
public import TauCeti.LinearAlgebra.IntegralLattice.Characteristic.EvenSublattice
public import TauCeti.LinearAlgebra.IntegralLattice.Milgram
public import TauCeti.LinearAlgebra.IntegralLattice.Overlattice.Isotropic
import TauCeti.Algebra.Group.Primary.Card
import TauCeti.LinearAlgebra.FiniteBilinearModule.GaussSum.AffineLagrangian
import TauCeti.LinearAlgebra.FiniteBilinearModule.Primary.GaussSum
import TauCeti.LinearAlgebra.IntegralLattice.Overlattice.Index

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

* `TauCeti.IntegralLattice.halfCharacteristicDual`,
  `TauCeti.IntegralLattice.quadratic_halfCharacteristicDual`, and
  `TauCeti.IntegralLattice.quadratic_halfCharacteristicDual_add`: the dual vector `w / 2 ∈ Nᵛ` and
  constancy of `q_N` on its `L / N`-coset.
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

private theorem half_characteristic_mem_dual {w : L} (hw : L.IsCharacteristicVector w) :
    (1 / 2 : ℚ) • (w : V) ∈ L.evenSublattice.dualCarrier := by
  rw [LinearMap.BilinForm.mem_dualSubmodule]
  intro y hy
  let yL : L := ⟨y, L.evenSublattice_carrier_le hy⟩
  have he : Even (L.integralNorm yL) := (L.mem_evenSublattice_carrier_iff yL).mp hy
  have hp := (L.isCharacteristicVector_iff w).mp hw yL
  have hb : 2 ∣ L.integralForm w yL := Int.modEq_zero_iff_dvd.mp
    (hp.trans (Int.modEq_zero_iff_dvd.mpr (even_iff_two_dvd.mp he)))
  obtain ⟨k, hk⟩ := hb
  refine Submodule.mem_one.mpr ⟨k, ?_⟩
  rw [eq_intCast, L.evenSublattice_form, map_smul, LinearMap.smul_apply, smul_eq_mul,
    ← L.integralForm_cast w yL, hk]
  push_cast
  ring

/-- For a characteristic vector `w` of `L`, half of `w` lies in the dual lattice of
`L.evenSublattice`. -/
noncomputable def halfCharacteristicDual {w : L} (hw : L.IsCharacteristicVector w) :
    L.evenSublattice.dualCarrier :=
  ⟨(1 / 2 : ℚ) • (w : V), half_characteristic_mem_dual L hw⟩

/-- The underlying ambient vector of `halfCharacteristicDual` is `(1 / 2) • w`. -/
@[simp]
theorem coe_halfCharacteristicDual {w : L} (hw : L.IsCharacteristicVector w) :
    (L.halfCharacteristicDual hw : V) = (1 / 2 : ℚ) • (w : V) := by
  rfl

/-- On the class of `w / 2`, the discriminant quadratic map of `L.evenSublattice` takes the value
`L.integralNorm w / 8 mod ℤ`. -/
theorem quadratic_halfCharacteristicDual {w : L} (hw : L.IsCharacteristicVector w) :
    L.evenSublattice.discriminantQuadraticMap L.isEven_evenSublattice
        (Submodule.Quotient.mk (L.halfCharacteristicDual hw)) =
      ZMod.toRatAddCircle 8 (L.integralNorm w : ZMod 8) := by
  rw [discriminantQuadraticMap_mk, L.evenSublattice_form, ZMod.toRatAddCircle_intCast,
    L.integralNorm_cast, L.norm_apply]
  simp only [coe_halfCharacteristicDual, map_smul, LinearMap.smul_apply, smul_eq_mul]
  congr 1
  ring

private theorem halfNorm_add_lattice_vector {w : L} (hw : L.IsCharacteristicVector w)
    (y : L) :
    ∃ k : ℤ, L.form ((1 / 2 : ℚ) • (w : V) + y)
        ((1 / 2 : ℚ) • (w : V) + y) / 2 =
      L.form ((1 / 2 : ℚ) • (w : V)) ((1 / 2 : ℚ) • (w : V)) / 2 + k := by
  obtain ⟨k, hk⟩ := Int.modEq_iff_dvd.mp ((L.isCharacteristicVector_iff w).mp hw y)
  refine ⟨L.integralForm w y + k, ?_⟩
  rw [← L.norm_apply, ← L.norm_apply, L.norm_add]
  simp only [L.norm_smul, map_smul, LinearMap.smul_apply, smul_eq_mul]
  rw [← L.integralForm_cast w y, ← L.integralNorm_cast y]
  have hkq : (L.integralNorm y : ℚ) - L.integralForm w y = 2 * k := by exact_mod_cast hk
  push_cast
  linarith

/-- The discriminant quadratic map of `L.evenSublattice` is constant on the `L / L.evenSublattice`
coset of `halfCharacteristicDual`. -/
theorem quadratic_halfCharacteristicDual_add {w : L}
    (hw : L.IsCharacteristicVector w)
    (h : L.evenSublattice.discriminantSubgroup
      (L.toIntermediateCarrier L.evenSublattice_form.symm L.evenSublattice_carrier_le)) :
    L.evenSublattice.discriminantQuadraticMap L.isEven_evenSublattice
        ((Submodule.Quotient.mk (L.halfCharacteristicDual hw) :
          L.evenSublattice.DiscriminantGroup) + h) =
      L.evenSublattice.discriminantQuadraticMap L.isEven_evenSublattice
        (Submodule.Quotient.mk (L.halfCharacteristicDual hw)) := by
  obtain ⟨x, hx⟩ := h
  induction x using Submodule.Quotient.induction_on with
  | _ y =>
    have hy : (y : V) ∈ L.carrier := by
      have := (L.evenSublattice.mk_mem_discriminantSubgroup_iff
        (L.toIntermediateCarrier L.evenSublattice_form.symm L.evenSublattice_carrier_le) y).mp hx
      rwa [coe_toIntermediateCarrier] at this
    obtain ⟨k, hk⟩ := halfNorm_add_lattice_vector L hw ⟨y, hy⟩
    rw [← Submodule.Quotient.mk_add, discriminantQuadraticMap_mk,
      discriminantQuadraticMap_mk, L.evenSublattice_form]
    simp only [Submodule.coe_add, coe_halfCharacteristicDual]
    rw [hk, AddCircle.coe_add_intCast]

private theorem halfCharacteristicDual_mk_mem_primaryComponent_two {w : L}
    (hw : L.IsCharacteristicVector w) :
    Submodule.Quotient.mk (L.halfCharacteristicDual hw) ∈
      AddCommGroup.primaryComponent L.evenSublattice.DiscriminantGroup 2 := by
  refine AddCommGroup.mem_primaryComponent.mpr ⟨2, ?_⟩
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero,
    L.evenSublattice.mem_carrierInDual_iff]
  have hval : (((2 ^ 2 : ℕ) • L.halfCharacteristicDual hw : L.evenSublattice.dualCarrier) : V) =
      (((2 : ℤ) • w : L) : V) := by
    simp only [SetLike.val_smul, coe_halfCharacteristicDual, Submodule.coe_smul_of_tower]
    rw [← Nat.cast_smul_eq_nsmul ℚ (2 ^ 2), smul_smul]
    norm_num
    rw [two_smul ℚ (w : V), two_zsmul]
  rw [hval, L.evenSublattice_carrier]
  exact Submodule.mem_map_of_mem (L.two_smul_mem_evenSubmodule w)

private theorem natCard_primaryComponent_two_evenSublattice [L.IsNondegenerate]
    (hodd : Odd L.discriminant) :
    Nat.card (AddCommGroup.primaryComponent L.evenSublattice.DiscriminantGroup 2) =
      L.evenSublattice.carrier.toAddSubgroup.relIndex L.carrier.toAddSubgroup ^ 2 := by
  have hfact_L : L.discriminant.factorization 2 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd fun hdvd ↦
      Nat.not_even_iff_odd.mpr hodd (even_iff_two_dvd.mpr hdvd)
  rw [TauCeti.AddCommGroup.natCard_primaryComponent _ Nat.prime_two,
    L.evenSublattice.natCard_discriminantGroup,
    L.evenSublattice.discriminant_eq_mul_relIndex_sq L L.evenSublattice_form
      L.evenSublattice_carrier_le]
  rcases L.relIndex_evenSublattice_eq_one_or_two with h1 | h2
  · rw [h1, one_pow, mul_one, hfact_L, pow_zero]
  · rw [h2, Nat.factorization_mul hodd.pos.ne' (by decide), Finsupp.add_apply, hfact_L, zero_add,
      Nat.factorization_pow, Finsupp.smul_apply, Nat.Prime.factorization_self Nat.prime_two,
      smul_eq_mul, mul_one]

private theorem isLagrangian_evenSublattice_primaryComponent_two [L.IsNondegenerate]
    (hodd : Odd L.discriminant) :
    let N := L.evenSublattice
    let A := N.discriminantQuadraticModule L.isEven_evenSublattice
    let H : AddSubgroup A := N.discriminantSubgroup
      (L.toIntermediateCarrier L.evenSublattice_form.symm L.evenSublattice_carrier_le)
    let A₂ := A.restrict (AddCommGroup.primaryComponent A 2)
    let H₂ : AddSubgroup A₂ := H.addSubgroupOf (AddCommGroup.primaryComponent A 2)
    A₂.toFiniteBilinearModule.IsLagrangian H₂ := by
  intro N A H A₂ H₂
  let M₀ : N.IntermediateCarrier :=
    L.toIntermediateCarrier L.evenSublattice_form.symm L.evenSublattice_carrier_le
  have hI : IntermediateCarrier.IsIntegral M₀ :=
    L.isIntegral_toIntermediateCarrier L.evenSublattice_form.symm L.evenSublattice_carrier_le
  have hidx : IntermediateCarrier.index M₀ =
      N.carrier.toAddSubgroup.relIndex L.carrier.toAddSubgroup := by
    rw [IntermediateCarrier.index_def, coe_toIntermediateCarrier]
  have hcard_H : Nat.card H = N.carrier.toAddSubgroup.relIndex L.carrier.toAddSubgroup :=
    (IntermediateCarrier.index_eq_natCard_discriminantSubgroup M₀).symm.trans hidx
  have hH_le : H ≤ AddCommGroup.primaryComponent A 2 := fun x hx ↦ by
    have hkill : N.carrier.toAddSubgroup.relIndex L.carrier.toAddSubgroup • x = 0 :=
      addOrderOf_dvd_iff_nsmul_eq_zero.mp (hcard_H ▸ H.addOrderOf_dvd_natCard hx)
    refine AddCommGroup.mem_primaryComponent.mpr ⟨1, ?_⟩
    rw [pow_one]
    rcases L.relIndex_evenSublattice_eq_one_or_two with h1 | h2
    · rw [h1, one_nsmul] at hkill
      simp [hkill]
    · rwa [h2] at hkill
  have hcard_H2 : Nat.card H₂ = N.carrier.toAddSubgroup.relIndex L.carrier.toAddSubgroup :=
    (Nat.card_congr (AddSubgroup.addSubgroupOfEquivOfLe hH_le).toEquiv).trans hcard_H
  have hH2_iso : H₂ ≤ A₂.toFiniteBilinearModule.orthogonalComplement H₂ := fun x hx ↦ by
    rw [A₂.toFiniteBilinearModule.mem_orthogonalComplement_iff]
    exact fun y hy ↦ (N.discriminantBilinearModule_pairing x.1 y.1).trans
      ((IntermediateCarrier.isIntegral_iff_forall_discriminantPairing_eq_zero M₀).mp hI
        x.1 hx y.1 hy)
  refine (A₂.toFiniteBilinearModule.isLagrangian_def H₂).mpr
    (AddSubgroup.eq_of_le_of_card_ge hH2_iso ?_)
  have hmul := FiniteBilinearModule.IsNondegenerate.card_mul_card_orthogonalComplement
    A₂.toFiniteBilinearModule
    (A.isNondegenerate_restrict_primaryComponent
      (N.isNondegenerate_discriminantQuadraticModule L.isEven_evenSublattice) Nat.prime_two) H₂
  have hcard_A2 : Nat.card A₂.toFiniteBilinearModule = Nat.card H₂ * Nat.card H₂ :=
    (A.natCard_restrict _).trans
      ((L.natCard_primaryComponent_two_evenSublattice hodd).trans (by rw [hcard_H2, sq]))
  rw [hcard_A2] at hmul
  exact (Nat.mul_left_cancel (hcard_H2 ▸ L.relIndex_evenSublattice_pos) hmul).le

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
    exact L.quadratic_halfCharacteristicDual hw
  have ha_const (h : H₂) : A₂.quadratic (a₂ + h) = A₂.quadratic a₂ :=
    L.quadratic_halfCharacteristicDual_add hw ⟨h.1.1, h.2⟩
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
