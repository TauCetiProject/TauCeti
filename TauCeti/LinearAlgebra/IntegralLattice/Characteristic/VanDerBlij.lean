/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wentao Li, The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Torsion
public import TauCeti.LinearAlgebra.IntegralLattice.Characteristic.Unimodular
public import TauCeti.LinearAlgebra.IntegralLattice.Characteristic.EvenSublattice
public import TauCeti.LinearAlgebra.IntegralLattice.Milgram
import TauCeti.Algebra.Group.Primary.Card
import TauCeti.LinearAlgebra.FiniteBilinearModule.GaussSum.AffineLagrangian
import TauCeti.LinearAlgebra.FiniteBilinearModule.Primary.GaussSum
import TauCeti.LinearAlgebra.FiniteBilinearModule.Primary.Subgroup

/-!
# Van der Blij's characteristic-norm congruence

In a unimodular integral lattice, every characteristic vector has integral norm
congruent to the signature difference modulo eight. The statement applies to all signatures
and to both even and odd lattices.

For the canonical even sublattice `N`, the original lattice determines a subgroup `H = L/N` in the
discriminant form of `N`. A characteristic vector `w` gives a dual vector `w/2` of order dividing
four; the quadratic form is constant on its class plus `H`, with value `w²/8`. Whenever `L` has
odd discriminant, `H` is a bilinear Lagrangian in the `2`-primary component of `q_N`, so character
averaging identifies the `2`-primary Gauss-sum invariant of `q_N` with `w²` modulo eight
(`TauCeti.IntegralLattice.gaussSign_restrict_primaryComponent_two_evenSublattice`). When `L` is
unimodular, `q_N` is purely `2`-primary and Milgram's theorem identifies the same phase with the
signature of `L`. When `L` is even and `w = 0`, the congruence gives divisibility of the signature
by eight.

## Main results

* `TauCeti.IntegralLattice.gaussSign_restrict_primaryComponent_two_evenSublattice`: for a
  nondegenerate lattice of odd discriminant, the `2`-primary Gauss-sum invariant of `q_N` equals the
  norm of any characteristic vector modulo eight.
* `TauCeti.IntegralLattice.vanDerBlij`: the signature difference of a unimodular integral lattice is
  congruent modulo eight to the norm of any characteristic vector.

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
  obtain ⟨k, hk⟩ := Int.modEq_zero_iff_dvd.mp (((L.isCharacteristicVector_iff w).mp hw yL).trans
    (Int.modEq_zero_iff_dvd.mpr
      (even_iff_two_dvd.mp ((L.mem_evenSublattice_carrier_iff yL).mp hy))))
  refine Submodule.mem_one.mpr ⟨k, ?_⟩
  rw [eq_intCast, L.evenSublattice_form, map_smul, LinearMap.smul_apply, smul_eq_mul,
    ← L.integralForm_cast w yL, hk]
  push_cast; ring

private def halfCharacteristicDual {w : L} (hw : L.IsCharacteristicVector w) :
    L.evenSublattice.dualCarrier :=
  ⟨(1 / 2 : ℚ) • (w : V), half_characteristic_mem_dual L hw⟩

private theorem quadratic_halfCharacteristicDual {w : L} (hw : L.IsCharacteristicVector w) :
    L.evenSublattice.discriminantQuadraticMap L.isEven_evenSublattice
        (Submodule.Quotient.mk (halfCharacteristicDual L hw)) =
      ZMod.toRatAddCircle 8 (L.integralNorm w : ZMod 8) := by
  rw [discriminantQuadraticMap_mk, L.evenSublattice_form, ZMod.toRatAddCircle_intCast,
    L.integralNorm_cast, L.norm_apply]
  simp only [halfCharacteristicDual, Subtype.coe_mk, map_smul, LinearMap.smul_apply, smul_eq_mul]
  congr 1; ring

private theorem halfNorm_add_lattice_vector {w : L} (hw : L.IsCharacteristicVector w) (y : L) :
    ∃ k : ℤ, L.form ((1 / 2 : ℚ) • (w : V) + y) ((1 / 2 : ℚ) • (w : V) + y) / 2 =
      L.form ((1 / 2 : ℚ) • (w : V)) ((1 / 2 : ℚ) • (w : V)) / 2 + k := by
  obtain ⟨k, hk⟩ := Int.modEq_iff_dvd.mp ((L.isCharacteristicVector_iff w).mp hw y)
  refine ⟨L.integralForm w y + k, ?_⟩
  rw [← L.norm_apply, ← L.norm_apply, L.norm_add]
  simp only [L.norm_smul, map_smul, LinearMap.smul_apply, smul_eq_mul]
  rw [← L.integralForm_cast w y, ← L.integralNorm_cast y]
  have hkq : (L.integralNorm y : ℚ) - L.integralForm w y = 2 * k := by exact_mod_cast hk
  push_cast; linarith

private theorem quadratic_halfCharacteristicDual_add {w : L} (hw : L.IsCharacteristicVector w)
    (h : L.evenSublattice.discriminantSubgroup
      (L.toIntermediateCarrier L.evenSublattice_form.symm L.evenSublattice_carrier_le)) :
    L.evenSublattice.discriminantQuadraticMap L.isEven_evenSublattice
        ((Submodule.Quotient.mk (halfCharacteristicDual L hw) :
          L.evenSublattice.DiscriminantGroup) + h) =
      L.evenSublattice.discriminantQuadraticMap L.isEven_evenSublattice
        (Submodule.Quotient.mk (halfCharacteristicDual L hw)) := by
  obtain ⟨x, hx⟩ := h
  induction x using Submodule.Quotient.induction_on with
  | _ y =>
    have hy : (y : V) ∈ L.carrier := by
      simpa using (L.evenSublattice.mk_mem_discriminantSubgroup_iff
        (L.toIntermediateCarrier L.evenSublattice_form.symm L.evenSublattice_carrier_le) y).mp hx
    obtain ⟨k, hk⟩ := halfNorm_add_lattice_vector L hw ⟨y, hy⟩
    rw [← Submodule.Quotient.mk_add, discriminantQuadraticMap_mk,
      discriminantQuadraticMap_mk, L.evenSublattice_form]
    simp only [Submodule.coe_add, halfCharacteristicDual, Subtype.coe_mk]
    rw [hk, AddCircle.coe_add_intCast]

private theorem halfCharacteristicDual_mem_primaryComponent_two [L.IsNondegenerate] {w : L}
    (hw : L.IsCharacteristicVector w) :
    (Submodule.Quotient.mk (halfCharacteristicDual L hw) :
      L.evenSublattice.discriminantQuadraticModule L.isEven_evenSublattice) ∈
      AddCommGroup.primaryComponent
        (L.evenSublattice.discriminantQuadraticModule L.isEven_evenSublattice) 2 := by
  refine AddCommGroup.mem_primaryComponent.mpr ⟨2, ?_⟩
  -- State the torsion equation in `DiscriminantGroup` so quotient `nsmul` and `mk_smul` use the
  -- quotient `AddCommGroup` instance rather than `discriminantQuadraticModule.addCommGroup`.
  have h : (2 ^ 2 • Submodule.Quotient.mk (halfCharacteristicDual L hw) :
      L.evenSublattice.DiscriminantGroup) = 0 := by
    rw [← Nat.cast_smul_eq_nsmul ℤ, ← Submodule.Quotient.mk_smul,
      L.evenSublattice.discriminantGroup_mk_eq_zero_iff, L.evenSublattice_carrier]
    refine ⟨(2 : ℤ) • w, L.two_smul_mem_evenSubmodule w, ?_⟩
    rw [map_smul, Submodule.coe_subtype, Submodule.coe_smul, halfCharacteristicDual]
    simp only [Nat.cast_pow, Nat.cast_ofNat, ← Int.cast_smul_eq_zsmul ℚ, smul_smul]; norm_num
  exact h

private theorem natCard_comap_primaryComponent_two_evenSublattice_sq [L.IsNondegenerate]
    (hodd : Odd L.discriminant) :
    let A := L.evenSublattice.discriminantQuadraticModule L.isEven_evenSublattice
    let H : AddSubgroup A := L.evenSublattice.discriminantSubgroup
      (L.toIntermediateCarrier L.evenSublattice_form.symm L.evenSublattice_carrier_le)
    Nat.card (H.comap (AddCommGroup.primaryComponent A 2).subtype) ^ 2 =
      Nat.card (A.restrict (AddCommGroup.primaryComponent A 2)) := by
  dsimp only
  let A := L.evenSublattice.discriminantQuadraticModule L.isEven_evenSublattice
  let P := AddCommGroup.primaryComponent A 2
  let I := L.toIntermediateCarrier L.evenSublattice_form.symm L.evenSublattice_carrier_le
  let H : AddSubgroup A := L.evenSublattice.discriminantSubgroup I
  let idx := L.evenSublattice.carrier.toAddSubgroup.relIndex L.carrier.toAddSubgroup
  have hcardH : Nat.card H = idx :=
    (IntermediateCarrier.index_eq_natCard_discriminantSubgroup I).symm.trans
      (by simp [IntermediateCarrier.index_def, I, idx])
  have hidx_cases : idx = 1 ∨ idx = 2 := by
    by_cases hL : L.IsEven <;> simp [idx, L.relIndex_evenSublattice, hL]
  have hHP : H ≤ P := fun x hx ↦ by
    have hx0 : idx • x = 0 :=
      hcardH ▸ congrArg Subtype.val (card_nsmul_eq_zero' (x := (⟨x, hx⟩ : H)))
    rcases hidx_cases with h1 | h2
    · exact AddCommGroup.mem_primaryComponent.mpr ⟨0, by simpa [h1] using hx0⟩
    · exact AddCommGroup.mem_primaryComponent.mpr ⟨1, by simpa [h2] using hx0⟩
  have hcardH₂ : Nat.card (H.comap P.subtype) = idx :=
    (Nat.card_congr (H.addSubgroupOfEquivOfLe hHP).toEquiv).trans hcardH
  have hcardA : Nat.card A = L.discriminant * idx ^ 2 := by
    rw [L.evenSublattice.natCard_discriminantQuadraticModule L.isEven_evenSublattice,
      L.evenSublattice.natCard_discriminantGroup,
      L.evenSublattice.discriminant_eq_mul_relIndex_sq L L.evenSublattice_form
        L.evenSublattice_carrier_le]
  have hfac0 : L.discriminant.factorization 2 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd hodd.not_two_dvd_nat
  rw [hcardH₂, A.natCard_restrict P,
    TauCeti.AddCommGroup.natCard_primaryComponent A Nat.prime_two, hcardA]
  rcases hidx_cases with h1 | h2
  · simp [h1, hfac0]
  · rw [h2, Nat.factorization_mul hodd.pos.ne' (by positivity), Finsupp.coe_add, Pi.add_apply,
      hfac0, Nat.factorization_pow, Finsupp.smul_apply, Nat.prime_two.factorization_self]
    norm_num

private theorem isLagrangian_comap_primaryComponent_two_evenSublattice [L.IsNondegenerate]
    (hodd : Odd L.discriminant) :
    let A := L.evenSublattice.discriminantQuadraticModule L.isEven_evenSublattice
    let P := AddCommGroup.primaryComponent A 2
    let H : AddSubgroup A := L.evenSublattice.discriminantSubgroup
      (L.toIntermediateCarrier L.evenSublattice_form.symm L.evenSublattice_carrier_le)
    (A.restrict P).toFiniteBilinearModule.IsLagrangian (H.comap P.subtype) ∧
      Nat.card (H.comap P.subtype) ^ 2 = Nat.card (A.restrict P) := by
  dsimp only
  let A := L.evenSublattice.discriminantQuadraticModule L.isEven_evenSublattice
  let P := AddCommGroup.primaryComponent A 2
  let I := L.toIntermediateCarrier L.evenSublattice_form.symm L.evenSublattice_carrier_le
  let H : AddSubgroup A := L.evenSublattice.discriminantSubgroup I
  have hsq := natCard_comap_primaryComponent_two_evenSublattice_sq L hodd
  have hpart : H.comap P.subtype = AddSubgroup.primaryPart H 2 :=
    AddSubgroup.ext fun x ↦ (AddSubgroup.mem_primaryPart_iff H 2 x).symm
  have hH₂_iso : (A.restrict P).toFiniteBilinearModule.IsIsotropic (H.comap P.subtype) :=
    hpart.symm ▸ (L.evenSublattice.discriminantBilinearModule.isIsotropic_iff_primaryPart H).mp
      ((IntermediateCarrier.isIntegral_iff_isIsotropic_discriminantSubgroup I).mp
        (L.isIntegral_toIntermediateCarrier L.evenSublattice_form.symm L.evenSublattice_carrier_le))
      2 Nat.prime_two
  exact ⟨FiniteBilinearModule.IsIsotropic.isLagrangian_of_card_sq_eq _ hH₂_iso
    (A.isNondegenerate_restrict_primaryComponent
      (L.evenSublattice.isNondegenerate_discriminantQuadraticModule L.isEven_evenSublattice)
      Nat.prime_two) hsq, hsq⟩

/-- For a nondegenerate integral lattice of odd discriminant, the `2`-primary component of the
discriminant quadratic module of its even sublattice has Gauss-sum invariant equal to the norm of
any characteristic vector modulo eight. -/
theorem gaussSign_restrict_primaryComponent_two_evenSublattice [L.IsNondegenerate]
    (hodd : Odd L.discriminant) {w : L} (hw : L.IsCharacteristicVector w) :
    ((L.evenSublattice.discriminantQuadraticModule L.isEven_evenSublattice).restrict
      (AddCommGroup.primaryComponent
        (L.evenSublattice.discriminantQuadraticModule L.isEven_evenSublattice) 2)).gaussSign =
      (L.integralNorm w : ZMod 8) := by
  let A := L.evenSublattice.discriminantQuadraticModule L.isEven_evenSublattice
  let P := AddCommGroup.primaryComponent A 2; let A₂ := A.restrict P
  let H : AddSubgroup A := L.evenSublattice.discriminantSubgroup
    (L.toIntermediateCarrier L.evenSublattice_form.symm L.evenSublattice_carrier_le)
  let H₂ : AddSubgroup A₂ := H.comap P.subtype
  obtain ⟨hH₂_lag, hsq⟩ := isLagrangian_comap_primaryComponent_two_evenSublattice L hodd
  let a₂ : A₂ := ⟨Submodule.Quotient.mk (halfCharacteristicDual L hw),
    halfCharacteristicDual_mem_primaryComponent_two L hw⟩
  have ha₂ (h : H₂) : A₂.quadratic (a₂ + h) = A₂.quadratic a₂ :=
    (A.restrict_quadratic P (a₂ + (h : A₂))).trans <|
      (L.evenSublattice.discriminantQuadraticModule_quadratic L.isEven_evenSublattice _).trans <|
        (quadratic_halfCharacteristicDual_add L hw ⟨h.val.val, h.property⟩).trans <|
          (L.evenSublattice.discriminantQuadraticModule_quadratic L.isEven_evenSublattice
            a₂.val).symm.trans (A.restrict_quadratic P a₂).symm
  have hqa₂ : A₂.quadratic a₂ = ZMod.toRatAddCircle 8 (L.integralNorm w : ZMod 8) :=
    (A.restrict_quadratic P a₂).trans <|
      (L.evenSublattice.discriminantQuadraticModule_quadratic L.isEven_evenSublattice
        a₂.val).trans (quadratic_halfCharacteristicDual L hw)
  have hsq' : Nat.card H₂ ^ 2 = Nat.card A₂ := hsq.trans (A.natCard_restrict P).symm
  refine FiniteQuadraticModule.gaussSign_eq_of_gaussSum_eq A₂ ?_
  rw [FiniteQuadraticModule.gaussSum_eq_natCard_mul_expCircle_of_bilinear_isLagrangian a₂
    hH₂_lag ha₂, hqa₂, ← hsq', Nat.cast_pow, Real.sqrt_sq (Nat.cast_nonneg _),
    Complex.ofReal_natCast]

/-- Milgram's theorem applied to `L.evenSublattice` expresses its Gauss-sum invariant as the
signature difference of `L` modulo eight. -/
theorem gaussSign_evenSublattice_eq_sigPos_sub_sigNeg [L.IsNondegenerate] :
    (L.evenSublattice.discriminantQuadraticModule L.isEven_evenSublattice).gaussSign =
      (L.sigPos : ZMod 8) - L.sigNeg := by
  have hm := L.evenSublattice.gaussSign_discriminantQuadraticModule_eq_sigPos_sub_sigNeg
    L.isEven_evenSublattice
  have hs := L.evenSublattice_signature
  simp only [signature, Prod.mk.injEq] at hs
  rwa [hs.1, hs.2.2] at hm

/-- **Van der Blij's congruence:** the signature difference of a unimodular
integral lattice is congruent modulo eight to the norm of any characteristic vector. -/
theorem vanDerBlij (hL : L.IsUnimodular) {w : L}
    (hw : L.IsCharacteristicVector w) :
    ((L.sigPos : ℤ) - L.sigNeg) ≡ L.integralNorm w [ZMOD 8] := by
  have : L.IsNondegenerate := ⟨hL.nondegenerate⟩
  have hdisc : L.discriminant = 1 := L.isUnimodular_iff_discriminant_eq_one.mp hL
  have hsub : (Nat.card (L.evenSublattice.discriminantQuadraticModule
      L.isEven_evenSublattice)).primeFactors ⊆ ({2} : Finset ℕ) := by
    rw [L.evenSublattice.natCard_discriminantQuadraticModule L.isEven_evenSublattice,
      L.evenSublattice.natCard_discriminantGroup]
    simpa [hdisc] using L.primeFactors_discriminant_evenSublattice_subset
  have hg := FiniteQuadraticModule.gaussSign_eq_sum_of_primeFactors_subset
    (L.evenSublattice.isNondegenerate_discriminantQuadraticModule L.isEven_evenSublattice)
    (fun p hp ↦ Finset.mem_singleton.mp hp ▸ Nat.prime_two) hsub
  rw [Finset.sum_singleton,
    L.gaussSign_restrict_primaryComponent_two_evenSublattice (hdisc ▸ odd_one) hw] at hg
  apply (ZMod.intCast_eq_intCast_iff _ _ 8).mp
  simpa only [Int.cast_sub, Int.cast_natCast] using
    L.gaussSign_evenSublattice_eq_sigPos_sub_sigNeg.symm.trans hg

end TauCeti.IntegralLattice
