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
import TauCeti.LinearAlgebra.FiniteBilinearModule.Primary.Component
import TauCeti.LinearAlgebra.IntegralLattice.Overlattice.Metabolic

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

private def halfCharacteristicDual {w : L} (hw : L.IsCharacteristicVector w) :
    L.evenSublattice.dualCarrier :=
  ⟨(1 / 2 : ℚ) • (w : V), half_characteristic_mem_dual L hw⟩

private theorem quadratic_halfCharacteristicDual {w : L} (hw : L.IsCharacteristicVector w) :
    L.evenSublattice.discriminantQuadraticMap L.isEven_evenSublattice
        (Submodule.Quotient.mk (halfCharacteristicDual L hw)) =
      ZMod.toRatAddCircle 8 (L.integralNorm w : ZMod 8) := by
  rw [discriminantQuadraticMap_mk, L.evenSublattice_form, ZMod.toRatAddCircle_intCast,
    L.integralNorm_cast, L.norm_apply]
  simp only [halfCharacteristicDual, Subtype.coe_mk, map_smul, LinearMap.smul_apply,
    smul_eq_mul]
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

private theorem quadratic_halfCharacteristicDual_add {w : L}
    (hw : L.IsCharacteristicVector w)
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
      have := (L.evenSublattice.mk_mem_discriminantSubgroup_iff
        (L.toIntermediateCarrier L.evenSublattice_form.symm L.evenSublattice_carrier_le) y).mp hx
      rwa [coe_toIntermediateCarrier] at this
    obtain ⟨k, hk⟩ := halfNorm_add_lattice_vector L hw ⟨y, hy⟩
    rw [← Submodule.Quotient.mk_add, discriminantQuadraticMap_mk,
      discriminantQuadraticMap_mk, L.evenSublattice_form]
    simp only [Submodule.coe_add, halfCharacteristicDual, Subtype.coe_mk]
    rw [hk, AddCircle.coe_add_intCast]

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
  let a : A := Submodule.Quotient.mk (halfCharacteristicDual L hw)
  have hM : hI.toIntegralLattice.IsUnimodular := by
    rw [L.toIntegralLattice_toIntermediateCarrier]
    exact hL
  have hH : A.toFiniteBilinearModule.IsLagrangian H := by
    simpa only [A, H, L.evenSublattice.discriminantQuadraticModule_toFiniteBilinearModule
      L.isEven_evenSublattice] using
      hI.isUnimodular_toIntegralLattice_iff_isLagrangian.mp hM
  have ha (h : H) : A.quadratic (a + h) = A.quadratic a :=
    quadratic_halfCharacteristicDual_add L hw h
  have hqa : A.quadratic a = ZMod.toRatAddCircle 8 (L.integralNorm w : ZMod 8) :=
    quadratic_halfCharacteristicDual L hw
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

private theorem halfCharacteristicDual_mem_primaryComponent_two [L.IsNondegenerate] {w : L}
    (hw : L.IsCharacteristicVector w) :
    (Submodule.Quotient.mk (halfCharacteristicDual L hw) :
      L.evenSublattice.discriminantQuadraticModule L.isEven_evenSublattice) ∈
      AddCommGroup.primaryComponent
        (L.evenSublattice.discriminantQuadraticModule L.isEven_evenSublattice) 2 := by
  refine AddCommGroup.mem_primaryComponent.mpr ⟨2, ?_⟩
  -- View `4 • mk (w / 2)` as a quotient class of `evenSublattice.dualCarrier`.
  change Submodule.Quotient.mk ((4 : ℕ) • halfCharacteristicDual L hw) =
    (0 : L.evenSublattice.dualCarrier ⧸ L.evenSublattice.carrierInDual)
  rw [Submodule.Quotient.mk_eq_zero, L.evenSublattice.mem_carrierInDual_iff,
    L.evenSublattice_carrier]
  refine ⟨(2 : ℤ) • w, L.two_smul_mem_evenSubmodule w, ?_⟩
  rw [map_smul, Submodule.coe_subtype, Submodule.coe_smul_of_tower, halfCharacteristicDual]
  simp only [← Nat.cast_smul_eq_nsmul ℚ, ← Int.cast_smul_eq_zsmul ℚ, smul_smul]
  norm_num

private theorem isLagrangian_comap_primaryComponent_two_evenSublattice [L.IsNondegenerate]
    (hodd : Odd L.discriminant) :
    let A := L.evenSublattice.discriminantQuadraticModule L.isEven_evenSublattice
    let P := AddCommGroup.primaryComponent A 2
    let H : AddSubgroup A := L.evenSublattice.discriminantSubgroup
      (L.toIntermediateCarrier L.evenSublattice_form.symm L.evenSublattice_carrier_le)
    (A.restrict P).toFiniteBilinearModule.IsLagrangian (H.comap P.subtype) ∧
      Nat.card (H.comap P.subtype) ^ 2 = Nat.card (A.restrict P) := by
  have := L.finiteDimensional
  let A := L.evenSublattice.discriminantQuadraticModule L.isEven_evenSublattice
  let P := AddCommGroup.primaryComponent A 2
  let A₂ := A.restrict P
  let I := L.toIntermediateCarrier L.evenSublattice_form.symm L.evenSublattice_carrier_le
  have hILat : I.1.IsLattice ℚ := by
    rw [L.coe_toIntermediateCarrier]
    infer_instance
  have hI := L.isIntegral_toIntermediateCarrier L.evenSublattice_form.symm
    L.evenSublattice_carrier_le
  let H : AddSubgroup A := L.evenSublattice.discriminantSubgroup I
  have hidx_pos : 0 < IntermediateCarrier.index I := IntermediateCarrier.index_pos I
  have hidx_le : IntermediateCarrier.index I ≤ 2 := by
    simpa only [IntermediateCarrier.index_def, I, coe_toIntermediateCarrier] using
      L.relIndex_evenSublattice_le_two
  have hcardH : Nat.card H = IntermediateCarrier.index I :=
    (IntermediateCarrier.index_eq_natCard_discriminantSubgroup I).symm
  have hHP : H ≤ P := fun x hx ↦ by
    have hx0 : Nat.card H • x = 0 :=
      congrArg Subtype.val (card_nsmul_eq_zero' (x := (⟨x, hx⟩ : H)))
    rw [hcardH] at hx0
    rcases (by omega : IntermediateCarrier.index I = 1 ∨ IntermediateCarrier.index I = 2) with
      h1 | h2
    · exact AddCommGroup.mem_primaryComponent.mpr ⟨0, by simpa [h1] using hx0⟩
    · exact AddCommGroup.mem_primaryComponent.mpr ⟨1, by simpa [h2] using hx0⟩
  let H₂ : AddSubgroup A₂ := H.comap P.subtype
  let eH : H₂ ≃ H :=
    { toFun := fun x ↦ ⟨x.1.1, x.2⟩
      invFun := fun y ↦ ⟨⟨y.1, hHP y.2⟩, y.2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  have hcardH₂ : Nat.card H₂ = IntermediateCarrier.index I := (Nat.card_congr eH).trans hcardH
  have hcardA : Nat.card A = L.discriminant * IntermediateCarrier.index I ^ 2 := by
    -- The carrier of `discriminantQuadraticModule` is definitionally `DiscriminantGroup`.
    change Nat.card L.evenSublattice.DiscriminantGroup = _
    rw [L.evenSublattice.natCard_discriminantGroup, ← hI.discriminant_mul_index_sq,
      L.toIntegralLattice_toIntermediateCarrier]
  have hcardA₂ : Nat.card A₂ = 2 ^ (Nat.card A).factorization 2 :=
    TauCeti.AddCommGroup.natCard_primaryComponent A Nat.prime_two
  have hfac0 : L.discriminant.factorization 2 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd hodd.not_two_dvd_nat
  have hsq : Nat.card H₂ ^ 2 = Nat.card A₂ := by
    rw [hcardH₂, hcardA₂, hcardA]
    rcases (by omega : IntermediateCarrier.index I = 1 ∨ IntermediateCarrier.index I = 2) with
      h1 | h2
    · simp [h1, hfac0]
    · rw [h2, Nat.factorization_mul hodd.pos.ne' (by positivity), Finsupp.coe_add, Pi.add_apply,
        hfac0, Nat.factorization_pow, Finsupp.smul_apply, Nat.prime_two.factorization_self]
      norm_num
  have hH_iso : L.evenSublattice.discriminantBilinearModule.IsIsotropic H :=
    (IntermediateCarrier.isIntegral_iff_isIsotropic_discriminantSubgroup I).mp hI
  have hH₂_iso : A₂.toFiniteBilinearModule.IsIsotropic H₂ :=
    A₂.toFiniteBilinearModule.isIsotropic_def.mpr fun x hx y hy ↦
      (L.evenSublattice.discriminantBilinearModule.isIsotropic_def.mp hH_iso) x.1 hx y.1 hy
  refine ⟨FiniteBilinearModule.IsIsotropic.isLagrangian_of_card_sq_eq A₂.toFiniteBilinearModule
    hH₂_iso (A.isNondegenerate_restrict_primaryComponent
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
  have := L.finiteDimensional
  let A := L.evenSublattice.discriminantQuadraticModule L.isEven_evenSublattice
  let P := AddCommGroup.primaryComponent A 2
  let A₂ := A.restrict P
  let H : AddSubgroup A := L.evenSublattice.discriminantSubgroup
    (L.toIntermediateCarrier L.evenSublattice_form.symm L.evenSublattice_carrier_le)
  let H₂ : AddSubgroup A₂ := H.comap P.subtype
  obtain ⟨hH₂_lag, hsq⟩ := isLagrangian_comap_primaryComponent_two_evenSublattice L hodd
  let a₂ : A₂ := ⟨Submodule.Quotient.mk (halfCharacteristicDual L hw),
    halfCharacteristicDual_mem_primaryComponent_two L hw⟩
  have ha₂ (h : H₂) : A₂.quadratic (a₂ + h) = A₂.quadratic a₂ :=
    quadratic_halfCharacteristicDual_add L hw ⟨h.1.1, h.2⟩
  have hqa₂ : A₂.quadratic a₂ = ZMod.toRatAddCircle 8 (L.integralNorm w : ZMod 8) :=
    quadratic_halfCharacteristicDual L hw
  refine FiniteQuadraticModule.gaussSign_eq_of_gaussSum_eq A₂ ?_
  rw [FiniteQuadraticModule.gaussSum_eq_natCard_mul_expCircle_of_bilinear_isLagrangian a₂
    hH₂_lag ha₂, hqa₂, ← hsq, Nat.cast_pow, Real.sqrt_sq (Nat.cast_nonneg _),
    Complex.ofReal_natCast]
  rfl

end TauCeti.IntegralLattice
