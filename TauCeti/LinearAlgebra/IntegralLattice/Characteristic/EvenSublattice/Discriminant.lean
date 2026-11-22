/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.FiniteBilinearModule.Primary.Component
public import TauCeti.LinearAlgebra.IntegralLattice.Characteristic.Basic
public import TauCeti.LinearAlgebra.IntegralLattice.Characteristic.EvenSublattice.Basic
public import TauCeti.LinearAlgebra.IntegralLattice.Discriminant.Quadratic
public import TauCeti.LinearAlgebra.IntegralLattice.Overlattice.Isotropic
import TauCeti.Algebra.Group.Primary.Card
import TauCeti.LinearAlgebra.IntegralLattice.Overlattice.Index

/-!
# The `2`-primary discriminant module of the even sublattice

For a nondegenerate lattice `L` of odd discriminant, `N = L.evenSublattice` has index
`[L : N] ∈ {1, 2}`, discriminant `L.discriminant * [L : N]²`, and `(A_N)_2` of order `[L : N]²`,
in which `L / N` is a bilinear Lagrangian. Any characteristic vector `w` of `L` gives
`halfCharacteristicDual` (`w / 2 ∈ Nᵛ`) whose class lies in `(A_N)_2` with constant value
`w² / 8` on its `L / N`-coset.

## Main results

* `TauCeti.IntegralLattice.natCard_primaryComponent_two_evenSublattice`
* `TauCeti.IntegralLattice.isLagrangian_evenSublattice_primaryComponent_two`
* `TauCeti.IntegralLattice.halfCharacteristicDual`,
  `TauCeti.IntegralLattice.discriminantQuadraticMap_mk_halfCharacteristicDual`,
  `TauCeti.IntegralLattice.discriminantQuadraticMap_mk_halfCharacteristicDual_add`,
  `TauCeti.IntegralLattice.halfCharacteristicDual_mk_mem_primaryComponent_two`
-/

public section

namespace TauCeti.IntegralLattice

universe u
variable {V : Type u} [AddCommGroup V] [Module ℚ V] (L : IntegralLattice V)

/-- For a nondegenerate lattice `L` of odd discriminant, the `2`-primary component of the
discriminant group of `L.evenSublattice` has cardinality `[L : L.evenSublattice]²`. -/
theorem natCard_primaryComponent_two_evenSublattice [L.IsNondegenerate]
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

/-- For a nondegenerate lattice `L` of odd discriminant, the gluing subgroup `L / L.evenSublattice`
is a bilinear Lagrangian in the `2`-primary component of the discriminant quadratic module of
`L.evenSublattice`. -/
theorem isLagrangian_evenSublattice_primaryComponent_two [L.IsNondegenerate]
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
    · rw [h1, one_nsmul] at hkill; simp [hkill]
    · rwa [h2] at hkill
  have hcard_H2 : Nat.card H₂ = N.carrier.toAddSubgroup.relIndex L.carrier.toAddSubgroup :=
    (Nat.card_congr (AddSubgroup.addSubgroupOfEquivOfLe hH_le).toEquiv).trans hcard_H
  have hH2_iso : A₂.toFiniteBilinearModule.IsIsotropic H₂ :=
    A₂.toFiniteBilinearModule.isIsotropic_def.mpr fun x hx y hy ↦
      (A.restrict_pairing _ x y).trans <|
        (N.discriminantQuadraticModule_pairing L.isEven_evenSublattice x.val y.val).trans <|
          (IntermediateCarrier.isIntegral_iff_forall_discriminantPairing_eq_zero M₀).mp hI
            x.val hx y.val hy
  exact FiniteBilinearModule.IsIsotropic.isLagrangian_of_card_sq_eq A₂.toFiniteBilinearModule
    hH2_iso
    (A.isNondegenerate_restrict_primaryComponent
      (N.isNondegenerate_discriminantQuadraticModule L.isEven_evenSublattice) Nat.prime_two)
    (by
      rw [hcard_H2, ← L.natCard_primaryComponent_two_evenSublattice hodd]
      exact (A.natCard_restrict _).symm)

/-- The half-characteristic dual vector `w / 2` in `L.evenSublattice.dualCarrier` associated with a
characteristic vector `w` of `L`. -/
@[expose] noncomputable def halfCharacteristicDual {w : L} (hw : L.IsCharacteristicVector w) :
    L.evenSublattice.dualCarrier :=
  ⟨(1 / 2 : ℚ) • (w : V), by
    rw [LinearMap.BilinForm.mem_dualSubmodule]
    intro y hy
    let yL : L := ⟨y, L.evenSublattice_carrier_le hy⟩
    have hp := (L.isCharacteristicVector_iff w).mp hw yL
    obtain ⟨k, hk⟩ := Int.modEq_zero_iff_dvd.mp (hp.trans (Int.modEq_zero_iff_dvd.mpr
      (even_iff_two_dvd.mp ((L.mem_evenSublattice_carrier_iff yL).mp hy))))
    refine Submodule.mem_one.mpr ⟨k, ?_⟩
    rw [eq_intCast, L.evenSublattice_form, map_smul, LinearMap.smul_apply, smul_eq_mul,
      ← L.integralForm_cast w yL, hk]
    push_cast; ring⟩

/-- The ambient rational vector underlying `L.halfCharacteristicDual hw` is `(1 / 2 : ℚ) • w`. -/
theorem coe_halfCharacteristicDual {w : L} (hw : L.IsCharacteristicVector w) :
    (L.halfCharacteristicDual hw : V) = (1 / 2 : ℚ) • (w : V) := rfl

/-- The discriminant quadratic value of `L.evenSublattice` at `[w / 2]` is `w² / 8 mod ℤ`. -/
theorem discriminantQuadraticMap_mk_halfCharacteristicDual {w : L}
    (hw : L.IsCharacteristicVector w) :
    L.evenSublattice.discriminantQuadraticMap L.isEven_evenSublattice
        (Submodule.Quotient.mk (L.halfCharacteristicDual hw)) =
      ZMod.toRatAddCircle 8 (L.integralNorm w : ZMod 8) := by
  rw [discriminantQuadraticMap_mk, L.evenSublattice_form, ZMod.toRatAddCircle_intCast,
    L.integralNorm_cast, L.norm_apply]
  simp only [coe_halfCharacteristicDual, map_smul, LinearMap.smul_apply, smul_eq_mul]
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

/-- Translating `[w / 2]` by an element of the gluing subgroup `L / L.evenSublattice` leaves
`q_{L.evenSublattice}` unchanged. -/
theorem discriminantQuadraticMap_mk_halfCharacteristicDual_add {w : L}
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

/-- The discriminant class `[w / 2]` lies in the `2`-primary component of
`L.evenSublattice.DiscriminantGroup`. -/
theorem halfCharacteristicDual_mk_mem_primaryComponent_two {w : L}
    (hw : L.IsCharacteristicVector w) :
    Submodule.Quotient.mk (L.halfCharacteristicDual hw) ∈
      AddCommGroup.primaryComponent L.evenSublattice.DiscriminantGroup 2 := by
  refine AddCommGroup.mem_primaryComponent.mpr ⟨2, ?_⟩
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero,
    L.evenSublattice.mem_carrierInDual_iff]
  have hval : (((2 ^ 2 : ℕ) • L.halfCharacteristicDual hw : L.evenSublattice.dualCarrier) : V) =
      (((2 : ℤ) • w : L) : V) := by
    simp only [SetLike.val_smul, coe_halfCharacteristicDual, Submodule.coe_smul_of_tower]
    rw [← Nat.cast_smul_eq_nsmul ℚ (2 ^ 2), smul_smul]; norm_num
    rw [two_smul ℚ (w : V), two_zsmul]
  rw [hval, L.evenSublattice_carrier]
  exact Submodule.mem_map_of_mem (L.two_smul_mem_evenSubmodule w)

end TauCeti.IntegralLattice
