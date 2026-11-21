/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.FiniteBilinearModule.Primary.Component
public import TauCeti.LinearAlgebra.IntegralLattice.Characteristic.EvenSublattice.Basic
public import TauCeti.LinearAlgebra.IntegralLattice.Discriminant.Quadratic
public import TauCeti.LinearAlgebra.IntegralLattice.Overlattice.Isotropic
import TauCeti.Algebra.Group.Primary.Card
import TauCeti.LinearAlgebra.IntegralLattice.Overlattice.Index

/-!
# The `2`-primary discriminant module of the even sublattice

For a nondegenerate integral lattice `L` of odd discriminant, the canonical even sublattice
`N = L.evenSublattice` has index `[L : N] ∈ {1, 2}` and discriminant `L.discriminant * [L : N]²`.
Consequently, the `2`-primary component `(A_N)_2` of the discriminant module of `N` has order
`[L : N]²`, and the gluing subgroup `L / N` embeds into `(A_N)_2` as an isotropic subgroup of order
`[L : N]`, hence as a bilinear Lagrangian.

## Main results

* `TauCeti.IntegralLattice.natCard_primaryComponent_two_evenSublattice`: at odd discriminant, the
  cardinality `Nat.card (AddCommGroup.primaryComponent L.evenSublattice.DiscriminantGroup 2)`
  equals `[L : L.evenSublattice]²`.
* `TauCeti.IntegralLattice.isLagrangian_evenSublattice_primaryComponent_two`: at odd discriminant,
  the gluing subgroup `L / L.evenSublattice` is a bilinear Lagrangian in the `2`-primary component
  of the discriminant quadratic module of `L.evenSublattice`.
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
    · rw [h1, one_nsmul] at hkill
      simp [hkill]
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

end TauCeti.IntegralLattice
