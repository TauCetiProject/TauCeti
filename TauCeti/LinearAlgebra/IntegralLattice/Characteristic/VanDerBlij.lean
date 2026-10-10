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
import TauCeti.LinearAlgebra.IntegralLattice.Overlattice.Metabolic

/-!
# Van der Blij's characteristic-norm congruence

In a nondegenerate unimodular integral lattice, every characteristic vector has integral norm
congruent to the signature difference modulo eight. The statement applies to all signatures
and to both even and odd lattices.

For the canonical even sublattice `N`, the original lattice determines a bilinear Lagrangian
`H = L/N` in the discriminant form of `N`. A characteristic vector `w` gives a dual vector
`w/2`; the quadratic form is constant on its class plus `H`, with value `w²/8`. Character
averaging therefore evaluates the normalized Gauss sum as `expCircle (w²/8)`. Milgram's
theorem identifies the same phase with the signature of `N`, which is the signature of `L`.
When `L` is even and `w = 0`, the congruence gives divisibility of the signature by eight.

## References

* F. van der Blij, *An invariant of quadratic forms mod 8*, Indag. Math. 21 (1959), 291–293.
* J. Milnor and D. Husemoller, *Symmetric Bilinear Forms*, Appendix 4.
-/

public section

open scoped Real

namespace TauCeti.IntegralLattice

universe u
variable {V : Type u} [AddCommGroup V] [Module ℚ V] (L : IntegralLattice V)

private def originalCarrierIntermediate : L.evenSublattice.IntermediateCarrier := by
  refine ⟨L.carrier, L.evenSublattice_carrier_le, ?_⟩
  intro x hx
  rw [LinearMap.BilinForm.mem_dualSubmodule]
  intro y hy
  rw [L.evenSublattice_form]
  exact L.le_dual hx y (L.evenSublattice_carrier_le hy)

private theorem originalCarrier_isIntegral :
    IntermediateCarrier.IsIntegral (originalCarrierIntermediate L) := by
  rw [IntermediateCarrier.isIntegral_def]
  intro x hx y hy
  rw [L.evenSublattice_form]
  exact L.le_dual hx y hy

private theorem originalCarrier_toIntegralLattice [L.IsNondegenerate] :
    (originalCarrier_isIntegral L).toIntegralLattice = L := by
  apply IntegralLattice.ext
  · exact (originalCarrier_isIntegral L).toIntegralLattice_carrier
  · exact (originalCarrier_isIntegral L).toIntegralLattice_form.trans L.evenSublattice_form

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
    (h : L.evenSublattice.discriminantSubgroup (originalCarrierIntermediate L)) :
    L.evenSublattice.discriminantQuadraticMap L.isEven_evenSublattice
        ((Submodule.Quotient.mk (halfCharacteristicDual L hw) :
          L.evenSublattice.DiscriminantGroup) + h) =
      L.evenSublattice.discriminantQuadraticMap L.isEven_evenSublattice
        (Submodule.Quotient.mk (halfCharacteristicDual L hw)) := by
  obtain ⟨x, hx⟩ := h
  induction x using Submodule.Quotient.induction_on with
  | _ y =>
    have hy : (y : V) ∈ L.carrier :=
      (L.evenSublattice.mk_mem_discriminantSubgroup_iff (originalCarrierIntermediate L) y).mp hx
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
  let H : AddSubgroup A :=
    L.evenSublattice.discriminantSubgroup (originalCarrierIntermediate L)
  let a : A := Submodule.Quotient.mk (halfCharacteristicDual L hw)
  have hM : (originalCarrier_isIntegral L).toIntegralLattice.IsUnimodular := by
    rw [originalCarrier_toIntegralLattice L]
    exact hL
  have hH : A.toFiniteBilinearModule.IsLagrangian H := by
    simpa only [A, H, L.evenSublattice.discriminantQuadraticModule_toFiniteBilinearModule
      L.isEven_evenSublattice] using
      (originalCarrier_isIntegral L).isUnimodular_toIntegralLattice_iff_isLagrangian.mp hM
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

/-- **Van der Blij's congruence:** the signature difference of a nondegenerate unimodular
integral lattice is congruent modulo eight to the norm of any characteristic vector. -/
theorem vanDerBlij [L.IsNondegenerate] (hL : L.IsUnimodular) {w : L}
    (hw : L.IsCharacteristicVector w) :
    ((L.sigPos : ℤ) - L.sigNeg) ≡ L.integralNorm w [ZMOD 8] := by
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

end TauCeti.IntegralLattice
