/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.Characteristic.Basic
public import TauCeti.LinearAlgebra.IntegralLattice.Gram
import TauCeti.Data.Int.MulPred
import TauCeti.LinearAlgebra.IntegralLattice.Discriminant.Cardinality

/-!
# Characteristic vectors in lattices of odd discriminant

Every integral lattice of odd discriminant `d = |det L|` has a characteristic vector. Because `d`
is positive, `L` is nondegenerate and `d = #(Lᵛ / L)` annihilates the discriminant group; scaling
the dual vector that represents `bᵢ ↦ B(bᵢ, bᵢ)` on a `ℤ`-basis `b` by the odd integer `d` lands in
`L` and preserves every pairing modulo two.

## Main results

* `TauCeti.IntegralLattice.exists_isCharacteristicVector_of_odd_discriminant`: every integral
  lattice of odd discriminant has a characteristic vector.

## References

* J. Milnor and D. Husemoller, *Symmetric Bilinear Forms*, Appendix 4.
* V. V. Nikulin, *Integral symmetric bilinear forms and some of their applications*, §1.16.
-/

public section

namespace TauCeti.IntegralLattice

universe u

variable {V : Type u} [AddCommGroup V] [Module ℚ V]

/-- **Every integral lattice of odd discriminant has a characteristic vector.** Scaling the dual
vector that pairs with a chosen basis `b` via `bᵢ ↦ B(bᵢ, bᵢ)` by the odd discriminant `d = #(Lᵛ/L)`
lands in `L` and leaves all pairings unchanged modulo two. -/
theorem exists_isCharacteristicVector_of_odd_discriminant (L : IntegralLattice V)
    (hL : Odd L.discriminant) :
    ∃ w : L, L.IsCharacteristicVector w := by
  classical
  have : L.IsNondegenerate := ⟨L.discriminant_pos_iff.mp hL.pos⟩
  let b := Module.finBasis ℤ L
  let y : L.dualCarrier := L.dualPairingEquiv.symm (b.constr ℤ fun i ↦ L.integralNorm (b i))
  have hy_mem : (L.discriminant • y : L.dualCarrier) ∈ L.carrierInDual := by
    rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_smul, ← L.natCard_discriminantGroup]
    exact card_nsmul_eq_zero'
  let w : L := ⟨(L.discriminant • y : L.dualCarrier), (L.mem_carrierInDual_iff _).mp hy_mem⟩
  refine ⟨w, (L.isCharacteristicVector_iff_isCharacteristic w).mpr
    ((L.isSymm_integralForm.isCharacteristic_iff_forall_basis Int.two_dvd_sq_sub_self b).mpr
      fun i ↦ ?_)⟩
  have hform : L.integralForm w (b i) = (L.discriminant : ℤ) * L.integralNorm (b i) := by
    apply Int.cast_injective (α := ℚ)
    have hyb : L.form (y : V) (b i) = (L.integralNorm (b i) : ℚ) := by
      rw [← L.dualPairingEquiv_cast y (b i), LinearEquiv.apply_symm_apply,
        Module.Basis.constr_basis]
    rw [L.integralForm_cast]
    simp only [w]
    rw [← natCast_zsmul, SetLike.val_smul, natCast_zsmul, map_nsmul, LinearMap.smul_apply, hyb,
      nsmul_eq_mul, Int.cast_mul, Int.cast_natCast]
  obtain ⟨k, hk⟩ := hL
  rw [hform, ← L.integralNorm_apply, hk]
  exact ⟨k * L.integralNorm (b i), by push_cast; ring⟩

end TauCeti.IntegralLattice
