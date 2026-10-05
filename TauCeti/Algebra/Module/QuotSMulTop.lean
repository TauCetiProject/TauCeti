/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.QuotSMulTop
public import Mathlib.GroupTheory.FiniteAbelian.Basic
import TauCeti.Algebra.Module.Torsion.Snake

/-!
# Scalar quotients and base change

The quotient of a finitely generated abelian group by a nonzero integer multiple is finite.
This supplies finiteness for reductions of integral representations without choosing a basis.
If a scalar vanishes in a coefficient algebra, quotienting by it before extending scalars does
not change the resulting module.
-/

public section

namespace TauCeti

open TensorProduct
open scoped Pointwise

/-- Tensoring scalar multiplication gives the zero map when the scalar vanishes in the
coefficient algebra. -/
theorem lTensor_toLinearMap_eq_zero_of_algebraMap_eq_zero {R A M : Type*}
    [CommSemiring R] [CommSemiring A] [Algebra R A] [AddCommMonoid M] [Module R M]
    (r : R) (hr : algebraMap R A r = 0) : (DistribSMul.toLinearMap R M r).lTensor A = 0 := by
  ext a x
  simp only [AlgebraTensorModule.curry_apply, TensorProduct.curry_apply,
    LinearMap.restrictScalars_apply, LinearMap.zero_apply,
    LinearMap.lTensor_tmul, DistribSMul.toLinearMap_apply]
  rw [← TensorProduct.smul_tmul, ← IsScalarTower.algebraMap_smul A r a]
  simp [hr]

/-- The projection onto a scalar quotient becomes bijective after tensoring with an algebra
in which the scalar vanishes. -/
theorem bijective_lTensor_mkQ_smul_top_of_algebraMap_eq_zero {R A M : Type*}
    [CommRing R] [CommRing A] [Algebra R A] [AddCommGroup M] [Module R M]
    (r : R) (hr : algebraMap R A r = 0) :
    Function.Bijective ((r • (⊤ : Submodule R M)).mkQ.lTensor A) := by
  refine ⟨?_, LinearMap.lTensor_surjective A (Submodule.mkQ_surjective _)⟩
  have hex := lTensor_exact A (exact_toLinearMap_mkQ r M)
    (Submodule.mkQ_surjective (r • (⊤ : Submodule R M)))
  rw [lTensor_toLinearMap_eq_zero_of_algebraMap_eq_zero r hr] at hex
  exact (LinearMap.exact_zero_iff_injective _ _).mp hex

/-- A finitely generated abelian group modulo a nonzero integer multiple is finite. -/
instance instFiniteQuotSMulTopInt (M : Type*) [AddCommGroup M] [Module ℤ M] [Module.Finite ℤ M]
    (r : ℤ) [NeZero r] : Finite (QuotSMulTop r M) := by
  -- The structural quotient action agrees with the canonical integer action only
  -- propositionally; select it so finite generation and the annihilator use the same action.
  let : Module ℤ (QuotSMulTop r M) := Submodule.Quotient.module _
  exact Module.finite_of_fg_torsion _ fun x =>
    ⟨⟨r, mem_nonZeroDivisors_of_ne_zero (NeZero.ne r)⟩,
      Module.mem_annihilator.mp (QuotSMulTop.mem_annihilator M r) x⟩

end TauCeti
