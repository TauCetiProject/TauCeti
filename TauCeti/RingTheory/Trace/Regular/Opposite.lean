/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Trace.Regular
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.LinearAlgebra.Basis.MulOpposite

/-!
# Regular traces on the opposite algebra

The nondegenerate regular trace pairing identifies right multiplication with the transpose of
left multiplication. Consequently the opposite algebra has the same regular trace form. This is
the discriminant comparison used in the last paragraph of §3 of Masser and Wüstholz,
*Factorization estimates for abelian varieties*.
-/

public section

open LinearMap MulOpposite

namespace Algebra

variable {K A : Type*} [Field K] [Ring A] [Algebra K A] [FiniteDimensional K A]

/-- Left multiplication on the opposite algebra has the same trace as left multiplication on the
original algebra when the regular trace form is nondegenerate. -/
@[simp↓]
theorem trace_lmul_op (hB : (regularTraceForm K A).Nondegenerate) (a : A) :
    LinearMap.trace K Aᵐᵒᵖ (lmul K Aᵐᵒᵖ (op a)) = LinearMap.trace K A (lmul K A a) := by
  let e := (regularTraceForm K A).toDual hB
  let eop := (opLinearEquiv K : A ≃ₗ[K] Aᵐᵒᵖ).symm.trans e
  have heop (x : Aᵐᵒᵖ) : eop x = e (unop x) := by simp [eop]
  -- The regular trace pairs right multiplication with left multiplication by associativity.
  have hadj (x y : A) : e (x * a) y = e x (a * y) := by
    simp [e, BilinForm.toDual_def hB, mul_assoc]
  have hc : eop.conj (lmul K Aᵐᵒᵖ (op a)) = Module.Dual.transpose (lmul K A a) := by
    ext f y
    obtain ⟨x, rfl⟩ := eop.surjective f
    rw [LinearEquiv.conj_apply_apply, eop.symm_apply_apply]
    simpa [heop, Module.Dual.transpose_apply, Algebra.coe_lmul_eq_mul, mul_apply', unop_mul]
      using hadj (unop x) y
  rw [← trace_conj' _ eop, hc, trace_transpose']

/-- Passing to the opposite algebra preserves the regular trace form. -/
@[simp high]
theorem regularTraceForm_op (hB : (regularTraceForm K A).Nondegenerate) (x y : A) :
    regularTraceForm K Aᵐᵒᵖ (op x) (op y) = regularTraceForm K A x y := by
  rw [regularTraceForm_apply, ← op_mul, trace_lmul_op hB,
    ← regularTraceForm_apply]
  exact (regularTraceForm_isSymm K A).eq y x

end Algebra
