/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import TauCeti.FieldTheory.FunctionField.RiemannRoch.Basic

/-!
# The constants of `ℂ(x)` over `ℝ`

The rational function field `ℂ(x)` is a function field over `ℝ`, but its full constant field is
`ℂ`. Consequently its zero-divisor Riemann–Roch space has real dimension two. This concrete
example shows why the equality `ℓ(0) = 1` requires the exact-constants hypothesis.
-/

public section

namespace TauCeti

open AlgebraicGeometry

namespace Divisor

/-- The zero-divisor Riemann–Roch space of `ℂ(x)` has real dimension two. -/
@[simp]
theorem dim_zero_real_ratFunc_complex :
    dim (0 : Divisor ℝ (RatFunc ℂ)) = 2 := by
  have hF : IsFunctionField ℝ (RatFunc ℂ) :=
    (IsFunctionField.ratFunc ℂ).of_finiteDimensional
  have hc : algebraicClosure ℝ (RatFunc ℂ) =
      (⊥ : IntermediateField ℂ (RatFunc ℂ)).restrictScalars ℝ :=
    hF.algebraicClosure_eq_restrictScalars_bot
      (IsFunctionField.ratFunc ℂ) (isIntegrallyClosedIn_ratFunc)
  rw [dim_zero hF, hc]
  let T := (⊥ : IntermediateField ℂ (RatFunc ℂ)).restrictScalars ℝ
  -- Identify the restricted field with the original bottom field as real vector spaces.
  let e : T ≃ₗ[ℝ] (⊥ : IntermediateField ℂ (RatFunc ℂ)) :=
    { toFun := fun x => ⟨x.1, by
        simpa only [T, IntermediateField.mem_restrictScalars] using x.property⟩
      invFun := fun x => ⟨x.1, by
        simpa only [T, IntermediateField.mem_restrictScalars] using x.property⟩
      left_inv := fun x => Subtype.ext rfl
      right_inv := fun x => Subtype.ext rfl
      map_add' := fun _ _ => Subtype.ext rfl
      map_smul' := by
        intro r x
        apply Subtype.ext
        simp only [IntermediateField.coe_smul, Algebra.smul_def,
          IntermediateField.coe_mul, IntermediateField.coe_algebraMap_apply,
          RingHom.id_apply]
        change (algebraMap ℝ (RatFunc ℂ) r) * (x : RatFunc ℂ) =
          (r : ℂ) • (x : RatFunc ℂ)
        rw [Algebra.smul_def, IsScalarTower.algebraMap_apply ℝ ℂ (RatFunc ℂ)]
        simp }
  exact e.finrank_eq.trans
    (((IntermediateField.botEquiv ℂ (RatFunc ℂ)).toLinearEquiv.restrictScalars ℝ).finrank_eq.trans
      Complex.finrank_real_complex)

end Divisor

end TauCeti
