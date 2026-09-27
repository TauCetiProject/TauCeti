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
theorem dim_zero_real_ratFunc_complex :
    dim (0 : Divisor ℝ (RatFunc ℂ)) = 2 := by
  have hF : IsFunctionField ℝ (RatFunc ℂ) :=
    (IsFunctionField.ratFunc ℂ).of_finiteDimensional
  have hc : algebraicClosure ℝ (RatFunc ℂ) =
      (⊥ : IntermediateField ℂ (RatFunc ℂ)).restrictScalars ℝ :=
    hF.algebraicClosure_eq_restrictScalars_bot
      (IsFunctionField.ratFunc ℂ) (isIntegrallyClosedIn_ratFunc)
  rw [dim_zero hF, hc]
  -- The restricted bottom intermediate field has the same carrier as `ℂ`.
  let T := (⊥ : IntermediateField ℂ (RatFunc ℂ)).restrictScalars ℝ
  let f : ℂ →ₗ[ℝ] T :=
    { toFun := fun c => ⟨algebraMap ℂ (RatFunc ℂ) c, by
          simpa only [T, IntermediateField.mem_restrictScalars] using
            (IntermediateField.algebraMap_mem (⊥ : IntermediateField ℂ (RatFunc ℂ)) c)⟩
      map_add' := by
        intro a b
        apply Subtype.ext
        exact map_add (algebraMap ℂ (RatFunc ℂ)) a b
      map_smul' := by
        intro a b
        apply Subtype.ext
        simp only [Algebra.smul_def, map_mul, IntermediateField.coe_mul, RingHom.id_apply]
        exact congrArg (· * (algebraMap ℂ (RatFunc ℂ)) b)
          (calc
            (algebraMap ℂ (RatFunc ℂ)) ((algebraMap ℝ ℂ) a) =
                (algebraMap ℝ (RatFunc ℂ)) a :=
              (IsScalarTower.algebraMap_apply ℝ ℂ (RatFunc ℂ) a).symm
            _ = ((algebraMap ℝ T) a : RatFunc ℂ) := by
              rw [IsScalarTower.algebraMap_apply ℝ T (RatFunc ℂ) a,
                IntermediateField.algebraMap_apply]) }
  have hf : Function.Bijective f := by
    constructor
    · intro a b hab
      exact (algebraMap ℂ (RatFunc ℂ)).injective (congrArg Subtype.val hab)
    · intro x
      obtain ⟨c, hc⟩ := IntermediateField.mem_bot.mp
        (by simpa only [T, IntermediateField.mem_restrictScalars] using x.property)
      exact ⟨c, Subtype.ext hc⟩
  exact (LinearEquiv.ofBijective f hf).finrank_eq.symm.trans Complex.finrank_real_complex

end Divisor

end TauCeti
