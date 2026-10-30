/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Padics.PadicNumbers
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Expand

/-!
# The Tate algebra at radius `√p` over `ℚ_p`

The radius `√p` is not the norm of an element of `ℚ_p`, but `‖p‖ * √p ^ 2 = 1`. So
`Y ↦ p X²` is an injective finite algebra map from the unit-radius Tate algebra `ℚ_p⟨Y⟩` to the
restricted series `ℚ_p{X/√p}`, which is generated over it by the monomials `1` and `X`.
-/

public section

open MvPowerSeries TauCeti.MvPowerSeries

variable (p : ℕ) [hp : Fact p.Prime]

/-- The radius `√p` is positive. -/
local instance : Fact (0 < √p) :=
  ⟨Real.sqrt_pos.mpr (Nat.cast_pos.mpr hp.out.pos)⟩

-- `ℚ_p{X/√p}` is finite over `ℚ_p⟨Y⟩` through an injective algebra map.
example : ∃ φ : IsRestricted.subring (R := ℚ_[p]) (fun _ : Unit ↦ (1 : ℝ)) →ₐ[ℚ_[p]]
    IsRestricted.subring (R := ℚ_[p]) (fun _ : Unit ↦ √p),
      Function.Injective φ ∧ φ.Finite := by
  refine exists_injective_finite_algHom_of_norm_mul_pow_eq_one fun _ ↦ ⟨2, two_ne_zero, p, ?_⟩
  rw [Padic.norm_p, Real.sq_sqrt (Nat.cast_nonneg p),
    inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hp.out.ne_zero)]

-- The presenting map sends `Y` to `p X²`.
example :
    restrictedRescaleExpand 2 two_ne_zero
        (fun _ : Unit ↦ Units.mk0 (p : ℚ_[p]) (Nat.cast_ne_zero.mpr hp.out.ne_zero))
        (fun _ ↦ (TauCeti.isNormMulUnit_iff_isUnit _).mpr (Units.isUnit _))
        (fun _ ↦ by
          rw [Units.val_mk0, Padic.norm_p, Real.sq_sqrt (Nat.cast_nonneg p),
            inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hp.out.ne_zero)])
        (⟨X (), isRestricted_X _ ()⟩ : IsRestricted.subring (R := ℚ_[p]) fun _ : Unit ↦ 1) =
      algebraMap ℚ_[p] _ (p : ℚ_[p]) *
        (⟨X (), isRestricted_X _ ()⟩ : IsRestricted.subring (R := ℚ_[p]) fun _ : Unit ↦ √p) ^ 2 :=
  restrictedRescaleExpand_X _ _ _ _ _ ()
