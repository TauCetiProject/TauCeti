/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Padics.Complex.Basic
public import TauCeti.RingTheory.Perfectoid.Padic
public import TauCeti.RingTheory.Perfectoid.UniformTilt.Field

/-!
# Checks for the tilt of a perfectoid field

The tilt of `ℂ_p` is a perfectoid field, and the compatible system `p♭ = (p ^ (1 / p ^ n))ₙ` has
norm `‖p♭‖ = ‖p‖ = p⁻¹` in it. The same construction applied to `ℚ_p`, which is not perfectoid,
only produces the trivial norm: `‖x♯‖ = ‖x⁽ⁿ⁾‖ ^ p ^ n` forces the valuation of a nonzero `x♯` to
be divisible by every `p ^ n`. So the tilt of `ℚ_p` is not a nontrivially normed field.
-/

public section

open TauCeti.Huber TauCeti.Perfectoid

namespace TauCeti.Examples.TiltField

variable (p : ℕ) [Fact p.Prime]

example : IsPerfectoidField p (tiltField p ℂ_[p]) := inferInstance

-- A compatible system of `p`-power roots of `p` has norm `p⁻¹` in the tilt of `ℂ_p`.
example : ∃ x : tiltField p ℂ_[p], ‖x‖ = (p : ℝ)⁻¹ := by
  choose r hr using fun y : ℂ_[p] ↦ IsAlgClosed.exists_pow_nat_eq y (Fact.out : p.Prime).pos
  refine ⟨WithAbs.toAbs _ (uniformTilt.mk (fun n ↦ r^[n] p) fun n ↦ ?_), ?_⟩
  · rw [Function.iterate_succ_apply', hr]
  · rw [tiltField.norm_toAbs, uniformTilt.coeff_mk, Function.iterate_zero_apply,
      PadicComplex.norm_p]

local instance : Fact (IsTopologicallyNilpotent (p : ℚ_[p])) :=
  ⟨tendsto_pow_atTop_nhds_zero_of_norm_lt_one Padic.norm_p_lt_one⟩

-- The tilt of `ℚ_p` carries the trivial norm.
example (x : tiltField p ℚ_[p]) (hx : x ≠ 0) : ‖x‖ = 1 := by
  set y := WithAbs.equiv _ x
  have hy (n : ℕ) : uniformTilt.coeff p ℚ_[p] n y ≠ 0 := fun h ↦ hx <| by
    rw [← (WithAbs.equiv _).map_eq_zero_iff, ← uniformTilt.coeff_zero_eq_zero_iff,
      ← uniformTilt.coeff_pow_p_pow y 0 n, zero_add, h, zero_pow (pow_ne_zero _ (NeZero.ne p))]
  -- the valuation of `y♯` is divisible by every `p ^ n`, hence vanishes
  have hv : (uniformTilt.coeff p ℚ_[p] 0 y).valuation = 0 := by
    set k := (uniformTilt.coeff p ℚ_[p] 0 y).valuation.natAbs
    refine Int.eq_zero_of_dvd_of_natAbs_lt_natAbs (d := (p : ℤ) ^ k)
      ⟨(uniformTilt.coeff p ℚ_[p] k y).valuation, ?_⟩ ?_
    · rw [← uniformTilt.coeff_pow_p_pow y 0 k, zero_add, Padic.valuation_pow]
      push_cast
      ring
    · rw [Int.natAbs_pow, Int.natAbs_natCast]
      exact Nat.lt_pow_self (Fact.out : p.Prime).one_lt
  rw [tiltField.norm_def, Padic.norm_eq_zpow_neg_valuation (hy 0), hv, neg_zero, zpow_zero]

end TauCeti.Examples.TiltField
