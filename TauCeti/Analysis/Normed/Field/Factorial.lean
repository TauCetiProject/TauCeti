/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Ring.Ultra
public import TauCeti.NumberTheory.Padics.Factorial

/-!
# Factorial bounds without a normalization of the prime norm

In an ultrametric field of characteristic zero, a prime of norm less than one determines
the norm of every nonzero natural number. Legendre's bound consequently gives
`‖p‖ ^ (n / (p - 1)) ≤ ‖n!‖`, with no normalization of `‖p‖`.
These estimates control factorial denominators in divided powers.

The bound on the multiplicity of `p` in `n!` is Legendre's formula, used here in the form
`TauCeti.multiplicity_factorial_le_div`.
-/

public section

namespace TauCeti

variable {C : Type*} [NormedField C] [IsUltrametricDist C] [CharZero C]
  {p : ℕ}

omit [CharZero C] in
/-- A prime of norm less than one determines the norm of every nonzero natural number. -/
theorem norm_natCast_eq_pow_multiplicity (hp : p.Prime) (hpC : ‖(p : C)‖ < 1)
    {m : ℕ} (hm : m ≠ 0) : ‖(m : C)‖ = ‖(p : C)‖ ^ multiplicity p m := by
  have hfin : FiniteMultiplicity p m :=
    Nat.finiteMultiplicity_iff.mpr ⟨hp.ne_one, Nat.pos_of_ne_zero hm⟩
  obtain ⟨u, hu, hpu⟩ := hfin.exists_eq_pow_mul_and_not_dvd
  conv_lhs => rw [hu]
  rw [Nat.cast_mul, Nat.cast_pow, norm_mul, norm_pow,
    IsUltrametricDist.norm_natCast_eq_one_of_coprime hpC (hp.coprime_iff_not_dvd.mpr hpu),
    mul_one]

/-- Legendre's lower bound for the norm of a factorial in an arbitrarily normalized
ultrametric field. -/
theorem rpow_div_le_norm_factorial (hp : p.Prime) (hpC : ‖(p : C)‖ < 1) (m : ℕ) :
    ‖(p : C)‖ ^ ((m : ℝ) / ((p : ℝ) - 1)) ≤ ‖(m.factorial : C)‖ := by
  have : Fact p.Prime := ⟨hp⟩
  rw [norm_natCast_eq_pow_multiplicity hp hpC (Nat.factorial_ne_zero m),
    ← Real.rpow_natCast]
  exact Real.rpow_le_rpow_of_exponent_ge (norm_pos_iff.mpr (Nat.cast_ne_zero.mpr hp.ne_zero))
    hpC.le (multiplicity_factorial_le_div p m)

/-- Inverse factorials grow at most geometrically with base `‖p‖ ^ (-(p - 1)⁻¹)`. -/
theorem norm_inv_factorial_le_prime_norm (hp : p.Prime) (hpC : ‖(p : C)‖ < 1) (m : ℕ) :
    ‖(m.factorial : C)⁻¹‖ ≤ (‖(p : C)‖ ^ (-((p : ℝ) - 1)⁻¹)) ^ m := by
  have hp0 : 0 < ‖(p : C)‖ := norm_pos_iff.mpr (Nat.cast_ne_zero.mpr hp.ne_zero)
  rw [norm_inv]
  calc
    ‖(m.factorial : C)‖⁻¹ ≤ (‖(p : C)‖ ^ ((m : ℝ) / ((p : ℝ) - 1)))⁻¹ :=
      inv_anti₀ (Real.rpow_pos_of_pos hp0 _) (rpow_div_le_norm_factorial hp hpC m)
    _ = _ := by
      rw [← Real.rpow_neg hp0.le, ← Real.rpow_natCast, ← Real.rpow_mul hp0.le]
      congr 1
      ring

end TauCeti
