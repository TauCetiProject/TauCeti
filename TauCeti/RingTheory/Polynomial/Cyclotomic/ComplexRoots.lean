/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
public import TauCeti.RingTheory.RootsOfUnity.Complex.Exp
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import TauCeti.RingTheory.RootsOfUnity.NthRoots

/-!
# Complex root multisets of cyclotomic and related polynomials

The complex roots of `Φ_h` are `exp (2πi e / h)` for `e < h` coprime to `h`, and are simple. The
complex root multisets of `1 + X + ⋯ + X ^ (n - 1)` and `X ^ n + 1` are likewise given in
exponential form from a primitive complex root of unity.
-/

public section

namespace Polynomial

/-- The complex roots of `Φ_h` are the `exp (2πi e / h)` for `e < h` coprime to `h`. For `h = 0` the
polynomial is `1`, which has no roots, and the right side is empty. -/
theorem mem_roots_cyclotomic_complex_iff {h : ℕ} (ζ : ℂ) :
    ζ ∈ (cyclotomic h ℂ).roots ↔
      ∃ e ∈ (List.range h).filter (Nat.Coprime · h),
        Complex.exp (2 * Real.pi * Complex.I * (e / h)) = ζ := by
  rcases eq_or_ne h 0 with rfl | hh
  · simp
  have : NeZero (h : ℂ) := ⟨Nat.cast_ne_zero.2 hh⟩
  rw [cyclotomic.roots_eq_primitiveRoots_val, Finset.mem_val,
    mem_primitiveRoots (Nat.pos_of_ne_zero hh), Complex.isPrimitiveRoot_iff ζ h hh]
  simp only [List.mem_filter, List.mem_range, decide_eq_true_eq]
  constructor
  · rintro ⟨i, hi, hc, h⟩; exact ⟨i, ⟨hi, hc⟩, h⟩
  · rintro ⟨i, ⟨hi, hc⟩, h⟩; exact ⟨i, hi, hc, h⟩

/-- The complex roots of `Φ_h` are simple, also for `h = 0`, where there are none. -/
theorem nodup_roots_cyclotomic_complex (h : ℕ) : (cyclotomic h ℂ).roots.Nodup := by
  rcases eq_or_ne h 0 with rfl | hh
  · simp
  have : NeZero (h : ℂ) := ⟨Nat.cast_ne_zero.2 hh⟩
  exact roots_cyclotomic_nodup

/-- **The complex root multiset of `Φ_h`** consists of `exp (2πi e / h)` for `e < h` coprime to `h`,
each once. -/
theorem roots_cyclotomic_complex (h : ℕ) :
    (cyclotomic h ℂ).roots =
      (((List.range h).filter (Nat.Coprime · h) : Multiset ℕ)).map
        fun e : ℕ => Complex.exp (2 * Real.pi * Complex.I * (e / h)) := by
  have hnd : ((((List.range h).filter (Nat.Coprime · h) : Multiset ℕ)).map
      fun e : ℕ => Complex.exp (2 * Real.pi * Complex.I * (e / h))).Nodup :=
    Complex.nodup_map_exp_two_pi_I_mul_div (Multiset.coe_nodup.2 (List.nodup_range.filter _))
      fun _ he => List.mem_range.1 (List.mem_of_mem_filter (Multiset.mem_coe.1 he))
  refine (Multiset.Nodup.ext (nodup_roots_cyclotomic_complex h) hnd).2 fun ζ => ?_
  rw [mem_roots_cyclotomic_complex_iff, Multiset.mem_map]
  simp

/-- **The complex root multiset of `1 + X + ⋯ + X ^ (n - 1)`** consists of `exp (2πi (e + 1) / n)`
for `e = 0, …, n - 2`, each once. -/
theorem roots_geom_sum_complex (n : ℕ) :
    (∑ i ∈ Finset.range n, (X : ℂ[X]) ^ i).roots =
      (Multiset.range (n - 1)).map
        fun e : ℕ => Complex.exp (2 * Real.pi * Complex.I * ((e + 1 : ℕ) / n)) := by
  obtain rfl | hn := eq_or_ne n 0
  · simp
  rw [(Complex.isPrimitiveRoot_exp n hn).roots_geom_sum]
  exact Multiset.map_congr rfl fun e _ => (Complex.exp_two_pi_I_mul_div (e + 1) n).symm

/-- **The complex root multiset of `X ^ n + 1`** consists of `exp (2πi (2k + 1) / (2n))` for
`k = 0, …, n - 1`, each once. -/
theorem roots_X_pow_add_one_complex (n : ℕ) :
    (X ^ n + 1 : ℂ[X]).roots =
      (Multiset.range n).map
        fun k : ℕ => Complex.exp (2 * Real.pi * Complex.I * ((2 * k + 1 : ℕ) / (2 * n : ℕ))) := by
  obtain rfl | hn := eq_or_ne n 0
  · rw [pow_zero, ← C_1, ← map_add, roots_C]; simp
  rw [(Complex.isPrimitiveRoot_exp (2 * n) (by positivity)).roots_X_pow_add_one]
  exact Multiset.map_congr rfl fun k _ => (Complex.exp_two_pi_I_mul_div (2 * k + 1) (2 * n)).symm

end Polynomial

end
