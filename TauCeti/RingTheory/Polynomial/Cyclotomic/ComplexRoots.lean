/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
public import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots

/-!
# The complex roots of a cyclotomic polynomial

The complex roots of `Φ_h` are the `exp (2πi e / h)` for `e < h` coprime to `h`, and are simple.
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

end Polynomial

end
