/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import TauCeti.FieldTheory.RealClosure.IVT
public import Mathlib.Basic.Sign.Basic

/-! # Polynomial signs between roots in a real closed field

Signs are constant on root-free intervals. At a simple root, the signs
on either side are determined by the sign of the derivative.
-/

public section

namespace Polynomial

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]

/-- A polynomial has a constant sign on a root-free interval. -/
theorem sign_eval_const (p : R[X]) {a b : R} (hab : a ≤ b)
    (hz : ∀ x ∈ Set.Icc a b, p.eval x ≠ 0) :
    SignType.sign (p.eval a) = SignType.sign (p.eval b) := by
  rcases mul_pos_iff.mp (p.eval_mul_pos_of_no_roots hab hz) with h | h
  · rw [sign_pos h.1, sign_pos h.2]
  · rw [sign_neg h.1, sign_neg h.2]

/-- If a polynomial has no zeros except possibly at an interior point, and does
not vanish there either, both endpoint signs agree with its sign at that point. -/
theorem signs_at_nonroot (p : R[X]) {a r b : R} (har : a < r) (hrb : r < b)
    (hr : p.eval r ≠ 0) (hz : ∀ x ∈ Set.Icc a b, x ≠ r → p.eval x ≠ 0) :
    SignType.sign (p.eval a) = SignType.sign (p.eval r) ∧
      SignType.sign (p.eval b) = SignType.sign (p.eval r) := by
  have hne (x : R) (hx : x ∈ Set.Icc a b) : p.eval x ≠ 0 := by
    rcases eq_or_ne x r with rfl | hxr
    · exact hr
    · exact hz x hx hxr
  exact ⟨p.sign_eval_const har.le (fun x hx => hne x ⟨hx.1, hx.2.trans hrb.le⟩),
    (p.sign_eval_const hrb.le (fun x hx => hne x ⟨har.le.trans hx.1, hx.2⟩)).symm⟩

/-- Near an isolated simple root, a polynomial changes from the negative
of its derivative's sign to its derivative's sign. -/
theorem signs_at_root (p : R[X]) {a r b : R} (har : a < r) (hrb : r < b)
    (hr : p.eval r = 0) (hd : p.derivative.eval r ≠ 0)
    (hz : ∀ x ∈ Set.Icc a b, x ≠ r → p.eval x ≠ 0) :
    SignType.sign (p.eval a) = -SignType.sign (p.derivative.eval r) ∧
    SignType.sign (p.eval b) = SignType.sign (p.derivative.eval r) := by
  obtain ⟨d, hp⟩ := (dvd_iff_isRoot.mpr hr : X - C r ∣ p)
  have hdr : p.derivative.eval r = d.eval r := by
    rw [hp, derivative_mul]
    simp
  have hdz : ∀ x ∈ Set.Icc a b, d.eval x ≠ 0 := by
    intro x hx
    by_cases hxr : x = r
    · simpa [hxr, hdr] using hd
    · intro hdx
      apply hz x hx hxr
      simp [hp, hdx]
  have hda := sign_eval_const _ har.le (fun x hx => hdz x ⟨hx.1, hx.2.trans hrb.le⟩)
  have hdb := sign_eval_const _ hrb.le (fun x hx => hdz x ⟨har.le.trans hx.1, hx.2⟩)
  constructor
  · rw [hdr, hp, eval_mul, eval_sub, eval_X, eval_C, sign_mul,
      sign_neg (sub_neg.mpr har), neg_one_mul, hda]
  · rw [hdr, hp, eval_mul, eval_sub, eval_X, eval_C, sign_mul,
      sign_pos (sub_pos.mpr hrb), one_mul, ← hdb]

end Polynomial
