/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import TauCeti.FieldTheory.RealClosure.IVT
public import TauCeti.Algebra.Polynomial.Eval.OneSided
public import Mathlib.Basic.Sign.Basic
import TauCeti.Data.Finset.Jumps

/-! # Polynomial signs between roots in a real closed field

Signs are constant on root-free intervals. Up to the next root on either side of a point,
a polynomial has the algebraic one-sided signs `derivSignLeft` and `derivSignRight` of that point.
Consequently a polynomial changes sign across an isolated root exactly when the root has odd
multiplicity, and at a simple root the signs on either side are determined by the sign of the
derivative. Between two nonroots, the change of sign is the sum of the jumps
`derivSignRight - derivSignLeft` of the one-sided signs at the roots in between.

## References

S. Basu, R. Pollack, and M.-F. Roy,
*Algorithms in Real Algebraic Geometry*, second edition, Chapter 2.
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

/-- Up to its next root to the right of `r`, a polynomial has its right-hand sign at `r`. -/
theorem sign_eval_eq_derivSignRight (p : R[X]) {r b : R} (hrb : r < b)
    (hz : ∀ x ∈ Set.Ioc r b, p.eval x ≠ 0) :
    SignType.sign (p.eval b) = p.derivSignRight r := by
  obtain ⟨-, u, -, hu, -, hR⟩ := p.exists_derivSignLeft_derivSignRight r
  obtain ⟨y, hry, hy⟩ := exists_between (lt_min hu hrb)
  rw [← hR y ⟨hry, hy.trans_le (min_le_left _ _)⟩]
  exact (p.sign_eval_const (hy.trans_le (min_le_right _ _)).le
    fun x hx => hz x ⟨hry.trans_le hx.1, hx.2⟩).symm

/-- Up to its next root to the left of `r`, a polynomial has its left-hand sign at `r`. -/
theorem sign_eval_eq_derivSignLeft (p : R[X]) {a r : R} (har : a < r)
    (hz : ∀ x ∈ Set.Ico a r, p.eval x ≠ 0) :
    SignType.sign (p.eval a) = p.derivSignLeft r := by
  obtain ⟨l, -, hl, -, hL, -⟩ := p.exists_derivSignLeft_derivSignRight r
  obtain ⟨x, hx, hxr⟩ := exists_between (max_lt hl har)
  rw [← hL x ⟨(le_max_left _ _).trans_lt hx, hxr⟩]
  exact p.sign_eval_const ((le_max_right _ _).trans_lt hx).le
    fun y hy => hz y ⟨hy.1, hy.2.trans_lt hxr⟩

/-- If a polynomial has no zeros in `[a, b]` except possibly at an interior point `r`, its
endpoint signs are its one-sided signs at `r`. Multiple roots and nonroots are allowed. -/
theorem signs_at_isolated_point (p : R[X]) {a r b : R} (har : a < r) (hrb : r < b)
    (hz : ∀ x ∈ Set.Icc a b, x ≠ r → p.eval x ≠ 0) :
    SignType.sign (p.eval a) = p.derivSignLeft r ∧
      SignType.sign (p.eval b) = p.derivSignRight r :=
  ⟨p.sign_eval_eq_derivSignLeft har fun x hx => hz x ⟨hx.1, hx.2.le.trans hrb.le⟩ hx.2.ne,
    p.sign_eval_eq_derivSignRight hrb fun x hx => hz x ⟨har.le.trans hx.1.le, hx.2⟩ hx.1.ne'⟩

/-- A polynomial keeps its sign across an isolated point of `[a, b]` exactly when its root
multiplicity there is even. This includes a nonroot, of multiplicity zero. -/
theorem sign_eval_eq_sign_eval_iff_even_rootMultiplicity (p : R[X]) {a r b : R} (har : a < r)
    (hrb : r < b) (hz : ∀ x ∈ Set.Icc a b, x ≠ r → p.eval x ≠ 0) :
    SignType.sign (p.eval a) = SignType.sign (p.eval b) ↔ Even (p.rootMultiplicity r) := by
  obtain ⟨ha, hb⟩ := p.signs_at_isolated_point har hrb hz
  rw [ha, hb, derivSignLeft_eq_derivSignRight_iff]

/-- A polynomial changes sign across an isolated root in `[a, b]` exactly when the root has odd
multiplicity. -/
theorem sign_eval_eq_neg_sign_eval_iff_odd_rootMultiplicity (p : R[X]) {a r b : R} (har : a < r)
    (hrb : r < b) (hz : ∀ x ∈ Set.Icc a b, x ≠ r → p.eval x ≠ 0) :
    SignType.sign (p.eval a) = -SignType.sign (p.eval b) ↔ Odd (p.rootMultiplicity r) := by
  have hp : p ≠ 0 := fun h => hz b ⟨(har.trans hrb).le, le_rfl⟩ hrb.ne' (by simp [h])
  obtain ⟨ha, hb⟩ := p.signs_at_isolated_point har hrb hz
  rw [ha, hb, derivSignLeft_eq_neg_derivSignRight_iff hp]

/-- If a polynomial has no zeros except possibly at an interior point, and does
not vanish there either, both endpoint signs agree with its sign at that point. -/
theorem signs_at_nonroot (p : R[X]) {a r b : R} (har : a < r) (hrb : r < b)
    (hr : p.eval r ≠ 0) (hz : ∀ x ∈ Set.Icc a b, x ≠ r → p.eval x ≠ 0) :
    SignType.sign (p.eval a) = SignType.sign (p.eval r) ∧
      SignType.sign (p.eval b) = SignType.sign (p.eval r) := by
  obtain ⟨ha, hb⟩ := p.signs_at_isolated_point har hrb hz
  exact ⟨ha.trans (p.derivSignLeft_eq_sign_eval hr), hb.trans (p.derivSignRight_eq_sign_eval hr)⟩

/-- Near an isolated simple root, a polynomial changes from the negative
of its derivative's sign to its derivative's sign. -/
theorem signs_at_root (p : R[X]) {a r b : R} (har : a < r) (hrb : r < b)
    (hr : p.eval r = 0) (hd : p.derivative.eval r ≠ 0)
    (hz : ∀ x ∈ Set.Icc a b, x ≠ r → p.eval x ≠ 0) :
    SignType.sign (p.eval a) = -SignType.sign (p.derivative.eval r) ∧
    SignType.sign (p.eval b) = SignType.sign (p.derivative.eval r) := by
  -- At a root the derivative has the right-hand sign of `p` and the opposite left-hand sign.
  have hL := derivSignLeft_derivative_of_isRoot (p := p) hr
  have hR := derivSignRight_derivative_of_isRoot (p := p) hr
  rw [derivSignLeft_eq_sign_eval _ hd] at hL
  rw [derivSignRight_eq_sign_eval _ hd] at hR
  obtain ⟨ha, hb⟩ := p.signs_at_isolated_point har hrb hz
  exact ⟨ha.trans (by rw [hL, neg_neg]), hb.trans hR.symm⟩

/-- Between two nonroots, the change of sign of a polynomial is the sum of the jumps of its
one-sided signs at the roots in between. Multiple roots are allowed. -/
theorem sign_eval_sub_sign_eval_eq_sum (p : R[X]) {a b : R} (hab : a < b) (ha : p.eval a ≠ 0)
    (hb : p.eval b ≠ 0) :
    (SignType.sign (p.eval b) : ℤ) - SignType.sign (p.eval a) =
      ∑ x ∈ p.roots.toFinset.filter (fun x => a < x ∧ x < b),
        ((p.derivSignRight x : ℤ) - p.derivSignLeft x) := by
  classical
  have hp : p ≠ 0 := fun h => ha (by simp [h])
  have hS (x : R) : x ∈ p.roots.toFinset ↔ p.eval x = 0 := by simp [mem_roots hp]
  -- Telescope the negated sign over the roots: it is constant on root-free intervals, and at an
  -- isolated root it changes by the jump of the one-sided signs.
  have h := Finset.sum_jumps p.roots.toFinset (fun x => -(SignType.sign (p.eval x) : ℤ))
    (fun x => (p.derivSignRight x : ℤ) - p.derivSignLeft x)
    (fun c d _ _ hcd hn => by
      rw [p.sign_eval_const hcd.le fun x hx hx0 => hn x ((hS x).2 hx0) hx])
    (fun c r d _ _ hcr hrd _ hn => by
      obtain ⟨hc, hd⟩ := p.signs_at_isolated_point hcr hrd fun x hx hxr hx0 =>
        hxr (hn x ((hS x).2 hx0) hx)
      rw [hc, hd]
      ring)
    hab (by simpa [hS] using ha) (by simpa [hS] using hb)
  rw [← h]
  ring

end Polynomial
