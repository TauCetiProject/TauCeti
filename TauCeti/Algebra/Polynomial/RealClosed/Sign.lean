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

Signs are constant on root-free intervals. At a simple root, the signs
on either side are determined by the sign of the derivative. Between two
nonroots, the change of sign is the sum of the jumps `signRight - signLeft`
of the one-sided signs at the roots in between.
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

/-- Between two nonroots, the change of sign of a polynomial is the sum of the jumps of its
one-sided signs at the roots in between. Multiple roots are allowed. -/
theorem sign_eval_sub_sign_eval_eq_sum (p : R[X]) {a b : R} (hab : a < b) (ha : p.eval a ≠ 0)
    (hb : p.eval b ≠ 0) :
    (SignType.sign (p.eval b) : ℤ) - SignType.sign (p.eval a) =
      ∑ x ∈ p.roots.toFinset.filter (fun x => a < x ∧ x < b),
        ((p.signRight x : ℤ) - p.signLeft x) := by
  classical
  have hp : p ≠ 0 := fun h => ha (by simp [h])
  have hS (x : R) : x ∈ p.roots.toFinset ↔ p.eval x = 0 := by simp [mem_roots hp]
  -- Points of `[c, d]` other than `r` are nonroots when `r` is the only root there.
  have hfree {c d r : R} (hn : ∀ x ∈ p.roots.toFinset, x ∈ Set.Icc c d → x = r)
      {c' d' : R} (hc : c ≤ c') (hd : d' ≤ d) (hr : r ∉ Set.Icc c' d') :
      ∀ x ∈ Set.Icc c' d', p.eval x ≠ 0 := fun x hx hx0 =>
    hr (hn x ((hS x).2 hx0) ⟨hc.trans hx.1, hx.2.trans hd⟩ ▸ hx)
  -- Telescope the negated sign over the roots: it is constant on root-free intervals, and at a
  -- root it changes by the jump of the one-sided signs, realized at nearby points.
  have h := Finset.sum_jumps p.roots.toFinset (fun x => -(SignType.sign (p.eval x) : ℤ))
    (fun x => (p.signRight x : ℤ) - p.signLeft x)
    (fun c d _ _ hcd hn => by
      rw [p.sign_eval_const hcd.le fun x hx hx0 => hn x ((hS x).2 hx0) hx])
    (fun c r d _ _ hcr hrd _ hn => by
      obtain ⟨l, u, hl, hu, hL, hR⟩ := p.exists_signLeft_signRight r
      obtain ⟨x, hx, hxr⟩ := exists_between (max_lt hl hcr)
      obtain ⟨y, hry, hy⟩ := exists_between (lt_min hu hrd)
      have hcx : SignType.sign (p.eval c) = SignType.sign (p.eval x) :=
        p.sign_eval_const ((le_max_right l c).trans hx.le)
          (hfree hn le_rfl (hxr.trans hrd).le fun h => hxr.not_ge h.2)
      have hyd : SignType.sign (p.eval y) = SignType.sign (p.eval d) :=
        p.sign_eval_const (hy.trans_le (min_le_right u d)).le
          (hfree hn (hcr.trans hry).le le_rfl fun h => hry.not_ge h.1)
      rw [hcx, ← hyd, hL x ⟨(le_max_left l c).trans_lt hx, hxr⟩,
        hR y ⟨hry, hy.trans_le (min_le_left u d)⟩]
      ring)
    hab (by simpa [hS] using ha) (by simpa [hS] using hb)
  rw [← h]
  ring

end Polynomial
