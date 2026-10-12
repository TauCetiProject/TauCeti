/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import TauCeti.FieldTheory.RealClosure.IVT
public import TauCeti.Algebra.Polynomial.Rolle
import TauCeti.Algebra.Polynomial.LinearFactor
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-! # Polynomial Rolle over an abstract real closed field

`polynomialRolle_of_isRealClosed` supplies `TauCeti.PolynomialRolle R` from `IsRealClosed R`.
The direct `Polynomial.exists_derivative_root` and
`Polynomial.exists_eval_sub_eq_derivative_eval_mul` give Rolle and mean value without a separate
Rolle premise. The four `Polynomial.*On_of_derivative_*` theorems give monotonicity,
antitonicity, and their strict variants on closed intervals. Under `IsRealClosed`, use these
direct statements; `TauCeti.Algebra.Polynomial.Rolle` instead derives the same consequences
from an explicit polynomial Rolle hypothesis over a general ordered field.

Between consecutive roots, removing their multiplicities leaves a polynomial
of constant nonzero sign. A factor of the derivative has opposite signs at
the endpoints, so polynomial IVT supplies the required critical point.

## References

Salma Kuhlmann,
[Real Algebraic Geometry, Lecture 6](https://www.math.uni-konstanz.de/algebra/WS0910/Notes06.pdf),
Corollary 2.2.
-/

public section

namespace TauCeti.RealClosure

open Polynomial Set

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]

/-- Rolle between consecutive distinct roots, allowing arbitrary endpoint multiplicities. -/
private theorem exists_derivative_root_of_consecutive (p : R[X]) {a b : R} (hab : a < b)
    (ha : p.eval a = 0) (hb : p.eval b = 0)
    (hroot : ∀ x ∈ Ioo a b, p.eval x ≠ 0) :
    ∃ c ∈ Ioo a b, p.derivative.eval c = 0 := by
  have hp : p ≠ 0 := by
    intro h
    obtain ⟨c, hc⟩ := exists_between hab
    exact hroot c hc (by simp [h])
  obtain ⟨m, q, hpq, hqa⟩ := IsRoot.exists_eq_pow_succ_mul ha hp
  have hq0 : q ≠ 0 := by intro h; exact hqa (by simp [h])
  have hqb : q.eval b = 0 := by
    rw [hpq, eval_mul, eval_pow, eval_sub, eval_X, eval_C] at hb
    exact (mul_eq_zero.mp hb).resolve_left (pow_ne_zero _ (sub_ne_zero.mpr hab.ne'))
  obtain ⟨n, r, hqr, hrb⟩ := IsRoot.exists_eq_pow_succ_mul hqb hq0
  have hra : r.eval a ≠ 0 := by
    intro h
    apply hqa
    rw [hqr]
    simp [h]
  have hrr : ∀ x ∈ Icc a b, r.eval x ≠ 0 := by
    intro x hx
    rcases hx.1.eq_or_lt with rfl | hax
    · exact hra
    rcases hx.2.eq_or_lt with rfl | hxb
    · exact hrb
    intro h
    apply hroot x ⟨hax, hxb⟩
    rw [hpq, hqr]
    simp [h]
  -- Removing `(X - C a) ^ m * (X - C b) ^ n` from the derivative leaves the factor `d`.
  let d : R[X] := C ((m : R) + 1) * (X - C b) * r +
    C ((n : R) + 1) * (X - C a) * r + (X - C a) * (X - C b) * r.derivative
  have hderiv : p.derivative = (X - C a) ^ m * (X - C b) ^ n * d := by
    rw [hpq, hqr]
    exact derivative_root_factors a b m n r
  have hda : d.eval a = ((m : R) + 1) * (a - b) * r.eval a := by simp [d]
  have hdb : d.eval b = ((n : R) + 1) * (b - a) * r.eval b := by simp [d]
  have hm : 0 < (m : R) + 1 := by positivity
  have hn : 0 < (n : R) + 1 := by positivity
  have hsign : d.eval a * d.eval b < 0 := by
    rw [hda, hdb]
    have hneg := mul_neg_of_neg_of_pos (sub_neg.mpr hab) (sub_pos.mpr hab)
    have hpos := eval_mul_pos_of_no_roots r hab.le hrr
    convert mul_neg_of_pos_of_neg (mul_pos hm hn) (mul_neg_of_neg_of_pos hneg hpos) using 1
    ring
  obtain ⟨c, hc, hd⟩ := exists_root_Ioo_of_mul_neg d hab hsign
  exact ⟨c, hc, by rw [hderiv]; simp [hd]⟩

/-- Between any two distinct roots there is a root of the formal derivative. -/
theorem _root_.Polynomial.exists_derivative_root_of_isRoot (p : R[X]) {a b : R} (hab : a < b)
    (ha : p.eval a = 0) (hb : p.eval b = 0) :
    ∃ c ∈ Ioo a b, p.derivative.eval c = 0 := by
  classical
  by_cases hp : p = 0
  · obtain ⟨c, hac, hcb⟩ := exists_between hab
    exact ⟨c, ⟨hac, hcb⟩, by simp [hp]⟩
  have hbmem : b ∈ p.roots.toFinset := by simpa [mem_roots hp] using hb
  obtain ⟨b', hb'mem, hab', hnext⟩ :=
    Finset.exists_next_right (s := p.roots.toFinset) ⟨b, hbmem, hab⟩
  have hb' : p.eval b' = 0 := by simpa [mem_roots hp] using hb'mem
  have hb'b : b' ≤ b := hnext b hbmem hab
  have hroot : ∀ x ∈ Ioo a b', p.eval x ≠ 0 := by
    intro x hx hz
    have hmem : x ∈ p.roots.toFinset := by simpa [mem_roots hp] using hz
    exact hx.2.not_ge (hnext x hmem hx.1)
  obtain ⟨c, hc, hd⟩ := exists_derivative_root_of_consecutive p hab' ha hb' hroot
  exact ⟨c, ⟨hc.1, hc.2.trans_le hb'b⟩, hd⟩

/-- Polynomial Rolle follows from the abstract real-closed-field axioms. -/
theorem polynomialRolle_of_isRealClosed : PolynomialRolle R := by
  apply PolynomialRolle.of_forall
  intro p a b hab heq
  obtain ⟨c, hc, hd⟩ := exists_derivative_root_of_isRoot (p - C (p.eval a)) hab
    (by simp) (by simp [heq])
  exact ⟨c, hc, by simpa using hd⟩

/-- Equal endpoint values give an interior derivative root over a real closed field. -/
theorem _root_.Polynomial.exists_derivative_root (p : R[X]) {a b : R}
    (hab : a < b) (h : p.eval a = p.eval b) : ∃ c ∈ Ioo a b, p.derivative.eval c = 0 :=
  polynomialRolle_of_isRealClosed.exists_derivative_root p hab h

/-- Polynomial mean value over an ordered real closed field. -/
theorem _root_.Polynomial.exists_eval_sub_eq_derivative_eval_mul (p : R[X]) {a b : R}
    (hab : a < b) :
    ∃ c ∈ Ioo a b, p.eval b - p.eval a = p.derivative.eval c * (b - a) :=
  polynomialRolle_of_isRealClosed.exists_eval_sub_eq_derivative_eval_mul p hab

/-- A nonnegative formal derivative makes polynomial evaluation monotone on an interval. -/
theorem _root_.Polynomial.monotoneOn_of_derivative_nonneg (p : R[X]) {a b : R}
    (hd : ∀ x ∈ Ioo a b, 0 ≤ p.derivative.eval x) : MonotoneOn p.eval (Icc a b) :=
  polynomialRolle_of_isRealClosed.monotoneOn p hd

/-- A nonpositive formal derivative makes polynomial evaluation antitone on an interval. -/
theorem _root_.Polynomial.antitoneOn_of_derivative_nonpos (p : R[X]) {a b : R}
    (hd : ∀ x ∈ Ioo a b, p.derivative.eval x ≤ 0) : AntitoneOn p.eval (Icc a b) :=
  polynomialRolle_of_isRealClosed.antitoneOn p hd

/-- A positive formal derivative makes polynomial evaluation strictly monotone on an interval. -/
theorem _root_.Polynomial.strictMonoOn_of_derivative_pos (p : R[X]) {a b : R}
    (hd : ∀ x ∈ Ioo a b, 0 < p.derivative.eval x) : StrictMonoOn p.eval (Icc a b) :=
  polynomialRolle_of_isRealClosed.strictMonoOn p hd

/-- A negative formal derivative makes polynomial evaluation strictly antitone on an interval. -/
theorem _root_.Polynomial.strictAntiOn_of_derivative_neg (p : R[X]) {a b : R}
    (hd : ∀ x ∈ Ioo a b, p.derivative.eval x < 0) : StrictAntiOn p.eval (Icc a b) :=
  polynomialRolle_of_isRealClosed.strictAntiOn p hd

end TauCeti.RealClosure
