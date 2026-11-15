/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Minpoly.Field
public import TauCeti.NumberTheory.NewtonPolygon.Roots
public import TauCeti.RingTheory.Valuation.Denominator

/-!
# Ramification forced by the slopes of a Newton polygon

Let `v` be a real additive valuation on a field `K` and `w` a real additive valuation on an
extension field `L` restricting to `v`. If every finite slope of a polynomial `f` over `K` equals
the rational number `q`, every nonzero root `α` of `f` in `L` has valuation `w α = -q`, by
`Polynomial.addValuation_eq_neg_of_forall_mem_newtonSlopes_eq`. The denominator of `q` therefore
constrains the arithmetic of `L`:

* if `e • w` takes integer values on the nonzero elements of `L`, as for the integral
  normalisation of `L` when `e` is the ramification index, then `q.den ∣ e`;
* if `v` takes integer values on the nonzero elements of `K` and `L/K` is finite, then
  `q.den ≤ [L : K]`, the bound complementing `e ≤ [L : K]`.

The minimal polynomial of a nonzero algebraic element is a nonzero polynomial with that element as
a root, so the same conclusions hold when it is pure. No completeness of `K` and no hypothesis on
the residue field is used. For instance, `X ^ p - p` has the single slope `-1 / p`, so any finite
extension of `ℚ_[p]` containing a `p`-th root of `p` has ramification index divisible by `p`.

## Main results

* `Polynomial.den_dvd_of_forall_mem_newtonSlopes_eq`: the denominator of the slope of a pure
  polynomial with a nonzero root in `L` divides the ramification index.
* `Polynomial.den_le_finrank_of_forall_mem_newtonSlopes_eq`: that denominator is at most
  `[L : K]`.
* `minpoly.den_dvd_of_forall_mem_newtonSlopes_eq`: the same divisibility for a pure minimal
  polynomial.

## References

* J. Neukirch, *Algebraic Number Theory*, Grundlehren 322, Springer, 1999, Chapter II, §6.
* N. Koblitz, *p-adic Numbers, p-adic Analysis, and Zeta-Functions*, second edition,
  Graduate Texts in Mathematics 58, Springer, 1984, Chapter IV §3.
-/

public section

variable {K L : Type*} [Field K] [Field L] [Algebra K L] {v : AddValuation K (WithTop ℝ)}
  {w : AddValuation L (WithTop ℝ)}

namespace Polynomial

/-- A nonzero root in `L` of a polynomial over `K` all of whose finite slopes equal `q` has
valuation `-q`. -/
private theorem addValuation_eq_neg_ratCast (hw : ∀ x, w (algebraMap K L x) = v x) {f : K[X]}
    (hf : f ≠ 0) {q : ℚ} (hq : ∀ m ∈ f.newtonSlopes v, m = q) {α : L} (hα : α ≠ 0)
    (hroot : aeval α f = 0) : w α = (((-q : ℚ) : ℝ) : WithTop ℝ) := by
  rw [Rat.cast_neg]
  exact addValuation_eq_neg_of_forall_mem_newtonSlopes_eq (fun x ↦ w.top_iff.mp)
    (algebraMap K L) hw ((Polynomial.map_ne_zero_iff (algebraMap K L).injective).mpr hf) hq hα
    (by rwa [IsRoot, eval_map_algebraMap])

/-- **The slope denominator of a pure polynomial divides the ramification index.** Let `w` on `L`
restrict to `v` on `K`, and let `e • w` take integer values on the nonzero elements of `L`. If
every finite slope of a nonzero `f : K[X]` equals `q` and `f` has a nonzero root in `L`, then
`q.den ∣ e`. -/
theorem den_dvd_of_forall_mem_newtonSlopes_eq (hw : ∀ x, w (algebraMap K L x) = v x) {e : ℕ}
    (hL : ∀ y : L, y ≠ 0 → ∃ n : ℤ, w y = ((n / e : ℝ) : WithTop ℝ)) {f : K[X]} (hf : f ≠ 0)
    {q : ℚ} (hq : ∀ m ∈ f.newtonSlopes v, m = q) {α : L} (hα : α ≠ 0)
    (hroot : aeval α f = 0) : q.den ∣ e := by
  simpa using AddValuation.den_dvd_of_map_eq_ratCast hL
    (addValuation_eq_neg_ratCast hw hf hq hα hroot)

/-- **The slope denominator of a pure polynomial is at most the degree.** Let `w` on a finite
extension `L` restrict to a valuation `v` on `K` taking integer values on nonzero elements. If
every finite slope of a nonzero `f : K[X]` equals `q` and `f` has a nonzero root in `L`, then
`q.den ≤ [L : K]`. -/
theorem den_le_finrank_of_forall_mem_newtonSlopes_eq [FiniteDimensional K L]
    (hint : ∀ x : K, x ≠ 0 → ∃ n : ℤ, v x = ((n : ℝ) : WithTop ℝ))
    (hw : ∀ x, w (algebraMap K L x) = v x) {f : K[X]} (hf : f ≠ 0) {q : ℚ}
    (hq : ∀ m ∈ f.newtonSlopes v, m = q) {α : L} (hα : α ≠ 0) (hroot : aeval α f = 0) :
    q.den ≤ Module.finrank K L := by
  simpa using AddValuation.den_le_finrank_of_map_eq_ratCast hint hw
    (addValuation_eq_neg_ratCast hw hf hq hα hroot)

end Polynomial

namespace minpoly

/-- **The slope denominator of a pure minimal polynomial divides the ramification index.** Let `w`
on `L` restrict to `v` on `K`, and let `e • w` take integer values on the nonzero elements of `L`.
If `α ∈ L` is nonzero and integral over `K` and every finite slope of its minimal polynomial
equals `q`, then `q.den ∣ e`. -/
theorem den_dvd_of_forall_mem_newtonSlopes_eq (hw : ∀ x, w (algebraMap K L x) = v x) {e : ℕ}
    (hL : ∀ y : L, y ≠ 0 → ∃ n : ℤ, w y = ((n / e : ℝ) : WithTop ℝ)) {α : L} (hα : α ≠ 0)
    (hαK : IsIntegral K α) {q : ℚ} (hq : ∀ m ∈ (minpoly K α).newtonSlopes v, m = q) :
    q.den ∣ e :=
  Polynomial.den_dvd_of_forall_mem_newtonSlopes_eq hw hL (minpoly.ne_zero hαK) hq hα
    (minpoly.aeval K α)

end minpoly

end
