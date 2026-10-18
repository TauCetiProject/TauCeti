/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Separable

/-!
# Powers of a separable minimal polynomial

Let `L / K` be a field extension and let `x ∈ L` be separable over `K`. Then `x` is a simple root
of `minpoly K x`, so the multiplicity of `x` as a root of a polynomial `p ∈ K[X]` is the
multiplicity of `minpoly K x` as a factor of `p`: `minpoly K x ^ m` divides `p` if and only if
`(X - x) ^ m` divides `p` in `L[X]`. For `m = 1` this reduces to `minpoly.dvd_iff`.

In Thue's method of Diophantine approximation this turns high-order vanishing of a polynomial with
rational coefficients at an algebraic number `α` into divisibility by a power of the minimal
polynomial of `α`, and hence into a lower bound for its degree.

Separability is needed: over a field `K` of characteristic `p` containing an element `a` which is
not a `p`-th power, a `p`-th root `x` of `a` has `minpoly K x = X ^ p - a = (X - x) ^ p`, so
`(X - x) ^ p` divides `minpoly K x` while `minpoly K x ^ p` does not.

## Main results

* `minpoly.pow_dvd_iff`: for `x` separable over `K`, a polynomial `p ∈ K[X]` is divisible by
  `minpoly K x ^ m` if and only if `(X - x) ^ m` divides `p` in `L[X]`.

## References

* J.-H. Evertse, *Diophantine Approximation*, lecture notes (2019), ch. 6, Lemma 6.11.
-/

public section

open Polynomial

namespace minpoly

variable {K L : Type*} [Field K] [Field L] [Algebra K L] {x : L}

/-- For `x` separable over `K`, a polynomial `p ∈ K[X]` is divisible by `minpoly K x ^ m` if and
only if `(X - x) ^ m` divides `p` in `L[X]`. -/
theorem pow_dvd_iff (hx : IsSeparable K x) {p : K[X]} {m : ℕ} :
    minpoly K x ^ m ∣ p ↔ (X - C x) ^ m ∣ p.map (algebraMap K L) := by
  obtain ⟨q, hq⟩ : X - C x ∣ (minpoly K x).map (algebraMap K L) := by
    rw [dvd_iff_isRoot, IsRoot.def, eval_map_algebraMap, minpoly.aeval]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · refine (pow_dvd_pow_of_dvd (Dvd.intro q hq.symm) m).trans ?_
    rw [← Polynomial.map_pow]
    exact Polynomial.map_dvd _ h
  -- `x` is a simple root of `minpoly K x`, so the cofactor `q` does not vanish at `x`.
  have hqx : ¬q.IsRoot x := fun hq₀ ↦ hx.aeval_derivative_ne_zero (minpoly.aeval K x) <| by
    rw [← eval_map_algebraMap, ← derivative_map, hq, derivative_mul]
    simp [hq₀.eq_zero]
  have hcop : IsCoprime (X - C x) q :=
    (irreducible_X_sub_C x).coprime_iff_not_dvd.2 (by rwa [dvd_iff_isRoot])
  induction m generalizing p with
  | zero => simp
  | succ m ih =>
    obtain ⟨g, rfl⟩ := minpoly.dvd K x (p := p) <| by
      rw [← eval_map_algebraMap, ← IsRoot.def, ← dvd_iff_isRoot]
      exact (dvd_pow_self _ m.succ_ne_zero).trans h
    have h' : (X - C x) ^ m ∣ q * g.map (algebraMap K L) := by
      simpa [hq, pow_succ', mul_assoc, mul_dvd_mul_iff_left, X_sub_C_ne_zero] using h
    rw [pow_succ']
    exact mul_dvd_mul_left _ (ih (hcop.pow_left.dvd_of_dvd_mul_left h'))

end minpoly
