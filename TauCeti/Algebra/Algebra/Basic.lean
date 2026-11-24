/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Basic

/-!
# Power commutation for scalar-commuting elements of an algebra

Let `A` be an `R`-algebra over a commutative semiring `R`. If two elements satisfy a
scalar-commutation law `x * u = c • (u * x)`, then `x` moves past `u ^ n` with factor `c ^ n`.
When `c = r ^ 2`, induction gives `(u * x) ^ n = r ^ (n * (n - 1)) • (u ^ n * x ^ n)`.

A monoid acting on `A` multiplicatively and commuting with the scalars of `R`, for instance by
`R`-algebra endomorphisms, fixes the image `Algebra.algebraMapSubmonoid A M` of every submonoid `M`
of `R`.

## Main results

* `TauCeti.mul_pow_of_mul_eq_smul_mul`: `x * u = c • (u * x)` implies
  `x * u ^ n = c ^ n • (u ^ n * x)`.
* `TauCeti.mul_pow_of_mul_eq_sq_smul_mul`: `x * u = r ^ 2 • (u * x)` implies
  `(u * x) ^ n = r ^ (n * (n - 1)) • (u ^ n * x ^ n)`.
* `TauCeti.Algebra.smul_eq_of_mem_algebraMapSubmonoid`: such an action fixes the elements of
  `Algebra.algebraMapSubmonoid A M`.
-/

public section

namespace TauCeti

variable {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]

/-- If `x * u = c • (u * x)` in an `R`-algebra, then `x * u ^ n = c ^ n • (u ^ n * x)`. -/
theorem mul_pow_of_mul_eq_smul_mul {c : R} {u x : A} (h : x * u = c • (u * x)) (n : ℕ) :
    x * u ^ n = c ^ n • (u ^ n * x) := by
  have hxu : SemiconjBy x u (c • u) := by rw [SemiconjBy, smul_mul_assoc, h]
  simpa only [smul_pow, smul_mul_assoc] using (hxu.pow_right n).eq

/-- If `x * u = r ^ 2 • (u * x)` in an `R`-algebra, then
`(u * x) ^ n = r ^ (n * (n - 1)) • (u ^ n * x ^ n)`. -/
theorem mul_pow_of_mul_eq_sq_smul_mul {r : R} {u x : A} (h : x * u = r ^ 2 • (u * x))
    (n : ℕ) : (u * x) ^ n = r ^ (n * (n - 1)) • (u ^ n * x ^ n) := by
  have hux : SemiconjBy u (r ^ 2 • x) x := by rw [SemiconjBy, mul_smul_comm, h]
  induction n with
  | zero => simp
  | succ n ih =>
    have hxnu : x ^ n * u = (r ^ 2) ^ n • (u * x ^ n) := by
      rw [← (hux.pow_right n).eq, smul_pow, mul_smul_comm]
    have hexp : n * (n - 1) + 2 * n = (n + 1) * n := by cases n <;> grind
    rw [pow_succ, ih, smul_mul_assoc, mul_assoc, ← mul_assoc (x ^ n), hxnu, smul_mul_assoc,
      mul_smul_comm, smul_smul, ← pow_mul, ← pow_add, hexp, mul_assoc u (x ^ n) x, ← pow_succ x,
      ← mul_assoc (u ^ n) u, ← pow_succ u, Nat.add_sub_cancel]

/-- A monoid `G` acting on the `R`-algebra `A` multiplicatively and commuting with the scalars of
`R`, for instance by `R`-algebra endomorphisms, fixes the image in `A` of a submonoid of `R`. -/
theorem Algebra.smul_eq_of_mem_algebraMapSubmonoid {G : Type*} [Monoid G]
    [MulDistribMulAction G A] [SMulCommClass G R A] {M : Submonoid R} (g : G) {a : A}
    (ha : a ∈ Algebra.algebraMapSubmonoid A M) : g • a = a := by
  obtain ⟨m, -, rfl⟩ := ha
  exact smul_algebraMap g m

end TauCeti
