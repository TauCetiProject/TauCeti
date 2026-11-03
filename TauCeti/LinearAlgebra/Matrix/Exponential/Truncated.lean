/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.TrivSqZeroExt.Basic

/-!
# Truncated matrix exponential series over coefficient algebras

`Matrix.expSeries A d x` is the finite sum for `exp(x • A)` truncated below degree `d`.
It is defined over any commutative algebra of the base field, including polynomial rings and
dual numbers, without assuming that `A` is nilpotent. `AlgHom.map_expSeries` gives its
naturality under change of coefficients, and `Matrix.expSeries_inr` computes its value at a
purely infinitesimal dual number. These formulas let polynomial matrix families be evaluated
and differentiated algebraically.
-/

public section

namespace Matrix

open TrivSqZeroExt

section ExpSeries

variable {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]

/-- The exponential series of `x • A`, truncated below degree `d`, for a matrix `A` over `K` and a
scalar `x` in a commutative `K`-algebra `S`. It is a truncated sum rather than `IsNilpotent.exp`
so that it is defined over every commutative `K`-algebra, polynomial rings and dual numbers
included, and commutes with every `K`-algebra map. -/
noncomputable def expSeries {S : Type*} [CommRing S] [Algebra K S] (A : Matrix ι ι K)
    (d : ℕ) (x : S) : Matrix ι ι S :=
  ∑ k ∈ Finset.range d, (x ^ k * algebraMap K S (k.factorial : K)⁻¹) • A.map (algebraMap K S) ^ k

/-- The finite-sum formula for the truncated exponential series. -/
theorem expSeries_def {S : Type*} [CommRing S] [Algebra K S] (A : Matrix ι ι K)
    (d : ℕ) (x : S) :
    expSeries A d x =
      ∑ k ∈ Finset.range d,
        (x ^ k * algebraMap K S (k.factorial : K)⁻¹) • A.map (algebraMap K S) ^ k := (rfl)

/-- The truncated exponential series is natural in the coefficient algebra. -/
@[simp]
theorem _root_.AlgHom.map_expSeries {S S' : Type*} [CommRing S] [Algebra K S] [CommRing S']
    [Algebra K S'] (f : S →ₐ[K] S') (A : Matrix ι ι K) (d : ℕ) (x : S) :
    (expSeries A d x).map f = expSeries A d (f x) := by
  rw [← AlgHom.mapMatrix_apply]
  have hsmul (r : S) (M : Matrix ι ι S) : f.mapMatrix (r • M) = f r • f.mapMatrix M := by
    ext i j
    simp
  simp only [expSeries, map_sum, hsmul, map_pow, map_mul, AlgHom.commutes]
  congr! 3
  ext i j
  simp

/-- With a square-zero coefficient `ε c`, the truncated exponential series is `1 + ε c A`. -/
theorem expSeries_inr {d : ℕ} (hd : 2 ≤ d) (A : Matrix ι ι K) (c : K) :
    expSeries A d (inr c : TrivSqZeroExt K K) = 1 + (c • A).map inr := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le' hd
  have hsq (k : ℕ) : (inr c : TrivSqZeroExt K K) ^ (k + 1 + 1) = 0 := by
    rw [pow_succ, pow_succ, mul_assoc, inr_mul_inr, mul_zero]
  rw [expSeries, Finset.sum_range_succ', Finset.sum_range_succ', Finset.sum_eq_zero, zero_add]
  · simp only [zero_add, pow_one, pow_zero, Nat.factorial_zero, Nat.factorial_one, Nat.cast_one,
      inv_one, map_one, mul_one, one_smul, add_comm (1 : Matrix ι ι _)]
    congr 1
    ext i j : 1
    simp [algebraMap_eq_inl, inr_mul_inl]
  · intro k _
    rw [hsq, zero_mul]
    ext i j : 1
    simp

end ExpSeries

end Matrix
