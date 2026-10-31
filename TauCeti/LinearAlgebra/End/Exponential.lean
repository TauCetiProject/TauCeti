/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Nilpotent.Log
public import TauCeti.LinearAlgebra.End.JordanChain.Partition
import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic

/-!
# Jordan type under the finite exponential

For a nilpotent endomorphism `f`, the endomorphisms `exp f - 1` and `f` have the same
kernels and ranges of all powers. In finite dimension they therefore have the same Jordan
partition and are conjugate. Conversely, the Jordan type of `log u` is that of `u - 1`
for a unipotent endomorphism `u`.

These comparisons connect the finite exponential/logarithm equivalence with the classification
of nilpotent and unipotent conjugacy classes. The filtration statements allow any coefficient
semiring and any module equipped with rational scalar multiplication, without finite dimension.
The Jordan-partition and conjugacy statements require a finite-dimensional vector space.
They use the native finite exponential and `IsNilpotent.log`; no topology or analytic convergence
is involved.

## References

* J. E. Humphreys, *Linear Algebraic Groups* (1975), §15.3.
* D. H. Collingwood and W. M. McGovern, *Nilpotent Orbits in Semisimple Lie Algebras*,
  §6.1.
-/

public section

open IsNilpotent

namespace Module.End

variable {R V : Type*} [Semiring R] [AddCommGroup V] [Module R V] [Module ℚ V]

/-- Exponentiation preserves every kernel in the nilpotent filtration. -/
@[simp]
theorem ker_pow_exp_sub_one (f : End R V) (hf : IsNilpotent f) (k : ℕ) :
    LinearMap.ker ((exp f - 1) ^ k) = LinearMap.ker (f ^ k) := by
  obtain ⟨u, hu, heq⟩ := hf.exists_commute_mul_eq_exp_sub_one
  rw [← heq, hu.mul_pow, (hu.pow_pow k k).eq]
  exact LinearMap.ker_comp_of_ker_eq_bot _
    (LinearMap.GeneralLinearGroup.toLinearEquiv (u ^ k)).ker

/-- Exponentiation preserves every range in the nilpotent filtration. -/
@[simp]
theorem range_pow_exp_sub_one (f : End R V) (hf : IsNilpotent f) (k : ℕ) :
    LinearMap.range ((exp f - 1) ^ k) = LinearMap.range (f ^ k) := by
  obtain ⟨u, hu, heq⟩ := hf.exists_commute_mul_eq_exp_sub_one
  rw [← heq, hu.mul_pow]
  exact LinearMap.range_comp_of_range_eq_top _
    (LinearMap.GeneralLinearGroup.toLinearEquiv (u ^ k)).range

/-- Taking the finite logarithm preserves every kernel in the unipotent filtration. -/
@[simp]
theorem ker_pow_log (u : End R V) (hu : IsNilpotent (u - 1)) (k : ℕ) :
    LinearMap.ker (log u ^ k) = LinearMap.ker ((u - 1) ^ k) := by
  -- Rational scalars act on endomorphisms even when they do not act on the coefficient semiring.
  let : Algebra ℚ (End R V) :=
    Algebra.ofModule smul_mul_assoc fun r f g => (smul_comm r f g).symm
  simpa only [exp_log hu] using (ker_pow_exp_sub_one (log u) (isNilpotent_log hu) k).symm

/-- Taking the finite logarithm preserves every range in the unipotent filtration. -/
@[simp]
theorem range_pow_log (u : End R V) (hu : IsNilpotent (u - 1)) (k : ℕ) :
    LinearMap.range (log u ^ k) = LinearMap.range ((u - 1) ^ k) := by
  -- Use the rational action on endomorphisms, not on the coefficient semiring.
  let : Algebra ℚ (End R V) :=
    Algebra.ofModule smul_mul_assoc fun r f g => (smul_comm r f g).symm
  simpa only [exp_log hu] using (range_pow_exp_sub_one (log u) (isNilpotent_log hu) k).symm

section FiniteDimensional

variable {K : Type*} [Field K] [Module K V] [FiniteDimensional K V]

/-- The unipotent exponential of a nilpotent endomorphism has the same Jordan block sizes:
the nilpotent endomorphisms `exp f - 1` and `f` have equal Jordan partitions. -/
@[simp]
theorem jordanPartition_exp_sub_one (f : End K V) (hf : IsNilpotent f) :
    (exp f - 1).jordanPartition (isNilpotent_exp_sub_one hf) = f.jordanPartition hf := by
  apply Nat.Partition.ext
  exact (jordanPartition_parts_eq_iff _ _ _ _).2 fun k => by rw [ker_pow_exp_sub_one f hf]

/-- The nilpotent logarithm of a unipotent endomorphism has the same Jordan block sizes
as its difference from the identity. -/
@[simp]
theorem jordanPartition_log (u : End K V) (hu : IsNilpotent (u - 1)) :
    (log u).jordanPartition (isNilpotent_log hu) = (u - 1).jordanPartition hu := by
  apply Nat.Partition.ext
  exact (jordanPartition_parts_eq_iff _ _ _ _).2 fun k => by rw [ker_pow_log u hu]

/-- The difference between a nilpotent endomorphism's exponential and the identity is
conjugate to the original endomorphism. -/
theorem exists_linearEquiv_conj_exp_sub_one (f : End K V) (hf : IsNilpotent f) :
    ∃ e : V ≃ₗ[K] V, e.conj f = exp f - 1 :=
  (exists_linearEquiv_conj_eq_iff hf (isNilpotent_exp_sub_one hf)).2
    fun k => by rw [ker_pow_exp_sub_one f hf]

/-- The logarithm of a unipotent endomorphism is conjugate to its difference from the identity. -/
theorem exists_linearEquiv_conj_log (u : End K V) (hu : IsNilpotent (u - 1)) :
    ∃ e : V ≃ₗ[K] V, e.conj (u - 1) = log u :=
  (exists_linearEquiv_conj_eq_iff hu (isNilpotent_log hu)).2
    fun k => by rw [ker_pow_log u hu]

end FiniteDimensional

end Module.End
