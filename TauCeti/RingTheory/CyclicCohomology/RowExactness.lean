/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.CyclicCohomology.ConnesOperator
import Mathlib.Algebra.Ring.GeomSum

/-!
# Split exactness of the rows of the cyclic bicomplex

In degree `n`, write `λ` for the signed cyclic operator and `N = 1 + λ + ⋯ + λⁿ`.
When `n + 1` is invertible in the coefficient ring, averaging gives a projection
`P = N / (n + 1)` onto the cyclic cochains. The operator
`H = (∑ j ≤ n, ∑ k < j, λᵏ) / (n + 1)` satisfies
`(1 - λ) H = H (1 - λ) = 1 - P`.

Consequently the row alternating between `1 - λ` and `N` is exact at both kinds
of terms: `range N = ker (1 - λ)` and `range (1 - λ) = ker N`.
These explicit splittings are used to compare the cyclic cochain complex with
the total cyclic bicomplex. No multiplication or unit on the argument module is
needed for these horizontal identities.

## References

* A. Connes, *Noncommutative Geometry*, Chapter III, §1.
* J.-L. Loday, *Cyclic Homology*, §2.1.
-/

public section

namespace TauCeti

variable (R A M : Type*)

section Semiring

variable [Semiring R] [AddCommMonoid A] [Module R A] [AddCommGroup M] [Module R M]
  [SMulCommClass R R M]

/-- On a cyclic cochain, the cyclic norm is multiplication by the number of arguments. -/
theorem cyclicNorm_apply_of_mem_cyclicCochains {n : ℕ}
    {φ : MultilinearMap R (fun _ : Fin (n + 1) ↦ A) M}
    (hφ : φ ∈ cyclicCochains R A M n) :
    cyclicNorm R A M n φ = (n + 1 : R) • φ := by
  have hfix := mem_cyclicCochains_iff_cyclicOperator_apply_eq_self.1 hφ
  simp only [cyclicNorm_def, LinearMap.sum_apply, Module.End.pow_apply,
    Function.iterate_fixed hfix]
  rw [Finset.sum_const, Finset.card_range, ← Nat.cast_smul_eq_nsmul R,
    Nat.cast_add, Nat.cast_one]

/-- The fixed-point submodule of the cyclic operator is the kernel of `1 - λ`. -/
theorem ker_one_sub_cyclicOperator (n : ℕ) :
    LinearMap.ker (1 - cyclicOperator R A M n) = cyclicCochains R A M n := by
  ext φ
  simp only [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero,
    mem_cyclicCochains_iff_cyclicOperator_apply_eq_self]
  exact eq_comm

end Semiring

variable [CommRing R] [AddCommMonoid A] [Module R A] [AddCommGroup M] [Module R M]
  (n : ℕ) [Invertible (n + 1 : R)]

/-- Averaging over cyclic rotations projects onto the cyclic cochains. -/
noncomputable def cyclicAverage :
    Module.End R (MultilinearMap R (fun _ : Fin (n + 1) ↦ A) M) :=
  ⅟(n + 1 : R) • cyclicNorm R A M n

/-- The cyclic average is the cyclic norm divided by the number of arguments. -/
-- Keep averaging intact under simplification so its projection identities remain normal forms.
theorem cyclicAverage_apply (φ : MultilinearMap R (fun _ : Fin (n + 1) ↦ A) M) :
    cyclicAverage R A M n φ = ⅟(n + 1 : R) • cyclicNorm R A M n φ := (rfl)

/-- Averaging takes values in the cyclic cochains. -/
theorem cyclicAverage_mem_cyclicCochains
    (φ : MultilinearMap R (fun _ : Fin (n + 1) ↦ A) M) :
    cyclicAverage R A M n φ ∈ cyclicCochains R A M n :=
  (cyclicCochains R A M n).smul_mem _ (cyclicNorm_mem_cyclicCochains φ)

/-- Averaging fixes every cyclic cochain. -/
theorem cyclicAverage_apply_of_mem_cyclicCochains
    {φ : MultilinearMap R (fun _ : Fin (n + 1) ↦ A) M}
    (hφ : φ ∈ cyclicCochains R A M n) : cyclicAverage R A M n φ = φ := by
  rw [cyclicAverage_apply, cyclicNorm_apply_of_mem_cyclicCochains R A M hφ,
    invOf_smul_smul]

/-- The cyclic average is idempotent. -/
@[simp]
theorem cyclicAverage_cyclicAverage
    (φ : MultilinearMap R (fun _ : Fin (n + 1) ↦ A) M) :
    cyclicAverage R A M n (cyclicAverage R A M n φ) = cyclicAverage R A M n φ :=
  cyclicAverage_apply_of_mem_cyclicCochains R A M n
    (cyclicAverage_mem_cyclicCochains R A M n φ)

/-- The image of averaging is exactly the cyclic cochains. -/
theorem range_cyclicAverage :
    LinearMap.range (cyclicAverage R A M n) = cyclicCochains R A M n := by
  apply le_antisymm
  · rintro _ ⟨φ, rfl⟩
    exact cyclicAverage_mem_cyclicCochains R A M n φ
  · intro φ hφ
    exact ⟨φ, cyclicAverage_apply_of_mem_cyclicCochains R A M n hφ⟩

/-- The cyclic row homotopy. Its product with `1 - λ` on either side is `1 - P`,
where `P` is cyclic averaging. -/
noncomputable def cyclicRowHomotopy :
    Module.End R (MultilinearMap R (fun _ : Fin (n + 1) ↦ A) M) :=
  ⅟(n + 1 : R) • ∑ j ∈ Finset.range (n + 1),
    ∑ k ∈ Finset.range j, cyclicOperator R A M n ^ k

/-- The explicit finite-sum formula for the cyclic row homotopy. -/
theorem cyclicRowHomotopy_def :
    cyclicRowHomotopy R A M n = ⅟(n + 1 : R) •
      ∑ j ∈ Finset.range (n + 1), ∑ k ∈ Finset.range j, cyclicOperator R A M n ^ k :=
  (rfl)

/-- The row homotopy splits `1 - λ` on the left, up to the cyclic projection. -/
theorem one_sub_cyclicOperator_mul_cyclicRowHomotopy :
    (1 - cyclicOperator R A M n) * cyclicRowHomotopy R A M n =
      1 - cyclicAverage R A M n := by
  rw [cyclicRowHomotopy_def, mul_smul_comm, Finset.mul_sum]
  simp only [mul_neg_geom_sum, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_range, ← cyclicNorm_def]
  rw [smul_sub, ← Nat.cast_smul_eq_nsmul R, Nat.cast_add, Nat.cast_one,
    invOf_smul_smul, cyclicAverage]

/-- The row homotopy splits `1 - λ` on the right, up to the cyclic projection. -/
theorem cyclicRowHomotopy_mul_one_sub_cyclicOperator :
    cyclicRowHomotopy R A M n * (1 - cyclicOperator R A M n) =
      1 - cyclicAverage R A M n := by
  rw [cyclicRowHomotopy_def, smul_mul_assoc, Finset.sum_mul]
  simp only [geom_sum_mul_neg, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_range, ← cyclicNorm_def]
  rw [smul_sub, ← Nat.cast_smul_eq_nsmul R, Nat.cast_add, Nat.cast_one,
    invOf_smul_smul, cyclicAverage]

/-- The cyclic norm surjects onto the cyclic cochains. -/
theorem range_cyclicNorm :
    LinearMap.range (cyclicNorm R A M n) = cyclicCochains R A M n := by
  apply le_antisymm
  · rintro _ ⟨φ, rfl⟩
    exact cyclicNorm_mem_cyclicCochains φ
  · intro φ hφ
    refine ⟨⅟(n + 1 : R) • φ, ?_⟩
    rw [map_smul, cyclicNorm_apply_of_mem_cyclicCochains R A M hφ, invOf_smul_smul]

/-- Exactness of a cyclic-bicomplex row at a term following `N`. -/
theorem range_cyclicNorm_eq_ker_one_sub_cyclicOperator :
    LinearMap.range (cyclicNorm R A M n) =
      LinearMap.ker (1 - cyclicOperator R A M n) := by
  rw [range_cyclicNorm R A M n, ker_one_sub_cyclicOperator]

/-- Exactness of a cyclic-bicomplex row at a term following `1 - λ`.
For a cochain killed by `N`, the row homotopy gives an explicit preimage. -/
theorem range_one_sub_cyclicOperator_eq_ker_cyclicNorm :
    LinearMap.range (1 - cyclicOperator R A M n) =
      LinearMap.ker (cyclicNorm R A M n) := by
  apply le_antisymm
  · rintro _ ⟨φ, rfl⟩
    simp only [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, map_sub]
    rw [← Module.End.mul_apply, cyclicNorm_mul_cyclicOperator, sub_self]
  · intro φ hφ
    refine ⟨cyclicRowHomotopy R A M n φ, ?_⟩
    have h := LinearMap.congr_fun
      (one_sub_cyclicOperator_mul_cyclicRowHomotopy R A M n) φ
    simpa [Module.End.mul_apply, cyclicAverage_apply, LinearMap.mem_ker.1 hφ] using h

end TauCeti
