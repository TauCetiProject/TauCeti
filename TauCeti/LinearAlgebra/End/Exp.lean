/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Nilpotent.Exp
public import TauCeti.Algebra.BigOperators.Finset.Range
public import TauCeti.LinearAlgebra.End.LocallyNilpotent
import Mathlib.Algebra.Module.BigOperators
import TauCeti.LinearAlgebra.End.Basic
import Mathlib.Tactic.FieldSimp

/-!
# The exponential of a locally nilpotent endomorphism

Let `f` be an endomorphism of a module `M` over a semiring `R`, where `M` is also a `ℚ`-vector
space. Call `f` *locally nilpotent* when every vector is killed by some power of `f`, the power
depending on the vector. Then the exponential series

`exp f x = ∑ i, (fⁱ x) / i!`

is a finite sum at every vector, and `Module.End.locallyNilpotentExp f hf` is the resulting
`R`-linear automorphism of `M`. Its inverse is the exponential of `-f`.

Mathlib's `IsNilpotent.exp` exponentiates an element of a `ℚ`-algebra that is nilpotent, so for an
endomorphism it needs a power of `f` killing every vector at once. For nilpotent `f` the two
exponentials agree (`Module.End.locallyNilpotentExp_eq_exp`). Local nilpotence without a uniform
bound is the situation of the adjoint action of a Chevalley generator on a Lie algebra presented by
generators and relations, such as Mathlib's Serre construction `Matrix.ToLieAlgebra`, which is not
known to be finite-dimensional in advance.

## Main definitions

* `Module.End.locallyNilpotentExp`: the exponential of a locally nilpotent endomorphism, as a
  linear automorphism.

## Main results

* `Module.End.locallyNilpotentExp_apply_eq_sum`: at a vector killed by `f ^ k`, the exponential is
  the exponential series truncated at length `k`.
* `Module.End.locallyNilpotentExp_symm_apply_eq_sum`: the inverse is the exponential series of
  `-f`.
* `Module.End.locallyNilpotentExp_eq_exp`: for nilpotent `f` the exponential is
  `IsNilpotent.exp f`.
-/

public section

open Finset

namespace Module.End

variable {R M : Type*} [Semiring R] [AddCommGroup M] [Module R M] [Module ℚ M]
  (f : Module.End R M)

/-- The exponential series of `f` at a vector killed by `f ^ k` does not change when it is
truncated at any length beyond `k`. -/
private theorem sum_range_eq_of_le {x : M} {k l : ℕ} (hk : (f ^ k) x = 0) (hkl : k ≤ l) :
    ∑ i ∈ range l, (i.factorial : ℚ)⁻¹ • (f ^ i) x =
      ∑ i ∈ range k, (i.factorial : ℚ)⁻¹ • (f ^ i) x := by
  rw [← sum_range_add_sum_Ico _ hkl, add_eq_left]
  refine sum_eq_zero fun i hi ↦ ?_
  rw [pow_map_zero_of_le (mem_Ico.1 hi).1 hk, smul_zero]

/-- The coefficients of the product of the exponential series of `-X` and of `X`: the coefficient
of `Xⁿ` is `(1 - 1)ⁿ / n!`. -/
private theorem sum_antidiagonal_neg_one_pow_mul_inv_factorial (n : ℕ) :
    ∑ p ∈ antidiagonal n, (-1 : ℚ) ^ p.1 * ((p.1.factorial : ℚ)⁻¹ * (p.2.factorial : ℚ)⁻¹) =
      if n = 0 then 1 else 0 := by
  have hterm : ∀ m ∈ range (n + 1), (-1 : ℚ) ^ m * ((m.factorial : ℚ)⁻¹ *
      ((n - m).factorial : ℚ)⁻¹) = (n.factorial : ℚ)⁻¹ * ((-1) ^ m * 1 ^ (n - m) * n.choose m) := by
    intro m hm
    have hmn : m ≤ n := Nat.lt_succ_iff.1 (mem_range.1 hm)
    have hfac : (n.choose m : ℚ) * m.factorial * (n - m).factorial = n.factorial := by
      exact_mod_cast Nat.choose_mul_factorial_mul_factorial hmn
    have hc : (n.choose m : ℚ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hmn).ne'
    rw [one_pow, mul_one, ← hfac]
    field_simp
  rw [Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j ↦ (-1 : ℚ) ^ i * ((i.factorial : ℚ)⁻¹ * (j.factorial : ℚ)⁻¹)) n,
    sum_congr rfl hterm, ← mul_sum, ← add_pow, neg_add_cancel]
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · simp [hn]

variable (hf : ∀ x, ∃ n, (f ^ n) x = 0)

/-- The exponential series of `f` at `x`, truncated at some power of `f` that kills `x`. -/
private noncomputable def expFun (x : M) : M :=
  ∑ i ∈ range (hf x).choose, (i.factorial : ℚ)⁻¹ • (f ^ i) x

private theorem expFun_eq_sum {x : M} {k : ℕ} (hk : (f ^ k) x = 0) :
    expFun f hf x = ∑ i ∈ range k, (i.factorial : ℚ)⁻¹ • (f ^ i) x := by
  rw [expFun, ← sum_range_eq_of_le f (hf x).choose_spec (le_max_left _ k),
    sum_range_eq_of_le f hk (le_max_right _ k)]

/-- The truncated exponential series is `R`-linear. -/
private noncomputable def expLinearMap : M →ₗ[R] M where
  toFun := expFun f hf
  map_add' x y := by
    obtain ⟨k, hx⟩ := hf x
    obtain ⟨l, hy⟩ := hf y
    have hx' := pow_map_zero_of_le (le_max_left k l) hx
    have hy' := pow_map_zero_of_le (le_max_right k l) hy
    have hxy : (f ^ max k l) (x + y) = 0 := by rw [map_add, hx', hy', add_zero]
    rw [expFun_eq_sum f hf hx', expFun_eq_sum f hf hy', expFun_eq_sum f hf hxy,
      ← sum_add_distrib]
    simp only [map_add, smul_add]
  map_smul' c x := by
    obtain ⟨k, hx⟩ := hf x
    have hcx : (f ^ k) (c • x) = 0 := by rw [map_smul, hx, smul_zero]
    rw [expFun_eq_sum f hf hx, expFun_eq_sum f hf hcx, RingHom.id_apply, smul_sum]
    exact sum_congr rfl fun i _ ↦ by rw [map_smul, smul_comm]

/-- The exponential series of `-f` inverts that of `f`. The endomorphism `-f` is passed as any `g`
equal to it, so that both composites of the two series are instances. -/
private theorem expFun_expFun_of_eq_neg {g : Module.End R M} (hfg : g = -f)
    (hg : ∀ x, ∃ n, (g ^ n) x = 0) (x : M) : expFun g hg (expFun f hf x) = x := by
  subst hfg
  obtain ⟨k, hk⟩ := hf x
  -- Work with a positive truncation length `K`, so that the term `n = 0` below is present.
  set K := k + 1 with hK
  have hKx : (f ^ K) x = 0 := pow_map_zero_of_le (Nat.le_succ k) hk
  have hpow : ∀ i j, K ≤ i + j → (f ^ (i + j)) x = 0 := fun i j h ↦ pow_map_zero_of_le h hKx
  have hy : ((-f) ^ K) (expFun f hf x) = 0 := by
    rw [neg_pow_apply_eq_zero_iff, expFun_eq_sum f hf hKx, map_sum]
    refine sum_eq_zero fun i _ ↦ ?_
    rw [map_rat_smul, ← Module.End.mul_apply, ← pow_add, add_comm, hpow i K (by omega), smul_zero]
  have hterm : ∀ i j, ((-f) ^ i) ((f ^ j) x) = ((-1 : ℚ) ^ i) • (f ^ (i + j)) x := by
    intro i j
    rw [neg_pow_apply, pow_add, Module.End.mul_apply, ← Int.cast_smul_eq_zsmul ℚ, Int.cast_pow,
      Int.cast_neg, Int.cast_one]
  rw [expFun_eq_sum (-f) hg hy, expFun_eq_sum f hf hKx]
  simp_rw [map_sum, map_rat_smul, hterm, smul_sum, smul_smul]
  rw [← TauCeti.sum_range_add_antidiagonal_of_support K K
    (fun p ↦ ((p.1.factorial : ℚ)⁻¹ * ((p.2.factorial : ℚ)⁻¹ * (-1) ^ p.1)) •
      (f ^ (p.1 + p.2)) x)
    (fun i j h ↦ by rw [hpow i j (by omega), smul_zero])]
  have hn : ∀ n, ∑ p ∈ antidiagonal n,
      ((p.1.factorial : ℚ)⁻¹ * ((p.2.factorial : ℚ)⁻¹ * (-1) ^ p.1)) • (f ^ (p.1 + p.2)) x =
        (if n = 0 then (1 : ℚ) else 0) • (f ^ n) x := by
    intro n
    rw [← sum_antidiagonal_neg_one_pow_mul_inv_factorial, Finset.sum_smul]
    refine sum_congr rfl fun p hp ↦ ?_
    rw [mem_antidiagonal.1 hp]
    congr 1
    ring
  simp_rw [hn, ite_smul, one_smul, zero_smul]
  rw [sum_ite_eq' (range (K + K)) 0]
  simp [K]

/-- **The exponential of a locally nilpotent endomorphism.** If every vector of `M` is killed by
some power of `f`, the exponential series `∑ (fⁱ x) / i!` is a finite sum at every vector `x`, and
it defines an `R`-linear automorphism of `M` whose inverse is the exponential series of `-f`. -/
noncomputable def locallyNilpotentExp : M ≃ₗ[R] M :=
  LinearEquiv.ofLinearMap (expLinearMap f hf)
    (expLinearMap (-f) ((forall_exists_neg_pow_apply_eq_zero_iff f).2 hf))
    (LinearMap.ext fun x ↦
      expFun_expFun_of_eq_neg (-f) ((forall_exists_neg_pow_apply_eq_zero_iff f).2 hf)
        (neg_neg f).symm hf x)
    (LinearMap.ext fun x ↦
      expFun_expFun_of_eq_neg f hf rfl ((forall_exists_neg_pow_apply_eq_zero_iff f).2 hf) x)

/-- **The exponential as a truncated series.** At a vector killed by `f ^ k`, the exponential of
`f` is its exponential series truncated at length `k`. -/
theorem locallyNilpotentExp_apply_eq_sum {x : M} {k : ℕ} (hk : (f ^ k) x = 0) :
    locallyNilpotentExp f hf x = ∑ i ∈ range k, (i.factorial : ℚ)⁻¹ • (f ^ i) x :=
  expFun_eq_sum f hf hk

/-- **The inverse of the exponential.** At a vector killed by `f ^ k`, the inverse of the
exponential of `f` is the exponential series of `-f` truncated at length `k`. -/
theorem locallyNilpotentExp_symm_apply_eq_sum {x : M} {k : ℕ} (hk : (f ^ k) x = 0) :
    (locallyNilpotentExp f hf).symm x = ∑ i ∈ range k, (i.factorial : ℚ)⁻¹ • ((-f) ^ i) x :=
  expFun_eq_sum (-f) ((forall_exists_neg_pow_apply_eq_zero_iff f).2 hf)
    ((neg_pow_apply_eq_zero_iff f k x).2 hk)

/-- For a nilpotent endomorphism, the exponential is Mathlib's `IsNilpotent.exp`. -/
theorem locallyNilpotentExp_eq_exp (hnil : IsNilpotent f) :
    (locallyNilpotentExp f hf : Module.End R M) = IsNilpotent.exp f := by
  obtain ⟨k, hk⟩ := hnil
  ext x
  rw [LinearEquiv.coe_coe, locallyNilpotentExp_apply_eq_sum f hf (by rw [hk]; rfl),
    IsNilpotent.exp_eq_sum hk, LinearMap.sum_apply]
  rfl

end Module.End
