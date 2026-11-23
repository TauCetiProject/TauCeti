/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-!
# Compatible systems of primitive prime-power roots of unity

A `p`-th root of a primitive `p ^ k`-th root of unity is a primitive `p ^ (k + 1)`-th root of
unity whenever `k ≠ 0`. Iterating a choice of `p`-th roots in an algebraically closed
field therefore produces a sequence `ρ 0, ρ 1, …` with `ρ (n + 1) ^ p = ρ n` and `ρ n` primitive
of order `p ^ (n + 1)`, as soon as `ρ 0` is a primitive `p`-th root of unity. Such a compatible
system fixes generators of all levels of the `p`-power cyclotomic tower over any subfield at
once, so that the norm maps between the levels can be computed on these generators.

The sequence is a choice. Compatible lifts exist but are not unique (the primitive ninth roots
`ζ₉` and `ζ₉⁴` have the same cube `ζ₉³`), and independently chosen primitive roots of the right
orders are in general not compatible.

## Main definitions and results

* `IsPrimitiveRoot.of_pow`: if `ζ ^ p` is a primitive `p ^ k`-th root of unity with `k ≠ 0`,
  then `ζ` is a primitive `p ^ (k + 1)`-th root of unity.
* `TauCeti.compatibleCyclotomicRoot p M`: a chosen sequence of `p`-power roots of unity in `M`.
* `TauCeti.compatibleCyclotomicRoot_succ_pow`: `ρ (n + 1) ^ p = ρ n`.
* `TauCeti.isPrimitiveRoot_compatibleCyclotomicRoot`: `ρ n` is a primitive `p ^ (n + 1)`-th root
  of unity.

## References

* J. Rodrigues Jacinto and C. Williams, *An introduction to p-adic L-functions*, Essential Number
  Theory 4 (2025), §9.
-/

public section

namespace IsPrimitiveRoot

variable {M : Type*} [CommMonoid M] {p k : ℕ} {ζ : M}

/-- A `p`-th root of a primitive `p ^ k`-th root of unity, with `k ≠ 0`, is a primitive
`p ^ (k + 1)`-th root of unity. The exponent `k ≠ 0` is needed: `1` is a `p`-th root of the
primitive first root of unity `1`. -/
theorem of_pow (hk : k ≠ 0) (h : IsPrimitiveRoot (ζ ^ p) (p ^ k)) :
    IsPrimitiveRoot ζ (p ^ (k + 1)) := by
  refine ⟨by rw [pow_succ', pow_mul, h.pow_eq_one], fun l hl ↦ ?_⟩
  obtain ⟨m, rfl⟩ : p ^ k ∣ l := h.dvd_of_pow_eq_one l (by rw [← pow_mul, mul_comm, pow_mul, hl,
    one_pow])
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
  have hm : p ^ (j + 1) ∣ p ^ j * m := h.dvd_of_pow_eq_one _ (by
    rw [← pow_mul, ← mul_assoc, ← pow_succ', hl])
  rcases eq_or_ne p 0 with rfl | hp
  · simp
  rw [pow_succ] at hm
  rw [pow_succ _ (j + 1)]
  exact mul_dvd_mul_left _ (Nat.dvd_of_mul_dvd_mul_left (pow_pos (Nat.pos_of_ne_zero hp) j) hm)

end IsPrimitiveRoot

namespace TauCeti

/-- A chosen compatible system of `p`-power roots of unity in `M`: `ρ 0` is a chosen primitive
`p`-th root of unity and `ρ (n + 1)` is a chosen `p`-th root of `ρ n`. In an algebraically closed
field in which `p` is nonzero, `ρ n` is a primitive `p ^ (n + 1)`-th root of unity
(`isPrimitiveRoot_compatibleCyclotomicRoot`) and `ρ (n + 1) ^ p = ρ n`
(`compatibleCyclotomicRoot_succ_pow`). -/
noncomputable def compatibleCyclotomicRoot (p : ℕ) (M : Type*) [CommMonoid M] : ℕ → M
  | 0 => Classical.epsilon fun z : M => IsPrimitiveRoot z p
  | n + 1 => Classical.epsilon fun w : M => w ^ p = compatibleCyclotomicRoot p M n

variable {p : ℕ}

/-- The level-zero root is the chosen primitive `p`-th root of unity. -/
theorem compatibleCyclotomicRoot_zero (M : Type*) [CommMonoid M] :
    compatibleCyclotomicRoot p M 0 = Classical.epsilon fun z : M => IsPrimitiveRoot z p :=
  (rfl)

/-- The root at level `n + 1` is the chosen `p`-th root of the root at level `n`. -/
theorem compatibleCyclotomicRoot_succ (M : Type*) [CommMonoid M] (n : ℕ) :
    compatibleCyclotomicRoot p M (n + 1) =
      Classical.epsilon fun w : M => w ^ p = compatibleCyclotomicRoot p M n :=
  (rfl)

/-- The chosen level-zero root is a primitive `p`-th root of unity whenever one exists. -/
theorem isPrimitiveRoot_compatibleCyclotomicRoot_zero {M : Type*} [CommMonoid M]
    [HasEnoughRootsOfUnity M p] : IsPrimitiveRoot (compatibleCyclotomicRoot p M 0) p := by
  rw [compatibleCyclotomicRoot_zero]
  exact Classical.epsilon_spec (HasEnoughRootsOfUnity.exists_isPrimitiveRoot M p)

/-- For `p = 2` the chosen level-zero root is `-1`. -/
theorem compatibleCyclotomicRoot_two_zero {R : Type*} [CommRing R] [NoZeroDivisors R]
    [HasEnoughRootsOfUnity R 2] : compatibleCyclotomicRoot 2 R 0 = -1 :=
  isPrimitiveRoot_compatibleCyclotomicRoot_zero.eq_neg_one_of_two_right

variable {K : Type*} [Field K] [IsAlgClosed K]

/-- Consecutive chosen roots are compatible: `ρ (n + 1) ^ p = ρ n`. -/
@[simp]
theorem compatibleCyclotomicRoot_succ_pow [NeZero p] (n : ℕ) :
    compatibleCyclotomicRoot p K (n + 1) ^ p = compatibleCyclotomicRoot p K n := by
  rw [compatibleCyclotomicRoot_succ K n]
  exact Classical.epsilon_spec (IsAlgClosed.exists_pow_nat_eq _ (Nat.pos_of_neZero p))

/-- The chosen roots are compatible across several levels: `ρ (n + k) ^ (p ^ k) = ρ n`. -/
theorem compatibleCyclotomicRoot_add_pow [NeZero p] (n k : ℕ) :
    compatibleCyclotomicRoot p K (n + k) ^ (p ^ k) = compatibleCyclotomicRoot p K n := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [← add_assoc, pow_succ', pow_mul, compatibleCyclotomicRoot_succ_pow, ih]

/-- The chosen root at level `n` is a primitive `p ^ (n + 1)`-th root of unity. Level zero has
order `p`, not `1`. -/
theorem isPrimitiveRoot_compatibleCyclotomicRoot [NeZero (p : K)] (n : ℕ) :
    IsPrimitiveRoot (compatibleCyclotomicRoot p K n) (p ^ (n + 1)) := by
  induction n with
  | zero => simpa using isPrimitiveRoot_compatibleCyclotomicRoot_zero
  | succ n ih =>
    have : NeZero p := .of_neZero_natCast K
    rw [← compatibleCyclotomicRoot_succ_pow (K := K) n] at ih
    exact ih.of_pow n.succ_ne_zero

end TauCeti
