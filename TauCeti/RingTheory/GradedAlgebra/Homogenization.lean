/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.GradedAlgebra.Basic

/-!
# Homogenization in `ℕ`-graded rings

Let `A` be a semiring graded by `𝒜 : ℕ → σ`, and let `t ∈ 𝒜 1` be a homogeneous element of degree
one. Any element `a : A` can be homogenized against `t` by taking a common degree `n` above the
support of `a` and multiplying each degree-`i` homogeneous component `aᵢ` by `t ^ (n - i)`. The
resulting sum `P` lies in `𝒜 n`, and every ring homomorphism `φ : A →+* B` sending `t` to `1`
agrees on `P` and `a`.

Applied to `SymmetricAlgebra R (Module.Dual R (M × R))` with `t` the coordinate projection onto the
trivial factor `R`, this lifts any polynomial function on `M` to a homogeneous polynomial on
`M × R` with the same values on the affine chart `{(u, 1) | u ∈ M}`.

## Main results

* `TauCeti.GradedAlgebra.exists_mem_grade_and_forall_map_eq_of_mem_one`: every element of an
  `ℕ`-graded semiring homogenizes against any degree-one element `t ∈ 𝒜 1` to a homogeneous
  element agreeing with it under all ring homomorphisms sending `t` to `1`.
-/

public section

namespace TauCeti.GradedAlgebra

open DirectSum

universe u v w

variable {A : Type u} {σ : Type v} [Semiring A] [SetLike σ A] [AddSubmonoidClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- **Homogenization in an `ℕ`-graded semiring.** Given a degree-one homogeneous element
`t ∈ 𝒜 1` and an element `a : A`, there exist a degree `n` and a homogeneous element `P ∈ 𝒜 n`
such that every ring homomorphism `φ : A →+* B` with `φ t = 1` satisfies `φ P = φ a`. -/
theorem exists_mem_grade_and_forall_map_eq_of_mem_one {t : A} (ht : t ∈ 𝒜 1) (a : A) :
    ∃ n : ℕ, ∃ P ∈ 𝒜 n, ∀ {B : Type w} [Semiring B] (φ : A →+* B), φ t = 1 → φ P = φ a := by
  classical
  let n : ℕ := (decompose 𝒜 a).support.sup id
  refine ⟨n, ∑ i ∈ (decompose 𝒜 a).support, (decompose 𝒜 a i : A) * t ^ (n - i), ?_, ?_⟩
  · refine sum_mem fun i hi ↦ ?_
    have hin : i ≤ n := Finset.le_sup (f := id) hi
    have hti : t ^ (n - i) ∈ 𝒜 (n - i) := by simpa using SetLike.pow_mem_graded (n - i) ht
    have hmul := SetLike.mul_mem_graded (SetLike.coe_mem (decompose 𝒜 a i)) hti
    rwa [Nat.add_sub_of_le hin] at hmul
  · intro B _ φ hφ
    conv_rhs => rw [← sum_support_decompose 𝒜 a]
    simp [map_sum, map_mul, map_pow, hφ]

end TauCeti.GradedAlgebra
