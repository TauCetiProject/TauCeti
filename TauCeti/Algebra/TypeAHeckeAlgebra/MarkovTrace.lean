/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.TypeAHeckeAlgebra.Infinite

/-!
# Markov traces on the infinite type-A Hecke algebra

A Markov trace with parameter `z : R` on the infinite type-A Hecke algebra
`TauCeti.InfiniteTypeAHeckeAlgebra R q` is an `R`-linear functional `τ` with

* `τ 1 = 1`,
* `τ (x * y) = τ (y * x)`, and
* the Markov rule `τ (x * T n) = z * τ x` for `x` in the stage of the first `n + 1` strands:
  the generator `T n` adds the new strand `n + 1`.

Since the infinite algebra is the union of its stages, such a functional is the same as a family
of compatible normalized traces on the stages. Ocneanu's theorem (Jones, Theorem 5.1) asserts
that there is exactly one Markov trace for every `z`, the Ocneanu trace. This file proves the
uniqueness half, and the multiplicativity of every Markov trace on disjoint blocks of strands;
existence needs the basis theorem for the stages and is not proved here. Both results follow
from the decomposition `Hₙ₊₂ = Hₙ₊₁ + Hₙ₊₁ Tₙ Hₙ₊₁` of the stages
(`TauCeti.InfiniteTypeAHeckeAlgebra.toSubmodule_stage_add_two`), along which the Markov rule
computes `τ (a * T n * b) = z * τ (b * a)`.

The characters `T i ↦ q` and `T i ↦ -q⁻¹` are Markov traces with parameters `q` and `-q⁻¹`, so by
uniqueness they are the Ocneanu traces for these two values of `z`.

## Main definitions

* `TauCeti.InfiniteTypeAHeckeAlgebra.IsMarkovTrace`: the predicate that a linear functional is a
  Markov trace with parameter `z`.

## Main results

* `TauCeti.InfiniteTypeAHeckeAlgebra.IsMarkovTrace.map_mul_T_mul`: the recursive rule
  `τ (a * T n * b) = z * τ (b * a)`.
* `TauCeti.InfiniteTypeAHeckeAlgebra.IsMarkovTrace.unique`: there is at most one Markov trace with
  a given parameter.
* `TauCeti.InfiniteTypeAHeckeAlgebra.IsMarkovTrace.map_mul_shift`: block multiplicativity,
  `τ (x * shift a y) = τ x * τ y` for `x` in the stage of the first `a` strands.
* `TauCeti.InfiniteTypeAHeckeAlgebra.isMarkovTrace_indexCharacter` and
  `TauCeti.InfiniteTypeAHeckeAlgebra.isMarkovTrace_signCharacter`: the two characters are Markov
  traces.

## References

* V. F. R. Jones, *Hecke algebra representations of braid groups and link polynomials*,
  Ann. of Math. 126 (1987), 335–388, Section 5 (Theorem 5.1 and its proof).
-/

public section

namespace TauCeti

namespace InfiniteTypeAHeckeAlgebra

variable {R : Type*} [CommRing R] {q : Rˣ}

/-- A Markov trace with parameter `z` on the infinite type-A Hecke algebra: an `R`-linear
functional which is normalized, tracial, and satisfies the Markov rule `τ (x * T n) = z * τ x` for
every `x` in the stage of the first `n + 1` strands. -/
structure IsMarkovTrace (z : R) (τ : InfiniteTypeAHeckeAlgebra R q →ₗ[R] R) : Prop where
  /-- A Markov trace is normalized. -/
  map_one : τ 1 = 1
  /-- A Markov trace is tracial. -/
  map_mul_comm (x y : InfiniteTypeAHeckeAlgebra R q) : τ (x * y) = τ (y * x)
  /-- The Markov rule: multiplying by the generator that adds a new last strand multiplies the
  trace by `z`. -/
  map_mul_T {n : ℕ} {x : InfiniteTypeAHeckeAlgebra R q} (hx : x ∈ stage R q (n + 1)) :
    τ (x * T q n) = z * τ x

namespace IsMarkovTrace

variable {z : R} {τ : InfiniteTypeAHeckeAlgebra R q →ₗ[R] R}

/-- A Markov trace takes the scalar `r` to `r`. -/
theorem map_algebraMap (hτ : IsMarkovTrace z τ) (r : R) : τ (algebraMap R _ r) = r := by
  rw [Algebra.algebraMap_eq_smul_one, map_smul, hτ.map_one, smul_eq_mul, mul_one]

/-- The recursive rule for a Markov trace: for `a` and `b` in the stage of the first `n + 1`
strands, `τ (a * T n * b) = z * τ (b * a)`. -/
theorem map_mul_T_mul (hτ : IsMarkovTrace z τ) {n : ℕ} {a b : InfiniteTypeAHeckeAlgebra R q}
    (ha : a ∈ stage R q (n + 1)) (hb : b ∈ stage R q (n + 1)) :
    τ (a * T q n * b) = z * τ (b * a) := by
  rw [hτ.map_mul_comm, ← mul_assoc, hτ.map_mul_T (mul_mem hb ha)]

/-- **Uniqueness of the Ocneanu trace.** Two Markov traces with the same parameter are equal. -/
theorem unique {τ' : InfiniteTypeAHeckeAlgebra R q →ₗ[R] R} (hτ : IsMarkovTrace z τ)
    (hτ' : IsMarkovTrace z τ') : τ = τ' :=
  LinearMap.ext fun x ↦ LinearMap.mem_eqLocus.1 <| Submodule.eq_top_iff'.1
    (eq_top_of_algebraMap_mem_of_mul_T_mul_mem
      (fun r ↦ LinearMap.mem_eqLocus.2 <| by rw [hτ.map_algebraMap, hτ'.map_algebraMap])
      (fun _ ih a ha b hb ↦ LinearMap.mem_eqLocus.2 <| by
        rw [hτ.map_mul_T_mul ha hb, hτ'.map_mul_T_mul ha hb, LinearMap.mem_eqLocus.1 <|
          ih ((Subalgebra.mem_toSubmodule _).2 (mul_mem hb ha))])) x

/-- **Block multiplicativity.** A Markov trace is multiplicative on disjoint blocks of strands:
for `x` in the stage of the first `a` strands and any `y`, whose shift by `a` lives on the strands
from `a` on, `τ (x * shift a y) = τ x * τ y`. By
`TauCeti.InfiniteTypeAHeckeAlgebra.coe_blockIncl_tmul`, this is the multiplicativity of `τ` along
the disjoint block map `TauCeti.InfiniteTypeAHeckeAlgebra.blockIncl`. -/
theorem map_mul_shift (hτ : IsMarkovTrace z τ) {a : ℕ} {x : InfiniteTypeAHeckeAlgebra R q}
    (hx : x ∈ stage R q a) (y : InfiniteTypeAHeckeAlgebra R q) :
    τ (x * shift R q a y) = τ x * τ y := by
  -- Both sides are linear in `y`; compare them on scalars and along `Hₙ₊₂ = Hₙ₊₁ + Hₙ₊₁ Tₙ Hₙ₊₁`.
  let f : InfiniteTypeAHeckeAlgebra R q →ₗ[R] R :=
    τ ∘ₗ LinearMap.mulLeft R x ∘ₗ (shift R q a).toLinearMap
  have hf : ∀ y, f y = τ (x * shift R q a y) := fun _ ↦ rfl
  refine (hf y).symm.trans <| LinearMap.mem_eqLocus.1 <| Submodule.eq_top_iff'.1
    (eq_top_of_algebraMap_mem_of_mul_T_mul_mem (P := LinearMap.eqLocus f (τ x • τ))
      (fun r ↦ LinearMap.mem_eqLocus.2 ?_) (fun n ih d hd e he ↦ LinearMap.mem_eqLocus.2 ?_)) y
  · simp [hf, Algebra.algebraMap_eq_smul_one, hτ.map_one, mul_comm]
  · have hd' : shift R q a d ∈ stage R q (n + a + 1) :=
      stage_mono (by omega) (shift_mem_stage a hd)
    have he' : shift R q a e ∈ stage R q (n + a + 1) :=
      stage_mono (by omega) (shift_mem_stage a he)
    have hed : τ (x * shift R q a (e * d)) = τ x * τ (e * d) :=
      LinearMap.mem_eqLocus.1 (ih ((Subalgebra.mem_toSubmodule _).2 (mul_mem he hd)))
    rw [hf, LinearMap.smul_apply, smul_eq_mul]
    calc τ (x * shift R q a (d * T q n * e))
        = τ (x * shift R q a d * T q (n + a) * shift R q a e) := by
          simp only [map_mul (shift R q a), shift_T, mul_assoc]
      _ = z * τ (x * shift R q a (e * d)) := by
          rw [hτ.map_mul_T_mul (mul_mem (stage_mono (by omega) hx) hd') he', ← mul_assoc,
            ← (commute_shift_of_mem_stage hx e).eq, mul_assoc, map_mul (shift R q a)]
      _ = τ x * τ (d * T q n * e) := by
          rw [hed, hτ.map_mul_T_mul hd he, mul_left_comm]

end IsMarkovTrace

/-- The index character `T i ↦ q` is a Markov trace with parameter `q`. -/
theorem isMarkovTrace_indexCharacter :
    IsMarkovTrace (q : R) (indexCharacter R q).toLinearMap where
  map_one := map_one (indexCharacter R q)
  map_mul_comm x y := by simp only [AlgHom.toLinearMap_apply, map_mul, mul_comm]
  map_mul_T _ := by simp only [AlgHom.toLinearMap_apply, map_mul, indexCharacter_T, mul_comm]

/-- The sign character `T i ↦ -q⁻¹` is a Markov trace with parameter `-q⁻¹`. -/
theorem isMarkovTrace_signCharacter :
    IsMarkovTrace (-(↑q⁻¹ : R)) (signCharacter R q).toLinearMap where
  map_one := map_one (signCharacter R q)
  map_mul_comm x y := by simp only [AlgHom.toLinearMap_apply, map_mul, mul_comm]
  map_mul_T _ := by simp only [AlgHom.toLinearMap_apply, map_mul, signCharacter_T, mul_comm]

end InfiniteTypeAHeckeAlgebra

end TauCeti
