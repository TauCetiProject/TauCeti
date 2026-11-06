/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.TypeAHeckeAlgebra.CosetBasis
public import TauCeti.Algebra.TypeAHeckeAlgebra.CosetSpanning
public import TauCeti.Algebra.TypeAHeckeAlgebra.MarkovTrace

/-!
# Cycle words

Write `gᵢ = q • T i`, so that `(gᵢ + 1) * (gᵢ - q²) = 0`. The cycle word on `m` strands is
`ζₘ = g_(m-2) * ⋯ * g_0`, with strands counted from `0` (in one-based notation
`ζₘ = g_(m-1) ⋯ g_1`), and `ζ₁ = 1`. It lies in the stage of the first `m` strands, and is the
element `q ^ (m - 1) • T_w` attached to the `m`-cycle `w = s_(m-2) ⋯ s_0`, although that
identification is not needed here. Every descending product `T (n - 1) * ⋯ * T a` is a rescaled
strand shift of a cycle word (`TauCeti.InfiniteTypeAHeckeAlgebra.cosetRep_eq_smul_shift_cycleWord`).

A Markov trace with parameter `z` takes the value `(q * z) ^ (m - 1)` on `ζₘ`
(`TauCeti.InfiniteTypeAHeckeAlgebra.IsMarkovTrace.map_cycleWord`). The cycle words determine
every tracial, block-multiplicative functional, and so in particular the Markov traces; this is
proved with the cocenter of the stages, in `TauCeti.Algebra.TypeAHeckeAlgebra.Cocenter`.

The same word in the Hecke algebra presented on `m` strands is
`TauCeti.TypeAHeckeAlgebra.cycleWord`, built from the descending last-strand words
`TauCeti.TypeAHeckeAlgebra.cosetWord`. It is the cycle word on which functionals defined only on
the finite algebras, such as weighted traces of tensor representations, are evaluated, and its
image in the infinite algebra is `ζₘ` (`TauCeti.TypeAHeckeAlgebra.toInfinite_cycleWord`).

## Main definitions

* `TauCeti.InfiniteTypeAHeckeAlgebra.cycleWord`: the cycle word `ζₘ`.
* `TauCeti.TypeAHeckeAlgebra.cycleWord`: the cycle word in the Hecke algebra on `m` strands.

## Main results

* `TauCeti.InfiniteTypeAHeckeAlgebra.cosetRep_eq_smul_shift_cycleWord`: descending products are
  rescaled shifted cycle words.
* `TauCeti.InfiniteTypeAHeckeAlgebra.IsMarkovTrace.map_cosetRep` and
  `TauCeti.InfiniteTypeAHeckeAlgebra.IsMarkovTrace.map_cycleWord`: the values of a Markov trace on
  descending products and on cycle words.
* `TauCeti.TypeAHeckeAlgebra.cycleWord_add_two` and
  `TauCeti.TypeAHeckeAlgebra.toInfinite_cycleWord`: the recursion of the finite cycle words and
  their images in the infinite algebra.

## References

* A. Ram, *A Frobenius formula for the characters of the Hecke algebras*, Invent. Math. 106
  (1991), 461–488, for the cycle words `g_(m-1) ⋯ g_1` on consecutive blocks.
-/

public section

namespace TauCeti

namespace InfiniteTypeAHeckeAlgebra

variable {R : Type*} [CommRing R] {q : Rˣ}

section CycleWord

variable (q) in
/-- The cycle word `ζₘ = q ^ (m - 1) • T (m - 2) * ⋯ * T 0`, the product `g_(m-2) * ⋯ * g_0` of
the rescaled generators `gᵢ = q • T i` that cross two of the first `m` strands, in descending
order. In one-based notation it is `g_(m-1) ⋯ g_1`. It is `1` on at most one strand. -/
def cycleWord (m : ℕ) : InfiniteTypeAHeckeAlgebra R q :=
  (q : R) ^ (m - 1) • cosetRep q (m - 1) 0

/-- The cycle word is the rescaled descending product of the generators. -/
theorem cycleWord_def (m : ℕ) : cycleWord q m = (q : R) ^ (m - 1) • cosetRep q (m - 1) 0 := (rfl)

/-- The cycle word on no strands is `1`. -/
@[simp]
theorem cycleWord_zero : cycleWord q 0 = 1 := by
  simp [cycleWord_def]

/-- The cycle word on one strand is `1`. -/
@[simp]
theorem cycleWord_one : cycleWord q 1 = 1 := by
  simp [cycleWord_def]

/-- The cycle word on `m + 2` strands is `g_m * ζₘ₊₁`, where `g_m = q • T m`. -/
theorem cycleWord_add_two (m : ℕ) :
    cycleWord q (m + 2) = ((q : R) • T q m) * cycleWord q (m + 1) := by
  rw [cycleWord_def, cycleWord_def, Nat.add_sub_cancel, Nat.add_succ_sub_one,
    cosetRep_succ (Nat.zero_le m), smul_mul_smul, pow_succ']

/-- The cycle word on `m` strands lies in the stage of the first `m` strands. -/
theorem cycleWord_mem_stage (m : ℕ) : cycleWord q m ∈ stage R q m := by
  rcases m with _ | m
  · rw [cycleWord_zero]
    exact one_mem _
  · rw [cycleWord_def, Nat.add_sub_cancel]
    exact Subalgebra.smul_mem _ (cosetRep_mem_stage _ _) _

/-- The descending product `T (n - 1) * ⋯ * T a` is the rescaled shift by `a` of the cycle word
on `n + 1 - a` strands. -/
theorem cosetRep_eq_smul_shift_cycleWord {a n : ℕ} (han : a ≤ n) :
    cosetRep q n a = (↑q⁻¹ : R) ^ (n - a) • shift R q a (cycleWord q (n + 1 - a)) := by
  simp [cycleWord_def, show n + 1 - a - 1 = n - a by omega, Nat.sub_add_cancel han, smul_smul,
    ← mul_pow]

end CycleWord

namespace IsMarkovTrace

variable {z : R} {τ : InfiniteTypeAHeckeAlgebra R q →ₗ[R] R}

/-- A Markov trace with parameter `z` takes the value `z ^ (n - m)` on the descending product
`T (n - 1) * ⋯ * T m`. -/
theorem map_cosetRep (hτ : IsMarkovTrace z τ) (n m : ℕ) : τ (cosetRep q n m) = z ^ (n - m) := by
  rcases le_or_gt n m with h | h
  · rw [cosetRep_of_le h, hτ.map_one, Nat.sub_eq_zero_of_le h, pow_zero]
  induction n, h using Nat.le_induction with
  | base =>
    rw [cosetRep_succ le_rfl, cosetRep_self, mul_one, ← one_mul (T q m),
      hτ.map_mul_T (one_mem _), hτ.map_one, mul_one]
    simp
  | succ n hn ih =>
    rw [cosetRep_succ (by omega), hτ.map_mul_comm, hτ.map_mul_T (cosetRep_mem_stage n m), ih,
      ← pow_succ', Nat.sub_add_comm (by omega)]

/-- A Markov trace with parameter `z` takes the value `(q * z) ^ (m - 1)` on the cycle word
`ζₘ`. -/
theorem map_cycleWord (hτ : IsMarkovTrace z τ) (m : ℕ) :
    τ (cycleWord q m) = ((q : R) * z) ^ (m - 1) := by
  rw [cycleWord_def, map_smul, hτ.map_cosetRep, Nat.sub_zero, smul_eq_mul, mul_pow]

end IsMarkovTrace

end InfiniteTypeAHeckeAlgebra

namespace TypeAHeckeAlgebra

variable {R : Type*} [CommRing R]

variable (q : Rˣ) in
/-- The cycle word `ζₘ = q ^ (m - 1) • T (m - 2) * ⋯ * T 0` in the Hecke algebra on `m` strands,
the product `g_(m-2) * ⋯ * g_0` of the rescaled generators `gᵢ = q • T i` in descending order. It
is `1` on at most one strand. -/
def cycleWord : (m : ℕ) → TypeAHeckeAlgebra R q m
  | 0 => 1
  | m + 1 => (q : R) ^ m • cosetWord q m 0

variable {q : Rˣ}

/-- The cycle word on no strands is `1`. -/
@[simp]
theorem cycleWord_zero : cycleWord q 0 = 1 := (rfl)

/-- The cycle word on `m + 1` strands is the rescaled descending word `T (m - 1) * ⋯ * T 0`. -/
theorem cycleWord_succ (m : ℕ) : cycleWord q (m + 1) = (q : R) ^ m • cosetWord q m 0 := (rfl)

/-- The cycle word on one strand is `1`. -/
@[simp]
theorem cycleWord_one : cycleWord q 1 = 1 := by
  simp [cycleWord_succ]

/-- The cycle word on `m + 2` strands is `g_m` times the cycle word on the first `m + 1` strands,
where `g_m = q • T m` crosses the last two strands. -/
theorem cycleWord_add_two (m : ℕ) :
    cycleWord q (m + 2) =
      ((q : R) • T q (Fin.last m)) * strandIncl R q (m + 1) (cycleWord q (m + 1)) := by
  rw [cycleWord_succ, cycleWord_succ, ← Fin.castSucc_zero, cosetWord_castSucc, map_smul,
    smul_mul_smul, pow_succ']

/-- The embedding in the infinite algebra sends the finite cycle word to the cycle word `ζₘ`. -/
@[simp]
theorem toInfinite_cycleWord (m : ℕ) :
    toInfinite R q m (cycleWord q m) = InfiniteTypeAHeckeAlgebra.cycleWord q m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rcases m with _ | m
    · simp
    · rw [cycleWord_add_two, InfiniteTypeAHeckeAlgebra.cycleWord_add_two, map_mul,
        toInfinite_strandIncl, ih, map_smul, toInfinite_T, Fin.val_last]

end TypeAHeckeAlgebra

end TauCeti
