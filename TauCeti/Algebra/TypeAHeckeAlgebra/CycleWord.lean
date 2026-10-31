/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.TypeAHeckeAlgebra.CosetBasis
public import TauCeti.Algebra.TypeAHeckeAlgebra.MarkovTrace

/-!
# Cycle words determine block-multiplicative traces

Write `gᵢ = q • T i`, so that `(gᵢ + 1) * (gᵢ - q²) = 0`. The cycle word on `m` strands is
`ζₘ = g_(m-2) * ⋯ * g_0`, with strands counted from `0` (in one-based notation
`ζₘ = g_(m-1) ⋯ g_1`), and `ζ₁ = 1`. It lies in the stage of the first `m` strands, and is the
element `q ^ (m - 1) • T_w` attached to the `m`-cycle `w = s_(m-2) ⋯ s_0`, although that
identification is not needed here.

A linear functional `τ` on the infinite type-A Hecke algebra is *block multiplicative* when
`τ (x * shift a y) = τ x * τ y` for every `x` in the stage of the first `a` strands and every
`y`: the trace of a product of elements living on disjoint consecutive blocks of strands is the
product of their traces. Markov traces are block multiplicative
(`TauCeti.InfiniteTypeAHeckeAlgebra.IsMarkovTrace.map_mul_shift`).

The main result `TauCeti.InfiniteTypeAHeckeAlgebra.towerTrace_eq_of_cycleChain_values` says that
two tracial, block-multiplicative functionals agree as soon as they agree on every cycle word
`ζₘ`. The block-multiplicativity hypothesis is essential: the values on the cycle words alone
do not determine an arbitrary trace, which may take independent values on products of cycle
words over several blocks. The proof reduces every element, modulo commutators,
to products of cycle words on consecutive blocks of strands, one strand at a time, along the
decomposition `Hₙ₊₂ = Hₙ₊₁ + Hₙ₊₁ Tₙ Hₙ₊₁`
(`TauCeti.InfiniteTypeAHeckeAlgebra.toSubmodule_stage_add_two`). It uses neither the basis
theorem nor any hypothesis on the coefficient ring or on `q`.

A Markov trace with parameter `z` takes the value `(q * z) ^ (m - 1)` on `ζₘ`
(`TauCeti.InfiniteTypeAHeckeAlgebra.IsMarkovTrace.map_cycleWord`). So a tracial,
block-multiplicative functional with these cycle values is the Markov trace with parameter `z`
(`TauCeti.InfiniteTypeAHeckeAlgebra.IsMarkovTrace.eq_of_map_cycleWord`).

## Main definitions

* `TauCeti.InfiniteTypeAHeckeAlgebra.cycleWord`: the cycle word `ζₘ`.

## Main results

* `TauCeti.InfiniteTypeAHeckeAlgebra.towerTrace_eq_of_cycleChain_values`: tracial,
  block-multiplicative functionals agreeing on all cycle words are equal.
* `TauCeti.InfiniteTypeAHeckeAlgebra.IsMarkovTrace.map_cosetRep` and
  `TauCeti.InfiniteTypeAHeckeAlgebra.IsMarkovTrace.map_cycleWord`: the values of a Markov trace on
  descending products and on cycle words.
* `TauCeti.InfiniteTypeAHeckeAlgebra.IsMarkovTrace.eq_of_map_cycleWord`: a tracial,
  block-multiplicative functional with the cycle values of a Markov trace is that Markov trace.

## References

* V. F. R. Jones, *Hecke algebra representations of braid groups and link polynomials*,
  Ann. of Math. 126 (1987), 335–388, Section 5, for the reduction of traces along
  `Hₙ₊₂ = Hₙ₊₁ + Hₙ₊₁ Tₙ Hₙ₊₁`.
* M. Geck and G. Pfeiffer, *Characters of Finite Coxeter Groups and Iwahori-Hecke Algebras*,
  OUP (2000), Section 8.2, where traces are shown to be determined by their values on the
  elements `T_w` of minimal length in their conjugacy classes; in type A these are products of
  cycle words on consecutive blocks.
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
  rw [cycleWord_def, cycleWord_def, show m + 2 - 1 = m + 1 by omega, Nat.add_sub_cancel,
    cosetRep_succ (Nat.zero_le m), smul_mul_smul, pow_succ']

/-- The cycle word on `m` strands lies in the stage of the first `m` strands. -/
theorem cycleWord_mem_stage (m : ℕ) : cycleWord q m ∈ stage R q m := by
  rcases m with _ | m
  · rw [cycleWord_zero]
    exact one_mem _
  · rw [cycleWord_def, Nat.add_sub_cancel]
    exact Subalgebra.smul_mem _ (cosetRep_mem_stage _ _) _

end CycleWord

section Comparison

variable {τ τ' : InfiniteTypeAHeckeAlgebra R q →ₗ[R] R}

/-- A descending product ending at `T m` is the strand shift by `m` of one ending at `T 0`. -/
private theorem cosetRep_eq_shift {n m : ℕ} (h : m ≤ n) :
    cosetRep q n m = shift R q m (cosetRep q (n - m) 0) := by
  rw [shift_cosetRep, Nat.sub_add_cancel h, Nat.zero_add]

/-- Agreement on the cycle word `ζₙ₊₁` is agreement on `T (n - 1) * ⋯ * T 0`. -/
private theorem map_cosetRep_zero_eq (h : ∀ m, τ (cycleWord q m) = τ' (cycleWord q m)) (n : ℕ) :
    τ (cosetRep q n 0) = τ' (cosetRep q n 0) := by
  have hn := h (n + 1)
  simp only [cycleWord_def, Nat.add_sub_cancel, map_smul, smul_eq_mul] at hn
  exact (q.isUnit.pow n).mul_left_cancel hn

/-- The rotation step: for a tracial functional, `b` in the stage of the first `a + 1` strands and
`a < n`, the trace of `b * T a * e * cosetRep q n (a + 1)` is the trace of
`e * b * cosetRep q n a`. -/
private theorem map_mul_T_mul_mul_cosetRep (hτ : ∀ x y, τ (x * y) = τ (y * x)) {a n : ℕ}
    (han : a < n) {b : InfiniteTypeAHeckeAlgebra R q} (hb : b ∈ stage R q (a + 1))
    (e : InfiniteTypeAHeckeAlgebra R q) :
    τ (b * T q a * e * cosetRep q n (a + 1)) = τ (e * b * cosetRep q n a) := by
  have hbc : b * cosetRep q n (a + 1) = cosetRep q n (a + 1) * b := by
    rw [cosetRep_eq_shift han]
    exact (commute_shift_of_mem_stage hb _).eq
  calc τ (b * T q a * e * cosetRep q n (a + 1))
      = τ (cosetRep q n (a + 1) * b * T q a * e) := by
        rw [hτ (b * T q a * e)]
        simp only [mul_assoc]
    _ = τ (e * (b * cosetRep q n (a + 1) * T q a)) := by
        rw [← hbc, hτ (b * cosetRep q n (a + 1) * T q a) e]
    _ = τ (e * b * cosetRep q n a) := by
        rw [← cosetRep_succ_mul_T han]
        simp only [mul_assoc]

/-- The inductive step of the comparison: if two tracial, block-multiplicative functionals agree
on the cycle words and on the stages of the first `j + 1` strands for `j < a`, then they agree on
`y * cosetRep q n a` for every `y` in the stage of the first `a + 1` strands. -/
private theorem map_mul_cosetRep_eq (hτ : ∀ x y, τ (x * y) = τ (y * x))
    (hτ' : ∀ x y, τ' (x * y) = τ' (y * x))
    (hτm : ∀ {a x}, x ∈ stage R q a → ∀ y, τ (x * shift R q a y) = τ x * τ y)
    (hτm' : ∀ {a x}, x ∈ stage R q a → ∀ y, τ' (x * shift R q a y) = τ' x * τ' y)
    (h : ∀ m, τ (cycleWord q m) = τ' (cycleWord q m)) {a n : ℕ} (han : a ≤ n)
    (hS : ∀ j < a, ∀ x ∈ stage R q (j + 1), τ x = τ' x) {y : InfiniteTypeAHeckeAlgebra R q}
    (hy : y ∈ stage R q (a + 1)) :
    τ (y * cosetRep q n a) = τ' (y * cosetRep q n a) := by
  induction a generalizing y with
  | zero =>
    rw [stage_eq_bot_of_le_one le_rfl, Algebra.mem_bot] at hy
    obtain ⟨r, rfl⟩ := hy
    simp only [← Algebra.smul_def, map_smul, map_cosetRep_zero_eq h]
  | succ a ih =>
    -- Split `y ∈ Hₐ₊₂` as `Hₐ₊₁ + Hₐ₊₁ Tₐ Hₐ₊₁`.
    let P : Submodule R (InfiniteTypeAHeckeAlgebra R q) :=
      (LinearMap.eqLocus τ τ').comap (LinearMap.mulRight R (cosetRep q n (a + 1)))
    have hP : ∀ y, y ∈ P ↔ τ (y * cosetRep q n (a + 1)) = τ' (y * cosetRep q n (a + 1)) :=
      fun _ ↦ LinearMap.mem_eqLocus
    refine (hP y).1 <| (toSubmodule_stage_add_two_le_iff.2 ⟨fun b hb ↦ (hP b).2 ?_,
      fun b hb e he ↦ (hP _).2 ?_⟩) hy
    · -- On `Hₐ₊₁`, block multiplicativity splits off the cycle word on the last strands.
      rw [cosetRep_eq_shift han, hτm hb, hτm' hb, hS a (Nat.lt_succ_self a) b hb,
        map_cosetRep_zero_eq h]
    · -- On `Hₐ₊₁ Tₐ Hₐ₊₁`, rotating the trace lowers the descending product by one strand.
      rw [map_mul_T_mul_mul_cosetRep hτ han hb, map_mul_T_mul_mul_cosetRep hτ' han hb]
      exact ih (by omega) (fun j hj ↦ hS j (by omega)) (mul_mem (stage_mono (by omega) he) hb)

/-- **Cycle words determine block-multiplicative traces.** Two tracial linear functionals on the
infinite type-A Hecke algebra, both multiplicative on disjoint blocks of strands, are equal as
soon as they agree on every cycle word `ζₘ`. -/
theorem towerTrace_eq_of_cycleChain_values (hτ : ∀ x y, τ (x * y) = τ (y * x))
    (hτ' : ∀ x y, τ' (x * y) = τ' (y * x))
    (hτm : ∀ {a x}, x ∈ stage R q a → ∀ y, τ (x * shift R q a y) = τ x * τ y)
    (hτm' : ∀ {a x}, x ∈ stage R q a → ∀ y, τ' (x * shift R q a y) = τ' x * τ' y)
    (h : ∀ m, τ (cycleWord q m) = τ' (cycleWord q m)) : τ = τ' := by
  -- Agreement on the stage of the first `n + 1` strands, by strong induction on `n`.
  have hS : ∀ n, ∀ x ∈ stage R q (n + 1), τ x = τ' x := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro x hx
      simpa only [cosetRep_self, mul_one] using
        map_mul_cosetRep_eq hτ hτ' hτm hτm' h le_rfl ih hx
  ext x
  obtain ⟨n, hx⟩ := exists_mem_stage x
  exact hS n x (stage_mono (Nat.le_succ n) hx)

end Comparison

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

/-- A tracial, block-multiplicative linear functional taking the value `(q * z) ^ (m - 1)` on
every cycle word `ζₘ` is the Markov trace with parameter `z`. -/
theorem eq_of_map_cycleWord {τ' : InfiniteTypeAHeckeAlgebra R q →ₗ[R] R}
    (hτ : IsMarkovTrace z τ) (hτ' : ∀ x y, τ' (x * y) = τ' (y * x))
    (hτm' : ∀ {a x}, x ∈ stage R q a → ∀ y, τ' (x * shift R q a y) = τ' x * τ' y)
    (h : ∀ m, τ' (cycleWord q m) = ((q : R) * z) ^ (m - 1)) : τ' = τ :=
  towerTrace_eq_of_cycleChain_values hτ' hτ.map_mul_comm hτm' hτ.map_mul_shift
    fun m ↦ by rw [h, hτ.map_cycleWord]

end IsMarkovTrace

end InfiniteTypeAHeckeAlgebra

end TauCeti
