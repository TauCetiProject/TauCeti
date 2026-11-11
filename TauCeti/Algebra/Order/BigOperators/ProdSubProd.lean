/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Comparing two products of elements of the unit ball

For families taking values in the closed unit ball of a seminormed commutative ring, the difference
of the products is controlled by the sum of the pointwise differences:

```text
‖∏ i ∈ s, a i - ∏ i ∈ s, b i‖ ≤ ∑ i ∈ s, ‖a i - b i‖
```

Only `‖a i‖ ≤ 1` and `‖b i‖ ≤ 1` are needed, and the norm enters only through subadditivity and
submultiplicativity, so the bound holds in any seminormed commutative ring, `ℝ` and `ℂ` included.

The file also records the auxiliary bounds `norm_prod_le_prod_norm` (the seminormed version of
Mathlib's `Finset.norm_prod_le`) and `norm_prod_le_one`, and the real-valued corollary
`abs_prod_sub_prod_le_sum_abs_sub`, phrased with `|·|`.

This is the elementary step that turns coordinatewise convergence of finitely many bounded
observables into convergence of their product, without Hölder or dominated-convergence machinery.
-/

public section

namespace TauCeti

open Finset

/-- The norm of a finite product is bounded by the product of the norms, over a seminormed
commutative ring with `‖1‖ = 1`. Mathlib's `Finset.norm_prod_le` states this only for a
`NormedCommRing`. -/
theorem norm_prod_le_prod_norm {ι R : Type*} [SeminormedCommRing R] [NormOneClass R]
    (s : Finset ι) (f : ι → R) : ‖∏ i ∈ s, f i‖ ≤ ∏ i ∈ s, ‖f i‖ :=
  le_prod_of_submultiplicative_of_nonneg norm norm_nonneg norm_one.le norm_mul_le s f

/-- **A finite product of unit-ball elements lies in the unit ball**, over a seminormed
commutative ring with `‖1‖ = 1`. -/
theorem norm_prod_le_one {ι R : Type*} [SeminormedCommRing R] [NormOneClass R] {s : Finset ι}
    {b : ι → R} (hb : ∀ i ∈ s, ‖b i‖ ≤ 1) : ‖∏ i ∈ s, b i‖ ≤ 1 :=
  (norm_prod_le_prod_norm s b).trans (Finset.prod_le_one₀ (fun _ _ ↦ norm_nonneg _) hb)

/-- **A finite product over a nonempty set of unit-ball elements lies in the unit ball**, over a
seminormed commutative ring, without assuming `‖1‖ = 1`. For the empty product, which is `1`, see
`TauCeti.norm_prod_le_one`. -/
theorem norm_prod_le_one_of_nonempty {ι R : Type*} [SeminormedCommRing R] {s : Finset ι}
    (hs : s.Nonempty) {b : ι → R} (hb : ∀ i ∈ s, ‖b i‖ ≤ 1) : ‖∏ i ∈ s, b i‖ ≤ 1 := by
  induction hs using Finset.Nonempty.cons_induction with
  | singleton i => simpa using hb i (Finset.mem_singleton_self i)
  | cons i t hi _ ih =>
    rw [Finset.prod_cons]
    exact (norm_mul_le _ _).trans ((mul_le_mul (hb i (Finset.mem_cons_self i t))
      (ih fun k hk ↦ hb k (Finset.mem_cons_of_mem hk)) (norm_nonneg _) zero_le_one).trans_eq
      (mul_one 1))

/-- **Telescoping bound for a product of unit-ball elements.** If `‖a i‖ ≤ 1` and `‖b i‖ ≤ 1` for
every `i ∈ s`, then the difference of the products is at most the sum of the pointwise
differences. -/
theorem norm_prod_sub_prod_le_sum_norm_sub {ι R : Type*} [SeminormedCommRing R]
    (s : Finset ι) {a b : ι → R}
    (ha : ∀ i ∈ s, ‖a i‖ ≤ 1) (hb : ∀ i ∈ s, ‖b i‖ ≤ 1) :
    ‖∏ i ∈ s, a i - ∏ i ∈ s, b i‖ ≤ ∑ i ∈ s, ‖a i - b i‖ := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert j s hj ih =>
    rcases s.eq_empty_or_nonempty with rfl | hne
    · simp
    · have hmem : ∀ i ∈ s, i ∈ insert j s := fun i hi => Finset.mem_insert_of_mem hi
      have hjs : j ∈ insert j s := Finset.mem_insert_self j s
      have ihs := ih (fun i hi => ha i (hmem i hi)) (fun i hi => hb i (hmem i hi))
      have hprodb : ‖∏ i ∈ s, b i‖ ≤ 1 :=
        norm_prod_le_one_of_nonempty hne fun i hi => hb i (hmem i hi)
      rw [Finset.prod_insert hj, Finset.prod_insert hj, Finset.sum_insert hj]
      have hsplit : a j * ∏ i ∈ s, a i - b j * ∏ i ∈ s, b i
          = a j * (∏ i ∈ s, a i - ∏ i ∈ s, b i) + (a j - b j) * ∏ i ∈ s, b i := by ring
      rw [hsplit]
      refine (norm_add_le _ _).trans ?_
      have h1 : ‖a j * (∏ i ∈ s, a i - ∏ i ∈ s, b i)‖ ≤ ∑ i ∈ s, ‖a i - b i‖ :=
        calc ‖a j * (∏ i ∈ s, a i - ∏ i ∈ s, b i)‖
            ≤ ‖a j‖ * ‖∏ i ∈ s, a i - ∏ i ∈ s, b i‖ := norm_mul_le _ _
          _ ≤ 1 * ‖∏ i ∈ s, a i - ∏ i ∈ s, b i‖ := by gcongr; exact ha j hjs
          _ = ‖∏ i ∈ s, a i - ∏ i ∈ s, b i‖ := one_mul _
          _ ≤ ∑ i ∈ s, ‖a i - b i‖ := ihs
      have h2 : ‖(a j - b j) * ∏ i ∈ s, b i‖ ≤ ‖a j - b j‖ :=
        calc ‖(a j - b j) * ∏ i ∈ s, b i‖ ≤ ‖a j - b j‖ * ‖∏ i ∈ s, b i‖ := norm_mul_le _ _
          _ ≤ ‖a j - b j‖ * 1 := by gcongr
          _ = ‖a j - b j‖ := mul_one _
      linarith

/-- **Real-valued form** of `norm_prod_sub_prod_le_sum_norm_sub`, phrased with `|·|`: if
`|a i| ≤ 1` and `|b i| ≤ 1` for every `i ∈ s`, then the difference of the products is at most the
sum of the pointwise differences. -/
theorem abs_prod_sub_prod_le_sum_abs_sub {ι : Type*} (s : Finset ι) {a b : ι → ℝ}
    (ha : ∀ i ∈ s, |a i| ≤ 1) (hb : ∀ i ∈ s, |b i| ≤ 1) :
    |∏ i ∈ s, a i - ∏ i ∈ s, b i| ≤ ∑ i ∈ s, |a i - b i| := by
  simpa only [Real.norm_eq_abs] using
    norm_prod_sub_prod_le_sum_norm_sub s (a := a) (b := b)
      (fun i hi => by simpa only [Real.norm_eq_abs] using ha i hi)
      (fun i hi => by simpa only [Real.norm_eq_abs] using hb i hi)

end TauCeti
