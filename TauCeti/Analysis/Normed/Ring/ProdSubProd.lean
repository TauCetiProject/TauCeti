/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Ring.Basic
import TauCeti.Analysis.Normed.Ring.Basic

/-!
# Comparing two products of elements of the unit ball

For families taking values in the closed unit ball of a seminormed commutative ring, the difference
of the products is controlled by the sum of the pointwise differences:

```text
‖∏ i ∈ s, a i - ∏ i ∈ s, b i‖ ≤ ∑ i ∈ s, ‖a i - b i‖
```

Only `‖a i‖ ≤ 1` and `‖b i‖ ≤ 1` are assumed: the bound `norm_prod_sub_prod_le_sum_norm_sub` holds
in any seminormed commutative ring, `ℝ` and `ℂ` included, without assuming `‖1‖ = 1`. For an empty
`s` both sides are `0`.

The bounds on a single product, `TauCeti.norm_prod_le_prod_norm`, `TauCeti.norm_prod_le_one` and
its nonempty form `TauCeti.norm_prod_le_one_of_nonempty` (which needs no `‖1‖ = 1`), are in
`TauCeti.Analysis.Normed.Ring.Basic`. The real-valued corollary
`abs_prod_sub_prod_le_sum_abs_sub` is phrased with `|·|`.

This is the elementary step that turns coordinatewise convergence of finitely many bounded
observables into convergence of their product, without Hölder or dominated-convergence machinery.
-/

public section

namespace TauCeti

open Finset

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
