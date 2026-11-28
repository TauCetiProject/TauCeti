/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Ring.Basic
import TauCeti.Analysis.Normed.Ring.Basic

/-!
# Comparing products in a seminormed commutative ring

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

A second comparison measures how far a product of translates `∏ i ∈ s, (z + a i)` is from the
power `z ^ #s`, without any bound on `z`: in a seminormed commutative ring with `‖1‖ = 1`,

```text
‖∏ i ∈ s, (z + a i) - z ^ #s‖ ≤ ∏ i ∈ s, (‖z‖ + ‖a i‖) - ‖z‖ ^ #s
```

(`TauCeti.norm_prod_add_sub_pow_card_le`), and so at most `(‖z‖ + A) ^ #s - ‖z‖ ^ #s` when every
`‖a i‖ ≤ A` (`TauCeti.norm_prod_add_sub_pow_card_le_of_norm_le`). Expanding the product, the
difference is the sum over the nonempty subsets `t ⊆ s` of `z ^ (#s - #t) * ∏ i ∈ t, a i`, and the
right side is the same sum for the norms. This controls a polynomial whose roots are moved by the
`a i` away from a multiple root at `0`.
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
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp
  induction hs using Finset.Nonempty.cons_induction with
  | singleton j => simp
  | cons j s hj hs ih =>
    simp only [mem_cons, forall_eq_or_imp] at ha hb
    rw [prod_cons, prod_cons, sum_cons]
    calc _ = ‖a j * (∏ i ∈ s, a i - ∏ i ∈ s, b i) + (a j - b j) * ∏ i ∈ s, b i‖ := by
          congr 1; ring
      _ ≤ ‖a j‖ * ‖∏ i ∈ s, a i - ∏ i ∈ s, b i‖ + ‖a j - b j‖ * ‖∏ i ∈ s, b i‖ :=
          (norm_add_le _ _).trans (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))
      _ ≤ 1 * ∑ i ∈ s, ‖a i - b i‖ + ‖a j - b j‖ * 1 := by
          gcongr; exacts [ha.1, ih ha.2 hb.2, norm_prod_le_one_of_nonempty hs hb.2]
      _ = _ := by ring

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

/-- **A product of translates is close to a power.** In a seminormed commutative ring with
`‖1‖ = 1`, the product `∏ i ∈ s, (z + a i)` differs from `z ^ #s` by at most
`∏ i ∈ s, (‖z‖ + ‖a i‖) - ‖z‖ ^ #s`, the same difference for the norms. -/
theorem norm_prod_add_sub_pow_card_le {ι R : Type*} [SeminormedCommRing R] [NormOneClass R]
    (s : Finset ι) (z : R) (a : ι → R) :
    ‖∏ i ∈ s, (z + a i) - z ^ #s‖ ≤ ∏ i ∈ s, (‖z‖ + ‖a i‖) - ‖z‖ ^ #s := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons j s hj ih =>
    rw [prod_cons, prod_cons, card_cons, pow_succ, pow_succ]
    calc ‖(z + a j) * ∏ i ∈ s, (z + a i) - z ^ #s * z‖
        = ‖(z + a j) * (∏ i ∈ s, (z + a i) - z ^ #s) + a j * z ^ #s‖ := by congr 1; ring
      _ ≤ ‖z + a j‖ * ‖∏ i ∈ s, (z + a i) - z ^ #s‖ + ‖a j‖ * ‖z ^ #s‖ :=
          (norm_add_le _ _).trans (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))
      _ ≤ (‖z‖ + ‖a j‖) * (∏ i ∈ s, (‖z‖ + ‖a i‖) - ‖z‖ ^ #s) + ‖a j‖ * ‖z‖ ^ #s := by
          gcongr
          exacts [norm_add_le _ _, norm_pow_le _ _]
      _ = (‖z‖ + ‖a j‖) * ∏ i ∈ s, (‖z‖ + ‖a i‖) - ‖z‖ ^ #s * ‖z‖ := by ring

/-- **A product of small translates is close to a power.** If `‖a i‖ ≤ A` for every `i ∈ s`, then
`∏ i ∈ s, (z + a i)` differs from `z ^ #s` by at most `(‖z‖ + A) ^ #s - ‖z‖ ^ #s`. -/
theorem norm_prod_add_sub_pow_card_le_of_norm_le {ι R : Type*} [SeminormedCommRing R]
    [NormOneClass R] (s : Finset ι) (z : R) {a : ι → R} {A : ℝ} (ha : ∀ i ∈ s, ‖a i‖ ≤ A) :
    ‖∏ i ∈ s, (z + a i) - z ^ #s‖ ≤ (‖z‖ + A) ^ #s - ‖z‖ ^ #s := by
  refine (norm_prod_add_sub_pow_card_le s z a).trans (sub_le_sub_right ?_ _)
  calc ∏ i ∈ s, (‖z‖ + ‖a i‖) ≤ ∏ _i ∈ s, (‖z‖ + A) :=
        prod_le_prod₀ (fun _ _ ↦ by positivity) fun i hi ↦ by gcongr; exact ha i hi
    _ = (‖z‖ + A) ^ #s := prod_const _

end TauCeti
