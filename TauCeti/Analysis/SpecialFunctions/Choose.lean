/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Tactic.Positivity
import Mathlib.Topology.Algebra.GroupWithZero

/-!
# Limits of binomial coefficients along proportional sequences

For fixed `k`, the leading term of `a.choose k` is `a ^ k / k!`. This file records the
corresponding limit when `a` and the normalizing denominator vary together: in a topological field
of characteristic zero, if `a i / b i` converges to `x` and `(b i)⁻¹` converges to zero, then

```text
  (a i).choose k / (b i) ^ k → x ^ k / k!.
```

The statement includes boundary limits such as `x = 0`; no divergence hypothesis on `a` is
needed. It is useful for finite-population limits, where one of a population and its complement
may stay bounded.

## Main result

* `TauCeti.tendsto_choose_div_pow_of_tendsto_div` — the normalized fixed-order binomial
  coefficient along an asymptotically proportional sequence.
* `TauCeti.tendsto_choose_mul_div_choose_of_tendsto_div` — the resulting limit of the ratio
  of products of normalized binomial coefficients, as in the hypergeometric-to-binomial limit.
-/

public section

open Filter Polynomial Topology

namespace TauCeti

/-- A fixed-order binomial coefficient has its expected leading-term limit along any sequence
whose ratio to a common denominator converges.

The separate hypothesis that the inverse denominator tends to zero makes the statement applicable
to denominators other than the natural index. -/
theorem tendsto_choose_div_pow_of_tendsto_div {α 𝕜 : Type*} [Field 𝕜] [CharZero 𝕜]
    [TopologicalSpace 𝕜] [IsTopologicalRing 𝕜] {l : Filter α} {a : α → ℕ} {b : α → 𝕜} {x : 𝕜}
    (hab : Tendsto (fun i ↦ (a i : 𝕜) / b i) l (𝓝 x))
    (hb : Tendsto (fun i ↦ (b i)⁻¹) l (𝓝 0)) (k : ℕ) :
    Tendsto (fun i ↦ ((a i).choose k : 𝕜) / b i ^ k) l (𝓝 (x ^ k / k.factorial)) := by
  have hprod : Tendsto (fun i ↦ ∏ j ∈ Finset.range k, ((a i : 𝕜) / b i - j * (b i)⁻¹)) l
      (𝓝 (x ^ k)) := by
    simpa using tendsto_finsetProd (Finset.range k) fun j _ ↦ hab.sub (hb.const_mul (j : 𝕜))
  refine (hprod.div_const _).congr fun i ↦ ?_
  simp_rw [Nat.cast_choose_eq_descPochhammer_div, descPochhammer_eval_eq_prod_range, div_eq_mul_inv,
    ← sub_mul, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
  ring


/-- If the marked proportion `K N / N` tends to `p`, the product of the normalized marked and
unmarked binomial coefficients, divided by the normalized total one, tends to the corresponding
ratio of limits. -/
theorem tendsto_choose_mul_div_choose_of_tendsto_div (p : ℝ) (K : ℕ → ℕ)
    (hK : ∀ᶠ N in atTop, K N ≤ N)
    (hKp : Tendsto (fun N ↦ (K N : ℝ) / N) atTop (nhds p)) (n k : ℕ) :
    Tendsto (fun N : ℕ ↦
        ((K N).choose k / (N : ℝ) ^ k * ((N - K N).choose (n - k) / (N : ℝ) ^ (n - k))) /
          ((id N).choose n / (N : ℝ) ^ n)) atTop
      (nhds (p ^ k / (k.factorial : ℝ) * ((1 - p) ^ (n - k) / ((n - k).factorial : ℝ)) /
        (1 ^ n / (n.factorial : ℝ)))) := by
  have hinv : Tendsto (fun N : ℕ ↦ ((N : ℝ))⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_nhds_zero_nat
  have hcomplement :
      Tendsto (fun N ↦ ((N - K N : ℕ) : ℝ) / N) atTop
        (nhds (1 - (p : ℝ))) := by
    refine Tendsto.congr' ?_ (tendsto_const_nhds.sub hKp)
    filter_upwards [eventually_ge_atTop 1, hK] with N hN hKN
    have hN0 : N ≠ 0 := by omega
    have hN0' : (N : ℝ) ≠ 0 := by exact_mod_cast hN0
    rw [Nat.cast_sub hKN, sub_div, div_self hN0']
  have htotal : Tendsto (fun N : ℕ ↦ (N : ℝ) / N) atTop (nhds 1) := by
    refine Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hN0 : N ≠ 0 := by omega
    have hN0' : (N : ℝ) ≠ 0 := by exact_mod_cast hN0
    rw [div_self hN0']
  have hmarked := tendsto_choose_div_pow_of_tendsto_div
    (a := K) (b := fun N : ℕ ↦ (N : ℝ)) hKp hinv k
  have hunmarked :=
    tendsto_choose_div_pow_of_tendsto_div (a := fun N ↦ N - K N)
      (b := fun N : ℕ ↦ (N : ℝ)) hcomplement hinv (n - k)
  have hpopulation := tendsto_choose_div_pow_of_tendsto_div
    (a := id) (b := fun N : ℕ ↦ (N : ℝ)) htotal hinv n
  -- Combine the three limits before identifying the normalized ratio with the mass.
  exact (hmarked.mul hunmarked).div hpopulation (by positivity)

end TauCeti
