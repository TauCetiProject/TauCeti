/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.Analysis.SpecialFunctions.Log.Summable
public import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Sharp and exponential bounds for products in normed rings

For any finite family `u : ι → R` in a seminormed commutative ring `R`, the distance from
`∏ i ∈ s, (1 + u i)` to `1` satisfies the sharp majorant

`‖∏ i ∈ s, (1 + u i) - 1‖ ≤ ∏ i ∈ s, (1 + ‖u i‖) - 1`

(`Finset.norm_prod_one_add_sub_one_le_prod_one_add_norm_sub_one`). This bound requires neither
`NormOneClass R` nor nonvanishing of `1 + u i`, so it applies uniformly to `ℂ`, `p`-adic rings,
submultiplicative rescalings with `‖1‖ > 1`, and the zero ring, and is attained at `u = ![1, 1]`
and `u = ![-1, 0]`.

More generally, `HasProd.norm_le_exp_of_sum_le` bounds any supplied infinite product from real
exponential bounds on its factors and a common bound on all finite sums of the exponents, and
`TauCeti.norm_tprod_le_exp_of_sum_le` gives the corresponding totalized product bound.

For infinite products with `Summable (fun i ↦ ‖f i‖)`, these estimates give the sharp majorants
`‖∏' i, (1 + f i) - 1‖ ≤ (∏' i, (1 + ‖f i‖)) - 1` and `‖∏' i, (1 + f i)‖ ≤ ∏' i, (1 + ‖f i‖)`,
together with the exponential corollaries `‖∏' i, (1 + f i)‖ ≤ exp (∑' i, ‖f i‖)` (in a seminormed
commutative ring) and `‖∏' i, (1 + f i) - 1‖ ≤ exp (∑' i, ‖f i‖) - 1` used to bound theta products
and Siegel functions on the upper half-plane, the exact zero-set characterization
`(∏' i, (1 + f i)) = 0 ↔ ∃ i, 1 + f i = 0`, and the finite-head times cofinite-tail splitting
`(∏ i ∈ t, (1 + f i)) * (∏' i : {i // i ∉ t}, (1 + f i)) = ∏' i, (1 + f i)`.

## Main declarations

* `Finset.norm_prod_one_add_sub_one_le_prod_one_add_norm_sub_one`: sharp finite-product majorant
  `‖∏ i ∈ s, (1 + u i) - 1‖ ≤ ∏ i ∈ s, (1 + ‖u i‖) - 1` in any `SeminormedCommRing`.
* `Finset.norm_prod_one_sub_sub_one_le_prod_one_add_norm_sub_one`: subtracted-term variant for
  `∏ i ∈ s, (1 - u i)`.
* `Finset.norm_prod_one_add_le_prod_one_add_norm`: `‖∏ i ∈ s, (1 + u i)‖ ≤ ∏ i ∈ s, (1 + ‖u i‖)`
  under `NormOneClass`.
* `HasProd.norm_le_exp_of_sum_le`: exponential norm bound for a supplied infinite product from
  factor bounds `‖f i‖ ≤ exp (b i)` and finite-sum bounds `∑ i ∈ s, b i ≤ B`.
* `TauCeti.norm_tprod_one_add_sub_one_le_tprod_one_add_norm_sub_one`: sharp infinite-product
  distance-to-one majorant in any `SeminormedCommRing`.
* `TauCeti.norm_tprod_one_add_le_tprod_one_add_norm`: sharp infinite-product norm bound under
  `NormOneClass`.
* `TauCeti.norm_tprod_le_exp_of_sum_le`: totalized infinite-product norm bound from factor bounds
  `‖f i‖ ≤ exp (b i)` and finite-sum bounds `∑ i ∈ s, b i ≤ B`.
* `TauCeti.norm_tprod_one_add_le_exp_tsum`, `TauCeti.norm_tprod_one_add_sub_one_le`: exponential
  upper bounds in terms of `exp (∑' i, ‖f i‖)`.
* `TauCeti.tprod_one_add_eq_zero_iff`, `TauCeti.tprod_one_sub_eq_zero_iff`: an absolutely
  convergent product `∏' i, (1 ± f i)` vanishes if and only if one factor vanishes.
* `TauCeti.prod_mul_tprod_compl_one_add`: finite-head times cofinite-tail factorization of an
  absolutely convergent product `∏' i, (1 + f i)` in any complete normed commutative ring.

## References

* A. Rainer, *Advanced Complex Analysis*, Proposition 14.2.
-/

public section

open scoped BigOperators

namespace Finset

section SeminormedCommRing

variable {ι R : Type*} [SeminormedCommRing R]

/-- **Sharp finite-product majorant.** For every finite family in a seminormed commutative ring,
`‖∏ i ∈ s, (1 + u i) - 1‖ ≤ ∏ i ∈ s, (1 + ‖u i‖) - 1`, with no condition on `‖1‖` and no
nonvanishing assumption on the factors. -/
theorem norm_prod_one_add_sub_one_le_prod_one_add_norm_sub_one (s : Finset ι) (u : ι → R) :
    ‖∏ i ∈ s, (1 + u i) - 1‖ ≤ ∏ i ∈ s, (1 + ‖u i‖) - 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    have hstep :
        (1 + u a) * ∏ i ∈ s, (1 + u i) - 1 =
          (∏ i ∈ s, (1 + u i) - 1) + u a * (∏ i ∈ s, (1 + u i) - 1) + u a := by ring
    rw [Finset.prod_insert ha, Finset.prod_insert ha, hstep]
    calc ‖(∏ i ∈ s, (1 + u i) - 1) + u a * (∏ i ∈ s, (1 + u i) - 1) + u a‖
        ≤ ‖∏ i ∈ s, (1 + u i) - 1‖ + ‖u a * (∏ i ∈ s, (1 + u i) - 1)‖ + ‖u a‖ :=
          norm_add₃_le
      _ ≤ (∏ i ∈ s, (1 + ‖u i‖) - 1) + ‖u a‖ * (∏ i ∈ s, (1 + ‖u i‖) - 1) + ‖u a‖ := by
          gcongr
          exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left ih (norm_nonneg _))
      _ = (1 + ‖u a‖) * (∏ i ∈ s, (1 + ‖u i‖)) - 1 := by ring

/-- Subtracted-term form of `Finset.norm_prod_one_add_sub_one_le_prod_one_add_norm_sub_one`:
`‖∏ i ∈ s, (1 - u i) - 1‖ ≤ ∏ i ∈ s, (1 + ‖u i‖) - 1` in any seminormed commutative ring. -/
theorem norm_prod_one_sub_sub_one_le_prod_one_add_norm_sub_one (s : Finset ι) (u : ι → R) :
    ‖∏ i ∈ s, (1 - u i) - 1‖ ≤ ∏ i ∈ s, (1 + ‖u i‖) - 1 := by
  simpa [sub_eq_add_neg] using s.norm_prod_one_add_sub_one_le_prod_one_add_norm_sub_one (-u)

/-- In a seminormed commutative ring with `‖1‖ = 1`,
`‖∏ i ∈ s, (1 + u i)‖ ≤ ∏ i ∈ s, (1 + ‖u i‖)`. -/
theorem norm_prod_one_add_le_prod_one_add_norm [NormOneClass R] (s : Finset ι) (u : ι → R) :
    ‖∏ i ∈ s, (1 + u i)‖ ≤ ∏ i ∈ s, (1 + ‖u i‖) := by
  have h := s.norm_prod_one_add_sub_one_le_prod_one_add_norm_sub_one u
  have h1 := norm_le_norm_sub_add (∏ i ∈ s, (1 + u i)) 1
  rw [norm_one] at h1
  linarith

end SeminormedCommRing

end Finset

/-- A supplied infinite product has norm at most `exp B` if each factor has norm at most
`exp (b i)` and every finite sum of the real exponents is at most `B`. -/
theorem HasProd.norm_le_exp_of_sum_le {ι R : Type*} [SeminormedCommRing R] [NormOneClass R]
    {f : ι → R} {a : R} (hf : HasProd f a) {b : ι → ℝ} {B : ℝ}
    (hb : ∀ i, ‖f i‖ ≤ Real.exp (b i))
    (hB : ∀ s : Finset ι, ∑ i ∈ s, b i ≤ B) : ‖a‖ ≤ Real.exp B := by
  refine le_of_tendsto' (Filter.Tendsto.norm hf) fun s ↦ ?_
  exact (Finset.le_prod_of_submultiplicative_of_nonneg (norm : R → ℝ) norm_nonneg
    norm_one.le norm_mul_le s f).trans <|
    (Finset.prod_le_prod₀ (fun _ _ ↦ norm_nonneg _) fun i _ ↦ hb i).trans <|
      (Real.exp_sum s b).symm.trans_le (Real.exp_le_exp.mpr (hB s))

namespace TauCeti

section SeminormedCommRing

variable {ι R : Type*} [SeminormedCommRing R]

/-- **Sharp infinite-product distance-to-one majorant.** In a seminormed commutative ring,
`‖∏' i, (1 + f i) - 1‖ ≤ (∏' i, (1 + ‖f i‖)) - 1` whenever `∑' i, ‖f i‖` converges, with no
condition on `‖1‖`. -/
theorem norm_tprod_one_add_sub_one_le_tprod_one_add_norm_sub_one {f : ι → R}
    (hf : Summable fun i ↦ ‖f i‖) :
    ‖∏' i, (1 + f i) - 1‖ ≤ (∏' i, (1 + ‖f i‖)) - 1 := by
  have hm : Multipliable fun i ↦ 1 + ‖f i‖ := Real.multipliable_one_add_of_summable hf
  by_cases h : Multipliable fun i ↦ 1 + f i
  · exact le_of_tendsto_of_tendsto' ((h.hasProd.sub_const 1).norm) (hm.hasProd.sub_const 1)
      fun s ↦ s.norm_prod_one_add_sub_one_le_prod_one_add_norm_sub_one f
  · rw [tprod_eq_one_of_not_multipliable h, sub_self, norm_zero, sub_nonneg]
    refine ge_of_tendsto' hm.hasProd fun s ↦ ?_
    simpa using Finset.prod_le_prod₀ (s := s) (f := fun _ ↦ (1 : ℝ)) (g := fun i ↦ 1 + ‖f i‖)
      (fun _ _ ↦ zero_le_one) fun i _ ↦ le_add_of_nonneg_right (norm_nonneg (f i))

variable [NormOneClass R]

/-- In a seminormed commutative ring with `‖1‖ = 1`,
`‖∏' i, (1 + f i)‖ ≤ ∏' i, (1 + ‖f i‖)` whenever `∑' i, ‖f i‖` converges. -/
theorem norm_tprod_one_add_le_tprod_one_add_norm {f : ι → R}
    (hf : Summable fun i ↦ ‖f i‖) :
    ‖∏' i, (1 + f i)‖ ≤ ∏' i, (1 + ‖f i‖) := by
  have hm : Multipliable fun i ↦ 1 + ‖f i‖ := Real.multipliable_one_add_of_summable hf
  by_cases h : Multipliable fun i ↦ 1 + f i
  · exact le_of_tendsto_of_tendsto' (Filter.Tendsto.norm h.hasProd) hm.hasProd
      fun s ↦ s.norm_prod_one_add_le_prod_one_add_norm f
  · rw [tprod_eq_one_of_not_multipliable h, norm_one]
    refine ge_of_tendsto' hm.hasProd fun s ↦ ?_
    simpa using Finset.prod_le_prod₀ (s := s) (f := fun _ ↦ (1 : ℝ)) (g := fun i ↦ 1 + ‖f i‖)
      (fun _ _ ↦ zero_le_one) fun i _ ↦ le_add_of_nonneg_right (norm_nonneg (f i))

/-- The totalized infinite product has norm at most `exp B` if each factor has norm at most
`exp (b i)` and every finite sum of the real exponents is at most `B`. -/
theorem norm_tprod_le_exp_of_sum_le {f : ι → R} {b : ι → ℝ} {B : ℝ}
    (hb : ∀ i, ‖f i‖ ≤ Real.exp (b i))
    (hB : ∀ s : Finset ι, ∑ i ∈ s, b i ≤ B) : ‖∏' i, f i‖ ≤ Real.exp B := by
  by_cases h : Multipliable f
  · exact h.hasProd.norm_le_exp_of_sum_le hb hB
  · rw [tprod_eq_one_of_not_multipliable h, norm_one]
    exact Real.one_le_exp (by simpa using hB ∅)

/-- In a seminormed commutative ring, `‖∏' i, (1 + f i)‖ ≤ exp (∑' i, ‖f i‖)` whenever
`‖f i‖` is summable. -/
theorem norm_tprod_one_add_le_exp_tsum {f : ι → R} (hf : Summable fun i ↦ ‖f i‖) :
    ‖∏' i, (1 + f i)‖ ≤ Real.exp (∑' i, ‖f i‖) := by
  refine norm_tprod_le_exp_of_sum_le (b := fun i ↦ ‖f i‖) ?_ ?_
  · intro i
    calc
      ‖1 + f i‖ ≤ 1 + ‖f i‖ := (norm_add_le _ _).trans_eq (by rw [norm_one])
      _ ≤ Real.exp ‖f i‖ := by simpa only [add_comm] using Real.add_one_le_exp ‖f i‖
  · exact fun s ↦ hf.sum_le_tsum s fun _ _ ↦ norm_nonneg _

end SeminormedCommRing

section NormedCommRing

variable {ι R : Type*} [NormedCommRing R] [NormOneClass R]

/-- In a normed commutative ring, `‖∏' i, (1 + f i) - 1‖ ≤ exp (∑' i, ‖f i‖) - 1` whenever the
norms `‖f i‖` are summable. -/
theorem norm_tprod_one_add_sub_one_le {f : ι → R} (hf : Summable fun i ↦ ‖f i‖) :
    ‖∏' i, (1 + f i) - 1‖ ≤ Real.exp (∑' i, ‖f i‖) - 1 := by
  by_cases h : Multipliable fun i ↦ 1 + f i
  · refine le_of_tendsto' ((h.hasProd.sub_const 1).norm) fun s ↦ ?_
    exact (s.norm_prod_one_add_sub_one_le f).trans <| sub_le_sub_right
      (Real.exp_le_exp.2 (hf.sum_le_tsum s fun _ _ ↦ norm_nonneg _)) 1
  · rw [tprod_eq_one_of_not_multipliable h, sub_self, norm_zero, sub_nonneg]
    exact Real.one_le_exp (tsum_nonneg fun _ ↦ norm_nonneg _)

/-- In a complete normed commutative ring with multiplicative norm, an absolutely convergent
product `∏' i, (1 + f i)` vanishes if and only if one of its factors vanishes. -/
theorem tprod_one_add_eq_zero_iff [CompleteSpace R] [NormMulClass R] {f : ι → R}
    (hf : Summable fun i ↦ ‖f i‖) :
    (∏' i, (1 + f i)) = 0 ↔ ∃ i, 1 + f i = 0 := by
  refine ⟨fun h ↦ ?_, tprod_of_exists_eq_zero⟩
  by_contra! hne
  exact tprod_one_add_ne_zero_of_summable hne hf h

/-- Subtracted-term form of `TauCeti.tprod_one_add_eq_zero_iff`: an absolutely convergent product
`∏' i, (1 - f i)` vanishes if and only if `f i = 1` for some `i`. -/
theorem tprod_one_sub_eq_zero_iff [CompleteSpace R] [NormMulClass R] {f : ι → R}
    (hf : Summable fun i ↦ ‖f i‖) :
    (∏' i, (1 - f i)) = 0 ↔ ∃ i, f i = 1 := by
  have h := tprod_one_add_eq_zero_iff (f := fun i ↦ -f i) (by simpa using hf)
  simp only [← sub_eq_add_neg, sub_eq_zero, eq_comm (a := (1 : R))] at h
  exact h

/-- In a complete normed commutative ring, any absolutely convergent product `∏' i, (1 + f i)`
splits into the finite product over `t : Finset ι` times the complementary infinite product over
`{i // i ∉ t}`, even when factors in `t` vanish. -/
theorem prod_mul_tprod_compl_one_add [CompleteSpace R] {f : ι → R}
    (hf : Summable fun i ↦ ‖f i‖) (t : Finset ι) :
    (∏ i ∈ t, (1 + f i)) * (∏' i : {i // i ∉ t}, (1 + f i)) = ∏' i, (1 + f i) := by
  have hs : Multipliable (fun i : (t : Set ι) ↦ 1 + f i) := (hasProd_fintype _).multipliable
  have hsc : Multipliable (fun i : ↑(t : Set ι)ᶜ ↦ 1 + f i) :=
    multipliable_one_add_of_summable (hf.subtype _)
  have hmul := hs.tprod_mul_tprod_compl (s := (t : Set ι)) (f := fun i ↦ 1 + f i) hsc
  rw [t.tprod_subtype' fun i ↦ 1 + f i] at hmul
  have heq : (∏' i : ↑(t : Set ι)ᶜ, (1 + f i)) = ∏' i : {i // i ∉ t}, (1 + f i) :=
    (Equiv.subtypeEquivRight (p := (· ∈ (t : Set ι)ᶜ)) (q := (· ∉ t)) fun i ↦ by simp).tprod_eq
      fun i ↦ 1 + f i
  rwa [heq] at hmul

end NormedCommRing

end TauCeti

/-! ### Examples

The sharp bound `Finset.norm_prod_one_add_sub_one_le_prod_one_add_norm_sub_one` is an equality at
`u = ![1, 1]` (where both sides equal `3`, strictly below `exp 2 - 1`) and at `u = ![-1, 0]`
(where a factor vanishes and both sides equal `1`). -/

example :
    ‖∏ i : Fin 2, (1 + (![1, 1] i : ℂ)) - 1‖ = 3 ∧
      ∏ i : Fin 2, (1 + ‖(![1, 1] i : ℂ)‖) - 1 = 3 := by
  norm_num [Fin.prod_univ_two]

example :
    ‖∏ i : Fin 2, (1 + (![-1, 0] i : ℂ)) - 1‖ = 1 ∧
      ∏ i : Fin 2, (1 + ‖(![-1, 0] i : ℂ)‖) - 1 = 1 := by
  norm_num [Fin.prod_univ_two]

