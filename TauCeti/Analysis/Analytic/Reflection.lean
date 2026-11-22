/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Vanishing order, reflection, and parity of Taylor coefficients

For a nonzero analytic germ satisfying `f (2a - z) = ε • f z`, the scalar `ε` is
`(-1) ^ ord_a(f)` (`AnalyticAt.neg_one_pow_analyticOrderNatAt_eq_of_reflection`), and every
iterated derivative at `a` whose order has parity opposite to `ord_a(f)` vanishes
(`AnalyticAt.iteratedDeriv_eq_zero_of_reflection`). Both statements use only an equality of germs,
not a global functional equation.
-/

public section

open Filter Topology

private theorem neg_one_pow_smul_iteratedDeriv_eq
    {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {f : 𝕜 → E} {a ε : 𝕜}
    (heq : (fun z ↦ f (2 * a - z)) =ᶠ[𝓝 a] fun z ↦ ε • f z) (k : ℕ) :
    (-1 : 𝕜) ^ k • iteratedDeriv k f a = ε • iteratedDeriv k f a := by
  have hd := heq.iteratedDeriv_eq k
  rw [iteratedDeriv_comp_const_sub, iteratedDeriv_fun_const_smul_field] at hd
  have hcenter : 2 * a - a = a := by ring
  simpa only [hcenter] using hd

/-- The scalar in a reflection equation for a nonzero analytic germ is the sign of its
vanishing order. This applies to vector-valued germs as well as scalar-valued ones. -/
theorem AnalyticAt.neg_one_pow_analyticOrderNatAt_eq_of_reflection
    {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [CharZero 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    {f : 𝕜 → E} {a ε : 𝕜} (hf : AnalyticAt 𝕜 f a)
    (hfinite : analyticOrderAt f a ≠ ⊤)
    (heq : (fun z ↦ f (2 * a - z)) =ᶠ[𝓝 a] fun z ↦ ε • f z) :
    (-1 : 𝕜) ^ analyticOrderNatAt f a = ε := by
  have hn := (analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero hf).mp
    (Nat.cast_analyticOrderNatAt hfinite).symm
  exact smul_left_injective 𝕜 hn.2
    (neg_one_pow_smul_iteratedDeriv_eq heq (analyticOrderNatAt f a))

/-- For a nonzero analytic germ satisfying `f (2 * a - z) =ᶠ[𝓝 a] ε • f z`, every iterated
derivative at `a` whose order `k` has parity opposite to `analyticOrderNatAt f a` vanishes. -/
theorem AnalyticAt.iteratedDeriv_eq_zero_of_reflection
    {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [CharZero 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    {f : 𝕜 → E} {a ε : 𝕜} {k : ℕ} (hf : AnalyticAt 𝕜 f a)
    (hfinite : analyticOrderAt f a ≠ ⊤)
    (heq : (fun z ↦ f (2 * a - z)) =ᶠ[𝓝 a] fun z ↦ ε • f z)
    (hodd : Odd (k + analyticOrderNatAt f a)) :
    iteratedDeriv k f a = 0 := by
  have hε : (-1 : 𝕜) ^ analyticOrderNatAt f a = ε :=
    hf.neg_one_pow_analyticOrderNatAt_eq_of_reflection hfinite heq
  have hd := neg_one_pow_smul_iteratedDeriv_eq heq k
  rw [← hε] at hd
  have hpow : (-1 : 𝕜) ^ k = -((-1 : 𝕜) ^ analyticOrderNatAt f a) := by
    have hm := congrArg (· * (-1 : 𝕜) ^ analyticOrderNatAt f a) hodd.neg_one_pow
    simpa [pow_add, mul_assoc, ← mul_pow] using hm
  rw [hpow, neg_smul] at hd
  have : HasUniqueDiv E := .of_isTorsionFree 𝕜 E
  have hzero := self_eq_neg.1 hd.symm
  exact (smul_eq_zero.mp hzero).resolve_left (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
