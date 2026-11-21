/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.EvenFunction
public import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Vanishing order, reflection, and parity of Taylor coefficients

For a nonzero analytic germ satisfying `f (2a - z) = ε • f z`, the scalar `ε` is
`(-1) ^ ord_a(f)` (`AnalyticAt.neg_one_pow_analyticOrderNatAt_eq_of_reflection`), and every
iterated derivative at `a` whose order has parity opposite to `ord_a(f)` vanishes
(`AnalyticAt.iteratedDeriv_eq_zero_of_reflection`). Both statements use only an equality of germs,
not a global functional equation.

Globally at the origin, if `f z = z ^ m • g z` with `g` continuous and nonzero at `0` and
`f (-z) = δ • f z` for all `z`, then `δ = (-1) ^ m` and `g` is even
(`TauCeti.eq_neg_one_pow_and_even_of_eq_pow_smul` and
`TauCeti.eq_neg_one_pow_and_even_of_eq_pow_mul`).
-/

public section

open Filter Topology

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
  have hd := heq.iteratedDeriv_eq (analyticOrderNatAt f a)
  rw [iteratedDeriv_comp_const_sub, iteratedDeriv_fun_const_smul_field] at hd
  have hcenter : 2 * a - a = a := by ring
  simp only [hcenter] at hd
  exact smul_left_injective 𝕜 hn.2 hd

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
  have hd := heq.iteratedDeriv_eq k
  rw [iteratedDeriv_comp_const_sub, iteratedDeriv_fun_const_smul_field, ← hε] at hd
  have hcenter : 2 * a - a = a := by ring
  simp only [hcenter] at hd
  have hpow : (-1 : 𝕜) ^ k = -((-1 : 𝕜) ^ analyticOrderNatAt f a) := by
    have hm := congrArg (· * (-1 : 𝕜) ^ analyticOrderNatAt f a) hodd.neg_one_pow
    simpa [pow_add, mul_assoc, ← mul_pow] using hm
  rw [hpow, neg_smul] at hd
  have : HasUniqueDiv E := .of_isTorsionFree 𝕜 E
  have hzero := self_eq_neg.1 hd.symm
  exact (smul_eq_zero.mp hzero).resolve_left (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))

namespace TauCeti

/-- If `f z = z ^ m • g z` globally with `g` continuous and nonzero at `0`, and `f (-z) = δ • f z`
for all `z`, then `δ = (-1) ^ m` and `g` is even. -/
theorem eq_neg_one_pow_and_even_of_eq_pow_smul {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] {f g : 𝕜 → E} {δ : 𝕜} {m : ℕ}
    (hfg : ∀ z, f z = z ^ m • g z) (hparity : ∀ z, f (-z) = δ • f z)
    (hg_cts : ContinuousAt g 0) (hg0 : g 0 ≠ 0) :
    δ = (-1 : 𝕜) ^ m ∧ g.Even := by
  have hg_rel_ne {z : 𝕜} (hz : z ≠ 0) : (-1 : 𝕜) ^ m • g (-z) = δ • g z := by
    apply smul_right_injective E (pow_ne_zero m hz)
    calc z ^ m • ((-1 : 𝕜) ^ m • g (-z))
        = (-z) ^ m • g (-z) := by rw [smul_smul, ← mul_pow, mul_neg_one]
      _ = f (-z) := (hfg (-z)).symm
      _ = δ • f z := hparity z
      _ = z ^ m • (δ • g z) := by rw [hfg z, smul_comm]
  have hg_rel (z : 𝕜) : (-1 : 𝕜) ^ m • g (-z) = δ • g z := by
    by_cases hz : z = 0
    · subst hz
      have hleft : ContinuousAt (fun w : 𝕜 ↦ (-1 : 𝕜) ^ m • g (-w)) 0 :=
        (hg_cts.comp_of_eq continuous_neg.continuousAt neg_zero).const_smul _
      have hright : ContinuousAt (fun w : 𝕜 ↦ δ • g w) 0 := hg_cts.const_smul δ
      have heq : (fun w : 𝕜 ↦ (-1 : 𝕜) ^ m • g (-w)) =ᶠ[𝓝[≠] (0 : 𝕜)] fun w ↦ δ • g w :=
        eventually_nhdsWithin_of_forall fun _ hw ↦ hg_rel_ne hw
      simpa only [neg_zero] using
        ((hleft.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE hright).mp heq).eq_of_nhds
    · exact hg_rel_ne hz
  have hδ_eq : δ = (-1 : 𝕜) ^ m := by
    have h0 := hg_rel 0
    rw [neg_zero] at h0
    exact (smul_left_injective 𝕜 hg0 h0).symm
  refine ⟨hδ_eq, fun z ↦ ?_⟩
  have hrel := hg_rel z
  rw [hδ_eq] at hrel
  exact smul_right_injective E (pow_ne_zero m (neg_ne_zero.mpr one_ne_zero)) hrel

/-- Scalar form of `TauCeti.eq_neg_one_pow_and_even_of_eq_pow_smul`: if `f z = z ^ m * g z` globally
with `g` continuous and nonzero at `0`, and `f (-z) = δ * f z` for all `z`, then `δ = (-1) ^ m` and
`g` is even. -/
theorem eq_neg_one_pow_and_even_of_eq_pow_mul {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {f g : 𝕜 → 𝕜} {δ : 𝕜} {m : ℕ}
    (hfg : ∀ z, f z = z ^ m * g z) (hparity : ∀ z, f (-z) = δ * f z)
    (hg_cts : ContinuousAt g 0) (hg0 : g 0 ≠ 0) :
    δ = (-1 : 𝕜) ^ m ∧ g.Even :=
  eq_neg_one_pow_and_even_of_eq_pow_smul
    (fun z ↦ by simpa only [smul_eq_mul] using hfg z)
    (fun z ↦ by simpa only [smul_eq_mul] using hparity z) hg_cts hg0

end TauCeti
