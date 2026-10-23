/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.Order

/-!
# Dividing an analytic function by prescribed zeros

If an analytic function `f` vanishes to order at least `k x` at each point `x` of a finite set
`s`, then `f` factors globally as `f z = (∏ x ∈ s, (z - x) ^ k x) • g z`, where `g` is analytic
wherever `f` is. The quotient `g` is obtained by repeatedly taking divided differences
`dslope · x`, each of which lowers the order of vanishing at `x` by one.

Over `ℂ` this is the factorization of an entire function with zeros of prescribed multiplicities
used in transcendence proofs, where `g` is then estimated by the maximum modulus principle. The
order hypotheses may be given as vanishing of derivatives through Mathlib's
`natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero`.

## Main results

* `AnalyticAt.analyticOrderAt_dslope_add_one`: at a zero `a` of `f`, the divided difference
  `dslope f a` has order one less than `f` at `a`.
* `TauCeti.iterate_dslope_apply_eq_zero_of_lt`: if `f` vanishes to order at least `n` at `a`,
  then the first `n` iterated divided differences of `f` at `a` vanish at `a`.
* `AnalyticOnNhd.exists_eq_prod_pow_smul`: an analytic function with zeros of orders at least
  `k x` at the points `x ∈ s` is `∏ x ∈ s, (z - x) ^ k x` times an analytic function.

## References

* J.-H. Evertse, *Diophantine approximation*, lecture notes (2019), ch. 4, §4.4, Lemma 4.24.
-/

public section

open Function

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {f : 𝕜 → E} {a : 𝕜}

/-- At a zero `a` of an analytic function `f`, the divided difference `dslope f a` vanishes to
order one less than `f` at `a`. -/
theorem AnalyticAt.analyticOrderAt_dslope_add_one (hf : AnalyticAt 𝕜 f a) (ha : f a = 0) :
    analyticOrderAt (dslope f a) a + 1 = analyticOrderAt f a := by
  have hfa : ((· - a) • dslope f a) = f := funext fun z ↦ sub_smul_dslope_of_zero ha z
  calc analyticOrderAt (dslope f a) a + 1
      = analyticOrderAt ((· - a) • dslope f a) a := by
        rw [analyticOrderAt_smul (by fun_prop) (hf.dslope a), analyticOrderAt_id_sub_const_self,
          add_comm]
    _ = analyticOrderAt f a := by rw [hfa]

/-- Iterated divided differences at `a` preserve analyticity at every point where `f` is
analytic. -/
theorem AnalyticAt.iterate_dslope {z : 𝕜} (hf : AnalyticAt 𝕜 f z) (n : ℕ) :
    AnalyticAt 𝕜 ((swap dslope a)^[n] f) z := by
  induction n with
  | zero => exact hf
  | succ n ih => rw [iterate_succ_apply']; exact ih.dslope a

namespace TauCeti

/-- If `f` vanishes to order at least `n` at `a`, then each of the first `n` iterated divided
differences `(swap dslope a)^[k] f`, `k < n`, vanishes at `a`. -/
theorem iterate_dslope_apply_eq_zero_of_lt {n k : ℕ} (hn : (n : ℕ∞) ≤ analyticOrderAt f a)
    (hk : k < n) : (swap dslope a)^[k] f a = 0 := by
  induction k generalizing f n with
  | zero => exact apply_eq_zero_of_analyticOrderAt_ne_zero (lt_of_lt_of_le (mod_cast hk) hn).ne'
  | succ k ih =>
    obtain ⟨hfa, ha⟩ := analyticOrderAt_ne_zero.mp
      (lt_of_lt_of_le (mod_cast Nat.zero_lt_of_lt hk) hn).ne'
    rw [iterate_succ_apply]
    refine ih (n := n - 1) ?_ (by lia)
    have h := hfa.analyticOrderAt_dslope_add_one ha
    rw [← h, show (n : ℕ∞) = ((n - 1 : ℕ) : ℕ∞) + 1 by norm_cast; lia] at hn
    exact (ENat.add_le_add_iff_right ENat.one_ne_top).mp hn

end TauCeti

/-- **Division by prescribed zeros.** If `f` is analytic on a neighbourhood of `U` and vanishes
to order at least `k x` at each point `x` of a finite set `s`, then
`f z = (∏ x ∈ s, (z - x) ^ k x) • g z` for all `z` and some `g` analytic on a neighbourhood of
`U`. -/
theorem AnalyticOnNhd.exists_eq_prod_pow_smul {U : Set 𝕜} (hf : AnalyticOnNhd 𝕜 f U)
    (s : Finset 𝕜) (k : 𝕜 → ℕ) (hk : ∀ x ∈ s, (k x : ℕ∞) ≤ analyticOrderAt f x) :
    ∃ g : 𝕜 → E, AnalyticOnNhd 𝕜 g U ∧ ∀ z, f z = (∏ x ∈ s, (z - x) ^ k x) • g z := by
  classical
  induction s using Finset.induction_on generalizing f with
  | empty => exact ⟨f, hf, by simp⟩
  | insert a s ha ih =>
    set g₁ := (swap dslope a)^[k a] f
    have hfg₁ (z : 𝕜) : f z = (z - a) ^ k a • g₁ z :=
      (pow_sub_smul_iterate_dslope_of_zero (k a)
        (fun j hj ↦ TauCeti.iterate_dslope_apply_eq_zero_of_lt
          (hk a (Finset.mem_insert_self a s)) hj)
        z).symm
    have hk₁ : ∀ x ∈ s, (k x : ℕ∞) ≤ analyticOrderAt g₁ x := by
      intro x hx
      rcases eq_or_ne (k x) 0 with h0 | h0
      · simp [h0]
      have hkx := hk x (Finset.mem_insert_of_mem hx)
      have hfx : AnalyticAt 𝕜 f x :=
        (analyticOrderAt_ne_zero.mp (lt_of_lt_of_le (mod_cast Nat.pos_of_ne_zero h0) hkx).ne').1
      have hxa : x ≠ a := fun h ↦ ha (h ▸ hx)
      have hpow : analyticOrderAt (fun z ↦ (z - a) ^ k a) x = 0 :=
        analyticOrderAt_eq_zero.mpr (.inr (pow_ne_zero _ (sub_ne_zero.mpr hxa)))
      have hfeq : f = (fun z ↦ (z - a) ^ k a) • g₁ := funext hfg₁
      rwa [hfeq, analyticOrderAt_smul (by fun_prop) (hfx.iterate_dslope (k a)), hpow,
        zero_add] at hkx
    obtain ⟨g, hg, hg₁⟩ := ih (f := g₁) (fun z hz ↦ (hf z hz).iterate_dslope (k a)) hk₁
    refine ⟨g, hg, fun z ↦ ?_⟩
    rw [hfg₁, hg₁, Finset.prod_insert ha, mul_smul]
