/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.GrowthOrder
public import TauCeti.Analysis.Analytic.ExtractZeros

/-!
# Removing a zero without increasing the order of growth

An entire function that is not identically zero factors as `(z - c)^m * g(z)`, where
`m = analyticOrderNatAt f c` and `g` is entire and nonzero at `c`. The cofactor has the
same upper bound `TauCeti.OrderLE` on its growth. This holds at every complex center and
for every real order, including the native convention for constants at negative order.

This is the origin-zero removal step preceding Hadamard factorization. Analytic extraction
uses the finite-zero factorization API; away from a sufficiently large disk the cofactor
is bounded in norm by the original function. The origin factor also occurs in Matteo Cipollina's
PNT+ Hadamard denominator.

## References

* K. S. Kedlaya, [*Notes on analytic number theory*](https://kskedlaya.org/papers/ant-ptx.pdf),
  Theorem 8.7 proof (p.49) and Exercise 8.4.10 (p.52), for the Hadamard growth estimates.
* A. Kupers, *Lectures on complex analysis*, §14.1, the finite-order Hadamard context.
* [PNT+ Hadamard factorization](https://github.com/TauCetiProject/PrimeNumberTheoremAnd/blob/58bf81d2ac766ad4a1f64583fc5ca6403a22f2fb/PrimeNumberTheoremAnd/Mathlib/Analysis/Complex/HadamardFactorization.lean#L219).
-/

public section

open Complex Filter Asymptotics Bornology Topology

namespace TauCeti

/-- If an entire function is not identically zero and has growth bounded by `OrderLE f ρ`,
then removing its full zero at any center gives an entire cofactor nonzero there,
with the same upper bound `OrderLE g ρ`. -/
theorem OrderLE.exists_eq_sub_pow_mul {f : ℂ → ℂ} {ρ : ℝ}
    (h : OrderLE f ρ) (hf : Differentiable ℂ f) (hnot : ∃ z, f z ≠ 0) (c : ℂ) :
    ∃ g : ℂ → ℂ, Differentiable ℂ g ∧ g c ≠ 0 ∧ OrderLE g ρ ∧
      ∀ z, f z = (z - c) ^ analyticOrderNatAt f c * g z := by
  have ha : AnalyticOnNhd ℂ f Set.univ := fun z _ ↦ hf.analyticAt z
  obtain ⟨w, hw⟩ := hnot
  have hfinite : analyticOrderAt f c ≠ ⊤ := ha.analyticOrderAt_ne_top_of_isPreconnected
    isPreconnected_univ (Set.mem_univ w) (Set.mem_univ c)
    (by simp [analyticOrderAt_eq_zero.mpr (.inr hw)])
  let m := analyticOrderNatAt f c
  obtain ⟨g, hg, hfg⟩ := ha.exists_eq_prod_pow_smul {c} (fun _ ↦ m)
    (by simpa [m] using (Nat.cast_analyticOrderNatAt hfinite).le)
  have hfg' (z : ℂ) : f z = (z - c) ^ m * g z := by simpa using hfg z
  have hga : AnalyticAt ℂ g c := hg c (Set.mem_univ c)
  have heq : f = (· - c) ^ m * g := by
    funext z
    simpa only [Pi.mul_apply, Pi.pow_apply] using hfg' z
  have horder : (m : ℕ∞) + analyticOrderAt g c = m := by
    calc
      _ = analyticOrderAt ((· - c) ^ m * g) c := by
        rw [analyticOrderAt_mul (by fun_prop) hga, analyticOrderAt_centeredMonomial]
      _ = analyticOrderAt f c := by rw [← heq]
      _ = (m : ℕ∞) := by simpa [m] using (Nat.cast_analyticOrderNatAt hfinite).symm
  have hg0 : g c ≠ 0 := hga.analyticOrderAt_eq_zero.mp
    (ENat.add_right_injective_of_ne_top (ENat.natCast_ne_top m)
      (horder.trans (add_zero _).symm))
  have hdom : ∀ᶠ z in cobounded ℂ, ‖g z‖ ≤ ‖f z‖ := by
    filter_upwards [tendsto_norm_cobounded_atTop.eventually
      (eventually_ge_atTop (‖c‖ + 1))] with z hz
    have hz' : 1 ≤ ‖z - c‖ := by linarith [norm_sub_norm_le z c]
    have hp : 1 ≤ ‖z - c‖ ^ m := one_le_pow₀ hz'
    rw [hfg', norm_mul, norm_pow]
    nlinarith [norm_nonneg (g z)]
  exact ⟨g, differentiableOn_univ.mp hg.differentiableOn, hg0,
    (IsBigO.of_bound' hdom).orderLE h, hfg'⟩

end TauCeti
