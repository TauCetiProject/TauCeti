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
is bounded in norm by the original function. No canonical-product or logarithm theorem is used.
The cofactor step is commissioned by AnalyticNumberTheoryPartI §0.22. It is also implicit
in Matteo Cipollina's origin factor in the PNT+ Hadamard denominator. The proof here composes
the existing analytic extraction and growth APIs; it does not use a canonical product.

## References

* A. Kupers, *Lectures on complex analysis*, §14.1, the finite-order Hadamard context.
* [PNT+ Hadamard factorization](https://github.com/TauCetiProject/PrimeNumberTheoremAnd/blob/58bf81d2ac766ad4a1f64583fc5ca6403a22f2fb/PrimeNumberTheoremAnd/Mathlib/Analysis/Complex/HadamardFactorization.lean#L219).
-/

public section

open Complex Filter Asymptotics Bornology Topology

namespace TauCeti

/-- Dividing out the full zero at a prescribed center preserves the entire function's order
of growth. The cofactor is nonzero at the center. -/
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
  have horder : (m : ℕ∞) + analyticOrderAt g c = m := by
    have heq : f = fun z ↦ (z - c) ^ m * g z := funext hfg'
    calc
      _ = analyticOrderAt (fun z ↦ (z - c) ^ m * g z) c := by
        rw [analyticOrderAt_fun_mul (by fun_prop) hga]
        congr 1
        change (m : ℕ∞) = analyticOrderAt ((fun z : ℂ ↦ z - c) ^ m) c
        rw [analyticOrderAt_pow (by fun_prop), analyticOrderAt_id_sub_const_self,
          nsmul_one]
      _ = analyticOrderAt f c := by rw [← heq]
      _ = (m : ℕ∞) := by simpa [m] using (Nat.cast_analyticOrderNatAt hfinite).symm
  have hg0 : g c ≠ 0 := hga.analyticOrderAt_eq_zero.mp (le_antisymm
    ((ENat.add_le_add_iff_left (by simp : (m : ℕ∞) ≠ ⊤)).mp (by simpa using horder.le))
    (zero_le))
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
