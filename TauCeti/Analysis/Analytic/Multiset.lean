/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.Basic
public import TauCeti.RingTheory.MvPolynomial.Symmetric.NewtonIdentities
import Mathlib.Analysis.Analytic.Constructions

/-!
# Analytic elementary symmetric functions of multisets

Newton's identities express each elementary symmetric function of a multiset in terms of lower
elementary symmetric functions and power sums. Consequently, a family of multisets whose power sums
through degree `k` are analytic has analytic `k`-th elementary symmetric function.

## Main declarations

* `TauCeti.analyticAt_esymm_of_forall_analyticAt_sum_map_pow`: analyticity of the power sums through
  degree `k` implies analyticity of the `k`-th elementary symmetric function.
-/

public section

namespace TauCeti

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [CharZero 𝕜] [NormedAddCommGroup E]
  [NormedSpace 𝕜 E]

/-- If the power sums through degree `k` of a family of multisets depend analytically on the
parameter, then so does its `k`-th elementary symmetric function, by Newton's identities. -/
theorem analyticAt_esymm_of_forall_analyticAt_sum_map_pow {m : E → Multiset 𝕜} {x₀ : E} (k : ℕ)
    (h : ∀ j, 0 < j → j ≤ k → AnalyticAt 𝕜 (fun x => ((m x).map (· ^ j)).sum) x₀) :
    AnalyticAt 𝕜 (fun x => (m x).esymm k) x₀ := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simpa [Multiset.esymm] using analyticAt_const
    have hrec : (fun x => (m x).esymm k) = fun x => (k : 𝕜)⁻¹ * ((-1) ^ (k + 1) *
        ∑ a ∈ Finset.antidiagonal k with a.1 < k,
          (-1) ^ a.1 * (m x).esymm a.1 * ((m x).map (· ^ a.2)).sum) := by
      funext x
      rw [← Multiset.mul_esymm_eq_sum, inv_mul_cancel_left₀ (Nat.cast_ne_zero.2 hk.ne')]
    rw [hrec]
    refine analyticAt_const.mul <| analyticAt_const.mul <|
      Finset.analyticAt_fun_sum _ fun a ha => ?_
    obtain ⟨ha, hak⟩ := Finset.mem_filter.1 ha
    have ha2 : 0 < a.2 := by
      have := Finset.mem_antidiagonal.1 ha
      omega
    have ha2k : a.2 ≤ k := by
      have := Finset.mem_antidiagonal.1 ha
      omega
    exact (analyticAt_const.mul (ih a.1 hak fun j hj hja => h j hj
      (hja.trans (Nat.le_of_lt hak)))).mul
      (h a.2 ha2 ha2k)

end TauCeti
