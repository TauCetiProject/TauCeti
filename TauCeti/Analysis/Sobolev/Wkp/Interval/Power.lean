/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import TauCeti.Analysis.Sobolev.Wkp.Classical
import TauCeti.Analysis.SpecialFunctions.Integrability.Rpow

/-!
# Powers in the Sobolev spaces of an interval

On an interval `(0, b)`, `b > 0`, the power `x ↦ x ^ s`, `s : ℝ`, is smooth, and its `i`-th
derivative is `s (s - 1) ⋯ (s - i + 1) x ^ (s - i)`, the descending Pochhammer polynomial of
order `i` evaluated at `s`, times `x ^ (s - i)` (Mathlib's `Real.iter_deriv_rpow_const`). Its only
singularity is at the endpoint `0`, where `x ^ (s - i)` lies in `Lᵖ` for a finite exponent `p`
exactly when `-1 < (s - i) p`. This file turns this into a complete description of the Sobolev
classes containing `x ^ s`: for `1 ≤ p < ∞` and every order `k`, the power `x ^ s` represents an
element of `W^{k,p}(0, b)` if and only if `s` is one of `0, 1, …, k - 1`, in which case it is a
polynomial of degree below `k` whose derivatives of order `k` vanish, or `-1 < (s - k) p`
(`TauCeti.Wkp.exists_value_ae_eq_rpow_const_Ioo_iff`).

The derivatives of order `i ≤ k` are characterized one by one
(`TauCeti.memLp_iteratedFDeriv_rpow_const_restrict_Ioo_iff`), and a `Cᵏ` function on an open set is
a Sobolev function of order `k` exactly when these derivatives lie in `Lᵖ`
(`TauCeti.Wkp.exists_value_ae_eq_iff_of_contDiffOn`). The condition at the top order `k` implies
those below it, since the exponents `s - i` decrease with `i` and the Pochhammer factors vanish
from the first order above a natural number `s`.

For instance `x ^ (3/2)` lies in `W^{1,2}(0, 1)` but not in `W^{2,2}(0, 1)`: its second derivative
`(3/4) x ^ (-1/2)` has square `(9/16) x⁻¹`, which is not integrable at `0`. This is worked out in
`TauCeti.Examples.Analysis.Sobolev.Wkp.Interval.ThreeHalvesPower`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., §5.2 (the powers `|x|^{-α}` in the
  Sobolev spaces of the unit ball, the higher-dimensional counterpart of these examples).
-/

public section

open MeasureTheory Set TopologicalSpace
open scoped ENNReal

namespace TauCeti

variable {s b : ℝ} {p : ℝ≥0∞}

/-- **Powers in the Sobolev spaces of an interval.** For `1 ≤ p < ∞`, the power `x ^ s` represents
an element of `W^{k,p}(0, b)` if and only if `s` is one of `0, 1, …, k - 1` or
`-1 < (s - k) p`. -/
theorem Wkp.exists_value_ae_eq_rpow_const_Ioo_iff [Fact (1 ≤ p)] (hb : 0 < b) (hp : p ≠ ∞)
    (k : ℕ) :
    (∃ u : Wkp volume ⟨Ioo (0 : ℝ) b, isOpen_Ioo⟩ p k,
        (value k u : ℝ → ℝ) =ᵐ[volume.restrict (Ioo 0 b)] fun x => x ^ s) ↔
      (∃ m : ℕ, m < k ∧ s = m) ∨ -1 < (s - k) * p.toReal := by
  have hsmooth : ContDiffOn ℝ k (fun x : ℝ => x ^ s) (Ioo 0 b) := fun x hx =>
    (Real.contDiffAt_rpow_const_of_ne hx.1.ne').contDiffWithinAt
  have hpoch (i : ℕ) : (descPochhammer ℝ i).eval s = 0 ↔ ∃ m : ℕ, m < i ∧ s = m := by
    simp [descPochhammer_eval_eq_prod_range, Finset.prod_eq_zero_iff, sub_eq_zero]
  refine (exists_value_ae_eq_iff_of_contDiffOn (Omega := ⟨Ioo 0 b, isOpen_Ioo⟩) hsmooth).trans ?_
  simp only [Opens.coe_mk, memLp_iteratedFDeriv_rpow_const_restrict_Ioo_iff hb hp, hpoch]
  refine ⟨fun h => h k le_rfl, ?_⟩
  rintro (⟨m, -, rfl⟩ | h) i hi
  · -- Below the order `m + 1` the exponent `m - i` is nonnegative; above it the coefficient
    -- vanishes.
    rcases lt_or_ge m i with hmi | him
    · exact .inl ⟨m, hmi, rfl⟩
    · have : (0 : ℝ) ≤ ((m : ℝ) - i) * p.toReal :=
        mul_nonneg (sub_nonneg.2 (by exact_mod_cast him)) ENNReal.toReal_nonneg
      exact .inr (by linarith)
  · have : (s - k) * p.toReal ≤ (s - i) * p.toReal :=
      mul_le_mul_of_nonneg_right (by linarith [(Nat.cast_le (α := ℝ)).2 hi])
        ENNReal.toReal_nonneg
    exact .inr (by linarith)

end TauCeti
