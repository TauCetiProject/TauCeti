/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.LFunction.Sign
public import TauCeti.NumberTheory.ModularForms.LFunction.Order
import TauCeti.Analysis.Analytic.Reflection

/-!
# The root number determines the parity of analytic rank

For a self-dual positive-weight newform, the root number `i^k λ_N(f)` equals
`(-1)^r`, where `r` is its analytic rank. Thus root number `1` means even rank,
and root number `-1` means odd rank. In particular a positive root number does
not assert nonvanishing at the central point.

The rank is the order of the entire continuation of the ordinary L-function.
The completed L-function has the same order at the positive central point, so
its reflection functional equation determines the parity of this rank.

## Main results

* `HeckeRing.GL2.Newform.IsSelfDual.neg_one_pow_analyticRank`: the parity formula
  for every self-dual newform, including nontrivial real nebentypus.
* `HeckeRing.GL2.Newform.neg_one_pow_analyticRank_eq_I_zpow_mul_frickeSign`: the
  formula with the Fricke sign at trivial nebentypus.

## References

* F. Diamond and J. Shurman, *A First Course in Modular Forms*, §5.10.
-/

public section

open TauCeti

namespace HeckeRing.GL2.Newform

variable {N : ℕ} [NeZero N] {k : ℤ}

namespace IsSelfDual

variable {f : Newform N k}

/-- The root number of a self-dual newform is `(-1)` to its analytic rank.
The rank is computed using the entire L-function, not its Dirichlet series. -/
theorem neg_one_pow_analyticRank (hf : f.IsSelfDual) (hk : 0 < k) :
    (-1 : ℂ) ^ f.analyticRank hk = Complex.I ^ k * f.frickePseudoEigenvalue := by
  have hs : 0 < ((k : ℂ) / 2).re := by
    simp only [Complex.div_ofNat_re, Complex.intCast_re]
    positivity
  have horder := CuspForm.analyticOrderAt_frickeCompletedL_eq_L f.toCuspForm
    (N.toPNat (NeZero.pos N)) hk hs
  have hfinite : analyticOrderAt
      (CuspForm.frickeCompletedL f.toCuspForm (N.toPNat (NeZero.pos N))) ((k : ℂ) / 2) ≠ ⊤ := by
    rw [horder]
    exact f.analyticOrderAt_L_ne_top hk _
  have hF := (CuspForm.differentiable_frickeCompletedL f.toCuspForm
    (N.toPNat (NeZero.pos N)) hk).analyticAt ((k : ℂ) / 2)
  have hreflect := hF.neg_one_pow_analyticOrderNatAt_eq_of_reflection hfinite
        (Filter.Eventually.of_forall fun s ↦ by
          have hcenter : 2 * ((k : ℂ) / 2) = k := by ring
          simpa only [hcenter, smul_eq_mul] using hf.frickeCompletedL_sub_eq hk s)
  simpa only [analyticRank_def, analyticOrderNatAt, horder] using hreflect

/-- A self-dual newform has even analytic rank exactly when its root number is `1`. -/
@[simp]
theorem even_analyticRank_iff (hf : f.IsSelfDual) (hk : 0 < k) :
    Even (f.analyticRank hk) ↔ Complex.I ^ k * f.frickePseudoEigenvalue = 1 := by
  rw [← hf.neg_one_pow_analyticRank hk, neg_one_pow_eq_one_iff_even (by norm_num : (-1 : ℂ) ≠ 1)]

/-- A self-dual newform has odd analytic rank exactly when its root number is `-1`. -/
@[simp]
theorem odd_analyticRank_iff (hf : f.IsSelfDual) (hk : 0 < k) :
    Odd (f.analyticRank hk) ↔ Complex.I ^ k * f.frickePseudoEigenvalue = -1 := by
  rw [← hf.neg_one_pow_analyticRank hk,
    neg_one_pow_eq_neg_one_iff_odd (by norm_num : (-1 : ℂ) ≠ 1)]

end IsSelfDual

/-- At trivial nebentypus the root number is `i^k` times the Fricke sign, and it
is `(-1)` to the analytic rank. -/
theorem neg_one_pow_analyticRank_eq_I_zpow_mul_frickeSign (f : Newform N k)
    (hχ : f.χ = 1) (hk : 0 < k) :
    (-1 : ℂ) ^ f.analyticRank hk = Complex.I ^ k * f.frickeSign hχ := by
  rw [← f.frickePseudoEigenvalue_eq_frickeSign hχ]
  exact (f.isSelfDual_of_χ_eq_one hχ).neg_one_pow_analyticRank hk

end HeckeRing.GL2.Newform
