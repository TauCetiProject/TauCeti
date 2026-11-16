/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.ModularForms.LFunction
public import TauCeti.NumberTheory.ModularForms.LevelOne.Eigenbasis

import TauCeti.NumberTheory.ModularForms.LFunction.EulerProduct

/-!
# Nonvanishing of L-functions on the level-one newform basis

At level one, the canonical Hecke eigenbasis `TauCeti.levelOneNewformBasis k` of `CuspForm 𝒮ℒ k`
transports each `f : Newform 1 k` along `(Gamma1 1).map (mapGL ℝ) = 𝒮ℒ` without changing the
underlying function on `ℍ`, and the cusp at `∞` has strict width `1`. Consequently, on the
Euler-product half-plane `Re s > k / 2 + 1`, Mathlib's `ModularForm.L` of
`levelOneNewformBasis k f` coincides with the `q`-expansion `LSeries` of `f.toCuspForm` and
therefore does not vanish.

## Main results

* `TauCeti.L_levelOneNewformBasis_ne_zero`: for `0 < k`, `f : Newform 1 k`, and
  `(k : ℝ) / 2 + 1 < s.re`, `ModularForm.L hk (levelOneNewformBasis k f) s ≠ 0`.

## References

* [F. Diamond and J. Shurman, *A first course in modular forms*][diamondshurman2005],
  Proposition 5.8.5 and §5.9.
-/

public section

open CongruenceSubgroup HeckeRing.GL2 Matrix.SpecialLinearGroup UpperHalfPlane
open scoped MatrixGroups

namespace TauCeti

/-- On the Euler-product half-plane `Re s > k / 2 + 1`, `ModularForm.L` of the level-one newform
basis vector `levelOneNewformBasis k f` does not vanish. -/
theorem L_levelOneNewformBasis_ne_zero {k : ℤ} (hk : 0 < k) (f : Newform 1 k) {s : ℂ}
    (hs : (k : ℝ) / 2 + 1 < s.re) :
    ModularForm.L hk (levelOneNewformBasis k f) s ≠ 0 := by
  have hwidth : Subgroup.strictWidthInfty 𝒮ℒ = 1 := by
    rw [← Gamma1_one_map_eq_SL, strictWidthInfty_Gamma1]
  have hL := CuspForm.LSeries_qExpansion_coeff_eq hk (levelOneNewformBasis k f) hs
  rw [hwidth, Complex.ofReal_one, Complex.one_cpow, one_mul, coe_levelOneNewformBasis_apply] at hL
  rw [← hL]
  exact f.LSeries_ne_zero_of_lt_re (by linarith)

end TauCeti
