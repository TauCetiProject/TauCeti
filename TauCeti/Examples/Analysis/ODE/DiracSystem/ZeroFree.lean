/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.ODE.DiracSystem.ZeroFree

/-!
# Checks for the Hermite–Biehler property

* **Linear functions.** `z + i` is Hermite–Biehler
  (`TauCeti.Examples.HermiteBiehler.isHermiteBiehler_add_I`), while `z - i` is not
  (`TauCeti.Examples.HermiteBiehler.not_isHermiteBiehler_sub_I`): on the upper half-plane
  `|z + i| > |z - i|`, so the inequality points the wrong way for `z - i`.
* **The free Hermite–Biehler function.** `e^{-itz}` is Hermite–Biehler exactly when `t > 0`
  (`TauCeti.Examples.HermiteBiehler.isHermiteBiehler_cexp_iff`): at `z = x + iy`,
  `|e^{-itz}| = e^{ty}` and `|e^{-it conj z}| = e^{-ty}`.
* **Time `0`.** At `t = 0` the fundamental matrix is the identity, so `E(0, ·) = 1` and the
  Dirichlet function `F(0, ·) = -i` are constant, and a constant has `|H#| = |H|`
  (`TauCeti.not_isHermiteBiehler_const`): the hypothesis
  `t > 0` of `TauCeti.isHermiteBiehler_diracFundamentalMatrix` is needed
  (`TauCeti.Examples.HermiteBiehler.not_isHermiteBiehler_diracFundamentalMatrix_zero`).
-/

public section

open Complex ComplexConjugate

namespace TauCeti.Examples.HermiteBiehler

/-- `z + i` is Hermite–Biehler: for `Im z > 0`, `|conj z + i| < |z + i|`. -/
theorem isHermiteBiehler_add_I : IsHermiteBiehler fun z ↦ z + I := by
  refine isHermiteBiehler_iff.2 ⟨differentiable_id.add_const I, fun z hz ↦ ?_⟩
  refine lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) ?_
  simp only [← normSq_eq_norm_sq, normSq_apply, add_re, add_im, conj_re, conj_im, I_re, I_im]
  nlinarith

/-- `z - i` is not Hermite–Biehler: at `z = i`, `|conj i - i| = 2 > 0 = |i - i|`. -/
theorem not_isHermiteBiehler_sub_I : ¬ IsHermiteBiehler fun z ↦ z - I := fun h ↦
  h.ne_zero (z := I) (by simp) (sub_self I)

/-- `e^{-itz}` is Hermite–Biehler exactly when `t > 0`. -/
theorem isHermiteBiehler_cexp_iff (t : ℝ) :
    (IsHermiteBiehler fun z ↦ exp (-I * t * z)) ↔ 0 < t := by
  have hn (z : ℂ) : ‖exp (-I * t * z)‖ = Real.exp (t * z.im) := by
    rw [norm_exp]
    congr 1
    simp
  constructor
  · intro h
    have := h.norm_lt (z := I) (by simp)
    simp only [hn, conj_I, neg_im, I_im] at this
    nlinarith [Real.exp_lt_exp.1 this]
  · intro ht
    refine isHermiteBiehler_iff.2 ⟨by fun_prop, fun z hz ↦ ?_⟩
    simp only [hn, conj_im]
    exact Real.exp_lt_exp.2 (by nlinarith)

/-- At `t = 0` neither `E(0, ·) = 1` nor `F(0, ·) = -i` is Hermite–Biehler. -/
theorem not_isHermiteBiehler_diracFundamentalMatrix_zero (q : ℝ → ℂ) (j : Fin 2) :
    ¬ IsHermiteBiehler fun z ↦
      diracFundamentalMatrix q 0 z 0 j - I * diracFundamentalMatrix q 0 z 1 j := by
  fin_cases j <;> simpa using not_isHermiteBiehler_const _

end TauCeti.Examples.HermiteBiehler
