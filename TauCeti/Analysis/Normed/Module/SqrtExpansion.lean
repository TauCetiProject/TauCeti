/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import Mathlib.Analysis.Normed.Operator.Bilinear
public import TauCeti.Analysis.Real.Sqrt

/-!
# Uniform one-sided square-root expansions on real normed spaces

A positive lower bound for the expansion scale and uniform linear, bilinear and cubic
coefficient bounds give one cubic error constant for all real seminormed spaces. This pointwise
estimate feeds the square-root touching upper-support construction in
`TauCeti.Analysis.InnerProductSpace.Laplacian.UpperSupport.Sqrt`.

## References

* https://github.com/frenzymath/lean-eval-submissions
* https://github.com/frenzymath/PoincareConjecture
-/

public section

namespace TauCeti

/-- A one-sided quadratic-plus-cubic bound gives a uniform upper expansion for its square root.
The error constant is chosen before the seminormed space and the expansion coefficients. -/
theorem exists_forall_sqrt_le_quadratic_add_cubic (d L₀ Q₀ C₀ : ℝ) (hd : 0 < d) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {V : Type*} [SeminormedAddCommGroup V] [NormedSpace ℝ V] (v : V) (c y : ℝ)
        (L : V →L[ℝ] ℝ) (Q : V →L[ℝ] V →L[ℝ] ℝ),
        d ≤ c → ‖L‖ ≤ L₀ → ‖Q‖ ≤ Q₀ → ‖v‖ ≤ 1 →
        y ≤ c ^ 2 + L v + Q v v / 2 + C₀ * ‖v‖ ^ 3 →
        Real.sqrt y ≤ c + L v / (2 * c) + Q v v / (4 * c) -
          (L v) ^ 2 / (8 * c ^ 3) + C * ‖v‖ ^ 3 := by
  obtain ⟨C, hC, hs⟩ := Real.exists_forall_sqrt_le_quadratic_add_cubic d L₀ Q₀ C₀ hd
  refine ⟨C, hC, ?_⟩
  intro V _ _ v c y L Q hdc hL hQ hv hy
  apply hs c y (L v) (Q v v) ‖v‖ hdc (norm_nonneg _) hv ?_ ?_ hy
  · simpa only [Real.norm_eq_abs] using
      (L.le_opNorm v).trans (mul_le_mul_of_nonneg_right hL (norm_nonneg _))
  · simpa only [Real.norm_eq_abs, pow_two, mul_assoc] using
      (Q.le_opNorm₂ v v).trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hQ (norm_nonneg _)) (norm_nonneg _))

end TauCeti
