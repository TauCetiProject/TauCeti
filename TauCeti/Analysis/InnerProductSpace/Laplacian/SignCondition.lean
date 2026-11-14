/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Laplacian.Trigonometric

/-!
# Necessity of the zeroth-order sign condition in the maximum principle

The weak maximum principle for `-Δ + c` in
`TauCeti.Analysis.InnerProductSpace.Laplacian.ZerothOrderMaximumPrinciple` assumes that the
zeroth-order coefficient is nonnegative. This file records that the assumption is essential: the
principle fails for every negative constant coefficient.

Let `c < 0` and `a = √(-c)`. On the interval `[0, π / a]`, the function `u(x) = sin (a x)` is
positive in the interior, vanishes on the frontier, and satisfies

`Δ u = c u`,

by the eigenvalue identity `TauCeti.laplacian_sin_const_mul` of
`TauCeti.Analysis.InnerProductSpace.Laplacian.Trigonometric`.

Thus `u` and the zero function are distinct solutions of the homogeneous Dirichlet problem for
`-Δ + c`, and the boundary estimate `u ≤ 0` fails in the interior. In particular, both the weak
maximum principle and Dirichlet uniqueness fail for every negative constant zeroth-order
coefficient. Here `u` is the first Dirichlet eigenfunction of `-Δ` on `[0, π / a]`.

## Main declarations

* `TauCeti.exists_laplacian_eq_mul_eqOn_zero_frontier_pos_of_neg`: for every negative constant
  `c`, a fully quantified counterexample to dropping the nonnegativity assumption from the
  zeroth-order maximum principle.
-/

public section

noncomputable section

namespace TauCeti

open InnerProductSpace Laplacian Set

/-- Every negative constant zeroth-order coefficient violates the weak maximum principle.

For every `c < 0` there are a compact set `K` and a function `f`, continuous on `K` and `C²` on
its interior, such that `Δ f = c f` in the interior and `f = 0` on the frontier, but `f` is
positive somewhere in `K`. With `a = √(-c)`, the witnesses are `K = [0, π / a]` and
`f x = sin (a x)`.

Consequently, the nonnegativity hypothesis on `c` in
`TauCeti.le_of_mul_le_laplacian_le_frontier` and
`TauCeti.eqOn_of_laplacian_sub_mul_eq_of_eqOn_frontier` cannot be weakened to allow any negative
constant. -/
theorem exists_laplacian_eq_mul_eqOn_zero_frontier_pos_of_neg {c : ℝ} (hc : c < 0) :
    ∃ (K : Set ℝ) (f : ℝ → ℝ), IsCompact K ∧ ContinuousOn f K ∧
      (∀ ⦃x⦄, x ∈ interior K → ContDiffAt ℝ 2 f x) ∧
      (∀ ⦃x⦄, x ∈ interior K → Δ f x = c * f x) ∧ Set.EqOn f 0 (frontier K) ∧
      ∃ x ∈ K, 0 < f x := by
  have ha : 0 < √(-c) := Real.sqrt_pos.2 (neg_pos.2 hc)
  refine ⟨Icc 0 (Real.pi / √(-c)), fun x => Real.sin (√(-c) * x), isCompact_Icc, by fun_prop,
    fun _ _ => by fun_prop, fun x _ => ?_, ?_, Real.pi / (2 * √(-c)), ?_, ?_⟩
  · rw [laplacian_sin_const_mul, Real.sq_sqrt (neg_pos.2 hc).le, neg_neg]
  · rw [frontier_Icc (by positivity)]
    rintro x (rfl | rfl) <;> simp [mul_div_cancel₀ _ ha.ne']
  · exact ⟨by positivity, by gcongr; linarith⟩
  · have h : √(-c) * (Real.pi / (2 * √(-c))) = Real.pi / 2 := by field_simp
    simp [h]

end TauCeti

end
