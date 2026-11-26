/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.InnerProductSpace.LinearMap

/-!
# The Laplacian of trigonometric functions

On the real line the Laplacian is the second derivative, so for every `a : ℝ`

`Δ (fun y ↦ sin (a y)) x = -a ^ 2 * sin (a x)`.

For `a ≠ 0` this says that `y ↦ sin (a y)` is an eigenfunction of `Δ` with eigenvalue `-a ^ 2`;
for `a = 0` both sides vanish.

On a finite-dimensional real inner product space the cosine plane wave `y ↦ cos ⟪ξ, y⟫` is
likewise an eigenfunction, `Δ cos ⟪ξ, ·⟫ = -‖ξ‖ ^ 2 cos ⟪ξ, ·⟫`, so `Δ^[r]` multiplies it by
`(-‖ξ‖ ^ 2) ^ r`. Each derivative brings out one factor `⟪ξ, ·⟫` and a derivative of `cos`, which
is bounded by `1`, so the `m`-th derivative of the plane wave has norm at most `‖ξ‖ ^ m`. These are
the bounds on the data `D^m Δ^r cos ⟪ξ, ·⟫` of the fields of the heat flow of a plane wave.

These identities are not `@[simp]`: Mathlib's simp lemma
`InnerProductSpace.laplacian_eq_iteratedDeriv_real` rewrites `Δ` on `ℝ` to `iteratedDeriv 2`, so
their left-hand sides are not in simp normal form on `ℝ`.

## Main declarations

* `TauCeti.laplacian_sin_const_mul`: `Δ (sin (a ·)) x = -a ^ 2 * sin (a x)`.
* `TauCeti.norm_iteratedFDeriv_cos_inner_le`: `‖D^m cos ⟪ξ, ·⟫‖ ≤ ‖ξ‖ ^ m`.
* `TauCeti.laplacian_cos_inner`: `Δ cos ⟪ξ, ·⟫ = -‖ξ‖ ^ 2 cos ⟪ξ, ·⟫`.
* `TauCeti.iterate_laplacian_cos_inner`: `Δ^[r] cos ⟪ξ, ·⟫ = (-‖ξ‖ ^ 2) ^ r cos ⟪ξ, ·⟫`.
-/

public section

namespace TauCeti

open InnerProductSpace Laplacian
open scoped RealInnerProductSpace

/-- On the real line, the Laplacian of `x ↦ sin (a * x)` is `-a ^ 2 * sin (a * x)`. For `a ≠ 0`,
this makes `x ↦ sin (a * x)` an eigenfunction of `Δ` with eigenvalue `-a ^ 2`. -/
theorem laplacian_sin_const_mul (a x : ℝ) :
    Δ (fun y => Real.sin (a * y)) x = -a ^ 2 * Real.sin (a * x) := by
  rw [laplacian_eq_iteratedDeriv_real, iteratedDeriv_comp_const_mul Real.contDiff_sin]
  simp

section PlaneWave

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The cosine plane wave `y ↦ cos ⟪ξ, y⟫` is `cos` composed with the linear form `⟪ξ, ·⟫`. -/
private theorem cos_inner_eq_comp (ξ : E) :
    (fun y ↦ Real.cos ⟪ξ, y⟫) = Real.cos ∘ innerSL ℝ ξ :=
  funext fun y ↦ by rw [Function.comp_apply, innerSL_apply_apply]

/-- The `m`-th derivative of the cosine plane wave `y ↦ cos ⟪ξ, y⟫` has norm at most `‖ξ‖ ^ m`. -/
theorem norm_iteratedFDeriv_cos_inner_le (ξ x : E) (m : ℕ) :
    ‖iteratedFDeriv ℝ m (fun y ↦ Real.cos ⟪ξ, y⟫) x‖ ≤ ‖ξ‖ ^ m := by
  rw [cos_inner_eq_comp, (innerSL ℝ ξ).iteratedFDeriv_comp_right (Real.contDiff_cos (n := m)) x
    le_rfl]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, innerSL_apply_norm]
  have hcos : ‖iteratedFDeriv ℝ m Real.cos (innerSL ℝ ξ x)‖ ≤ 1 := by
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs]
    exact Real.abs_iteratedDeriv_cos_le_one m _
  calc _ ≤ 1 * ‖ξ‖ ^ m := by gcongr
    _ = ‖ξ‖ ^ m := one_mul _

variable [FiniteDimensional ℝ E]

/-- **The cosine plane waves are eigenfunctions of the Laplacian.** For `ξ ∈ E`,
`Δ cos ⟪ξ, ·⟫ = -‖ξ‖ ^ 2 cos ⟪ξ, ·⟫`. -/
theorem laplacian_cos_inner (ξ x : E) :
    Δ (fun y ↦ Real.cos ⟪ξ, y⟫) x = -‖ξ‖ ^ 2 * Real.cos ⟪ξ, x⟫ := by
  set b := stdOrthonormalBasis ℝ E
  -- The second derivative along `v` is `cos'' ⟪ξ, x⟫ ⟪ξ, v⟫ ^ 2 = -cos ⟪ξ, x⟫ ⟪ξ, v⟫ ^ 2`.
  have hterm (v : E) : iteratedFDeriv ℝ 2 (fun y ↦ Real.cos ⟪ξ, y⟫) x ![v, v] =
      -Real.cos ⟪ξ, x⟫ * ⟪ξ, v⟫ ^ 2 := by
    rw [cos_inner_eq_comp, (innerSL ℝ ξ).iteratedFDeriv_comp_right (Real.contDiff_cos (n := 2)) x
      le_rfl, ContinuousMultilinearMap.compContinuousLinearMap_apply,
      iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod]
    simp [Fin.prod_univ_two, innerSL_apply_apply]
    ring
  rw [congrFun (laplacian_eq_iteratedFDeriv_orthonormalBasis _ b) x]
  simp only [hterm]
  rw [← Finset.mul_sum, b.sum_sq_inner_left ξ]
  ring

/-- **The iterated Laplacians of a cosine plane wave.** For `ξ ∈ E` and `r : ℕ`,
`Δ^[r] cos ⟪ξ, ·⟫ = (-‖ξ‖ ^ 2) ^ r cos ⟪ξ, ·⟫`. -/
theorem iterate_laplacian_cos_inner (ξ : E) (r : ℕ) :
    Δ^[r] (fun y ↦ Real.cos ⟪ξ, y⟫) = fun y ↦ (-‖ξ‖ ^ 2) ^ r * Real.cos ⟪ξ, y⟫ := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Function.iterate_succ_apply', ih]
    funext x
    have hsmul : (fun y ↦ (-‖ξ‖ ^ 2) ^ r * Real.cos ⟪ξ, y⟫) =
        (-‖ξ‖ ^ 2) ^ r • fun y ↦ Real.cos ⟪ξ, y⟫ := (rfl)
    rw [hsmul, laplacian_smul _ (by rw [cos_inner_eq_comp]; fun_prop), smul_eq_mul,
      laplacian_cos_inner]
    ring

end PlaneWave

end TauCeti
