/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Analysis.RCLike.Basic

/-!
# The dual of a product of normed spaces

The product `E × F` carries the maximum norm `max ‖x‖ ‖y‖`. Its dual norm is the `ℓ¹` norm of the
two restrictions: a continuous linear functional `f` on `E × F` has
`‖f‖ = ‖f ∘ inl‖ + ‖f ∘ inr‖` (`StrongDual.norm_eq_norm_comp_inl_add_norm_comp_inr`). The
inequality `≤` is the triangle inequality; for `≥`, rotating `x` and `y` by unimodular scalars
makes `f (x, 0)` and `f (0, y)` nonnegative reals, so their absolute values add up. The equality
fails for vector-valued maps: the identity of `ℝ × ℝ` has norm `1`, while its two restrictions
have norm `1` each.

This is the duality `(E ⊕_∞ F)* = E* ⊕₁ F*` (see Megginson, *An Introduction to Banach Space
Theory*, §1.10). Together with the Hahn–Banach theorem it identifies the dual of a closed subspace
of `E × F`, such as the intersection of a compatible couple of Banach spaces, with a quotient of
`E* ⊕₁ F*`.
-/

public section

open RCLike

namespace StrongDual

variable {𝕜 E F : Type*} [RCLike 𝕜] [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- The values of a functional on `E × F` at points of the unit balls of `E` and `F` have
absolute values adding up to at most its norm. -/
theorem norm_apply_inl_add_norm_apply_inr_le (f : StrongDual 𝕜 (E × F)) {x : E} {y : F}
    (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) : ‖f (x, 0)‖ + ‖f (0, y)‖ ≤ ‖f‖ := by
  -- Rotate `x` and `y` so that `f` takes the nonnegative real values `‖f (x, 0)‖`, `‖f (0, y)‖`.
  obtain ⟨a, ha, hax⟩ := exists_norm_eq_mul_self (f (x, 0))
  obtain ⟨b, hb, hby⟩ := exists_norm_eq_mul_self (f (0, y))
  have hab : f (a • x, b • y) = ((‖f (x, 0)‖ + ‖f (0, y)‖ : ℝ) : 𝕜) := by
    have hsplit : ((a • x, b • y) : E × F) = a • (x, 0) + b • (0, y) := by simp
    rw [hsplit, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul, ← hax, ← hby, ofReal_add]
  have hle : ‖((a • x, b • y) : E × F)‖ ≤ 1 := by
    simpa [Prod.norm_def, norm_smul, ha, hb] using And.intro hx hy
  calc ‖f (x, 0)‖ + ‖f (0, y)‖ = ‖f (a • x, b • y)‖ := by
        rw [hab, norm_ofReal, abs_of_nonneg (by positivity)]
    _ ≤ ‖f‖ * ‖((a • x, b • y) : E × F)‖ := f.le_opNorm _
    _ ≤ ‖f‖ := mul_le_of_le_one_right (norm_nonneg f) hle

/-- The dual norm of the maximum norm on `E × F` is the `ℓ¹` norm of the two restrictions:
`‖f‖ = ‖f ∘ inl‖ + ‖f ∘ inr‖` for a continuous linear functional `f` on `E × F`. -/
theorem norm_eq_norm_comp_inl_add_norm_comp_inr (f : StrongDual 𝕜 (E × F)) :
    ‖f‖ = ‖f.comp (ContinuousLinearMap.inl 𝕜 E F)‖ + ‖f.comp (ContinuousLinearMap.inr 𝕜 E F)‖ := by
  set f₀ := f.comp (ContinuousLinearMap.inl 𝕜 E F)
  set f₁ := f.comp (ContinuousLinearMap.inr 𝕜 E F)
  have key (x : E) (y : F) (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) : ‖f₀ x‖ + ‖f₁ y‖ ≤ ‖f‖ :=
    f.norm_apply_inl_add_norm_apply_inr_le hx hy
  refine le_antisymm (f.opNorm_le_bound (by positivity) fun z => ?_) ?_
  · calc ‖f z‖ = ‖f₀ z.1 + f₁ z.2‖ := by simp [f₀, f₁, ← map_add]
      _ ≤ ‖f₀‖ * ‖z‖ + ‖f₁‖ * ‖z‖ := norm_add_le_of_le
          ((f₀.le_opNorm _).trans (by gcongr; exact norm_fst_le z))
          ((f₁.le_opNorm _).trans (by gcongr; exact norm_snd_le z))
      _ = (‖f₀‖ + ‖f₁‖) * ‖z‖ := (add_mul _ _ _).symm
  · -- Bound `‖f₀‖` by `‖f‖ - ‖f₁ y‖` for each unit vector `y`, then `‖f₁‖` by `‖f‖ - ‖f₀‖`.
    have h₀ : ‖f₀‖ ≤ ‖f‖ := f₀.opNorm_le_of_unit_norm (norm_nonneg f) fun x hx => by
      simpa using key x 0 hx.le (by simp)
    have h₁ : ‖f₁‖ ≤ ‖f‖ - ‖f₀‖ := f₁.opNorm_le_of_unit_norm (sub_nonneg.2 h₀) fun y hy => by
      have : ‖f₀‖ ≤ ‖f‖ - ‖f₁ y‖ :=
        f₀.opNorm_le_of_unit_norm (sub_nonneg.2 (by simpa using key 0 y (by simp) hy.le))
          fun x hx => le_sub_iff_add_le.2 (key x y hx.le hy.le)
      linarith
    linarith

end StrongDual
