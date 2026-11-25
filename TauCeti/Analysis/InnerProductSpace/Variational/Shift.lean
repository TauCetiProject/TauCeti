/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.LinearPMap.ClosedForm.Basic
public import TauCeti.Analysis.InnerProductSpace.Variational.EnergySpace

/-!
# Semibounded shifts of Hermitian forms

Let `a : V →L⋆[𝕜] V →L[𝕜] 𝕜` be a bounded sesquilinear form on a normed space `V` over
`𝕜 = ℝ` or `ℂ` and `j : V →L[𝕜] H` a continuous linear map to an inner product space. Its shift
by a real number `α` is the form `a_α(u, v) = a(u, v) + α ⟪j u, j v⟫`
(`ContinuousLinearMap.shiftedForm j a α`). The added term is the inner product of `H`, not that of
`V`, so the weak equations `a_α(u, ·) = ℓ` and `a(u, ·) = ℓ - α ⟪j u, j ·⟫` agree
(`ContinuousLinearMap.shiftedForm_apply`). Since shifts compose additively
(`ContinuousLinearMap.shiftedForm_shiftedForm`), `a` is recovered from `a_α` as its shift by `-α`
(with `ContinuousLinearMap.shiftedForm_zero`), and two shifts differ by `(α - β) ⟪j ·, j ·⟫`
(`ContinuousLinearMap.shiftedForm_sub_shiftedForm`).

Suppose that `a` is Hermitian and **semibounded** relative to `j`, with the quantitative lower
bound `c ‖u‖² ≤ re a(u, u) + ω ‖j u‖²` for some `c > 0` and real `ω`. Then for every `α ≥ ω` the
shifted form `a_α` is coercive with the same constant `c`
(`ContinuousLinearMap.mul_norm_sq_le_re_shiftedForm_self`), so it is a
`TauCeti.CoerciveHermitianForm` (`TauCeti.CoerciveHermitianForm.ofSemibounded`). Its energy norm
satisfies `√c ‖u‖ ≤ ‖u‖_α ≤ √‖a_α‖ ‖u‖`, with a lower constant independent of `α`
(`TauCeti.CoerciveHermitianForm.sqrt_mul_norm_le_norm_toEnergySpace` and
`TauCeti.CoerciveHermitianForm.norm_toEnergySpace_le`). So the energy norms for all `α ≥ ω` are
equivalent to the norm of `V`, and to each other
(`TauCeti.CoerciveHermitianForm.sqrt_mul_norm_toEnergySpace_le`); the examples below spell these
bounds out for `ofSemibounded`.

## Examples

On `V = H = ℝ` with `j = id` and `a(u, v) = -u v`, the bound holds with `c = 1`, `ω = 2`, and
the shift by `2` is the coercive form `u v`. The shift by `1` vanishes on the diagonal and is not
coercive, so the hypothesis `ω ≤ α` cannot be dropped. Negative `ω` is allowed:
`a(u, v) = 2 u v` satisfies the bound with `c = 1`, `ω = -1`.

## References

* J. K. Hunter, *Notes on Partial Differential Equations*, Chapter 4, Theorems 4.21 and 4.22
  (the Dirichlet form with a Gårding constant).
-/

public section

noncomputable section

open RCLike ContinuousLinearMap
open scoped InnerProductSpace

variable {𝕜 V H : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [NormedSpace 𝕜 V]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
  (a : V →L⋆[𝕜] V →L[𝕜] 𝕜) (j : V →L[𝕜] H)

namespace TauCeti

/-- The shift `a_α`, for `α ≥ ω`, of a Hermitian form `a` with
`c ‖u‖² ≤ re a(u, u) + ω ‖j u‖²` and `c > 0`, as a coercive Hermitian form; its coercivity
constant is `c`, whatever `α ≥ ω`. -/
def CoerciveHermitianForm.ofSemibounded (ha : ∀ u v, a u v = star (a v u)) {c ω : ℝ} (hc : 0 < c)
    (hb : ∀ u, c * ‖u‖ ^ 2 ≤ re (a u u) + ω * ‖j u‖ ^ 2) (α : ℝ) (hα : ω ≤ α) :
    CoerciveHermitianForm 𝕜 V where
  form := shiftedForm j a α
  form_apply_eq_star := shiftedForm_eq_star j ha α
  exists_coercive := ⟨c, hc, mul_norm_sq_le_re_shiftedForm_self j hα hb⟩

@[simp]
theorem CoerciveHermitianForm.ofSemibounded_form (ha : ∀ u v, a u v = star (a v u)) {c ω : ℝ}
    (hc : 0 < c) (hb : ∀ u, c * ‖u‖ ^ 2 ≤ re (a u u) + ω * ‖j u‖ ^ 2) (α : ℝ) (hα : ω ≤ α) :
    (CoerciveHermitianForm.ofSemibounded a j ha hc hb α hα).form = shiftedForm j a α :=
  (rfl)

/-- The energy norm of every shift `a_α` with `α ≥ ω` is at least `√c` times the norm of `V`,
with `c` the constant of the semibounded bound, independent of `α`. -/
example (ha : ∀ u v, a u v = star (a v u)) {c ω : ℝ} (hc : 0 < c)
    (hb : ∀ u, c * ‖u‖ ^ 2 ≤ re (a u u) + ω * ‖j u‖ ^ 2) (α : ℝ) (hα : ω ≤ α) (u : V) :
    √c * ‖u‖ ≤ ‖(CoerciveHermitianForm.ofSemibounded a j ha hc hb α hα).toEnergySpace u‖ :=
  (CoerciveHermitianForm.ofSemibounded a j ha hc hb α hα).sqrt_mul_norm_le_norm_toEnergySpace u
    (mul_norm_sq_le_re_shiftedForm_self j hα hb u)

/-- For shifts `α, β ≥ ω`, the energy norm of `a_β` is bounded by that of `a_α`:
`√c ‖u‖_β ≤ √‖a_β‖ ‖u‖_α`. -/
example (ha : ∀ u v, a u v = star (a v u)) {c ω : ℝ} (hc : 0 < c)
    (hb : ∀ u, c * ‖u‖ ^ 2 ≤ re (a u u) + ω * ‖j u‖ ^ 2) {α β : ℝ} (hα : ω ≤ α) (hβ : ω ≤ β)
    (u : V) :
    √c * ‖(CoerciveHermitianForm.ofSemibounded a j ha hc hb β hβ).toEnergySpace u‖ ≤
      √‖shiftedForm j a β‖ *
        ‖(CoerciveHermitianForm.ofSemibounded a j ha hc hb α hα).toEnergySpace u‖ := by
  simpa using (CoerciveHermitianForm.ofSemibounded a j ha hc hb α hα).sqrt_mul_norm_toEnergySpace_le
    (CoerciveHermitianForm.ofSemibounded a j ha hc hb β hβ) u
    (mul_norm_sq_le_re_shiftedForm_self j hα hb u)

/-! ### Examples on `ℝ` -/

/-- The form `a(u, v) = -u v` on `ℝ` satisfies the semibounded bound with `c = 1` and `ω = 2`,
for `j = id`. -/
example (u : ℝ) :
    1 * ‖u‖ ^ 2 ≤ re ((-innerSL ℝ : ℝ →L⋆[ℝ] ℝ →L[ℝ] ℝ) u u) +
      2 * ‖ContinuousLinearMap.id ℝ ℝ u‖ ^ 2 := by
  simp
  linarith

/-- The shift by `2` of `a(u, v) = -u v` on `ℝ` is the coercive form `u v`. -/
example :
    shiftedForm (ContinuousLinearMap.id ℝ ℝ) (-innerSL ℝ : ℝ →L⋆[ℝ] ℝ →L[ℝ] ℝ) 2 = innerSL ℝ := by
  ext u
  simp only [shiftedForm_apply, neg_apply, innerSL_apply_apply, ContinuousLinearMap.id_apply]
  push_cast
  ring

/-- The shift by `1` of `a(u, v) = -u v` on `ℝ` vanishes on the diagonal, so it is not coercive.
Since `1 < ω = 2`, this shows that the hypothesis `ω ≤ α` cannot be dropped. (Any shift `α > 1`
of this form is coercive; `α ≥ 2` is what keeps the constant `c = 1`.) -/
example :
    ¬ ∃ c > 0, ∀ u : ℝ, c * ‖u‖ ^ 2 ≤
      re (shiftedForm (ContinuousLinearMap.id ℝ ℝ) (-innerSL ℝ : ℝ →L⋆[ℝ] ℝ →L[ℝ] ℝ) 1 u u) := by
  rintro ⟨c, hc, h⟩
  have := h 1
  simp at this
  linarith

/-- Negative `ω` is allowed: `a(u, v) = 2 u v` on `ℝ` satisfies the semibounded bound with `c = 1`
and `ω = -1`, for `j = id`. -/
example (u : ℝ) :
    1 * ‖u‖ ^ 2 ≤ re ((2 : ℝ) • (innerSL ℝ : ℝ →L⋆[ℝ] ℝ →L[ℝ] ℝ) u u) +
      (-1) * ‖ContinuousLinearMap.id ℝ ℝ u‖ ^ 2 := by
  simp
  nlinarith [sq_nonneg u]

end TauCeti
