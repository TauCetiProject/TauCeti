/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Continuous
public import Mathlib.Analysis.InnerProductSpace.LinearMap

/-!
# The Gelfand triple `V ↪ H ↪ V*`

Let `ι : V →L[ℝ] H` be a continuous linear map from a real seminormed space `V` into a real inner
product space `H`, which need only be seminormed. Pairing with `H` through `ι` gives the continuous
linear map

`ι.gelfandDual : H →L[ℝ] StrongDual ℝ V`, `h ↦ (x ↦ ⟪h, ι x⟫)`.

When `H` is normed and `ι` is injective with dense range, `V ↪ H ↪ V*` is a **Gelfand triple**
(also called an evolution triple, with `H` the pivot space): `ι.gelfandDual` is then injective
as well (`ContinuousLinearMap.gelfandDual_injective`), so `H` sits inside `V*`, and the pairing of
`V*` with `V` restricts on `H × V` to the inner product of `H`. The standard example is
`H¹₀(Ω) ↪ L²(Ω) ↪ H⁻¹(Ω)`. Evolution equations `u' + A u = f` are posed in such a triple: the
solution takes values in `V`, while its time derivative takes values in `V*`.

The composite `ι.gelfandDual ∘ ι : V →L[ℝ] StrongDual ℝ V` is the symmetric bilinear form
`(x, y) ↦ ⟪ι x, ι y⟫` (`ContinuousLinearMap.flip_gelfandDual_comp`).

## Main declarations

* `ContinuousLinearMap.gelfandDual`: the map `H → V*`, `h ↦ ⟪h, ι ·⟫`.
* `ContinuousLinearMap.gelfandDual_apply`: its defining formula.
* `ContinuousLinearMap.norm_gelfandDual`: its norm is `‖ι‖`.
* `ContinuousLinearMap.gelfandDual_injective`: for normed `H`, it is injective when `ι` has dense
  range.
* `ContinuousLinearMap.flip_gelfandDual_comp`: the form `⟪ι x, ι y⟫` on `V` is symmetric.
* `ContinuousLinearMap.gelfandDual_comp_injective_iff`: for normed `H`, the composite `V → V*` is
  injective exactly when `ι` is.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., §5.9.2 and §7.1.
* E. Zeidler, *Nonlinear Functional Analysis and its Applications II/A*, Chapter 23.
-/

public section

noncomputable section

open scoped InnerProductSpace

namespace ContinuousLinearMap

variable {V H : Type*} [SeminormedAddCommGroup V] [NormedSpace ℝ V]

section Seminormed

variable [SeminormedAddCommGroup H] [InnerProductSpace ℝ H] (ι : V →L[ℝ] H)

/-- The map `H → V*`, `h ↦ (x ↦ ⟪h, ι x⟫)`, induced by a continuous linear map `ι : V →L[ℝ] H`
into a real inner product space. When `H` is normed and `ι` is injective with dense range, this
is the second embedding of the Gelfand triple `V ↪ H ↪ V*`. -/
def gelfandDual : H →L[ℝ] StrongDual ℝ V :=
  ((compL ℝ V H ℝ).flip ι).comp (innerSL ℝ : H →L[ℝ] H →L[ℝ] ℝ)

/-- The defining formula of `ContinuousLinearMap.gelfandDual`. -/
@[simp]
theorem gelfandDual_apply (h : H) (x : V) : ι.gelfandDual h x = ⟪h, ι x⟫_ℝ := by
  simp [gelfandDual]

/-- The map `H → V*` of a Gelfand triple has the same norm as `ι`. -/
@[simp]
theorem norm_gelfandDual : ‖ι.gelfandDual‖ = ‖ι‖ := by
  refine le_antisymm (opNorm_le_bound _ (norm_nonneg _) fun h ↦
    opNorm_le_bound _ (by positivity) fun x ↦ ?_)
    (opNorm_le_bound ι (norm_nonneg ι.gelfandDual) fun x ↦ ?_)
  · rw [gelfandDual_apply, mul_right_comm]
    grw [norm_inner_le_norm, ι.le_opNorm x]
    exact (mul_comm _ _).le
  · -- Test `ι.gelfandDual (ι x)` on `x`: it returns `⟪ι x, ι x⟫ = ‖ι x‖²`.
    have h := ι.gelfandDual.le_opNorm₂ (ι x) x
    rw [gelfandDual_apply, real_inner_self_eq_norm_mul_norm, norm_mul, norm_norm,
      mul_right_comm] at h
    rcases (norm_nonneg (ι x)).eq_or_lt with hx | hx
    · rw [← hx]
      positivity
    exact le_of_mul_le_mul_right h hx

/-- The bilinear form `(x, y) ↦ ⟪ι x, ι y⟫` that the composite `V → H → V*` defines on `V` is
symmetric. -/
@[simp]
theorem flip_gelfandDual_comp : (ι.gelfandDual.comp ι).flip = ι.gelfandDual.comp ι := by
  ext x y
  simp [real_inner_comm]

end Seminormed

variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] (ι : V →L[ℝ] H)

/-- If `ι` has dense range, the map `H → V*` is injective: an element of `H` orthogonal to the
dense subspace `ι(V)` is zero. Together with an injective `ι`, this makes `V ↪ H ↪ V*` a chain
of continuous embeddings. -/
theorem gelfandDual_injective (hι : DenseRange ι) : Function.Injective ι.gelfandDual := by
  refine (injective_iff_map_eq_zero _).2 fun h hh ↦ hι.eq_zero_of_inner_left ℝ fun x ↦ ?_
  simpa using congr($hh x)

/-- The composite `ι.gelfandDual ∘ ι : V → V*` is injective exactly when `ι` is: testing
`ι.gelfandDual (ι x)` on `x` returns `‖ι x‖²`. -/
theorem gelfandDual_comp_injective_iff :
    Function.Injective (ι.gelfandDual.comp ι) ↔ Function.Injective ι := by
  refine ⟨fun h ↦ (coe_comp ι.gelfandDual ι ▸ h).of_comp, fun hι ↦ ?_⟩
  refine (injective_iff_map_eq_zero _).2 fun x hx ↦ (injective_iff_map_eq_zero ι).1 hι x ?_
  simpa using congr($hx x)

end ContinuousLinearMap
