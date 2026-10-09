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

Let `ι : V →L[ℝ] H` be a continuous linear map from a real normed space `V` into a real inner
product space `H`. Pairing with `H` through `ι` gives the continuous linear map

`ι.gelfandDual : H →L[ℝ] StrongDual ℝ V`, `h ↦ (x ↦ ⟪h, ι x⟫)`.

When `ι` is injective with dense range, `V ↪ H ↪ V*` is a **Gelfand triple** (also called an
evolution triple, with `H` the pivot space): `ι.gelfandDual` is then injective as well
(`ContinuousLinearMap.gelfandDual_injective`), so `H` sits inside `V*`, and the pairing of
`V*` with `V` restricts on `H × V` to the inner product of `H`. The standard example is
`H¹₀(Ω) ↪ L²(Ω) ↪ H⁻¹(Ω)`. Evolution equations `u' + A u = f` are posed in such a triple: the
solution takes values in `V`, while its time derivative takes values in `V*`.

The composite `ι.gelfandDual ∘ ι : V →L[ℝ] StrongDual ℝ V` is the symmetric bilinear form
`(x, y) ↦ ⟪ι x, ι y⟫` (`ContinuousLinearMap.flip_gelfandDual_comp`).

## Main declarations

* `ContinuousLinearMap.gelfandDual`: the map `H → V*`, `h ↦ ⟪h, ι ·⟫`.
* `ContinuousLinearMap.gelfandDual_apply`: its defining formula.
* `ContinuousLinearMap.norm_gelfandDual`: its norm is `‖ι‖`.
* `ContinuousLinearMap.gelfandDual_injective`: it is injective when `ι` has dense range.
* `ContinuousLinearMap.flip_gelfandDual_comp`: the form `⟪ι x, ι y⟫` on `V` is symmetric.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., §5.9.2 and §7.1.
* E. Zeidler, *Nonlinear Functional Analysis and its Applications II/A*, Chapter 23.
-/

public section

noncomputable section

open scoped InnerProductSpace

namespace ContinuousLinearMap

variable {V H : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup H]
  [InnerProductSpace ℝ H] (ι : V →L[ℝ] H)

/-- The map `H → V*`, `h ↦ (x ↦ ⟪h, ι x⟫)`, induced by a continuous linear map `ι : V →L[ℝ] H`
into a real inner product space. When `ι` is injective with dense range this is the second
embedding of the Gelfand triple `V ↪ H ↪ V*`. -/
def gelfandDual : H →L[ℝ] StrongDual ℝ V :=
  ((compL ℝ V H ℝ).flip ι).comp (innerSL ℝ : H →L[ℝ] H →L[ℝ] ℝ)

/-- The defining formula of `ContinuousLinearMap.gelfandDual`. -/
@[simp]
theorem gelfandDual_apply (h : H) (x : V) : ι.gelfandDual h x = ⟪h, ι x⟫_ℝ := by
  simp [gelfandDual]

/-- The map `H → V*` of a Gelfand triple has the same norm as `ι`. -/
theorem norm_gelfandDual : ‖ι.gelfandDual‖ = ‖ι‖ := by
  refine le_antisymm (opNorm_le_bound _ (norm_nonneg _) fun h ↦
    opNorm_le_bound _ (by positivity) fun x ↦ ?_)
    (opNorm_le_bound ι (norm_nonneg ι.gelfandDual) fun x ↦ ?_)
  · rw [gelfandDual_apply, Real.norm_eq_abs]
    calc |⟪h, ι x⟫_ℝ| ≤ ‖h‖ * ‖ι x‖ := abs_real_inner_le_norm h (ι x)
      _ ≤ ‖h‖ * (‖ι‖ * ‖x‖) := by gcongr; exact ι.le_opNorm x
      _ = ‖ι‖ * ‖h‖ * ‖x‖ := by ring
  · -- Test `ι.gelfandDual (ι x)` on `x`: it returns `⟪ι x, ι x⟫ = ‖ι x‖²`.
    rcases (norm_nonneg (ι x)).eq_or_lt with hx | hx
    · rw [← hx]
      positivity
    refine le_of_mul_le_mul_left ?_ hx
    calc ‖ι x‖ * ‖ι x‖ = ι.gelfandDual (ι x) x := by
          rw [gelfandDual_apply, real_inner_self_eq_norm_mul_norm]
      _ ≤ ‖ι.gelfandDual (ι x) x‖ := Real.le_norm_self _
      _ ≤ ‖ι.gelfandDual‖ * ‖ι x‖ * ‖x‖ := ι.gelfandDual.le_opNorm₂ (ι x) x
      _ = ‖ι x‖ * (‖ι.gelfandDual‖ * ‖x‖) := by ring

/-- If `ι` has dense range, the map `H → V*` is injective: an element of `H` orthogonal to the
dense subspace `ι(V)` is zero. Together with an injective `ι`, this makes `V ↪ H ↪ V*` a chain
of continuous embeddings. -/
theorem gelfandDual_injective (hι : DenseRange ι) : Function.Injective ι.gelfandDual := by
  refine (injective_iff_map_eq_zero _).2 fun h hh ↦ hι.eq_zero_of_inner_left ℝ fun x ↦ ?_
  simpa using congr($hh x)

/-- The bilinear form `(x, y) ↦ ⟪ι x, ι y⟫` that the composite `V → H → V*` defines on `V` is
symmetric. -/
theorem flip_gelfandDual_comp : (ι.gelfandDual.comp ι).flip = ι.gelfandDual.comp ι := by
  ext x y
  simp [real_inner_comm]

end ContinuousLinearMap
