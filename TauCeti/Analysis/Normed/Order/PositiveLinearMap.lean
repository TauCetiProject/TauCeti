/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Module.PositiveLinearMap
public import Mathlib.Analysis.Normed.Operator.Basic

/-!
# Positive linear functionals dominated by a unit

Let `E` be a real seminormed space with an order, and let `u : E` satisfy `f ≤ ‖f‖ • u` for every
`f : E`. For bounded real functions with the supremum norm, `u = 1` has this property, and so does
the class of `1` in `L∞`. A positive real linear functional `φ` on `E` is then controlled by its
value at `u`:

```text
|φ f| ≤ φ u * ‖f‖.
```

Hence `φ` is automatically Lipschitz and continuous, and when `‖u‖ ≤ 1` its operator norm is
exactly `φ u`. In particular a positive functional normalized by `φ u = 1`, such as a mean on a
space of bounded functions, has operator norm one.

The lemmas are stated for any type of positive linear maps, in the sense of `LinearMapClass` and
`OrderHomClass`, following the convention of `Mathlib.Algebra.Order.Module.PositiveLinearMap`.
No continuity is assumed. Compare `PositiveLinearMap.exists_norm_apply_le`, the corresponding
automatic continuity for positive maps between C⋆-algebras.

## Main results

* `PositiveLinearMap.abs_apply_le_mul_norm`: the bound `|φ f| ≤ φ u * ‖f‖`.
* `PositiveLinearMap.lipschitzWith_of_forall_le_norm_smul`: `φ` is `φ u`-Lipschitz.
* `ContinuousLinearMap.opNorm_eq_apply_of_monotone`: a monotone continuous linear functional has
  operator norm `ψ u` when `‖u‖ ≤ 1`.
-/

public section

open scoped NNReal

namespace PositiveLinearMap

variable {F E : Type*} [SeminormedAddCommGroup E] [Module ℝ E] [LE E]
  [FunLike F E ℝ] [LinearMapClass F ℝ E ℝ] [OrderHomClass F E ℝ] (φ : F) {u : E}

/-- A positive linear functional is bounded above by its value at a dominating element `u`, scaled
by the norm. -/
theorem apply_le_mul_norm (hu : ∀ f : E, f ≤ ‖f‖ • u) (f : E) : φ f ≤ φ u * ‖f‖ := by
  simpa [mul_comm] using map_rel φ (hu f)

/-- A positive linear functional is controlled in absolute value by its value at a dominating
element `u`, scaled by the norm. -/
theorem abs_apply_le_mul_norm (hu : ∀ f : E, f ≤ ‖f‖ • u) (f : E) : |φ f| ≤ φ u * ‖f‖ := by
  refine abs_le.2 ⟨neg_le.1 ?_, apply_le_mul_norm φ hu f⟩
  simpa using apply_le_mul_norm φ hu (-f)

/-- A positive linear functional is nonnegative at a dominating element `u`. -/
theorem apply_nonneg_of_forall_le_norm_smul (hu : ∀ f : E, f ≤ ‖f‖ • u) : 0 ≤ φ u := by
  have := apply_le_mul_norm φ hu (-u)
  rw [map_neg, norm_neg] at this
  nlinarith [norm_nonneg u]

/-- A positive linear functional is controlled by its value at a dominating element `u`, scaled by
the norm of the difference of the arguments. -/
theorem abs_apply_sub_apply_le_mul_norm (hu : ∀ f : E, f ≤ ‖f‖ • u) (f g : E) :
    |φ f - φ g| ≤ φ u * ‖f - g‖ := by
  simpa using abs_apply_le_mul_norm φ hu (f - g)

/-- A positive linear functional is Lipschitz, with constant its value at a dominating
element `u`. -/
theorem lipschitzWith_of_forall_le_norm_smul (hu : ∀ f : E, f ≤ ‖f‖ • u) :
    LipschitzWith (φ u).toNNReal φ :=
  AddMonoidHomClass.lipschitz_of_bound φ _ fun f => abs_apply_le_mul_norm φ hu f

/-- A positive linear functional is continuous as soon as some element `u` dominates every `f`
in the sense `f ≤ ‖f‖ • u`. -/
theorem continuous_of_forall_le_norm_smul (hu : ∀ f : E, f ≤ ‖f‖ • u) : Continuous φ :=
  (lipschitzWith_of_forall_le_norm_smul φ hu).continuous

end PositiveLinearMap

namespace ContinuousLinearMap

variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E] [PartialOrder E] {u : E}

/-- A monotone continuous linear functional has operator norm equal to its value at an element
`u` of norm at most one dominating every `f` in the sense `f ≤ ‖f‖ • u`. -/
theorem opNorm_eq_apply_of_monotone (ψ : E →L[ℝ] ℝ) (hψ : Monotone ψ)
    (hu : ∀ f : E, f ≤ ‖f‖ • u) (hu₁ : ‖u‖ ≤ 1) : ‖ψ‖ = ψ u := by
  let φ : E →ₚ[ℝ] ℝ := { toLinearMap := ψ.toLinearMap, monotone' := hψ }
  have hφ (f : E) : φ f = ψ f := rfl
  have hnonneg : 0 ≤ ψ u := hφ u ▸ PositiveLinearMap.apply_nonneg_of_forall_le_norm_smul φ hu
  refine le_antisymm (ψ.opNorm_le_bound hnonneg fun f => ?_) ?_
  · simpa [hφ] using PositiveLinearMap.abs_apply_le_mul_norm φ hu f
  · calc ψ u ≤ ‖ψ u‖ := Real.le_norm_self _
      _ ≤ ‖ψ‖ * ‖u‖ := ψ.le_opNorm u
      _ ≤ ‖ψ‖ := mul_le_of_le_one_right (norm_nonneg ψ) hu₁

end ContinuousLinearMap
