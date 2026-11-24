/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Module.PositiveLinearMap
public import Mathlib.Analysis.Normed.Operator.Basic
import TauCeti.Algebra.Order.Ring.Abs
import TauCeti.Analysis.Normed.Order.OrderUnit

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
The basic bound `abs_apply_le_mul_norm` takes the order preservation as an explicit hypothesis
instead, so that it also covers monotone functionals on a preordered space. No continuity is
assumed. Compare `PositiveLinearMap.exists_norm_apply_le`, the corresponding
automatic continuity for positive maps between C⋆-algebras.

These are the real-valued cases, with target `ℝ` and order unit `1`, of the bounds
`TauCeti.IsOrderUnitNorm.norm_map_le` and `TauCeti.IsOrderUnitNorm.opNorm_eq_norm_apply` for
positive maps into an order-unit space, and are derived from them.

## Main results

* `PositiveLinearMap.abs_apply_le_mul_norm`: the bound `|φ f| ≤ φ u * ‖f‖` for an
  order-preserving linear functional `φ`.
* `PositiveLinearMap.apply_eq_zero_of_apply_eq_zero`: an order-preserving linear functional
  vanishing at `u` vanishes identically.
* `PositiveLinearMap.lipschitzWith_of_forall_le_norm_smul`: `φ` is `φ u`-Lipschitz.
* `ContinuousLinearMap.opNorm_eq_apply_of_monotone`: a monotone continuous linear functional has
  operator norm `ψ u` when `‖u‖ ≤ 1`.
* `LinearMapClass.apply_nonneg_of_abs_apply_le_mul_norm`: conversely, a linear functional with
  `|ψ f| ≤ ψ u * ‖f‖` is nonnegative at every `f` with `‖‖f‖ • u - f‖ ≤ ‖f‖`.
-/

public section

open scoped NNReal
open TauCeti (nonneg_of_abs_le_mul)

namespace PositiveLinearMap

variable {F E : Type*} [SeminormedAddCommGroup E] [Module ℝ E] [LE E]
  [FunLike F E ℝ] [LinearMapClass F ℝ E ℝ] {u : E}

/-- An order-preserving linear functional is controlled in absolute value by its value at a
dominating element `u`, scaled by the norm. Order preservation is an explicit hypothesis, so this
also applies to monotone functionals on a preordered space, which do not bundle into
`E →ₚ[ℝ] ℝ`; for a positive linear map `φ`, pass `fun _ _ => map_rel φ`. -/
theorem abs_apply_le_mul_norm (φ : F) (hφ : ∀ ⦃f g : E⦄, f ≤ g → φ f ≤ φ g)
    (hu : ∀ f : E, f ≤ ‖f‖ • u) (f : E) : |φ f| ≤ φ u * ‖f‖ := by
  -- `φ u` is nonnegative, since `-φ u ≤ ‖u‖ * φ u`
  have hφu : 0 ≤ φ u := by
    have := hφ (hu (-u))
    rw [map_neg, norm_neg, map_smul, smul_eq_mul] at this
    nlinarith [norm_nonneg u]
  simpa [abs_of_nonneg hφu] using TauCeti.isOrderUnitNorm_real_one.norm_map_le hu φ hφ f

/-- An order-preserving linear functional vanishing at a dominating element `u` vanishes
identically. -/
theorem apply_eq_zero_of_apply_eq_zero (φ : F) (hφ : ∀ ⦃f g : E⦄, f ≤ g → φ f ≤ φ g)
    (hu : ∀ f : E, f ≤ ‖f‖ • u) (hφu : φ u = 0) (f : E) : φ f = 0 :=
  abs_nonpos_iff.1 (by simpa [hφu] using abs_apply_le_mul_norm φ hφ hu f)

variable [OrderHomClass F E ℝ] (φ : F)

/-- A positive linear functional is nonnegative at a dominating element `u`. -/
theorem apply_nonneg_of_forall_le_norm_smul (hu : ∀ f : E, f ≤ ‖f‖ • u) : 0 ≤ φ u :=
  nonneg_of_abs_le_mul (abs_apply_le_mul_norm φ (fun _ _ => map_rel φ) hu u) (norm_nonneg u)

/-- A positive linear functional is controlled by its value at a dominating element `u`, scaled by
the norm of the difference of the arguments. -/
theorem abs_apply_sub_apply_le_mul_norm (hu : ∀ f : E, f ≤ ‖f‖ • u) (f g : E) :
    |φ f - φ g| ≤ φ u * ‖f - g‖ := by
  simpa using abs_apply_le_mul_norm φ (fun _ _ => map_rel φ) hu (f - g)

/-- A positive linear functional is Lipschitz, with constant its value at a dominating
element `u`. -/
theorem lipschitzWith_of_forall_le_norm_smul (hu : ∀ f : E, f ≤ ‖f‖ • u) :
    LipschitzWith (φ u).toNNReal φ :=
  AddMonoidHomClass.lipschitz_of_bound φ _ (abs_apply_le_mul_norm φ (fun _ _ => map_rel φ) hu)

/-- A positive linear functional is continuous as soon as some element `u` dominates every `f`
in the sense `f ≤ ‖f‖ • u`. -/
theorem continuous_of_forall_le_norm_smul (hu : ∀ f : E, f ≤ ‖f‖ • u) : Continuous φ :=
  (lipschitzWith_of_forall_le_norm_smul φ hu).continuous

end PositiveLinearMap

namespace ContinuousLinearMap

variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E] [Preorder E] {u : E}

/-- A monotone continuous linear functional has operator norm equal to its value at an element
`u` of norm at most one dominating every `f` in the sense `f ≤ ‖f‖ • u`. -/
theorem opNorm_eq_apply_of_monotone (ψ : E →L[ℝ] ℝ) (hψ : Monotone ψ)
    (hu : ∀ f : E, f ≤ ‖f‖ • u) (hu₁ : ‖u‖ ≤ 1) : ‖ψ‖ = ψ u := by
  rw [TauCeti.isOrderUnitNorm_real_one.opNorm_eq_norm_apply hu hu₁ ψ hψ, Real.norm_of_nonneg]
  exact nonneg_of_abs_le_mul (PositiveLinearMap.abs_apply_le_mul_norm ψ hψ hu u) (norm_nonneg u)

end ContinuousLinearMap

namespace LinearMapClass

variable {E : Type*} [SeminormedAddCommGroup E] [Module ℝ E] {u : E}

/-- A converse to `PositiveLinearMap.abs_apply_le_mul_norm`: a linear functional `ψ` with
`|ψ g| ≤ ψ u * ‖g‖` for all `g` is nonnegative at every `f` with `‖‖f‖ • u - f‖ ≤ ‖f‖`. For
bounded real functions or real `L∞` with `u = 1`, every nonnegative `f` has this property. -/
theorem apply_nonneg_of_abs_apply_le_mul_norm {F : Type*} [FunLike F E ℝ]
    [LinearMapClass F ℝ E ℝ] (ψ : F) (hψ : ∀ g, |ψ g| ≤ ψ u * ‖g‖) {f : E}
    (hf : ‖‖f‖ • u - f‖ ≤ ‖f‖) : 0 ≤ ψ f := by
  have hu : 0 ≤ ψ u := nonneg_of_abs_le_mul (hψ u) (norm_nonneg u)
  have := (le_abs_self _).trans (hψ (‖f‖ • u - f))
  rw [map_sub, map_smul, smul_eq_mul] at this
  nlinarith [mul_le_mul_of_nonneg_left hf hu]

end LinearMapClass
