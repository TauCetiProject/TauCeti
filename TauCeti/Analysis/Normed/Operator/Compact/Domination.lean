/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giada Franz, The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.Compact.Interpolation
public import TauCeti.Analysis.Normed.Operator.Compact.Pi
public import Mathlib.Analysis.Normed.Group.Constructions

/-!
# Operators dominated by compact operators

Let `T : X → Y` be a linear map into a Banach space and `K₁, …, Kₘ` finitely many
compact operators out of `X`. If `‖T x‖ ≤ C (‖K₁ x‖ + ⋯ + ‖Kₘ x‖)` for every `x`, then `T` is
compact. Indeed the image of the unit ball under `(K₁, …, Kₘ)` is totally bounded, and the
domination transfers a finite net of it to a finite net of the image of the unit ball under `T`.

This is the form in which compactness of a global embedding is reduced to compactness of local
pieces, for instance for Sobolev spaces defined through finitely many charts.

## Main results

* `IsCompactOperator.of_norm_le_mul_sum`: an operator dominated by finitely many compact operators
  is compact.
* `IsCompactOperator.of_enorm_le_mul_sum`: the same, with extended norms.
-/

public section

open Metric Set

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {ι : Type*} [Fintype ι] {X Y : Type*}
  [SeminormedAddCommGroup X] [NormedSpace 𝕜 X] [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
  [CompleteSpace Y]
  {Z : ι → Type*} [∀ i, SeminormedAddCommGroup (Z i)] [∀ i, NormedSpace 𝕜 (Z i)]

/-- **Domination by compact operators.** A linear map into a Banach space whose norm is
bounded by a multiple of the sum of the norms of finitely many compact operators is compact. -/
theorem IsCompactOperator.of_norm_le_mul_sum (T : X →ₗ[𝕜] Y) (K : ∀ i, X →L[𝕜] Z i)
    (hK : ∀ i, IsCompactOperator (K i)) {C : ℝ} (h : ∀ x, ‖T x‖ ≤ C * ∑ i, ‖K i x‖) :
    IsCompactOperator T := by
  classical
  let P : X →L[𝕜] ∀ i, Z i := ContinuousLinearMap.pi K
  set C' := max C 0
  have hdom (x : X) : ‖T x‖ ≤ (C' * Fintype.card ι) * ‖P x‖ := by
    refine (h x).trans ?_
    calc C * ∑ i, ‖K i x‖ ≤ C' * ∑ i, ‖K i x‖ :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (Finset.sum_nonneg fun i _ ↦ norm_nonneg _)
      _ ≤ C' * (Fintype.card ι * ‖P x‖) := by
          refine mul_le_mul_of_nonneg_left ?_ (le_max_right _ _)
          simpa only [nsmul_eq_mul, P, ContinuousLinearMap.pi_apply] using
            Pi.sum_norm_apply_le_norm (P x)
      _ = C' * Fintype.card ι * ‖P x‖ := by ring
  exact (IsCompactOperator.pi hK).of_norm_le_mul_norm (T₀ := P.toLinearMap) fun x ↦ by
    simpa only [ContinuousLinearMap.coe_coe] using hdom x

/-- **Domination by compact operators, extended-norm form.** A linear map into a Banach
space whose extended norm is bounded by a finite multiple of the sum of the extended norms of
finitely many compact operators is compact. -/
theorem IsCompactOperator.of_enorm_le_mul_sum (T : X →ₗ[𝕜] Y) (K : ∀ i, X →L[𝕜] Z i)
    (hK : ∀ i, IsCompactOperator (K i)) {C : ENNReal} (hC : C ≠ ⊤)
    (h : ∀ x, ‖T x‖ₑ ≤ C * ∑ i, ‖K i x‖ₑ) : IsCompactOperator T := by
  refine IsCompactOperator.of_norm_le_mul_sum T K hK (C := C.toReal) fun x ↦ ?_
  have hfin : C * ∑ i, ‖K i x‖ₑ ≠ ⊤ :=
    ENNReal.mul_ne_top hC (ENNReal.sum_ne_top.mpr fun i _ ↦ eNorm_ne_top)
  have := ENNReal.toReal_mono hfin (h x)
  rwa [toReal_eNorm, ENNReal.toReal_mul, ENNReal.toReal_sum fun i _ ↦ eNorm_ne_top] at this
