/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giada Franz, The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import Mathlib.Analysis.Normed.Group.Constructions

/-!
# Operators dominated by compact operators

Let `T : X → Y` be a continuous linear map into a Banach space and `K₁, …, Kₘ` finitely many
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

variable {ι : Type*} [Fintype ι] {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
  {Z : ι → Type*} [∀ i, NormedAddCommGroup (Z i)] [∀ i, NormedSpace ℝ (Z i)]

private theorem IsCompactOperator.of_norm_le_of_totallyBounded_image_ball
    {W : Type*} [NormedAddCommGroup W] (T : X →L[ℝ] Y) (P : X → W)
    (hP : TotallyBounded (P '' ball 0 1)) (hPsub : ∀ x y, P (x - y) = P x - P y)
    {D : ℝ} (hD : 0 ≤ D) (hdom : ∀ x, ‖T x‖ ≤ D * ‖P x‖) :
    IsCompactOperator T := by
  classical
  refine (isCompactOperator_iff_isCompact_closure_image_ball (T : X →ₗ[ℝ] Y) one_pos).mpr ?_
  rw [isCompact_iff_totallyBounded_isComplete]
  refine ⟨TotallyBounded.closure ?_, isClosed_closure.isComplete⟩
  rw [Metric.totallyBounded_iff]
  intro ε hε
  set E := D + 1
  have hE : 0 < E := by positivity
  obtain ⟨t, ht, hcover⟩ := Metric.totallyBounded_iff.mp hP (ε / E / 2) (by positivity)
  let good : Set W := {y ∈ t | ∃ x ∈ ball (0 : X) 1, dist (P x) y < ε / E / 2}
  have hgood : good.Finite := ht.subset fun y hy ↦ hy.1
  let pick : W → X := fun y ↦
    if hy : ∃ x ∈ ball (0 : X) 1, dist (P x) y < ε / E / 2 then hy.choose else 0
  refine ⟨(fun y ↦ T (pick y)) '' good, hgood.image _, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨y, hyt, hy⟩ := mem_iUnion₂.mp (hcover ⟨x, hx, rfl⟩)
  have hex : ∃ x ∈ ball (0 : X) 1, dist (P x) y < ε / E / 2 := ⟨x, hx, hy⟩
  have hpick : dist (P (pick y)) y < ε / E / 2 := by
    simp only [pick, hex, ↓reduceDIte]
    exact hex.choose_spec.2
  refine mem_iUnion₂.mpr ⟨T (pick y), ⟨y, ⟨hyt, hex⟩, rfl⟩, ?_⟩
  have hPx : ‖P x - P (pick y)‖ < ε / E := by
    rw [← dist_eq_norm]
    calc dist (P x) (P (pick y)) ≤ dist (P x) y + dist (P (pick y)) y :=
          dist_triangle_right _ _ _
      _ < ε / E / 2 + ε / E / 2 := add_lt_add hy hpick
      _ = ε / E := by ring
  rw [mem_ball, dist_eq_norm]
  change ‖T x - T (pick y)‖ < ε
  rw [← map_sub]
  calc ‖T (x - pick y)‖ ≤ D * ‖P (x - pick y)‖ := hdom _
    _ ≤ D * (ε / E) := by
        rw [hPsub]
        exact mul_le_mul_of_nonneg_left hPx.le hD
    _ < ε := by
        rw [mul_div_assoc', div_lt_iff₀ hE]
        nlinarith

/-- **Domination by compact operators.** A continuous linear map into a Banach space whose norm is
bounded by a multiple of the sum of the norms of finitely many compact operators is compact. -/
theorem IsCompactOperator.of_norm_le_mul_sum (T : X →L[ℝ] Y) (K : ∀ i, X →L[ℝ] Z i)
    (hK : ∀ i, IsCompactOperator (K i)) {C : ℝ} (h : ∀ x, ‖T x‖ ≤ C * ∑ i, ‖K i x‖) :
    IsCompactOperator T := by
  classical
  let P : X → ∀ i, Z i := fun x i ↦ K i x
  have hP : TotallyBounded (P '' ball 0 1) := by
    refine (isCompact_univ_pi fun i ↦ (hK i).isCompact_closure_image_ball 1).totallyBounded.subset
      ?_
    rintro _ ⟨x, hx, rfl⟩ i -
    exact subset_closure ⟨x, hx, rfl⟩
  set C' := max C 0
  have hdom (x : X) : ‖T x‖ ≤ (C' * Fintype.card ι) * ‖P x‖ := by
    refine (h x).trans ?_
    calc C * ∑ i, ‖K i x‖ ≤ C' * ∑ i, ‖K i x‖ :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (Finset.sum_nonneg fun i _ ↦ norm_nonneg _)
      _ ≤ C' * (Fintype.card ι * ‖P x‖) := by
          refine mul_le_mul_of_nonneg_left ?_ (le_max_right _ _)
          calc ∑ i, ‖K i x‖ ≤ ∑ _i : ι, ‖P x‖ :=
                Finset.sum_le_sum fun i _ ↦ norm_le_pi_norm (P x) i
            _ = Fintype.card ι * ‖P x‖ := by simp
      _ = C' * Fintype.card ι * ‖P x‖ := by ring
  refine IsCompactOperator.of_norm_le_of_totallyBounded_image_ball T P hP ?_
    (by positivity) hdom
  intro x y
  change (fun i ↦ K i (x - y)) = (fun i ↦ K i x) - (fun i ↦ K i y)
  funext i
  simp

/-- **Domination by compact operators, extended-norm form.** A continuous linear map into a Banach
space whose extended norm is bounded by a finite multiple of the sum of the extended norms of
finitely many compact operators is compact. -/
theorem IsCompactOperator.of_enorm_le_mul_sum (T : X →L[ℝ] Y) (K : ∀ i, X →L[ℝ] Z i)
    (hK : ∀ i, IsCompactOperator (K i)) {C : ENNReal} (hC : C ≠ ⊤)
    (h : ∀ x, ‖T x‖ₑ ≤ C * ∑ i, ‖K i x‖ₑ) : IsCompactOperator T := by
  refine IsCompactOperator.of_norm_le_mul_sum T K hK (C := C.toReal) fun x ↦ ?_
  have hfin : C * ∑ i, ‖K i x‖ₑ ≠ ⊤ :=
    ENNReal.mul_ne_top hC (ENNReal.sum_ne_top.mpr fun i _ ↦ eNorm_ne_top)
  have := ENNReal.toReal_mono hfin (h x)
  rwa [toReal_eNorm, ENNReal.toReal_mul, ENNReal.toReal_sum fun i _ ↦ eNorm_ne_top] at this
