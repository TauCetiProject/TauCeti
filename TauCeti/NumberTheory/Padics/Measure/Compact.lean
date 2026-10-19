/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Padics.Measure.Topology
public import Mathlib.NumberTheory.Padics.ProperSpace
public import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# Weak compactness of integral measures

Integral measures on a compact space form a compact space for the weak topology of
integration against continuous integral tests. Evaluation embeds them as a closed subset of
the product of copies of `ℤ_[p]` indexed by test functions: its image consists exactly of the
linear functions that are `1`-Lipschitz. The uniform contraction bound follows by dividing a
nonzero test function by a value of maximal norm and using `ℤ_[p]`-linearity.

This supplies weak compactness without a countability hypothesis on the compact space.
No norm or topology instance on measures is installed.

## Main declarations

* `TauCeti.AbstractMeasure.norm_integral_apply_le μ f` bounds the integral of a test function.
* `TauCeti.AbstractMeasure.lipschitzWith_integral μ` gives the uniform Lipschitz bound.
* `TauCeti.AbstractMeasure.isClosedEmbedding_integral_eval_weak` gives the closed evaluation image.
* `TauCeti.AbstractMeasure.compactSpace_integralMeasures_weak` gives weak compactness.

## References

J. Rodrigues Jacinto and C. Williams, *An introduction to p-adic L-functions*,
Proposition 3.16 and Remarks 3.11 and 3.28.
-/

public section

open ContinuousMap Topology
open _root_.AbstractMeasure

namespace TauCeti.AbstractMeasure

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] {p : ℕ} [Fact p.Prime]

/-- An integral measure contracts the supremum norm of its test functions. -/
theorem norm_integral_apply_le (μ : D(X, ℤ_[p])) (f : C(X, ℤ_[p])) :
    ‖μ f‖ ≤ ‖f‖ := by
  by_cases hf : f = 0
  · simp [hf]
  cases isEmpty_or_nonempty X with
  | inl h => exact (hf (Subsingleton.elim _ _)).elim
  | inr h =>
    obtain ⟨x, _, hx⟩ := isCompact_univ.exists_isMaxOn Set.univ_nonempty
      f.continuous.norm.continuousOn
    have ha : f x ≠ 0 := by
      intro ha
      apply hf
      ext y
      exact norm_eq_zero.mp (le_antisymm (by simpa [ha] using hx (Set.mem_univ y))
        (norm_nonneg _))
    have ha' : (f x : ℚ_[p]) ≠ 0 := PadicInt.coe_ne_zero.mpr ha
    have hdiv (y : X) : ‖(f y : ℚ_[p]) / (f x : ℚ_[p])‖ ≤ 1 := by
      rw [norm_div, div_le_one (norm_pos_iff.mpr ha')]
      exact hx (Set.mem_univ y)
    let g : C(X, ℤ_[p]) := ⟨fun y ↦ ⟨(f y : ℚ_[p]) / (f x : ℚ_[p]), hdiv y⟩,
      ((continuous_subtype_val.comp f.continuous).div_const _).subtype_mk _⟩
    have hfg : f = f x • g := by
      ext y
      exact (mul_div_cancel₀ _ ha').symm
    calc
      ‖μ f‖ = ‖f x‖ * ‖μ g‖ := by rw [congrArg μ hfg, map_smul, norm_smul]
      _ ≤ ‖f x‖ * 1 := mul_le_mul_of_nonneg_left (PadicInt.norm_le_one _) (norm_nonneg _)
      _ ≤ ‖f‖ := by simpa using f.norm_coe_le_norm x

/-- Integral measures are uniformly `1`-Lipschitz on the space of integral tests. -/
theorem lipschitzWith_integral (μ : D(X, ℤ_[p])) : LipschitzWith 1 μ := by
  refine lipschitzWith_iff_dist_le_mul.mpr fun f g ↦ ?_
  simpa only [dist_eq_norm, ← map_sub, NNReal.coe_one, one_mul] using
    norm_integral_apply_le μ (f - g)

/-- Evaluation on all integral tests is a closed embedding for the weak topology. -/
theorem isClosedEmbedding_integral_eval_weak :
    @IsClosedEmbedding _ _ (WeakTopology (X := X) (R := ℤ_[p]) (E := ℤ_[p])) _
      (fun μ : D(X, ℤ_[p]) ↦ fun f : C(X, ℤ_[p]) ↦ μ f) := by
  let : TopologicalSpace D(X, ℤ_[p]) := WeakTopology
  refine ⟨⟨⟨rfl⟩, DFunLike.coe_injective⟩, ?_⟩
  have hrange : Set.range (fun μ : D(X, ℤ_[p]) ↦ fun f : C(X, ℤ_[p]) ↦ μ f) =
      Set.range ((↑) : (C(X, ℤ_[p]) →ₗ[ℤ_[p]] ℤ_[p]) → C(X, ℤ_[p]) → ℤ_[p]) ∩
        {F | LipschitzWith 1 F} := by
    ext F
    constructor
    · rintro ⟨μ, rfl⟩
      exact ⟨⟨(toCLMEquiv μ).toLinearMap, funext (coe_toCLMEquiv μ)⟩,
        lipschitzWith_integral μ⟩
    · rintro ⟨⟨L, rfl⟩, hL⟩
      exact ⟨toCLMEquiv.symm ⟨L, hL.continuous⟩,
        funext (coe_symm_toCLMEquiv ⟨L, hL.continuous⟩)⟩
  rw [hrange]
  exact (LinearMap.isClosed_range_coe _ _ _).inter (isClosed_setOfPred_lipschitzWith 1)

/-- Integral measures on any compact space are compact for the weak topology.
The domain need not have a countable basis. -/
theorem compactSpace_integralMeasures_weak :
    @CompactSpace D(X, ℤ_[p]) (WeakTopology (X := X) (R := ℤ_[p]) (E := ℤ_[p])) := by
  let : TopologicalSpace D(X, ℤ_[p]) := WeakTopology
  exact isClosedEmbedding_integral_eval_weak.compactSpace

end TauCeti.AbstractMeasure
