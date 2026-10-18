/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Padics.Measure.ExtendCoefficients
public import Mathlib.NumberTheory.Padics.Measure.Topology
public import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# Weak compactness of integral measures

Integral measures on a profinite space form a compact space for the weak topology of
integration against continuous integral tests. Evaluation embeds them as a closed subset of
the product of copies of `ℤ_[p]` indexed by test functions: its image consists exactly of the
linear functions that are `1`-Lipschitz. The uniform contraction bound follows from extension
of coefficients to `ℚ_[p]`, whose operator norm is at most one.

This supplies weak compactness without a countability hypothesis on the profinite space.
No norm or topology instance on measures is installed.

## References

J. Rodrigues Jacinto and C. Williams, *An introduction to p-adic L-functions*,
Proposition 3.16 and Remarks 3.11 and 3.28.
-/

public section

open ContinuousMap Topology
open _root_.AbstractMeasure

namespace TauCeti.AbstractMeasure

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
  [TotallyDisconnectedSpace X] {p : ℕ} [Fact p.Prime]

/-- An integral measure contracts the supremum norm of its test functions. -/
theorem norm_integral_apply_le (μ : D(X, ℤ_[p])) (f : C(X, ℤ_[p])) :
    ‖μ f‖ ≤ ‖f‖ := by
  let j : ℤ_[p] →+* ℚ_[p] := PadicInt.Coe.ringHom
  have hj : ∀ a, ‖j a‖ ≤ 1 := by simpa [j] using PadicInt.norm_le_one
  have hjc : Continuous j := continuous_subtype_val
  let g : C(X, ℚ_[p]) := (⟨j, hjc⟩ : C(ℤ_[p], ℚ_[p])).comp f
  have hg : ‖g‖ ≤ ‖f‖ := by
    refine (ContinuousMap.norm_le _ (norm_nonneg _)).mpr fun x ↦ ?_
    simpa [g, j] using f.norm_coe_le_norm x
  calc
    ‖μ f‖ = ‖extendCoefficients j hj μ g‖ := by
      simp only [g, extendCoefficients_apply_comp j μ hj hjc]
      simp [j]
    _ ≤ 1 * ‖g‖ := by
      simpa only [coe_toCLMEquiv] using
        (toCLMEquiv (extendCoefficients j hj μ)).le_of_opNorm_le
          (norm_toCLMEquiv_extendCoefficients_le j hj μ) g
    _ ≤ ‖f‖ := by simpa using hg

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

/-- Integral measures on any profinite space are compact for the weak topology.
The domain need not have a countable basis. -/
theorem compactSpace_integralMeasures_weak :
    @CompactSpace D(X, ℤ_[p]) (WeakTopology (X := X) (R := ℤ_[p]) (E := ℤ_[p])) := by
  let : TopologicalSpace D(X, ℤ_[p]) := WeakTopology
  exact isClosedEmbedding_integral_eval_weak.compactSpace

end TauCeti.AbstractMeasure
