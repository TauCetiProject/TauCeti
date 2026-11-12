/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Extend
public import TauCeti.LinearAlgebra.Finsupp.LinearCombination
public import TauCeti.Topology.Algebra.Module.Span

/-!
# Equivalence of generating families

Two families are equivalent when the norms of their finite linear combinations are comparable
in both directions. These inequalities extend the correspondence between the families to a
continuous linear equivalence of their closed spans. In particular, they give the usual
criterion for equivalence of basic sequences, without assuming unconditional convergence.

We first construct the equivalence for families with dense span, retaining the given bounds
for the operator and its inverse. We then characterize equivalence of arbitrary closed spans.
The families need not be linearly independent, and their index set can be arbitrary.

The construction uses Mathlib's `LinearEquiv.extend` on finitely supported coefficient families.

## References

* F. Albiac and N. J. Kalton, *Topics in Banach Space Theory*, Chapter 1.
-/

public section

noncomputable section

open Set Submodule

namespace TauCeti

variable {𝕜 ι E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

section DenseSpan

variable [CompleteSpace E] [CompleteSpace F]
  (v : ι → E) (w : ι → F)
  (hv : Dense (span 𝕜 (range v) : Set E)) (hw : Dense (span 𝕜 (range w) : Set F))
  {C D : ℝ}
  (hC : ∀ a : ι →₀ 𝕜,
    ‖Finsupp.linearCombination 𝕜 w a‖ ≤ C * ‖Finsupp.linearCombination 𝕜 v a‖)
  (hD : ∀ a : ι →₀ 𝕜,
    ‖Finsupp.linearCombination 𝕜 v a‖ ≤ D * ‖Finsupp.linearCombination 𝕜 w a‖)

/-- Two-sided bounds on finite linear combinations extend the correspondence of densely
spanning families to a continuous linear equivalence. -/
def continuousLinearEquivOfLinearCombinationBounds : E ≃L[𝕜] F :=
  (LinearEquiv.refl 𝕜 (ι →₀ 𝕜)).extend
    (Finsupp.linearCombination 𝕜 v) (Finsupp.linearCombination 𝕜 w)
    (by simpa only [DenseRange, ← LinearMap.coe_range, Finsupp.range_linearCombination] using hv)
    ⟨C, hC⟩
    (by simpa only [DenseRange, ← LinearMap.coe_range, Finsupp.range_linearCombination] using hw)
    ⟨D, hD⟩

/-- The extension sends every finite linear combination to the corresponding combination. -/
@[simp]
theorem continuousLinearEquivOfLinearCombinationBounds_linearCombination (a : ι →₀ 𝕜) :
    continuousLinearEquivOfLinearCombinationBounds v w hv hw hC hD
      (Finsupp.linearCombination 𝕜 v a) = Finsupp.linearCombination 𝕜 w a := by
  simp [continuousLinearEquivOfLinearCombinationBounds]

/-- The extension sends each member of the first family to its counterpart. -/
@[simp]
theorem continuousLinearEquivOfLinearCombinationBounds_apply (i : ι) :
    continuousLinearEquivOfLinearCombinationBounds v w hv hw hC hD (v i) = w i := by
  simpa using continuousLinearEquivOfLinearCombinationBounds_linearCombination
    v w hv hw hC hD (Finsupp.single i 1)

/-- The inverse extension sends each member of the second family back to its counterpart. -/
@[simp]
theorem continuousLinearEquivOfLinearCombinationBounds_symm_apply (i : ι) :
    (continuousLinearEquivOfLinearCombinationBounds v w hv hw hC hD).symm (w i) = v i := by
  apply (continuousLinearEquivOfLinearCombinationBounds v w hv hw hC hD).injective
  simp

/-- The forward finite-combination bound is also an operator-norm bound. -/
theorem norm_continuousLinearEquivOfLinearCombinationBounds_le (hC₀ : 0 ≤ C) :
    ‖(continuousLinearEquivOfLinearCombinationBounds v w hv hw hC hD).toContinuousLinearMap‖
      ≤ C := by
  apply ContinuousLinearMap.opNorm_le_bound _ hC₀
  intro x
  exact LinearEquiv.norm_extend_le _ _ _ C
    (by simpa only [DenseRange, ← LinearMap.coe_range, Finsupp.range_linearCombination] using hv)
    hC
    (by simpa only [DenseRange, ← LinearMap.coe_range, Finsupp.range_linearCombination] using hw)
    ⟨D, hD⟩ x

/-- The backward finite-combination bound is also an inverse-operator-norm bound. -/
theorem norm_continuousLinearEquivOfLinearCombinationBounds_symm_le (hD₀ : 0 ≤ D) :
    ‖(continuousLinearEquivOfLinearCombinationBounds v w hv hw hC hD).symm.toContinuousLinearMap‖
      ≤ D := by
  apply ContinuousLinearMap.opNorm_le_bound _ hD₀
  exact LinearEquiv.norm_extend_symm_le _ _ _ D _ ⟨C, hC⟩ _ hD

/-- A continuous linear map agreeing with the correspondence on the generating family is the
constructed extension. -/
theorem continuousLinearEquivOfLinearCombinationBounds_unique (T : E →L[𝕜] F)
    (hT : ∀ i, T (v i) = w i) :
    T = (continuousLinearEquivOfLinearCombinationBounds v w hv hw hC hD).toContinuousLinearMap := by
  apply ContinuousLinearMap.ext_on hv
  rintro _ ⟨i, rfl⟩
  simp [hT]

end DenseSpan

/-- Families with two-sided finite-combination bounds have continuously linearly equivalent
closed spans, with the prescribed operator-norm bounds and prescribed values on the families. -/
theorem exists_continuousLinearEquiv_topologicalClosure_span_of_bounds
    (v : ι → E) (w : ι → F)
    [CompleteSpace (span 𝕜 (range v)).topologicalClosure]
    [CompleteSpace (span 𝕜 (range w)).topologicalClosure]
    {C D : ℝ} (hC₀ : 0 ≤ C) (hD₀ : 0 ≤ D)
    (hC : ∀ a : ι →₀ 𝕜,
      ‖Finsupp.linearCombination 𝕜 w a‖ ≤ C * ‖Finsupp.linearCombination 𝕜 v a‖)
    (hD : ∀ a : ι →₀ 𝕜,
      ‖Finsupp.linearCombination 𝕜 v a‖ ≤ D * ‖Finsupp.linearCombination 𝕜 w a‖) :
    ∃ T : (span 𝕜 (range v)).topologicalClosure ≃L[𝕜]
        (span 𝕜 (range w)).topologicalClosure,
      (∀ i, (T ⟨v i, (span 𝕜 (range v)).le_topologicalClosure
        (subset_span (mem_range_self i))⟩ : F) = w i) ∧
      ‖T.toContinuousLinearMap‖ ≤ C ∧ ‖T.symm.toContinuousLinearMap‖ ≤ D := by
  let v' : ι → (span 𝕜 (range v)).topologicalClosure := fun i ↦
    ⟨v i, (span 𝕜 (range v)).le_topologicalClosure (subset_span (mem_range_self i))⟩
  let w' : ι → (span 𝕜 (range w)).topologicalClosure := fun i ↦
    ⟨w i, (span 𝕜 (range w)).le_topologicalClosure (subset_span (mem_range_self i))⟩
  have hvw : ∀ a : ι →₀ 𝕜,
      ‖Finsupp.linearCombination 𝕜 w' a‖ ≤ C * ‖Finsupp.linearCombination 𝕜 v' a‖ := by
    simpa only [← Submodule.norm_coe, Submodule.coe_linearCombination] using hC
  have hwv : ∀ a : ι →₀ 𝕜,
      ‖Finsupp.linearCombination 𝕜 v' a‖ ≤ D * ‖Finsupp.linearCombination 𝕜 w' a‖ := by
    simpa only [← Submodule.norm_coe, Submodule.coe_linearCombination] using hD
  refine ⟨continuousLinearEquivOfLinearCombinationBounds v' w'
    (dense_span_in_topologicalClosure v) (dense_span_in_topologicalClosure w) hvw hwv, ?_,
    norm_continuousLinearEquivOfLinearCombinationBounds_le _ _ _ _ _ _ hC₀,
    norm_continuousLinearEquivOfLinearCombinationBounds_symm_le _ _ _ _ _ _ hD₀⟩
  intro i
  exact congrArg Subtype.val
    (continuousLinearEquivOfLinearCombinationBounds_apply _ _ _ _ _ _ i)

/-- The finite-combination criterion for equivalence of families: their closed spans admit a
continuous linear equivalence sending one family to the other exactly when their finite linear
combinations satisfy norm bounds in both directions. -/
theorem exists_continuousLinearEquiv_topologicalClosure_span_iff
    (v : ι → E) (w : ι → F)
    [CompleteSpace (span 𝕜 (range v)).topologicalClosure]
    [CompleteSpace (span 𝕜 (range w)).topologicalClosure] :
    (∃ T : (span 𝕜 (range v)).topologicalClosure ≃L[𝕜]
        (span 𝕜 (range w)).topologicalClosure,
      ∀ i, (T ⟨v i, (span 𝕜 (range v)).le_topologicalClosure
        (subset_span (mem_range_self i))⟩ : F) = w i) ↔
    ∃ C D : ℝ, 0 ≤ C ∧ 0 ≤ D ∧
      (∀ a : ι →₀ 𝕜,
        ‖Finsupp.linearCombination 𝕜 w a‖ ≤ C * ‖Finsupp.linearCombination 𝕜 v a‖) ∧
      (∀ a : ι →₀ 𝕜,
        ‖Finsupp.linearCombination 𝕜 v a‖ ≤ D * ‖Finsupp.linearCombination 𝕜 w a‖) := by
  constructor
  · rintro ⟨T, hT⟩
    let v' : ι → (span 𝕜 (range v)).topologicalClosure := fun i ↦
      ⟨v i, (span 𝕜 (range v)).le_topologicalClosure (subset_span (mem_range_self i))⟩
    let w' : ι → (span 𝕜 (range w)).topologicalClosure := fun i ↦
      ⟨w i, (span 𝕜 (range w)).le_topologicalClosure (subset_span (mem_range_self i))⟩
    have hTw : ∀ i, T (v' i) = w' i := fun i ↦ Subtype.ext (hT i)
    have hTv : ∀ i, T.symm (w' i) = v' i := fun i ↦ by rw [← hTw i]; simp
    refine ⟨‖T.toContinuousLinearMap‖, ‖T.symm.toContinuousLinearMap‖,
      norm_nonneg _, norm_nonneg _, ?_, ?_⟩
    · intro a
      have hmap : T (Finsupp.linearCombination 𝕜 v' a) =
          Finsupp.linearCombination 𝕜 w' a := by
        simpa only [LinearEquiv.coe_coe, ContinuousLinearEquiv.coe_toLinearEquiv,
          Function.comp_def, hTw] using
          Finsupp.apply_linearCombination 𝕜 T.toLinearEquiv.toLinearMap v' a
      have h := T.toContinuousLinearMap.le_opNorm (Finsupp.linearCombination 𝕜 v' a)
      simp only [ContinuousLinearEquiv.coe_coe, hmap] at h
      simpa only [← Submodule.norm_coe, Submodule.coe_linearCombination] using h
    · intro a
      have hmap : T.symm (Finsupp.linearCombination 𝕜 w' a) =
          Finsupp.linearCombination 𝕜 v' a := by
        simpa only [LinearEquiv.coe_coe, ContinuousLinearEquiv.coe_toLinearEquiv,
          Function.comp_def, hTv] using
          Finsupp.apply_linearCombination 𝕜 T.symm.toLinearEquiv.toLinearMap w' a
      have h := T.symm.toContinuousLinearMap.le_opNorm (Finsupp.linearCombination 𝕜 w' a)
      simp only [ContinuousLinearEquiv.coe_coe, hmap] at h
      simpa only [← Submodule.norm_coe, Submodule.coe_linearCombination] using h
  · rintro ⟨C, D, hC₀, hD₀, hC, hD⟩
    obtain ⟨T, hT, _, _⟩ :=
      exists_continuousLinearEquiv_topologicalClosure_span_of_bounds v w hC₀ hD₀ hC hD
    exact ⟨T, hT⟩

end TauCeti
