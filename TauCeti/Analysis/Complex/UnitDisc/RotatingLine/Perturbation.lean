/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.UnitDisc.RotatingLine.Pi
import TauCeti.Analysis.Calculus.ContinuousLinearMapInverse
import TauCeti.Analysis.Normed.Operator.Basic

/-!
# The perturbed real-boundary disc problem in Hölder spaces

Let `D` be the open unit disc, `0 < α < 1` and `ι` a finite index type. For coefficients
`A, B ∈ C^{0,α}(D, ℂ^ι →L[ℝ] ℂ^ι)` consider the augmented operator

`u ↦ (∂u/∂(conj z) + A ∂u/∂z + B u, u 0, ∂ₛu(0))`

(`TauCeti.perturbedAugmentedConjWirtingerDerivL`) on the closed subspace `X_3` of
`C^{1,α}(D, ℂ^ι)` cut out by the totally real boundary condition `e^{3iθ/2} ℝ^ι`
(`TauCeti.rotatingLinePiSubspace`). For `A = B = 0` it is the normalized disc solver
`TauCeti.rotatingLinePiAugmentedEquiv`, a Banach isomorphism onto
`C^{0,α}(D, ℂ^ι) × ℂ^ι × ℂ^ι`. The perturbation `u ↦ A ∂u/∂z + B u` is a bounded operator
depending continuously and linearly on `(A, B)`, so a Neumann series inverts the perturbed
operator for small coefficients. This gives:

* for `‖A‖, ‖B‖ < ε` the problem
  `∂u/∂(conj z) + A ∂u/∂z + B u = f`, `u 0 = a`, `∂ₛu(0) = b`, `u ∈ X_3`
  has exactly one solution for every forcing `f ∈ C^{0,α}` and all `a`, `b`, with the Schauder
  estimate `‖u‖_{C^{1,α}} ≤ C (‖f‖_{C^α} + |a| + |b|)`, where `C` does not depend on `A`, `B`
  (`TauCeti.exists_pos_existsUnique_perturbedAugmentedConjWirtingerDerivL_eq_and_norm_le`);
* the coefficients for which the operator is invertible form an open set, on which the inverse,
  and hence the solution, is a `C^n` function of the coefficients for every `n`, including
  `n = ω` (`TauCeti.contDiffOn_inverse_perturbedAugmentedConjWirtingerDerivL_comp_subtypeL`).
  This holds for any target space `F` in place of `ℂ^ι` and any complete subspace in place of
  `X_3`.

The forcing is an arbitrary Hölder function, so this is the local Hölder boundary problem of the
linear theory of holomorphic discs, which does not require the forcing to be Sobolev.

## Main declarations

* `TauCeti.perturbedAugmentedConjWirtingerDerivL`: the perturbed augmented operator.
* `exists_pos_isInvertible_perturbedAugmentedConjWirtingerDerivL_comp_subtypeL_and_norm_inverse_le`:
  invertibility on `X_3` for small coefficients, with a uniform bound on the inverse.
* `TauCeti.exists_pos_existsUnique_perturbedAugmentedConjWirtingerDerivL_eq_and_norm_le`: unique
  solvability with the uniform Schauder estimate.
* `TauCeti.isOpen_setOf_isInvertible_perturbedAugmentedConjWirtingerDerivL_comp_subtypeL` and
  `TauCeti.contDiffOn_inverse_perturbedAugmentedConjWirtingerDerivL_comp_subtypeL`: parameter
  dependence on any complete subspace of `C^{1,α}(D, F)`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications **52**, 2012, Appendix C (the boundary value problem on the disc).
-/

public section

noncomputable section

namespace TauCeti

open Metric Set TopologicalSpace CkHolderSpaceOn ContinuousLinearMap
open scoped NNReal

variable {α : ℝ≥0}

/-! ### The perturbed augmented operator -/

section operator

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

variable (F) in
/-- The augmented operator `u ↦ (∂u/∂(conj z) + A ∂u/∂z + B u, u 0, ∂ₛu(0))` on
`C^{1,α}(D, F)`, for the open unit disc `D`, `α ≤ 1` and coefficients
`A, B ∈ C^{0,α}(D, F →L[ℝ] F)`: the augmented Cauchy–Riemann operator
`TauCeti.augmentedConjWirtingerDerivL` plus the perturbation `u ↦ A ∂u/∂z + B u` in its first
component. -/
def perturbedAugmentedConjWirtingerDerivL (hα : α ≤ 1)
    (A B : HolderSpace α (unitBallOpens ℂ) (F →L[ℝ] F)) :
    CkHolderSpaceOn 1 α (unitBallOpens ℂ) F →L[ℝ] HolderSpace α (unitBallOpens ℂ) F × F × F :=
  augmentedConjWirtingerDerivL α F +
    inl ℝ _ _ ∘L wirtingerPerturbationL (unitBallOpens ℂ) F (convex_unitBallOpens ℂ) hα A B

/-- The components of the perturbed augmented operator. -/
@[simp]
theorem perturbedAugmentedConjWirtingerDerivL_apply (hα : α ≤ 1)
    (A B : HolderSpace α (unitBallOpens ℂ) (F →L[ℝ] F))
    (u : CkHolderSpaceOn 1 α (unitBallOpens ℂ) F) :
    perturbedAugmentedConjWirtingerDerivL F hα A B u =
      (conjWirtingerDerivL α (unitBallOpens ℂ) F u +
          wirtingerPerturbationL (unitBallOpens ℂ) F (convex_unitBallOpens ℂ) hα A B u,
        u.extend 0, fderiv ℝ u.extend 0 1) := by
  simp [perturbedAugmentedConjWirtingerDerivL]

/-- Without coefficients the perturbed augmented operator is the augmented Cauchy–Riemann
operator. -/
@[simp]
theorem perturbedAugmentedConjWirtingerDerivL_zero_zero (hα : α ≤ 1) :
    perturbedAugmentedConjWirtingerDerivL F hα 0 0 = augmentedConjWirtingerDerivL α F := by
  rw [perturbedAugmentedConjWirtingerDerivL, wirtingerPerturbationL_zero_zero, comp_zero,
    add_zero]

/-- The perturbed augmented operator depends continuously and affinely on its coefficients, so it
is a `C^n` function of them for every `n`, including `n = ω`. -/
theorem contDiff_perturbedAugmentedConjWirtingerDerivL (hα : α ≤ 1) {n : WithTop ℕ∞} :
    ContDiff ℝ n fun p : HolderSpace α (unitBallOpens ℂ) (F →L[ℝ] F) ×
        HolderSpace α (unitBallOpens ℂ) (F →L[ℝ] F) ↦
      perturbedAugmentedConjWirtingerDerivL F hα p.1 p.2 :=
  contDiff_const.add (contDiff_const.clm_comp
    (contDiff_wirtingerPerturbationL (Ω := unitBallOpens ℂ) (F := F) (convex_unitBallOpens ℂ) hα))

/-- The coefficients `(A, B)` for which the perturbed augmented operator is invertible on a
complete subspace `V` of `C^{1,α}(D, F)` form an open set. -/
theorem isOpen_setOf_isInvertible_perturbedAugmentedConjWirtingerDerivL_comp_subtypeL
    (hα : α ≤ 1) (V : Submodule ℝ (CkHolderSpaceOn 1 α (unitBallOpens ℂ) F)) [CompleteSpace V] :
    IsOpen {p : HolderSpace α (unitBallOpens ℂ) (F →L[ℝ] F) ×
        HolderSpace α (unitBallOpens ℂ) (F →L[ℝ] F) |
      (perturbedAugmentedConjWirtingerDerivL F hα p.1 p.2 ∘L V.subtypeL).IsInvertible} :=
  isOpen_setOfPred_isInvertible.preimage
    ((contDiff_perturbedAugmentedConjWirtingerDerivL (F := F) (n := 0) hα).continuous.clm_comp
      continuous_const)

/-- **Parameter dependence of the perturbed disc problem.** On the open set of coefficients
`(A, B)` for which the perturbed augmented operator is invertible on a complete subspace `V`
of `C^{1,α}(D, F)`, its inverse is a `C^n` function of `(A, B)` for every `n`, including
`n = ω`. For `F = ℂ^ι`, `V = X_3` and `0 < α < 1` this set contains every pair of coefficients of
small norm
(`exists_pos_isInvertible_perturbedAugmentedConjWirtingerDerivL_comp_subtypeL_and_norm_inverse_le`).
-/
theorem contDiffOn_inverse_perturbedAugmentedConjWirtingerDerivL_comp_subtypeL
    (hα : α ≤ 1) (V : Submodule ℝ (CkHolderSpaceOn 1 α (unitBallOpens ℂ) F)) [CompleteSpace V]
    {n : WithTop ℕ∞} :
    ContDiffOn ℝ n
      (fun p : HolderSpace α (unitBallOpens ℂ) (F →L[ℝ] F) ×
          HolderSpace α (unitBallOpens ℂ) (F →L[ℝ] F) ↦
        (perturbedAugmentedConjWirtingerDerivL F hα p.1 p.2 ∘L V.subtypeL).inverse)
      {p | (perturbedAugmentedConjWirtingerDerivL F hα p.1 p.2 ∘L V.subtypeL).IsInvertible} :=
  ContDiffOn.clm_inverse
    ((contDiff_perturbedAugmentedConjWirtingerDerivL hα).clm_comp contDiff_const).contDiffOn
    fun _ hp ↦ hp

end operator

/-! ### Invertibility for small coefficients on `ℂ^ι` -/

variable {ι : Type*} [Fintype ι]

/-- On `X_3`, the perturbed augmented operator differs from the unperturbed one by the
perturbation `u ↦ A ∂u/∂z + B u` in the first component, of norm at most `‖A‖ + 3 ‖B‖`. -/
private theorem norm_perturbedAugmentedConjWirtingerDerivL_comp_subtypeL_sub_le (hα : α ≤ 1)
    (A B : HolderSpace α (unitBallOpens ℂ) ((ι → ℂ) →L[ℝ] (ι → ℂ))) :
    ‖perturbedAugmentedConjWirtingerDerivL (ι → ℂ) hα A B ∘L
          (rotatingLinePiSubspace ι 3 α).subtypeL -
        augmentedConjWirtingerDerivL α (ι → ℂ) ∘L (rotatingLinePiSubspace ι 3 α).subtypeL‖ ≤
      ‖A‖ + 3 * ‖B‖ := by
  set P := wirtingerPerturbationL (unitBallOpens ℂ) (ι → ℂ) (convex_unitBallOpens ℂ) hα A B
  set ι₁ := inl ℝ (HolderSpace α (unitBallOpens ℂ) (ι → ℂ)) ((ι → ℂ) × (ι → ℂ))
  rw [← sub_comp, perturbedAugmentedConjWirtingerDerivL, add_sub_cancel_left]
  calc _ ≤ ‖ι₁ ∘L P‖ * ‖(rotatingLinePiSubspace ι 3 α).subtypeL‖ := opNorm_comp_le _ _
    _ ≤ ‖ι₁‖ * ‖P‖ * 1 := by
        gcongr
        exacts [opNorm_comp_le _ _, Submodule.norm_subtypeL_le _]
    _ ≤ 1 * (‖A‖ + 3 * ‖B‖) * 1 := by
        gcongr
        exacts [norm_inl_le_one _ _ _, norm_wirtingerPerturbationL_le _ _ _ _]
    _ = ‖A‖ + 3 * ‖B‖ := by ring

/-- **Invertibility of the perturbed disc problem.** For `0 < α < 1` there are `ε > 0` and `C`
such that for all coefficients `A, B ∈ C^{0,α}(D, ℂ^ι →L[ℝ] ℂ^ι)` of norm less than `ε`, the
operator `u ↦ (∂u/∂(conj z) + A ∂u/∂z + B u, u 0, ∂ₛu(0))` is a Banach isomorphism from the
elements of `C^{1,α}(D, ℂ^ι)` with boundary values in `e^{3iθ/2} ℝ^ι` onto
`C^{0,α}(D, ℂ^ι) × ℂ^ι × ℂ^ι`, and its inverse has norm at most `C`. -/
theorem
    exists_pos_isInvertible_perturbedAugmentedConjWirtingerDerivL_comp_subtypeL_and_norm_inverse_le
    (hα0 : 0 < α) (hα1 : α < 1) :
    ∃ ε > 0, ∃ C, ∀ A B : HolderSpace α (unitBallOpens ℂ) ((ι → ℂ) →L[ℝ] (ι → ℂ)),
      ‖A‖ < ε → ‖B‖ < ε →
        (perturbedAugmentedConjWirtingerDerivL (ι → ℂ) hα1.le A B ∘L
          (rotatingLinePiSubspace ι 3 α).subtypeL).IsInvertible ∧
        ‖(perturbedAugmentedConjWirtingerDerivL (ι → ℂ) hα1.le A B ∘L
          (rotatingLinePiSubspace ι 3 α).subtypeL).inverse‖ ≤ C := by
  set T := augmentedConjWirtingerDerivL α (ι → ℂ) ∘L (rotatingLinePiSubspace ι 3 α).subtypeL
  set M := ‖T.inverse‖
  have hT : T.IsInvertible :=
    ⟨rotatingLinePiAugmentedEquiv hα0 hα1, ext (rotatingLinePiAugmentedEquiv_apply hα0 hα1)⟩
  have hM : 0 ≤ M := norm_nonneg T.inverse
  refine ⟨(8 * (M + 1))⁻¹, by positivity, 2 * M, fun A B hA hB ↦ ?_⟩
  -- The perturbation has norm less than `4 ε`, so `M ‖S - T‖ ≤ 1 / 2` bounds the Neumann series.
  have hsmall : M * ‖perturbedAugmentedConjWirtingerDerivL (ι → ℂ) hα1.le A B ∘L
      (rotatingLinePiSubspace ι 3 α).subtypeL - T‖ ≤ 1 / 2 := by
    calc _ ≤ M * (‖A‖ + 3 * ‖B‖) := by
          gcongr
          exact norm_perturbedAugmentedConjWirtingerDerivL_comp_subtypeL_sub_le hα1.le A B
      _ ≤ (M + 1) * (4 * (8 * (M + 1))⁻¹) := by
          gcongr
          · linarith
          · linarith
      _ = 1 / 2 := by field_simp; ring
  have hlt := hsmall.trans_lt (by norm_num : (1 / 2 : ℝ) < 1)
  refine ⟨hT.of_mul_norm_sub_lt le_rfl hlt, ?_⟩
  calc _ ≤ M / (1 - M * ‖perturbedAugmentedConjWirtingerDerivL (ι → ℂ) hα1.le A B ∘L
        (rotatingLinePiSubspace ι 3 α).subtypeL - T‖) :=
        hT.norm_inverse_le_of_mul_norm_sub_lt le_rfl hlt
    _ ≤ M / (1 / 2) := by
        gcongr
        linarith
    _ = 2 * M := by ring

/-- **Unique solvability of the perturbed disc problem, with a uniform Schauder estimate.** For
`0 < α < 1` there are `ε > 0` and `C` such that for all coefficients
`A, B ∈ C^{0,α}(D, ℂ^ι →L[ℝ] ℂ^ι)` of norm less than `ε`:
for every forcing `f ∈ C^{0,α}(D, ℂ^ι)` and all `a, b ∈ ℂ^ι` exactly one element `u` of
`C^{1,α}(D, ℂ^ι)` with boundary values in `e^{3iθ/2} ℝ^ι` solves
`∂u/∂(conj z) + A ∂u/∂z + B u = f`, `u 0 = a`, `∂ₛu(0) = b`; and every such `u` satisfies
`‖u‖ ≤ C ‖(∂u/∂(conj z) + A ∂u/∂z + B u, u 0, ∂ₛu(0))‖`. -/
theorem exists_pos_existsUnique_perturbedAugmentedConjWirtingerDerivL_eq_and_norm_le
    (hα0 : 0 < α) (hα1 : α < 1) :
    ∃ ε > 0, ∃ C, ∀ A B : HolderSpace α (unitBallOpens ℂ) ((ι → ℂ) →L[ℝ] (ι → ℂ)),
      ‖A‖ < ε → ‖B‖ < ε →
        (∀ y : HolderSpace α (unitBallOpens ℂ) (ι → ℂ) × (ι → ℂ) × (ι → ℂ),
          ∃! u : rotatingLinePiSubspace ι 3 α,
            perturbedAugmentedConjWirtingerDerivL (ι → ℂ) hα1.le A B u = y) ∧
        ∀ u ∈ rotatingLinePiSubspace ι 3 α,
          ‖u‖ ≤ C * ‖perturbedAugmentedConjWirtingerDerivL (ι → ℂ) hα1.le A B u‖ := by
  obtain ⟨ε, hε, C, h⟩ :=
    exists_pos_isInvertible_perturbedAugmentedConjWirtingerDerivL_comp_subtypeL_and_norm_inverse_le
      (ι := ι) hα0 hα1
  refine ⟨ε, hε, C, fun A B hA hB ↦ ?_⟩
  obtain ⟨hinv, hC⟩ := h A B hA hB
  refine ⟨fun y ↦ by simpa using hinv.bijective.existsUnique y, fun u hu ↦ ?_⟩
  exact (hinv.norm_le_norm_inverse_mul_norm ⟨u, hu⟩).trans
    (mul_le_mul_of_nonneg_right hC (norm_nonneg _))

end TauCeti
