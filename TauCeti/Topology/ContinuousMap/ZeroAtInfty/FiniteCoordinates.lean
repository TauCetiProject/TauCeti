/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.ContinuousMap.ZeroAtInfty.Discrete
public import TauCeti.Analysis.Normed.Ring.PseudoUniformizer
import TauCeti.Analysis.Normed.Operator.RingOpNorm.OpenMapping
import TauCeti.Analysis.Normed.Group.Ultra
import TauCeti.Topology.MetricSpace.Ultra.ContinuousMaps

/-!
# Finite coordinates on complete finite submodules of `C₀`

A complete finitely generated submodule of `C₀(I, R)` over a complete ultrametric Tate normed
ring admits uniform relative approximation by finite coordinate projections. A sufficiently
accurate projection preserves the norm, giving finite-coordinate norm detection with constant one.
No freeness or Noetherian hypothesis is needed for these statements.

Completeness of the submodule is an explicit hypothesis: for a closed submodule `P`, obtain it
from `hP.completeSpace_coe`. This does not assert closedness of arbitrary finite submodules.

The argument uses `TauCeti.exists_linearCombination_eq_and_norm_le` to choose bounded
coefficients for a finite generating family, then truncates all generators on the same finite set.
It follows the finite-coordinate argument of K. Buzzard, *Eigenvarieties*, Lemmas 2.2–2.3,
with the Banach–Tate setting of C. Johansson and J. Newton, *Extended eigenvarieties for
overconvergent cohomology*, §2.1.
-/

public section

open Filter Topology
open scoped ZeroAtInfty NNReal
open ZeroAtInftyContinuousMap

namespace Submodule

variable {I R : Type*} [TopologicalSpace I] [DiscreteTopology I]
  [NormedRing R] [IsUltrametricDist R] [CompleteSpace R] [TauCeti.NormedRing.IsTate R]

/-- Finite coordinate projections approximate the identity uniformly relative to the norm on a
complete finite submodule of `C₀(I, R)`. In particular this applies to closed finite submodules,
using the completeness instance `hP.completeSpace_coe`. -/
theorem exists_finset_norm_indicatorCLM_sub_le (P : Submodule R C₀(I, R))
    [Module.Finite R P] [CompleteSpace P] {ε : ℝ} (hε : 0 < ε) :
    ∃ S : Finset I, ∀ f ∈ P, ‖indicatorCLM R (S : Set I) f - f‖ ≤ ε * ‖f‖ := by
  classical
  obtain ⟨n, v, hv⟩ := Module.Finite.exists_fin (R := R) (M := P)
  obtain ⟨C, hC, hlift⟩ := TauCeti.exists_linearCombination_eq_and_norm_le v hv
  have htail : ∀ᶠ j in cofinite, ∀ k, ‖(v k : C₀(I, R)) j‖ < ε / C := by
    exact eventually_all.2 fun k ↦
      (NormedAddGroup.tendsto_nhds_zero.1 (v k : C₀(I, R)).tendsto_cofinite) _ (div_pos hε hC)
  let S := (eventually_cofinite.1 htail).toFinset
  refine ⟨S, fun f hf ↦ ?_⟩
  obtain ⟨c, hsum, hc⟩ := hlift ⟨f, hf⟩
  refine (ZeroAtInftyContinuousMap.norm_le (mul_nonneg hε.le (norm_nonneg f))).2 fun j ↦ ?_
  by_cases hj : j ∈ S
  · simpa [Set.indicator_apply, hj] using mul_nonneg hε.le (norm_nonneg f)
  · have hj' : ∀ k, ‖(v k : C₀(I, R)) j‖ < ε / C := by
      simpa only [S, Set.Finite.mem_toFinset, Set.mem_ofPred_eq, not_not] using hj
    have hfj : (∑ k, c k • (v k : C₀(I, R)) j) = f j := by
      simpa using congrArg (fun g : P ↦ (g : C₀(I, R)) j) hsum
    have hbound : ‖f j‖ ≤ ε * ‖f‖ := by
      rw [← hfj]
      refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg
        (mul_nonneg hε.le (norm_nonneg f)) fun k _ ↦ ?_
      calc
        ‖c k • (v k : C₀(I, R)) j‖ ≤ ‖c k‖ * ‖(v k : C₀(I, R)) j‖ := norm_smul_le _ _
        _ ≤ (C * ‖f‖) * (ε / C) :=
          mul_le_mul ((norm_le_pi_norm c k).trans hc) (hj' k).le (norm_nonneg _) (by positivity)
        _ = ε * ‖f‖ := by field_simp
    simpa [Set.indicator_apply, hj] using hbound

/-- On a complete finite submodule, the norm is the maximum of the norms at a fixed finite set
of coordinates. The supremum in `ℝ≥0` is zero when the set of coordinates is empty. -/
theorem exists_finset_norm_eq (P : Submodule R C₀(I, R))
    [Module.Finite R P] [CompleteSpace P] :
    ∃ S : Finset I, ∀ f ∈ P, ‖f‖ = (S.sup fun i ↦ ‖f i‖₊ : ℝ≥0) := by
  classical
  obtain ⟨S, hS⟩ := P.exists_finset_norm_indicatorCLM_sub_le (by norm_num : (0 : ℝ) < 1 / 2)
  refine ⟨S, fun f hf ↦ ?_⟩
  have heq : ‖indicatorCLM R (S : Set I) f‖ = ‖f‖ := by
    rcases eq_or_ne f 0 with rfl | hf0
    · simp
    have hlt : ‖indicatorCLM R (S : Set I) f - f‖ < ‖f‖ :=
      (hS f hf).trans_lt (by nlinarith [norm_pos_iff.2 hf0])
    exact (IsUltrametricDist.norm_eq_of_norm_sub_lt_left
      (by simpa only [norm_sub_rev] using hlt)).symm
  rw [← heq, indicatorCLM_finset_apply, ← coe_nnnorm, nnnorm_sum_single]

/-- A complete finite submodule has a finite-coordinate bound with a positive constant.
The stronger theorem `exists_finset_norm_eq` shows that the constant can be taken to be one. -/
theorem exists_finset_norm_le (P : Submodule R C₀(I, R))
    [Module.Finite R P] [CompleteSpace P] :
    ∃ S : Finset I, ∃ C > 0, ∀ f ∈ P,
      ‖f‖ ≤ C * (S.sup fun i ↦ ‖f i‖₊ : ℝ≥0) := by
  obtain ⟨S, hS⟩ := P.exists_finset_norm_eq
  exact ⟨S, 1, one_pos, fun f hf ↦ by rw [hS f hf, one_mul]⟩

end Submodule
