/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
public import TauCeti.Topology.Algebra.Module.LinearPMap.CommonDomain
import Mathlib.Analysis.Normed.Operator.Banach
import TauCeti.Analysis.Normed.Operator.Banach

/-!
# The partial operator of an operator on a common domain: normed spaces

For normed spaces `D`, `H`, `K`, an injective `ι : D →L H` and `A : D →L K`, this file
characterizes when the partial operator `ContinuousLinearMap.domainOperator ι A hι` of
`TauCeti.Topology.Algebra.Module.LinearPMap.CommonDomain`, with domain `range ι` and acting by
`ι x ↦ A x`, is closed, and when `K = H`, which scalars are its resolvent points.

* **Closedness.** If `D` is complete, the partial operator is closed when the norm of `D` is
  bounded by the graph norm, `‖x‖ ≤ C (‖ι x‖ + ‖A x‖)`
  (`ContinuousLinearMap.isClosed_domainOperator_of_norm_le`), and if `H` and `K` are complete as
  well, only then (`ContinuousLinearMap.isClosed_domainOperator_iff`).
* **Resolvent.** For complete `D` and `H`, `c` is a resolvent point exactly when
  `c • ι - A : D → H` is invertible (`ContinuousLinearMap.mem_resolventSet_domainOperator_iff`).

## References

* T. Kato, *Perturbation Theory for Linear Operators*, Sections III.5.2 and III.6.8.
-/

public section

noncomputable section

open Function

namespace ContinuousLinearMap

section Normed

variable {𝕜 D H K : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup D] [NormedSpace 𝕜 D] [NormedAddCommGroup H] [NormedSpace 𝕜 H]
  [NormedAddCommGroup K] [NormedSpace 𝕜 K]

/-- For complete `D` and `H`, a scalar `c` is a resolvent point of `domainOperator ι A hι` exactly
when `c • ι - A : D → H` is invertible. -/
theorem mem_resolventSet_domainOperator_iff [CompleteSpace D] [CompleteSpace H]
    {ι A : D →L[𝕜] H} {hι : Injective ι} {c : 𝕜} :
    c ∈ (domainOperator ι A hι).resolventSet ↔ (c • ι - A).IsInvertible :=
  ⟨fun h ↦ isInvertible_iff_bijective.2 (bijective_smul_sub_of_mem_resolventSet h),
    mem_resolventSet_domainOperator⟩

/-- If `D` is complete and its norm is bounded by the graph norm, `‖x‖ ≤ C (‖ι x‖ + ‖A x‖)`, then
`domainOperator ι A hι` is closed. -/
theorem isClosed_domainOperator_of_norm_le [CompleteSpace D] {ι : D →L[𝕜] H} {A : D →L[𝕜] K}
    {hι : Injective ι} {C : ℝ} (hC : ∀ x, ‖x‖ ≤ C * (‖ι x‖ + ‖A x‖)) :
    (domainOperator ι A hι).IsClosed := by
  rw [isClosed_domainOperator_iff_isClosed_range]
  have hbound : ∀ x, ‖x‖ ≤ (2 * max C 0).toNNReal * ‖ι.prod A x‖ := fun x ↦ by
    have h₁ : ‖ι x‖ ≤ ‖ι.prod A x‖ := norm_fst_le (ι.prod A x)
    have h₂ : ‖A x‖ ≤ ‖ι.prod A x‖ := norm_snd_le (ι.prod A x)
    rw [Real.coe_toNNReal _ (by positivity)]
    calc ‖x‖ ≤ C * (‖ι x‖ + ‖A x‖) := hC x
      _ ≤ max C 0 * (‖ι x‖ + ‖A x‖) := by gcongr; exact le_max_left _ _
      _ ≤ max C 0 * (2 * ‖ι.prod A x‖) := by gcongr; linarith
      _ = 2 * max C 0 * ‖ι.prod A x‖ := by ring
  exact ((ι.prod A).antilipschitz_of_bound hbound).isClosed_range (ι.prod A).uniformContinuous

/-- For complete `D`, `H` and `K`, `domainOperator ι A hι` is closed exactly when the norm of `D`
is bounded by the graph norm, `‖x‖ ≤ C (‖ι x‖ + ‖A x‖)` for some `C`. -/
theorem isClosed_domainOperator_iff [CompleteSpace D] [CompleteSpace H] [CompleteSpace K]
    {ι : D →L[𝕜] H} {A : D →L[𝕜] K} {hι : Injective ι} :
    (domainOperator ι A hι).IsClosed ↔ ∃ C, ∀ x, ‖x‖ ≤ C * (‖ι x‖ + ‖A x‖) := by
  refine ⟨fun h ↦ ?_, fun ⟨C, hC⟩ ↦ isClosed_domainOperator_of_norm_le hC⟩
  obtain ⟨K, hK⟩ := (ι.prod A).antilipschitz_of_injective_of_isClosed_range
    (fun x x' hxx' ↦ hι (by simpa using congrArg Prod.fst hxx'))
    (isClosed_domainOperator_iff_isClosed_range.1 h)
  refine ⟨K, fun x ↦ (hK.le_mul_norm (map_zero _) x).trans ?_⟩
  rw [prod_apply, Prod.norm_def]
  gcongr
  exact max_le_add_of_nonneg (norm_nonneg _) (norm_nonneg _)

end Normed

end ContinuousLinearMap
