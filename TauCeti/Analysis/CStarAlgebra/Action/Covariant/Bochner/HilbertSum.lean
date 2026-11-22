/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Action.Covariant.HilbertSum
public import TauCeti.Analysis.CStarAlgebra.Action.Covariant.L1

/-!
# Bochner `L¹` integrated forms of Hilbert direct sums

This file extends `TauCeti.Analysis.CStarAlgebra.Action.Covariant.HilbertSum` and
`TauCeti.Analysis.CStarAlgebra.Action.Covariant.L1`, proving that
`CovariantRepresentation.integratedOperatorBochnerL1` of a Hilbert direct sum commutes with
evaluation in each summand and equals the `lp.mapCLM` direct sum of the component integrated
operators.

## References

* Dana P. Williams, *Crossed Products of C*-Algebras*, Mathematical Surveys and Monographs,
  vol. 134, American Mathematical Society (2007), Chapter 2.
-/

public section

noncomputable section

open MeasureTheory

namespace TauCeti.CStarAction.CovariantRepresentation

variable {G A ι : Type*} {K : ι → Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G]
  [R1Space G] [BorelSpace G] [NonUnitalCStarAlgebra A] [∀ i, NormedAddCommGroup (K i)]
  [∀ i, InnerProductSpace ℂ (K i)] [∀ i, CompleteSpace (K i)]
  {α : CStarAction G A} (Q : ∀ i, CovariantRepresentation α (K i))
  (μ : Measure G) [μ.InnerRegularCompactLTTop]

/-- `integratedOperatorBochnerL1` commutes with evaluation in every summand of a Hilbert direct
sum. -/
@[simp]
theorem integratedOperatorBochnerL1_hilbertSum_apply (u : Lp A 1 μ) (x : lp K 2) (i : ι) :
    (hilbertSum Q).integratedOperatorBochnerL1 μ u x i =
      (Q i).integratedOperatorBochnerL1 μ u (x i) := by
  let ev := lp.evalCLM ℂ K 2 i
  calc
    (hilbertSum Q).integratedOperatorBochnerL1 μ u x i =
        ev ((hilbertSum Q).integratedOperatorBochnerL1 μ u x) :=
      (lp.evalCLM_apply i _).symm
    _ = ev (∫ g, (hilbertSum Q).coefficient (u g) ((hilbertSum Q).group g x) ∂μ) :=
      congrArg ev ((hilbertSum Q).integratedOperatorBochnerL1_apply u x)
    _ = ∫ g, ev ((hilbertSum Q).coefficient (u g) ((hilbertSum Q).group g x)) ∂μ :=
      (ev.integral_comp_comm
        ((hilbertSum Q).integrable_integrand_of_integrable (L1.integrable_coeFn u) x)).symm
    _ = ∫ g, (Q i).coefficient (u g) ((Q i).group g (x i)) ∂μ :=
      integral_congr_ae (.of_forall fun g => by simp [ev])
    _ = (Q i).integratedOperatorBochnerL1 μ u (x i) :=
      ((Q i).integratedOperatorBochnerL1_apply u (x i)).symm

/-- `integratedOperatorBochnerL1` of a Hilbert direct sum is the direct sum of the component
integrated maps. -/
theorem integratedOperatorBochnerL1_hilbertSum (u : Lp A 1 μ) :
    (hilbertSum Q).integratedOperatorBochnerL1 μ u =
      lp.mapCLM 2 (fun i => (Q i).integratedOperatorBochnerL1 μ u) (norm_nonneg u)
        (fun i => (Q i).norm_integratedOperatorBochnerL1_apply_le u) := by
  ext x i; simp

end TauCeti.CStarAction.CovariantRepresentation
