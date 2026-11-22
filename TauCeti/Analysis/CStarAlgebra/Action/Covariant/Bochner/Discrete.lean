/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Action.Covariant.L1
public import TauCeti.MeasureTheory.Measure.Count.Topology
import TauCeti.MeasureTheory.Integral.Bochner.SumMeasure

/-!
# Bochner `L¹` integrated forms for counting measure on discrete groups

This file extends `TauCeti.Analysis.CStarAlgebra.Action.Covariant.L1` to counting measure
`Measure.count` on an arbitrary discrete group `G`, expressing
`CovariantRepresentation.integratedOperatorBochnerL1` as an unconditionally convergent `ℓ¹`
operator-applied series `∑' g, P.coefficient (f g) (P.group g v)` and bounding its operator norm
by `∑' g, ‖f g‖` without countability assumptions.

## References

* Dana P. Williams, *Crossed Products of C*-Algebras*, Mathematical Surveys and Monographs,
  vol. 134, American Mathematical Society (2007), Chapter 7.
-/

public section

noncomputable section

open MeasureTheory

namespace TauCeti.CStarAction.CovariantRepresentation

variable {G A H : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]
  [MeasurableSpace G] [BorelSpace G] [NonUnitalCStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {α : CStarAction G A} (P : CovariantRepresentation α H)

/-- For counting measure on a discrete group, `integratedOperatorBochnerL1` acts on `v` by the
unconditionally convergent series `∑ g, π (u g) (U g v)`. -/
theorem hasSum_integratedOperatorBochnerL1_count_apply
    (u : Lp A 1 (Measure.count : Measure G)) (v : H) :
    HasSum (fun g => P.coefficient (u g) (P.group g v))
      (P.integratedOperatorBochnerL1 Measure.count u v) := by
  rw [integratedOperatorBochnerL1_apply]
  have hint := P.integrable_integrand_of_integrable (L1.integrable_coeFn u) v
  exact hasSum_integral_count hint

/-- Series formula for `integratedOperatorBochnerL1` with respect to counting measure on a
discrete group. -/
theorem integratedOperatorBochnerL1_count_apply
    (u : Lp A 1 (Measure.count : Measure G)) (v : H) :
    P.integratedOperatorBochnerL1 Measure.count u v =
      ∑' g, P.coefficient (u g) (P.group g v) :=
  (P.hasSum_integratedOperatorBochnerL1_count_apply u v).tsum_eq.symm

/-- For an `ℓ¹` family `f : G → A` on a discrete group, `g ↦ π (f g) (U g v)` sums unconditionally
to `integratedOperatorBochnerL1` of `(integrable_count_iff.2 hf).toL1 f`. -/
theorem hasSum_integratedOperatorBochnerL1_count_toL1 {f : G → A} (hf : Summable (‖f ·‖))
    (v : H) :
    HasSum (fun g => P.coefficient (f g) (P.group g v))
      (P.integratedOperatorBochnerL1 Measure.count ((integrable_count_iff.2 hf).toL1 f) v) := by
  have hcoe : ∀ g, ((integrable_count_iff.2 hf).toL1 f : G → A) g = f g :=
    Measure.ae_count_iff.1 (integrable_count_iff.2 hf).coeFn_toL1
  simpa only [hcoe] using
    P.hasSum_integratedOperatorBochnerL1_count_apply ((integrable_count_iff.2 hf).toL1 f) v

/-- For an `ℓ¹` family `f : G → A` on a discrete group, `integratedOperatorBochnerL1` acts by
`∑' g, π (f g) (U g v)`. -/
theorem integratedOperatorBochnerL1_count_toL1 {f : G → A} (hf : Summable (‖f ·‖)) (v : H) :
    P.integratedOperatorBochnerL1 Measure.count ((integrable_count_iff.2 hf).toL1 f) v =
      ∑' g, P.coefficient (f g) (P.group g v) :=
  (P.hasSum_integratedOperatorBochnerL1_count_toL1 hf v).tsum_eq.symm

/-- For an `ℓ¹` family `f : G → A` on a discrete group, the operator norm of
`integratedOperatorBochnerL1` is bounded by `∑' g, ‖f g‖`. -/
theorem norm_integratedOperatorBochnerL1_count_toL1_le {f : G → A} (hf : Summable (‖f ·‖)) :
    ‖P.integratedOperatorBochnerL1 Measure.count ((integrable_count_iff.2 hf).toL1 f)‖ ≤
      ∑' g, ‖f g‖ := by
  refine (P.norm_integratedOperatorBochnerL1_toL1_le Measure.count
    (integrable_count_iff.2 hf)).trans_eq ?_
  have hint := (integrable_count_iff.2 hf).norm
  exact integral_count_eq_tsum hint

end TauCeti.CStarAction.CovariantRepresentation
