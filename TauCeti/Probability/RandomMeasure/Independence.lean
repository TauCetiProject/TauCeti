/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Independence.Process.Basic
public import TauCeti.MeasureTheory.Measure.GiryMonad

/-!
# Independence of random measures from evaluations

Random measures are independent exactly when their finite vectors of measurable-set
masses are independent. Within each vector the test sets may overlap: individual
(or pairwise) independence of evaluations is not sufficient.

These criteria extend independence from count coordinates to the entire evaluation
sigma-algebra. In particular, they allow independent restrictions and color classes of
point processes to be identified as independent random measures, not merely as processes
with independent single counts. No topology, local finiteness, integrality, or finiteness
of the masses is required. Almost-everywhere measurability suffices, and different random
measures may have different state spaces.

The proofs use Mathlib's finite-dimensional independence criteria for stochastic
processes and the Giry evaluation measurable space on measures.

## References

* G. Last and M. Penrose, *Lectures on the Poisson Process*, Cambridge University Press,
  2018, Chapters 2 and 5.
-/

public section

open MeasureTheory

namespace ProbabilityTheory

variable {Ω ι : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {X : ι → Type*} [∀ i, MeasurableSpace (X i)] {N : (i : ι) → Ω → Measure (X i)}

/-- A family of random measures is independent if and only if every finite subfamily's
finite evaluation vectors are independent. Each member can have its own state space and
its own finite family of measurable test sets; those test sets need not be disjoint. -/
theorem iIndepFun_measure_iff (hN : ∀ i, AEMeasurable (N i) P) :
    iIndepFun N P ↔
      ∀ (I : Finset ι)
        (J : (i : I) → Finset {A : Set (X i) // MeasurableSet A}),
        iIndepFun (fun (i : I) ω (A : J i) ↦ N i ω A.val.val) P := by
  constructor
  · intro h I J
    exact h.restrict I |>.comp
      (fun i μ (A : J i) ↦ μ A.val.val)
      (fun i ↦ Measurable.of_eval fun A ↦ Measure.measurable_coe A.val.property)
  · intro h
    have he : iIndepFun
        (fun i ω (A : {A : Set (X i) // MeasurableSet A}) ↦ N i ω A.val) P :=
      iIndepFun.iIndepFun_process₀
        (fun i A ↦ (Measure.measurable_coe A.property).comp_aemeasurable (hN i)) h
    apply iIndep_of_iIndep_of_le he.iIndep
    exact fun i ↦ (Measure.measurableSpace_comap_eq_comap_eval (N i)).le

variable {S T : Type*} [MeasurableSpace S] [MeasurableSpace T]
  {M : Ω → Measure S} {L : Ω → Measure T}

/-- Two random measures are independent exactly when every pair of finite evaluation
vectors is independent. Infinite masses and overlapping test sets are allowed. -/
theorem indepFun_measure_iff [IsZeroOrProbabilityMeasure P]
    (hM : AEMeasurable M P) (hL : AEMeasurable L P) :
    IndepFun M L P ↔
      ∀ (I : Finset {A : Set S // MeasurableSet A})
        (J : Finset {B : Set T // MeasurableSet B}),
        IndepFun (fun ω (A : I) ↦ M ω A.val.val)
          (fun ω (B : J) ↦ L ω B.val.val) P := by
  constructor
  · intro h I J
    exact h.comp
      (Measurable.of_eval fun A ↦ Measure.measurable_coe A.val.property)
      (Measurable.of_eval fun B ↦ Measure.measurable_coe B.val.property)
  · intro h
    have he : IndepFun
        (fun ω (A : {A : Set S // MeasurableSet A}) ↦ M ω A.val)
        (fun ω (B : {B : Set T // MeasurableSet B}) ↦ L ω B.val) P :=
      IndepFun.process_indepFun_process₀
        (fun A ↦ (Measure.measurable_coe A.property).comp_aemeasurable hM)
        (fun B ↦ (Measure.measurable_coe B.property).comp_aemeasurable hL) h
    apply indep_of_indep_of_le he
    · exact (Measure.measurableSpace_comap_eq_comap_eval M).le
    · exact (Measure.measurableSpace_comap_eq_comap_eval L).le

end ProbabilityTheory
