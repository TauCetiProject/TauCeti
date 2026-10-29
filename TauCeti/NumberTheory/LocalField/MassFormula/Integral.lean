/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.MassFormula.RootCount
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import TauCeti.NumberTheory.LocalField.RootCount.Ball

/-!
# Decomposing root-count integrals into coefficient fibres

Fix a totally ramified degree-`n` subextension `L` of a separable closure of `K`. A finite
disjoint cover of the uniformizers of `L` by balls of order larger than its discriminant
exponent counts every root of an Eisenstein polynomial exactly once. Integrating this count
over the Eisenstein region gives the sum of the measures of its coefficient fibres: the
polynomials having a root in each fixed ball.

Each fibre is measurable because a closed valuation ball is compact and projection of the
closed evaluation-zero locus along that ball is closed. Consequently the decomposition holds
for every measure on coefficient space, without Haar, normalization, regularity or separability
assumptions on the polynomials. This isolates the integration step from the arithmetic
calculation of the individual fibre volumes.

## References

* J.-P. Serre, *Une « formule de masse » pour les extensions totalement ramifiées de degré donné
  d'un corps local*, C. R. Acad. Sci. Paris Sér. A **286** (1978), 1031–1036, §3, Lemmas 2–3.
-/

public section
noncomputable section

open ValuativeRel Polynomial IsDiscreteValuationRing MeasureTheory
open scoped ENNReal

namespace TauCeti

open TauCeti.Polynomial (monicOfCoeff)

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- Integrate the root count in a counted extension by summing the measures of the coefficient
fibres of any fixed finite disjoint ball cover of its uniformizers. The ball order must be
larger than the discriminant exponent, so every occupied ball contains exactly one root. -/
theorem _root_.IntermediateField.lintegral_rootCount_eq_sum_measure
    {n : ℕ} {L : IntermediateField K (SeparableClosure K)}
    (hL : L ∈ totallyRamifiedOfDegree K n) :
    letI := (mem_totallyRamifiedOfDegree_iff.1 hL).2.finite
    letI := finiteIntermediateFieldValuativeRel K (SeparableClosure K) L
    letI := finiteIntermediateFieldTopology K (SeparableClosure K) L
    haveI := finiteIntermediateField_isNonarchimedeanLocalField K (SeparableClosure K) L
    haveI := finiteIntermediateField_valuativeExtension K (SeparableClosure K) L
    ∀ [MeasurableSpace (Fin n → K)] [OpensMeasurableSpace (Fin n → K)]
      (μ : Measure (Fin n → K)) {r : ℕ}, L.discriminantExponent < r →
      ∀ C : Finset 𝒪[L], {x : 𝒪[L] | addVal 𝒪[L] x = 1} ⊆
        ⋃ c ∈ C, {x : 𝒪[L] | (r : ℕ∞) ≤ addVal 𝒪[L] (x - c)} →
      (C : Set 𝒪[L]).PairwiseDisjoint
        (fun c ↦ {x : 𝒪[L] | (r : ℕ∞) ≤ addVal 𝒪[L] (x - c)}) →
      ∫⁻ a in eisensteinSet K n, (L.rootCount a : ℝ≥0∞) ∂μ =
        ∑ c ∈ C, μ (eisensteinSet K n ∩ {a | ∃ z : 𝒪[L],
          aeval (z : L) (monicOfCoeff a) = 0 ∧ (r : ℕ∞) ≤ addVal 𝒪[L] (z - c)}) := by
  classical
  have hL' := mem_totallyRamifiedOfDegree_iff.1 hL
  let _ := hL'.2.finite
  let _ := finiteIntermediateFieldValuativeRel K (SeparableClosure K) L
  let _ := finiteIntermediateFieldTopology K (SeparableClosure K) L
  have := finiteIntermediateField_isNonarchimedeanLocalField K (SeparableClosure K) L
  have := finiteIntermediateField_valuativeExtension K (SeparableClosure K) L
  -- Fix the subring algebra so root transport stays inside `L`.
  let : Algebra 𝒪[L] L := Algebra.ofSubsemiring (R := L) (A := L) 𝒪[L]
  have : IsScalarTower 𝒪[K] 𝒪[L] L := .of_algebraMap_eq' rfl
  intro _ _ μ r hr C hcover hdisj
  let B (c : 𝒪[L]) : Set (Fin n → K) := {a | ∃ z : 𝒪[L],
    aeval (z : L) (monicOfCoeff a) = 0 ∧ (r : ℕ∞) ≤ addVal 𝒪[L] (z - c)}
  have hB (c : 𝒪[L]) : MeasurableSet (B c) :=
    measurableSet_setOf_exists_aeval_monicOfCoeff_eq_zero_le_addVal r c
  have hcount (a : Fin n → K) (ha : a ∈ eisensteinSet K n) :
      (L.rootCount a : ℝ≥0∞) = ∑ c ∈ C, (B c).indicator (fun _ ↦ 1) a := by
    obtain ⟨f, hf, he⟩ := mem_eisensteinSet_iff_exists_isEisensteinAt.mp ha
    have hz (z : 𝒪[L]) : aeval (z : L) (monicOfCoeff a) = 0 ↔ aeval z f = 0 := by
      rw [← hf, aeval_map_algebraMap]
      exact aeval_algebraMap_eq_zero_iff_of_injective (IsFractionRing.injective 𝒪[L] L)
    have hnat := L.rootCount_eq_sum_ite_of_eisenstein hL he hf hr C hcover hdisj
    have hcast := congrArg (fun k : ℕ ↦ (k : ℝ≥0∞)) hnat
    rw [hcast, Nat.cast_sum]
    refine Finset.sum_congr rfl fun c _ ↦ ?_
    simp only [B, Set.indicator_apply, Set.mem_ofPred_eq, hz, Nat.cast_ite,
      Nat.cast_one, Nat.cast_zero]
  calc
    ∫⁻ a in eisensteinSet K n, (L.rootCount a : ℝ≥0∞) ∂μ =
        ∫⁻ a in eisensteinSet K n, ∑ c ∈ C, (B c).indicator (fun _ ↦ 1) a ∂μ :=
      setLIntegral_congr_fun measurableSet_eisensteinSet hcount
    _ = ∑ c ∈ C, ∫⁻ a in eisensteinSet K n, (B c).indicator (fun _ ↦ 1) a ∂μ :=
      lintegral_finsetSum C fun c _ ↦ measurable_const.indicator (hB c)
    _ = ∑ c ∈ C, μ (eisensteinSet K n ∩ B c) := by
      refine Finset.sum_congr rfl fun c _ ↦ ?_
      rw [lintegral_indicator_fun_one (hB c), Measure.restrict_apply (hB c), Set.inter_comm]

end TauCeti
