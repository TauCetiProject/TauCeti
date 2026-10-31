/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.MassFormula.RootCount
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import TauCeti.NumberTheory.LocalField.InertiaDegree
import TauCeti.NumberTheory.LocalField.MassFormula.Eisenstein.Fibre
import TauCeti.NumberTheory.LocalField.RootCount.Ball
import TauCeti.RingTheory.DiscreteValuationRing.RootPartition
import TauCeti.RingTheory.DiscreteValuationRing.Sphere

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

When the balls are centred at uniformizers and have order at least `2`, the fibre of the
Eisenstein region over each ball is the image of the set of all integral coefficient vectors
whose polynomial has a root in that ball. The integral is therefore also a sum of measures of
such integral fibres, the sets on which the local root criterion at the centre and the volume
computation in power-basis coordinates operate.

Once those volumes are known, the integral is determined. Take balls of order `r` with `1 < r`
and `d < r`, where `d` is the discriminant exponent of `L`. If the coefficient fibre over each
such ball centred at a uniformizer has measure `q ^ (-(r + d))`, the root-count integral is
`q ^ (-(d + 1)) (1 - q⁻¹)`, Serre's value. The reason is that a partition of the uniformizers
into such balls has `q ^ (r - 1) - q ^ (r - 2)` members, and `L / K` has residue degree one, so
`q` is the residue cardinality of both `K` and `L`.

## Main results

* `IntermediateField.lintegral_rootCount_eq_sum_measure`: the root-count integral is the sum of
  the measures of the coefficient fibres of a disjoint ball cover of the uniformizers.
* `IntermediateField.lintegral_rootCount_eq_sum_measure_image`: for a partition of the
  uniformizers into balls of order at least `2`, the root-count integral is the sum of the
  measures of the integral coefficient fibres.
* `IntermediateField.lintegral_rootCount_eq_of_measure_eq`: if every such fibre over a ball of
  order `r` has measure `q ^ (-(r + d))`, the root-count integral is `q ^ (-(d + 1)) (1 - q⁻¹)`.

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

/-- **Root-count integrals as sums of integral coefficient fibres.** Let `L ∈ σ_K(n)`, with its
canonical local-field structure, and let `C` index a partition of the uniformizers of `L` into
balls `v_L(x - c) ≥ r` whose order `r` exceeds both `1` and the discriminant exponent `d(L)`.
Then the integral of `L.rootCount` over the Eisenstein region is the sum, over the balls, of the
measures of the sets of coefficient vectors of monic polynomials over `𝒪[K]` having a root in
the ball. The bound `1 < r` follows from `d(L) < r` unless `n = 1`, where `d(L) = 0`. -/
theorem _root_.IntermediateField.lintegral_rootCount_eq_sum_measure_image
    {n : ℕ} {L : IntermediateField K (SeparableClosure K)}
    (hL : L ∈ totallyRamifiedOfDegree K n) :
    letI := (mem_totallyRamifiedOfDegree_iff.1 hL).2.finite
    letI := finiteIntermediateFieldValuativeRel K (SeparableClosure K) L
    letI := finiteIntermediateFieldTopology K (SeparableClosure K) L
    haveI := finiteIntermediateField_isNonarchimedeanLocalField K (SeparableClosure K) L
    haveI := finiteIntermediateField_valuativeExtension K (SeparableClosure K) L
    ∀ [MeasurableSpace (Fin n → K)] [OpensMeasurableSpace (Fin n → K)]
      (μ : Measure (Fin n → K)) {r : ℕ}, 1 < r → L.discriminantExponent < r →
      ∀ C : Finset 𝒪[L], {x : 𝒪[L] | addVal 𝒪[L] x = 1} =
        ⋃ c ∈ C, {x : 𝒪[L] | (r : ℕ∞) ≤ addVal 𝒪[L] (x - c)} →
      (C : Set 𝒪[L]).PairwiseDisjoint
        (fun c ↦ {x : 𝒪[L] | (r : ℕ∞) ≤ addVal 𝒪[L] (x - c)}) →
      ∫⁻ a in eisensteinSet K n, (L.rootCount a : ℝ≥0∞) ∂μ =
        ∑ c ∈ C, μ ((fun b : Fin n → 𝒪[K] ↦ fun i ↦ (b i : K)) '' {b | ∃ z : 𝒪[L],
          aeval z (monicOfCoeff b) = 0 ∧ (r : ℕ∞) ≤ addVal 𝒪[L] (z - c)}) := by
  have hL' := mem_totallyRamifiedOfDegree_iff.1 hL
  let _ := hL'.2.finite
  let _ := finiteIntermediateFieldValuativeRel K (SeparableClosure K) L
  let _ := finiteIntermediateFieldTopology K (SeparableClosure K) L
  have := finiteIntermediateField_isNonarchimedeanLocalField K (SeparableClosure K) L
  have := finiteIntermediateField_valuativeExtension K (SeparableClosure K) L
  intro _ _ μ r hr1 hr C hcover hdisj
  have hn : ramificationIndex K L = n :=
    ((isTotallyRamified_iff_ramificationIndex_eq_finrank K L).1
      ((IntermediateField.isTotallyRamified_iff L).1 hL'.2)).trans hL'.1
  rw [L.lintegral_rootCount_eq_sum_measure hL μ hr C hcover.subset hdisj]
  refine Finset.sum_congr rfl fun c hc ↦ ?_
  -- Each centre lies in its own ball, hence on the sphere of uniformizers.
  have hc1 : c ∈ {x : 𝒪[L] | addVal 𝒪[L] x = 1} :=
    hcover ▸ Set.mem_biUnion hc (by
      rw [Set.mem_ofPred_eq, sub_self, IsDiscreteValuationRing.addVal_zero]
      exact le_top)
  rw [eisensteinSet_inter_setOf_exists_aeval_monicOfCoeff_eq_zero_le_addVal_eq_image hn hr1 hc1]

/-- **The root-count integral from the local fibre volumes.** Let `L ∈ σ_K(n)`, with discriminant
exponent `d`, and let `1 < r` and `d < r`. Suppose that for every uniformizer `c` of `L`, the
coefficient vectors in the Eisenstein region whose polynomial has a root in the ball
`v_L(z - c) ≥ r` have measure `q ^ (-(r + d))`, where `q` is the residue cardinality of `K`. Then
the root count of `L` integrates over the Eisenstein region to `q ^ (-(d + 1)) (1 - q⁻¹)`. -/
theorem _root_.IntermediateField.lintegral_rootCount_eq_of_measure_eq
    {n : ℕ} {L : IntermediateField K (SeparableClosure K)}
    (hL : L ∈ totallyRamifiedOfDegree K n) :
    letI := (mem_totallyRamifiedOfDegree_iff.1 hL).2.finite
    letI := finiteIntermediateFieldValuativeRel K (SeparableClosure K) L
    letI := finiteIntermediateFieldTopology K (SeparableClosure K) L
    haveI := finiteIntermediateField_isNonarchimedeanLocalField K (SeparableClosure K) L
    haveI := finiteIntermediateField_valuativeExtension K (SeparableClosure K) L
    ∀ [MeasurableSpace (Fin n → K)] [OpensMeasurableSpace (Fin n → K)]
      (μ : Measure (Fin n → K)) {r : ℕ}, 1 < r → L.discriminantExponent < r →
      (∀ c : 𝒪[L], addVal 𝒪[L] c = 1 →
        μ (eisensteinSet K n ∩ {a | ∃ z : 𝒪[L],
          aeval (z : L) (monicOfCoeff a) = 0 ∧ (r : ℕ∞) ≤ addVal 𝒪[L] (z - c)}) =
          1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ (r + L.discriminantExponent)) →
      ∫⁻ a in eisensteinSet K n, (L.rootCount a : ℝ≥0∞) ∂μ =
        1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ (L.discriminantExponent + 1) *
          (1 - 1 / (Nat.card 𝓀[K] : ℝ≥0∞)) := by
  have hL' := mem_totallyRamifiedOfDegree_iff.1 hL
  let _ := hL'.2.finite
  let _ := finiteIntermediateFieldValuativeRel K (SeparableClosure K) L
  let _ := finiteIntermediateFieldTopology K (SeparableClosure K) L
  have := finiteIntermediateField_isNonarchimedeanLocalField K (SeparableClosure K) L
  have := finiteIntermediateField_valuativeExtension K (SeparableClosure K) L
  intro _ _ μ r hr1 hr hμ
  obtain ⟨C, hC, hcover, hdisj⟩ := exists_finset_addVal_eq_biUnion (A := 𝒪[L]) hr1
  -- `L / K` has residue degree one, so both residue fields have `q` elements.
  have hq : Nat.card 𝓀[L] = Nat.card 𝓀[K] := by
    rw [natCard_residueField K L,
      ((IntermediateField.isTotallyRamified_iff L).1 hL'.2).inertiaDegree_eq_one, pow_one]
  have hmass := card_finset_div_pow_of_addVal_eq_biUnion hr1 C hcover hdisj
  rw [hq] at hmass
  have hq0 : (Nat.card 𝓀[K] : ℝ≥0∞) ≠ 0 := by simp [Nat.card_pos.ne']
  have hqt : (Nat.card 𝓀[K] : ℝ≥0∞) ≠ ∞ := ENNReal.natCast_ne_top _
  rw [L.lintegral_rootCount_eq_sum_measure hL μ hr C hcover.subset hdisj,
    Finset.sum_congr rfl fun c hc ↦ hμ c (hC c hc), Finset.sum_const, nsmul_eq_mul]
  simp only [one_div, pow_one] at hmass ⊢
  rw [div_eq_mul_inv] at hmass
  rw [pow_add, ENNReal.mul_inv (.inl (pow_ne_zero _ hq0)) (.inl (ENNReal.pow_ne_top hqt)),
    ← mul_assoc, hmass, pow_succ, ENNReal.mul_inv (.inl (pow_ne_zero _ hq0))
      (.inl (ENNReal.pow_ne_top hqt))]
  ring

end TauCeti
