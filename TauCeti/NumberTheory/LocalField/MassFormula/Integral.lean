/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.MassFormula.RootCount
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import TauCeti.NumberTheory.LocalField.Eisenstein.TotallyRamified
import TauCeti.NumberTheory.LocalField.RootCount.Ball
import TauCeti.RingTheory.DiscreteValuationRing.Basic

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

When the balls are centred at uniformizers and have order at least `2`, every root in a ball is
a uniformizer. A monic polynomial over `𝒪[K]` of degree `e(L/K)` with a uniformizer as a root is
Eisenstein, so the fibre of the Eisenstein region over a ball is the image of the set of all
integral coefficient vectors whose polynomial has a root in that ball. The integral is therefore
also a sum of measures of such integral fibres, the sets on which the local root criterion at
the centre and the volume computation in power-basis coordinates operate.

## Main results

* `IntermediateField.lintegral_rootCount_eq_sum_measure`: the root-count integral is the sum of
  the measures of the coefficient fibres of a disjoint ball cover of the uniformizers.
* `TauCeti.eisensteinSet_inter_setOf_exists_aeval_monicOfCoeff_eq_zero_le_addVal_eq_image`: over
  a ball of order at least `2` centred at a uniformizer, the fibre of the Eisenstein region is the
  image of the corresponding integral coefficient fibre.
* `IntermediateField.lintegral_rootCount_eq_sum_measure_image`: for a partition of the
  uniformizers into such balls, the root-count integral is the sum of the measures of the
  integral coefficient fibres.

## References

* J.-P. Serre, *Une « formule de masse » pour les extensions totalement ramifiées de degré donné
  d'un corps local*, C. R. Acad. Sci. Paris Sér. A **286** (1978), 1031–1036, §3, Lemmas 2–3.
-/

public section
noncomputable section

open ValuativeRel Polynomial IsDiscreteValuationRing MeasureTheory
open scoped ENNReal

namespace TauCeti

open TauCeti.Polynomial
  (monicOfCoeff map_monicOfCoeff monic_monicOfCoeff natDegree_monicOfCoeff)

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

section IntegralCoefficients

variable {L : Type*} [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L]

/-- **Coefficient fibres at a uniformizer are integral.** Let `n = e(L/K)`, let `c` be a
uniformizer of `L`, and let `1 < r`. A coefficient vector in the Eisenstein region whose
polynomial has a root in the ball `v_L(z - c) ≥ r` is the coefficient vector of a monic polynomial
over `𝒪[K]` with a root in that ball. Conversely, every root in that ball is a uniformizer, so
every monic polynomial of degree `e(L/K)` over `𝒪[K]` with such a root is Eisenstein. Hence this
part of the Eisenstein region is the image of the corresponding set of integral coefficient
vectors. -/
theorem eisensteinSet_inter_setOf_exists_aeval_monicOfCoeff_eq_zero_le_addVal_eq_image
    {n : ℕ} (hn : ramificationIndex K L = n) {r : ℕ} (hr : 1 < r) {c : 𝒪[L]}
    (hc : addVal 𝒪[L] c = 1) :
    eisensteinSet K n ∩ {a | ∃ z : 𝒪[L],
        aeval (z : L) (monicOfCoeff a) = 0 ∧ (r : ℕ∞) ≤ addVal 𝒪[L] (z - c)} =
      (fun b : Fin n → 𝒪[K] ↦ fun i ↦ (b i : K)) '' {b | ∃ z : 𝒪[L],
        aeval z (monicOfCoeff b) = 0 ∧ (r : ℕ∞) ≤ addVal 𝒪[L] (z - c)} := by
  -- Evaluating at `z` commutes with extending the coefficients from `𝒪[K]` to `K`.
  have hroot (b : Fin n → 𝒪[K]) (z : 𝒪[L]) :
      aeval (z : L) (monicOfCoeff fun i ↦ (b i : K)) = 0 ↔ aeval z (monicOfCoeff b) = 0 := by
    have hcomp : (algebraMap K L).comp (algebraMap 𝒪[K] K) =
        (𝒪[L].subtype : 𝒪[L] →+* L).comp (algebraMap 𝒪[K] 𝒪[L]) :=
      RingHom.ext fun x ↦ (coe_algebraMap_integerRing x).symm
    have hmap : (monicOfCoeff fun i ↦ (b i : K)) = (monicOfCoeff b).map (algebraMap 𝒪[K] K) := by
      rw [map_monicOfCoeff, Algebra.coe_algebraMap_ofSubsemiring]
    have hhom := hom_eval₂ (monicOfCoeff b) (algebraMap 𝒪[K] 𝒪[L]) 𝒪[L].subtype z
    simp only [Subring.coe_subtype] at hhom
    rw [hmap, aeval_def, eval₂_map, hcomp, ← hhom, ← aeval_def]
    exact ZeroMemClass.coe_eq_zero
  -- A root in the ball is a uniformizer, since `v_L(c) = 1 < r ≤ v_L(z - c)`.
  have hirr {z : 𝒪[L]} (hz : (r : ℕ∞) ≤ addVal 𝒪[L] (z - c)) : Irreducible z := by
    refine IsDiscreteValuationRing.addVal_eq_one_iff_irreducible.1 ?_
    have hlt : addVal 𝒪[L] c < addVal 𝒪[L] (z - c) :=
      hc ▸ lt_of_lt_of_le (by exact_mod_cast hr) hz
    rw [← add_sub_cancel c z, (addVal 𝒪[L]).map_add_eq_of_lt_left hlt, hc]
  ext a
  constructor
  · rintro ⟨ha, z, hz, hzr⟩
    let b : Fin n → 𝒪[K] := fun i ↦ ⟨a i, mem_integerBox.1 (eisensteinSet_subset_integerBox n ha) i⟩
    exact ⟨b, ⟨z, (hroot b z).1 hz, hzr⟩, rfl⟩
  · rintro ⟨b, ⟨z, hz, hzr⟩, rfl⟩
    refine ⟨mem_eisensteinSet_iff_exists_isEisensteinAt.2 ⟨monicOfCoeff b, ?_, ?_⟩,
      z, (hroot b z).2 hz, hzr⟩
    · rw [map_monicOfCoeff, Algebra.coe_algebraMap_ofSubsemiring]
    · refine isEisensteinAt_of_isRoot_of_irreducible ?_ ((natDegree_monicOfCoeff b).trans hn.symm)
        (hirr hzr) (by rwa [IsRoot, eval_map_algebraMap])
      rw [(monic_monicOfCoeff b).leadingCoeff]
      exact Ideal.one_notMem _

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

end IntegralCoefficients

end TauCeti
