/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Place.Expansion.PowerSeries
public import TauCeti.FieldTheory.FunctionField.Place.Completion.Basic
public import Mathlib.RingTheory.PowerSeries.PiTopology

/-!
# The completed valuation ring at a rational place

Uniformizer expansion identifies the completed valuation ring at a rational place with
`k[[T]]`. Every coefficient sequence is realized: its polynomial partial sums are Cauchy,
and their limit has the prescribed finite expansions. The isomorphism sends a chosen
uniformizer to `T` and identifies the order filtrations. With the constants discrete and
power series given their coefficientwise topology, it is also a homeomorphism.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Section IV.2.
-/

public section

open Filter Topology
open scoped BigOperators WithZero

namespace TauCeti.Place

variable {k F : Type*} [Field k] [Field F] [Algebra k F]
variable (P : Place k F) {t : F} (hP : P.degree = 1) (ht : P.ord t = 1)

private noncomputable def expansionPartialSum (f : PowerSeries k) (n : ℕ) : P.Completion :=
  ∑ i ∈ Finset.range n, algebraMap k P.Completion (PowerSeries.coeff i f) *
    P.completionEmbedding t ^ i

include ht in
private theorem expansionPartialSum_sub_mem (f : PowerSeries k) {n m : ℕ} (hnm : n ≤ m) :
    P.expansionPartialSum (t := t) f m - P.expansionPartialSum (t := t) f n ∈
      P.completionPlace.filtration n := by
  rw [expansionPartialSum, expansionPartialSum, ← Finset.sum_Ico_eq_sub _ hnm]
  apply Submodule.sum_mem
  intro i hi
  have hi' : (n : ℤ) ≤ (i : ℤ) := by exact_mod_cast (Finset.mem_Ico.mp hi).1
  have hpow := P.completionPlace.mem_filtration_ord (P.completionEmbedding t ^ i)
  simp only [ord_pow, ord_completionEmbedding, ht, mul_one] at hpow
  apply P.completionPlace.filtration_antitone hi'
  simpa only [zero_add] using P.completionPlace.mul_mem_filtration
    (P.completionPlace.mem_filtration_zero_iff.mpr
      (P.completionPlace.algebraMap_mem_integers _)) hpow

include ht in
private theorem expansionPartialSum_cauchy (f : PowerSeries k) :
    CauchySeq (P.expansionPartialSum (t := t) f) := by
  apply (Valued.hasBasis_uniformity P.Completion ℤᵐ⁰).cauchySeq_iff.mpr
  intro γ _
  obtain ⟨n, hn⟩ := WithZero.exists_exp_neg_natCast_lt
    (MonoidWithZeroHom.ValueGroup₀.embedding_unit_ne_zero γ)
  refine ⟨n, fun m hm l hl ↦ ?_⟩
  have hdiff : P.expansionPartialSum (t := t) f l -
      P.expansionPartialSum (t := t) f m ∈ P.completionPlace.filtration n := by
    have hm' := P.expansionPartialSum_sub_mem ht f hm
    have hl' := P.expansionPartialSum_sub_mem ht f hl
    convert (P.completionPlace.filtration n).sub_mem hl' hm' using 1
    ring
  simp only [Set.mem_ofPred_eq]
  rw [Valuation.restrict_lt_iff_lt_embedding]
  simpa only [completionPlace_valuation] using
    ((P.completionPlace.mem_filtration_iff.mp hdiff)).trans_lt hn

private theorem isClosed_expansionCongruence (f : PowerSeries k) (n : ℕ) :
    IsClosed {x : P.Completion | x - P.expansionPartialSum (t := t) f n ∈
      P.completionPlace.filtration n} := by
  obtain ⟨s, hs0, hs⟩ := P.exists_ne_zero_ord_eq (n : ℤ)
  have hball := Valued.isClosed_closedBall P.Completion
    (Valued.v.restrict (P.completionEmbedding s))
  have heq : {x : P.Completion | x - P.expansionPartialSum (t := t) f n ∈
      P.completionPlace.filtration n} =
      (fun x : P.Completion ↦ x - P.expansionPartialSum (t := t) f n) ⁻¹'
        {x | Valued.v.restrict x ≤ Valued.v.restrict (P.completionEmbedding s)} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, mem_filtration_iff,
      completionPlace_valuation, Valuation.restrict_le_iff, valuation_completionEmbedding,
      P.valuation_eq_exp_neg_ord hs0, hs]
  rw [heq]
  exact hball.preimage (continuous_id.sub continuous_const)

/-- Every power series over the constants is the uniformizer expansion of an element of
the completed valuation ring at a rational place. -/
theorem completionPlace_powerSeriesExpansion_surjective :
    Function.Surjective (P.completionPlace.powerSeriesExpansion
      (by simpa using hP) (by simpa using ht :
        P.completionPlace.ord (P.completionEmbedding t) = 1)) := by
  intro f
  obtain ⟨x, hx⟩ := cauchySeq_tendsto_of_complete (P.expansionPartialSum_cauchy ht f)
  have hrem (n : ℕ) : x - P.expansionPartialSum (t := t) f n ∈
      P.completionPlace.filtration n := by
    apply (P.isClosed_expansionCongruence (t := t) f n).mem_of_tendsto hx
    filter_upwards [eventually_ge_atTop n] with m hm
    exact P.expansionPartialSum_sub_mem ht f hm
  have hxint : x ∈ P.completionPlace.integers := by
    simpa [expansionPartialSum, mem_filtration_zero_iff] using hrem 0
  refine ⟨⟨x, hxint⟩, ?_⟩
  ext n
  have heq := (P.completionPlace.truncatedExpansion_eq_iff (by simpa using hP)
    (by simpa using ht : P.completionPlace.ord (P.completionEmbedding t) = 1)
    (n + 1) ⟨x, hxint⟩ (fun i ↦ PowerSeries.coeff i f)).mpr (by
      rw [Fin.sum_univ_eq_sum_range (fun i : ℕ ↦
        algebraMap k P.Completion (PowerSeries.coeff i f) * P.completionEmbedding t ^ i)]
      exact hrem (n + 1))
  rw [P.completionPlace.coeff_powerSeriesExpansion _ _ (n + 1) _ ⟨n, by omega⟩, heq]

/-- Uniformizer expansion identifies the completed valuation ring at a rational place with
the power-series ring over the constants. -/
noncomputable def completionIntegersEquivPowerSeries :
    P.completionPlace.integers ≃ₐ[k] PowerSeries k :=
  AlgEquiv.ofBijective (P.completionPlace.powerSeriesExpansion
    (by simpa using hP) (by simpa using ht :
      P.completionPlace.ord (P.completionEmbedding t) = 1))
    ⟨P.completionPlace.powerSeriesExpansion_injective _ _,
      P.completionPlace_powerSeriesExpansion_surjective hP ht⟩

/-- The completed-ring isomorphism is the uniformizer expansion map. -/
theorem completionIntegersEquivPowerSeries_apply (x : P.completionPlace.integers) :
    P.completionIntegersEquivPowerSeries hP ht x =
      P.completionPlace.powerSeriesExpansion (by simpa using hP)
        (by simpa using ht : P.completionPlace.ord (P.completionEmbedding t) = 1) x := (rfl)

/-- The inverse isomorphism realizes a power series to every finite order. -/
theorem sub_sum_coeff_completionIntegersEquivPowerSeries_symm_mem_filtration
    (f : PowerSeries k) (n : ℕ) :
    ((P.completionIntegersEquivPowerSeries hP ht).symm f : P.Completion) -
      ∑ i : Fin n, algebraMap k P.Completion (PowerSeries.coeff i f) *
        P.completionEmbedding t ^ (i : ℕ) ∈ P.completionPlace.filtration n := by
  have h := P.completionPlace.sub_sum_coeff_powerSeriesExpansion_mem_filtration
    (by simpa using hP) (by simpa using ht :
      P.completionPlace.ord (P.completionEmbedding t) = 1) n
    ((P.completionIntegersEquivPowerSeries hP ht).symm f)
  rw [← P.completionIntegersEquivPowerSeries_apply hP ht,
    AlgEquiv.apply_symm_apply] at h
  exact h

/-- The chosen uniformizer maps to the power-series variable. -/
@[simp]
theorem completionIntegersEquivPowerSeries_uniformizer :
    P.completionIntegersEquivPowerSeries hP ht
      (P.completionIntegersEmbedding
        ⟨t, P.mem_integers_iff_ord_nonneg.mpr (by omega)⟩) = PowerSeries.X := by
  rw [P.completionIntegersEquivPowerSeries_apply hP ht]
  have heq : P.completionIntegersEmbedding
      ⟨t, P.mem_integers_iff_ord_nonneg.mpr (by omega)⟩ =
      ⟨P.completionEmbedding t,
        P.completionPlace.mem_integers_iff_ord_nonneg.mpr
          (by simp only [ord_completionEmbedding, ht]; omega)⟩ :=
    Subtype.ext (P.completionIntegersEmbedding_apply _)
  rw [heq]
  exact P.completionPlace.powerSeriesExpansion_uniformizer _ _

section Topology

variable [TopologicalSpace k] [DiscreteTopology k]
open scoped PowerSeries.WithPiTopology

/-- Uniformizer expansion is continuous for the valuation topology on the completed ring
and the coefficientwise topology on power series over the discrete constant field. -/
theorem continuous_completionIntegersEquivPowerSeries :
    Continuous (P.completionIntegersEquivPowerSeries hP ht) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  rw [ContinuousAt, PowerSeries.WithPiTopology.tendsto_iff_coeff_tendsto]
  intro n
  rw [nhds_discrete k, tendsto_pure]
  obtain ⟨s, hs0, hs⟩ := P.exists_ne_zero_ord_eq (n + 1 : ℕ)
  have hs' : Valued.v.restrict (P.completionEmbedding s) ≠ 0 := by simp [hs0]
  have hU : {y : P.Completion | y - (x : P.Completion) ∈
      P.completionPlace.filtration (n + 1 : ℕ)} ∈ 𝓝 (x : P.Completion) := by
    apply Valued.mem_nhds.mpr
    refine ⟨Units.mk0 _ hs', fun y hy ↦ ?_⟩
    simp only [Set.mem_ofPred_eq] at hy ⊢
    rw [P.completionPlace.mem_filtration_iff, completionPlace_valuation]
    rw [Units.val_mk0, Valuation.restrict_lt_iff, valuation_completionEmbedding,
      P.valuation_eq_exp_neg_ord hs0, hs] at hy
    exact hy.le
  filter_upwards [continuous_subtype_val.continuousAt.preimage_mem_nhds hU] with y hy
  have hc := (P.completionPlace.sub_mem_filtration_iff_coeff_powerSeriesExpansion_eq
    (by simpa using hP) (by simpa using ht :
      P.completionPlace.ord (P.completionEmbedding t) = 1) (n + 1) y x).mp hy n (by omega)
  simpa only [P.completionIntegersEquivPowerSeries_apply hP ht] using hc

/-- Realizing a power series in the completed valuation ring is continuous: agreement of
finitely many coefficients gives approximation to any prescribed valuation precision. -/
theorem continuous_completionIntegersEquivPowerSeries_symm :
    Continuous (P.completionIntegersEquivPowerSeries hP ht).symm := by
  apply continuous_induced_rng.mpr
  apply continuous_iff_continuousAt.mpr
  intro f
  apply tendsto_iff_forall_eventually_mem.mpr
  intro U hU
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds.mp hU
  obtain ⟨n, hn⟩ := WithZero.exists_exp_neg_natCast_lt
    (MonoidWithZeroHom.ValueGroup₀.embedding_unit_ne_zero γ)
  have hc : ∀ᶠ g in 𝓝 f, ∀ i : Fin n,
      PowerSeries.coeff i g = PowerSeries.coeff i f := by
    apply Filter.eventually_all.mpr
    intro i
    have hi := (PowerSeries.WithPiTopology.continuous_coeff k i).continuousAt (x := f)
    rw [ContinuousAt, nhds_discrete k, tendsto_pure] at hi
    exact hi
  filter_upwards [hc] with g hg
  apply hγ
  simp only [Set.mem_ofPred_eq]
  rw [Valuation.restrict_lt_iff_lt_embedding]
  have hmem := (P.completionPlace.sub_mem_filtration_iff_coeff_powerSeriesExpansion_eq
    (by simpa using hP) (by simpa using ht :
      P.completionPlace.ord (P.completionEmbedding t) = 1) n
    ((P.completionIntegersEquivPowerSeries hP ht).symm g)
    ((P.completionIntegersEquivPowerSeries hP ht).symm f)).mpr (fun i hi ↦ by
      simpa only [← P.completionIntegersEquivPowerSeries_apply hP ht,
        AlgEquiv.apply_symm_apply] using hg ⟨i, hi⟩)
  simpa only [completionPlace_valuation, Function.comp_apply] using
    (P.completionPlace.mem_filtration_iff.mp hmem).trans_lt hn

/-- The completed valuation ring at a rational place is topologically `k[[T]]`, with `k`
discrete and the power-series ring carrying its coefficientwise topology. -/
noncomputable def completionIntegersHomeomorphPowerSeries :
    P.completionPlace.integers ≃ₜ PowerSeries k where
  toEquiv := (P.completionIntegersEquivPowerSeries hP ht).toEquiv
  continuous_toFun := P.continuous_completionIntegersEquivPowerSeries hP ht
  continuous_invFun := P.continuous_completionIntegersEquivPowerSeries_symm hP ht

/-- The topological identification uses the same uniformizer expansion as the algebraic one. -/
@[simp]
theorem completionIntegersHomeomorphPowerSeries_apply (x : P.completionPlace.integers) :
    P.completionIntegersHomeomorphPowerSeries hP ht x =
      P.completionIntegersEquivPowerSeries hP ht x := (rfl)

/-- The inverse topological identification is the inverse algebraic identification. -/
@[simp]
theorem completionIntegersHomeomorphPowerSeries_symm_apply (f : PowerSeries k) :
    (P.completionIntegersHomeomorphPowerSeries hP ht).symm f =
      (P.completionIntegersEquivPowerSeries hP ht).symm f := (rfl)

end Topology

end TauCeti.Place
