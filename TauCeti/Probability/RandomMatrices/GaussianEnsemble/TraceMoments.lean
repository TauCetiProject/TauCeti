/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.RandomMatrices.GaussianEnsemble.Measure
public import TauCeti.Combinatorics.Enumerative.PerfectMatching.Weighted
public import TauCeti.GroupTheory.Perm.OrbitCount.Basic
import Mathlib.MeasureTheory.SpecificCodomains.Pi
import Mathlib.Probability.Distributions.Gaussian.Fernique
import TauCeti.GroupTheory.Perm.Cycle.Colouring
import TauCeti.LinearAlgebra.Matrix.Trace.Pow
import TauCeti.Probability.Distributions.Gaussian.Wick
import TauCeti.Probability.RandomMatrices.GaussianEnsemble.Covariance

/-!
# Wick expansion of GUE trace moments

A GUE entry product has expectation given by perfect matchings of its positions. Each matched
pair must read the same matrix entry in opposite directions. In a product of traces, the
cyclic successor permutation records the order of factors in each trace. Matching the
entries makes the vertex labels constant on the cycles of the successor composed with the
matching, giving a power of the dimension for each matching.

## References

* R. Speicher, *Lecture Notes on Random Matrices*, arXiv:2009.05157, §2.2.
-/

public section

noncomputable section

open Equiv Matrix MeasureTheory ProbabilityTheory Finset

namespace TauCeti.Probability

variable {ι : Type*} [Fintype ι] {n : ℕ}

private def gueEntry (p : Fin n × Fin n) : (Fin n × Fin n → ℝ) →L[ℝ] ℂ where
  toFun g := gaussianEnsemble 2 n g p.1 p.2
  map_add' g h := by rw [gaussianEnsemble_add, Matrix.add_apply]
  map_smul' c g := by rw [gaussianEnsemble_smul, Matrix.smul_apply, RingHom.id_apply]
  cont := (continuous_gaussianEnsemble (β := 2) (n := n)).matrix_elem p.1 p.2

private theorem gueEntry_apply (p : Fin n × Fin n) (g : Fin n × Fin n → ℝ) :
    gueEntry p g = gaussianEnsemble 2 n g p.1 p.2 := rfl

private theorem integral_gueEntry (p : Fin n × Fin n) :
    (∫ g, gueEntry p g ∂(Measure.pi fun _ : Fin n × Fin n ↦ gaussianReal 0 1)) = 0 := by
  have h : (∫ g : Fin n × Fin n → ℝ, g ∂(Measure.pi fun _ : Fin n × Fin n ↦ gaussianReal 0 1)) =
      0 := by
    ext q
    rw [eval_integral (fun q ↦ IsGaussian.integrable_id.eval q) q, integral_eval,
      integral_id_gaussianReal]
    rfl
  have hcomp := (gueEntry p).integral_comp_comm
    (μ := Measure.pi fun _ : Fin n × Fin n ↦ gaussianReal 0 1) IsGaussian.integrable_id
  simpa only [id_eq, h, map_zero] using hcomp

private theorem integral_gueEntry_mul (p q : Fin n × Fin n) :
    (∫ g, gueEntry p g * gueEntry q g ∂(Measure.pi fun _ : Fin n × Fin n ↦ gaussianReal 0 1)) =
      if p.1 = q.2 ∧ p.2 = q.1 then (n : ℂ)⁻¹ else 0 := by
  simpa [gueEntry_apply, sum_gaussianEnsemble_single_apply_mul_apply_of_ne_one
    (by decide : (2 : ℕ) ≠ 1)]
    using integral_clm_mul_prod_pi_gaussianReal ({()} : Finset Unit) (gueEntry p)
      (fun _ ↦ gueEntry q) 0

/-- Every finite product of GUE entries is integrable, including repeated entries. -/
theorem integrable_prod_apply_gaussianEnsembleLaw_two (w v : ι → Fin n) :
    Integrable (fun A ↦ ∏ i, A (w i) (v i)) (gaussianEnsembleLaw 2 n) := by
  have hf : Continuous (fun A : Matrix (Fin n) (Fin n) ℂ ↦ ∏ i, A (w i) (v i)) :=
    continuous_finsetProd _ fun i _ ↦ continuous_id.matrix_elem (w i) (v i)
  rw [gaussianEnsembleLaw_def, integrable_map_measure hf.aestronglyMeasurable
    measurable_gaussianEnsemble.aemeasurable]
  simpa only [Function.comp_def, gueEntry_apply, Pi.zero_apply, add_zero] using
    IsGaussian.integrable_prod_clm (Measure.pi fun _ : Fin n × Fin n ↦ gaussianReal 0 1)
      (univ : Finset ι) (fun i ↦ gueEntry (w i, v i)) 0

variable [DecidableEq ι]

/-- The expected product of GUE entries is the sum over perfect matchings of the positions.
A pair contributes the inverse dimension when the two entries have reversed indices, and zero
otherwise. -/
theorem integral_prod_apply_gaussianEnsembleLaw_two_eq_sum_perfectMatching
    (w v : ι → Fin n) :
    (∫ A, ∏ i, A (w i) (v i) ∂gaussianEnsembleLaw 2 n) =
      ∑ D : PerfectMatching ι, ∏ e ∈ D.edgeFinset,
        Sym2.lift ⟨fun i j ↦ if w i = v j ∧ v i = w j then (n : ℂ)⁻¹ else 0,
          fun i j ↦ by simp only [eq_comm, and_comm]⟩ e := by
  have hf : Continuous (fun A : Matrix (Fin n) (Fin n) ℂ ↦ ∏ i, A (w i) (v i)) :=
    continuous_finsetProd _ fun i _ ↦ continuous_id.matrix_elem (w i) (v i)
  rw [gaussianEnsembleLaw_def, integral_map measurable_gaussianEnsemble.aemeasurable
    hf.aestronglyMeasurable]
  have h := IsGaussian.integral_prod_sub_clm_eq_sum_perfectMatching
    (Measure.pi fun _ : Fin n × Fin n ↦ gaussianReal 0 1) (fun i ↦ gueEntry (w i, v i))
  simp only [integral_gueEntry, sub_zero, integral_gueEntry_mul] at h
  simpa only [gueEntry_apply] using h

private theorem prod_guePair_eq_ite (σ : Perm ι) (D : PerfectMatching ι) (w : ι → Fin n) :
    (∏ e ∈ D.edgeFinset, Sym2.lift
      ⟨fun i j ↦ if w i = w (σ j) ∧ w (σ i) = w j then (n : ℂ)⁻¹ else 0,
        fun i j ↦ by simp only [eq_comm, and_comm]⟩ e) =
      if w ∘ (σ * D.val) = w then (n : ℂ)⁻¹ ^ (Fintype.card ι / 2) else 0 := by
  classical
  by_cases hw : w ∘ (σ * D.val) = w
  · rw [ite_eq_left hw, ← D.card_edgeFinset, ← Finset.prod_const]
    refine Finset.prod_congr rfl fun e he ↦ ?_
    obtain ⟨i, rfl⟩ := (D.mem_edgeFinset e).mp he
    have hi := congrFun hw i
    have hj := congrFun hw (D.val i)
    simp only [Function.comp_apply, Perm.mul_apply, D.apply_apply] at hi hj
    exact ite_eq_left ⟨hi.symm, hj⟩
  · rw [ite_eq_right hw]
    have ⟨i, hi⟩ : ∃ i, w (σ (D.val i)) ≠ w i := by
      by_contra! h
      exact hw (funext h)
    refine Finset.prod_eq_zero ((D.mk_mem_edgeFinset i (D.val i)).mpr rfl) ?_
    exact ite_eq_right fun h ↦ hi h.1.symm

private theorem sum_guePair_eq_orbitCount (σ : Perm ι) (D : PerfectMatching ι) :
    (∑ w : ι → Fin n, if w ∘ (σ * D.val) = w then (n : ℂ)⁻¹ ^ (Fintype.card ι / 2) else 0) =
      (n : ℂ) ^ orbitCount (σ * D.val) * (n : ℂ)⁻¹ ^ (Fintype.card ι / 2) := by
  classical
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  have hc : (univ.filter fun w : ι → Fin n ↦ w ∘ (σ * D.val) = w).card =
      n ^ orbitCount (σ * D.val) := by
    rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card,
      Perm.card_invariantColouring, Perm.card_fullCycleType, Nat.card_fin, orbitCount_def]
  rw [hc, Nat.cast_pow]

/-- A permutation specifies which positions follow which in a product of cyclic GUE matrix
words. Summing the expected entry products over all vertex labels gives one term per perfect
matching. The number of free labels is the number of cycles of the successor permutation
composed with the matching, including fixed points. -/
theorem integral_sum_prod_apply_gaussianEnsembleLaw_two_eq_sum_perfectMatching
    (σ : Perm ι) :
    (∫ A, ∑ w : ι → Fin n, ∏ i, A (w i) (w (σ i)) ∂gaussianEnsembleLaw 2 n) =
      ∑ D : PerfectMatching ι,
        (n : ℂ) ^ orbitCount (σ * D.val) * (n : ℂ)⁻¹ ^ (Fintype.card ι / 2) := by
  rw [integral_finsetSum]
  · simp_rw [integral_prod_apply_gaussianEnsembleLaw_two_eq_sum_perfectMatching]
    rw [Finset.sum_comm]
    simp_rw [prod_guePair_eq_ite, sum_guePair_eq_orbitCount]
  · exact fun w _ ↦ integrable_prod_apply_gaussianEnsembleLaw_two w (w ∘ σ)

/-- The expected trace of a positive power of a GUE matrix is a sum over pairings of the
positions in the trace. Each pairing contributes one factor of the dimension for each cycle of
its composition with the cyclic successor, and one inverse dimension for each pair. -/
theorem integral_trace_pow_gaussianEnsembleLaw_two_eq_sum_perfectMatching {k : ℕ} (hk : k ≠ 0) :
    (∫ A, (A ^ k).trace ∂gaussianEnsembleLaw 2 n) =
      ∑ D : PerfectMatching (Fin k),
        (n : ℂ) ^ orbitCount (finRotate k * D.val) * (n : ℂ)⁻¹ ^ (k / 2) := by
  simp_rw [Matrix.trace_pow_eq_sum_prod _ hk]
  simpa only [Fintype.card_fin] using
    integral_sum_prod_apply_gaussianEnsembleLaw_two_eq_sum_perfectMatching (n := n) (finRotate k)

/-- The mixed moments of traces of GUE powers are given by pairings of all trace positions.
The successor advances cyclically within each trace. A trace of the zeroth power contributes
one factor of the dimension and has no positions to pair. -/
theorem integral_prod_trace_pow_gaussianEnsembleLaw_two_eq_sum_perfectMatching (k : ι → ℕ) :
    (∫ A, ∏ i, (A ^ k i).trace ∂gaussianEnsembleLaw 2 n) =
      (∏ i, if k i = 0 then (n : ℂ) else 1) *
        ∑ D : PerfectMatching (Σ i, Fin (k i)),
          (n : ℂ) ^ orbitCount (Equiv.sigmaCongrRight (fun i ↦ finRotate (k i)) * D.val) *
            (n : ℂ)⁻¹ ^ ((∑ i, k i) / 2) := by
  classical
  let σ : Perm (Σ i, Fin (k i)) := Equiv.sigmaCongrRight fun i ↦ finRotate (k i)
  have hword (A : Matrix (Fin n) (Fin n) ℂ) (i : ι) :
      (A ^ k i).trace = (if k i = 0 then (n : ℂ) else 1) *
        ∑ w : Fin (k i) → Fin n, ∏ t, A (w t) (w (finRotate (k i) t)) := by
    by_cases hi : k i = 0
    · simp [hi, Matrix.trace_one]
    · simp [hi, Matrix.trace_pow_eq_sum_prod A hi]
  have hprod (A : Matrix (Fin n) (Fin n) ℂ) :
      ∏ i, (A ^ k i).trace =
        (∏ i, if k i = 0 then (n : ℂ) else 1) *
          ∑ w : (Σ i, Fin (k i)) → Fin n, ∏ t, A (w t) (w (σ t)) := by
    simp_rw [hword]
    rw [Finset.prod_mul_distrib, Fintype.prod_sum]
    congr 1
    rw [← (Equiv.piCurry fun i (_ : Fin (k i)) ↦ Fin n).sum_comp]
    simp [Fintype.prod_sigma, σ, Sigma.curry]
  simp_rw [hprod]
  rw [integral_const_mul]
  simpa only [Fintype.card_sigma, Fintype.card_fin, σ] using congrArg
    ((∏ i, if k i = 0 then (n : ℂ) else 1) * ·)
    (integral_sum_prod_apply_gaussianEnsembleLaw_two_eq_sum_perfectMatching (n := n) σ)

end TauCeti.Probability
