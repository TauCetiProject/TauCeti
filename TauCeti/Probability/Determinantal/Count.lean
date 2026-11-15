/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Determinantal.Ensemble

/-!
# Count laws and gap probabilities of finite determinantal ensembles

Counts include multiplicity and are measurable for every measurable window. Pushing the
labelled ensemble forward gives a probability law for any finite collection of counts.
Its probability generating function is a finite determinant, for arbitrary real or complex
arguments. In particular, the probability of a gap in a measurable window is the determinant
of the complement of the window's Gram matrix.

No atomlessness or continuity of the generators is needed. Each count is at most the number
of particles, so generating functions and gap formulas apply without any moment assumptions
beyond square integrability and orthonormality of the generating family.

## References

* G. W. Anderson, A. Guionnet, O. Zeitouni, *An Introduction to Random Matrices*,
  Cambridge University Press (2010), §§3.2 and 4.2.
-/

public section

noncomputable section

open MeasureTheory Matrix Finset
open scoped ENNReal NNReal

namespace TauCeti

variable {ι E 𝕜 : Type*} [Fintype ι] [RCLike 𝕜]

/-- The number of labelled particles in a window, counting multiplicity. -/
def particleCount (x : ι → E) (B : Set E) : ℕ := by
  classical
  exact (Finset.univ.filter fun i ↦ x i ∈ B).card

/-- A count never exceeds the number of particles. -/
theorem particleCount_le (x : ι → E) (B : Set E) : particleCount x B ≤ Fintype.card ι := by
  classical
  exact (Finset.card_filter_le _ _).trans_eq Finset.card_univ

/-- Counting all particles gives their number, including the empty family. -/
@[simp]
theorem particleCount_univ (x : ι → E) : particleCount x Set.univ = Fintype.card ι := by
  simp [particleCount]

/-- The empty window contains no particle. -/
@[simp]
theorem particleCount_empty (x : ι → E) : particleCount x ∅ = 0 := by
  simp [particleCount]

/-- A gap means that every particle avoids the window. -/
@[simp]
theorem particleCount_eq_zero_iff (x : ι → E) (B : Set E) :
    particleCount x B = 0 ↔ ∀ i, x i ∉ B := by
  classical
  simp [particleCount, Finset.filter_eq_empty_iff]

open Classical in
/-- Powers of a count are products of the one-particle generating factors. -/
theorem pow_particleCount {M : Type*} [CommMonoid M] (x : ι → E) (B : Set E) (z : M) :
    z ^ particleCount x B = ∏ i, if x i ∈ B then z else 1 := by
  classical
  simp [particleCount, Finset.prod_ite]

section Measurable

variable [MeasurableSpace E]

/-- Particle counts are measurable for measurable windows. -/
theorem measurable_particleCount {B : Set E} (hB : MeasurableSet B) :
    Measurable (fun x : ι → E ↦ particleCount x B) := by
  classical
  have h (x : ι → E) : particleCount x B = ∑ i : ι, if x i ∈ B then 1 else 0 := by
    simp [particleCount, Finset.sum_boole]
  simp_rw [h]
  exact Finset.measurable_sum _ fun i _ ↦
    Measurable.ite (hB.preimage (measurable_pi_apply i)) measurable_const measurable_const

variable [DecidableEq ι] {μ : Measure E} [SigmaFinite μ] {φ : ι → E → 𝕜}

/-- The joint law of the counts in a family of windows. It is a probability law whenever
the generators are orthonormal; overlapping windows are allowed. -/
def determinantalCountLaw {κ : Type*} (μ : Measure E) (φ : ι → E → 𝕜) (B : κ → Set E) :
    Measure (κ → ℕ) :=
  (determinantalEnsemble μ φ).map (fun x j ↦ particleCount x (B j))

omit [SigmaFinite μ] in
/-- The count law is exactly the pushforward by the vector of particle counts. -/
theorem determinantalCountLaw_def {κ : Type*} (B : κ → Set E) :
    determinantalCountLaw μ φ B =
      (determinantalEnsemble μ φ).map (fun x j ↦ particleCount x (B j)) := (rfl)

/-- An orthonormal family gives a probability law of its measurable counts. -/
theorem isProbabilityMeasure_determinantalCountLaw {κ : Type*}
    (hφ : ∀ i, MemLp (φ i) 2 μ)
    (horth : ∀ i j, ∫ x, φ i x * star (φ j x) ∂μ = if i = j then 1 else 0)
    (B : κ → Set E) :
    IsProbabilityMeasure (determinantalCountLaw μ φ B) := by
  have := isProbabilityMeasure_determinantalEnsemble hφ horth
  rw [determinantalCountLaw_def]
  infer_instance

omit [Fintype ι] [DecidableEq ι] [SigmaFinite μ] in
open Classical in
private theorem integrable_joint_window_multiplier {κ : Type*} [Fintype κ]
    (hφ : ∀ i, MemLp (φ i) 2 μ) {B : κ → Set E} (hB : ∀ k, MeasurableSet (B k))
    (z : κ → 𝕜) (i j : ι) :
    Integrable (fun x ↦ φ i x * ((∏ k, if x ∈ B k then z k else 1) * star (φ j x))) μ := by
  have hm : Measurable (fun x : E ↦ ∏ k, if x ∈ B k then z k else (1 : 𝕜)) :=
    Finset.measurable_prod _ fun k _ ↦ Measurable.ite (hB k) measurable_const measurable_const
  have hb (x : E) : ‖∏ k, if x ∈ B k then z k else (1 : 𝕜)‖ ≤ ∏ k, max ‖z k‖ 1 := by
    rw [norm_prod]
    apply Finset.prod_le_prod₀ (fun _ _ ↦ norm_nonneg _)
    intro k _
    split_ifs
    · exact le_max_left _ _
    · simp
  simpa only [mul_left_comm, Pi.mul_apply, Pi.star_apply] using
    ((hφ i).integrable_mul (hφ j).star).bdd_mul hm.aestronglyMeasurable (.of_forall hb)

omit [Fintype ι] [DecidableEq ι] [SigmaFinite μ] in
open Classical in
private theorem integrable_window_multiplier (hφ : ∀ i, MemLp (φ i) 2 μ)
    {B : Set E} (hB : MeasurableSet B) (z : 𝕜) (i j : ι) :
    Integrable (fun x ↦ φ i x * ((if x ∈ B then z else 1) * star (φ j x))) μ := by
  simpa using integrable_joint_window_multiplier hφ (B := fun _ : Unit ↦ B)
    (fun _ ↦ hB) (fun _ ↦ z) i j

/-- Orthonormality turns the count generating function into `det (I + (z - 1) G_B)`,
where `G_B` is the matrix of pairwise integrals over the window. -/
theorem integral_pow_particleCount (hφ : ∀ i, MemLp (φ i) 2 μ)
    (horth : ∀ i j, ∫ x, φ i x * star (φ j x) ∂μ = if i = j then 1 else 0)
    {B : Set E} (hB : MeasurableSet B) (z : 𝕜) :
    ∫ x, z ^ particleCount x B ∂determinantalEnsemble μ φ =
      det (1 + (z - 1) • Matrix.of fun i j ↦ ∫ x in B, φ i x * star (φ j x) ∂μ) := by
  classical
  have hi (i j : ι) : Integrable (fun x ↦ φ i x * star (φ j x)) μ :=
    (hφ i).integrable_mul (hφ j).star
  simp_rw [pow_particleCount]
  rw [integral_prod_determinantalEnsemble hφ (integrable_window_multiplier hφ hB z)]
  congr 1
  ext i j
  have heq (x : E) : φ i x * ((if x ∈ B then z else 1) * star (φ j x)) =
      φ i x * star (φ j x) +
        (z - 1) * B.indicator (fun x ↦ φ i x * star (φ j x)) x := by
    by_cases hx : x ∈ B <;> simp [hx]; ring
  simp only [Matrix.of_apply, heq, integral_add (hi i j)
    (((hi i j).indicator hB).const_mul (z - 1)), integral_const_mul,
    integral_indicator hB, horth, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.one_apply]

/-- **The gap formula**: no particle lies in `B` with probability `det (I - G_B)`.
The result uses the real part only to express the probability as a real number; the
determinant itself equals that real probability. -/
theorem measureReal_particleCount_eq_zero (hφ : ∀ i, MemLp (φ i) 2 μ)
    (horth : ∀ i j, ∫ x, φ i x * star (φ j x) ∂μ = if i = j then 1 else 0)
    {B : Set E} (hB : MeasurableSet B) :
    (determinantalEnsemble μ φ).real {x | particleCount x B = 0} =
      RCLike.re (det (1 - Matrix.of fun i j ↦ ∫ x in B, φ i x * star (φ j x) ∂μ)) := by
  have := isProbabilityMeasure_determinantalEnsemble hφ horth
  have h := integral_pow_particleCount hφ horth hB (0 : 𝕜)
  have hset : MeasurableSet {x : ι → E | particleCount x B = 0} :=
    (measurable_particleCount hB) (measurableSet_singleton 0)
  have hf (x : ι → E) : (0 : 𝕜) ^ particleCount x B =
      {x : ι → E | particleCount x B = 0}.indicator (fun _ ↦ (1 : 𝕜)) x := by
    by_cases hx : particleCount x B = 0
    · simp only [Set.indicator_apply, Set.mem_ofPred_eq, hx, pow_zero, ite_true]
    · simp only [Set.indicator_apply, Set.mem_ofPred_eq, hx, ite_false]
      exact zero_pow hx
  simp_rw [hf] at h
  rw [integral_indicator hset, integral_const] at h
  simpa only [zero_sub, neg_smul, one_smul, ← sub_eq_add_neg,
    measureReal_restrict_apply_univ, RCLike.real_smul_eq_coe_mul, mul_one, RCLike.ofReal_re]
      using congrArg RCLike.re h

open Classical in
/-- **The joint count generating function**, with overlapping windows allowed. The weight
inside each Gram entry is the product of the one-window factors. The formula holds at every
real or complex vector `z`, since a finite ensemble has bounded counts. -/
theorem integral_prod_pow_determinantalCountLaw {κ : Type*} [Fintype κ]
    (hφ : ∀ i, MemLp (φ i) 2 μ) {B : κ → Set E} (hB : ∀ k, MeasurableSet (B k))
    (z : κ → 𝕜) :
    ∫ c, ∏ k, z k ^ c k ∂determinantalCountLaw μ φ B =
      det (Matrix.of fun i j ↦ ∫ x,
        φ i x * ((∏ k, if x ∈ B k then z k else 1) * star (φ j x)) ∂μ) := by
  have hm : Measurable (fun c : κ → ℕ ↦ ∏ k, z k ^ c k) :=
    Finset.measurable_prod _ fun k _ ↦
      (measurable_of_countable (fun n : ℕ ↦ z k ^ n)).comp (measurable_pi_apply k)
  rw [determinantalCountLaw_def, integral_map
    (Measurable.of_eval fun k ↦ measurable_particleCount (hB k)).aemeasurable
    hm.aestronglyMeasurable]
  simp_rw [pow_particleCount]
  simp_rw [Finset.prod_comm (s := (univ : Finset κ))]
  exact integral_prod_determinantalEnsemble hφ (integrable_joint_window_multiplier hφ hB z)

omit [MeasurableSpace E] in
open Classical in
private theorem prod_window_weight_of_pairwise_disjoint {κ : Type*} [Fintype κ]
    {B : κ → Set E} (hdisj : Pairwise (fun i j ↦ Disjoint (B i) (B j)))
    (z : κ → 𝕜) (x : E) :
    (∏ k, if x ∈ B k then z k else 1) =
      1 + ∑ k, (B k).indicator (fun _ ↦ z k - 1) x := by
  classical
  by_cases hx : ∃ k, x ∈ B k
  · obtain ⟨k, hk⟩ := hx
    have hn (j : κ) (hjk : j ≠ k) : x ∉ B j := by
      exact fun hj ↦ Set.disjoint_left.mp (hdisj hjk) hj hk
    rw [Finset.prod_eq_single k, Finset.sum_eq_single k]
    · simp [hk]
    · intro j _ hjk
      simp [hn j hjk]
    · simp
    · intro j _ hjk
      simp [hn j hjk]
    · simp
  · have hn : ∀ k, x ∉ B k := by simpa using hx
    simp [hn]

/-- **The determinantal joint count formula on disjoint windows.** The generating matrix is
`I + ∑ₖ (zₖ - 1) G_{Bₖ}`. Disjointness is used only for this linear form; the general formula
also applies to overlapping windows. -/
theorem integral_prod_pow_determinantalCountLaw_eq_det {κ : Type*} [Fintype κ]
    (hφ : ∀ i, MemLp (φ i) 2 μ)
    (horth : ∀ i j, ∫ x, φ i x * star (φ j x) ∂μ = if i = j then 1 else 0)
    {B : κ → Set E} (hB : ∀ k, MeasurableSet (B k))
    (hdisj : Pairwise (fun i j ↦ Disjoint (B i) (B j))) (z : κ → 𝕜) :
    ∫ c, ∏ k, z k ^ c k ∂determinantalCountLaw μ φ B =
      det (1 + ∑ k, (z k - 1) •
        Matrix.of fun i j ↦ ∫ x in B k, φ i x * star (φ j x) ∂μ) := by
  classical
  have hi (i j : ι) : Integrable (fun x ↦ φ i x * star (φ j x)) μ :=
    (hφ i).integrable_mul (hφ j).star
  have hterm (i j : ι) (k : κ) :
      Integrable (fun x ↦ (z k - 1) * (B k).indicator
        (fun x ↦ φ i x * star (φ j x)) x) μ :=
    ((hi i j).indicator (hB k)).const_mul _
  rw [integral_prod_pow_determinantalCountLaw hφ hB]
  congr 1
  ext i j
  have heq (x : E) : φ i x *
      ((∏ k, if x ∈ B k then z k else 1) * star (φ j x)) =
      φ i x * star (φ j x) + ∑ k, (z k - 1) *
        (B k).indicator (fun x ↦ φ i x * star (φ j x)) x := by
    rw [prod_window_weight_of_pairwise_disjoint hdisj]
    simp only [add_mul, one_mul, mul_add, Finset.sum_mul, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    by_cases hx : x ∈ B k <;> simp [hx]; ring
  simp only [Matrix.of_apply, heq, integral_add (hi i j)
    (integrable_finsetSum _ fun k _ ↦ hterm i j k),
    integral_finsetSum _ fun k _ ↦ hterm i j k, integral_const_mul,
    integral_indicator (hB _), horth, Matrix.add_apply, Matrix.sum_apply,
    Matrix.smul_apply, smul_eq_mul, Matrix.one_apply]

end Measurable

end TauCeti
