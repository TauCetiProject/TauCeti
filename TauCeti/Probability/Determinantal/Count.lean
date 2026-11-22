/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Determinantal.Ensemble
public import TauCeti.Probability.PointProcess.ParticleCount
import TauCeti.Algebra.BigOperators.Group.Finset.Indicator
import TauCeti.MeasureTheory.Function.L1Space.Integrable

/-!
# Count laws and gap probabilities of finite determinantal ensembles

Pushing the labelled ensemble forward by the particle counts of a finite family of windows
gives a probability law of the counts. Integration against it is integration of the count
vector against the ensemble. Its probability generating function is a finite determinant, for
arbitrary real or complex arguments. In particular, the probability of a gap in a window is
the determinant of the complement of the window's Gram matrix.

Windows need only be null-measurable for the reference measure, and the linear form of the
generating function needs only almost everywhere disjoint windows. No atomlessness or
continuity of the generators is needed. Each count is at most the number of particles, so
generating functions and gap formulas apply without any moment assumptions beyond square
integrability and orthonormality of the generating family.

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
  [MeasurableSpace E] [DecidableEq ι] {μ : Measure E} [SigmaFinite μ] {φ : ι → E → 𝕜}

/-- Particle counts in a null-measurable window are almost everywhere measurable under the
labelled ensemble. -/
theorem aemeasurable_particleCount_determinantalEnsemble {B : Set E}
    (hB : NullMeasurableSet B μ) :
    AEMeasurable (fun x : ι → E ↦ particleCount x B) (determinantalEnsemble μ φ) := by
  rw [determinantalEnsemble_def]
  exact (aemeasurable_particleCount hB).mono_ac (withDensity_absolutelyContinuous _ _)

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

/-- Almost everywhere equal generators define the same count law. -/
theorem determinantalCountLaw_congr_ae {κ : Type*} {ψ : ι → E → 𝕜} (h : ∀ i, φ i =ᵐ[μ] ψ i)
    (B : κ → Set E) : determinantalCountLaw μ φ B = determinantalCountLaw μ ψ B := by
  rw [determinantalCountLaw_def, determinantalCountLaw_def, determinantalEnsemble_congr_ae h]

/-- An orthonormal family gives a probability law of its counts. -/
theorem isProbabilityMeasure_determinantalCountLaw {κ : Type*}
    (hφ : ∀ i, MemLp (φ i) 2 μ)
    (horth : ∀ i j, ∫ x, φ i x * star (φ j x) ∂μ = if i = j then 1 else 0)
    (B : κ → Set E) :
    IsProbabilityMeasure (determinantalCountLaw μ φ B) := by
  have := isProbabilityMeasure_determinantalEnsemble hφ horth
  rw [determinantalCountLaw_def]
  infer_instance

/-- Integration against the count law of finitely many null-measurable windows is integration
of the count vector against the labelled ensemble. -/
theorem integral_determinantalCountLaw {κ F : Type*} [Finite κ] [NormedAddCommGroup F]
    [NormedSpace ℝ F] {B : κ → Set E} (hB : ∀ k, NullMeasurableSet (B k) μ)
    (f : (κ → ℕ) → F) :
    ∫ c, f c ∂determinantalCountLaw μ φ B =
      ∫ x, f (fun k ↦ particleCount x (B k)) ∂determinantalEnsemble μ φ := by
  rw [determinantalCountLaw_def, integral_map (AEMeasurable.of_eval fun k ↦
    aemeasurable_particleCount_determinantalEnsemble (hB k)) .of_discrete]

/-- Integrability for the count law of finitely many null-measurable windows is integrability
of the count vector for the labelled ensemble. -/
theorem integrable_determinantalCountLaw_iff {κ F : Type*} [Finite κ] [NormedAddCommGroup F]
    {B : κ → Set E} (hB : ∀ k, NullMeasurableSet (B k) μ) {f : (κ → ℕ) → F} :
    Integrable f (determinantalCountLaw μ φ B) ↔
      Integrable (fun x ↦ f (fun k ↦ particleCount x (B k))) (determinantalEnsemble μ φ) := by
  rw [determinantalCountLaw_def, integrable_map_measure .of_discrete (AEMeasurable.of_eval
    fun k ↦ aemeasurable_particleCount_determinantalEnsemble (hB k)), Function.comp_def]

omit [Fintype ι] [SigmaFinite μ] [DecidableEq ι] in
private theorem integrable_mul_prod_mulIndicator_mul {κ : Type*} [Fintype κ]
    (hφ : ∀ i, MemLp (φ i) 2 μ) {B : κ → Set E} (hB : ∀ k, NullMeasurableSet (B k) μ)
    (z : κ → 𝕜) (i j : ι) :
    Integrable (fun x ↦ φ i x * ((∏ k, (B k).mulIndicator (fun _ ↦ z k) x) * star (φ j x))) μ := by
  simpa only [Pi.mul_apply, Pi.star_apply, smul_eq_mul, mul_left_comm] using
    ((hφ i).integrable_mul (hφ j).star).prod_mulIndicator_const_smul
      univ (fun k _ ↦ hB k) z

/-- The joint count generating function is integrable for every real or complex vector `z`,
since a finite ensemble has bounded counts. Orthonormality is not needed. -/
theorem integrable_prod_pow_determinantalCountLaw {κ : Type*} [Fintype κ]
    (hφ : ∀ i, MemLp (φ i) 2 μ) {B : κ → Set E} (hB : ∀ k, NullMeasurableSet (B k) μ)
    (z : κ → 𝕜) :
    Integrable (fun c : κ → ℕ ↦ ∏ k, z k ^ c k) (determinantalCountLaw μ φ B) := by
  rw [integrable_determinantalCountLaw_iff hB]
  simp_rw [prod_pow_particleCount]
  exact integrable_prod_determinantalEnsemble (fun i ↦ (hφ i).aemeasurable)
    (integrable_mul_prod_mulIndicator_mul hφ hB z)

/-- **The joint count generating function**, with overlapping windows allowed. The weight
inside each Gram entry is the product of the one-window factors. The formula holds at every
real or complex vector `z`, since a finite ensemble has bounded counts. -/
theorem integral_prod_pow_determinantalCountLaw {κ : Type*} [Fintype κ]
    (hφ : ∀ i, MemLp (φ i) 2 μ) {B : κ → Set E} (hB : ∀ k, NullMeasurableSet (B k) μ)
    (z : κ → 𝕜) :
    ∫ c, ∏ k, z k ^ c k ∂determinantalCountLaw μ φ B =
      det (Matrix.of fun i j ↦ ∫ x,
        φ i x * ((∏ k, (B k).mulIndicator (fun _ ↦ z k) x) * star (φ j x)) ∂μ) := by
  rw [integral_determinantalCountLaw hB]
  simp_rw [prod_pow_particleCount]
  exact integral_prod_determinantalEnsemble (fun i ↦ (hφ i).aemeasurable)
    (integrable_mul_prod_mulIndicator_mul hφ hB z)

/-- **The determinantal joint count formula on almost everywhere disjoint windows.** The
generating matrix is `I + ∑ₖ (zₖ - 1) G_{Bₖ}`. Disjointness is used only for this linear form;
the general formula also applies to overlapping windows. -/
theorem integral_prod_pow_determinantalCountLaw_of_pairwise_aedisjoint {κ : Type*}
    [Fintype κ] (hφ : ∀ i, MemLp (φ i) 2 μ)
    (horth : ∀ i j, ∫ x, φ i x * star (φ j x) ∂μ = if i = j then 1 else 0)
    {B : κ → Set E} (hB : ∀ k, NullMeasurableSet (B k) μ)
    (hdisj : Pairwise fun k l ↦ AEDisjoint μ (B k) (B l)) (z : κ → 𝕜) :
    ∫ c, ∏ k, z k ^ c k ∂determinantalCountLaw μ φ B =
      det (1 + ∑ k, (z k - 1) •
        Matrix.of fun i j ↦ ∫ x in B k, φ i x * star (φ j x) ∂μ) := by
  obtain ⟨t, -, hBt, ht, htd⟩ := exists_subordinate_pairwise_disjoint hB hdisj
  rw [integral_prod_pow_determinantalCountLaw hφ hB]
  congr 1
  ext i j
  have hi : Integrable (fun x ↦ φ i x * star (φ j x)) μ := (hφ i).integrable_mul (hφ j).star
  have hk (k : κ) : Integrable (fun x ↦ (z k - 1) *
      (t k).indicator (fun x ↦ φ i x * star (φ j x)) x) μ :=
    (hi.indicator (ht k)).const_mul _
  have hw : (fun x ↦ φ i x * ((∏ k, (B k).mulIndicator (fun _ ↦ z k) x) * star (φ j x))) =ᵐ[μ]
      fun x ↦ φ i x * star (φ j x) +
        ∑ k, (z k - 1) * (t k).indicator (fun x ↦ φ i x * star (φ j x)) x := by
    filter_upwards [ae_all_iff.2 fun k ↦ (hBt k).mem_iff] with x hx
    have hprod : ∏ k, (B k).mulIndicator (fun _ ↦ z k) x =
        ∏ k, (t k).mulIndicator (fun _ ↦ z k) x :=
      Finset.prod_congr rfl fun k _ ↦ by classical simp only [Set.mulIndicator_apply, hx k]
    rw [hprod, Finset.prod_mulIndicator_eq_one_add_sum_indicator univ
      (fun _ _ _ _ hkl ↦ htd hkl), add_mul, one_mul, mul_add, Finset.sum_mul, Finset.mul_sum]
    refine congrArg _ (Finset.sum_congr rfl fun k _ ↦ ?_)
    by_cases h : x ∈ t k <;> simp [h]
    ring
  rw [Matrix.of_apply, integral_congr_ae hw,
    integral_add hi (integrable_finsetSum _ fun k _ ↦ hk k),
    integral_finsetSum _ fun k _ ↦ hk k, horth]
  simp_rw [integral_const_mul, integral_indicator (ht _), ← setIntegral_congr_set (hBt _)]
  simp [Matrix.add_apply, Matrix.one_apply, Matrix.sum_apply]

/-- Orthonormality turns the count generating function into `det (I + (z - 1) G_B)`,
where `G_B` is the matrix of pairwise integrals over the window. -/
theorem integral_pow_particleCount_determinantalEnsemble (hφ : ∀ i, MemLp (φ i) 2 μ)
    (horth : ∀ i j, ∫ x, φ i x * star (φ j x) ∂μ = if i = j then 1 else 0)
    {B : Set E} (hB : NullMeasurableSet B μ) (z : 𝕜) :
    ∫ x, z ^ particleCount x B ∂determinantalEnsemble μ φ =
      det (1 + (z - 1) • Matrix.of fun i j ↦ ∫ x in B, φ i x * star (φ j x) ∂μ) := by
  have h := integral_prod_pow_determinantalCountLaw_of_pairwise_aedisjoint (κ := Unit)
    hφ horth (B := fun _ ↦ B) (fun _ ↦ hB)
    (fun i j hij ↦ (hij (Subsingleton.elim i j)).elim) (fun _ ↦ z)
  rw [integral_determinantalCountLaw fun _ ↦ hB] at h
  simpa only [Fintype.prod_unique, Fintype.sum_unique] using h

/-- The count generating function of one window is integrable for every real or complex `z`.
Orthonormality is not needed. -/
theorem integrable_pow_particleCount_determinantalEnsemble (hφ : ∀ i, MemLp (φ i) 2 μ)
    {B : Set E} (hB : NullMeasurableSet B μ) (z : 𝕜) :
    Integrable (fun x ↦ z ^ particleCount x B) (determinantalEnsemble μ φ) := by
  have h := integrable_prod_pow_determinantalCountLaw (κ := Unit) hφ (B := fun _ ↦ B)
    (fun _ ↦ hB) (fun _ ↦ z)
  rw [integrable_determinantalCountLaw_iff fun _ ↦ hB] at h
  simpa only [Fintype.prod_unique] using h

/-- **The gap formula**: no particle lies in `B` with probability `det (I - G_B)`.
The result uses the real part only to express the probability as a real number; the
determinant itself equals that real probability. -/
theorem measureReal_determinantalEnsemble_particleCount_eq_zero (hφ : ∀ i, MemLp (φ i) 2 μ)
    (horth : ∀ i j, ∫ x, φ i x * star (φ j x) ∂μ = if i = j then 1 else 0)
    {B : Set E} (hB : NullMeasurableSet B μ) :
    (determinantalEnsemble μ φ).real {x | particleCount x B = 0} =
      RCLike.re (det (1 - Matrix.of fun i j ↦ ∫ x in B, φ i x * star (φ j x) ∂μ)) := by
  have h := integral_pow_particleCount_determinantalEnsemble hφ horth hB (0 : 𝕜)
  have hset : NullMeasurableSet {x : ι → E | particleCount x B = 0}
      (determinantalEnsemble μ φ) :=
    (aemeasurable_particleCount_determinantalEnsemble hB).nullMeasurableSet_preimage
      (measurableSet_singleton 0)
  have hf (x : ι → E) : (0 : 𝕜) ^ particleCount x B =
      {x : ι → E | particleCount x B = 0}.indicator (fun _ ↦ (1 : 𝕜)) x := by
    by_cases hx : particleCount x B = 0
    · simp only [Set.indicator_apply, Set.mem_ofPred_eq, hx, pow_zero, ite_true]
    · simp only [Set.indicator_apply, Set.mem_ofPred_eq, hx, ite_false]
      exact zero_pow hx
  simp_rw [hf] at h
  rw [integral_indicator₀ hset, integral_const] at h
  simpa only [zero_sub, neg_smul, one_smul, ← sub_eq_add_neg,
    measureReal_restrict_apply_univ, RCLike.real_smul_eq_coe_mul, mul_one, RCLike.ofReal_re]
      using congrArg RCLike.re h

end TauCeti
