/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.TraceWord.Bipartite.Leading
public import TauCeti.Analysis.Matrix.SampleSecondMoment
public import Mathlib.Probability.Independence.Integration
import TauCeti.Probability.RandomMatrix.SampleCovariance.TraceWord
import TauCeti.Combinatorics.TraceWord.Bipartite.Counting
import TauCeti.MeasureTheory.Integral.MeanInequalities

/-!
# The rectangular trace-word method for sample covariance moments

For independent centred entries, the expected trace expansion has no singleton-edge terms.
A leading word matches each entry with its conjugate, and its expectation is the product of
the corresponding second absolute moments. The leading words are counted by noncrossing
column partitions with injective row and column labellings. The remaining words contribute
an error controlled by the absolute entry moment of order twice the trace exponent.

## References

* Z. D. Bai, *Methodologies in spectral analysis of large dimensional random matrices,
  a review*, Statistica Sinica 9 (1999), §2.1.2, (2.15).
-/

public section

open MeasureTheory ProbabilityTheory Matrix Finset Function
open scoped NNReal

namespace TauCeti.Probability

variable {Ω 𝕜 p n : Type*} [MeasurableSpace Ω] [RCLike 𝕜]
  {P : Measure Ω} {X : Ω → Matrix p n 𝕜} {k : ℕ}

/-- The trace of the `k`th power of a sample covariance matrix is integrable when the entries lie in
`L^(2k)`. There are no independence or centring assumptions. -/
theorem integrable_trace_sampleCovariance_pow [Fintype p] [DecidableEq p] [Fintype n]
    (hXk : ∀ i j, MemLp (fun ω ↦ X ω i j) (2 * k) P)
    [IsFiniteMeasure P] :
    Integrable (fun ω ↦ ((X ω).sampleCovariance ^ k).trace) P := by
  rcases eq_or_ne k 0 with rfl | hk
  · simp
  simp_rw [sampleCovariance_def, smul_pow, trace_smul, RCLike.real_smul_eq_coe_mul,
    trace_mul_conjTranspose_pow_eq_sum_prod _ hk]
  exact (integrable_finsetSum _ fun u _ ↦ integrable_finsetSum _ fun v _ ↦
    integrable_prod_apply_mul_star_apply hk hXk u v).const_mul _

/-- Each leading word contributes the product of the second absolute moments of the
row-to-column entries it visits. -/
theorem integral_prod_apply_mul_star_apply_of_isLeadingBipartiteWord
    [DecidableEq p] [DecidableEq n]
    (hXm : ∀ i j, AEMeasurable (fun ω ↦ X ω i j) P)
    (hindep : iIndepFun (fun ij : p × n ↦ fun ω ↦ X ω ij.1 ij.2) P)
    {u : Fin k → p} {v : Fin k → n} (hw : IsLeadingBipartiteWord u v) :
    (∫ ω, ∏ t, X ω (u t) (v t) * star (X ω (u (finRotate k t)) (v t)) ∂P) =
      ∏ t, ((∫ ω, ‖X ω (u t) (v t)‖ ^ 2 ∂P : ℝ) : 𝕜) := by
  obtain ⟨π, hπ, _⟩ := hw.existsUnique_perm
  simp only [bipartiteEdge_inl, bipartiteEdge_inr, Prod.mk.injEq] at hπ
  have hreindex (ω : Ω) :
      (∏ t, X ω (u t) (v t) * star (X ω (u (finRotate k t)) (v t))) =
        ∏ t, X ω (u t) (v t) * star (X ω (u t) (v t)) := by
    simp only [prod_mul_distrib]
    congr 1
    exact (Fintype.prod_equiv π _ _ fun t ↦ by rw [(hπ t).1, (hπ t).2])
  simp_rw [hreindex]
  have hInj : Injective (fun t : Fin k ↦ (u t, v t)) := by
    intro i j hij
    apply hw.injective_bipartiteEdge.1
    simpa only [Function.comp_apply, bipartiteEdge_inl] using hij
  rw [(hindep.precomp hInj).integral_fun_prod_comp (fun t ↦ hXm (u t) (v t))
    (f := fun _ z ↦ z * star z)
      (fun _ ↦ (continuous_id.mul continuous_star).aestronglyMeasurable)]
  simp only [RCLike.star_def, RCLike.mul_conj, ← RCLike.ofReal_pow, integral_ofReal]

/-- The absolute expectation along a bipartite word of half-length `k > 0` is bounded by a
common upper bound on the absolute `2k`th entry moments. -/
theorem norm_integral_prod_apply_mul_star_apply_le (hk : k ≠ 0)
    (hXk : ∀ i j, MemLp (fun ω ↦ X ω i j) (2 * k) P) {B : ℝ}
    (hB : ∀ i j, ∫ ω, ‖X ω i j‖ ^ (2 * k) ∂P ≤ B) (u : Fin k → p) (v : Fin k → n) :
    ‖∫ ω, ∏ t, X ω (u t) (v t) * star (X ω (u (finRotate k t)) (v t)) ∂P‖ ≤ B := by
  let f : Fin k ⊕ Fin k → Ω → 𝕜 := Sum.elim (fun t ω ↦ X ω (u t) (v t))
    (fun t ω ↦ star (X ω (u (finRotate k t)) (v t)))
  have hcard : Fintype.card (Fin k ⊕ Fin k) = 2 * k := by
    simp [two_mul]
  have hentry (i j) : Integrable (fun ω ↦ ‖X ω i j‖ ^ (2 * k)) P :=
    MemLp.integrable_norm_pow
      (by simpa only [Nat.cast_mul, Nat.cast_ofNat] using hXk i j) (by omega)
  have hmoment (t) : Integrable (fun ω ↦ ‖f t ω‖ ^ (2 * k)) P := by
    cases t <;> simpa [f] using hentry _ _
  have hbound (t) : ∫ ω, ‖f t ω‖ ^ (2 * k) ∂P ≤ B := by
    cases t <;> simpa [f] using hB _ _
  have hprod (ω : Ω) :
      (∏ t, X ω (u t) (v t) * star (X ω (u (finRotate k t)) (v t))) = ∏ t, f t ω := by
    simp [f, Fintype.prod_sum_type, prod_mul_distrib]
  have : Nonempty (Fin k ⊕ Fin k) := ⟨.inl ⟨0, Nat.pos_of_ne_zero hk⟩⟩
  simp_rw [hprod]
  calc
    _ ≤ ((2 * k : ℕ) : ℝ)⁻¹ * ∑ t, ∫ ω, ‖f t ω‖ ^ (2 * k) ∂P := by
      simpa only [card_univ, hcard] using
        norm_integral_prod_le_inv_card_mul_sum_integral_norm_pow f univ_nonempty
          (by simpa only [card_univ, hcard] using fun t (_ : t ∈ univ) ↦ hmoment t)
    _ ≤ ((2 * k : ℕ) : ℝ)⁻¹ * ∑ _t : Fin k ⊕ Fin k, B :=
      mul_le_mul_of_nonneg_left (sum_le_sum fun t _ ↦ hbound t) (by positivity)
    _ = B := by
      have h2k : ((2 * k : ℕ) : ℝ) ≠ 0 := by exact_mod_cast Nat.mul_ne_zero (by decide) hk
      rw [sum_const, card_univ, hcard, nsmul_eq_mul, ← mul_assoc, inv_mul_cancel₀ h2k, one_mul]

variable [Fintype p] [DecidableEq p] [Fintype n] [DecidableEq n]

/-- The expected trace of the `k`th power of a sample covariance, for centred independent
entries with unit second absolute moment, differs from the leading-word count times
`n⁻ᵏ` by at most `n⁻ᵏ p max(p,n)^(k-1) k^(2k+1) B`, where `B` bounds the `2k`th absolute entry
moments. Here `k > 0`, and labels are counted with their row and column dimensions. -/
theorem norm_integral_trace_sampleCovariance_pow_sub_leading_le (hk : k ≠ 0)
    (hindep : iIndepFun (fun ij : p × n ↦ fun ω ↦ X ω ij.1 ij.2) P)
    (hX : ∀ i j, ∫ ω, X ω i j ∂P = 0)
    (hXk : ∀ i j, MemLp (fun ω ↦ X ω i j) (2 * k) P)
    (hX₂ : ∀ i j, ∫ ω, ‖X ω i j‖ ^ 2 ∂P = 1) {B : ℝ≥0}
    (hB : ∀ i j, ∫ ω, ‖X ω i j‖ ^ (2 * k) ∂P ≤ B) :
    ‖(∫ ω, ((X ω).sampleCovariance ^ k).trace ∂P) - (Fintype.card n : 𝕜)⁻¹ ^ k *
      (Nat.card {w : (Fin k → p) × (Fin k → n) // IsLeadingBipartiteWord w.1 w.2} : 𝕜)‖ ≤
      (Fintype.card n : ℝ)⁻¹ ^ k * (Fintype.card p *
        max (Fintype.card p) (Fintype.card n) ^ (k - 1) * k ^ (2 * k + 1) : ℕ) * B := by
  classical
  let f (w : (Fin k → p) × (Fin k → n)) : 𝕜 :=
    ∫ ω, ∏ t, X ω (w.1 t) (w.2 t) * star (X ω (w.1 (finRotate k t)) (w.2 t)) ∂P
  let S : Finset ((Fin k → p) × (Fin k → n)) :=
    {w | ∀ a, ∃ b ≠ a, bipartiteEdge w.1 w.2 b = bipartiteEdge w.1 w.2 a}
  let L : Finset ((Fin k → p) × (Fin k → n)) := {w | IsLeadingBipartiteWord w.1 w.2}
  have hLS : L ⊆ S := fun w hw ↦ mem_filter.mpr ⟨mem_univ _,
    (isLeadingBipartiteWord_iff.mp (mem_filter.mp hw).2).1⟩
  have htrace : (∫ ω, ((X ω).sampleCovariance ^ k).trace ∂P) =
      (Fintype.card n : 𝕜)⁻¹ ^ k * ∑ w ∈ S, f w := by
    rw [integral_trace_sampleCovariance_pow hindep hX hk hXk]
    simp only [S, sum_filter, Fintype.sum_prod_type, f]
  have hleading : ∑ w ∈ L, f w =
      (Nat.card {w : (Fin k → p) × (Fin k → n) // IsLeadingBipartiteWord w.1 w.2} : 𝕜) := by
    rw [sum_congr rfl (g := fun _ ↦ 1) fun w hw ↦ by
      dsimp only [f]
      rw [integral_prod_apply_mul_star_apply_of_isLeadingBipartiteWord
        (fun i j ↦ (hXk i j).aestronglyMeasurable.aemeasurable) hindep (mem_filter.mp hw).2]
      simp only [hX₂, RCLike.ofReal_one, prod_const_one]]
    rw [sum_const, nsmul_one, Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hcount := card_bipartiteWord_le hk (S \ L) fun w hw ↦ by
    obtain ⟨hS, hL⟩ := mem_sdiff.mp hw
    have hS' := (mem_filter.mp hS).2
    have hv := card_image_add_card_image_le_add_one_of_no_singleton_edge hS'
    have hne : #(univ.image w.1) + #(univ.image w.2) ≠ k + 1 := fun he ↦
      hL (mem_filter.mpr ⟨mem_univ _, isLeadingBipartiteWord_iff.mpr ⟨hS', he⟩⟩)
    omega
  rw [htrace, ← hleading, ← mul_sub, ← sum_sdiff hLS, add_sub_cancel_right,
    norm_mul, norm_pow, norm_inv, RCLike.norm_natCast, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  calc
    _ ≤ ∑ w ∈ S \ L, ‖f w‖ := norm_sum_le _ _
    _ ≤ ∑ _w ∈ S \ L, (B : ℝ) := by
      apply sum_le_sum
      intro w _
      exact norm_integral_prod_apply_mul_star_apply_le hk hXk hB w.1 w.2
    _ = (#(S \ L) : ℝ) * B := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hcount) B.coe_nonneg

end TauCeti.Probability
