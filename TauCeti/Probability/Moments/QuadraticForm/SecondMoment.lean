/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Matrix.MeasurableSpace
public import TauCeti.Probability.Independence.Integration
public import TauCeti.Probability.Moments.SampleMean
public import TauCeti.Probability.Moments.CenteredTruncation
public import TauCeti.Analysis.Matrix.L2OpNorm
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import TauCeti.Analysis.Matrix.DotProduct

/-!
# Second-moment bounds for independent quadratic forms

Square-integrable quadratic monomials on distinct unordered pairs of centered independent
coordinates are orthogonal for the integrated real inner product. For the off-diagonal
quadratic form, the coordinate second moments suffice for square integrability.
The diagonal contribution is a sum of pairwise independent centered squares. Truncating
those squares bounds their fluctuation by the cutoff and the discarded second moments.
The two estimates give a mean absolute bound for a quadratic form after subtracting its mean.
For independent random coefficients, the centering holds the coefficient matrix fixed.

## References

* Z. D. Bai and J. W. Silverstein, *Spectral Analysis of Large Dimensional Random Matrices*,
  second edition, Appendix B, Lemma B.26.
-/

public section

open MeasureTheory Matrix Finset
open scoped InnerProductSpace NNReal ENNReal Matrix.Norms.L2Operator

namespace ProbabilityTheory.iIndepFun

variable {Ω ι 𝕜 : Type*} [MeasurableSpace Ω] [Fintype ι] [RCLike 𝕜]
  {P : Measure Ω} {X : ι → Ω → 𝕜}

omit [Fintype ι] in
/-- Square-integrable quadratic monomials on distinct unordered pairs of centered
independent coordinates have zero integrated real inner product. -/
theorem integral_real_inner_star_mul_eq_zero_of_distinct_pairs {i j k l : ι}
    (hX : iIndepFun (fun d : ({i, j, k, l} : Set ι) ↦ X d) P)
    (hm : ∀ d ∈ ({i, j, k, l} : Set ι), AEMeasurable (X d) P)
    (hc : ∀ d ∈ ({i, j, k, l} : Set ι), ∫ ω, X d ω ∂P = 0)
    (hij : i ≠ j) (hkl : k ≠ l)
    (hne : (i, j) ≠ (k, l)) (hswap : (i, j) ≠ (l, k)) (a b : 𝕜)
    (hLp : MemLp (fun ω ↦ a * (star (X i ω) * X j ω)) 2 P)
    (hLp' : MemLp (fun ω ↦ b * (star (X k ω) * X l ω)) 2 P) :
    (∫ ω, ⟪a * (star (X i ω) * X j ω), b * (star (X k ω) * X l ω)⟫_ℝ ∂P) = 0 := by
  classical
  let e : Fin 4 → ι := ![i, j, k, l]
  have he_mem (c : Fin 4) : e c ∈ ({i, j, k, l} : Set ι) := by
    fin_cases c <;> simp [e]
  let e' (c : Fin 4) : ({i, j, k, l} : Set ι) := ⟨e c, he_mem c⟩
  let f : Fin 4 → 𝕜 → 𝕜 := ![id, star, star, id]
  have hf (a : Fin 4) : Measurable (f a) := by
    fin_cases a <;> first | exact continuous_star.measurable | exact measurable_id
  have hs : i ≠ k ∧ i ≠ l ∨ j ≠ k ∧ j ≠ l ∨ k ≠ i ∧ k ≠ j ∨ l ≠ i ∧ l ≠ j := by
    grind
  have he : ∃ a : Fin 4, ∀ b, e b = e a → b = a := by
    rcases hs with h | h | h | h
    · exact ⟨0, by intro b; fin_cases b <;> simp [e, hij.symm, h.1.symm, h.2.symm]⟩
    · exact ⟨1, by intro b; fin_cases b <;> simp [e, hij, h.1.symm, h.2.symm]⟩
    · exact ⟨2, by intro b; fin_cases b <;> simp [e, h.1.symm, h.2.symm, hkl.symm]⟩
    · exact ⟨3, by intro b; fin_cases b <;> simp [e, h.1.symm, h.2.symm, hkl]⟩
  obtain ⟨c, hc'⟩ := he
  have hzero : ∫ ω, f c (X (e c) ω) ∂P = 0 := by
    have hh : ∫ ω, star (X (e c) ω) ∂P = 0 := by
      simp only [RCLike.star_def, integral_conj, hc _ (he_mem c), map_zero]
    fin_cases c <;> first | exact hh | exact hc _ (he_mem _)
  have hprod : (∫ ω, X i ω * star (X j ω) * (star (X k ω) * X l ω) ∂P) = 0 := by
    simpa [e', e, f, Fin.prod_univ_succ, mul_assoc] using
      hX.integral_fun_prod_comp_eq_zero_of_singleton_fiber univ e' (fun d _ ↦ hm d d.property)
        (fun k _ ↦ (hf k).aestronglyMeasurable) (mem_univ c)
        (fun b _ h ↦ hc' b (congrArg Subtype.val h)) hzero
  have heq (ω : Ω) :
      ⟪a * (star (X i ω) * X j ω), b * (star (X k ω) * X l ω)⟫_ℝ =
        RCLike.re ((star a * b) * (X i ω * star (X j ω) * (star (X k ω) * X l ω))) := by
    simp only [real_inner_eq_re_inner (𝕜 := 𝕜), RCLike.inner_apply, map_mul, RCLike.star_def,
      starRingEnd_self_apply]
    congr 1
    ring
  have hint := hLp.integrable_inner (𝕜 := 𝕜) hLp'
  simp only [RCLike.inner_apply, RCLike.star_def, map_mul] at hint
  have hint' : Integrable (fun ω ↦
      (star a * b) * (X i ω * star (X j ω) * (star (X k ω) * X l ω))) P :=
    hint.congr (.of_forall fun ω ↦ by simp; ring)
  simp_rw [heq]
  rw [integral_re hint', integral_const_mul, hprod, mul_zero,
    map_zero]

private theorem memLp_two_const_mul_star_mul {U V : Ω → 𝕜} (h : IndepFun U V P)
    (hU : MemLp U 2 P) (hV : MemLp V 2 P) (a : 𝕜) :
    MemLp (fun ω ↦ a * (star (U ω) * V ω)) 2 P :=
  ((h.comp continuous_star.measurable measurable_id).memLp_two_mul hU.star hV).const_mul a

omit [Fintype ι] in
/-- The mean norm of a sum of quadratic monomials on distinct unordered pairs is bounded
by the common second-moment cap times the Euclidean norm of the coefficients. -/
theorem integral_norm_sum_pairs_le {t : Set ι} (hX : iIndepFun (fun i : t ↦ X i) P)
    (hLp : ∀ i : t, MemLp (X i) 2 P) (hc : ∀ i : t, ∫ ω, X i ω ∂P = 0)
    (A : Matrix ι ι 𝕜) (s : Finset (ι × ι)) (ht : ∀ p ∈ s, p.1 ∈ t ∧ p.2 ∈ t)
    (hd : ∀ p ∈ s, p.1 ≠ p.2) (hs : ∀ p ∈ s, p.swap ∉ s) {v : ℝ}
    (hv : ∀ i : t, ∫ ω, ‖X i ω‖ ^ 2 ∂P ≤ v) (hv₀ : 0 ≤ v) :
    (∫ ω, ‖∑ p ∈ s, A p.1 p.2 * (star (X p.1 ω) * X p.2 ω)‖ ∂P) ≤
      v * Real.sqrt (∑ p ∈ s, ‖A p.1 p.2‖ ^ 2) := by
  have : IsProbabilityMeasure P := hX.isProbabilityMeasure
  let Y (p : ι × ι) (ω : Ω) := A p.1 p.2 * (star (X p.1 ω) * X p.2 ω)
  let left (p : ι × ι) (hp : p ∈ s) : t := ⟨p.1, (ht p hp).1⟩
  let right (p : ι × ι) (hp : p ∈ s) : t := ⟨p.2, (ht p hp).2⟩
  have hpind p (hp : p ∈ s) : IndepFun (X (left p hp)) (X (right p hp)) P :=
    hX.indepFun (fun h ↦ hd p hp (congrArg Subtype.val h))
  have hY p (hp : p ∈ s) : MemLp (Y p) 2 P :=
    memLp_two_const_mul_star_mul (hpind p hp) (hLp (left p hp)) (hLp (right p hp)) _
  have heq : (∫ ω, ‖∑ p ∈ s, Y p ω‖ ^ 2 ∂P) = ∑ p ∈ s, ∫ ω, ‖Y p ω‖ ^ 2 ∂P := by
    apply TauCeti.integral_norm_sum_sq_of_pairwise_integral_inner_eq_zero
      (fun i hi j hj ↦ (hY i hi).integrable_inner (hY j hj))
    intro i hi j hj hij
    exact (hX.precomp Subtype.val_injective).integral_real_inner_star_mul_eq_zero_of_distinct_pairs
      (fun k _ ↦ (hLp k).aemeasurable) (fun k _ ↦ hc k)
      (i := left i hi) (j := right i hi) (k := left j hj) (l := right j hj)
      (fun h ↦ hd i hi (congrArg Subtype.val h)) (fun h ↦ hd j hj (congrArg Subtype.val h))
      (fun h ↦ hij (congrArg (Prod.map Subtype.val Subtype.val) h))
      (fun h ↦ hs i hi (by
        have he : i = j.swap := congrArg (Prod.map Subtype.val Subtype.val) h
        rwa [Prod.swap_eq_iff_eq_swap.mpr he])) _ _ (hY i hi) (hY j hj)
  have hsum : MemLp (fun ω ↦ ∑ p ∈ s, Y p ω) 2 P := memLp_finsetSum _ hY
  calc
    _ ≤ Real.sqrt (∫ ω, ‖∑ p ∈ s, Y p ω‖ ^ 2 ∂P) := integral_le_sqrt_integral_sq hsum.norm
    _ ≤ Real.sqrt (v ^ 2 * ∑ p ∈ s, ‖A p.1 p.2‖ ^ 2) := by
      rw [heq, mul_sum]
      apply Real.sqrt_le_sqrt
      apply sum_le_sum
      intro p hp
      have he (ω : Ω) : ‖Y p ω‖ ^ 2 =
          ‖A p.1 p.2‖ ^ 2 * ‖star (X p.1 ω) * X p.2 ω‖ ^ 2 := by
        simp only [Y, norm_mul, mul_pow]
      simp_rw [he, integral_const_mul]
      have hmoment := (hpind p hp).integral_norm_sq_mul
        (hLp (left p hp)).aemeasurable (hLp (right p hp)).aemeasurable
      simp only [norm_mul, norm_star] at hmoment ⊢
      rw [hmoment]
      rw [mul_comm (v ^ 2), sq v]
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul (hv (left p hp)) (hv (right p hp)) (integral_nonneg fun _ ↦ sq_nonneg _) hv₀)
        (sq_nonneg _)
    _ = _ := by rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hv₀]

/-- The off-diagonal part of a quadratic form in centered independent coordinates is
integrable, with mean norm bounded in terms of the Euclidean operator norm. -/
theorem integral_norm_offDiag_le [DecidableEq ι] (hX : iIndepFun X P)
    (hLp : ∀ i, MemLp (X i) 2 P) (hc : ∀ i, ∫ ω, X i ω ∂P = 0)
    (A : Matrix ι ι 𝕜) {v : ℝ} (hv : ∀ i, ∫ ω, ‖X i ω‖ ^ 2 ∂P ≤ v) (hv₀ : 0 ≤ v) :
    let offDiag (ω : Ω) := ∑ p ∈ (univ : Finset ι).offDiag,
      A p.1 p.2 * (star (X p.1 ω) * X p.2 ω)
    Integrable offDiag P ∧
      (∫ ω, ‖offDiag ω‖ ∂P) ≤ 2 * v * (Real.sqrt (Fintype.card ι)) * ‖A‖ := by
  classical
  have := hX.isProbabilityMeasure
  let _ := LinearOrder.lift' (Fintype.equivFin ι) (Fintype.equivFin ι).injective
  let s : Finset (ι × ι) := univ.offDiag
  let Y (p : ι × ι) (ω : Ω) := A p.1 p.2 * (star (X p.1 ω) * X p.2 ω)
  have hd p (hp : p ∈ s) : p.1 ≠ p.2 := (mem_offDiag.mp hp).2.2
  have hX₂ : ∀ p ∈ s, MemLp (Y p) 2 P := fun p hp ↦
    memLp_two_const_mul_star_mul (hX.indepFun (hd p hp)) (hLp p.1) (hLp p.2) _
  have hbound (t : Finset (ι × ι)) (ht : t ⊆ s) (hs : ∀ p ∈ t, p.swap ∉ t) :
      ∫ ω, ‖∑ p ∈ t, Y p ω‖ ∂P ≤ v * (Real.sqrt (Fintype.card ι)) * ‖A‖ := by
    refine ((hX.precomp Subtype.val_injective).integral_norm_sum_pairs_le (t := Set.univ)
      (fun i ↦ hLp i) (fun i ↦ hc i) A t (fun _ _ ↦ by simp) (fun p hp ↦ hd p (ht hp))
      hs (fun i ↦ hv i) hv₀).trans ?_
    have hsum : ∑ p ∈ t, ‖A p.1 p.2‖ ^ 2 ≤ Fintype.card ι * ‖A‖ ^ 2 := by
      calc
        _ ≤ ∑ p ∈ (univ : Finset ι) ×ˢ (univ : Finset ι), ‖A p.1 p.2‖ ^ 2 :=
          sum_le_sum_of_subset_of_nonneg (fun _ _ ↦ by simp) (fun _ _ _ ↦ sq_nonneg _)
        _ ≤ _ := (sum_product _ _ (fun p : ι × ι ↦ ‖A p.1 p.2‖ ^ 2)).trans_le
          (Matrix.sum_sum_norm_sq_le_card_mul_l2_opNorm_sq A)
    calc
      _ ≤ v * Real.sqrt (Fintype.card ι * ‖A‖ ^ 2) :=
        mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hsum) hv₀
      _ = _ := by rw [Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq (norm_nonneg _), ← mul_assoc]
  let t := s.filter (fun p ↦ p.1 < p.2)
  let u := s.filter (fun p ↦ ¬p.1 < p.2)
  have ht : t ⊆ s := filter_subset _ _
  have hu : u ⊆ s := filter_subset _ _
  have ht' : ∀ p ∈ t, p.swap ∉ t := fun _ hp hswap ↦
    (mem_filter.mp hp).2.not_gt (mem_filter.mp hswap).2
  have hu' : ∀ p ∈ u, p.swap ∉ u := by
    intro p hp hswap
    exact hd p (hu hp) (le_antisymm (le_of_not_gt (mem_filter.mp hswap).2)
      (le_of_not_gt (mem_filter.mp hp).2))
  have hint (t : Finset (ι × ι)) (ht : t ⊆ s) :
      Integrable (fun ω ↦ ∑ p ∈ t, Y p ω) P :=
    (memLp_finsetSum t fun p hp ↦ hX₂ p (ht hp)).integrable one_le_two
  have hsplit (ω : Ω) : (∑ p ∈ s, Y p ω) = (∑ p ∈ t, Y p ω) + ∑ p ∈ u, Y p ω :=
    (sum_filter_add_sum_filter_not s (fun p ↦ p.1 < p.2) (fun p ↦ Y p ω)).symm
  refine ⟨hint s Subset.rfl, ?_⟩
  -- Work with the named sum to match the splitting identity under the integral.
  change (∫ ω, ‖∑ p ∈ s, Y p ω‖ ∂P) ≤ _
  simp_rw [hsplit]
  have ht₁ := hint t ht
  have hu₁ := hint u hu
  have htriangle := lpNorm_add_le (memLp_one_iff_integrable.mpr ht₁) le_rfl
    (g := fun ω ↦ ∑ p ∈ u, Y p ω)
  rw [lpNorm_one_eq_integral_norm (ht₁.add hu₁).aestronglyMeasurable,
    lpNorm_one_eq_integral_norm ht₁.aestronglyMeasurable,
    lpNorm_one_eq_integral_norm hu₁.aestronglyMeasurable] at htriangle
  exact htriangle.trans ((add_le_add (hbound t ht ht') (hbound u hu hu')).trans_eq (by ring))

/-- Mean-norm bound for a weighted sum of centered squares of pairwise independent variables.
The cutoff controls the retained part and the tail integrals bound the discarded part. -/
theorem _root_.TauCeti.integral_norm_weighted_centeredSquares_le [IsProbabilityMeasure P]
    (hX : Pairwise fun i j ↦ IndepFun (X i) (X j) P)
    (hLp : ∀ i, MemLp (X i) 2 P) (a : ι → 𝕜) {C v : ℝ} (hC : 0 ≤ C)
    (ha : ∀ i, ‖a i‖ ≤ C) (hv : ∀ i, ∫ ω, ‖X i ω‖ ^ 2 ∂P ≤ v) (r : ℝ≥0) :
    (∫ ω, ‖∑ i, a i * ((‖X i ω‖ ^ 2 - ∫ y, ‖X i y‖ ^ 2 ∂P : ℝ) : 𝕜)‖ ∂P) ≤
      C * (Real.sqrt ((r : ℝ) * Fintype.card ι * v) +
        2 * ∑ i, ∫ ω, {ω | (r : ℝ) < ‖X i ω‖ ^ 2}.indicator (fun ω ↦ ‖X i ω‖ ^ 2) ω ∂P) := by
  classical
  let W (i : ι) (ω : Ω) := ‖X i ω‖ ^ 2
  let T (i : ι) := TauCeti.Probability.centeredTruncation (W i) P r
  let Y (i : ι) (ω : Ω) := a i * (T i ω : 𝕜)
  let D (i : ι) (ω : Ω) := W i ω - (∫ y, W i y ∂P) - T i ω
  have hW (i : ι) : Integrable (W i) P :=
    (memLp_two_iff_integrable_sq_norm (hLp i).aestronglyMeasurable).mp (hLp i)
  have hY (i : ι) : MemLp (Y i) 2 P :=
    ((hW i).aestronglyMeasurable.memLp_centeredTruncation r).ofReal.const_mul _
  have hYi : Pairwise fun i j ↦ IndepFun (Y i) (Y j) P := by
    intro i j hij
    have h := (hX hij).comp (φ := fun z : 𝕜 ↦ ‖z‖ ^ 2) (ψ := fun z : 𝕜 ↦ ‖z‖ ^ 2)
      (by fun_prop) (by fun_prop)
    exact (h.centeredTruncation r r).comp (φ := fun z : ℝ ↦ a i * (z : 𝕜))
      (ψ := fun z : ℝ ↦ a j * (z : 𝕜)) (by fun_prop) (by fun_prop)
  have hmean (i : ι) : ∫ ω, Y i ω ∂P = 0 := by
    simp only [Y, integral_const_mul, integral_ofReal, T,
      (hW i).aestronglyMeasurable.integral_centeredTruncation, RCLike.ofReal_zero, mul_zero]
  have hsmall : (∫ ω, ‖∑ i, Y i ω‖ ∂P) ≤
      C * Real.sqrt ((r : ℝ) * Fintype.card ι * v) := by
    refine (TauCeti.integral_norm_sum_le_of_pairwise_indepFun (s := univ)
      (fun i _ ↦ hY i) (fun i _ ↦ hmean i) (fun _ _ _ _ hij ↦ hYi hij)
      (v := C ^ 2 * ((r : ℝ) * v)) (fun i _ ↦ ?_)).trans_eq ?_
    · simp only [Y, norm_mul, RCLike.norm_ofReal, mul_pow, integral_const_mul]
      exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) (ha i) 2)
        (((hW i).integral_norm_centeredTruncation_sq_le_mul r).trans
          (mul_le_mul_of_nonneg_left
            (by simpa only [W, Real.norm_of_nonneg (sq_nonneg _)] using hv i) r.coe_nonneg))
        (integral_nonneg fun _ ↦ sq_nonneg _) (sq_nonneg _)
    · rw [card_univ]
      calc
        _ = Real.sqrt (C ^ 2 * ((r : ℝ) * Fintype.card ι * v)) := by congr 1; ring
        _ = _ := by rw [Real.sqrt_mul (sq_nonneg C), Real.sqrt_sq hC]
  have hdiscard := TauCeti.Probability.integral_norm_sum_mul_centeredTruncation_residual_le
    hW a hC ha r
  have hsum (ω : Ω) : (∑ i, a i * ((‖X i ω‖ ^ 2 - ∫ y, ‖X i y‖ ^ 2 ∂P : ℝ) : 𝕜)) =
      (∑ i, Y i ω) + ∑ i, a i * (D i ω : 𝕜) := by
    rw [← sum_add_distrib]
    refine sum_congr rfl fun i _ ↦ ?_
    simp only [Y, D, W, RCLike.ofReal_sub]
    ring
  simp_rw [hsum, mul_add]
  have ht := (memLp_finsetSum univ fun i _ ↦ hY i).integrable one_le_two
  have htriangle := lpNorm_add_le (memLp_one_iff_integrable.mpr ht) le_rfl
    (g := fun ω ↦ ∑ i, a i * (D i ω : 𝕜))
  rw [lpNorm_one_eq_integral_norm (ht.add hdiscard.1).aestronglyMeasurable,
    lpNorm_one_eq_integral_norm ht.aestronglyMeasurable,
    lpNorm_one_eq_integral_norm hdiscard.1.aestronglyMeasurable] at htriangle
  refine htriangle.trans (add_le_add hsmall ?_)
  simpa only [W, Real.norm_of_nonneg (sq_nonneg _)] using hdiscard.2

/-- Mean absolute error of a quadratic form in centered independent coordinates,
relative to its diagonal second-moment sum. The cutoff applies to squared absolute values.
The bound uses only second moments and includes the contribution of the discarded tails. -/
theorem integral_norm_star_dotProduct_mulVec_sub_sum_diag_le [DecidableEq ι]
    (hX : iIndepFun X P) (hLp : ∀ i, MemLp (X i) 2 P) (hc : ∀ i, ∫ ω, X i ω ∂P = 0)
    (A : Matrix ι ι 𝕜) {v : ℝ} (hv : ∀ i, ∫ ω, ‖X i ω‖ ^ 2 ∂P ≤ v) (r : ℝ≥0) :
    (∫ ω, ‖star (fun i ↦ X i ω) ⬝ᵥ A *ᵥ (fun i ↦ X i ω) -
      ∑ i, A i i * ((∫ y, ‖X i y‖ ^ 2 ∂P : ℝ) : 𝕜)‖ ∂P) ≤
      ‖A‖ * (2 * v * Real.sqrt (Fintype.card ι) + Real.sqrt ((r : ℝ) * Fintype.card ι * v) +
        2 * ∑ i, ∫ ω, {ω | (r : ℝ) < ‖X i ω‖ ^ 2}.indicator (fun ω ↦ ‖X i ω‖ ^ 2) ω ∂P) := by
  cases isEmpty_or_nonempty ι
  · simp [dotProduct_of_isEmpty]
  obtain ⟨i⟩ := ‹Nonempty ι›
  have hv₀ : 0 ≤ v := (integral_nonneg fun ω ↦ sq_nonneg ‖X i ω‖).trans (hv i)
  have := hX.isProbabilityMeasure
  let m (i : ι) : ℝ := ∫ ω, ‖X i ω‖ ^ 2 ∂P
  have hA := hX.integral_norm_offDiag_le hLp hc A hv hv₀
  have hD := TauCeti.integral_norm_weighted_centeredSquares_le
    (fun _ _ hij ↦ hX.indepFun hij) hLp (fun i ↦ A i i) (norm_nonneg A)
    (fun i ↦ A.norm_apply_le_l2_opNorm i i) hv r
  have hW (i : ι) : Integrable (fun ω ↦ ‖X i ω‖ ^ 2) P :=
    (memLp_two_iff_integrable_sq_norm (hLp i).aestronglyMeasurable).mp (hLp i)
  have hDi : Integrable (fun ω ↦ ∑ i, A i i * ((‖X i ω‖ ^ 2 - m i : ℝ) : 𝕜)) P :=
    integrable_finsetSum _ fun i _ ↦
      ((RCLike.ofRealCLM (K := 𝕜)).integrable_comp ((hW i).sub (integrable_const _))).const_mul _
  simp_rw [A.star_dotProduct_mulVec_sub_sum_diag_eq]
  have htriangle := lpNorm_add_le (memLp_one_iff_integrable.mpr hA.1) le_rfl
    (g := fun ω ↦ ∑ i, A i i * ((‖X i ω‖ ^ 2 - m i : ℝ) : 𝕜))
  rw [lpNorm_one_eq_integral_norm (hA.1.add hDi).aestronglyMeasurable,
    lpNorm_one_eq_integral_norm hA.1.aestronglyMeasurable,
    lpNorm_one_eq_integral_norm hDi.aestronglyMeasurable] at htriangle
  exact htriangle.trans ((add_le_add hA.2 hD).trans_eq (by ring))

/-- The mean absolute quadratic-form bound for an independent random coefficient matrix
with integrable Euclidean operator norm. The quadratic form is integrable and is centered
by the mean obtained with the coefficient matrix held fixed. -/
theorem integral_norm_star_dotProduct_mulVec_sub_sum_diag_le_of_indepFun [DecidableEq ι]
    (hX : iIndepFun X P) (hLp : ∀ i, MemLp (X i) 2 P) (hc : ∀ i, ∫ ω, X i ω ∂P = 0)
    {A : Ω → Matrix ι ι 𝕜} (hA : AEMeasurable A P) (hind : IndepFun A (fun ω i ↦ X i ω) P)
    (hAnorm : Integrable (fun ω ↦ ‖A ω‖) P)
    {v : ℝ} (hv : ∀ i, ∫ ω, ‖X i ω‖ ^ 2 ∂P ≤ v) (r : ℝ≥0) :
    let Q := fun ω ↦ star (fun i ↦ X i ω) ⬝ᵥ A ω *ᵥ (fun i ↦ X i ω) -
      ∑ i, A ω i i * ((∫ y, ‖X i y‖ ^ 2 ∂P : ℝ) : 𝕜)
    Integrable Q P ∧ (∫ ω, ‖Q ω‖ ∂P) ≤ (∫ ω, ‖A ω‖ ∂P) *
      (2 * v * Real.sqrt (Fintype.card ι) + Real.sqrt ((r : ℝ) * Fintype.card ι * v) +
        2 * ∑ i, ∫ ω, {ω | (r : ℝ) < ‖X i ω‖ ^ 2}.indicator (fun ω ↦ ‖X i ω‖ ^ 2) ω ∂P) := by
  intro _
  have : IsProbabilityMeasure P := hX.isProbabilityMeasure
  let Z (ω : Ω) (i : ι) := X i ω
  have hZ : AEMeasurable Z P := aemeasurable_pi_iff.mpr fun i ↦ (hLp i).aemeasurable
  let m (i : ι) : ℝ := ∫ ω, ‖X i ω‖ ^ 2 ∂P
  let f (p : Matrix ι ι 𝕜 × (ι → 𝕜)) :=
    star p.2 ⬝ᵥ p.1 *ᵥ p.2 - ∑ i, p.1 i i * (m i : 𝕜)
  have hf : Measurable f := by
    simp only [f, dotProduct, mulVec, Pi.star_apply]
    fun_prop
  let K := 2 * v * Real.sqrt (Fintype.card ι) + Real.sqrt ((r : ℝ) * Fintype.card ι * v) +
    2 * ∑ i, ∫ ω, {ω | (r : ℝ) < ‖X i ω‖ ^ 2}.indicator (fun ω ↦ ‖X i ω‖ ^ 2) ω ∂P
  let g (B : Matrix ι ι 𝕜) := ‖B‖ * K
  have hg : Measurable g := measurable_norm.mul_const _
  have hgi : Integrable g (P.map A) :=
    (integrable_map_measure hg.aestronglyMeasurable hA).2 (hAnorm.mul_const _)
  have h := hind.integral_norm_comp_prodMk_le_of_sections hA hZ hf hgi (.of_forall fun B ↦ by
    have hint := (TauCeti.integral_star_dotProduct_mulVec_eq_sum_diag_of_pairwise_indepFun
      (fun _ _ hij ↦ hX.indepFun hij) (fun i ↦ (hLp i).integrable one_le_two)
      (fun i ↦ (memLp_two_iff_integrable_sq_norm (hLp i).aestronglyMeasurable).1 (hLp i))
      hc B).1
    exact ⟨hint.sub (integrable_const (∑ i, B i i * (m i : 𝕜))),
      hX.integral_norm_star_dotProduct_mulVec_sub_sum_diag_le hLp hc B hv r⟩)
  rw [integral_map hA hg.aestronglyMeasurable, integral_mul_const] at h
  exact h

end ProbabilityTheory.iIndepFun
