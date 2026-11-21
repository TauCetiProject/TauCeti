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

/-!
# Second-moment bounds for independent quadratic forms

Products associated to distinct unordered pairs of centered independent coordinates are
orthogonal in mean square. The off-diagonal quadratic form thus needs only second moments.
The diagonal contribution is a sum of independent centered squares. Truncating those squares
bounds their fluctuation by the cutoff and the discarded second moments. Together these
estimates give a mean absolute bound for the error of a quadratic form about its mean.

## References

* Z. D. Bai and J. W. Silverstein, *Spectral Analysis of Large Dimensional Random Matrices*,
  second edition, Appendix B, Lemma B.26.
-/

public section

open MeasureTheory Matrix Finset
open scoped InnerProductSpace NNReal ENNReal Matrix.Norms.L2Operator

namespace ProbabilityTheory.iIndepFun

variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
  {P : Measure Ω} {X : ι → Ω → ℂ}

omit [Fintype ι] in
private theorem integral_inner_mul_eq_zero (hX : iIndepFun X P)
    (hm : ∀ i, AEMeasurable (X i) P) (hc : ∀ i, ∫ ω, X i ω ∂P = 0)
    {i j k l : ι} (hij : i ≠ j) (hkl : k ≠ l)
    (hne : (i, j) ≠ (k, l)) (hswap : (i, j) ≠ (l, k)) (a b : ℂ)
    (hLp : MemLp (fun ω ↦ a * (star (X i ω) * X j ω)) 2 P)
    (hLp' : MemLp (fun ω ↦ b * (star (X k ω) * X l ω)) 2 P) :
    (∫ ω, ⟪a * (star (X i ω) * X j ω), b * (star (X k ω) * X l ω)⟫_ℝ ∂P) = 0 := by
  let e : Fin 4 → ι := ![i, j, k, l]
  let f : Fin 4 → ℂ → ℂ := ![id, star, star, id]
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
    have hh (d : ι) : ∫ ω, star (X d ω) ∂P = 0 := by
      simp only [Complex.star_def, integral_conj, hc, map_zero]
    fin_cases c <;> first | exact hh _ | exact hc _
  have hprod : (∫ ω, X i ω * star (X j ω) * (star (X k ω) * X l ω) ∂P) = 0 := by
    simpa [e, f, Fin.prod_univ_succ, mul_assoc] using
      hX.integral_fun_prod_comp_eq_zero_of_singleton_fiber hm e
        (fun k ↦ (hf k).aestronglyMeasurable) hc' hzero
  have heq (ω : Ω) :
      ⟪a * (star (X i ω) * X j ω), b * (star (X k ω) * X l ω)⟫_ℝ =
        ((star a * b) * (X i ω * star (X j ω) * (star (X k ω) * X l ω))).re := by
    simp only [real_inner_eq_re_inner (𝕜 := ℂ), RCLike.inner_apply, map_mul, Complex.star_def,
      starRingEnd_self_apply, RCLike.re_eq_complex_re]
    congr 1
    ring
  have hint := hLp.integrable_inner (𝕜 := ℂ) hLp'
  simp only [RCLike.inner_apply, Complex.star_def, map_mul] at hint
  have hint' : Integrable (fun ω ↦
      (star a * b) * (X i ω * star (X j ω) * (star (X k ω) * X l ω))) P :=
    hint.congr (.of_forall fun ω ↦ by simp; ring)
  simp_rw [heq]
  rw [← RCLike.re_eq_complex_re, integral_re hint', integral_const_mul, hprod, mul_zero,
    map_zero]

omit [Fintype ι] in
private theorem integral_norm_sq_star_mul (hX : iIndepFun X P)
    {i j : ι} (hij : i ≠ j) (hi : MemLp (X i) 2 P) (hj : MemLp (X j) 2 P) :
    MemLp (fun ω ↦ star (X i ω) * X j ω) 2 P ∧
      (∫ ω, ‖star (X i ω) * X j ω‖ ^ 2 ∂P) =
        (∫ ω, ‖X i ω‖ ^ 2 ∂P) * (∫ ω, ‖X j ω‖ ^ 2 ∂P) := by
  have h := (hX.indepFun hij).comp
    (φ := fun z : ℂ ↦ ‖z‖ ^ 2) (ψ := fun z : ℂ ↦ ‖z‖ ^ 2)
    (by fun_prop) (by fun_prop)
  have hi' := (memLp_two_iff_integrable_sq_norm hi.aestronglyMeasurable).1 hi
  have hj' := (memLp_two_iff_integrable_sq_norm hj.aestronglyMeasurable).1 hj
  refine ⟨(memLp_two_iff_integrable_sq_norm ?_).2 ?_, ?_⟩
  · exact (continuous_star.comp_aestronglyMeasurable hi.aestronglyMeasurable).mul
      hj.aestronglyMeasurable
  · simpa only [norm_mul, norm_star, mul_pow, Function.comp_apply] using
      (h.integrable_mul hi' hj').congr
      (.of_forall fun x ↦ Pi.mul_apply _ _ x)
  · simpa only [norm_mul, norm_star, mul_pow, Function.comp_apply, Pi.mul_apply] using
      h.integral_fun_mul_eq_mul_integral hi'.1 hj'.1

omit [Fintype ι] in
private theorem integral_norm_sum_pairs_le (hX : iIndepFun X P)
    (hLp : ∀ i, MemLp (X i) 2 P) (hc : ∀ i, ∫ ω, X i ω ∂P = 0)
    (A : Matrix ι ι ℂ) (s : Finset (ι × ι))
    (hd : ∀ p ∈ s, p.1 ≠ p.2) (hs : ∀ p ∈ s, p.swap ∉ s) {v : ℝ}
    (hv : ∀ i, ∫ ω, ‖X i ω‖ ^ 2 ∂P ≤ v) (hv₀ : 0 ≤ v) :
    (∫ ω, ‖∑ p ∈ s, A p.1 p.2 * (star (X p.1 ω) * X p.2 ω)‖ ∂P) ≤
      v * Real.sqrt (∑ p ∈ s, ‖A p.1 p.2‖ ^ 2) := by
  have : IsProbabilityMeasure P := hX.isProbabilityMeasure
  let Y (p : ι × ι) (ω : Ω) := A p.1 p.2 * (star (X p.1 ω) * X p.2 ω)
  have hpart p (hp : p ∈ s) := hX.integral_norm_sq_star_mul (hd p hp) (hLp p.1) (hLp p.2)
  have hY p (hp : p ∈ s) : MemLp (Y p) 2 P := (hpart p hp).1.const_mul _
  have heq : (∫ ω, ‖∑ p ∈ s, Y p ω‖ ^ 2 ∂P) = ∑ p ∈ s, ∫ ω, ‖Y p ω‖ ^ 2 ∂P :=
    TauCeti.integral_norm_sum_sq_of_pairwise_integral_inner_eq_zero
      (fun i hi j hj ↦ (hY i hi).integrable_inner (hY j hj)) (fun i hi j hj hij ↦
        hX.integral_inner_mul_eq_zero (fun k ↦ (hLp k).aemeasurable) hc (hd i hi) (hd j hj)
          hij (fun h ↦ hs j hj ((show i = j.swap from h) ▸ hi)) _ _ (hY i hi) (hY j hj))
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
      simp_rw [he, integral_const_mul, (hpart p hp).2]
      rw [mul_comm (v ^ 2), sq v]
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul (hv p.1) (hv p.2) (integral_nonneg fun _ ↦ sq_nonneg _) hv₀)
        (sq_nonneg _)
    _ = _ := by rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hv₀]

private theorem integral_norm_offDiag_le [DecidableEq ι] (hX : iIndepFun X P)
    (hLp : ∀ i, MemLp (X i) 2 P) (hc : ∀ i, ∫ ω, X i ω ∂P = 0)
    (A : Matrix ι ι ℂ) {v : ℝ} (hv : ∀ i, ∫ ω, ‖X i ω‖ ^ 2 ∂P ≤ v) (hv₀ : 0 ≤ v) :
    (∫ ω, ‖∑ p ∈ (univ : Finset ι).offDiag,
        A p.1 p.2 * (star (X p.1 ω) * X p.2 ω)‖ ∂P) ≤
      2 * v * (Real.sqrt (Fintype.card ι)) * ‖A‖ := by
  classical
  have := hX.isProbabilityMeasure
  let _ := LinearOrder.lift' (Fintype.equivFin ι) (Fintype.equivFin ι).injective
  let s : Finset (ι × ι) := univ.offDiag
  let Y (p : ι × ι) (ω : Ω) := A p.1 p.2 * (star (X p.1 ω) * X p.2 ω)
  have hd p (hp : p ∈ s) : p.1 ≠ p.2 := (mem_offDiag.mp hp).2.2
  have hX₂ : ∀ p ∈ s, MemLp (Y p) 2 P := fun p hp ↦
    (hX.integral_norm_sq_star_mul (hd p hp) (hLp p.1) (hLp p.2)).1.const_mul _
  have hbound (t : Finset (ι × ι)) (ht : t ⊆ s) (hs : ∀ p ∈ t, p.swap ∉ t) :
      ∫ ω, ‖∑ p ∈ t, Y p ω‖ ∂P ≤ v * (Real.sqrt (Fintype.card ι)) * ‖A‖ := by
    refine (hX.integral_norm_sum_pairs_le hLp hc A t (fun p hp ↦ hd p (ht hp)) hs hv hv₀).trans ?_
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
  have ht' : ∀ p ∈ t, p.swap ∉ t := by
    intro p hp hswap
    exact (mem_filter.mp hp).2.not_gt (mem_filter.mp hswap).2
  have hu' : ∀ p ∈ u, p.swap ∉ u := by
    intro p hp hswap
    exact hd p (hu hp) (le_antisymm (le_of_not_gt (mem_filter.mp hswap).2)
      (le_of_not_gt (mem_filter.mp hp).2))
  have hint (t : Finset (ι × ι)) (ht : t ⊆ s) :
      Integrable (fun ω ↦ ∑ p ∈ t, Y p ω) P :=
    (memLp_finsetSum t fun p hp ↦ hX₂ p (ht hp)).integrable one_le_two
  have hsplit (ω : Ω) : (∑ p ∈ s, Y p ω) = (∑ p ∈ t, Y p ω) + ∑ p ∈ u, Y p ω :=
    (sum_filter_add_sum_filter_not s (fun p ↦ p.1 < p.2) (fun p ↦ Y p ω)).symm
  -- Work with the named sum to match the splitting identity under the integral.
  change (∫ ω, ‖∑ p ∈ s, Y p ω‖ ∂P) ≤ _
  simp_rw [hsplit]
  refine (integral_mono ((hint t ht).add (hint u hu)).norm
    ((hint t ht).norm.add (hint u hu).norm) (fun _ ↦ norm_add_le _ _)).trans ?_
  rw [integral_add' (hint t ht).norm (hint u hu).norm]
  exact (add_le_add (hbound t ht ht') (hbound u hu hu')).trans_eq (by ring)

private theorem integral_norm_sum_centeredTruncation_le {Y : ι → Ω → ℂ}
    [IsProbabilityMeasure P] (hY : ∀ i, MemLp (Y i) 2 P)
    (hmean : ∀ i, ∫ ω, Y i ω ∂P = 0) (hYi : Pairwise fun i j ↦ IndepFun (Y i) (Y j) P)
    {C v : ℝ} (hC : 0 ≤ C) (r : ℝ≥0)
    (hbound : ∀ i, ∫ ω, ‖Y i ω‖ ^ 2 ∂P ≤ C ^ 2 * ((r : ℝ) * v)) :
    (∫ ω, ‖∑ i, Y i ω‖ ∂P) ≤ C * Real.sqrt ((r : ℝ) * Fintype.card ι * v) := by
  have hsq := TauCeti.integral_norm_sum_sq_of_pairwise_indepFun (s := univ)
    (fun i _ ↦ hY i) (fun i _ ↦ hmean i) (fun _ _ _ _ hij ↦ hYi hij)
  refine (integral_le_sqrt_integral_sq (memLp_finsetSum univ fun i _ ↦ hY i).norm).trans ?_
  rw [hsq, ← Real.sqrt_sq hC, ← Real.sqrt_mul (sq_nonneg C)]
  apply Real.sqrt_le_sqrt
  calc
    _ ≤ ∑ _i : ι, C ^ 2 * ((r : ℝ) * v) := by
      apply sum_le_sum
      intro i _
      exact hbound i
    _ = _ := by simp only [sum_const, card_univ, nsmul_eq_mul]; ring

private theorem integral_norm_weighted_centeredSquares_le (hX : iIndepFun X P)
    (hLp : ∀ i, MemLp (X i) 2 P) (a : ι → ℂ) {C v : ℝ} (hC : 0 ≤ C)
    (ha : ∀ i, ‖a i‖ ≤ C) (hv : ∀ i, ∫ ω, ‖X i ω‖ ^ 2 ∂P ≤ v) (r : ℝ≥0) :
    (∫ ω, ‖∑ i, a i * ((‖X i ω‖ ^ 2 - ∫ y, ‖X i y‖ ^ 2 ∂P : ℝ) : ℂ)‖ ∂P) ≤
      C * (Real.sqrt ((r : ℝ) * Fintype.card ι * v) +
        2 * ∑ i, ∫ ω, {ω | (r : ℝ) < ‖X i ω‖ ^ 2}.indicator (fun ω ↦ ‖X i ω‖ ^ 2) ω ∂P) := by
  classical
  have := hX.isProbabilityMeasure
  let W (i : ι) (ω : Ω) := ‖X i ω‖ ^ 2
  let T (i : ι) := TauCeti.Probability.centeredTruncation (W i) P r
  let Y (i : ι) (ω : Ω) := a i * (T i ω : ℂ)
  let D (i : ι) (ω : Ω) := W i ω - (∫ y, W i y ∂P) - T i ω
  have hW (i : ι) : Integrable (W i) P :=
    (memLp_two_iff_integrable_sq_norm (hLp i).aestronglyMeasurable).mp (hLp i)
  have hY (i : ι) : MemLp (Y i) 2 P :=
    ((hW i).aestronglyMeasurable.memLp_centeredTruncation r).ofReal.const_mul _
  have hTi : iIndepFun T P :=
    (hX.comp (fun _ z ↦ ‖z‖ ^ 2) (fun _ ↦ by fun_prop)).centeredTruncation (fun _ ↦ r)
  have hYi : iIndepFun Y P :=
    hTi.comp (fun i x ↦ a i * (x : ℂ)) (fun _ ↦ by fun_prop)
  have hmean (i : ι) : ∫ ω, Y i ω ∂P = 0 := by
    simp only [Y, integral_const_mul, integral_complex_ofReal, T,
      (hW i).aestronglyMeasurable.integral_centeredTruncation, Complex.ofReal_zero, mul_zero]
  have hsmall := integral_norm_sum_centeredTruncation_le hY hmean
    (fun _ _ hij ↦ hYi.indepFun hij) (v := v) hC r (fun i ↦ by
      simp only [Y, norm_mul, Complex.norm_real, mul_pow, integral_const_mul]
      exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) (ha i) 2)
        (((hW i).integral_norm_centeredTruncation_sq_le_mul (fun _ ↦ sq_nonneg _) r).trans
          (mul_le_mul_of_nonneg_left (hv i) r.coe_nonneg))
        (integral_nonneg fun _ ↦ sq_nonneg _) (sq_nonneg _))
  have hDi (i : ι) : Integrable (D i) P :=
    ((hW i).sub (integrable_const _)).sub
      (((hW i).aestronglyMeasurable.memLp_centeredTruncation r).integrable one_le_two)
  have hD (i : ι) : Integrable (fun ω ↦ a i * (D i ω : ℂ)) P :=
    (Complex.ofRealCLM.integrable_comp (hDi i)).const_mul _
  have hsum (ω : Ω) : (∑ i, a i * ((W i ω - ∫ y, W i y ∂P : ℝ) : ℂ)) =
      (∑ i, Y i ω) + ∑ i, a i * (D i ω : ℂ) := by
    rw [← sum_add_distrib]
    refine sum_congr rfl fun i _ ↦ ?_
    simp only [Y, D, Complex.ofReal_sub]
    ring
  -- Fold the squared coordinates to use the centered truncation decomposition.
  change (∫ ω, ‖∑ i, a i * ((W i ω - ∫ y, W i y ∂P : ℝ) : ℂ)‖ ∂P) ≤ _
  simp_rw [hsum]
  have ht := (memLp_finsetSum univ fun i _ ↦ hY i).integrable one_le_two
  have hd := integrable_finsetSum univ fun i _ ↦ hD i
  refine (integral_mono (ht.add hd).norm (ht.norm.add hd.norm) (fun _ ↦ norm_add_le _ _)).trans ?_
  rw [integral_add' ht.norm hd.norm, mul_add]
  refine add_le_add hsmall ?_
  calc
    _ ≤ ∫ ω, ∑ i, ‖a i * (D i ω : ℂ)‖ ∂P :=
      integral_mono hd.norm (integrable_finsetSum _ fun i _ ↦ (hD i).norm) (fun _ ↦ norm_sum_le _ _)
    _ ≤ _ := by
      rw [integral_finsetSum _ (fun i _ ↦ (hD i).norm), ← mul_assoc, mul_sum]
      apply sum_le_sum
      intro i _
      simp only [norm_mul, Complex.norm_real, integral_const_mul]
      rw [mul_assoc]
      exact mul_le_mul (ha i)
        ((hW i).integral_norm_sub_integral_sub_centeredTruncation_le (fun _ ↦ sq_nonneg _) r)
        (integral_nonneg fun _ ↦ norm_nonneg _) hC

open scoped Classical in
private theorem star_dotProduct_mulVec_sub_sum_diag_eq (A : Matrix ι ι ℂ)
    (x : ι → ℂ) (m : ι → ℝ) :
    star x ⬝ᵥ A *ᵥ x - ∑ i, A i i * (m i : ℂ) =
      (∑ p ∈ (univ : Finset ι).offDiag, A p.1 p.2 * (star (x p.1) * x p.2)) +
      ∑ i, A i i * ((‖x i‖ ^ 2 - m i : ℝ) : ℂ) := by
  let f (p : ι × ι) := A p.1 p.2 * (star (x p.1) * x p.2)
  have he : star x ⬝ᵥ A *ᵥ x = ∑ p ∈ (univ : Finset ι) ×ˢ (univ : Finset ι), f p := by
    rw [sum_product]
    simp only [dotProduct, mulVec, Pi.star_apply, mul_sum, f]
    exact sum_congr rfl fun i _ ↦ sum_congr rfl fun j _ ↦ by ring
  rw [he, ← diag_union_offDiag, sum_union (disjoint_diag_offDiag _), sum_diag]
  rw [add_comm, add_sub_assoc, ← sum_sub_distrib]
  refine congrArg (_ + ·) (sum_congr rfl fun i _ ↦ ?_)
  simp only [f, ← mul_sub, Complex.ofReal_sub, Complex.star_def, Complex.conj_mul',
    Complex.ofReal_pow]

/-- Mean absolute error of a quadratic form in centered independent complex coordinates,
relative to its diagonal second-moment sum. The cutoff applies to squared absolute values.
The bound uses only second moments and includes the contribution of the discarded tails. -/
theorem integral_norm_star_dotProduct_mulVec_sub_sum_diag_le [DecidableEq ι]
    (hX : iIndepFun X P) (hLp : ∀ i, MemLp (X i) 2 P) (hc : ∀ i, ∫ ω, X i ω ∂P = 0)
    (A : Matrix ι ι ℂ) {v : ℝ} (hv : ∀ i, ∫ ω, ‖X i ω‖ ^ 2 ∂P ≤ v) (r : ℝ≥0) :
    (∫ ω, ‖star (fun i ↦ X i ω) ⬝ᵥ A *ᵥ (fun i ↦ X i ω) -
      ∑ i, A i i * ((∫ y, ‖X i y‖ ^ 2 ∂P : ℝ) : ℂ)‖ ∂P) ≤
      ‖A‖ * (2 * v * Real.sqrt (Fintype.card ι) + Real.sqrt ((r : ℝ) * Fintype.card ι * v) +
        2 * ∑ i, ∫ ω, {ω | (r : ℝ) < ‖X i ω‖ ^ 2}.indicator (fun ω ↦ ‖X i ω‖ ^ 2) ω ∂P) := by
  cases isEmpty_or_nonempty ι
  · simp [dotProduct_of_isEmpty]
  obtain ⟨i⟩ := ‹Nonempty ι›
  have hv₀ : 0 ≤ v := (integral_nonneg fun ω ↦ sq_nonneg ‖X i ω‖).trans (hv i)
  have := hX.isProbabilityMeasure
  let m (i : ι) : ℝ := ∫ ω, ‖X i ω‖ ^ 2 ∂P
  have hA := hX.integral_norm_offDiag_le hLp hc A hv hv₀
  have hD := hX.integral_norm_weighted_centeredSquares_le hLp (fun i ↦ A i i) (norm_nonneg A)
    (fun i ↦ A.norm_apply_le_l2_opNorm i i) hv r
  have hW (i : ι) : Integrable (fun ω ↦ ‖X i ω‖ ^ 2) P :=
    (memLp_two_iff_integrable_sq_norm (hLp i).aestronglyMeasurable).mp (hLp i)
  have hDi : Integrable (fun ω ↦ ∑ i, A i i * ((‖X i ω‖ ^ 2 - m i : ℝ) : ℂ)) P :=
    integrable_finsetSum _ fun i _ ↦
      (Complex.ofRealCLM.integrable_comp ((hW i).sub (integrable_const _))).const_mul _
  have hAi : Integrable (fun ω ↦ ∑ p ∈ (univ : Finset ι).offDiag,
      A p.1 p.2 * (star (X p.1 ω) * X p.2 ω)) P :=
    integrable_finsetSum _ fun p hp ↦
      ((hX.integral_norm_sq_star_mul (mem_offDiag.mp hp).2.2 (hLp p.1) (hLp p.2)).1.integrable
        one_le_two).const_mul _
  simp_rw [star_dotProduct_mulVec_sub_sum_diag_eq]
  refine (integral_mono (hAi.add hDi).norm (hAi.norm.add hDi.norm)
    (fun _ ↦ norm_add_le _ _)).trans ?_
  rw [integral_add' hAi.norm hDi.norm]
  exact (add_le_add hA hD).trans_eq (by ring)

/-- The mean absolute quadratic-form bound for an independent random coefficient matrix with
almost surely bounded Euclidean operator norm. The centered quadratic form is integrable. -/
theorem integral_norm_star_dotProduct_mulVec_sub_sum_diag_le_of_indepFun [DecidableEq ι]
    (hX : iIndepFun X P) (hLp : ∀ i, MemLp (X i) 2 P) (hc : ∀ i, ∫ ω, X i ω ∂P = 0)
    {A : Ω → Matrix ι ι ℂ} (hA : AEMeasurable A P) (hind : IndepFun A (fun ω i ↦ X i ω) P)
    {C v : ℝ} (hC : ∀ᵐ ω ∂P, ‖A ω‖ ≤ C)
    (hv : ∀ i, ∫ ω, ‖X i ω‖ ^ 2 ∂P ≤ v) (r : ℝ≥0) :
    let Q := fun ω ↦ star (fun i ↦ X i ω) ⬝ᵥ A ω *ᵥ (fun i ↦ X i ω) -
      ∑ i, A ω i i * ((∫ y, ‖X i y‖ ^ 2 ∂P : ℝ) : ℂ)
    Integrable Q P ∧ (∫ ω, ‖Q ω‖ ∂P) ≤ C *
      (2 * v * Real.sqrt (Fintype.card ι) + Real.sqrt ((r : ℝ) * Fintype.card ι * v) +
        2 * ∑ i, ∫ ω, {ω | (r : ℝ) < ‖X i ω‖ ^ 2}.indicator (fun ω ↦ ‖X i ω‖ ^ 2) ω ∂P) := by
  intro Q
  cases isEmpty_or_nonempty ι
  · simp [Q, dotProduct_of_isEmpty]
  obtain ⟨i⟩ := ‹Nonempty ι›
  have hv₀ : 0 ≤ v := (integral_nonneg fun ω ↦ sq_nonneg ‖X i ω‖).trans (hv i)
  have : IsProbabilityMeasure P := hX.isProbabilityMeasure
  let Z (ω : Ω) (i : ι) := X i ω
  have hZ : AEMeasurable Z P := aemeasurable_pi_iff.mpr fun i ↦ (hLp i).aemeasurable
  let m (i : ι) : ℝ := ∫ ω, ‖X i ω‖ ^ 2 ∂P
  let f (p : Matrix ι ι ℂ × (ι → ℂ)) :=
    star p.2 ⬝ᵥ p.1 *ᵥ p.2 - ∑ i, p.1 i i * (m i : ℂ)
  have hf : Measurable f := by
    simp only [f, dotProduct, mulVec, Pi.star_apply]
    fun_prop
  let K := 2 * v * Real.sqrt (Fintype.card ι) + Real.sqrt ((r : ℝ) * Fintype.card ι * v) +
    2 * ∑ i, ∫ ω, {ω | (r : ℝ) < ‖X i ω‖ ^ 2}.indicator (fun ω ↦ ‖X i ω‖ ^ 2) ω ∂P
  have htail (i : ι) : 0 ≤ ∫ ω,
      {ω | (r : ℝ) < ‖X i ω‖ ^ 2}.indicator (fun ω ↦ ‖X i ω‖ ^ 2) ω ∂P :=
    integral_nonneg fun _ ↦ Set.indicator_nonneg (fun _ _ ↦ sq_nonneg _) _
  have hK : 0 ≤ K := by
    unfold K
    exact add_nonneg (by positivity) (mul_nonneg (by norm_num) (sum_nonneg fun i _ ↦ htail i))
  have hmap := hind.map_prod_eq_prod_map_map hA hZ
  have hprob : IsProbabilityMeasure (P.map A) := (Measure.isProbabilityMeasure_map_iff hA).2 ‹_›
  have hbound : (∫⁻ ω, ‖Q ω‖ₑ ∂P) ≤ ENNReal.ofReal (C * K) := by
    have hfn : Measurable (fun p ↦ ‖f p‖ₑ) := hf.eNorm
    -- Expose the joint map to use independence and the lower-integral product formula.
    change (∫⁻ ω, ‖f (A ω, Z ω)‖ₑ ∂P) ≤ _
    rw [← lintegral_map' hfn.aemeasurable (hA.prodMk hZ), hmap,
      lintegral_prod _ hfn.aemeasurable]
    calc
      _ ≤ ∫⁻ _ : Matrix ι ι ℂ, ENNReal.ofReal (C * K) ∂P.map A := by
        apply lintegral_mono_ae
        filter_upwards [(ae_map_iff hA (measurableSet_le measurable_norm measurable_const)).2 hC]
          with B hB
        have hfnB : Measurable (fun y ↦ ‖f (B, y)‖ₑ) := hfn.comp measurable_prodMk_left
        rw [lintegral_map' hfnB.aemeasurable hZ]
        have hint := (TauCeti.integral_star_dotProduct_mulVec_eq_sum_diag_of_pairwise_indepFun
          (fun _ _ hij ↦ hX.indepFun hij) (fun i ↦ (hLp i).integrable one_le_two)
          (fun i ↦ (memLp_two_iff_integrable_sq_norm (hLp i).aestronglyMeasurable).1 (hLp i))
          hc B).1
        have hint' : Integrable (fun ω ↦ f (B, Z ω)) P :=
          hint.sub (integrable_const (∑ i, B i i * (m i : ℂ)))
        rw [← ofReal_integral_norm_eq_lintegral_eNorm hint']
        apply ENNReal.ofReal_le_ofReal
        exact (hX.integral_norm_star_dotProduct_mulVec_sub_sum_diag_le hLp hc B hv r).trans
          (mul_le_mul_of_nonneg_right hB hK)
      _ = _ := by simp [lintegral_const]
  have hmeas : AEStronglyMeasurable Q P :=
    (hf.comp_aemeasurable (hA.prodMk hZ)).aestronglyMeasurable
  have hi : Integrable Q P :=
    ⟨hmeas, hasFiniteIntegral_iff_eNorm.2 (hbound.trans_lt ENNReal.ofReal_lt_top)⟩
  have hC₀ : 0 ≤ C := by
    obtain ⟨ω, hω⟩ := hC.exists
    exact (norm_nonneg _).trans hω
  refine ⟨hi, ?_⟩
  rw [integral_norm_eq_lintegral_eNorm hmeas]
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound).trans_eq
    (ENNReal.toReal_ofReal (mul_nonneg hC₀ hK))

end ProbabilityTheory.iIndepFun
