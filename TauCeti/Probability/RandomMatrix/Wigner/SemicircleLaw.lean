/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.RandomMatrix.Wigner.Resolvent
import TauCeti.Probability.RandomMatrix.Wigner.CornerAverage
import TauCeti.Probability.RandomMatrix.Centering
import TauCeti.Probability.RandomMatrix.Diagonal
import TauCeti.Analysis.Matrix.SpectralMeasure.ResolventStability
import Mathlib.Data.Nat.Choose.Cast

/-!
# The almost-sure semicircle law

For corners of a single complex Wigner array, a finite second moment of the upper-entry law
suffices. Bounded cutoffs obey the resolvent law, and the strong law for the upper-triangular
corners controls the normalized Frobenius error in each cutoff. The conclusion allows a
nonzero upper-entry mean and an identically distributed, pairwise independent real diagonal
with no moment assumption.

## References

* Z. D. Bai, *Methodologies in spectral analysis of large dimensional random matrices, a review*,
  Statistica Sinica 9 (1999), Theorem 2.1.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Matrix
open scoped Topology NNReal Matrix.Norms.Frobenius

namespace TauCeti.Probability

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {ξ : StrictUpper → Ω → ℂ} {X : Ω → ℂ}

private theorem exists_centered_norm_cutoffs [IsProbabilityMeasure P] (hX : MemLp X 2 P)
    (hmean : ∫ ω, X ω ∂P = 0) :
    ∃ g : ℕ → ℂ → ℂ, (∀ k, Measurable (g k)) ∧
      (∀ k, ∃ b : ℝ≥0, ∀ x, ‖g k x‖ ≤ b) ∧ (∀ k, ∫ ω, g k (X ω) ∂P = 0) ∧
      Tendsto (fun k ↦ ∫ ω, ‖g k (X ω)‖ ^ 2 ∂P) atTop (𝓝 (∫ ω, ‖X ω‖ ^ 2 ∂P)) ∧
      Tendsto (fun k ↦ ∫ ω, ‖X ω - g k (X ω)‖ ^ 2 ∂P) atTop (𝓝 0) := by
  let f (k : ℕ) (x : ℂ) := if ‖x‖ ≤ (k : ℝ) then x else 0
  let c (k : ℕ) := ∫ ω, f k (X ω) ∂P
  let g (k : ℕ) (x : ℂ) := f k x - c k
  let B := ∫ ω, ‖X ω‖ ∂P
  have hf (k : ℕ) : Measurable (f k) :=
    measurable_id.ite (measurableSet_le continuous_norm.measurable measurable_const)
      measurable_const
  have hbound (k : ℕ) (x : ℂ) : ‖f k x‖ ≤ min (k : ℝ) ‖x‖ := by
    dsimp only [f]
    split_ifs with h
    · simp [min_eq_right h]
    · exact (norm_zero (E := ℂ)).le.trans (le_min (by positivity) (norm_nonneg _))
  have hX₁ : Integrable X P := hX.integrable (by norm_num)
  have hfx (k : ℕ) : Integrable (fun ω ↦ f k (X ω)) P :=
    hX₁.norm.mono' ((hf k).comp_aemeasurable hX.aemeasurable).aestronglyMeasurable
      (.of_forall fun ω ↦ (hbound k (X ω)).trans (min_le_right _ _))
  have hc (k : ℕ) : ‖c k‖ ≤ B :=
    (norm_integral_le_integral_norm _).trans
      (integral_mono (hfx k).norm hX₁.norm fun ω ↦ (hbound k (X ω)).trans (min_le_right _ _))
  have hlim (x : ℂ) : Tendsto (fun k ↦ f k x) atTop (𝓝 x) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [tendsto_natCast_atTop_atTop.eventually_ge_atTop ‖x‖] with k hk
    simp [f, hk]
  -- The discarded entries have vanishing contribution to the mean.
  have hc0 : Tendsto c atTop (𝓝 0) := by
    rw [← hmean]
    exact tendsto_integral_filter_of_dominated_convergence (fun ω ↦ ‖X ω‖)
      (.of_forall fun k ↦ (hfx k).aestronglyMeasurable)
      (.of_forall fun k ↦ .of_forall fun ω ↦ (hbound k (X ω)).trans (min_le_right _ _))
      hX₁.norm (.of_forall fun ω ↦ hlim (X ω))
  have hg (k : ℕ) : Measurable (g k) := (hf k).sub_const _
  have hgnorm (k : ℕ) (ω : Ω) : ‖g k (X ω)‖ ≤ ‖X ω‖ + B :=
    (norm_sub_le _ _).trans (add_le_add ((hbound k _).trans (min_le_right _ _)) (hc k))
  have hg_lim (ω : Ω) : Tendsto (fun k ↦ g k (X ω)) atTop (𝓝 (X ω)) := by
    simpa only [sub_zero] using (hlim (X ω)).sub hc0
  have hdom (b : ℝ) : Integrable (fun ω ↦ (b * ‖X ω‖ + B) ^ 2) P :=
    ((hX.norm.const_mul b).add (memLp_const B)).integrable_sq
  -- The same integrable bound controls the centered variables and the approximation errors.
  refine ⟨g, hg, fun k ↦ ⟨k + ‖c k‖₊, fun x ↦ ?_⟩, fun k ↦ ?_, ?_, ?_⟩
  · simpa only [NNReal.coe_add, NNReal.coe_natCast, coe_nnNorm] using
      (norm_sub_le (f k x) (c k)).trans
        (add_le_add ((hbound k x).trans (min_le_left _ _)) le_rfl)
  · simp [g, c, integral_sub (hfx k) (integrable_const _)]
  · refine tendsto_integral_filter_of_dominated_convergence _ ?_ ?_ (hdom 1) ?_
    · exact .of_forall fun k ↦
        (((hg k).comp_aemeasurable hX.aemeasurable).norm.pow_const 2).aestronglyMeasurable
    · exact .of_forall fun k ↦ .of_forall fun ω ↦ by
        rw [Real.norm_of_nonneg (sq_nonneg _), one_mul]
        gcongr
        exact hgnorm k ω
    · exact .of_forall fun ω ↦ (hg_lim ω).norm.pow 2
  · rw [← integral_zero Ω ℝ]
    refine tendsto_integral_filter_of_dominated_convergence _ ?_ ?_ (hdom 2) ?_
    · exact .of_forall fun k ↦ ((hX.aemeasurable.sub
        ((hg k).comp_aemeasurable hX.aemeasurable)).norm.pow_const 2).aestronglyMeasurable
    · exact .of_forall fun k ↦ .of_forall fun ω ↦ by
        rw [Real.norm_of_nonneg (sq_nonneg _)]
        exact pow_le_pow_left₀ (norm_nonneg _)
          (by linarith [norm_sub_le (X ω) (g k (X ω)), hgnorm k ω]) _
    · exact .of_forall fun ω ↦ by
        simpa only [sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0)] using
          ((tendsto_const_nhds (x := X ω)).sub (hg_lim ω)).norm.pow 2

omit [MeasurableSpace Ω] in
private theorem norm_wignerMatrix_sub_div_sqrt_le
    (ζ : StrictUpper → Ω → ℂ) (n : ℕ) (ω : Ω) :
    ‖wignerMatrix ξ (fun _ _ ↦ 0) (n + 1) ω -
      wignerMatrix ζ (fun _ _ ↦ 0) (n + 1) ω‖ / Real.sqrt (n + 1) ≤
      Real.sqrt ((∑ i : StrictUpperFin (n + 1),
        ‖ξ (wignerUpperIndex i) ω - ζ (wignerUpperIndex i) ω‖ ^ 2) /
        ((n + 1).choose 2 : ℝ)) := by
  apply Real.le_sqrt_of_sq_le
  rw [div_pow, Real.sq_sqrt (by positivity), norm_wignerMatrix_sub_sq_eq_sum_strictUpperFin]
  cases n with
  | zero =>
    have : IsEmpty (StrictUpperFin 1) := ⟨fun i ↦
      (Nat.not_lt_zero _) (i.prop.trans_le (Nat.le_of_lt_succ i.val.2.isLt))⟩
    simp
  | succ n =>
    have hs : 0 < (((n + 1 + 1).choose 2 : ℕ) : ℝ) := by
      exact_mod_cast (Nat.choose_pos (by omega : 2 ≤ n + 1 + 1))
    have hn : 0 < (n + 1 + 1 : ℝ) := by positivity
    simp only [Nat.cast_add, Nat.cast_one]
    rw [div_le_div_iff₀ hn hs, mul_right_comm, mul_comm (∑ i : StrictUpperFin (n + 1 + 1),
      ‖ξ (wignerUpperIndex i) ω - ζ (wignerUpperIndex i) ω‖ ^ 2)]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    rw [Nat.cast_choose_two]
    simp only [Nat.cast_add, Nat.cast_one]
    field_simp
    linarith

section Limit

local notation "e₀" => (⟨(0, 1), by decide⟩ : StrictUpper)

private theorem ae_tendsto_wigner_cutoff_error
    (hind : iIndepFun ξ P) (hid : ∀ i, IdentDistrib (ξ i) (ξ e₀) P P)
    (hξ : MemLp (ξ e₀) 2 P) {g : ℂ → ℂ} (hg : Measurable g)
    {b : ℝ≥0} (hb : ∀ x, ‖g x‖ ≤ b) :
    ∀ᵐ ω ∂P, Tendsto (fun n : ℕ ↦
      Real.sqrt ((∑ i : StrictUpperFin (n + 1),
        ‖ξ (wignerUpperIndex i) ω - g (ξ (wignerUpperIndex i) ω)‖ ^ 2) /
        ((n + 1).choose 2 : ℝ))) atTop (𝓝 (Real.sqrt (∫ ω, ‖ξ e₀ ω - g (ξ e₀ ω)‖ ^ 2 ∂P))) := by
  have : IsProbabilityMeasure P := hind.isProbabilityMeasure
  let f := fun x : ℂ ↦ ‖x - g x‖ ^ 2
  have hf : Measurable f := ((measurable_id.sub hg).norm).pow_const 2
  have hg₂ : MemLp (fun ω ↦ g (ξ e₀ ω)) 2 P :=
    (memLp_const (b : ℝ)).of_le (hg.comp_aemeasurable hξ.aemeasurable).aestronglyMeasurable
      (.of_forall fun ω ↦ by simpa only [Real.norm_of_nonneg b.coe_nonneg] using hb (ξ e₀ ω))
  have hint : Integrable (fun ω ↦ f (ξ e₀ ω)) P :=
    (hξ.sub hg₂).integrable_norm_pow'
  filter_upwards [ae_tendsto_sum_strictUpperFin_div (X := fun i ω ↦ f (ξ i ω)) hint
    (fun _ _ hij ↦ (hind.indepFun hij).comp hf hf) (fun i ↦ (hid i).comp hf)] with ω hω
  exact (hω.comp (tendsto_add_atTop_nat 1)).sqrt

private theorem ae_tendsto_spectralMeasure_wignerMatrix_zero_of_cutoff
    (hind : iIndepFun ξ P) (hid : ∀ i, IdentDistrib (ξ i) (ξ e₀) P P)
    {g : ℂ → ℂ} (hg : Measurable g) {b : ℝ≥0} (hb : ∀ x, ‖g x‖ ≤ b)
    (hmean : ∫ ω, g (ξ e₀ ω) ∂P = 0) (v : ℝ≥0)
    (hv : ∫ ω, ‖g (ξ e₀ ω)‖ ^ 2 ∂P = v) :
    ∀ᵐ ω ∂P, Tendsto (fun n ↦ (wignerMatrix (fun i ω' ↦ g (ξ i ω'))
      (fun _ _ ↦ 0) (n + 1) ω).spectralMeasure (wignerMatrix_isHermitian _ _ ω (n + 1)))
      atTop (𝓝 (⟨semicircleReal 0 v, inferInstance⟩ : ProbabilityMeasure ℝ)) := by
  have : IsProbabilityMeasure P := hind.isProbabilityMeasure
  have hi i := (hid i).comp hg
  exact ae_tendsto_spectralMeasure_wignerMatrix_zero_of_hasSubgaussianMGF
    (K := b ^ 2) (fun i ↦ hasSubgaussianMGF_re_star_mul_of_norm_le
      (hi i).aemeasurable_fst (.of_forall fun ω ↦ hb (ξ i ω))
      ((hi i).integral_eq.trans hmean))
    (hind.comp (fun _ ↦ g) (fun _ ↦ hg))
    (fun i ↦ (((hi i).comp (by fun_prop : Measurable fun x : ℂ ↦ ‖x‖ ^ 2)).integral_eq.trans hv))

/-- Almost-sure weak convergence of the zero-diagonal Wigner corners for centred i.i.d.
upper entries with finite second moment `v`. -/
theorem ae_tendsto_spectralMeasure_wignerMatrix_zero_of_memLp
    (hind : iIndepFun ξ P) (hid : ∀ i, IdentDistrib (ξ i) (ξ e₀) P P)
    (hξ : MemLp (ξ e₀) 2 P) (hmean : ∫ ω, ξ e₀ ω ∂P = 0)
    (v : ℝ≥0) (hv : ∫ ω, ‖ξ e₀ ω‖ ^ 2 ∂P = v) :
    ∀ᵐ ω ∂P, Tendsto (fun n ↦ (wignerMatrix ξ (fun _ _ ↦ 0) (n + 1) ω).spectralMeasure
      (wignerMatrix_isHermitian ξ (fun _ _ ↦ 0) ω (n + 1))) atTop
      (𝓝 (⟨semicircleReal 0 v, inferInstance⟩ : ProbabilityMeasure ℝ)) := by
  have : IsProbabilityMeasure P := hind.isProbabilityMeasure
  obtain ⟨g, hg, hb, hmean_g, hv_lim, he_lim⟩ := exists_centered_norm_cutoffs hξ hmean
  choose b hb using hb
  let vₖ (k : ℕ) : ℝ≥0 := ⟨∫ ω, ‖g k (ξ e₀ ω)‖ ^ 2 ∂P, integral_nonneg fun _ ↦ sq_nonneg _⟩
  have hv_lim : Tendsto (fun k ↦ ((vₖ k : ℝ≥0) : ℝ)) atTop (𝓝 (v : ℝ)) := hv ▸ hv_lim
  apply ProbabilityMeasure.ae_tendsto_of_ae_tendsto_resolventTransform
  intro z hz
  let s (u : ℝ≥0) := resolventTransform (semicircleReal 0 u) z
  have hcut k := ae_tendsto_spectralMeasure_wignerMatrix_zero_of_cutoff
    hind hid (hg k) (hb k) (hmean_g k) (vₖ k) rfl
  have herror k := ae_tendsto_wigner_cutoff_error hind hid hξ (hg k) (hb k)
  filter_upwards [ae_all_iff.2 hcut, ae_all_iff.2 herror] with ω hcut herror
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hs (k : ℕ) : ‖s (vₖ k) - s v‖ ≤ |(vₖ k : ℝ) - v| / z.im ^ 3 :=
    norm_resolventTransform_semicircleReal_sub_le hz _
  have hvarSmall := ((hv_lim.sub_const (v : ℝ)).abs.div_const (z.im ^ 3)).eventually_lt_const
    (u := ε / 3) (by simpa only [sub_self, abs_zero, zero_div] using (by positivity : 0 < ε / 3))
  have herrSmall := (((he_lim.sqrt).const_mul (z.im⁻¹ ^ 2))).eventually_lt_const
    (u := ε / 3) (by simpa only [Real.sqrt_zero, mul_zero] using (by positivity : 0 < ε / 3))
  obtain ⟨k, hk₁, hk₂⟩ := (hvarSmall.and herrSmall).exists
  let W (x : StrictUpper → Ω → ℂ) (n : ℕ) := wignerMatrix x (fun _ _ ↦ 0) (n + 1) ω
  let m (x : StrictUpper → Ω → ℂ) (n : ℕ) := resolventTransform
    ((W x n).spectralMeasure (wignerMatrix_isHermitian x _ ω (n + 1)) : Measure ℝ) z
  let ζ (i : StrictUpper) (ω' : Ω) := g k (ξ i ω')
  have hzeta : Tendsto (m ζ) atTop (𝓝 (s (vₖ k))) :=
    ProbabilityMeasure.tendsto_resolventTransform_of_tendsto (hcut k) hz.ne'
  filter_upwards [Metric.tendsto_nhds.mp hzeta (ε / 3) (by positivity),
    ((herror k).const_mul (z.im⁻¹ ^ 2)).eventually_lt_const hk₂] with n hn hnorm
  have hpert := Matrix.norm_resolventTransform_spectralMeasure_sub_le_frobenius
    (wignerMatrix_isHermitian ξ (fun _ _ ↦ 0) ω (n + 1))
    (wignerMatrix_isHermitian ζ (fun _ _ ↦ 0) ω (n + 1)) (z := z) hz.ne'
  have hsmall : ‖m ξ n - m ζ n‖ < ε / 3 := by
    refine (hpert.trans ?_).trans_lt hnorm
    simp only [Fintype.card_fin, abs_of_pos hz, mul_div_assoc, Nat.cast_add, Nat.cast_one]
    exact mul_le_mul_of_nonneg_left (norm_wignerMatrix_sub_div_sqrt_le (ξ := ξ) ζ n ω)
      (by positivity)
  rw [dist_eq_norm] at hn ⊢
  exact (norm_sub_le_norm_sub_add_norm_sub (m ξ n) (m ζ n) (s v)).trans_lt
    (by linarith [norm_sub_le_norm_sub_add_norm_sub (m ζ n) (s (vₖ k)) (s v),
      (hs k).trans_lt hk₁])

/-- **Wigner's semicircle law.** The empirical spectral measures of the corners of a single
array converge almost surely to the standard semicircle law if the complex upper entries
are i.i.d. with finite second moment and centred variance one. The real diagonal entries
may have any common law and need only be pairwise independent. -/
theorem wigner_semicircle_ae (η : ℕ → Ω → ℝ)
    (hind : iIndepFun ξ P) (hid : ∀ i, IdentDistrib (ξ i) (ξ e₀) P P)
    (hv : ∫ ω, ‖ξ e₀ ω - ∫ ω', ξ e₀ ω' ∂P‖ ^ 2 ∂P = 1)
    (hηind : Pairwise fun i j ↦ IndepFun (η i) (η j) P)
    (hηid : ∀ i, IdentDistrib (η i) (η 0) P P) :
    ∀ᵐ ω ∂P, Tendsto (fun n ↦ (wignerMatrix ξ η (n + 1) ω).spectralMeasure
      (wignerMatrix_isHermitian ξ η ω (n + 1))) atTop
      (𝓝 (⟨semicircleReal 0 1, inferInstance⟩ : ProbabilityMeasure ℝ)) := by
  have : IsProbabilityMeasure P := hind.isProbabilityMeasure
  let c := ∫ ω, ξ e₀ ω ∂P
  have hint : Integrable (fun ω ↦ ‖ξ e₀ ω - c‖ ^ 2) P := by
    by_contra h
    exact zero_ne_one ((integral_undef h).symm.trans hv)
  have hξc : MemLp (fun ω ↦ ξ e₀ ω - c) 2 P :=
    (memLp_two_iff_integrable_sq_norm
      ((hid e₀).aemeasurable_fst.sub_const c).aestronglyMeasurable).2 hint
  have hξ : MemLp (ξ e₀) 2 P :=
    (hξc.add (memLp_const c)).ae_eq (.of_forall fun ω ↦ sub_add_cancel (ξ e₀ ω) c)
  have hcentred : ∫ ω, (ξ e₀ ω - c) ∂P = 0 := by
    simp [c, integral_sub (hξ.integrable (by norm_num)) (integrable_const _)]
  have hξ₀ := ae_tendsto_spectralMeasure_wignerMatrix_zero_of_memLp
    (ξ := fun i ω ↦ ξ i ω - c)
    (hind.comp (fun _ z ↦ z - c) (fun _ ↦ measurable_id.sub_const _))
    (fun i ↦ (hid i).comp (measurable_id.sub_const _))
    hξc hcentred 1 (by simpa only [NNReal.coe_one] using hv)
  have hzero := (ae_tendsto_spectralMeasure_wignerMatrix_center_iff
    P ξ (fun _ _ ↦ 0) c _).2 hξ₀
  filter_upwards [hzero, ae_tendsto_spectralMeasure_wignerMatrix_zero_iff ξ η hηind hηid]
    with ω hω hdiag
  exact (hdiag _).1 hω

end Limit

end TauCeti.Probability
