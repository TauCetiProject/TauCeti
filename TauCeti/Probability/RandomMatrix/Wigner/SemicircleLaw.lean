/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.RandomMatrix.Wigner.Resolvent
import TauCeti.Probability.StrongLaw
import TauCeti.Probability.RandomMatrix.Wigner.Centering.SpectralMeasure
import TauCeti.Probability.RandomMatrix.Wigner.Diagonal.SpectralMeasure
import TauCeti.Analysis.Matrix.SpectralMeasure.ResolventStability
import TauCeti.MeasureTheory.Function.Lp.Norm
import TauCeti.MeasureTheory.Function.L2Space
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp

/-!
# The almost-sure semicircle law

For corners of a single complex Wigner array, a finite second moment of the upper-entry law
suffices. Bounded approximations obey the resolvent law, and the strong law for the upper-triangular
corners controls the normalized Frobenius error in each approximation. The conclusion allows a
nonzero upper-entry mean and an identically distributed, pairwise independent real diagonal
with no moment assumption.

## References

* Z. D. Bai, *Methodologies in spectral analysis of large dimensional random matrices, a review*,
  Statistica Sinica 9 (1999), Theorem 2.1.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Matrix
open scoped Topology NNReal ENNReal Matrix.Norms.Frobenius

namespace TauCeti.Probability

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {ξ : StrictUpper → Ω → ℂ}

omit [MeasurableSpace Ω] in
private theorem norm_wignerMatrix_sub_div_sqrt_le
    (ζ : StrictUpper → Ω → ℂ) (n : ℕ) (ω : Ω) :
    ‖wignerMatrix ξ (fun _ _ ↦ 0) (n + 1) ω -
      wignerMatrix ζ (fun _ _ ↦ 0) (n + 1) ω‖ / Real.sqrt (n + 1) ≤
      Real.sqrt ((∑ i : FinStrictUpper (n + 1),
        ‖ξ i.toStrictUpper ω - ζ i.toStrictUpper ω‖ ^ 2) /
        ((n + 1).choose 2 : ℝ)) := by
  apply Real.le_sqrt_of_sq_le
  rw [div_pow, Real.sq_sqrt (by positivity), norm_wignerMatrix_sub_sq_eq_sum_finStrictUpper]
  cases n with
  | zero =>
    have : IsEmpty (FinStrictUpper 1) := ⟨fun i ↦ i.prop.ne (Subsingleton.elim _ _)⟩
    simp
  | succ n =>
    have hs : 0 < (((n + 1 + 1).choose 2 : ℕ) : ℝ) := by
      exact_mod_cast (Nat.choose_pos (by omega : 2 ≤ n + 1 + 1))
    have hn : 0 < (n + 1 + 1 : ℝ) := by positivity
    simp only [Nat.cast_add, Nat.cast_one]
    rw [div_le_div_iff₀ hn hs, mul_right_comm, mul_comm (∑ i : FinStrictUpper (n + 1 + 1),
      ‖ξ i.toStrictUpper ω - ζ i.toStrictUpper ω‖ ^ 2)]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    rw [Nat.cast_choose_two]
    simp only [Nat.cast_add, Nat.cast_one]
    field_simp
    linarith

section Limit

local notation "e₀" => (⟨(0, 1), by decide⟩ : StrictUpper)

private theorem ae_tendsto_wigner_approximation_error
    (hind : iIndepFun ξ P) (hid : ∀ i, IdentDistrib (ξ i) (ξ e₀) P P)
    (hξ : MemLp (ξ e₀) 2 P) {g : ℂ → ℂ} (hg : Measurable g)
    {b : ℝ≥0} (hb : ∀ x, ‖g x‖ ≤ b) :
    ∀ᵐ ω ∂P, Tendsto (fun n : ℕ ↦
      Real.sqrt ((∑ i : FinStrictUpper (n + 1),
        ‖ξ i.toStrictUpper ω - g (ξ i.toStrictUpper ω)‖ ^ 2) /
        ((n + 1).choose 2 : ℝ))) atTop (𝓝 (Real.sqrt (∫ ω, ‖ξ e₀ ω - g (ξ e₀ ω)‖ ^ 2 ∂P))) := by
  have : IsProbabilityMeasure P := hind.isProbabilityMeasure
  let f := fun x : ℂ ↦ ‖x - g x‖ ^ 2
  have hf : Measurable f := ((measurable_id.sub hg).norm).pow_const 2
  have hg₂ : MemLp (fun ω ↦ g (ξ e₀ ω)) 2 P :=
    (memLp_const (b : ℝ)).of_le (hg.comp_aemeasurable hξ.aemeasurable).aestronglyMeasurable
      (.of_forall fun ω ↦ by simpa only [Real.norm_of_nonneg b.coe_nonneg] using hb (ξ e₀ ω))
  have hint : Integrable (fun ω ↦ f (ξ e₀ ω)) P :=
    (hξ.sub hg₂).integrable_norm_pow'
  filter_upwards [ae_tendsto_inv_smul_sum_finStrictUpper (X := fun i ω ↦ f (ξ i ω)) hint
    (fun _ _ hij ↦ (hind.indepFun hij).comp hf hf) (fun i ↦ (hid i).comp hf)] with ω hω
  simp only [smul_eq_mul, inv_mul_eq_div] at hω
  exact (hω.comp (tendsto_add_atTop_nat 1)).sqrt

private theorem ae_tendsto_spectralMeasure_wignerMatrix_zero_of_bounded
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

private theorem ae_tendsto_spectralMeasure_wignerMatrix_zero_of_bounded_approximations
    (hind : iIndepFun ξ P) (hid : ∀ i, IdentDistrib (ξ i) (ξ e₀) P P)
    (hξ : MemLp (ξ e₀) 2 P) (v : ℝ≥0) (hv : ∫ ω, ‖ξ e₀ ω‖ ^ 2 ∂P = v)
    {g : ℕ → ℂ → ℂ} (hg : ∀ k, Measurable (g k))
    {b : ℕ → ℝ≥0} (hb : ∀ k x, ‖g k x‖ ≤ b k)
    (hmean_g : ∀ k, ∫ ω, g k (ξ e₀ ω) ∂P = 0)
    (hG : ∀ k, MemLp (fun ω ↦ g k (ξ e₀ ω)) 2 P)
    (hGL : Tendsto (fun k ↦ (hG k).toLp fun ω ↦ g k (ξ e₀ ω)) atTop (𝓝 (hξ.toLp (ξ e₀)))) :
    ∀ᵐ ω ∂P, Tendsto (fun n ↦ (wignerMatrix ξ (fun _ _ ↦ 0) (n + 1) ω).spectralMeasure
      (wignerMatrix_isHermitian ξ (fun _ _ ↦ 0) ω (n + 1))) atTop
      (𝓝 (⟨semicircleReal 0 v, inferInstance⟩ : ProbabilityMeasure ℝ)) := by
  let vₖ (k : ℕ) : ℝ≥0 := ⟨∫ ω, ‖g k (ξ e₀ ω)‖ ^ 2 ∂P, integral_nonneg fun _ ↦ sq_nonneg _⟩
  have hvₖ (k : ℕ) : (vₖ k : ℝ) = ∫ ω, ‖g k (ξ e₀ ω)‖ ^ 2 ∂P := rfl
  have hv_lim : Tendsto (fun k ↦ (vₖ k : ℝ)) atTop (𝓝 (v : ℝ)) := by
    simpa only [MemLp.norm_toLp_sq, hv, hvₖ] using hGL.norm.pow 2
  have he_lim : Tendsto (fun k ↦ ∫ ω, ‖ξ e₀ ω - g k (ξ e₀ ω)‖ ^ 2 ∂P) atTop (𝓝 0) := by
    have herr := (tendsto_const_nhds (x := hξ.toLp (ξ e₀))).sub hGL
    simpa only [← MemLp.toLp_sub, MemLp.norm_toLp_sq, Pi.sub_apply, sub_self, norm_zero, zero_pow
      (by decide : 2 ≠ 0)] using herr.norm.pow 2
  apply ProbabilityMeasure.ae_tendsto_of_ae_tendsto_resolventTransform
  intro z hz
  let s (u : ℝ≥0) := resolventTransform (semicircleReal 0 u) z
  have hbounded k := ae_tendsto_spectralMeasure_wignerMatrix_zero_of_bounded
    hind hid (hg k) (hb k) (hmean_g k) (vₖ k) rfl
  have herror k := ae_tendsto_wigner_approximation_error hind hid hξ (hg k) (hb k)
  filter_upwards [ae_all_iff.2 hbounded, ae_all_iff.2 herror] with ω hbounded herror
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
    ProbabilityMeasure.tendsto_resolventTransform_of_tendsto (hbounded k) hz.ne'
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
  let X := ξ e₀
  -- Approximate the identity under the entry law so that one map works for every entry.
  let f (k : ℕ) := SimpleFunc.approxOn (id : ℂ → ℂ) measurable_id Set.univ 0 (Set.mem_univ _) k
  have hbound (k : ℕ) : ∃ b : ℝ≥0, ∀ z, ‖f k z‖ ≤ b := by
    obtain ⟨b, hb⟩ := ((f k).finite_range.image fun z ↦ ‖z‖₊).bddAbove
    exact ⟨b, fun z ↦ hb ⟨f k z, ⟨z, rfl⟩, rfl⟩⟩
  choose b hb using hbound
  let F (k : ℕ) (ω : Ω) := f k (X ω)
  have hF (k : ℕ) : MemLp (F k) 2 P :=
    (memLp_const (b k : ℝ)).of_le
      ((f k).measurable.comp_aemeasurable hξ.aemeasurable).aestronglyMeasurable
      (.of_forall fun ω ↦ by simpa only [Real.norm_of_nonneg (b k).coe_nonneg] using hb k (X ω))
  have happrox {p : ℝ≥0∞} (hp : p ≠ ∞) (hX : MemLp X p P) :
      Tendsto (fun k ↦ eLpNorm (F k - X) p P) atTop (𝓝 0) := by
    have hid_mem : MemLp (id : ℂ → ℂ) p (P.map X) :=
      (memLp_map_measure_iff aestronglyMeasurable_id hX.aemeasurable).2 hX
    have hmap (k : ℕ) : eLpNorm (⇑(f k) - id) p (P.map X) = eLpNorm (F k - X) p P :=
      eLpNorm_map_measure ((f k).aestronglyMeasurable.sub aestronglyMeasurable_id) hX.aemeasurable
    have ht : Tendsto (fun k ↦ eLpNorm (⇑(f k) - id) p (P.map X)) atTop (𝓝 0) :=
      SimpleFunc.tendsto_approxOn_Lp_eLpNorm measurable_id (Set.mem_univ (0 : ℂ)) hp
        (.of_forall fun z ↦ subset_closure (Set.mem_univ (id z)))
        (by simpa only [sub_zero] using hid_mem.eLpNorm_lt_top)
    simpa only [hmap] using ht
  let c (k : ℕ) := ∫ ω, F k ω ∂P
  have hc : Tendsto c atTop (𝓝 0) :=
    hmean ▸ tendsto_integral_of_L1' X (.of_forall fun k ↦ (hF k).integrable one_le_two)
      (happrox (by simp) (hξ.mono_exponent one_le_two))
  let g (k : ℕ) (z : ℂ) := f k z - c k
  have hG (k : ℕ) : MemLp (fun ω ↦ g k (X ω)) 2 P := (hF k).sub (memLp_const (c k))
  -- Centering changes the L² classes by constants tending to zero.
  have hFL : Tendsto (fun k ↦ (hF k).toLp (F k)) atTop (𝓝 (hξ.toLp X)) :=
    (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' F hF X hξ).2 (happrox (by simp) hξ)
  have hcL := ((Lp.constL 2 P ℂ : ℂ →L[ℂ] Lp ℂ 2 P).continuous.tendsto 0).comp hc
  have hcenter (k : ℕ) : (hG k).toLp (fun ω ↦ g k (X ω)) =
      (hF k).toLp (F k) - Lp.const 2 P (c k) := by
    rw [← MemLp.toLp_const]
    exact MemLp.toLp_sub (hF k) (memLp_const (c k))
  have hGL : Tendsto (fun k ↦ (hG k).toLp fun ω ↦ g k (X ω)) atTop (𝓝 (hξ.toLp X)) := by
    simpa only [hcenter, Function.comp_def, Lp.constL_apply, map_zero, sub_zero] using hFL.sub hcL
  refine ae_tendsto_spectralMeasure_wignerMatrix_zero_of_bounded_approximations hind hid hξ v hv
    (g := g) (b := fun k ↦ b k + ‖c k‖₊) (fun k ↦ (f k).measurable.sub_const _) ?_ ?_ hG hGL
  · intro k z
    simpa only [NNReal.coe_add, coe_nnNorm] using
      (norm_sub_le (f k z) (c k)).trans (add_le_add (hb k z) le_rfl)
  · intro k
    have hcenter_mean : ∫ ω, (F k ω - c k) ∂P = 0 := by
      rw [integral_sub ((hF k).integrable one_le_two) (integrable_const (c k))]
      simp [c]
    exact hcenter_mean

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
  have hξc : MemLp (fun ω ↦ ξ e₀ ω - c) 2 P :=
    ((hid e₀).aemeasurable_fst.sub_const c).aestronglyMeasurable
      |>.memLp_two_of_integral_norm_sq_ne_zero (hv.trans_ne one_ne_zero)
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
