/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Function
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Function.UniformIntegrable
public import TauCeti.MeasureTheory.Integral.Lebesgue.Truncation

/-!
# The de la Vallée Poussin criterion

A function `Φ : ℝ → ℝ` is superlinear when `Φ t / t → ∞` as `t → ∞`. De la Vallée Poussin's
criterion relates integrability and uniform integrability to integral bounds on `Φ(‖f‖)` for
such `Φ`. This file proves the two directions used to exclude concentration of mass in
approximation arguments: the existence of `Φ` for a single integrable function, and uniform
control on small sets from a uniform bound on `∫ Φ(‖fᵢ‖)`.

* If `f` is integrable, there is a convex, monotone, superlinear `Φ` with `Φ 0 = 0` and
  `Φ ∘ ‖f‖` integrable (`MeasureTheory.Integrable.exists_convexOn_superlinear_integrable`).
  Convexity makes such a bound compatible with Jensen's inequality.
* If `∫ Φ(‖fᵢ‖) ≤ C < ∞` for all `i` and `Φ` is superlinear, then for every `ε > 0` there is
  `T` with `∫_s ‖fᵢ‖ ≤ T μ(s) + ε` for all `i` and all sets `s`
  (`TauCeti.exists_setLIntegral_enorm_le_mul_add`). In particular a family of a.e. strongly
  measurable functions with such a bound is uniformly integrable in Mathlib's sense
  (`TauCeti.unifIntegrable_of_lintegral_ofReal_le`).
* On a finite measure space, the same superlinear bound gives `UniformIntegrable`
  (`TauCeti.uniformIntegrable_of_lintegral_ofReal_le`) and turns convergence in measure
  into convergence of Bochner integrals (`TauCeti.tendsto_integral_of_lintegral_ofReal_le`),
  requiring measurability and the bound only eventually along the filter.
  The square-integrable specialization uses eventually uniformly bounded integrals of squared norms
  (`TauCeti.tendsto_integral_of_integral_norm_sq_le`).

## Implementation notes

The function `Φ` of the first statement is the sum of ramps `∑ₖ max (x - tₖ) 0`, where the
levels `tₖ ≥ k` are chosen so that `∫ (‖f‖ - tₖ)⁺ ≤ δₖ` for a summable sequence `δₖ`. Each ramp
is convex and monotone, and the sum is superlinear because ever more ramps are active.

## References

* C. de la Vallée Poussin, *Sur l'intégrale de Lebesgue*, Trans. Amer. Math. Soc. **16** (1915),
  435–501.
* V. I. Bogachev, *Measure Theory*, Vol. I, Springer, 2007, §4.5.
-/

public section

open Filter MeasureTheory Set Topology
open scoped ENNReal NNReal

variable {α F ι : Type*} [MeasurableSpace α] [NormedAddCommGroup F] {μ : Measure α}

namespace TauCeti

section Ramps

variable {t : ℕ → ℝ}

private theorem summable_max_sub_zero (ht : ∀ k : ℕ, (k : ℝ) ≤ t k) (x : ℝ) :
    Summable fun k ↦ max (x - t k) 0 := by
  refine summable_of_ne_finset_zero (s := Finset.range (⌊x⌋₊ + 1)) fun k hk ↦ ?_
  have hxk : x < k := Nat.lt_of_floor_lt (Nat.lt_of_succ_le (not_lt.1 (Finset.mem_range.not.1 hk)))
  exact max_eq_right (by linarith [ht k])

private theorem tsum_max_sub_zero_zero (ht : ∀ k : ℕ, (k : ℝ) ≤ t k) :
    ∑' k, max (0 - t k) 0 = 0 := by
  have h : ∀ k, max (0 - t k) 0 = 0 := fun k ↦
    max_eq_right (by linarith [ht k, (Nat.cast_nonneg k : (0 : ℝ) ≤ k)])
  simp only [h, tsum_zero]

private theorem monotone_tsum_max_sub_zero (ht : ∀ k : ℕ, (k : ℝ) ≤ t k) :
    Monotone fun x ↦ ∑' k, max (x - t k) 0 := fun x y hxy ↦
  (summable_max_sub_zero ht x).tsum_le_tsum (fun k ↦ max_le_max (by linarith) le_rfl)
    (summable_max_sub_zero ht y)

private theorem convexOn_tsum_max_sub_zero (ht : ∀ k : ℕ, (k : ℝ) ≤ t k) :
    ConvexOn ℝ univ fun x ↦ ∑' k, max (x - t k) 0 := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab ↦ ?_⟩
  simp only [smul_eq_mul]
  rw [← tsum_mul_left, ← tsum_mul_left,
    ← ((summable_max_sub_zero ht x).mul_left a).tsum_add ((summable_max_sub_zero ht y).mul_left b)]
  refine (summable_max_sub_zero ht _).tsum_le_tsum (fun k ↦ max_le ?_ (by positivity))
    (((summable_max_sub_zero ht x).mul_left a).add ((summable_max_sub_zero ht y).mul_left b))
  have hx := mul_le_mul_of_nonneg_left (le_max_left (x - t k) 0) ha
  have hy := mul_le_mul_of_nonneg_left (le_max_left (y - t k) 0) hb
  have : a * x + b * y - t k = a * (x - t k) + b * (y - t k) := by
    linear_combination t k * hab
  linarith

private theorem tendsto_tsum_max_sub_zero_div (ht : ∀ k : ℕ, (k : ℝ) ≤ t k) :
    Tendsto (fun x ↦ (∑' k, max (x - t k) 0) / x) atTop atTop := by
  refine tendsto_atTop.2 fun M ↦ ?_
  set N := ⌈M⌉₊ + 1
  set S := ∑ k ∈ Finset.range N, t k
  filter_upwards [eventually_ge_atTop (max S 1)] with x hx
  have hx1 : 1 ≤ x := le_of_max_le_right hx
  have hxS : S ≤ x := le_of_max_le_left hx
  -- Each ramp dominates `x - t k`, so the first `N` ramps sum to at least `N * x - S`.
  have hsum : N * x - S ≤ ∑' k, max (x - t k) 0 :=
    calc (N : ℝ) * x - S = ∑ k ∈ Finset.range N, (x - t k) := by
          simp [Finset.sum_sub_distrib, S]
      _ ≤ ∑ k ∈ Finset.range N, max (x - t k) 0 :=
          Finset.sum_le_sum fun k _ ↦ le_max_left _ _
      _ ≤ _ := (summable_max_sub_zero ht x).sum_le_tsum _ fun k _ ↦ le_max_right _ _
  have hN : M + 1 ≤ N := by
    simp only [N, Nat.cast_add, Nat.cast_one, add_le_add_iff_right]
    exact Nat.le_ceil M
  rw [le_div_iff₀ (by linarith)]
  nlinarith

end Ramps

end TauCeti

namespace MeasureTheory.Integrable

open TauCeti

/-- **De la Vallée Poussin's lemma.** Every integrable function `f` remains integrable after
composing its norm with some convex, monotone function `Φ` with `Φ 0 = 0` that grows
superlinearly, `Φ t / t → ∞`. -/
theorem exists_convexOn_superlinear_integrable {f : α → F} (hf : Integrable f μ) :
    ∃ Φ : ℝ → ℝ, Φ 0 = 0 ∧ Monotone Φ ∧ ConvexOn ℝ univ Φ ∧
      Tendsto (fun t ↦ Φ t / t) atTop atTop ∧ Integrable (fun a ↦ Φ ‖f a‖) μ := by
  -- The positive parts `(‖f‖ - s)⁺` have integrals tending to zero as `s → ∞`.
  have htail : Tendsto (fun s : ℝ ↦ ∫⁻ a, ENNReal.ofReal (‖f a‖ - s) ∂μ) atTop (𝓝 0) := by
    refine ((tendsto_lintegral_tsub_atTop
      hf.hasFiniteIntegral.ne).comp Real.tendsto_toNNReal_atTop).congr' ?_
    filter_upwards [eventually_ge_atTop 0] with s hs
    simp only [Function.comp_apply, ← ofReal_norm, ENNReal.ofReal_sub _ hs]
    rfl
  obtain ⟨δ, hδ, hδsum⟩ := ENNReal.exists_pos_sum_of_countable one_ne_zero ℕ
  -- Choose levels `t k ≥ k` above which `‖f‖` has integral at most `δ k`.
  choose t ht hδt using fun k : ℕ ↦ ((eventually_ge_atTop (k : ℝ)).and
    (htail.eventually
      (ge_mem_nhds (by exact_mod_cast hδ k : (0 : ℝ≥0∞) < δ k)))).exists
  have hmono := monotone_tsum_max_sub_zero ht
  refine ⟨fun x ↦ ∑' k, max (x - t k) 0, tsum_max_sub_zero_zero ht, hmono,
    convexOn_tsum_max_sub_zero ht, tendsto_tsum_max_sub_zero_div ht,
    (hmono.measurable.comp_aemeasurable
      hf.aestronglyMeasurable.norm.aemeasurable).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ fun a ↦ tsum_nonneg fun k ↦ le_max_right _ _)]
  calc ∫⁻ a, ENNReal.ofReal (∑' k, max (‖f a‖ - t k) 0) ∂μ
      = ∑' k, ∫⁻ a, ENNReal.ofReal (‖f a‖ - t k) ∂μ := by
        simp only [ENNReal.ofReal_tsum_of_nonneg (fun _ ↦ le_max_right _ _)
          (summable_max_sub_zero ht _), ENNReal.ofReal_max, ENNReal.ofReal_zero, zero_le,
          max_eq_left]
        exact lintegral_tsum fun k ↦
          (hf.aestronglyMeasurable.norm.aemeasurable.sub_const _).ennreal_ofReal
    _ ≤ ∑' k, (δ k : ℝ≥0∞) := tsum_le_tsum hδt
    _ < ∞ := hδsum.trans ENNReal.one_lt_top

end MeasureTheory.Integrable

namespace TauCeti

/-- A superlinear function eventually dominates every positive multiple of the identity: for
every `δ > 0` there is `M` with `t ≤ M + δ Φ(t)` for all `t`, after truncating at zero. -/
private theorem exists_ofReal_le_add_mul_ofReal {Φ : ℝ → ℝ}
    (hΦ : Tendsto (fun t ↦ Φ t / t) atTop atTop) {δ : ℝ≥0} (hδ : 0 < δ) :
    ∃ M : ℝ≥0, ∀ t : ℝ, ENNReal.ofReal t ≤ M + δ * ENNReal.ofReal (Φ t) := by
  obtain ⟨N, hN⟩ := eventually_atTop.1
    ((hΦ.eventually_ge_atTop (δ : ℝ)⁻¹).and (eventually_gt_atTop 0))
  refine ⟨N.toNNReal, fun t ↦ ?_⟩
  rcases le_or_gt N t with h | h
  · obtain ⟨h₁, h₂⟩ := hN t h
    have hδ' : (0 : ℝ) < δ := hδ
    have : t ≤ δ * Φ t := by
      rw [le_div_iff₀ h₂] at h₁
      rw [← inv_mul_le_iff₀ hδ']
      linarith
    calc ENNReal.ofReal t ≤ ENNReal.ofReal (δ * Φ t) := ENNReal.ofReal_le_ofReal this
      _ = δ * ENNReal.ofReal (Φ t) := by
        rw [ENNReal.ofReal_mul δ.coe_nonneg, ENNReal.ofReal_coe_nnreal]
      _ ≤ _ := le_add_self
  · calc ENNReal.ofReal t ≤ ENNReal.ofReal N := ENNReal.ofReal_le_ofReal h.le
      _ ≤ _ := le_self_add

/-- **De la Vallée Poussin's criterion, quantitative form.** If `Φ` is superlinear and the
functions `f i` satisfy the uniform bound `∫ Φ(‖f i‖) ≤ C < ∞`, then for every `ε > 0` there is
a finite `T` with `∫_s ‖f i‖ ≤ T μ(s) + ε` for every index `i` and every set `s`. -/
theorem exists_setLIntegral_enorm_le_mul_add {Φ : ℝ → ℝ}
    (hΦ : Tendsto (fun t ↦ Φ t / t) atTop atTop) {f : ι → α → F} {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hf : ∀ i, ∫⁻ a, ENNReal.ofReal (Φ ‖f i a‖) ∂μ ≤ C) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ T : ℝ≥0, ∀ i (s : Set α), ∫⁻ a in s, ‖f i a‖ₑ ∂μ ≤ T * μ s + ε := by
  obtain ⟨δ, hδ, hδC⟩ := ENNReal.exists_nnreal_pos_mul_lt hC hε
  obtain ⟨M, hM⟩ := exists_ofReal_le_add_mul_ofReal hΦ hδ
  refine ⟨M, fun i s ↦ ?_⟩
  calc ∫⁻ a in s, ‖f i a‖ₑ ∂μ ≤ ∫⁻ a in s, (M + δ * ENNReal.ofReal (Φ ‖f i a‖)) ∂μ :=
        lintegral_mono fun a ↦ by rw [← ofReal_norm]; exact hM _
    _ = M * μ s + δ * ∫⁻ a in s, ENNReal.ofReal (Φ ‖f i a‖) ∂μ := by
        rw [lintegral_add_left measurable_const, lintegral_const, Measure.restrict_apply_univ,
          lintegral_const_mul' _ _ ENNReal.coe_ne_top]
    _ ≤ M * μ s + δ * C := by
        gcongr
        exact (setLIntegral_le_lintegral _ _).trans (hf i)
    _ ≤ M * μ s + ε := by gcongr

/-- **De la Vallée Poussin's criterion.** A family of a.e. strongly measurable functions with
`∫ Φ(‖f i‖) ≤ C < ∞` for a superlinear `Φ` is uniformly integrable. -/
theorem unifIntegrable_of_lintegral_ofReal_le {Φ : ℝ → ℝ}
    (hΦ : Tendsto (fun t ↦ Φ t / t) atTop atTop) {f : ι → α → F}
    (hfm : ∀ i, AEStronglyMeasurable (f i) μ) {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hf : ∀ i, ∫⁻ a, ENNReal.ofReal (Φ ‖f i a‖) ∂μ ≤ C) : UnifIntegrable f 1 μ := by
  refine unifIntegrable_iff.2 fun ε hε ↦ ?_
  obtain ⟨T, hT⟩ := exists_setLIntegral_enorm_le_mul_add hΦ hC hf
    (ENNReal.half_pos hε.ne').ne'
  obtain ⟨δ, hδ, hδT⟩ := ENNReal.exists_nnreal_pos_mul_lt ENNReal.coe_ne_top
    (ENNReal.half_pos hε.ne').ne'
  refine ⟨δ, by exact_mod_cast hδ, fun i s hs ↦ ?_⟩
  rw [eLpNorm_one_eq_lintegral_eNorm (hfm i).restrict]
  calc ∫⁻ a in s, ‖f i a‖ₑ ∂μ ≤ T * μ s + ε / 2 := hT i s
    _ ≤ δ * T + ε / 2 := by
        rw [mul_comm (δ : ℝ≥0∞)]
        gcongr
    _ ≤ ε / 2 + ε / 2 := by gcongr
    _ = ε := ENNReal.add_halves ε

/-- **De la Vallée Poussin's criterion on a finite measure space.** A family of a.e.
strongly measurable functions with uniformly bounded integrals of a superlinear function
of their norms is uniformly integrable, including a uniform bound on their L¹ norms. -/
theorem uniformIntegrable_of_lintegral_ofReal_le [IsFiniteMeasure μ] {Φ : ℝ → ℝ}
    (hΦ : Tendsto (fun t ↦ Φ t / t) atTop atTop) {f : ι → α → F}
    (hfm : ∀ i, AEStronglyMeasurable (f i) μ) {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hf : ∀ i, ∫⁻ a, ENNReal.ofReal (Φ ‖f i a‖) ∂μ ≤ C) : UniformIntegrable f 1 μ := by
  refine ⟨unifIntegrable_of_lintegral_ofReal_le hΦ hfm hC hf, ?_⟩
  obtain ⟨T, hT⟩ := exists_setLIntegral_enorm_le_mul_add hΦ hC hf (ε := 1) one_ne_zero
  have hfinite : (T : ℝ≥0∞) * μ univ + 1 < ∞ := by finiteness
  apply lt_of_le_of_lt (iSup_le fun i ↦ ?_) hfinite
  simpa only [eLpNorm_one_eq_lintegral_eNorm (hfm i), Measure.restrict_univ] using hT i univ

/-- On a finite measure space, a uniform integral bound on a superlinear function of the
norms turns convergence in measure into convergence of Bochner integrals. Measurability
and the bound are required only eventually along the filter. No integrability assumption on
the limit is needed. -/
theorem tendsto_integral_of_lintegral_ofReal_le [NormedSpace ℝ F] [IsFiniteMeasure μ]
    {Φ : ℝ → ℝ} (hΦ : Tendsto (fun t ↦ Φ t / t) atTop atTop) {f : ι → α → F}
    {l : Filter ι}
    (hfm : ∀ᶠ i in l, AEStronglyMeasurable (f i) μ) {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hf : ∀ᶠ i in l, ∫⁻ a, ENNReal.ofReal (Φ ‖f i a‖) ∂μ ≤ C) {g : α → F}
    (hlim : TendstoInMeasure μ f l g) :
    Tendsto (fun i ↦ ∫ x, f i x ∂μ) l (𝓝 (∫ x, g x ∂μ)) := by
  -- Positive rational thresholds suffice, so pass to a countably generated coarser filter.
  let A : Set ι := {i | AEStronglyMeasurable (f i) μ ∧
    ∫⁻ a, ENNReal.ofReal (Φ ‖f i a‖) ∂μ ≤ C}
  let tail (ε : ℝ) (i : ι) := μ {x | ε ≤ ‖f i x - g x‖}
  let l' := 𝓟 A ⊓ ⨅ q : {q : ℚ // 0 < q}, comap (tail q.val) (𝓝 0)
  have hl : l ≤ l' := le_inf (le_principal_iff.mpr (hfm.and hf)) <| le_iInf fun q ↦
    tendsto_iff_comap.mp (tendstoInMeasure_iff_norm.mp hlim q.val (by exact_mod_cast q.property))
  have hlim₀ : TendstoInMeasure μ f l' g := by
    refine tendstoInMeasure_iff_norm.mpr fun ε hε ↦ ?_
    obtain ⟨q, hq, hqε⟩ := exists_rat_btwn hε
    let r : {q : ℚ // 0 < q} := ⟨q, by exact_mod_cast hq⟩
    have hr : Tendsto (tail q) l' (𝓝 0) :=
      tendsto_comap.mono_left (inf_le_right.trans (iInf_le _ r))
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hr (fun _ ↦ zero_le)
      (fun _ ↦ measure_mono fun _ hx ↦ hqε.le.trans hx)
  suffices h : Tendsto (fun i ↦ ∫ x, f i x ∂μ) l' (𝓝 (∫ x, g x ∂μ)) from h.mono_left hl
  refine tendsto_iff_seq_tendsto.2 fun u hu ↦ ?_
  have hA : A ∈ l' := le_principal_iff.mp inf_le_left
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hu.eventually_mem hA)
  have hm (k : ℕ) := (hN (k + N) (Nat.le_add_left N k)).1
  have hb (k : ℕ) := (hN (k + N) (Nat.le_add_left N k)).2
  have hlim' : TendstoInMeasure μ (fun k ↦ f (u (k + N))) atTop g :=
    hlim₀.comp (hu.comp (tendsto_add_atTop_nat N))
  have hUI' := uniformIntegrable_of_lintegral_ofReal_le hΦ hm hC hb
  have hL1 := tendsto_Lp_finite_of_tendstoInMeasure le_rfl ENNReal.one_ne_top
    hm (hUI'.memLp_of_tendstoInMeasure hlim') hUI'.unifIntegrable hlim'
  exact (tendsto_add_atTop_iff_nat N).1 (tendsto_integral_of_L1' g
    (Eventually.of_forall fun k ↦ memLp_one_iff_integrable.mp (hUI'.memLp k)) hL1)

/-- On a finite measure space, convergence in measure of eventually square-integrable
(`MemLp · 2 μ`) functions with eventually uniformly bounded integrals of squared norms
(`∫ x, ‖f i x‖ ^ 2 ∂μ ≤ B`) implies convergence of Bochner integrals. No integrability
assumption on the limit is needed. -/
theorem tendsto_integral_of_integral_norm_sq_le [NormedSpace ℝ F] [IsFiniteMeasure μ]
    {f : ι → α → F} {l : Filter ι} {g : α → F}
    (hf : ∀ᶠ i in l, MemLp (f i) 2 μ) {B : ℝ}
    (hbound : ∀ᶠ i in l, ∫ x, ‖f i x‖ ^ 2 ∂μ ≤ B)
    (hlim : TendstoInMeasure μ f l g) :
    Tendsto (fun i ↦ ∫ x, f i x ∂μ) l (𝓝 (∫ x, g x ∂μ)) := by
  have hΦ : Tendsto (fun x : ℝ ↦ x ^ 2 / x) atTop atTop :=
    tendsto_id.congr fun x ↦ by simp only [id_eq, pow_two, mul_self_div_self]
  have hbound' : ∀ᶠ i in l,
      ∫⁻ x, ENNReal.ofReal (‖f i x‖ ^ 2) ∂μ ≤ ENNReal.ofReal B := by
    filter_upwards [hf, hbound] with i hi hbi
    rw [← ofReal_integral_eq_lintegral_ofReal (hi.integrable_norm_pow (by norm_num))
      (Eventually.of_forall fun _ ↦ sq_nonneg _)]
    exact ENNReal.ofReal_le_ofReal hbi
  exact tendsto_integral_of_lintegral_ofReal_le hΦ (hf.mono fun _ hi ↦ hi.aestronglyMeasurable)
    ENNReal.ofReal_ne_top hbound' hlim

end TauCeti
