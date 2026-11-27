/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import TauCeti.Analysis.Normed.Group.Real
import TauCeti.MeasureTheory.Integral.Bochner.Basic

/-!
# Continuity of parametric integrals with compactly supported integrand

Mathlib's `continuousOn_integral_of_compact_support` gives continuity of a parametric integral on
a set. This file records its global form: a jointly continuous integrand which vanishes unless the
integration variable lies in a fixed compact set has a continuous parametric integral, against any
measure which is finite on compact sets. It also records that the indicator function of a
bounded interval `[a, b)` is integrable against a locally finite measure, that the integral of
`|f|` over a set splits along the sign of `f`, that an integral over a set splits along finitely
many disjoint measurable subsets, that an almost everywhere positive function has positive
integral, bounds for the integral of the reciprocal of a function bounded below by a positive
constant, the bound `∫_s ψ² ≤ K² |B|` for a function bounded by `K` and supported in a closed
ball `B`, the bound `∫ ‖f‖ ≤ K |s|` for a function bounded by `K` on a set `s` of finite measure
and vanishing off it, the integral of `Φ x (f₀ x)` for an almost everywhere zero
extension `f₀` of `f` from `s` and an integrand `Φ` vanishing at `0`, the pairing
`∫ h φ = ∫_B (φ - c) h` of a function `h` of integral zero vanishing off `B`, and that a
continuous square-integrable function `h` with `∫ conj (h x) * h x = 0` vanishes, against a
measure positive on nonempty open sets.
It also bounds the integral over a measurable set `S` by integrals over unions with disjoint sets,
that a pointwise bound `m ≤ K σ` on `[a, a + K]` gives `m ≤ ∫_a^{a+K} σ`, that a pointwise
bound `0 ≤ f ≤ c₁ g₁ + c₂ g₂` integrates to the same bound for the integrals, and turns a bound
on the Lebesgue integral of a nonnegative function into integrability and a bound on its Bochner
integral.

## Main statements

* `TauCeti.continuous_integral_of_compact_support`: the parametric integral of a jointly
  continuous integrand which vanishes unless `r ∈ K`, for compact `K`, is continuous.
* `TauCeti.integrable_indicator_Ico_one`: the indicator function of `[a, b)` is integrable.
* `TauCeti.setIntegral_abs_eq_sub`: the integral of `|f|` over `s` is the integral of `f` over the
  part of `s` where `f ≥ 0` minus its integral over the rest of `s`.
* `TauCeti.setIntegral_pos_of_ae_pos`: an integrable function that is almost everywhere positive
  on a set of positive measure has positive integral over it.
* `TauCeti.div_le_setIntegral_inv` and `TauCeti.setIntegral_inv_pos`: if `λ ≤ a ≤ M` almost
  everywhere on a set `s` of finite measure, with `λ > 0`, then `∫_s a⁻¹ ≥ μ(s) / M`; the lower
  bound `a ≥ λ` alone gives `∫_s a⁻¹ > 0` when `μ s > 0`.
* `TauCeti.le_setIntegral_Icc_add_of_le_mul`: if `m ≤ K σ` on `[a, a + K]`, with `K > 0`, then
  `m ≤ ∫_a^{a+K} σ`.
* `TauCeti.setIntegral_le_mul_add_mul_of_le`: a pointwise bound `0 ≤ f ≤ c₁ g₁ + c₂ g₂` on a
  measurable set integrates to `∫_s f ≤ c₁ ∫_s g₁ + c₂ ∫_s g₂`.
* `TauCeti.setIntegral_sq_le_of_support_subset_closedBall`: a function bounded by `K` on a closed
  ball `B` and vanishing off it has `∫_s ψ² ≤ K² |B|` over every set `s`.
* `TauCeti.integral_norm_le_of_forall_compl_eq_zero`: a function bounded by `K` on a set `s` of
  finite measure and vanishing off it has `∫ ‖f‖ ≤ K |s|`.
* `TauCeti.integral_eq_setIntegral_of_ae_eq_indicator`: if `f₀` is almost everywhere the zero
  extension `1_s f` and `Φ x 0 = 0`, then `∫ Φ x (f₀ x) = ∫_s Φ x (f x)`.
* `TauCeti.integral_mul_eq_setIntegral_sub_mul`: if `h` vanishes off `B` and has integral zero,
  then `∫ h φ = ∫_B (φ - c) h` for every constant `c`.
* `TauCeti.setIntegral_norm_sq_le_setIntegral_add`: if `g = η` off a measurable set `T`, the
  `L²` norm of `η` on any set `S` is at most that of `g` there plus the `L²` norm of `η` on `T`.
* `TauCeti.integrableOn_sin_of_measure_ne_top`,
  `TauCeti.integrableOn_exp_ofReal_mul_I_of_measure_ne_top`: the sine and the unit-circle
  exponential `exp (t x I)` are integrable on a set of finite measure.
* `MeasureTheory.setIntegral_eq_setIntegral_sdiff_iUnion_add_sum`: an integral over `T` splits along
  finitely many pairwise disjoint measurable subsets of `T` and the rest of `T`.
* `MeasureTheory.setIntegral_mul_le_mul_setIntegral_abs`: the pairing of an integrable `f` on `Ω`
  with a function `g` bounded by `S` on `V ⊆ Ω` is at most `S ∫_Ω |f|`.
* `MeasureTheory.setLIntegral_enorm_sq_eq_ofReal_setIntegral`: the Lebesgue integral of `‖f‖ₑ ^ 2`
  over `A` is `ofReal` of the Bochner integral of `‖f‖ ^ 2`, and
  `MeasureTheory.setLIntegral_enorm_sq_le_ofReal` the corresponding bound.
* `MeasureTheory.integrableOn_and_setIntegral_le_of_setLIntegral_ofReal_le`: a function nonnegative
  on `Ω ⊆ S` whose Lebesgue integral over `S` is at most `ENNReal.ofReal E` is integrable on `Ω`
  with Bochner integral at most `E`.
* `Continuous.eq_zero_of_integral_conj_mul_self_eq_zero`: a continuous square-integrable function
  `h` with `∫ conj (h x) * h x = 0` vanishes.
* `MeasureTheory.norm_setIntegral_le_add_of_disjoint`: the integral over `S` is bounded by the
  integrals over `H ∪ (S ∪ T)`, `H` and `T`, for disjoint `H`, `S`, `T`.
* `ContinuousOn.integrableOn_insertNth_Icc`: continuity on a closed box `Set.Icc a b` gives
  integrability on every coordinate slice `x i = c` (`c ∈ Set.Icc (a i) (b i)`) against any
  measure finite on compact sets.
-/

public section

open MeasureTheory Function Set
open scoped ENNReal

namespace TauCeti

/-- The parametric integral `s ↦ ∫ r, F s r` of a jointly continuous integrand which vanishes
unless `r ∈ K`, for compact `K`, is continuous. -/
theorem continuous_integral_of_compact_support {X Y E : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [MeasurableSpace Y] [OpensMeasurableSpace Y] [NormedAddCommGroup E]
    [NormedSpace ℝ E] {F : X → Y → E} {K : Set Y} (μ : Measure Y) [IsFiniteMeasureOnCompacts μ]
    (hK : IsCompact K) (hFc : Continuous (uncurry F)) (hF : ∀ s r, F s r ≠ 0 → r ∈ K) :
    Continuous fun s => ∫ r, F s r ∂μ :=
  continuousOn_univ.mp <| continuousOn_integral_of_compact_support hK hFc.continuousOn
    fun s r _ hr => by_contra fun h => hr (hF s r h)

/-- The indicator function of a bounded interval `[a, b)` is integrable against a locally finite
measure. -/
theorem integrable_indicator_Ico_one {α : Type*} [MeasurableSpace α] [TopologicalSpace α]
    [LinearOrder α] [OrderClosedTopology α] [OpensMeasurableSpace α] [CompactIccSpace α]
    {μ : Measure α} [IsLocallyFiniteMeasure μ] (a b : α) :
    Integrable ((Ico a b).indicator (1 : α → ℝ)) μ :=
  (integrableOn_const measure_Ico_lt_top.ne).integrable_indicator measurableSet_Ico

/-- The integral of `|f|` over a set `s` is the integral of `f` over the part of `s` where `f` is
nonnegative minus the integral of `f` over the part where it is negative. -/
theorem setIntegral_abs_eq_sub {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℝ}
    {s : Set α} (hf : IntegrableOn f s μ) :
    ∫ x in s, |f x| ∂μ = ∫ x in s ∩ {x | 0 ≤ f x}, f x ∂μ - ∫ x in s \ {x | 0 ≤ f x}, f x ∂μ := by
  have hneg : {x | f x < 0} ∩ s = s \ {x | 0 ≤ f x} := by
    ext x
    simp [and_comm]
  simp_rw [← Real.norm_eq_abs]
  rw [integral_norm_eq_pos_sub_neg hf, ← setIntegral_neg_eq_setIntegral_nonpos hf.1,
    Measure.restrict_restrict₀ (aestronglyMeasurable_const.nullMeasurableSet_le hf.1),
    Measure.restrict_restrict₀ (hf.1.nullMeasurableSet_lt aestronglyMeasurable_const),
    inter_comm _ s, hneg]

/-- Perturbing `g` by a constant `c` changes the `L¹` distance over `S` to `f` by at most
the `L¹` norm of `c`. -/
theorem integral_norm_add_const_sub_le {α E : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup E] {S : Set α} {g f : α → E} (c : E) (hS : μ S ≠ ⊤)
    (hg : IntegrableOn g S μ) (hf : IntegrableOn f S μ) :
    (∫ t in S, ‖g t + c - f t‖ ∂μ) ≤ (∫ t in S, ‖g t - f t‖ ∂μ) + ∫ _ in S, ‖c‖ ∂μ := by
  have h1 : Integrable (fun t ↦ ‖g t - f t‖) (μ.restrict S) := (hg.sub hf).norm
  rw [← integral_add h1 (integrableOn_const hS)]
  refine integral_mono ((hg.add (integrableOn_const hS)).sub hf).norm
    ((hg.sub hf).norm.add (integrableOn_const hS)) ?_
  intro t
  dsimp only
  have he : g t + c - f t = (g t - f t) + c := by abel
  rw [he]
  exact norm_add_le _ _

/-- If disjoint parametrizations `Q i` of a domain `D` cover the complement of a set of seams
`Z`, and `g` is injective on `s`, the integral over `g '' s` is the sum of the integrals over the
images `(g ∘ Q i) '' (D ∩ Q i ⁻¹' s)` of the pieces cut out by each parametrization, up to the
transport identity `hpiece` for each piece. The integrand need only be integrable on `g '' s`, and
the seams need only have a null image `g '' (s ∩ Z)`. -/
theorem mul_integral_image_eq_sum_pieces {E M ι : Type*} [MeasurableSpace E] [Fintype ι]
    {Q : ι → E → M} {D : Set E} {Z : Set M} (himage : (⋃ i, Q i '' D) = Zᶜ)
    (hdisj : Pairwise (fun i j ↦ Disjoint (Q i '' D) (Q j '' D))) {g : M → E} {s : Set M}
    (hg : InjOn g s) (μ : Measure E) (hZ : μ (g '' (s ∩ Z)) = 0) {C : E → ℝ}
    (hC : IntegrableOn C (g '' s) μ)
    (c : ℝ) (V : ι → E → ℝ)
    (hT : ∀ i, MeasurableSet ((g ∘ Q i) '' (D ∩ Q i ⁻¹' s)))
    (hpiece : ∀ i, c * ∫ y in (g ∘ Q i) '' (D ∩ Q i ⁻¹' s), C y ∂μ =
      ∫ z in D ∩ Q i ⁻¹' s, V i z ∂μ) :
    c * ∫ y in g '' s, C y ∂μ = ∑ i, ∫ z in D ∩ Q i ⁻¹' s, V i z ∂μ := by
  have hpair : Pairwise (fun i k ↦ Disjoint ((g ∘ Q i) '' (D ∩ Q i ⁻¹' s))
      ((g ∘ Q k) '' (D ∩ Q k ⁻¹' s))) := fun i k hik ↦ by
    simp only [image_comp, image_inter_preimage]
    exact ((hdisj hik).mono inter_subset_left inter_subset_left).image hg inter_subset_right
      inter_subset_right
  have hcover : (⋃ i, (g ∘ Q i) '' (D ∩ Q i ⁻¹' s)) = g '' (s \ Z) := by
    simp only [image_comp, image_inter_preimage]
    rw [← image_iUnion, ← iUnion_inter, himage]
    congr 1
    ext x
    simp only [mem_inter_iff, mem_compl_iff, mem_sdiff]
    tauto
  have hsub : ∀ i, (g ∘ Q i) '' (D ∩ Q i ⁻¹' s) ⊆ g '' s := fun i ↦ by
    rw [image_comp, image_inter_preimage]
    exact image_mono inter_subset_right
  -- The seams contribute only the null image `g '' (s ∩ Z)`.
  have hae : g '' (s \ Z) =ᵐ[μ] g '' s := by
    have hsplit : g '' s = g '' (s \ Z) ∪ g '' (s ∩ Z) := by
      rw [← image_union, sdiff_union_inter]
    rw [hsplit]
    exact (union_ae_eq_left_of_ae_eq_empty (ae_eq_empty.mpr hZ)).symm
  rw [setIntegral_congr_set hae.symm, ← hcover,
    integral_iUnion_fintype hT hpair (fun i ↦ hC.mono_set (hsub i)), Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ ↦ hpiece i

/-- The sine is integrable on a set of finite measure. -/
theorem integrableOn_sin_of_measure_ne_top {ν : Measure ℝ} {s : Set ℝ} (hs : ν s ≠ ∞) :
    IntegrableOn (fun x : ℝ ↦ Real.sin x) s ν := by
  have : IsFiniteMeasure (ν.restrict s) := isFiniteMeasure_restrict.mpr hs
  exact Integrable.of_bound (by fun_prop) 1
    (ae_of_all _ fun x ↦ by simpa using Real.abs_sin_le_one x)

/-- The unit-circle exponential `x ↦ exp (t x I)` is integrable on a set of finite measure. -/
theorem integrableOn_exp_ofReal_mul_I_of_measure_ne_top {ν : Measure ℝ} {s : Set ℝ} (t : ℝ)
    (hs : ν s ≠ ∞) :
    IntegrableOn (fun x : ℝ ↦ Complex.exp ((t * x : ℝ) * Complex.I)) s ν := by
  have : IsFiniteMeasure (ν.restrict s) := isFiniteMeasure_restrict.mpr hs
  exact Integrable.of_bound (by fun_prop) 1 (ae_of_all _ fun x ↦ by
    simpa using (Complex.norm_exp_ofReal_mul_I (t * x)).le)

section Reciprocal

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {s : Set α} {a : α → ℝ} {lam M : ℝ}

/-- A function which is almost everywhere positive on a set `s` of positive measure, and
integrable there, has positive integral over `s`. -/
theorem setIntegral_pos_of_ae_pos {f : α → ℝ} (hs₀ : μ s ≠ 0) (hf : IntegrableOn f s μ)
    (hpos : ∀ᵐ t ∂μ.restrict s, 0 < f t) : 0 < ∫ t in s, f t ∂μ := by
  have hnn : 0 ≤ᵐ[μ.restrict s] f := hpos.mono fun _ ht => ht.le
  refine (integral_nonneg_of_ae hnn).lt_of_ne fun h => hs₀ ?_
  have hF : ∀ᵐ _ ∂μ.restrict s, False :=
    (hpos.and ((integral_eq_zero_iff_of_nonneg_ae hnn hf).1 h.symm)).mono fun _ ht =>
      ht.1.ne' ht.2
  rwa [Filter.eventually_false_iff_eq_bot, ae_eq_bot, Measure.restrict_eq_zero] at hF

/-- If `λ ≤ a ≤ M` almost everywhere on a set `s` of finite measure, with `λ > 0`, then
`∫_s a⁻¹ ≥ μ(s) / M`. -/
theorem div_le_setIntegral_inv (hs : μ s ≠ ∞) (hlam : 0 < lam)
    (ha : AEStronglyMeasurable a (μ.restrict s))
    (haM : ∀ᵐ t ∂μ.restrict s, lam ≤ a t ∧ a t ≤ M) :
    μ.real s / M ≤ ∫ t in s, (a t)⁻¹ ∂μ := by
  have : IsFiniteMeasure (μ.restrict s) := isFiniteMeasure_restrict.2 hs
  have h := integral_mono_ae (integrable_const M⁻¹)
    (Integrable.of_bound ha.aemeasurable.inv.aestronglyMeasurable _
      ((haM.mono fun _ ht => ht.1).norm_inv_le_inv hlam))
    (haM.mono fun t ht => inv_anti₀ (hlam.trans_le ht.1) ht.2)
  rwa [setIntegral_const, smul_eq_mul, ← div_eq_mul_inv] at h

/-- If `a ≥ λ > 0` almost everywhere on a set `s` of positive finite measure, then
`∫_s a⁻¹ > 0`. -/
theorem setIntegral_inv_pos (hs₀ : μ s ≠ 0) (hs : μ s ≠ ∞) (hlam : 0 < lam)
    (ha : AEStronglyMeasurable a (μ.restrict s)) (hlama : ∀ᵐ t ∂μ.restrict s, lam ≤ a t) :
    0 < ∫ t in s, (a t)⁻¹ ∂μ :=
  have : IsFiniteMeasure (μ.restrict s) := isFiniteMeasure_restrict.2 hs
  setIntegral_pos_of_ae_pos hs₀ (Integrable.of_bound ha.aemeasurable.inv.aestronglyMeasurable _
    (hlama.norm_inv_le_inv hlam)) (hlama.mono fun _ ht => inv_pos.2 (hlam.trans_le ht))

end Reciprocal

/-- If `m ≤ K σ(r)` for every `r ∈ [a, a + K]`, with `K > 0` and `σ` integrable there, then `m` is
at most the integral of `σ` over `[a, a + K]`: the average of `σ` over the interval is at least
`m / K`. -/
theorem le_setIntegral_Icc_add_of_le_mul {σ : ℝ → ℝ} {a K m : ℝ} (hK : 0 < K)
    (hσ : IntegrableOn σ (Icc a (a + K))) (hm : ∀ r ∈ Icc a (a + K), m ≤ K * σ r) :
    m ≤ ∫ r in Icc a (a + K), σ r := by
  have h := setIntegral_ge_of_const_le_real measurableSet_Icc (by simp)
    (fun r hr ↦ (div_le_iff₀' hK).2 (hm r hr)) hσ
  simpa [hK.le, hK.ne'] using h

/-- **Integrating a bound by a combination of two functions.** If `0 ≤ f ≤ c₁ g₁ + c₂ g₂` on a
measurable set `s`, with `g₁` and `g₂` integrable on `s`, then
`∫_s f ≤ c₁ ∫_s g₁ + c₂ ∫_s g₂`. -/
theorem setIntegral_le_mul_add_mul_of_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {s : Set α} {f g₁ g₂ : α → ℝ} {c₁ c₂ : ℝ} (hs : MeasurableSet s) (hf : ∀ x ∈ s, 0 ≤ f x)
    (hg₁ : IntegrableOn g₁ s μ) (hg₂ : IntegrableOn g₂ s μ)
    (h : ∀ x ∈ s, f x ≤ c₁ * g₁ x + c₂ * g₂ x) :
    ∫ x in s, f x ∂μ ≤ c₁ * (∫ x in s, g₁ x ∂μ) + c₂ * ∫ x in s, g₂ x ∂μ := by
  rw [← integral_const_mul, ← integral_const_mul,
    ← integral_add (hg₁.const_mul c₁) (hg₂.const_mul c₂)]
  exact integral_mono_of_nonneg (ae_restrict_of_forall_mem hs hf)
    ((hg₁.const_mul c₁).add (hg₂.const_mul c₂)) (ae_restrict_of_forall_mem hs h)

open Metric in
/-- A function bounded by `K` on a closed ball and vanishing off it has `∫_s ψ² ≤ K² |B|` over
every set `s`, where `B` is the closed ball. -/
theorem setIntegral_sq_le_of_support_subset_closedBall {E : Type*} [PseudoMetricSpace E]
    [ProperSpace E] [MeasurableSpace E] [OpensMeasurableSpace E] {mu : Measure E}
    [IsFiniteMeasureOnCompacts mu] {s : Set E} {ψ : E → ℝ} {x₀ : E} {R K : ℝ}
    (hψs : support ψ ⊆ closedBall x₀ R) (hψK : ∀ x ∈ closedBall x₀ R, ‖ψ x‖ ≤ K) :
    ∫ x in s, ψ x ^ 2 ∂mu ≤ K ^ 2 * mu.real (closedBall x₀ R) := by
  have hmeasB : MeasurableSet (closedBall x₀ R) := measurableSet_closedBall
  calc ∫ x in s, ψ x ^ 2 ∂mu
      ≤ ∫ x in s, (closedBall x₀ R).indicator (fun _ => K ^ 2) x ∂mu := by
        refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => by positivity)
          ((integrableOn_const measure_closedBall_lt_top.ne).integrable_indicator
            hmeasB).restrict
          (Filter.Eventually.of_forall fun x => ?_)
        by_cases hx : x ∈ closedBall x₀ R
        · rw [indicator_of_mem hx]
          have := pow_le_pow_left₀ (norm_nonneg _) (hψK x hx) 2
          rwa [Real.norm_eq_abs, sq_abs] at this
        · simp [indicator_of_notMem hx, notMem_support.1 fun hx' => hx (hψs hx')]
    _ ≤ K ^ 2 * mu.real (closedBall x₀ R) := by
        rw [integral_indicator_const _ hmeasB, smul_eq_mul, mul_comm]
        gcongr
        rw [measureReal_restrict_apply hmeasB]
        exact measureReal_mono inter_subset_left measure_closedBall_lt_top.ne

/-- A function bounded by `K` on a set `s` of finite measure and vanishing off it has
`∫ ‖f‖ ≤ K |s|`. -/
theorem integral_norm_le_of_forall_compl_eq_zero {X E : Type*} [MeasurableSpace X]
    {mu : Measure X} [SeminormedAddCommGroup E] {f : X → E} {s : Set X} {K : ℝ}
    (hs : mu s < ∞) (hfK : ∀ x ∈ s, ‖f x‖ ≤ K) (hf0 : ∀ x ∉ s, f x = 0) :
    ∫ x, ‖f x‖ ∂mu ≤ K * mu.real s := by
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by rw [hf0 x hx, norm_zero]]
  exact (Real.le_norm_self _).trans (norm_setIntegral_le_of_norm_le_const hs
    fun x hx => (norm_norm (f x)).trans_le (hfK x hx))

/-- If `f₀` is almost everywhere the zero extension `1_s f` of `f` and `Φ x 0 = 0` for every
`x`, then the integral of `Φ x (f₀ x)` over the whole space is the integral of `Φ x (f x)`
over `s`. -/
theorem integral_eq_setIntegral_of_ae_eq_indicator {X E G : Type*} [MeasurableSpace X] [Zero E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] {μ : Measure X} {s : Set X}
    (hs : NullMeasurableSet s μ) {f f₀ : X → E} (Φ : X → E → G) (hΦ : ∀ x, Φ x 0 = 0)
    (h : f₀ =ᵐ[μ] s.indicator f) :
    ∫ x, Φ x (f₀ x) ∂μ = ∫ x in s, Φ x (f x) ∂μ := by
  rw [← integral_indicator₀ hs]
  refine integral_congr_ae (h.mono fun x hx => ?_)
  by_cases hx' : x ∈ s <;> simp [hx, hx', hΦ]

/-- If `h` vanishes off `B` and has integral zero, its pairing with `φ` only sees `φ - c` on `B`,
for any constant `c`: `∫ h φ = ∫_B (φ - c) h`. -/
theorem integral_mul_eq_setIntegral_sub_mul {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {B : Set α} {h φ : α → ℝ}
    (hh : Integrable h (μ.restrict B)) (hsupp : ∀ᵐ x ∂μ, x ∉ B → h x = 0)
    (hmean : ∫ x, h x ∂μ = 0) (c : ℝ)
    (hint : Integrable (fun x => (φ x - c) * h x) (μ.restrict B)) :
    ∫ x, h x * φ x ∂μ = ∫ x in B, (φ x - c) * h x ∂μ := by
  rw [← setIntegral_eq_integral_of_ae_compl_eq_zero (s := B)
    (by filter_upwards [hsupp] with x hx hxB; rw [hx hxB, zero_mul])]
  calc ∫ x in B, h x * φ x ∂μ = ∫ x in B, ((φ x - c) * h x + c * h x) ∂μ :=
        integral_congr_ae (ae_of_all _ fun x => by ring)
    _ = _ := by
        rw [integral_add hint (hh.const_mul c), integral_const_mul,
          (setIntegral_eq_integral_of_ae_compl_eq_zero hsupp).trans hmean, mul_zero, add_zero]

/-- If `g = η` off a measurable set `T`, then on every set `S` the `L²` norm of `η` is at most
that of `g` plus the `L²` norm of `η` on `T`. -/
theorem setIntegral_norm_sq_le_setIntegral_add {X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] {μ : Measure X} {η g : X → E} {S T : Set X} (hT : MeasurableSet T)
    (hηi : Integrable (fun z ↦ ‖η z‖ ^ 2) μ) (hgi : Integrable (fun z ↦ ‖g z‖ ^ 2) μ)
    (hgη : ∀ z ∉ T, g z = η z) :
    ∫ z in S, ‖η z‖ ^ 2 ∂μ ≤ (∫ z in S, ‖g z‖ ^ 2 ∂μ) + ∫ z in T, ‖η z‖ ^ 2 ∂μ := by
  have hind : Integrable (T.indicator fun z ↦ ‖η z‖ ^ 2) μ := hηi.indicator hT
  calc ∫ z in S, ‖η z‖ ^ 2 ∂μ ≤ ∫ z in S, (‖g z‖ ^ 2 + T.indicator (fun z ↦ ‖η z‖ ^ 2) z) ∂μ := by
        refine setIntegral_mono hηi.integrableOn (hgi.integrableOn.add hind.integrableOn)
          fun z ↦ ?_
        by_cases hz : z ∈ T
        · rw [indicator_of_mem hz]
          linarith [sq_nonneg ‖g z‖]
        · rw [indicator_of_notMem hz, hgη z hz, add_zero]
    _ = (∫ z in S, ‖g z‖ ^ 2 ∂μ) + ∫ z in S, T.indicator (fun z ↦ ‖η z‖ ^ 2) z ∂μ :=
        integral_add hgi.integrableOn hind.integrableOn
    _ ≤ (∫ z in S, ‖g z‖ ^ 2 ∂μ) + ∫ z in T, ‖η z‖ ^ 2 ∂μ := by
        gcongr
        rw [← integral_indicator hT]
        exact setIntegral_le_integral hind (ae_of_all _ (indicator_nonneg fun z _ ↦ by positivity))

end TauCeti

/-- A continuous square-integrable function `h` with `∫ conj (h x) * h x = 0` vanishes, against a
measure positive on nonempty open sets. -/
theorem Continuous.eq_zero_of_integral_conj_mul_self_eq_zero {X 𝕜 : Type*} [TopologicalSpace X]
    [MeasurableSpace X] [RCLike 𝕜] {μ : Measure X}
    [μ.IsOpenPosMeasure] {h : X → 𝕜} (hc : Continuous h) (hL : MemLp h 2 μ)
    (h0 : ∫ x, starRingEnd 𝕜 (h x) * h x ∂μ = 0) : h = 0 := by
  by_contra hne
  obtain ⟨x, hx⟩ := Function.ne_iff.1 hne
  have hpos := MeasureTheory.integral_pos_of_integrable_nonneg_ne_zero (μ := μ) (f :=
    fun x => ‖h x‖ ^ 2)
    (x := x) (by fun_prop) (hL.integrable_norm_pow two_ne_zero) (fun _ => by positivity)
    (by simpa using hx)
  simp_rw [RCLike.conj_mul, ← RCLike.ofReal_pow, integral_ofReal, RCLike.ofReal_eq_zero] at h0
  exact hpos.ne' h0

namespace MeasureTheory

/-- An integral over `T` splits along finitely many pairwise disjoint measurable sets `A i ⊆ T`
into the integral over the rest `T \ ⋃ i, A i` plus the sum of the integrals over the `A i`. -/
theorem setIntegral_eq_setIntegral_sdiff_iUnion_add_sum {α E ι : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype ι] {ν : Measure α} {T : Set α}
    {A : ι → Set α} (hAm : ∀ i, MeasurableSet (A i)) (hAd : Pairwise (Disjoint on A))
    (hAT : ∀ i, A i ⊆ T) {f : α → E} (hf : IntegrableOn f T ν) :
    ∫ x in T, f x ∂ν = (∫ x in T \ ⋃ i, A i, f x ∂ν) + ∑ i, ∫ x in A i, f x ∂ν := by
  conv_lhs => rw [← sdiff_union_of_subset (iUnion_subset hAT)]
  rw [setIntegral_union disjoint_sdiff_left (MeasurableSet.iUnion hAm)
    (hf.mono_set sdiff_subset) (hf.mono_set (iUnion_subset hAT)),
    integral_iUnion_fintype hAm hAd fun i ↦ hf.mono_set (hAT i)]

/-- The pairing of an integrable function `f` on `Ω` with a function `g` bounded by `S` on
`V ⊆ Ω` is at most `S ∫_Ω |f|`. -/
theorem setIntegral_mul_le_mul_setIntegral_abs {α : Type*} [MeasurableSpace α]
    {ν : Measure α} {V Ω : Set α} {f g : α → ℝ} {S : ℝ} (hVΩ : V ⊆ Ω)
    (hf : IntegrableOn f Ω ν) (hS0 : 0 ≤ S) (hgS : ∀ᵐ x ∂ν.restrict V, |g x| ≤ S) :
    ∫ x in V, f x * g x ∂ν ≤ S * ∫ x in Ω, |f x| ∂ν := by
  have hbound : ∀ᵐ x ∂ν.restrict V, ‖f x * g x‖ ≤ S * |f x| := by
    filter_upwards [hgS] with x hx
    rw [Real.norm_eq_abs, abs_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right hx (abs_nonneg _)
  have hfV : IntegrableOn f V ν := hf.mono_set hVΩ
  have hΔV : IntegrableOn (fun x => S * |f x|) V ν := hfV.abs.const_mul S
  calc _ ≤ ‖∫ x in V, f x * g x ∂ν‖ := Real.le_norm_self _
    _ ≤ ∫ x in V, S * |f x| ∂ν := norm_integral_le_of_norm_le hΔV hbound
    _ = S * ∫ x in V, |f x| ∂ν := integral_const_mul S _
    _ ≤ S * ∫ x in Ω, |f x| ∂ν :=
        mul_le_mul_of_nonneg_left (setIntegral_mono_set hf.abs
          (ae_of_all _ fun _ => abs_nonneg _) (ae_of_all _ hVΩ)) hS0

/-- The Lebesgue integral of `‖f‖ₑ ^ 2` over `A` is the `ENNReal.ofReal` of the Bochner integral of
`‖f‖ ^ 2`, when `‖f‖ ^ 2` is integrable on `A`. -/
theorem setLIntegral_enorm_sq_eq_ofReal_setIntegral {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] {ν : Measure α} {A : Set α} {f : α → E}
    (hf : IntegrableOn (fun x => ‖f x‖ ^ 2) A ν) :
    ∫⁻ x in A, ‖f x‖ₑ ^ 2 ∂ν = ENNReal.ofReal (∫ x in A, ‖f x‖ ^ 2 ∂ν) := by
  rw [ofReal_integral_eq_lintegral_ofReal hf (ae_of_all _ fun _ => by positivity)]
  refine lintegral_congr fun x => ?_
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

/-- A bound on the Bochner integral of `‖f‖ ^ 2` over `A` bounds the Lebesgue integral of
`‖f‖ₑ ^ 2`. -/
theorem setLIntegral_enorm_sq_le_ofReal {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] {ν : Measure α} {A : Set α} {f : α → E} {c : ℝ}
    (hf : IntegrableOn (fun x => ‖f x‖ ^ 2) A ν) (h : ∫ x in A, ‖f x‖ ^ 2 ∂ν ≤ c) :
    ∫⁻ x in A, ‖f x‖ₑ ^ 2 ∂ν ≤ ENNReal.ofReal c :=
  (setLIntegral_enorm_sq_eq_ofReal_setIntegral hf).trans_le (ENNReal.ofReal_le_ofReal h)

/-- Let `f` be almost everywhere strongly measurable and almost everywhere nonnegative on `Ω ⊆ S`.
If the Lebesgue integral of `ENNReal.ofReal ∘ f` over `S` is at most `ENNReal.ofReal E` with
`E ≥ 0`, then `f` is integrable on `Ω` and its Bochner integral over `Ω` is at most `E`. -/
theorem integrableOn_and_setIntegral_le_of_setLIntegral_ofReal_le {α : Type*}
    [MeasurableSpace α] {ν : Measure α} {S Ω : Set α} {f : α → ℝ}
    (hf : AEStronglyMeasurable f (ν.restrict Ω)) (hf0 : 0 ≤ᵐ[ν.restrict Ω] f) (hΩS : Ω ⊆ S)
    {E : ℝ} (hE0 : 0 ≤ E) (hE : ∫⁻ x in S, ENNReal.ofReal (f x) ∂ν ≤ ENNReal.ofReal E) :
    IntegrableOn f Ω ν ∧ ∫ x in Ω, f x ∂ν ≤ E := by
  have h := TauCeti.MeasureTheory.integrable_and_integral_le_of_lintegral_ofReal_le hf hf0
    (E := E.toNNReal) ((lintegral_mono_set hΩS).trans hE)
  exact ⟨h.1, h.2.trans_eq (Real.coe_toNNReal _ hE0)⟩

variable {α : Type*} {m : MeasurableSpace α} {μ : Measure α} {E : Type*} [NormedAddCommGroup E]
  [NormedSpace ℝ E]

/-- If `H`, `S` and `T` are disjoint, with `S` and `T` measurable, then the integral of `f` over `S`
is bounded by its integrals over `H ∪ (S ∪ T)`, `H` and `T`. -/
theorem norm_setIntegral_le_add_of_disjoint {f : α → E} {H S T : Set α}
    (hf : IntegrableOn f (H ∪ (S ∪ T)) μ)
    (hS : MeasurableSet S) (hT : MeasurableSet T) (hHST : Disjoint H (S ∪ T))
    (hST : Disjoint S T) :
    ‖∫ x in S, f x ∂μ‖ ≤
      ‖∫ x in H ∪ (S ∪ T), f x ∂μ‖ + ‖∫ x in H, f x ∂μ‖ + ‖∫ x in T, f x ∂μ‖ := by
  have hfH : IntegrableOn f H μ := hf.mono_set subset_union_left
  have hfS : IntegrableOn f S μ := hf.mono_set (subset_union_left.trans subset_union_right)
  have hfT : IntegrableOn f T μ := hf.mono_set (subset_union_right.trans subset_union_right)
  rw [setIntegral_union hHST (hS.union hT) hfH (hfS.union hfT), setIntegral_union hST hT hfS hfT]
  set a := ∫ x in H, f x ∂μ
  set b := ∫ x in S, f x ∂μ
  set c := ∫ x in T, f x ∂μ
  calc ‖b‖ = ‖a + (b + c) - a - c‖ := by congr 1; abel
    _ ≤ ‖a + (b + c) - a‖ + ‖c‖ := norm_sub_le _ _
    _ ≤ ‖a + (b + c)‖ + ‖a‖ + ‖c‖ := by gcongr; exact norm_sub_le _ _

end MeasureTheory

/-- Continuity of `f` on the closed box `Set.Icc a b` gives integrability on every slice `x i = c`
for `c ∈ Set.Icc (a i) (b i)`, against any measure finite on compact sets. -/
theorem ContinuousOn.integrableOn_insertNth_Icc {n : ℕ} {α : Fin (n + 1) → Type*}
    [∀ j, Preorder (α j)] [∀ j, TopologicalSpace (α j)]
    {E : Type*} [NormedAddCommGroup E]
    {a b : ∀ j, α j} {f : (∀ j, α j) → E}
    (hf : ContinuousOn f (Icc a b)) (i : Fin (n + 1))
    [MeasurableSpace (∀ j, α (i.succAbove j))]
    [OpensMeasurableSpace (∀ j, α (i.succAbove j))]
    [CompactIccSpace (∀ j, α (i.succAbove j))] [T2Space (∀ j, α (i.succAbove j))]
    {μ : Measure (∀ j, α (i.succAbove j))} [IsFiniteMeasureOnCompacts μ]
    {c : α i} (hc : c ∈ Icc (a i) (b i)) :
    IntegrableOn (fun x ↦ f (i.insertNth c x))
      (Icc (fun j ↦ a (i.succAbove j)) (fun j ↦ b (i.succAbove j))) μ :=
  (hf.comp (continuousOn_const.finInsertNth i continuousOn_id) fun _ hx ↦
    Fin.insertNth_mem_Icc.mpr ⟨hc, hx⟩).integrableOn_Icc
