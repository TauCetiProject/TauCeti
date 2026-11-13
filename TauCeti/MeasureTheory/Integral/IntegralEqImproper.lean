/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Derivatives of improper tail integrals

For an integrable function `f` on `(a, ∞)`, its tail integral `t ↦ ∫ s in Ioi t, f s`
has strict derivative `-f t` at each `t > a` where `f` is continuous. If `f` is continuous on
the whole ray, the derivative identity also gives a formula for every higher iterated
derivative. These results apply to Banach-space-valued integrands and support differential
closure arguments for improper integrals.

For a real function `g` integrable and continuous on `(x, ∞)`, with tail integral
`Ψ v = ∫ u in Ioi v, g u`, the product `g * Ψ ^ k` is integrable on `(x, ∞)`
(`MeasureTheory.IntegrableOn.integrableOn_mul_pow_integral_Ioi`) with integral
`Ψ x ^ (k + 1) / (k + 1)` (`MeasureTheory.IntegrableOn.integral_Ioi_mul_pow_integral_Ioi`).

For a compactly supported `C¹` map `u` on a real normed space, integrating its derivative along a
ray from `w` recovers `-u w` (`HasCompactSupport.integral_Ioi_fderiv_apply_ray`).

If nonnegative functions `f` and `g` satisfy `∫_{φ i} f ≤ ∫_{φ i} g + e i` along an exhaustion `φ`
with errors `e i → 0`, and `g` is integrable, then `f` is integrable with `∫ f ≤ ∫ g`
(`MeasureTheory.AECover.integrable_and_integral_le_of_setIntegral_le_add`). For the truncations
`[-n, n] × T` of a strip `ℝ × T` this is
`TauCeti.integrableOn_univ_prod_and_setIntegral_le_of_setIntegral_Icc_prod_le_add`.

A nonnegative function whose integrals over the preimages of the balls `closedBall x₀ (r i)`
under a continuous map converge as the radii `r i` tend to infinity has the limit as its integral
over the whole space (`TauCeti.lintegral_ofReal_eq_of_tendsto_setIntegral_closedBall`). For
example, the plane `ℝ × ℝ` is exhausted by the Euclidean discs `{‖w‖ ≤ r}` of `ℂ`.

## References

* Mathlib's `intervalIntegral.integral_Ioi_sub_Ioi'`,
  `intervalIntegral.integral_hasStrictDerivAt_right` and
  `HasCompactSupport.integral_Ioi_deriv_eq`.
-/

public section

open Set Filter intervalIntegral
open scoped Topology

namespace MeasureTheory.IntegrableOn

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable {f : ℝ → E} {a t : ℝ}

/-- At a continuity point strictly inside an integrable ray, the tail integral is strictly
differentiable with derivative equal to the negated integrand. -/
theorem hasStrictDerivAt_integral_Ioi (hint : IntegrableOn f (Ioi a)) (hcont : ContinuousAt f t)
    (ht : a < t) : HasStrictDerivAt (fun u ↦ ∫ s in Ioi u, f s) (-f t) t := by
  have hfinite : HasStrictDerivAt (fun u ↦ ∫ s in t..u, f s) (f t) t :=
    integral_hasStrictDerivAt_right IntervalIntegrable.refl
      (AEStronglyMeasurable.stronglyMeasurableAtFilter_of_mem
        hint.aestronglyMeasurable (Ioi_mem_nhds ht)) hcont
  have heq : (fun u ↦ (∫ s in Ioi t, f s) - ∫ s in t..u, f s) =ᶠ[𝓝 t]
      (fun u ↦ ∫ s in Ioi u, f s) := by
    filter_upwards [Ioi_mem_nhds ht] with u hu
    rw [← integral_Ioi_sub_Ioi' (hint.mono_set (Ioi_subset_Ioi ht.le))
      (hint.mono_set (Ioi_subset_Ioi hu.le)), sub_sub_cancel]
  exact (hfinite.const_sub (∫ s in Ioi t, f s)).congr_of_eventuallyEq heq

/-- At a continuity point strictly inside an integrable ray, the tail integral has derivative
equal to the negated integrand. -/
theorem hasDerivAt_integral_Ioi (hint : IntegrableOn f (Ioi a)) (hcont : ContinuousAt f t)
    (ht : a < t) : HasDerivAt (fun u ↦ ∫ s in Ioi u, f s) (-f t) t :=
  (hint.hasStrictDerivAt_integral_Ioi hcont ht).hasDerivAt

/-- The derivative of an improper tail integral is the negated integrand at each continuity
point strictly inside the integrable ray. -/
theorem deriv_integral_Ioi (hint : IntegrableOn f (Ioi a)) (hcont : ContinuousAt f t)
    (ht : a < t) : deriv (fun u ↦ ∫ s in Ioi u, f s) t = -f t :=
  (hint.hasDerivAt_integral_Ioi hcont ht).deriv

/-- For a continuous integrand on an integrable ray, the derivative of order `n + 1` of its
tail integral is the negated derivative of order `n` of the integrand at each interior point.
The identity concerns total iterated derivatives and does not assume higher smoothness. -/
theorem iteratedDeriv_integral_Ioi (hint : IntegrableOn f (Ioi a))
    (hcont : ContinuousOn f (Ioi a)) (n : ℕ) (ht : a < t) :
    iteratedDeriv (n + 1) (fun u ↦ ∫ s in Ioi u, f s) t = -iteratedDeriv n f t := by
  have heq : deriv (fun u ↦ ∫ s in Ioi u, f s) =ᶠ[𝓝 t] (fun u ↦ -f u) := by
    filter_upwards [Ioi_mem_nhds ht] with u hu
    exact hint.deriv_integral_Ioi (hcont.continuousAt (isOpen_Ioi.mem_nhds hu)) hu
  rw [iteratedDeriv_succ', heq.iteratedDeriv_eq n, iteratedDeriv_fun_neg]

section Real

variable {g : ℝ → ℝ} {x : ℝ}

/-- If `g` is integrable on `(x, ∞)` and continuous there, then so is `g v * Ψ v ^ k` for the
tail integral `Ψ v = ∫ u in Ioi v, g u`, which is bounded by `∫ u in Ioi x, |g u|`. -/
theorem integrableOn_mul_pow_integral_Ioi (hint : IntegrableOn g (Ioi x))
    (hcont : ContinuousOn g (Ioi x)) (k : ℕ) :
    IntegrableOn (fun v ↦ g v * (∫ u in Ioi v, g u) ^ k) (Ioi x) := by
  have hΨ : ContinuousOn (fun v ↦ ∫ u in Ioi v, g u) (Ioi x) :=
    hint.continuousOn_Ici_primitive_Ioi.mono Ioi_subset_Ici_self
  refine Integrable.mono' (hint.norm.mul_const ((∫ u in Ioi x, ‖g u‖) ^ k))
    ((hcont.mul (hΨ.pow k)).aestronglyMeasurable measurableSet_Ioi) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
  rw [norm_mul, norm_pow]
  gcongr
  exact (norm_integral_le_integral_norm _).trans (setIntegral_mono_set hint.norm
    (ae_of_all _ fun _ ↦ norm_nonneg _) (Ioi_subset_Ioi hv.le).eventuallySubset)

/-- For `g` integrable and continuous on `(x, ∞)`, with tail integral
`Ψ v = ∫ u in Ioi v, g u`, the integral of `g * Ψ ^ k` over `(x, ∞)` is
`Ψ x ^ (k + 1) / (k + 1)`, since `-Ψ ^ (k + 1) / (k + 1)` is a primitive of `g * Ψ ^ k`
tending to `0` at infinity. This is the estimate behind the factorial decay of Picard iterates
of Volterra integral equations on a half-line. -/
theorem integral_Ioi_mul_pow_integral_Ioi (hint : IntegrableOn g (Ioi x))
    (hcont : ContinuousOn g (Ioi x)) (k : ℕ) :
    ∫ v in Ioi x, g v * (∫ u in Ioi v, g u) ^ k = (∫ u in Ioi x, g u) ^ (k + 1) / (k + 1) := by
  set Ψ : ℝ → ℝ := fun v ↦ ∫ u in Ioi v, g u
  have hderiv : ∀ y ∈ Ioi x, HasDerivAt (fun v ↦ -(Ψ v ^ (k + 1) / (k + 1))) (g y * Ψ y ^ k) y :=
    fun y hy ↦ by
      convert ((HasDerivAt.pow (hint.hasDerivAt_integral_Ioi
        (hcont.continuousAt (isOpen_Ioi.mem_nhds hy)) hy) (k + 1)).div_const ((k : ℝ) + 1)).neg
        using 1
      push_cast
      field_simp
      ring
  have htend : Tendsto Ψ atTop (𝓝 0) := by
    have := (intervalIntegral_tendsto_integral_Ioi x hint tendsto_id).const_sub (Ψ x)
    rw [sub_self] at this
    refine this.congr' ?_
    filter_upwards [eventually_ge_atTop x] with y hy
    rw [id, ← integral_Ioi_sub_Ioi hint hy, sub_sub_cancel]
  have hcontΨ : ContinuousWithinAt (fun v ↦ -(Ψ v ^ (k + 1) / (k + 1))) (Ici x) x :=
    (((hint.continuousOn_Ici_primitive_Ioi x self_mem_Ici).pow (k + 1)).div_const _).neg
  rw [integral_Ioi_of_hasDerivAt_of_tendsto hcontΨ hderiv
    (hint.integrableOn_mul_pow_integral_Ioi hcont k)
    (((htend.pow (k + 1)).div_const ((k : ℝ) + 1)).neg)]
  simp [Ψ]

end Real

end MeasureTheory.IntegrableOn

section Ray

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- Integrating the derivative of a compactly supported `C¹` map `u` along the ray from `w` in a
nonzero direction `e` recovers `-u w`. This is the directional form of
`HasCompactSupport.integral_Ioi_deriv_eq`, for the restriction `r ↦ u (w + r • e)` of `u` to the
line through `w` in direction `e`. -/
theorem HasCompactSupport.integral_Ioi_fderiv_apply_ray {u : E → F}
    (hc : HasCompactSupport u) (hu : ContDiff ℝ 1 u) (w : E) {e : E} (he : e ≠ 0) :
    ∫ r in Ioi (0 : ℝ), fderiv ℝ u (w + r • e) e = -u w := by
  have hline : HasCompactSupport fun r : ℝ => u (w + r • e) :=
    hc.comp_isClosedEmbedding
      ((Homeomorph.addLeft w).isClosedEmbedding.comp (isClosedEmbedding_smul_left he))
  have hderiv (r : ℝ) : deriv (fun r : ℝ => u (w + r • e)) r = fderiv ℝ u (w + r • e) e := by
    simpa [Function.comp_def] using
      ((hu.differentiable one_ne_zero _).hasFDerivAt.comp_hasDerivAt r
        (((hasDerivAt_id' r).smul_const e).const_add w)).deriv
  have h := hline.integral_Ioi_deriv_eq (f := fun r : ℝ => u (w + r • e))
    (hu.comp (by fun_prop : ContDiff ℝ 1 fun r : ℝ => w + r • e)) 0
  simpa only [hderiv, zero_smul, add_zero] using h

end Ray

namespace MeasureTheory.AECover

variable {α ι : Type*} [MeasurableSpace α] {μ : Measure α} {l : Filter ι} [l.NeBot]
  [l.IsCountablyGenerated] {φ : ι → Set α}

/-- **Integral bounds from an exhaustion.** Let `φ` cover `μ`-almost everything along `l`, and
let `f` and `g` be almost everywhere nonnegative, with `g` integrable and `f` integrable on each
`φ i`. If eventually `∫_{φ i} f ≤ ∫_{φ i} g + e i` with errors `e i → 0`, then `f` is integrable
and `∫ f ≤ ∫ g`. -/
theorem integrable_and_integral_le_of_setIntegral_le_add (hφ : AECover μ l φ) {f g : α → ℝ}
    {e : ι → ℝ} (hf : 0 ≤ᵐ[μ] f) (hg : 0 ≤ᵐ[μ] g) (hfi : ∀ i, IntegrableOn f (φ i) μ)
    (hgi : Integrable g μ) (he : Tendsto e l (𝓝 0))
    (hle : ∀ᶠ i in l, ∫ x in φ i, f x ∂μ ≤ ∫ x in φ i, g x ∂μ + e i) :
    Integrable f μ ∧ ∫ x, f x ∂μ ≤ ∫ x, g x ∂μ := by
  have hfint : Integrable f μ := by
    refine hφ.integrable_of_integral_bounded_of_nonneg_ae (∫ x, g x ∂μ + 1) hfi hf ?_
    filter_upwards [hle, he.eventually (gt_mem_nhds zero_lt_one)] with i hi hei
    exact hi.trans (add_le_add (setIntegral_le_integral hgi hg) hei.le)
  refine ⟨hfint, le_of_tendsto_of_tendsto (hφ.integral_tendsto_of_countably_generated hfint) ?_ hle⟩
  simpa using (hφ.integral_tendsto_of_countably_generated hgi).add he

end MeasureTheory.AECover

namespace TauCeti

open MeasureTheory

/-- **Integral bounds over a strip from its truncations.** Let `T ⊆ ℝ` be measurable, and let `f`
and `g` be nonnegative on the strip `ℝ × T`, with `g` integrable there and `f` integrable on each
truncation `[-n, n] × T`. If `∫_{[-n, n] × T} f ≤ ∫_{[-n, n] × T} g + e n` with errors `e n → 0`,
then `f` is integrable on the strip and `∫_{ℝ × T} f ≤ ∫_{ℝ × T} g`. -/
theorem integrableOn_univ_prod_and_setIntegral_le_of_setIntegral_Icc_prod_le_add {T : Set ℝ}
    (hT : MeasurableSet T) {f g : ℝ × ℝ → ℝ} {e : ℕ → ℝ} (hf : ∀ z ∈ univ ×ˢ T, 0 ≤ f z)
    (hg : ∀ z ∈ univ ×ˢ T, 0 ≤ g z) (hfi : ∀ n : ℕ, IntegrableOn f (Icc (-(n : ℝ)) n ×ˢ T))
    (hgi : IntegrableOn g (univ ×ˢ T)) (he : Tendsto e atTop (𝓝 0))
    (hle : ∀ n : ℕ, ∫ z in Icc (-(n : ℝ)) n ×ˢ T, f z ≤
      (∫ z in Icc (-(n : ℝ)) n ×ˢ T, g z) + e n) :
    IntegrableOn f (univ ×ˢ T) ∧ ∫ z in univ ×ˢ T, f z ≤ ∫ z in univ ×ˢ T, g z := by
  have hS : MeasurableSet (univ ×ˢ T : Set (ℝ × ℝ)) := MeasurableSet.univ.prod hT
  -- The truncations exhaust the strip.
  have hφ : AECover (volume.restrict (univ ×ˢ T)) atTop fun n : ℕ ↦ Icc (-(n : ℝ)) n ×ˢ T :=
    aecover_restrict_of_ae_imp hS (ae_of_all _ fun z hz ↦
      (tendsto_natCast_atTop_atTop.eventually_ge_atTop |z.1|).mono fun _ hn ↦
        ⟨abs_le.1 hn, hz.2⟩) fun _ ↦ measurableSet_Icc.prod hT
  have hres (n : ℕ) : (volume.restrict (univ ×ˢ T)).restrict (Icc (-(n : ℝ)) n ×ˢ T) =
      volume.restrict (Icc (-(n : ℝ)) n ×ˢ T) := by
    rw [Measure.restrict_restrict (measurableSet_Icc.prod hT),
      inter_eq_left.2 (prod_mono (subset_univ _) subset_rfl)]
  refine hφ.integrable_and_integral_le_of_setIntegral_le_add
    ((ae_restrict_iff' hS).2 (ae_of_all _ hf)) ((ae_restrict_iff' hS).2 (ae_of_all _ hg))
    (fun n ↦ ?_) hgi he (Eventually.of_forall fun n ↦ ?_)
  · rw [IntegrableOn, hres]
    exact hfi n
  · simpa only [hres] using hle n

/-- **Exhausting a space by balls.** If a nonnegative function is integrable on the preimages of
the balls `closedBall x₀ (r i)` under a continuous map `g`, and its integrals over them converge
to `c` as the radii `r i` tend to infinity, then its integral over the whole space is `c`. -/
theorem lintegral_ofReal_eq_of_tendsto_setIntegral_closedBall {α X ι : Type*}
    [TopologicalSpace α] [MeasurableSpace α] [OpensMeasurableSpace α] [PseudoMetricSpace X]
    {μ : Measure α} {l : Filter ι} [l.NeBot] [l.IsCountablyGenerated] {g : α → X} {x₀ : X}
    (hg : Continuous g) {r : ι → ℝ} (hr : Tendsto r l atTop) {f : α → ℝ} (hf : 0 ≤ᵐ[μ] f)
    (hfi : ∀ i, IntegrableOn f (g ⁻¹' Metric.closedBall x₀ (r i)) μ)
    {c : ℝ} (hc : Tendsto (fun i ↦ ∫ z in g ⁻¹' Metric.closedBall x₀ (r i), f z ∂μ) l (𝓝 c)) :
    ∫⁻ z, ENNReal.ofReal (f z) ∂μ = ENNReal.ofReal c := by
  have hφ : AECover μ l fun i ↦ g ⁻¹' Metric.closedBall x₀ (r i) :=
    ⟨ae_of_all _ fun z ↦ hr.eventually_ge_atTop (dist (g z) x₀),
      fun _ ↦ (Metric.isClosed_closedBall.preimage hg).measurableSet⟩
  rw [← ofReal_integral_eq_lintegral_ofReal
    (hφ.integrable_of_integral_tendsto_of_nonneg_ae c hfi hf hc) hf,
    hφ.integral_eq_of_tendsto_of_nonneg_ae c hf hfi hc]

end TauCeti
