/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.VectorMeasure.SetIntegral
import Mathlib.MeasureTheory.Integral.IntegrableOn

/-!
# Uniform approximation of vector-measure integrals by value truncation

An L¹ error against the variation measure controls the error of the pairing integral on
**every** integration set, with a bound independent of the set. Thus L¹ convergence gives
uniform convergence of set integrals, not just convergence on each fixed set.

In particular, cutting an integrable function off outside expanding norm balls approximates
all its set integrals uniformly. For real functions these cutoffs are the value windows
`[-R, R]`. The radii must tend to infinity: one fixed window need not recover the integrand.
Applied to derivative vector measures of bounded-variation paths, the result gives bounded
approximations of Stieltjes integrands, uniformly for all accumulated integrals `(a,t]`.
No continuity of the integrator or atomlessness of its variation is required.
-/

public section

open Filter Set
open scoped ENNReal Topology

namespace MeasureTheory.VectorMeasure

variable {X E F G : Type*} [MeasurableSpace X]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  {μ : VectorMeasure X F} {B : E →L[ℝ] F →L[ℝ] G} {f g : X → E}

/-- An L¹ error against the variation controls the pairing-integral error on every set,
with a bound independent of the integration set. -/
theorem edist_setIntegral_le_lintegral_edist (hf : μ.Integrable f) (hg : μ.Integrable g)
    (s : Set X) :
    edist (∫ᵛ x in s, f x ∂[B; μ]) (∫ᵛ x in s, g x ∂[B; μ]) ≤
      ‖B‖ₑ * ∫⁻ x, edist (f x) (g x) ∂μ.variation := by
  apply (edist_integral_le_lintegral_edist hf.restrict hg.restrict).trans
  gcongr
  exact variation_restrict_le.trans Measure.restrict_le_self

/-- L¹ convergence against the variation gives uniform convergence of all set integrals.
The integration sets need not be measurable: the native integral is zero on such sets. -/
theorem tendstoUniformly_setIntegral_of_L1 {ι : Type*} {l : Filter ι}
    (hf : μ.Integrable f) {u : ι → X → E} (hu : ∀ᶠ i in l, μ.Integrable (u i))
    (hlim : Tendsto (fun i ↦ ∫⁻ x, edist (u i x) (f x) ∂μ.variation) l (𝓝 0)) :
    TendstoUniformly (fun i s ↦ ∫ᵛ x in s, u i x ∂[B; μ])
      (fun s ↦ ∫ᵛ x in s, f x ∂[B; μ]) l := by
  have hbound : Tendsto (fun i ↦ ‖B‖ₑ * ∫⁻ x, edist (u i x) (f x) ∂μ.variation)
      l (𝓝 0) := by
    simpa using ENNReal.Tendsto.const_mul hlim (a := ‖B‖ₑ) (by simp)
  refine EMetric.tendstoUniformly_iff.mpr fun ε hε ↦ ?_
  filter_upwards [hu, hbound.eventually (gt_mem_nhds hε)] with i hi hεi s
  rw [edist_comm]
  exact (edist_setIntegral_le_lintegral_edist hi hf s).trans_lt hεi

/-- Expanding norm cutoffs of any L¹ integrand approximate all pairing set integrals
uniformly. The radii may be nonmonotone, provided they tend to infinity. Only a.e. strong
measurability is needed; the cutoff sets are null-measurable for the variation measure. -/
theorem Integrable.tendstoUniformly_setIntegral_indicator_norm_le (hf : μ.Integrable f)
    {R : ℕ → ℝ} (hR : Tendsto R atTop atTop) :
    TendstoUniformly
      (fun n s ↦ ∫ᵛ x in s, ({x | ‖f x‖ ≤ R n}.indicator f) x ∂[B; μ])
      (fun s ↦ ∫ᵛ x in s, f x ∂[B; μ]) atTop := by
  have hcut n : μ.Integrable ({x | ‖f x‖ ≤ R n}.indicator f) :=
    MeasureTheory.Integrable.indicator₀ hf
      (nullMeasurableSet_le hf.aestronglyMeasurable.norm.aemeasurable
      aemeasurable_const)
  apply tendstoUniformly_setIntegral_of_L1 hf (Eventually.of_forall hcut)
  have hdom : ∀ n x,
      edist (({x | ‖f x‖ ≤ R n}.indicator f) x) (f x) ≤ ‖f x‖ₑ := by
    intro n x
    by_cases hx : ‖f x‖ ≤ R n <;> simp [hx, edist_eq_enorm_sub]
  have hpoint x : Tendsto
      (fun n ↦ edist (({x | ‖f x‖ ≤ R n}.indicator f) x) (f x)) atTop (𝓝 0) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [hR.eventually (eventually_ge_atTop ‖f x‖)] with n hn
    simp [hn]
  simpa using tendsto_lintegral_of_dominated_convergence' (fun x ↦ ‖f x‖ₑ)
    (fun n ↦ ((hcut n).aestronglyMeasurable.edist hf.aestronglyMeasurable))
    (fun n ↦ Eventually.of_forall (hdom n)) hf.hasFiniteIntegral.ne
    (Eventually.of_forall hpoint)

end MeasureTheory.VectorMeasure
