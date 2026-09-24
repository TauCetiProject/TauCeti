/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.W1p.CompactSupport
public import TauCeti.Analysis.Sobolev.W1p.Translation
public import TauCeti.MeasureTheory.Function.Lp.Translation
public import TauCeti.Analysis.Sobolev.W1p.Restriction

/-!
# Difference quotients of `W^{1,p}(Ω)` functions

For `u ∈ W^{1,p}(Ω)`, `1 ≤ p < ∞`, a direction `v` and a compact `K ⊆ Ω`, the difference
quotients of `u` are bounded on `K` by the directional derivative of `u`:

`‖t⁻¹ (u(· + t v) - u)‖_{Lᵖ(K)} ≤ ‖⟪v, ∇u⟫‖_{Lᵖ(Ω)}`

as soon as the segments `[x, x + t v]`, `x ∈ K`, stay inside `Ω`, and in particular for all
sufficiently small `t`. No boundary regularity of `Ω` is needed. This is the half of the
difference-quotient characterisation of Sobolev functions that is used, in the difference-quotient
method, to bound the difference quotients of a weak solution in the energy estimate; the converse
half is `TauCeti.exists_norm_le_hasWeakLineDerivOn_of_frequently_eLpNorm_inv_mul_sub_le`.

The bound comes from a local translation estimate,

`‖u(· + h) - u‖_{Lᵖ(K)} ≤ ‖⟪h, ∇u⟫‖_{Lᵖ(T)}`

whenever the segments `[x, x + h]`, `x ∈ K`, lie in `T ⊆ Ω`. For smooth functions this is
`ContDiff.eLpNorm_comp_add_sub_le_eLpNorm_fderiv_apply`; it passes to `W^{1,p}(ℝⁿ)` by density of
the test functions. A general `u ∈ W^{1,p}(Ω)` is first multiplied by a smooth cutoff equal to
one near the segments and compactly supported in `Ω`, and then extended by zero to the whole
space; neither operation changes `u` or its gradient near the segments.

## Main declarations

* `TauCeti.W1p.differenceQuotient`: the local Sobolev difference quotient, whose value and weak
  gradient are characterized by `_ae` lemmas and whose defining formula is
  `TauCeti.W1p.differenceQuotient_def`.
* `TauCeti.W1p.eLpNorm_value_comp_add_sub_le`: the local translation estimate on `W^{1,p}(Ω)`.
* `TauCeti.W1p.eLpNorm_inv_mul_value_comp_add_smul_sub_le`: the difference-quotient bound.
* `TauCeti.W1p.eventually_eLpNorm_inv_mul_value_comp_add_smul_sub_le`: the difference-quotient
  bound for all sufficiently small `t`.
* `TauCeti.W1p.norm_value_differenceQuotient_le`: on the whole space the bound holds for every
  step `t`, with no compactness, in the form `‖D^t_v u‖_p ≤ ‖v‖ ‖∇u‖_p`.

## References

* L. C. Evans, *Partial Differential Equations*, §5.8.2, Theorem 3 (i).
* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Lemma 7.23.
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory Set TopologicalSpace Filter Topology
open scoped Distributions ENNReal Gradient InnerProductSpace

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {Omega : Opens E} {p : ENNReal} [Fact (1 ≤ p)]

/-! ### Local difference quotients -/

/-- **The local Sobolev difference quotient.** For `V ⊆ Ω` and `V + t • w ⊆ Ω`, this is the
element of `W^{1,p}(V)` represented by `x ↦ t⁻¹ (u (x + t • w) - u x)`.

No assumption `t ≠ 0` is needed for the definition: at `t = 0` both the value and gradient are
zero. Applications approximating a derivative impose `t ≠ 0` through their estimates. -/
def W1p.differenceQuotient {Omega V : Opens E} (hV : V ≤ Omega) (w : E) (t : ℝ)
    (hVO : MapsTo (· + t • w) V Omega) (u : W1p mu Omega p) : W1p mu V p :=
  t⁻¹ • (W1p.translate hVO u - W1p.restrictL hV u)

/-- The local Sobolev difference quotient as a scaled difference of a translate and a
restriction. The body of `TauCeti.W1p.differenceQuotient` is not exposed to importing modules,
so this is how downstream files unfold it. -/
theorem W1p.differenceQuotient_def {Omega V : Opens E} (hV : V ≤ Omega) (w : E) (t : ℝ)
    (hVO : MapsTo (· + t • w) V Omega) (u : W1p mu Omega p) :
    W1p.differenceQuotient hV w t hVO u = t⁻¹ • (W1p.translate hVO u - W1p.restrictL hV u) := by
  rfl

/-- The value of the local Sobolev difference quotient has the expected representative. -/
theorem W1p.value_differenceQuotient_ae {Omega V : Opens E} (hV : V ≤ Omega) (w : E) (t : ℝ)
    (hVO : MapsTo (· + t • w) V Omega) (u : W1p mu Omega p) :
    W1p.value (W1p.differenceQuotient hV w t hVO u) =ᵐ[mu.restrict V]
      fun x ↦ t⁻¹ * (W1p.value u (x + t • w) - W1p.value u x) := by
  have hvalue : W1p.value (W1p.differenceQuotient hV w t hVO u) =
      t⁻¹ • (W1p.value (W1p.translate hVO u) - W1p.value (W1p.restrictL hV u)) := by
    rw [← W1p.valueL_apply, W1p.differenceQuotient, map_smul, map_sub,
      W1p.valueL_apply, W1p.valueL_apply]
  rw [hvalue]
  filter_upwards [W1p.value_translate_ae hVO u, W1p.value_restrictL_ae hV u,
    Lp.coeFn_sub (W1p.value (W1p.translate hVO u))
      (W1p.value (W1p.restrictL hV u)),
    Lp.coeFn_smul t⁻¹ (W1p.value (W1p.translate hVO u) -
      W1p.value (W1p.restrictL hV u))] with x htrans hres hsub hsmul
  rw [hsmul, Pi.smul_apply, hsub, Pi.sub_apply, htrans, hres, smul_eq_mul]

/-- The weak gradient of the local Sobolev difference quotient is the corresponding difference
quotient of the weak gradient. -/
theorem W1p.gradient_differenceQuotient_ae {Omega V : Opens E} (hV : V ≤ Omega) (w : E)
    (t : ℝ) (hVO : MapsTo (· + t • w) V Omega) (u : W1p mu Omega p) :
    W1p.gradient (W1p.differenceQuotient hV w t hVO u) =ᵐ[mu.restrict V]
      fun x ↦ t⁻¹ • (W1p.gradient u (x + t • w) - W1p.gradient u x) := by
  have hgradient : W1p.gradient (W1p.differenceQuotient hV w t hVO u) =
      t⁻¹ • (W1p.gradient (W1p.translate hVO u) - W1p.gradient (W1p.restrictL hV u)) := by
    rw [← W1p.gradientL_apply, W1p.differenceQuotient, map_smul, map_sub,
      W1p.gradientL_apply, W1p.gradientL_apply]
  rw [hgradient]
  filter_upwards [W1p.gradient_translate_ae hVO u, W1p.gradient_restrictL_ae hV u,
    Lp.coeFn_sub (W1p.gradient (W1p.translate hVO u))
      (W1p.gradient (W1p.restrictL hV u)),
    Lp.coeFn_smul t⁻¹ (W1p.gradient (W1p.translate hVO u) -
      W1p.gradient (W1p.restrictL hV u))] with x htrans hres hsub hsmul
  rw [hsmul, Pi.smul_apply, hsub, Pi.sub_apply, htrans, hres]

/-! ### Difference-quotient estimates -/

/-- **The local translation estimate on `W^{1,p}(ℝⁿ)`.** If `T` is measurable and every segment
`[x, x + h]` with `x ∈ K` lies in `T`, then

`‖w(· + h) - w‖_{Lᵖ(K)} ≤ ‖⟪h, ∇w⟫‖_{Lᵖ(T)}`.

This holds for `1 ≤ p < ∞`; neither `K` nor `T` needs to be compact. -/
theorem W1p.eLpNorm_value_comp_add_sub_le_of_top (hp : p ≠ ∞) (w : W1p mu ⊤ p) (h : E)
    {K T : Set E} (hT : MeasurableSet T) (hKT : ∀ x ∈ K, ∀ t ∈ Icc (0 : ℝ) 1, x + t • h ∈ T) :
    eLpNorm (fun x ↦ W1p.value w (x + h) - W1p.value w x) p (mu.restrict K)
      ≤ eLpNorm (fun x ↦ ⟪h, W1p.gradient w x⟫_ℝ) p (mu.restrict T) := by
  set nu := mu.restrict ((⊤ : Opens E) : Set E)
  have htop : nu = mu := by simp only [nu, Opens.coe_top, Measure.restrict_univ]
  let _ : nu.IsAddHaarMeasure := by
    rw [htop]
    infer_instance
  have hq : Tendsto (· + h) (ae mu) (ae mu) :=
    (measurePreserving_add_right mu h).quasiMeasurePreserving.tendsto_ae
  -- Both sides are extended norms of continuous linear images of `w`.
  set A : W1p mu ⊤ p →L[ℝ] Lp ℝ p (nu.restrict K) :=
    (LpToLpRestrictCLM E ℝ ℝ nu p K).comp
      (((nu.translateLp p h).toLinearIsometry.toContinuousLinearMap -
        ContinuousLinearMap.id ℝ _).comp W1p.valueL)
  set B : W1p mu ⊤ p →L[ℝ] Lp ℝ p (nu.restrict T) :=
    (LpToLpRestrictCLM E ℝ ℝ nu p T).comp (((innerSL ℝ h).compLpL p nu).comp W1p.gradientL)
  have hA : ∀ v : W1p mu ⊤ p, ‖A v‖ₑ =
      eLpNorm (fun x ↦ W1p.value v (x + h) - W1p.value v x) p (mu.restrict K) := fun v ↦ by
    rw [Lp.enorm_def]
    refine (eLpNorm_congr_ae ?_).trans (by rw [htop])
    filter_upwards [LpToLpRestrictCLM_coeFn ℝ K (nu.translateLp p h (W1p.valueL v) -
        W1p.valueL v), ae_restrict_of_ae (Lp.coeFn_sub (nu.translateLp p h (W1p.valueL v))
        (W1p.valueL v)), ae_restrict_of_ae (Measure.coeFn_translateLp (mu := nu) h
        (W1p.valueL v))] with x h1 h2 h3
    rw [← W1p.valueL_apply]
    simp only [A, ContinuousLinearMap.comp_apply, FunLike.coe_sub, Pi.sub_apply,
      LinearIsometry.coe_toContinuousLinearMap, LinearIsometryEquiv.coe_toLinearIsometry,
      ContinuousLinearMap.id_apply]
    rw [h1, h2, Pi.sub_apply, h3, Function.comp_apply]
  have hB : ∀ v : W1p mu ⊤ p, ‖B v‖ₑ =
      eLpNorm (fun x ↦ ⟪h, W1p.gradient v x⟫_ℝ) p (mu.restrict T) := fun v ↦ by
    rw [Lp.enorm_def]
    refine (eLpNorm_congr_ae ?_).trans (by rw [htop])
    filter_upwards [LpToLpRestrictCLM_coeFn ℝ T ((innerSL ℝ h).compLpL p nu (W1p.gradientL v)),
      ae_restrict_of_ae ((innerSL ℝ h).coeFn_compLpL (W1p.gradientL v))] with x h1 h2
    simp only [B, ContinuousLinearMap.comp_apply]
    rw [h1, h2, innerSL_apply_apply, W1p.gradientL_apply]
  have hclosed : IsClosed {v : W1p mu ⊤ p |
      eLpNorm (fun x ↦ W1p.value v (x + h) - W1p.value v x) p (mu.restrict K)
        ≤ eLpNorm (fun x ↦ ⟪h, W1p.gradient v x⟫_ℝ) p (mu.restrict T)} := by
    simp only [← hA, ← hB]
    exact isClosed_le A.continuous.enorm B.continuous.enorm
  -- Pass the smooth estimate to all of `W^{1,p}(ℝⁿ)` by density of test functions.
  refine w1p0Submodule_subset_of_isClosed hclosed (fun phi ↦ ?_) (W1p.mem_w1p0Submodule_top hp w)
  -- The estimate for a single test function is the smooth estimate.
  have hvalue : ⇑(W1p.value (W1p.ofTestFunctionₗ mu ⊤ p phi)) =ᵐ[mu] (phi : E → ℝ) := by
    rw [W1p.value_ofTestFunctionₗ]
    exact (testFunctionLp_apply_ae p phi).filter_mono (ae_mono htop.ge)
  have hgrad : ⇑(W1p.gradient (W1p.ofTestFunctionₗ mu ⊤ p phi)) =ᵐ[mu]
      fun x ↦ ∇ (phi : E → ℝ) x := by
    rw [W1p.gradient_ofTestFunctionₗ]
    exact (gradientTestFunctionLp_apply_ae p phi).filter_mono (ae_mono htop.ge)
  have hL : eLpNorm (fun x ↦ W1p.value (W1p.ofTestFunctionₗ mu ⊤ p phi) (x + h) -
      W1p.value (W1p.ofTestFunctionₗ mu ⊤ p phi) x) p (mu.restrict K) =
      eLpNorm (fun x ↦ (phi : E → ℝ) (x + h) - phi x) p (mu.restrict K) := by
    refine eLpNorm_congr_ae (ae_restrict_of_ae ?_)
    filter_upwards [hvalue, hq.eventually hvalue] with x h1 h2
    rw [h1, h2]
  have hR : eLpNorm (fun x ↦ ⟪h, W1p.gradient (W1p.ofTestFunctionₗ mu ⊤ p phi) x⟫_ℝ) p
      (mu.restrict T) = eLpNorm (fun x ↦ fderiv ℝ (phi : E → ℝ) x h) p (mu.restrict T) := by
    refine eLpNorm_congr_ae (ae_restrict_of_ae ?_)
    filter_upwards [hgrad] with x hx
    rw [hx, real_inner_comm, inner_gradient_left]
  rw [Set.mem_ofPred_eq, hL, hR]
  have hphi : ContDiff ℝ 1 (phi : E → ℝ) := phi.contDiff.of_le (by simp)
  exact hphi.eLpNorm_comp_add_sub_le_eLpNorm_fderiv_apply Fact.out hp h hT hKT

/-- **The local translation estimate on `W^{1,p}(Ω)`.** Let `u ∈ W^{1,p}(Ω)`, `1 ≤ p < ∞`, and
let `K` be compact. If every segment `[x, x + h]` with `x ∈ K` lies in a set `T ⊆ Ω`, then

`‖u(· + h) - u‖_{Lᵖ(K)} ≤ ‖⟪h, ∇u⟫‖_{Lᵖ(T)}`.

No boundary regularity of `Ω` is needed: the estimate only sees `u` near the segments. -/
theorem W1p.eLpNorm_value_comp_add_sub_le (hp : p ≠ ∞) (u : W1p mu Omega p) (h : E)
    {K T : Set E} (hK : IsCompact K) (hTO : T ⊆ Omega)
    (hKT : ∀ x ∈ K, ∀ t ∈ Icc (0 : ℝ) 1, x + t • h ∈ T) :
    eLpNorm (fun x ↦ W1p.value u (x + h) - W1p.value u x) p (mu.restrict K)
      ≤ eLpNorm (fun x ↦ ⟪h, W1p.gradient u x⟫_ℝ) p (mu.restrict T) := by
  -- `S ⊆ T` is the compact union of the segments; on it `u` is a whole-space function `w`.
  set S := (fun z : E × ℝ ↦ z.1 + z.2 • h) '' (K ×ˢ Icc (0 : ℝ) 1)
  have hS : IsCompact S := (hK.prod isCompact_Icc).image (by fun_prop)
  have hKS : ∀ x ∈ K, ∀ t ∈ Icc (0 : ℝ) 1, x + t • h ∈ S := fun x hx t ht ↦
    ⟨(x, t), ⟨hx, ht⟩, rfl⟩
  have hST : S ⊆ T := by
    rintro _ ⟨z, ⟨hx, ht⟩, rfl⟩
    exact hKT z.1 hx z.2 ht
  obtain ⟨w, hvalue, hgrad⟩ :=
    W1p.exists_top_value_gradient_ae_eq_on_of_isCompact hp u hS (hST.trans hTO)
  have hq : Tendsto (· + h) (ae mu) (ae mu) :=
    (measurePreserving_add_right mu h).quasiMeasurePreserving.tendsto_ae
  have hL : eLpNorm (fun x ↦ W1p.value w (x + h) - W1p.value w x) p (mu.restrict K) =
      eLpNorm (fun x ↦ W1p.value u (x + h) - W1p.value u x) p (mu.restrict K) := by
    refine eLpNorm_congr_ae ?_
    filter_upwards [ae_restrict_mem hK.measurableSet, ae_restrict_of_ae hvalue,
      ae_restrict_of_ae (hq.eventually hvalue)] with x hxK h1 h2
    have hx1 := hKS x hxK 1 ⟨zero_le_one, le_rfl⟩
    have hx0 := hKS x hxK 0 ⟨le_rfl, zero_le_one⟩
    rw [one_smul] at hx1
    rw [zero_smul, add_zero] at hx0
    rw [h1 hx0, h2 hx1]
  have hR : eLpNorm (fun x ↦ ⟪h, W1p.gradient w x⟫_ℝ) p (mu.restrict S) =
      eLpNorm (fun x ↦ ⟪h, W1p.gradient u x⟫_ℝ) p (mu.restrict S) := by
    refine eLpNorm_congr_ae ?_
    filter_upwards [ae_restrict_mem hS.measurableSet, ae_restrict_of_ae hgrad] with x hxS hx
    rw [hx hxS]
  calc eLpNorm (fun x ↦ W1p.value u (x + h) - W1p.value u x) p (mu.restrict K)
      = eLpNorm (fun x ↦ W1p.value w (x + h) - W1p.value w x) p (mu.restrict K) := hL.symm
    _ ≤ eLpNorm (fun x ↦ ⟪h, W1p.gradient w x⟫_ℝ) p (mu.restrict S) :=
        W1p.eLpNorm_value_comp_add_sub_le_of_top hp w h hS.measurableSet hKS
    _ = eLpNorm (fun x ↦ ⟪h, W1p.gradient u x⟫_ℝ) p (mu.restrict S) := hR
    _ ≤ eLpNorm (fun x ↦ ⟪h, W1p.gradient u x⟫_ℝ) p (mu.restrict T) :=
      eLpNorm_mono_measure _ (Measure.restrict_mono hST le_rfl)

/-- **Difference quotients of a `W^{1,p}(Ω)` function are bounded by its directional
derivative.** Let `u ∈ W^{1,p}(Ω)`, `1 ≤ p < ∞`, and let `K` be compact. If every segment
`[x, x + t v]` with `x ∈ K` lies in a set `T ⊆ Ω`, then

`‖t⁻¹ (u(· + t v) - u)‖_{Lᵖ(K)} ≤ ‖⟪v, ∇u⟫‖_{Lᵖ(T)}`.

For `t = 0` the left-hand side is zero. -/
theorem W1p.eLpNorm_inv_mul_value_comp_add_smul_sub_le (hp : p ≠ ∞) (u : W1p mu Omega p)
    (v : E) (t : ℝ) {K T : Set E} (hK : IsCompact K) (hTO : T ⊆ Omega)
    (hKT : ∀ x ∈ K, ∀ s ∈ Icc (0 : ℝ) 1, x + s • t • v ∈ T) :
    eLpNorm (fun x ↦ t⁻¹ * (W1p.value u (x + t • v) - W1p.value u x)) p (mu.restrict K)
      ≤ eLpNorm (fun x ↦ ⟪v, W1p.gradient u x⟫_ℝ) p (mu.restrict T) := by
  rcases eq_or_ne t 0 with rfl | ht
  · simp
  have hbound := W1p.eLpNorm_value_comp_add_sub_le hp u (t • v) hK hTO hKT
  simp_rw [real_inner_smul_left] at hbound
  -- Pointwise multiplication by a real scalar is the function-space scalar action.
  change eLpNorm (t⁻¹ • fun x ↦ W1p.value u (x + t • v) - W1p.value u x) p (mu.restrict K) ≤ _
  change _ ≤ eLpNorm (t • fun x ↦ ⟪v, W1p.gradient u x⟫_ℝ) p (mu.restrict T) at hbound
  rw [eLpNorm_const_smul] at hbound ⊢
  calc ‖t⁻¹‖ₑ * eLpNorm (fun x ↦ W1p.value u (x + t • v) - W1p.value u x) p (mu.restrict K)
      ≤ ‖t⁻¹‖ₑ * (‖t‖ₑ * eLpNorm (fun x ↦ ⟪v, W1p.gradient u x⟫_ℝ) p (mu.restrict T)) := by
        gcongr
    _ = eLpNorm (fun x ↦ ⟪v, W1p.gradient u x⟫_ℝ) p (mu.restrict T) := by
        rw [← mul_assoc, ← enorm_mul, inv_mul_cancel₀ ht, enorm_one, one_mul]

/-- **Uniform bound on difference quotients near a compact set.** Let `u ∈ W^{1,p}(Ω)`,
`1 ≤ p < ∞`, and let `K ⊆ Ω` be compact. Then for all sufficiently small `t`,

`‖t⁻¹ (u(· + t v) - u)‖_{Lᵖ(K)} ≤ ‖⟪v, ∇u⟫‖_{Lᵖ(Ω)}`. -/
theorem W1p.eventually_eLpNorm_inv_mul_value_comp_add_smul_sub_le (hp : p ≠ ∞)
    (u : W1p mu Omega p) (v : E) {K : Set E} (hK : IsCompact K) (hKO : K ⊆ Omega) :
    ∀ᶠ t in 𝓝 (0 : ℝ),
      eLpNorm (fun x ↦ t⁻¹ * (W1p.value u (x + t • v) - W1p.value u x)) p (mu.restrict K)
        ≤ eLpNorm (fun x ↦ ⟪v, W1p.gradient u x⟫_ℝ) p (mu.restrict Omega) := by
  obtain ⟨δ, hδ, hδO⟩ := hK.exists_cthickening_subset_open Omega.isOpen hKO
  have htend : Tendsto (fun t : ℝ ↦ t • v) (𝓝 0) (𝓝 0) := by
    simpa using (tendsto_id (x := 𝓝 (0 : ℝ))).smul_const v
  filter_upwards [htend.eventually (Metric.closedBall_mem_nhds 0 hδ)] with t ht
  refine W1p.eLpNorm_inv_mul_value_comp_add_smul_sub_le hp u v t hK subset_rfl fun x hx s hs ↦
    hδO ?_
  refine Metric.mem_cthickening_of_dist_le _ x δ _ hx ?_
  rw [dist_zero_right] at ht
  rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg hs.1]
  exact (mul_le_of_le_one_left (norm_nonneg _) hs.2).trans ht

/-- **The whole-space difference-quotient bound.** On `Ω = ⊤` no compactness is needed: the
`Lᵖ` norm of the difference quotient of `u ∈ W^{1,p}(ℝⁿ)` in the direction `v` is at most
`‖v‖ ‖∇u‖_p`, uniformly in the step `t`. This is the form of
`TauCeti.W1p.eLpNorm_inv_mul_value_comp_add_smul_sub_le` that a difference-quotient argument on
the whole space consumes, stated for the bundled quotient
`TauCeti.W1p.differenceQuotient`. -/
theorem W1p.norm_value_differenceQuotient_le (hp : p ≠ ∞) (v : E) (t : ℝ) (u : W1p mu ⊤ p) :
    ‖W1p.value (W1p.differenceQuotient le_rfl v t (Set.mapsTo_univ (· + t • v) _) u)‖
      ≤ ‖v‖ * ‖W1p.gradient u‖ := by
  set nu := mu.restrict ((⊤ : Opens E) : Set E) with hnu
  set q := W1p.differenceQuotient le_rfl v t (Set.mapsTo_univ (· + t • v) _) u with hq
  -- The inner product against `v` is dominated by `‖v‖` times the gradient.
  have hinner : eLpNorm (fun x ↦ ⟪v, W1p.gradient u x⟫_ℝ) p nu
      ≤ ‖v‖ₑ * eLpNorm (W1p.gradient u : E → E) p nu := by
    calc eLpNorm (fun x ↦ ⟪v, W1p.gradient u x⟫_ℝ) p nu
        ≤ eLpNorm (‖v‖ • (W1p.gradient u : E → E)) p nu :=
          eLpNorm_mono_ae (Filter.Eventually.of_forall fun x ↦ by
            rw [Pi.smul_apply, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_norm]
            exact abs_real_inner_le_norm v _)
      _ = ‖v‖ₑ * eLpNorm (W1p.gradient u : E → E) p nu := by
          rw [eLpNorm_const_smul, enorm_norm]
  -- The difference quotient itself, through the whole-space translation estimate.
  have hquot : eLpNorm (W1p.value q : E → ℝ) p nu
      ≤ ‖v‖ₑ * eLpNorm (W1p.gradient u : E → E) p nu := by
    rw [hq, eLpNorm_congr_ae
      (W1p.value_differenceQuotient_ae le_rfl v t (Set.mapsTo_univ (· + t • v) _) u)]
    refine le_trans ?_ hinner
    rcases eq_or_ne t 0 with rfl | ht
    · simp
    have hbase := W1p.eLpNorm_value_comp_add_sub_le_of_top (mu := mu) hp u (t • v)
      (K := ((⊤ : Opens E) : Set E)) (T := ((⊤ : Opens E) : Set E))
      (⊤ : Opens E).isOpen.measurableSet fun x _ s _ ↦ by simp
    have hl : (fun x ↦ t⁻¹ * (W1p.value u (x + t • v) - W1p.value u x))
        = t⁻¹ • fun x ↦ W1p.value u (x + t • v) - W1p.value u x :=
      funext fun x ↦ by rw [Pi.smul_apply, smul_eq_mul]
    have hr : (fun x ↦ ⟪t • v, W1p.gradient u x⟫_ℝ)
        = t • fun x ↦ ⟪v, W1p.gradient u x⟫_ℝ :=
      funext fun x ↦ by rw [Pi.smul_apply, smul_eq_mul, real_inner_smul_left]
    rw [hr, eLpNorm_const_smul] at hbase
    rw [hl, eLpNorm_const_smul]
    calc ‖t⁻¹‖ₑ * eLpNorm (fun x ↦ W1p.value u (x + t • v) - W1p.value u x) p nu
        ≤ ‖t⁻¹‖ₑ * (‖t‖ₑ * eLpNorm (fun x ↦ ⟪v, W1p.gradient u x⟫_ℝ) p nu) := by gcongr
      _ = eLpNorm (fun x ↦ ⟪v, W1p.gradient u x⟫_ℝ) p nu := by
          rw [← mul_assoc, ← enorm_mul, inv_mul_cancel₀ ht, enorm_one, one_mul]
  have hfin : ‖v‖ₑ * eLpNorm (W1p.gradient u : E → E) p nu ≠ ∞ :=
    ENNReal.mul_ne_top (by simp) (Lp.eLpNorm_ne_top _)
  calc ‖W1p.value q‖ = (eLpNorm (W1p.value q : E → ℝ) p nu).toReal := Lp.norm_def _
    _ ≤ (‖v‖ₑ * eLpNorm (W1p.gradient u : E → E) p nu).toReal := ENNReal.toReal_mono hfin hquot
    _ = ‖v‖ * ‖W1p.gradient u‖ := by
        rw [ENNReal.toReal_mul, ← Lp.norm_def]
        simp

end TauCeti
