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
import TauCeti.Analysis.Sobolev.DifferenceQuotient
import TauCeti.MeasureTheory.Function.Lp.Norm

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
* `TauCeti.W1p.exists_norm_le_hasWeakLineDerivOn_inner_gradient_of_norm_gradient_le`: on the
  whole space, gradients of the difference quotients of `u ∈ H¹(ℝⁿ)` bounded uniformly in the step
  give second weak derivatives of `u` in `L²`.
* `TauCeti.W1p.eLpNorm_inv_mul_value_comp_add_smul_sub_le`: the difference-quotient bound.
* `TauCeti.W1p.eventually_eLpNorm_inv_mul_value_comp_add_smul_sub_le`: the difference-quotient
  bound for all sufficiently small `t`.
* `TauCeti.W1p.norm_value_differenceQuotient_le`: on the whole space the bound holds for every
  step `t`, with no compactness, in the form `‖D^t_v u‖_p ≤ ‖v‖ ‖∇u‖_p`.
* `TauCeti.W1p.abs_integral_value_mul_gradient_differenceQuotient_le`: on the whole space a
  difference quotient moves from `∇v` onto a field `z Φ`, with `z ∈ H¹(ℝⁿ)` and `Φ` a bounded,
  Lipschitz field of linear forms, at the cost of the `H¹` norm of `z`.

## References

* L. C. Evans, *Partial Differential Equations*, §5.8.2, Theorem 3 (i).
* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Lemma 7.23.
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory Set TopologicalSpace Filter Topology
open scoped Distributions ENNReal Gradient InnerProductSpace NNReal

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

/-- **Bounded difference quotients of the gradient give second weak derivatives.** If the
gradients of the difference quotients of `u ∈ H¹(ℝⁿ)` in the direction `w` are bounded by `C` in
`L²`, uniformly in the step `t`, then for every `y` the derivative `∂_y u = ⟪∇u, y⟫` has a weak
derivative in the direction `w`, with `‖∂_w ∂_y u‖_{L²} ≤ ‖y‖ C`.

This is the step of the difference-quotient method that turns the uniform bound of an energy
estimate into second derivatives in `L²`, by the difference-quotient criterion
`TauCeti.exists_norm_le_hasWeakLineDerivOn_of_frequently_eLpNorm_inv_mul_sub_le`. -/
theorem W1p.exists_norm_le_hasWeakLineDerivOn_inner_gradient_of_norm_gradient_le
    (u : W1p mu ⊤ 2) (w : E) {C : ℝ}
    (hC : ∀ t : ℝ, ‖W1p.gradient
      (W1p.differenceQuotient le_rfl w t (Set.mapsTo_univ (· + t • w) _) u)‖ ≤ C) (y : E) :
    ∃ G : Lp ℝ 2 (mu.restrict ((⊤ : Opens E) : Set E)),
      ‖G‖ ≤ ‖y‖ * C ∧ HasWeakLineDerivOn mu ⊤ (fun x ↦ ⟪W1p.gradient u x, y⟫_ℝ) G w := by
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  have hloc : LocallyIntegrableOn (fun x ↦ ⟪W1p.gradient u x, y⟫_ℝ)
      ((⊤ : Opens E) : Set E) mu := by
    simpa using ((W1p.hasWeakFDerivOn u).hasWeakLineDerivOn y).locallyIntegrableOn_deriv
  -- The uniform bound on the difference quotients of `∂_y u`, on the whole space.
  have hglobal : ∀ t : ℝ, eLpNorm
      (fun x ↦ t⁻¹ * (⟪W1p.gradient u (x + t • w), y⟫_ℝ - ⟪W1p.gradient u x, y⟫_ℝ)) 2
      (mu.restrict ((⊤ : Opens E) : Set E)) ≤ ENNReal.ofReal (‖y‖ * C) := by
    intro t
    obtain ⟨g, hg⟩ : ∃ g : W1p mu ⊤ 2,
        g = W1p.differenceQuotient le_rfl w t (Set.mapsTo_univ (· + t • w) _) u := ⟨_, rfl⟩
    have hgC : ‖W1p.gradient g‖ ≤ C := hg ▸ hC t
    have hae : (fun x ↦ t⁻¹ * (⟪W1p.gradient u (x + t • w), y⟫_ℝ - ⟪W1p.gradient u x, y⟫_ℝ))
        =ᵐ[mu.restrict ((⊤ : Opens E) : Set E)] fun x ↦ ⟪W1p.gradient g x, y⟫_ℝ := by
      filter_upwards [hg ▸ W1p.gradient_differenceQuotient_ae le_rfl w t
        (Set.mapsTo_univ (· + t • w) _) u] with x hx
      rw [hx, inner_smul_left, inner_sub_left]
      simp [mul_sub]
    rw [eLpNorm_congr_ae hae]
    calc eLpNorm (fun x ↦ ⟪W1p.gradient g x, y⟫_ℝ) 2 (mu.restrict ((⊤ : Opens E) : Set E))
        ≤ eLpNorm (‖y‖ • (W1p.gradient g : E → E)) 2 (mu.restrict ((⊤ : Opens E) : Set E)) :=
          eLpNorm_mono_ae ((Lp.aestronglyMeasurable (W1p.gradient g)).inner_const)
            (Filter.Eventually.of_forall fun x ↦ by
              rw [Pi.smul_apply, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_norm,
                mul_comm]
              exact abs_real_inner_le_norm _ y)
      _ = ‖y‖ₑ * eLpNorm (W1p.gradient g : E → E) 2 (mu.restrict ((⊤ : Opens E) : Set E)) := by
          rw [eLpNorm_const_smul, enorm_norm]
      _ = ‖y‖ₑ * ENNReal.ofReal ‖W1p.gradient g‖ := by
          rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top _)]
      _ ≤ ‖y‖ₑ * ENNReal.ofReal C := by gcongr
      _ = ENNReal.ofReal (‖y‖ * C) := by
          rw [← ofReal_norm, ← ENNReal.ofReal_mul (norm_nonneg y)]
  exact exists_norm_le_hasWeakLineDerivOn_of_frequently_eLpNorm_inv_mul_sub_le hloc w
    (by positivity) fun K hK _ ↦ Filter.Eventually.frequently <|
      Filter.Eventually.of_forall fun t ↦
        le_trans (eLpNorm_mono_measure _ (Measure.restrict_mono hK le_rfl)) (hglobal t)

/-- **The whole-space difference-quotient bound.** On `Ω = ⊤` no compactness is needed: the
`Lᵖ` norm of the difference quotient of `u ∈ W^{1,p}(ℝⁿ)` in the direction `v` is at most
`‖v‖ ‖∇u‖_p`, uniformly in the step `t`. This is the form of
`TauCeti.W1p.eLpNorm_inv_mul_value_comp_add_smul_sub_le` that a difference-quotient argument on
the whole space consumes, stated for the bundled quotient
`TauCeti.W1p.differenceQuotient`. -/
theorem W1p.norm_value_differenceQuotient_le (hp : p ≠ ∞) (v : E) (t : ℝ) (u : W1p mu ⊤ p) :
    ‖W1p.value (W1p.differenceQuotient le_rfl v t (Set.mapsTo_univ (· + t • v) _) u)‖
      ≤ ‖v‖ * ‖W1p.gradient u‖ := by
  set nu := mu.restrict ((⊤ : Opens E) : Set E) with _
  set q := W1p.differenceQuotient le_rfl v t (Set.mapsTo_univ (· + t • v) _) u with hq
  -- The inner product against `v` is dominated by `‖v‖` times the gradient.
  have hmeas : AEStronglyMeasurable (fun x ↦ ⟪v, W1p.gradient u x⟫_ℝ) nu :=
    aestronglyMeasurable_const.inner (Lp.aestronglyMeasurable (W1p.gradient u))
  have hinner : eLpNorm (fun x ↦ ⟪v, W1p.gradient u x⟫_ℝ) p nu
      ≤ ‖v‖ₑ * eLpNorm (W1p.gradient u : E → E) p nu := by
    calc eLpNorm (fun x ↦ ⟪v, W1p.gradient u x⟫_ℝ) p nu
        ≤ eLpNorm (‖v‖ • (W1p.gradient u : E → E)) p nu :=
          eLpNorm_mono_ae hmeas (Filter.Eventually.of_forall fun x ↦ by
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

omit [MeasurableSpace E] [FiniteDimensional ℝ E] [BorelSpace E] in
/-- **The product rule for difference quotients, pointwise.** If `Φ` is a field of linear forms
bounded by `C` and `L`-Lipschitz, then for a real function `Z`, a vector `g`, a point `x`, a
direction `e` and a step `t`,

`|t⁻¹ (Z(x - t e) Φ(x - t e) g - Z(x) Φ(x) g)|`
  `≤ C |t⁻¹ (Z(x) - Z(x - t e))| ‖g‖ + L ‖e‖ |Z(x)| ‖g‖`. -/
private theorem norm_inv_mul_sub_le
    {Φ : E → StrongDual ℝ E} {C : ℝ} {L : ℝ≥0}
    (hC : ∀ x, ‖Φ x‖ ≤ C) (hL : LipschitzWith L Φ) {Z : E → ℝ}
    {g x e : E} {t : ℝ} :
    ‖t⁻¹ * (Z (x - t • e) * Φ (x - t • e) g - Z x * Φ x g)‖
      ≤ C * (‖t⁻¹ * (Z x - Z (x - t • e))‖ * ‖g‖) + L * ‖e‖ * (‖Z x‖ * ‖g‖) := by
  have hsplit : t⁻¹ * (Z (x - t • e) * Φ (x - t • e) g - Z x * Φ x g)
      = -(t⁻¹ * (Z x - Z (x - t • e))) * Φ (x - t • e) g
        + Z x * (t⁻¹ * (Φ (x - t • e) - Φ x) g) := by
    rw [_root_.sub_apply]
    ring
  -- The difference quotient of `Φ` is bounded by the Lipschitz constant.
  have hΦd : |t⁻¹| * ‖Φ (x - t • e) - Φ x‖ ≤ L * ‖e‖ := by
    have h1 : ‖Φ (x - t • e) - Φ x‖ ≤ L * (|t| * ‖e‖) := by
      simpa [dist_eq_norm, norm_smul] using hL.dist_le_mul (x - t • e) x
    rcases eq_or_ne t 0 with rfl | ht
    · simp only [_root_.inv_zero, abs_zero, zero_mul]
      positivity
    · calc |t⁻¹| * ‖Φ (x - t • e) - Φ x‖ ≤ |t⁻¹| * (L * (|t| * ‖e‖)) := by gcongr
        _ = L * ‖e‖ := by
            rw [abs_inv]
            field_simp
  have h2 : ‖Φ (x - t • e) g‖ ≤ C * ‖g‖ :=
    ((Φ (x - t • e)).le_opNorm g).trans (mul_le_mul_of_nonneg_right (hC _) (norm_nonneg _))
  have h3 : ‖t⁻¹ * (Φ (x - t • e) - Φ x) g‖ ≤ L * ‖e‖ * ‖g‖ := by
    rw [norm_mul, Real.norm_eq_abs]
    calc |t⁻¹| * ‖(Φ (x - t • e) - Φ x) g‖ ≤ |t⁻¹| * (‖Φ (x - t • e) - Φ x‖ * ‖g‖) := by
          gcongr
          exact (Φ (x - t • e) - Φ x).le_opNorm g
      _ = (|t⁻¹| * ‖Φ (x - t • e) - Φ x‖) * ‖g‖ := by ring
      _ ≤ L * ‖e‖ * ‖g‖ := by gcongr
  rw [hsplit]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_mul, norm_neg]
  calc ‖t⁻¹ * (Z x - Z (x - t • e))‖ * ‖Φ (x - t • e) g‖ +
        ‖Z x‖ * ‖t⁻¹ * (Φ (x - t • e) - Φ x) g‖
      ≤ ‖t⁻¹ * (Z x - Z (x - t • e))‖ * (C * ‖g‖) + ‖Z x‖ * (L * ‖e‖ * ‖g‖) := by gcongr
    _ = C * (‖t⁻¹ * (Z x - Z (x - t • e))‖ * ‖g‖) + L * ‖e‖ * (‖Z x‖ * ‖g‖) := by ring

/-- **Moving a difference quotient onto a Lipschitz-weighted field.** Let `z ∈ H¹(ℝⁿ)` and let
`Φ` be a field of linear forms bounded by `C` and `L`-Lipschitz. For every `v ∈ H¹(ℝⁿ)`, every
direction `e` and every step `t`,

`|∫ z Φ(∇Dᵗ v)| ≤ ‖e‖ (C ‖∇z‖_{L²} + L ‖z‖_{L²}) ‖∇v‖_{L²}`.

A translation moves the difference quotient from `∇v` onto the field `z Φ`, and the product rule
for difference quotients splits `D⁻ᵗ(z Φ)` into `(D⁻ᵗ z) Φ(· - t e)`, bounded through
`‖D⁻ᵗ z‖_{L²} ≤ ‖e‖ ‖∇z‖_{L²}`, and `z D⁻ᵗ Φ`, bounded through the Lipschitz constant. -/
theorem W1p.abs_integral_value_mul_gradient_differenceQuotient_le
    {Φ : E → StrongDual ℝ E} {C : ℝ} {L : ℝ≥0}
    (hC : ∀ x, ‖Φ x‖ ≤ C) (hL : LipschitzWith L Φ) (z v : W1p mu ⊤ 2)
    (e : E) (t : ℝ) :
    |∫ x, W1p.value z x * Φ x (W1p.gradient
      (W1p.differenceQuotient le_rfl e t (Set.mapsTo_univ (· + t • e) _) v) x) ∂mu|
      ≤ ‖e‖ * (C * ‖W1p.gradient z‖ + L * ‖W1p.value z‖) * ‖W1p.gradient v‖ := by
  have hle : mu ≤ mu.restrict ((⊤ : Opens E) : Set E) := by
    rw [Opens.coe_top, Measure.restrict_univ]
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  set Z : E → ℝ := fun x ↦ W1p.value z x
  set G : E → E := fun x ↦ W1p.gradient v x
  set Dz := W1p.value (W1p.differenceQuotient le_rfl e (-t) (Set.mapsTo_univ (· + (-t) • e) _) z)
  have hZ : MemLp Z 2 mu := (Lp.memLp (W1p.value z)).mono_measure hle
  have hG : MemLp G 2 mu := (Lp.memLp (W1p.gradient v)).mono_measure hle
  have hDz : MemLp (Dz : E → ℝ) 2 mu := (Lp.memLp Dz).mono_measure hle
  have hΦm : AEStronglyMeasurable Φ mu := hL.continuous.aestronglyMeasurable
  have happ : ∀ {p : E → E} {q : E →
      StrongDual ℝ E}, AEStronglyMeasurable q mu →
      AEStronglyMeasurable p mu → AEStronglyMeasurable (fun x ↦ q x (p x)) mu :=
    fun hq hp ↦ (continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable
      (hq.prodMk hp)
  -- Translates of `Z`, `G` and `Φ`.
  have hZs : MemLp (fun x ↦ Z (x - t • e)) 2 mu := by
    have := hZ.comp_measurePreserving (measurePreserving_add_right mu (-(t • e)))
    simpa [Function.comp_def, sub_eq_add_neg] using this
  have hGs : MemLp (fun x ↦ G (x + t • e)) 2 mu :=
    hG.comp_measurePreserving (measurePreserving_add_right mu _)
  have hΦs : AEStronglyMeasurable (fun x ↦ Φ (x - t • e)) mu :=
    (hL.continuous.comp (continuous_sub_right _)).aestronglyMeasurable
  have hint : ∀ {P : E → ℝ} {q : E →
      StrongDual ℝ E} {p : E → E},
      MemLp P 2 mu → AEStronglyMeasurable q mu → (∀ x, ‖q x‖ ≤ C) → MemLp p 2 mu →
      Integrable (fun x ↦ P x * q x (p x)) mu := fun {P q p} hP hq hqC hp ↦
    ((hP.norm.integrable_mul hp.norm).const_mul C).mono'
      (hP.aestronglyMeasurable.mul (happ hq hp.aestronglyMeasurable))
      (Filter.Eventually.of_forall fun x ↦ by
        rw [Pi.mul_apply, norm_mul, mul_left_comm]
        exact mul_le_mul_of_nonneg_left (((q x).le_opNorm _).trans
          (mul_le_mul_of_nonneg_right (hqC x) (norm_nonneg _))) (norm_nonneg _))
  have hI1 := hint hZ hΦm hC hGs
  have hI2 := hint hZ hΦm hC hG
  have hI3 := hint hZs hΦs (fun x ↦ hC _) hG
  -- The difference quotient, moved by a translation from `∇v` onto `z Φ`.
  have htrans : ∫ x, Z x * Φ x (G (x + t • e)) ∂mu =
      ∫ x, Z (x - t • e) * Φ (x - t • e) (G x) ∂mu := by
    rw [← integral_add_right_eq_self (fun x ↦ Z (x - t • e) * Φ (x - t • e) (G x)) (t • e)]
    simp only [add_sub_cancel_right]
  have hrepr : ∫ x, W1p.value z x * Φ x (W1p.gradient
      (W1p.differenceQuotient le_rfl e t (Set.mapsTo_univ (· + t • e) _) v) x) ∂mu
      = ∫ x, t⁻¹ * (Z (x - t • e) * Φ (x - t • e) (G x) - Z x * Φ x (G x)) ∂mu := by
    calc _ = ∫ x, t⁻¹ * (Z x * Φ x (G (x + t • e)) - Z x * Φ x (G x)) ∂mu := by
          refine integral_congr_ae ?_
          filter_upwards [(W1p.gradient_differenceQuotient_ae le_rfl e t
            (Set.mapsTo_univ (· + t • e) _) v).filter_mono (ae_mono hle)] with x hx
          rw [hx, map_smul, map_sub, smul_eq_mul]
          ring
      _ = t⁻¹ * (∫ x, Z x * Φ x (G (x + t • e)) ∂mu - ∫ x, Z x * Φ x (G x) ∂mu) := by
          rw [integral_const_mul, integral_sub hI1 hI2]
      _ = _ := by
          rw [htrans, ← integral_sub hI3 hI2, ← integral_const_mul]
  -- The pointwise bound by the product rule for difference quotients.
  have hpt : ∀ᵐ x ∂mu, ‖t⁻¹ * (Z (x - t • e) * Φ (x - t • e) (G x) - Z x * Φ x (G x))‖
      ≤ C * (‖Dz x‖ * ‖G x‖) + L * ‖e‖ * (‖Z x‖ * ‖G x‖) := by
    filter_upwards [(W1p.value_differenceQuotient_ae le_rfl e (-t)
      (Set.mapsTo_univ (· + (-t) • e) _) z).filter_mono (ae_mono hle)] with x hx
    have hDx : Dz x = t⁻¹ * (Z x - Z (x - t • e)) := by
      rw [hx, neg_smul, ← sub_eq_add_neg, inv_neg]
      ring
    rw [hDx]
    exact norm_inv_mul_sub_le hC hL
  -- Cauchy--Schwarz, and the difference-quotient bound on `z`.
  have hDzG := Lp.integral_norm_mul_norm_le hle hle Dz (W1p.gradient v)
  have hZG := Lp.integral_norm_mul_norm_le hle hle (W1p.value z) (W1p.gradient v)
  have hDzn : ‖Dz‖ ≤ ‖e‖ * ‖W1p.gradient z‖ :=
    W1p.norm_value_differenceQuotient_le (by norm_num) e (-t) z
  have hint1 : Integrable (fun x ↦ ‖Dz x‖ * ‖G x‖) mu := hDz.norm.integrable_mul hG.norm
  have hint2 : Integrable (fun x ↦ ‖Z x‖ * ‖G x‖) mu := hZ.norm.integrable_mul hG.norm
  rw [hrepr]
  calc |∫ x, t⁻¹ * (Z (x - t • e) * Φ (x - t • e) (G x) - Z x * Φ x (G x)) ∂mu|
      ≤ ∫ x, ‖t⁻¹ * (Z (x - t • e) * Φ (x - t • e) (G x) - Z x * Φ x (G x))‖ ∂mu := by
        rw [← Real.norm_eq_abs]
        exact norm_integral_le_integral_norm _
    _ ≤ ∫ x, (C * (‖Dz x‖ * ‖G x‖) + L * ‖e‖ * (‖Z x‖ * ‖G x‖)) ∂mu :=
        integral_mono_ae ((hI3.sub hI2).const_mul t⁻¹).norm
          ((hint1.const_mul C).add (hint2.const_mul _)) hpt
    _ = C * ∫ x, ‖Dz x‖ * ‖G x‖ ∂mu + L * ‖e‖ * ∫ x, ‖Z x‖ * ‖G x‖ ∂mu := by
        rw [integral_add (hint1.const_mul C) (hint2.const_mul _), integral_const_mul,
          integral_const_mul]
    _ ≤ C * (‖Dz‖ * ‖W1p.gradient v‖) + L * ‖e‖ * (‖W1p.value z‖ * ‖W1p.gradient v‖) := by
        gcongr
    _ ≤ C * ((‖e‖ * ‖W1p.gradient z‖) * ‖W1p.gradient v‖) +
          L * ‖e‖ * (‖W1p.value z‖ * ‖W1p.gradient v‖) := by gcongr
    _ = ‖e‖ * (C * ‖W1p.gradient z‖ + L * ‖W1p.value z‖) * ‖W1p.gradient v‖ := by ring

end TauCeti
