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
import TauCeti.Analysis.Sobolev.W1p.Symmetry
import TauCeti.MeasureTheory.Function.LpSeminorm.CompactExhaustion
import TauCeti.MeasureTheory.Function.Lp.FiniteDimensional
import TauCeti.Analysis.Calculus.FDeriv.Remainder

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

The difference quotients also converge: `t⁻¹ (u(· + t v) - u) → ⟪v, ∇u⟫` in `Lᵖ` as `t → 0`. On
the whole space this follows from the uniform bound and the density of test functions, for which
the error is `O(t)`. On a domain mapped into itself by every translation `x ↦ x + t v`, such as a
half-space with `v` parallel to its boundary, it holds on all of `Ω`: on a compact set `u` agrees
with a whole-space Sobolev function, and off a large compact set both the difference quotients and
`⟪v, ∇u⟫` are small. If moreover every first derivative of `u` lies in `W^{1,p}(Ω)`, the difference
quotients converge to `∂_v u` in `W^{1,p}(Ω)`, so a tangential derivative of a function with zero
boundary values again has zero boundary values. This is the step of the regularity theory up to
a flat boundary that differentiates the equation in tangential directions.

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
* `TauCeti.W1p.differenceQuotient_mem_w1p0Submodule`,
  `TauCeti.W1p0.extendByZeroL_eq_differenceQuotient`,
  `TauCeti.W1p0.norm_value_differenceQuotient_le`: on a domain mapped onto itself by the
  translation, difference quotients preserve `W^{1,p}_0(Ω)`, commute with extension by zero, and
  satisfy the whole-space bound.

* `TauCeti.W1p.eLpNorm_inv_mul_value_comp_add_smul_sub_le_of_isOpen`: the difference-quotient
  bound on an open set, with no compactness.
* `TauCeti.W1p.tendsto_eLpNorm_inv_mul_value_comp_add_smul_sub_sub_inner_top` and
  `TauCeti.W1p.tendsto_eLpNorm_inv_mul_value_comp_add_smul_sub_sub_inner`: the difference
  quotients converge in `Lᵖ`, on the whole space and on a translation-invariant domain.
* `TauCeti.W1p.tendsto_differenceQuotient`: on a translation-invariant domain, the difference
  quotients of a function with first derivatives in `W^{1,p}(Ω)` converge in `W^{1,p}(Ω)`.
* `TauCeti.W1p.mem_w1p0Submodule_of_hasWeakLineDerivOn`: a tangential derivative of such a
  function in `W^{1,p}_0(Ω)` lies in `W^{1,p}_0(Ω)`.

Translations parallel to the boundary of a half-space map it onto itself, so the statements on
translation-invariant domains are what a difference-quotient argument in tangential directions
uses.

## References

* L. C. Evans, *Partial Differential Equations*, §5.8.2, Theorem 3 (i), and §6.3.2 (proof of
  Theorem 5, where the tangential derivatives of the solution are shown to lie in `H¹₀`).
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

/-- **The local translation estimate for a test function**, as an element of `W^{1,p}(ℝⁿ)`: the
smooth estimate `ContDiff.eLpNorm_comp_add_sub_le_eLpNorm_fderiv_apply` for the value and the
weak gradient of its jet. -/
private theorem eLpNorm_value_ofTestFunctionₗ_comp_add_sub_le (phi : 𝓓((⊤ : Opens E), ℝ)) (h : E)
    {K T : Set E} (hT : MeasurableSet T) (hKT : ∀ x ∈ K, ∀ t ∈ Icc (0 : ℝ) 1, x + t • h ∈ T) :
    eLpNorm (fun x ↦ W1p.value (W1p.ofTestFunctionₗ mu ⊤ p phi) (x + h) -
      W1p.value (W1p.ofTestFunctionₗ mu ⊤ p phi) x) p (mu.restrict K) ≤
      eLpNorm (fun x ↦ ⟪h, W1p.gradient (W1p.ofTestFunctionₗ mu ⊤ p phi) x⟫_ℝ) p
        (mu.restrict T) := by
  have htop : mu.restrict ((⊤ : Opens E) : Set E) = mu := by
    simp only [Opens.coe_top, Measure.restrict_univ]
  have hq : Tendsto (· + h) (ae mu) (ae mu) :=
    (measurePreserving_add_right mu h).quasiMeasurePreserving.tendsto_ae
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
  rw [hL, hR]
  have hphi : ContDiff ℝ 1 (phi : E → ℝ) := phi.contDiff.of_le (by simp)
  exact hphi.eLpNorm_comp_add_sub_le_eLpNorm_fderiv_apply Fact.out h hT hKT

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
  -- Both sides are extended norms of continuous linear images of `w`.
  set A : W1p mu ⊤ p →L[ℝ] Lp ℝ p (nu.restrict K) :=
    (LpToLpRestrictCLM E ℝ ℝ nu p K).comp
      (((nu.translateLp p h).toLinearIsometry.toContinuousLinearMap -
        ContinuousLinearMap.id ℝ _).comp W1p.valueL)
  set B : W1p mu ⊤ p →L[ℝ] Lp ℝ p (nu.restrict T) :=
    (LpToLpRestrictCLM E ℝ ℝ nu p T).comp (((innerSL ℝ h).compLpL p nu).comp W1p.gradientL)
  have hA : ∀ v : W1p mu ⊤ p, ‖A v‖ₑ =
      eLpNorm (fun x ↦ W1p.value v (x + h) - W1p.value v x) p (mu.restrict K) := fun v ↦ by
    rw [Lp.eNorm_def]
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
    rw [Lp.eNorm_def]
    refine (eLpNorm_congr_ae ?_).trans (by rw [htop])
    filter_upwards [LpToLpRestrictCLM_coeFn ℝ T ((innerSL ℝ h).compLpL p nu (W1p.gradientL v)),
      ae_restrict_of_ae ((innerSL ℝ h).coeFn_compLpL (W1p.gradientL v))] with x h1 h2
    simp only [B, ContinuousLinearMap.comp_apply]
    rw [h1, h2, innerSL_apply_apply, W1p.gradientL_apply]
  have hclosed : IsClosed {v : W1p mu ⊤ p |
      eLpNorm (fun x ↦ W1p.value v (x + h) - W1p.value v x) p (mu.restrict K)
        ≤ eLpNorm (fun x ↦ ⟪h, W1p.gradient v x⟫_ℝ) p (mu.restrict T)} := by
    simp only [← hA, ← hB]
    exact isClosed_le A.continuous.eNorm B.continuous.eNorm
  -- Pass the smooth estimate to all of `W^{1,p}(ℝⁿ)` by density of test functions.
  refine w1p0Submodule_subset_of_isClosed hclosed (fun phi ↦ ?_) (W1p.mem_w1p0Submodule_top hp w)
  exact eLpNorm_value_ofTestFunctionₗ_comp_add_sub_le phi h hT hKT

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
        rw [← mul_assoc, ← eNorm_mul, inv_mul_cancel₀ ht, eNorm_one, one_mul]

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

omit [FiniteDimensional ℝ E] in
/-- The `Lᵖ` norm of the directional derivative `⟪v, ∇u⟫` of `u ∈ W^{1,p}(Ω)` is at most
`‖v‖ ‖∇u‖_p`. -/
theorem W1p.eLpNorm_inner_gradient_le (u : W1p mu Omega p) (v : E) :
    eLpNorm (fun x ↦ ⟪v, W1p.gradient u x⟫_ℝ) p (mu.restrict Omega)
      ≤ ‖v‖ₑ * eLpNorm (W1p.gradient u : E → E) p (mu.restrict Omega) := by
  calc eLpNorm (fun x ↦ ⟪v, W1p.gradient u x⟫_ℝ) p (mu.restrict Omega)
      ≤ eLpNorm (‖v‖ • (W1p.gradient u : E → E)) p (mu.restrict Omega) :=
        eLpNorm_mono_ae (aestronglyMeasurable_const.inner (Lp.aestronglyMeasurable _))
          (Filter.Eventually.of_forall fun x ↦ by
            rw [Pi.smul_apply, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_norm]
            exact abs_real_inner_le_norm v _)
    _ = ‖v‖ₑ * eLpNorm (W1p.gradient u : E → E) p (mu.restrict Omega) := by
        rw [eLpNorm_const_smul, eNorm_norm]

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
  -- The difference quotient itself, through the whole-space translation estimate.
  have hquot : eLpNorm (W1p.value q : E → ℝ) p nu
      ≤ ‖v‖ₑ * eLpNorm (W1p.gradient u : E → E) p nu := by
    rw [hq, eLpNorm_congr_ae
      (W1p.value_differenceQuotient_ae le_rfl v t (Set.mapsTo_univ (· + t • v) _) u)]
    refine le_trans ?_ (W1p.eLpNorm_inner_gradient_le u v)
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
          rw [← mul_assoc, ← eNorm_mul, inv_mul_cancel₀ ht, eNorm_one, one_mul]
  have hfin : ‖v‖ₑ * eLpNorm (W1p.gradient u : E → E) p nu ≠ ∞ :=
    ENNReal.mul_ne_top (by simp) (Lp.eLpNorm_ne_top _)
  calc ‖W1p.value q‖ = (eLpNorm (W1p.value q : E → ℝ) p nu).toReal := Lp.norm_def _
    _ ≤ (‖v‖ₑ * eLpNorm (W1p.gradient u : E → E) p nu).toReal := ENNReal.toReal_mono hfin hquot
    _ = ‖v‖ * ‖W1p.gradient u‖ := by
        rw [ENNReal.toReal_mul, ← Lp.norm_def]
        simp

/-! ### Domains mapped onto themselves by the translation -/

/-- **Difference quotients preserve zero boundary values.** If translation by `t • w` maps `Ω`
onto itself, then the difference quotient of `u ∈ W^{1,p}_0(Ω)` in the direction `w`
with step `t` lies in `W^{1,p}_0(Ω)`. -/
theorem W1p.differenceQuotient_mem_w1p0Submodule {w : E} {t : ℝ}
    (hVO : MapsTo (· + t • w) Omega Omega) (hΩ : ∀ x, x + t • w ∈ Omega → x ∈ Omega)
    {u : W1p mu Omega p} (hu : u ∈ w1p0Submodule mu Omega p) :
    W1p.differenceQuotient le_rfl w t hVO u ∈ w1p0Submodule mu Omega p := by
  rw [W1p.differenceQuotient_def, W1p.restrictL_self]
  exact (w1p0Submodule mu Omega p).toSubmodule.smul_mem _
    (sub_mem (W1p.translate_mem_w1p0Submodule hVO hΩ hu) hu)

/-- **Difference quotients commute with extension by zero.** Let translation by `t • w` map `Ω`
onto itself and `p < ∞`. If `g ∈ W^{1,p}_0(Ω)` is the difference quotient of `u ∈ W^{1,p}_0(Ω)`
in the direction `w` with step `t`, then the zero-extension of `g` to the whole space is the
difference quotient of the zero-extension of `u`. -/
theorem W1p0.extendByZeroL_eq_differenceQuotient {w : E} {t : ℝ}
    (hVO : MapsTo (· + t • w) Omega Omega) (hΩ : ∀ x, x + t • w ∈ Omega → x ∈ Omega)
    {u g : W1p0 mu Omega p}
    (hg : (g : W1p mu Omega p) = W1p.differenceQuotient le_rfl w t hVO (u : W1p mu Omega p)) :
    (W1p0.extendByZeroL le_top g : W1p mu ⊤ p) =
      W1p.differenceQuotient le_rfl w t (Set.mapsTo_univ (· + t • w) _)
        (W1p0.extendByZeroL le_top u : W1p mu ⊤ p) := by
  have hm := Omega.isOpen.measurableSet
  have hsub : (Omega : Set E) ⊆ ((⊤ : Opens E) : Set E) := subset_univ _
  -- Both sides vanish off `Ω`, and on `Ω` they are the difference quotient of `u`.
  have hext : ∀ v : Lp ℝ p (mu.restrict Omega),
      (extendByZeroLpₗᵢ ℝ mu hm hsub v : E → ℝ) =ᵐ[mu] (Omega : Set E).indicator v := fun v => by
    simpa only [Opens.coe_top, Measure.restrict_univ] using coeFn_extendByZeroLpₗᵢ ℝ hm hsub v
  refine W1p.ext_value (Lp.ext ?_)
  rw [W1p0.value_extendByZeroL, hg]
  filter_upwards [ae_restrict_of_ae (hext _), W1p.value_differenceQuotient_ae le_rfl w t
      (Set.mapsTo_univ (· + t • w) _) (W1p0.extendByZeroL le_top u : W1p mu ⊤ p),
    ae_restrict_of_ae (hext (W1p.value (u : W1p mu Omega p))),
    ae_restrict_of_ae ((measurePreserving_add_right mu (t • w)).quasiMeasurePreserving.ae_eq_comp
      (hext (W1p.value (u : W1p mu Omega p)))),
    ae_restrict_of_ae ((ae_restrict_iff' hm).1
      (W1p.value_differenceQuotient_ae le_rfl w t hVO (u : W1p mu Omega p)))]
    with x h1 h2 h3 h4 h5
  simp only [Function.comp_apply] at h4
  rw [h1, h2, W1p0.value_extendByZeroL, h4, h3]
  by_cases hx : x ∈ (Omega : Set E)
  · rw [indicator_of_mem hx, indicator_of_mem hx, indicator_of_mem (hVO hx), h5 hx]
  · rw [indicator_of_notMem hx, indicator_of_notMem hx,
      indicator_of_notMem (mt (hΩ x) hx), sub_zero, mul_zero]

/-- **The difference-quotient bound for zero boundary values.** If translation by `t • w` maps
`Ω` onto itself and `p < ∞`, the difference quotient of `u ∈ W^{1,p}_0(Ω)` satisfies
`‖D^t_w u‖_p ≤ ‖w‖ ‖∇u‖_p`, with no compactness and uniformly in `t`, as on the whole space. -/
theorem W1p0.norm_value_differenceQuotient_le (hp : p ≠ ∞) {w : E} {t : ℝ}
    (hVO : MapsTo (· + t • w) Omega Omega) (hΩ : ∀ x, x + t • w ∈ Omega → x ∈ Omega)
    (u : W1p0 mu Omega p) :
    ‖W1p.value (W1p.differenceQuotient le_rfl w t hVO (u : W1p mu Omega p))‖ ≤
      ‖w‖ * ‖W1p.gradient (u : W1p mu Omega p)‖ := by
  have h := W1p.norm_value_differenceQuotient_le hp w t (W1p0.extendByZeroL le_top u : W1p mu ⊤ p)
  rwa [← W1p0.extendByZeroL_eq_differenceQuotient (g := ⟨_,
      W1p.differenceQuotient_mem_w1p0Submodule hVO hΩ u.2⟩) hVO hΩ rfl,
    W1p0.norm_value_extendByZeroL, W1p0.norm_gradient_extendByZeroL] at h

/-! ### Convergence of difference quotients -/

/-- The set `K + [-1, 1] • v` swept out by `K` under the translations `x ↦ x + s v`, `|s| ≤ 1`. -/
private def sweep (K : Set E) (v : E) : Set E :=
  (fun z : E × ℝ => z.1 + z.2 • v) '' (K ×ˢ Icc (-1 : ℝ) 1)

omit [MeasurableSpace E] [FiniteDimensional ℝ E] [BorelSpace E] in
private theorem isCompact_sweep {K : Set E} (hK : IsCompact K) (v : E) : IsCompact (sweep K v) :=
  (hK.prod isCompact_Icc).image (by fun_prop)

omit [MeasurableSpace E] [FiniteDimensional ℝ E] [BorelSpace E] in
private theorem add_smul_mem_sweep {K : Set E} {v y : E} (hy : y ∈ K) {s : ℝ}
    (hs : s ∈ Icc (-1 : ℝ) 1) : y + s • v ∈ sweep K v :=
  ⟨(y, s), ⟨hy, hs⟩, rfl⟩

omit [MeasurableSpace E] [FiniteDimensional ℝ E] [BorelSpace E] in
private theorem subset_sweep (K : Set E) (v : E) : K ⊆ sweep K v := fun y hy => by
  simpa using add_smul_mem_sweep (v := v) hy (s := 0) ⟨by norm_num, by norm_num⟩

omit [MeasurableSpace E] [FiniteDimensional ℝ E] [BorelSpace E] in
private theorem sweep_subset {v : E} (hΩ : ∀ t : ℝ, MapsTo (· + t • v) Omega Omega) {K : Set E}
    (hK : K ⊆ Omega) : sweep K v ⊆ Omega := by
  rintro _ ⟨⟨y, s⟩, ⟨hy, -⟩, rfl⟩
  exact hΩ s (hK hy)

omit [MeasurableSpace E] [FiniteDimensional ℝ E] [BorelSpace E] in
/-- A point outside `K + [-1, 1] • v` stays outside `K` after a translation by `r • v`,
`|r| ≤ 1`. -/
private theorem add_smul_notMem_of_notMem_sweep {K : Set E} {v x : E} {r : ℝ} (hr : |r| ≤ 1)
    (hx : x ∉ sweep K v) : x + r • v ∉ K :=
  fun h => hx ⟨(x + r • v, -r), ⟨h, by constructor <;> linarith [abs_le.1 hr]⟩, by
    simp [neg_smul]⟩

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- An almost-everywhere property also holds almost everywhere at the translated points
`x + c`. -/
private theorem ae_add_right {P : E → Prop} (h : ∀ᵐ x ∂mu, P x) (c : E) : ∀ᵐ x ∂mu, P (x + c) :=
  (measurePreserving_add_right mu c).quasiMeasurePreserving.tendsto_ae.eventually h

omit [MeasurableSpace E] [FiniteDimensional ℝ E] [BorelSpace E] in
/-- For a test function `φ` whose derivative is `L`-Lipschitz and `0 < |t| ≤ 1`, the error of the
difference quotient is at most `L |t| ‖v‖²`, and it vanishes off `tsupport φ + [-1, 1] • v`. -/
private theorem norm_inv_mul_comp_add_smul_sub_sub_fderiv_le (φ : 𝓓((⊤ : Opens E), ℝ))
    {L : NNReal} (hL : LipschitzWith L (fderiv ℝ (φ : E → ℝ))) (v x : E) {t : ℝ} (ht0 : t ≠ 0)
    (ht : |t| ≤ 1) :
    ‖t⁻¹ * ((φ : E → ℝ) (x + t • v) - φ x) - fderiv ℝ (φ : E → ℝ) x v‖ ≤
      (sweep (tsupport (φ : E → ℝ)) v).indicator (fun _ => (L : ℝ) * |t| * ‖v‖ ^ 2) x := by
  by_cases hx : x ∈ sweep (tsupport (φ : E → ℝ)) v
  · rw [indicator_of_mem hx]
    have h := norm_sub_sub_fderiv_le_of_lipschitzWith
      (φ.contDiff.differentiable (by simp)) hL x (t • v)
    simp only [map_smul, smul_eq_mul, norm_smul, Real.norm_eq_abs] at h
    have hrw : t⁻¹ * ((φ : E → ℝ) (x + t • v) - φ x) - fderiv ℝ (φ : E → ℝ) x v =
        t⁻¹ * ((φ : E → ℝ) (x + t • v) - φ x - t * fderiv ℝ (φ : E → ℝ) x v) := by
      field_simp
    rw [hrw, norm_mul, norm_inv, Real.norm_eq_abs, inv_mul_le_iff₀ (abs_pos.2 ht0)]
    exact h.trans_eq (by ring)
  · rw [indicator_of_notMem hx]
    have h0 : x ∉ tsupport (φ : E → ℝ) := fun h => hx (subset_sweep _ v h)
    rw [image_eq_zero_of_notMem_tsupport (add_smul_notMem_of_notMem_sweep ht hx),
      image_eq_zero_of_notMem_tsupport h0, fderiv_of_notMem_tsupport ℝ h0]
    simp

omit [FiniteDimensional ℝ E] in
/-- **Difference quotients of a test function converge in `Lᵖ`.** For a test function `φ` on the
whole space, a direction `v` and `p < ∞`, `‖t⁻¹ (φ(· + t v) - φ) - Dφ v‖_{Lᵖ} → 0` as `t → 0`. -/
private theorem tendsto_eLpNorm_inv_mul_comp_add_smul_sub_sub_fderiv (hp : p ≠ ∞)
    (φ : 𝓓((⊤ : Opens E), ℝ)) (v : E) :
    Tendsto (fun t : ℝ => eLpNorm (fun x => t⁻¹ * ((φ : E → ℝ) (x + t • v) - φ x) -
      fderiv ℝ (φ : E → ℝ) x v) p mu) (𝓝[≠] 0) (𝓝 0) := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne'
  have hφ := φ.contDiff
  have hφc : HasCompactSupport (φ : E → ℝ) := φ.hasCompactSupport
  obtain ⟨L, hL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport (hφc.fderiv ℝ)
    (hφ.fderiv_right (m := 1) (by simp)) one_ne_zero
  set S := sweep (tsupport (φ : E → ℝ)) v
  have hS : IsCompact S := isCompact_sweep hφc.isCompact v
  -- For `0 < |t| ≤ 1` the `Lᵖ` norm is at most `L |t| ‖v‖² μ(S)^(1/p)`.
  have hbound : ∀ t : ℝ, t ≠ 0 → |t| ≤ 1 → eLpNorm (fun x =>
      t⁻¹ * ((φ : E → ℝ) (x + t • v) - φ x) - fderiv ℝ (φ : E → ℝ) x v) p mu ≤
        ENNReal.ofReal ((L : ℝ) * |t| * ‖v‖ ^ 2) * mu S ^ (1 / p.toReal) := fun t ht0 ht => by
    have hc : Continuous fun x => t⁻¹ * ((φ : E → ℝ) (x + t • v) - φ x) -
        fderiv ℝ (φ : E → ℝ) x v := by
      have := φ.continuous
      have := hφ.continuous_fderiv (by simp)
      fun_prop
    refine (eLpNorm_mono_real hc.aestronglyMeasurable fun x =>
      norm_inv_mul_comp_add_smul_sub_sub_fderiv_le φ hL v x ht0 ht).trans ?_
    rw [eLpNorm_indicator_const hS.isClosed.measurableSet.nullMeasurableSet hp0 hp, ← ofReal_norm,
      Real.norm_of_nonneg (by positivity)]
  have hlim : Tendsto (fun t : ℝ => ENNReal.ofReal ((L : ℝ) * |t| * ‖v‖ ^ 2) *
      mu S ^ (1 / p.toReal)) (𝓝 0) (𝓝 0) := by
    have hc : Continuous fun t : ℝ => (L : ℝ) * |t| * ‖v‖ ^ 2 := by fun_prop
    have h := ENNReal.tendsto_ofReal (hc.tendsto (0 : ℝ))
    simp only [abs_zero, mul_zero, zero_mul, ENNReal.ofReal_zero] at h
    simpa using ENNReal.Tendsto.mul_const h (Or.inr (ENNReal.rpow_ne_top_of_nonneg (by positivity)
      hS.measure_lt_top.ne))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (hlim.mono_left nhdsWithin_le_nhds) (Eventually.of_forall fun _ => zero_le) ?_
  filter_upwards [self_mem_nhdsWithin,
    nhdsWithin_le_nhds (Metric.closedBall_mem_nhds (0 : ℝ) one_pos)] with t ht0 ht
  exact hbound t ht0 (by simpa using ht)

/-- **The difference-quotient bound on an open set.** Let `u ∈ W^{1,p}(Ω)`, `1 ≤ p < ∞`, and let
`A` be open. If every segment `[x, x + t v]` with `x ∈ A` lies in a set `T ⊆ Ω`, then

`‖t⁻¹ (u(· + t v) - u)‖_{Lᵖ(A)} ≤ ‖⟪v, ∇u⟫‖_{Lᵖ(T)}`.

This is `TauCeti.W1p.eLpNorm_inv_mul_value_comp_add_smul_sub_le` without compactness of `A`; on a
domain mapped into itself by the translations `x ↦ x + s v` it applies to `A = T = Ω`. -/
theorem W1p.eLpNorm_inv_mul_value_comp_add_smul_sub_le_of_isOpen (hp : p ≠ ∞)
    (u : W1p mu Omega p) (v : E) (t : ℝ) {A T : Set E} (hA : IsOpen A) (hTO : T ⊆ Omega)
    (hAT : ∀ x ∈ A, ∀ s ∈ Icc (0 : ℝ) 1, x + s • t • v ∈ T) :
    eLpNorm (fun x ↦ t⁻¹ * (W1p.value u (x + t • v) - W1p.value u x)) p (mu.restrict A)
      ≤ eLpNorm (fun x ↦ ⟪v, W1p.gradient u x⟫_ℝ) p (mu.restrict T) :=
  eLpNorm_restrict_le_of_forall_isCompact hA fun _ hK hKA =>
    W1p.eLpNorm_inv_mul_value_comp_add_smul_sub_le hp u v t hK hTO fun x hx => hAT x (hKA hx)

/-- On the whole space the error `t⁻¹ (z(· + t v) - z) - ⟪v, ∇z⟫` of the difference quotient is
at most `2 ‖v‖ ‖z‖` in `Lᵖ`, uniformly in `t`. -/
private theorem eLpNorm_inv_mul_value_comp_add_smul_sub_sub_inner_le_top (hp : p ≠ ∞)
    (z : W1p mu ⊤ p) (v : E) (t : ℝ) :
    eLpNorm (fun x => t⁻¹ * (W1p.value z (x + t • v) - W1p.value z x) -
      ⟪v, W1p.gradient z x⟫_ℝ) p mu ≤ 2 * (‖v‖ₑ * ‖z‖ₑ) := by
  have h1 : eLpNorm (fun x => t⁻¹ * (W1p.value z (x + t • v) - W1p.value z x)) p mu ≤
      eLpNorm (fun x => ⟪v, W1p.gradient z x⟫_ℝ) p mu := by
    simpa only [Opens.coe_top, Measure.restrict_univ] using
      W1p.eLpNorm_inv_mul_value_comp_add_smul_sub_le_of_isOpen hp z v t (T := univ) isOpen_univ
        (by simp) fun _ _ _ _ => mem_univ _
  have h2 : eLpNorm (fun x => ⟪v, W1p.gradient z x⟫_ℝ) p mu ≤ ‖v‖ₑ * ‖z‖ₑ := by
    have h := W1p.eLpNorm_inner_gradient_le z v
    rw [← Lp.eNorm_def] at h
    simp only [Opens.coe_top, Measure.restrict_univ] at h
    exact h.trans (by gcongr; exact W1p.enorm_gradient_le z)
  calc _ ≤ eLpNorm (fun x => t⁻¹ * (W1p.value z (x + t • v) - W1p.value z x)) p mu +
        eLpNorm (fun x => ⟪v, W1p.gradient z x⟫_ℝ) p mu := eLpNorm_sub_le Fact.out
    _ ≤ ‖v‖ₑ * ‖z‖ₑ + ‖v‖ₑ * ‖z‖ₑ := add_le_add (h1.trans h2) h2
    _ = 2 * (‖v‖ₑ * ‖z‖ₑ) := (two_mul _).symm

omit [FiniteDimensional ℝ E] in
/-- On the whole space the `Lᵖ` error of the difference quotient is subadditive in the
function. -/
private theorem eLpNorm_inv_mul_value_comp_add_smul_sub_sub_inner_add_le_top (z₁ z₂ : W1p mu ⊤ p)
    (v : E) (t : ℝ) :
    eLpNorm (fun x => t⁻¹ * (W1p.value (z₁ + z₂) (x + t • v) - W1p.value (z₁ + z₂) x) -
      ⟪v, W1p.gradient (z₁ + z₂) x⟫_ℝ) p mu ≤
    eLpNorm (fun x => t⁻¹ * (W1p.value z₁ (x + t • v) - W1p.value z₁ x) -
      ⟪v, W1p.gradient z₁ x⟫_ℝ) p mu +
    eLpNorm (fun x => t⁻¹ * (W1p.value z₂ (x + t • v) - W1p.value z₂ x) -
      ⟪v, W1p.gradient z₂ x⟫_ℝ) p mu := by
  refine (eLpNorm_congr_ae ?_).trans_le (eLpNorm_add_le Fact.out)
  have hv := W1p.value_add_ae z₁ z₂
  have hg := Lp.coeFn_add (W1p.gradient z₁) (W1p.gradient z₂)
  simp only [Opens.coe_top, Measure.restrict_univ] at hv hg
  filter_upwards [hv, ae_add_right hv (t • v), hg] with x h1 h2 h3
  simp only [Pi.add_apply] at h1 h2 h3 ⊢
  rw [h1, h2, W1p.gradient_add, h3, inner_add_right]
  ring

/-- **Difference quotients converge on the whole space.** For `w ∈ W^{1,p}(ℝⁿ)`, `1 ≤ p < ∞`, and
a direction `v`,

`‖t⁻¹ (w(· + t v) - w) - ⟪v, ∇w⟫‖_{Lᵖ} → 0` as `t → 0`. -/
theorem W1p.tendsto_eLpNorm_inv_mul_value_comp_add_smul_sub_sub_inner_top (hp : p ≠ ∞)
    (w : W1p mu ⊤ p) (v : E) :
    Tendsto (fun t : ℝ => eLpNorm (fun x => t⁻¹ * (W1p.value w (x + t • v) - W1p.value w x) -
      ⟪v, W1p.gradient w x⟫_ℝ) p mu) (𝓝[≠] 0) (𝓝 0) := by
  -- The difference quotients are bounded by `‖v‖ ‖∇w‖_p` uniformly in `t`, so the convergence
  -- passes from the dense subspace of test functions to all of `W^{1,p}(ℝⁿ)`.
  -- For test functions the error tends to zero.
  have hφ : ∀ φ : 𝓓((⊤ : Opens E), ℝ), Tendsto (fun t : ℝ => eLpNorm (fun x =>
      t⁻¹ * (W1p.value (W1p.ofTestFunctionₗ mu ⊤ p φ) (x + t • v) -
        W1p.value (W1p.ofTestFunctionₗ mu ⊤ p φ) x) -
      ⟪v, W1p.gradient (W1p.ofTestFunctionₗ mu ⊤ p φ) x⟫_ℝ) p mu) (𝓝[≠] 0) (𝓝 0) := fun φ => by
    refine (tendsto_eLpNorm_inv_mul_comp_add_smul_sub_sub_fderiv (mu := mu) hp φ v).congr'
      (Eventually.of_forall fun t => eLpNorm_congr_ae ?_)
    have hv := W1p.value_ofTestFunctionₗ_top_ae (mu := mu) (p := p) φ
    filter_upwards [hv, ae_add_right hv (t • v), W1p.gradient_ofTestFunctionₗ_top_ae (p := p) φ]
      with x h1 h2 h3
    rw [h1, h2, h3, real_inner_comm, inner_gradient_left]
  -- Approximate `w` by a test function `φ` with `2 ‖v‖ ‖w - φ‖ < ε / 2`.
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  have hlim : Tendsto (fun η : ℝ≥0∞ => 2 * (‖v‖ₑ * η)) (𝓝 0) (𝓝 0) := by
    have h := ENNReal.Tendsto.const_mul (ENNReal.Tendsto.const_mul (tendsto_id (x := 𝓝 0))
      (Or.inr (eNorm_ne_top (x := v)))) (Or.inr (ENNReal.ofNat_ne_top (n := 2)))
    simpa only [id, mul_zero] using h
  obtain ⟨δ, hδ, hδsub⟩ := ENNReal.nhds_zero_basis.eventually_iff.1
    (hlim.eventually (gt_mem_nhds (ENNReal.half_pos hε.ne')))
  obtain ⟨η, hη0, hηδ⟩ := exists_between hδ
  have hw : w ∈ closure (range (W1p.ofTestFunctionₗ mu ⊤ p)) := by
    rw [← coe_w1p0Submodule]
    exact W1p.mem_w1p0Submodule_top hp w
  obtain ⟨_, ⟨φ, rfl⟩, hwφ⟩ := EMetric.mem_closure_iff.1 hw η hη0
  rw [eDist_eq_eNorm_sub] at hwφ
  filter_upwards [(hφ φ).eventually (ENNReal.nhds_zero_basis.mem_of_mem
    (ENNReal.half_pos hε.ne'))] with t ht
  have hsplit := eLpNorm_inv_mul_value_comp_add_smul_sub_sub_inner_add_le_top
    (W1p.ofTestFunctionₗ mu ⊤ p φ) (w - W1p.ofTestFunctionₗ mu ⊤ p φ) v t
  rw [add_sub_cancel] at hsplit
  calc _ ≤ _ := hsplit
    _ ≤ ε / 2 + ε / 2 := add_le_add ht.le
        ((eLpNorm_inv_mul_value_comp_add_smul_sub_sub_inner_le_top hp _ v t).trans
          (hδsub (hwφ.trans hηδ)).le)
    _ = ε := ENNReal.add_halves ε

/-- Off `K₀ + [-1, 1] • v`, the `Lᵖ` error of a difference quotient with `|t| ≤ 1` on a
translation-invariant domain is at most twice the `Lᵖ` norm of `⟪v, ∇u⟫` off `K₀`. -/
private theorem eLpNorm_inv_mul_value_comp_add_smul_sub_sub_inner_restrict_sdiff_le
    (hp : p ≠ ∞) (u : W1p mu Omega p) {v : E} (hΩ : ∀ t : ℝ, MapsTo (· + t • v) Omega Omega)
    {K₀ : Set E} (hK₀ : IsCompact K₀) {t : ℝ} (ht : |t| ≤ 1) :
    eLpNorm (fun x => t⁻¹ * (W1p.value u (x + t • v) - W1p.value u x) - ⟪v, W1p.gradient u x⟫_ℝ)
      p (mu.restrict (Omega \ sweep K₀ v)) ≤
    eLpNorm (fun x => ⟪v, W1p.gradient u x⟫_ℝ) p (mu.restrict (Omega \ K₀)) +
      eLpNorm (fun x => ⟪v, W1p.gradient u x⟫_ℝ) p (mu.restrict (Omega \ K₀)) := by
  set K := sweep K₀ v
  have hK : IsCompact K := isCompact_sweep hK₀ v
  -- The segments of length `|t| ‖v‖` from points off `K` stay in `Ω` and miss `K₀`.
  have h1 := W1p.eLpNorm_inv_mul_value_comp_add_smul_sub_le_of_isOpen hp u v t
    (A := Omega \ K) (T := Omega \ K₀) (Omega.isOpen.sdiff hK.isClosed) sdiff_subset
    fun x hx s hs => ⟨by simpa [smul_smul] using hΩ (s * t) hx.1, by
      rw [smul_smul]
      refine add_smul_notMem_of_notMem_sweep ?_ hx.2
      rw [abs_mul, abs_of_nonneg hs.1]
      nlinarith [abs_nonneg t, hs.2]⟩
  have h2 : eLpNorm (fun x => ⟪v, W1p.gradient u x⟫_ℝ) p (mu.restrict (Omega \ K)) ≤
      eLpNorm (fun x => ⟪v, W1p.gradient u x⟫_ℝ) p (mu.restrict (Omega \ K₀)) :=
    eLpNorm_mono_measure _
      (Measure.restrict_mono (sdiff_subset_sdiff_right (subset_sweep K₀ v)) le_rfl)
  exact (eLpNorm_sub_le Fact.out).trans (add_le_add h1 h2)

/-- **Difference quotients converge on a translation-invariant domain.** Let `Ω` be mapped into
itself by every translation `x ↦ x + t v`, as a half-space is for `v` parallel to its boundary. For
`u ∈ W^{1,p}(Ω)`, `1 ≤ p < ∞`,

`‖t⁻¹ (u(· + t v) - u) - ⟪v, ∇u⟫‖_{Lᵖ(Ω)} → 0` as `t → 0`.

No regularity of `∂Ω` is needed. -/
theorem W1p.tendsto_eLpNorm_inv_mul_value_comp_add_smul_sub_sub_inner (hp : p ≠ ∞)
    (u : W1p mu Omega p) {v : E} (hΩ : ∀ t : ℝ, MapsTo (· + t • v) Omega Omega) :
    Tendsto (fun t : ℝ => eLpNorm (fun x => t⁻¹ * (W1p.value u (x + t • v) - W1p.value u x) -
      ⟪v, W1p.gradient u x⟫_ℝ) p (mu.restrict Omega)) (𝓝[≠] 0) (𝓝 0) := by
  -- On a compact set the difference quotients are those of a whole-space Sobolev function, where
  -- they converge; off a large compact set both the difference quotients and the directional
  -- derivative are small, by `TauCeti.W1p.eLpNorm_inv_mul_value_comp_add_smul_sub_le_of_isOpen`.
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  -- Cut off the tail of `⟪v, ∇u⟫` off a compact `K₀`, and let `K = K₀ + [-1, 1] • v`.
  obtain ⟨K₀, hK₀c, hK₀Ω, hK₀⟩ := exists_isCompact_eLpNorm_restrict_sdiff_le Omega.isOpen hp
    ((Lp.memLp (W1p.gradient u)).const_inner (𝕜 := ℝ) v)
    (ENNReal.half_pos (ENNReal.half_pos hε.ne').ne')
  set K := sweep K₀ v
  have hKc : IsCompact K := isCompact_sweep hK₀c v
  -- Near `K`, `u` is a whole-space Sobolev function `w`, so on `K` its error is that of `w`.
  obtain ⟨w, hwv, hwg⟩ := W1p.exists_top_value_gradient_ae_eq_on_of_isCompact hp u
    (isCompact_sweep hKc v) (sweep_subset hΩ (sweep_subset hΩ hK₀Ω))
  have hloc : ∀ t : ℝ, |t| ≤ 1 → eLpNorm (fun x => t⁻¹ * (W1p.value u (x + t • v) -
      W1p.value u x) - ⟪v, W1p.gradient u x⟫_ℝ) p (mu.restrict K) ≤ eLpNorm (fun x =>
        t⁻¹ * (W1p.value w (x + t • v) - W1p.value w x) - ⟪v, W1p.gradient w x⟫_ℝ) p mu :=
    fun t ht => by
    refine le_of_eq_of_le (eLpNorm_congr_ae ?_) (eLpNorm_mono_measure _ Measure.restrict_le_self)
    filter_upwards [ae_restrict_mem hKc.isClosed.measurableSet, ae_restrict_of_ae hwv,
      ae_restrict_of_ae (ae_add_right hwv (t • v)), ae_restrict_of_ae hwg] with x hx h1 h2 h3
    have hx0 : x ∈ sweep K v := subset_sweep K v hx
    simp only [h1 hx0, h2 (add_smul_mem_sweep hx (abs_le.1 ht)), h3 hx0]
  filter_upwards [(W1p.tendsto_eLpNorm_inv_mul_value_comp_add_smul_sub_sub_inner_top hp w
      v).eventually (ENNReal.nhds_zero_basis.mem_of_mem (ENNReal.half_pos hε.ne')),
    nhdsWithin_le_nhds (Metric.closedBall_mem_nhds (0 : ℝ) one_pos)] with t ht1 ht2
  have ht : |t| ≤ 1 := by simpa using ht2
  calc _ ≤ _ := eLpNorm_restrict_le_add_restrict_sdiff Fact.out _ hKc.isClosed.measurableSet
    _ ≤ ε / 2 + (ε / 2 / 2 + ε / 2 / 2) := add_le_add ((hloc t ht).trans ht1.le)
        ((eLpNorm_inv_mul_value_comp_add_smul_sub_sub_inner_restrict_sdiff_le hp u hΩ hK₀c
          ht).trans (add_le_add hK₀ hK₀))
    _ = ε := by rw [ENNReal.add_halves, ENNReal.add_halves]

/-- **Difference quotients converge in `W^{1,p}(Ω)`.** Let `Ω` be mapped into itself by every
translation `x ↦ x + t v`, let `1 ≤ p < ∞`, and let `u ∈ W^{1,p}(Ω)` have every first derivative
`∂_y u` in `W^{1,p}(Ω)`. If `d ∈ W^{1,p}(Ω)` is the weak derivative of `u` in the direction `v`,
then the difference quotients `t⁻¹ (u(· + t v) - u)` converge to `d` in `W^{1,p}(Ω)` as `t → 0`. -/
theorem W1p.tendsto_differenceQuotient (hp : p ≠ ∞) {v : E}
    (hΩ : ∀ t : ℝ, MapsTo (· + t • v) Omega Omega) {u d : W1p mu Omega p}
    (hd : HasWeakLineDerivOn mu Omega (W1p.value u) (W1p.value d) v)
    (hD : ∀ y : E, ∃ D : W1p mu Omega p,
      HasWeakLineDerivOn mu Omega (W1p.value u) (W1p.value D) y) :
    Tendsto (fun t => W1p.differenceQuotient le_rfl v t (hΩ t) u) (𝓝[≠] 0) (𝓝 d) := by
  -- `∂_y w = ⟪∇w, y⟫` for every `w ∈ W^{1,p}(Ω)`.
  have hfd : ∀ (w : W1p mu Omega p) (y : E),
      HasWeakLineDerivOn mu Omega (W1p.value w) (fun x => ⟪W1p.gradient w x, y⟫_ℝ) y :=
    fun w y => by
      simpa only [innerSL_apply_apply] using (W1p.hasWeakFDerivOn w).hasWeakLineDerivOn y
  rw [W1p.tendsto_iff_value_gradient, Lp.tendsto_Lp_iff_tendsto_eLpNorm',
    Lp.tendsto_Lp_iff_tendsto_eLpNorm']
  constructor
  · -- The values: `d = ⟪∇u, v⟫`.
    refine (W1p.tendsto_eLpNorm_inv_mul_value_comp_add_smul_sub_sub_inner hp u hΩ).congr
      fun t => eLpNorm_congr_ae ?_
    filter_upwards [W1p.value_differenceQuotient_ae le_rfl v t (hΩ t) u, hd.ae_eq (hfd u v)]
      with x h1 h2
    rw [Pi.sub_apply, h1, h2, real_inner_comm]
  · -- The gradients, coordinate by coordinate in an orthonormal basis `b`: the `i`-th coordinate
    -- of the error is the error for the difference quotients of `∂_{b i} u`.
    set b := stdOrthonormalBasis ℝ E
    choose D hD using fun i => hD (b i)
    have hcoord : ∀ i, Tendsto (fun t : ℝ => eLpNorm (fun x => b.toBasis.coord i ((⇑(W1p.gradient
        (W1p.differenceQuotient le_rfl v t (hΩ t) u)) - ⇑(W1p.gradient d)) x)) p
          (mu.restrict Omega)) (𝓝[≠] 0) (𝓝 0) := fun i => by
      refine (W1p.tendsto_eLpNorm_inv_mul_value_comp_add_smul_sub_sub_inner hp (D i) hΩ).congr
        fun t => eLpNorm_congr_ae ?_
      have hDi := (hD i).ae_eq (hfd u (b i))
      -- The identification `D i = ⟪∇u, b i⟫` also holds at the translated points.
      have hDit : ∀ᵐ x ∂mu.restrict Omega, W1p.value (D i) (x + t • v) =
          ⟪W1p.gradient u (x + t • v), b i⟫_ℝ := by
        have h := (ae_restrict_iff' Omega.isOpen.measurableSet).1 hDi
        rw [ae_restrict_iff' Omega.isOpen.measurableSet]
        filter_upwards [ae_add_right h (t • v)] with x hx hxΩ
        exact hx (hΩ t hxΩ)
      -- `⟪∇d, b i⟫ = ∂_v ∂_{b i} u = ⟪∇(D i), v⟫` by the symmetry of second derivatives.
      have hcomm := (W1p.hasWeakLineDerivOn_inner_gradient_comm ((hfd d (b i)).congr_ae
        (hd.ae_eq (hfd u v)))).ae_eq ((hfd (D i) v).congr_ae hDi)
      filter_upwards [W1p.gradient_differenceQuotient_ae le_rfl v t (hΩ t) u, hDi,
        hDit, hcomm] with x h1 h2 h3 h4
      -- Write every inner product as `⟪b i, ·⟫` or `⟪v, ·⟫`.
      simp only [Module.Basis.coord_apply, OrthonormalBasis.coe_toBasis_repr_apply,
        OrthonormalBasis.repr_apply_apply, Pi.sub_apply, h1, h2, h3, inner_sub_right,
        inner_smul_right, real_inner_comm (b i), real_inner_comm v] at h4 ⊢
      rw [h4]
    have hsum := tendsto_finsetSum Finset.univ fun i (_ : i ∈ Finset.univ) =>
      (ENNReal.Tendsto.const_mul (hcoord i) (Or.inr (eNorm_ne_top (x := b.toBasis i))))
    simp only [mul_zero, Finset.sum_const_zero] at hsum
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum (fun _ => zero_le)
      fun t => b.toBasis.eLpNorm_le_sum_enorm_mul_eLpNorm_coord
        ((Lp.aestronglyMeasurable _).sub (Lp.aestronglyMeasurable _))

/-- **Tangential derivatives keep zero boundary values.** Let `Ω` be mapped into itself by every
translation `x ↦ x + t v`, as a half-space is for `v` parallel to its boundary, and let
`1 ≤ p < ∞`. If `u ∈ W^{1,p}_0(Ω)` has every first derivative in `W^{1,p}(Ω)`, then its derivative
`d ∈ W^{1,p}(Ω)` in the direction `v` lies in `W^{1,p}_0(Ω)`. -/
theorem W1p.mem_w1p0Submodule_of_hasWeakLineDerivOn (hp : p ≠ ∞) {v : E}
    (hΩ : ∀ t : ℝ, MapsTo (· + t • v) Omega Omega) {u d : W1p mu Omega p}
    (hu : u ∈ w1p0Submodule mu Omega p)
    (hd : HasWeakLineDerivOn mu Omega (W1p.value u) (W1p.value d) v)
    (hD : ∀ y : E, ∃ D : W1p mu Omega p,
      HasWeakLineDerivOn mu Omega (W1p.value u) (W1p.value D) y) :
    d ∈ w1p0Submodule mu Omega p :=
  -- The difference quotients of `u` lie in `W^{1,p}_0(Ω)` and converge to `d` in `W^{1,p}(Ω)`.
  (w1p0Submodule mu Omega p).isClosed.mem_of_tendsto (W1p.tendsto_differenceQuotient hp hΩ hd hD)
    (Eventually.of_forall fun t => W1p.differenceQuotient_mem_w1p0Submodule (hΩ t)
      (fun x hx => by simpa using hΩ (-t) hx) hu)

end TauCeti
