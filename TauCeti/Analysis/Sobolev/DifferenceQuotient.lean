/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.TestFunctionLp
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Topology.Algebra.Group.Order
import Mathlib.Topology.MetricSpace.Thickening

/-!
# Bounded difference quotients give weak derivatives

For a locally integrable `u : E → ℝ` on an open set `Ω`, a direction `v` and a real `t ≠ 0`, the
difference quotient of `u` is

`t⁻¹ * (u (x + t • v) - u x)`.

This file proves the `L²` form of the difference-quotient criterion for weak differentiability:
if the difference quotients of `u` in the direction `v` are bounded by `C` in `L²(K)` for
arbitrarily small `t`, on every compact `K ⊆ Ω`, then `u` has a weak derivative in the
direction `v` which lies in `L²(Ω)` with norm at most `C`.  This is the step of the
difference-quotient method that turns the uniform `L²` bounds on difference quotients of a weak
solution into membership of its derivatives in `L²`, as in the proof of interior `H²` regularity
for elliptic equations.

The criterion combines two results of independent use.

* The difference quotients of `u` converge to its distributional derivative: paired with a test
  function `φ`, they tend to `-∫ ∂_v φ * u` as `t → 0`.
* A distributional derivative that is bounded against the `L²` norm of test functions is an
  `L²` function: the pairing `φ ↦ ∫ ∂_v φ * u` then extends to a bounded functional on `L²(Ω)`,
  and its Riesz representative is the weak derivative.

The criterion is stated for the exponent `2`, where every bounded functional on `L²(Ω)` is
represented by an element of `L²(Ω)`.

## Main declarations

* `TauCeti.exists_norm_le_hasWeakLineDerivOn_of_abs_integral_lineDeriv_mul_le`: if
  `|∫ ∂_v φ * u| ≤ C ‖φ‖₂` for every test function `φ`, then `u` has a weak derivative in the
  direction `v` in `L²(Ω)` of norm at most `C`.
* `TauCeti.integral_inv_mul_sub_mul_tendsto_neg_integral_lineDeriv_mul`: the difference
  quotients of a locally integrable function converge to its distributional derivative when
  paired with a test function.
* `TauCeti.exists_norm_le_hasWeakLineDerivOn_of_frequently_eLpNorm_inv_mul_sub_le`: the
  difference-quotient criterion.

## References

* L. C. Evans, *Partial Differential Equations*, §5.8.2, Theorem 3.
* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Lemma 7.24.
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory Metric Set TopologicalSpace Filter Topology
open scoped Distributions ENNReal InnerProductSpace

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [BorelSpace E] [FiniteDimensional ℝ E] {μ : Measure E} [μ.IsAddHaarMeasure] {Ω : Opens E}

/-- **An `L²`-bounded distributional derivative is an `L²` weak derivative.** Let `u` be locally
integrable on `Ω`. If for some `C ≥ 0` every test function `φ` on `Ω` satisfies

`|∫ ∂_v φ * u| ≤ C ‖φ‖₂`,

then `u` has a weak derivative in the direction `v` on `Ω` that lies in `L²(Ω)` and has norm at
most `C`. -/
theorem exists_norm_le_hasWeakLineDerivOn_of_abs_integral_lineDeriv_mul_le {u : E → ℝ}
    (hu : LocallyIntegrableOn u Ω μ) (v : E) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ φ : 𝓓(Ω, ℝ),
      |∫ x, lineDeriv ℝ (φ : E → ℝ) x v * u x ∂μ| ≤ C * (eLpNorm (φ : E → ℝ) 2 μ).toReal) :
    ∃ g : Lp ℝ 2 (μ.restrict Ω), ‖g‖ ≤ C ∧ HasWeakLineDerivOn μ Ω u g v := by
  -- The test functions, as a subspace of `L²(Ω)`.
  let T : 𝓓(Ω, ℝ) →ₗ[ℝ] Lp ℝ 2 (μ.restrict Ω) :=
    { toFun := testFunctionLp 2
      map_add' := testFunctionLp_add 2
      map_smul' := testFunctionLp_smul 2 }
  have hT : Function.Injective T := testFunctionLp_injective 2
  -- The pairing `φ ↦ ∫ ∂_v φ * u`, which the hypothesis bounds by the `L²` norm of `φ`.
  let ℓ : 𝓓(Ω, ℝ) →L[ℝ] ℝ :=
    (TestFunction.integralAgainstBilinCLM (n := ⊤) (ContinuousLinearMap.mul ℝ ℝ) μ u).comp
      (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ v)
  have hℓ : ∀ φ, ℓ φ = ∫ x, lineDeriv ℝ (φ : E → ℝ) x v * u x ∂μ := fun φ => by
    simp [ℓ, TestFunction.integralAgainstBilinCLM_eq_integral hu]
  let e := LinearEquiv.ofInjective T hT
  let f₀ : LinearMap.range T →ₗ[ℝ] ℝ := ℓ.toLinearMap ∘ₗ e.symm.toLinearMap
  have hf₀ : ∀ s, ‖f₀ s‖ ≤ C * ‖s‖ := by
    intro s
    obtain ⟨φ, rfl⟩ := e.surjective s
    have hnorm : ‖e φ‖ = (eLpNorm (φ : E → ℝ) 2 μ).toReal := by
      rw [← Submodule.norm_coe, LinearEquiv.ofInjective_apply, ← toReal_enorm]
      exact congrArg ENNReal.toReal (enorm_testFunctionLp_eq_eLpNorm 2 φ)
    simpa [f₀, hℓ, hnorm] using hbound φ
  obtain ⟨g', hg'f, hg'norm⟩ := exists_extension_norm_eq _ (f₀.mkContinuous C hf₀)
  refine ⟨(InnerProductSpace.toDual ℝ _).symm (-g'), ?_, ?_⟩
  · rw [LinearIsometryEquiv.norm_map, norm_neg, hg'norm]
    exact LinearMap.mkContinuous_norm_le _ hC hf₀
  · set g := (InnerProductSpace.toDual ℝ (Lp ℝ 2 (μ.restrict Ω))).symm (-g')
    have hg : LocallyIntegrableOn g Ω μ :=
      locallyIntegrableOn_of_locallyIntegrable_restrict
        ((Lp.memLp g).locallyIntegrable (by norm_num))
    refine hasWeakLineDerivOn_iff_testFunction.2 ⟨inferInstance, hu, hg, fun φ => ?_⟩
    have hg'φ : g' (T φ) = ℓ φ := by
      simpa [f₀, e, LinearEquiv.ofInjective_apply] using hg'f (e φ)
    have hinner : ⟪g, T φ⟫_ℝ = ∫ x, (φ : E → ℝ) x • g x ∂μ := by
      rw [L2.inner_def, ← setIntegral_smul_eq_integral_smul φ]
      refine integral_congr_ae ?_
      filter_upwards [testFunctionLp_apply_ae (mu := μ) 2 φ] with x hx
      simp [T, hx]
    rw [← hinner, InnerProductSpace.toDual_symm_apply, neg_apply, hg'φ, hℓ, neg_neg]
    simp only [smul_eq_mul]

omit [μ.IsAddHaarMeasure] in
/-- A locally integrable function on `Ω` agrees, on the support of a test function and on all its
small translates, with a globally integrable function: its truncation to a compact neighbourhood
of the support inside `Ω`. -/
private theorem exists_integrable_eqOn_tsupport_add {u : E → ℝ}
    (hu : LocallyIntegrableOn u Ω μ) (φ : 𝓓(Ω, ℝ)) (v : E) :
    ∃ w : E → ℝ, Integrable w μ ∧ EqOn w u (tsupport (φ : E → ℝ)) ∧
      ∀ᶠ t in 𝓝[≠] (0 : ℝ), ∀ x ∈ tsupport (φ : E → ℝ), w (x + t • v) = u (x + t • v) := by
  obtain ⟨δ, hδ, hδΩ⟩ :=
    φ.hasCompactSupport.isCompact.exists_cthickening_subset_open Ω.isOpen φ.tsupport_subset
  have hK : IsCompact (cthickening δ (tsupport (φ : E → ℝ))) :=
    φ.hasCompactSupport.isCompact.cthickening
  refine ⟨(cthickening δ (tsupport (φ : E → ℝ))).indicator u,
    (integrable_indicator_iff hK.measurableSet).2 (hu.integrableOn_compact_subset hδΩ hK),
    fun x hx => indicator_of_mem (self_subset_cthickening _ hx) u, ?_⟩
  have htend : Tendsto (fun t : ℝ => t • v) (𝓝 0) (𝓝 0) := by
    simpa using (tendsto_id (x := 𝓝 (0 : ℝ))).smul_const v
  filter_upwards [nhdsWithin_le_nhds (htend.eventually (closedBall_mem_nhds 0 hδ))] with t ht x hx
  refine indicator_of_mem (mem_cthickening_of_dist_le _ x δ _ hx ?_) u
  simpa [dist_eq_norm] using ht

/-- **Difference quotients converge to the distributional derivative.** If `u` is locally
integrable on `Ω` and `φ` is a test function on `Ω`, then as `t → 0` with `t ≠ 0`,

`∫ t⁻¹ * (u (x + t • v) - u x) * φ x → -∫ ∂_v φ * u`.

No differentiability of `u` is assumed: when `u` has a weak derivative `u'` in the direction `v`,
the limit is `∫ φ * u'`. -/
theorem integral_inv_mul_sub_mul_tendsto_neg_integral_lineDeriv_mul {u : E → ℝ}
    (hu : LocallyIntegrableOn u Ω μ) (φ : 𝓓(Ω, ℝ)) (v : E) :
    Tendsto (fun t : ℝ => ∫ x, t⁻¹ * (u (x + t • v) - u x) * φ x ∂μ) (𝓝[≠] 0)
      (𝓝 (-∫ x, lineDeriv ℝ (φ : E → ℝ) x v * u x ∂μ)) := by
  obtain ⟨w, hw, hwS, hwt⟩ := exists_integrable_eqOn_tsupport_add hu φ v
  have hφw : ∀ x, lineDeriv ℝ (φ : E → ℝ) x v * u x = lineDeriv ℝ (φ : E → ℝ) x v * w x := by
    intro x
    by_cases hx : x ∈ tsupport (φ : E → ℝ)
    · rw [hwS hx]
    · simp [lineDeriv_eq_zero_of_notMem_tsupport φ hx]
  obtain ⟨L, hL⟩ := φ.contDiff.lipschitzWith_of_hasCompactSupport φ.hasCompactSupport (by simp)
  -- For small `t`, the translation moves onto the test function.
  have hEq : ∀ᶠ t in 𝓝[≠] (0 : ℝ), ∫ y, (t⁻¹ • (φ (y + t • -v) - φ y)) * w y ∂μ =
      ∫ x, t⁻¹ * (u (x + t • v) - u x) * φ x ∂μ := by
    filter_upwards [hwt] with t ht
    have hpt : ∀ x, t⁻¹ * (u (x + t • v) - u x) * φ x = t⁻¹ * (w (x + t • v) - w x) * φ x := by
      intro x
      by_cases hx : x ∈ tsupport (φ : E → ℝ)
      · rw [ht x hx, hwS hx]
      · simp [image_eq_zero_of_notMem_tsupport hx]
    obtain ⟨M, hM⟩ := φ.continuous.bounded_above_of_compact_support φ.hasCompactSupport
    have h1 : Integrable (fun x => w (x + t • v) * φ x) μ :=
      (hw.comp_add_right (t • v)).mul_bdd φ.aestronglyMeasurable (ae_of_all _ hM)
    have h2 : Integrable (fun x => w x * φ x) μ :=
      hw.mul_bdd φ.aestronglyMeasurable (ae_of_all _ hM)
    have h3 : Integrable (fun x => w x * φ (x + t • -v)) μ :=
      hw.mul_bdd (φ.continuous.comp (continuous_id.add continuous_const)).aestronglyMeasurable
        (ae_of_all _ fun x => hM _)
    simp_rw [hpt]
    calc ∫ y, (t⁻¹ • (φ (y + t • -v) - φ y)) * w y ∂μ
        = t⁻¹ * (∫ y, w y * φ (y + t • -v) ∂μ - ∫ y, w y * φ y ∂μ) := by
          rw [← integral_sub h3 h2, ← integral_const_mul]
          congr 1 with y
          simp only [smul_eq_mul]
          ring
      _ = t⁻¹ * (∫ x, w (x + t • v) * φ x ∂μ - ∫ y, w y * φ y ∂μ) := by
          rw [← integral_add_right_eq_self (fun y => w y * φ (y + t • -v)) (t • v)]
          simp
      _ = ∫ x, t⁻¹ * (w (x + t • v) - w x) * φ x ∂μ := by
          rw [← integral_sub h1 h2, ← integral_const_mul]
          congr 1 with x
          ring
  refine Tendsto.congr' hEq ?_
  -- The one-sided limits are Mathlib's dominated convergence for a Lipschitz function.
  rw [← nhdsLT_sup_nhdsGT]
  refine Tendsto.sup ?_ ?_
  · have hleft := ((hL.integral_inv_smul_sub_mul_tendsto_integral_lineDeriv_mul (μ := μ) hw v).comp
      (by simpa using tendsto_neg_nhdsLT (a := (0 : ℝ)))).neg
    convert hleft using 1
    · ext t
      simp [smul_neg, integral_neg]
    · simp_rw [hφw]
  · convert hL.integral_inv_smul_sub_mul_tendsto_integral_lineDeriv_mul (μ := μ) hw (-v) using 2
    simp_rw [hφw, lineDeriv_neg, neg_mul, integral_neg]

/-- **The difference-quotient criterion for weak differentiability.** Let `u` be locally integrable
on `Ω` and `C ≥ 0`. Suppose that on every compact `K ⊆ Ω` the difference quotients of `u` in the
direction `v` satisfy

`‖t⁻¹ * (u (· + t • v) - u)‖_{L²(K)} ≤ C`

for arbitrarily small `t ≠ 0`. Then `u` has a weak derivative in the direction `v` on `Ω` that
lies in `L²(Ω)` and has norm at most `C`.

The hypothesis only asks for the bound frequently as `t → 0`; the usual hypothesis that it holds
for all sufficiently small `t ≠ 0` implies it by `Filter.Eventually.frequently`. -/
theorem exists_norm_le_hasWeakLineDerivOn_of_frequently_eLpNorm_inv_mul_sub_le {u : E → ℝ}
    (hu : LocallyIntegrableOn u Ω μ) (v : E) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ K ⊆ (Ω : Set E), IsCompact K → ∃ᶠ t in 𝓝[≠] (0 : ℝ),
      eLpNorm (fun x => t⁻¹ * (u (x + t • v) - u x)) 2 (μ.restrict K) ≤ ENNReal.ofReal C) :
    ∃ g : Lp ℝ 2 (μ.restrict Ω), ‖g‖ ≤ C ∧ HasWeakLineDerivOn μ Ω u g v := by
  refine exists_norm_le_hasWeakLineDerivOn_of_abs_integral_lineDeriv_mul_le hu v hC fun φ => ?_
  set S := tsupport (φ : E → ℝ)
  have hS : IsCompact S := φ.hasCompactSupport
  obtain ⟨w, hw, hwS, hwt⟩ := exists_integrable_eqOn_tsupport_add hu φ v
  have hlim := (integral_inv_mul_sub_mul_tendsto_neg_integral_lineDeriv_mul hu φ v).abs
  rw [abs_neg] at hlim
  refine le_of_tendsto_of_frequently hlim
    (((hbound S φ.tsupport_subset hS).and_eventually hwt).mono fun t ⟨ht, htw⟩ => ?_)
  -- On `S`, the difference quotient of `u` is that of the integrable function `w`.
  set D := fun x => t⁻¹ * (w (x + t • v) - w x)
  have hD : ∀ x ∈ S, t⁻¹ * (u (x + t • v) - u x) = D x := by
    intro x hx
    simp only [D, htw x hx, hwS hx]
  have hDmeas : AEStronglyMeasurable D μ :=
    aestronglyMeasurable_const.mul
      ((hw.comp_add_right (t • v)).aestronglyMeasurable.sub hw.aestronglyMeasurable)
  have hDbound : eLpNorm D 2 (μ.restrict S) ≤ ENNReal.ofReal C := by
    rw [← eLpNorm_congr_ae (ae_restrict_of_forall_mem hS.measurableSet hD)]
    exact ht
  have hint : ∫ x, t⁻¹ * (u (x + t • v) - u x) * φ x ∂μ = ∫ x in S, D x * φ x ∂μ := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
      simp [image_eq_zero_of_notMem_tsupport hx]]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    by_cases hx : x ∈ S
    · simp only [hD x hx]
    · simp [image_eq_zero_of_notMem_tsupport hx]
  have hHolder : ‖∫ x in S, D x * φ x ∂μ‖ₑ ≤ ENNReal.ofReal C * eLpNorm (φ : E → ℝ) 2 μ := by
    let _ : ENNReal.HolderTriple 2 2 1 := ⟨by simp [ENNReal.inv_two_add_inv_two]⟩
    calc ‖∫ x in S, D x * φ x ∂μ‖ₑ ≤ eLpNorm (fun x => D x * φ x) 1 (μ.restrict S) :=
          (enorm_integral_le_lintegral_enorm _).trans_eq eLpNorm_one_eq_lintegral_enorm.symm
      _ ≤ eLpNorm D 2 (μ.restrict S) * eLpNorm (φ : E → ℝ) 2 (μ.restrict S) := by
          simpa using eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm (p := 2) (q := 2) (r := 1)
            hDmeas.restrict φ.aestronglyMeasurable (· * ·) 1
            (Eventually.of_forall fun _ => by simp [nnnorm_mul])
      _ ≤ ENNReal.ofReal C * eLpNorm (φ : E → ℝ) 2 μ :=
          mul_le_mul' hDbound (eLpNorm_restrict_le _ _ _ _)
  rw [hint, ← Real.norm_eq_abs, ← toReal_enorm, ← ENNReal.toReal_ofReal hC, ← ENNReal.toReal_mul]
  exact ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (φ.continuous.memLp_of_hasCompactSupport φ.hasCompactSupport).eLpNorm_ne_top) hHolder

end TauCeti
