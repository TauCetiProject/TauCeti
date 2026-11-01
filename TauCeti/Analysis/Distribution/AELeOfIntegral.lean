/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.TestFunction
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import TauCeti.MeasureTheory.Integral.Bochner.Regular

/-!
# Pointwise bounds on a density from its pairings with test vector fields

Let `Ω` be an open set of a finite-dimensional real normed space `E`, let `ρ` be a measure on
`Ω` and let `h : Ω → F` be locally integrable, with values in a separable real inner product
space `F`. If every pairing of `h` with a test vector field `φ ∈ 𝓓(Ω, F)` of norm at most one
supported in an open set `U` is bounded by the integral of a fixed weight `k` over `U`,

`|∫ ⟪φ x, h x⟫ ∂ρ| ≤ ∫⁻ x in U, k x ∂ρ`,

then `‖h x‖ ≤ k x` for `ρ`-almost every `x`
(`TauCeti.ae_enorm_le_of_forall_enorm_integral_inner_le`). For `k = 0` this is the fundamental
lemma of the calculus of variations on `Ω`. With `k` the density of a second measure `ν` with
respect to `ρ`, it says that a functional bounded on test vector fields by `ν` is represented
against `ρ` by a density pointwise dominated by that of `ν`. This is how a measure-valued
derivative is shown to be absolutely continuous with respect to its variation, with a density of
norm at most one.

The proof first tests against smooth cutoffs equal to one on a compact set `K` and supported in
shrinking neighbourhoods of `K`, which gives `|∫_K h| ≤ ∫⁻_K k`. Inner regularity
(`TauCeti.enorm_setIntegral_le_of_forall_isClosed_subset`) extends this to measurable subsets of a
compact set, and the scalar case follows by comparing set integrals. The
vector case tests the scalar components `⟪h, w⟫` for `w` in a countable dense subset of `F`.

## Main declarations

* `TauCeti.ae_enorm_le_of_forall_enorm_integral_inner_le`: the pointwise bound `‖h‖ ≤ k`.

## References

* L. C. Evans, R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, revised edition,
  §1.8 (the representation of functionals bounded on compactly supported vector fields).
-/

public section

noncomputable section

open MeasureTheory TopologicalSpace Filter Metric Set
open scoped ENNReal NNReal Distributions Topology RealInnerProductSpace

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {Ω : Opens E} {ρ : Measure Ω} {k : Ω → ℝ≥0∞} {h : Ω → ℝ}

/-- The bound on pairings with nonnegative test functions bounds the integral of `h` over every
compact set. -/
private theorem enorm_setIntegral_isCompact_le (hh : LocallyIntegrable h ρ)
    (hk : ∀ K, IsCompact K → ∫⁻ x in K, k x ∂ρ ≠ ∞)
    (H : ∀ ψ : 𝓓(Ω, ℝ), (∀ x, 0 ≤ ψ x) → (∀ x, ψ x ≤ 1) → ∀ W : Set Ω, IsOpen W →
      tsupport ψ ⊆ (↑) '' W → ‖∫ x, ψ x * h x ∂ρ‖ₑ ≤ ∫⁻ x in W, k x ∂ρ)
    {K : Set Ω} (hK : IsCompact K) : ‖∫ x in K, h x ∂ρ‖ₑ ≤ ∫⁻ x in K, k x ∂ρ := by
  have := Ω.isOpen.locallyCompactSpace
  obtain ⟨L, hL, hKL⟩ := exists_compact_superset hK
  -- Shrinking open neighbourhoods of `K` inside the compact set `L`.
  set W : ℕ → Set Ω := fun n => interior L ∩ thickening (1 / ((n : ℝ) + 1)) K
  have hWo (n : ℕ) : IsOpen (W n) := isOpen_interior.inter isOpen_thickening
  have hKW (n : ℕ) : K ⊆ W n := subset_inter hKL (self_subset_thickening (by positivity) K)
  have hWanti : Antitone W := fun m n hmn =>
    inter_subset_inter_right _ (thickening_mono (one_div_le_one_div_of_le (by positivity)
      (by exact_mod_cast Nat.add_le_add_right hmn 1)) K)
  have hWK : ⋂ n, W n = K := by
    refine Subset.antisymm (fun x hx => ?_) (subset_iInter hKW)
    rw [← hK.isClosed.closure_eq, Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
    obtain ⟨y, hy, hxy⟩ := mem_thickening_iff.1 (mem_iInter.1 hx n).2
    exact ⟨y, hy, hxy.trans hn⟩
  -- Smooth cutoffs with values in `[0, 1]`, equal to one on `K` and supported in `W n`.
  have hcut (n : ℕ) : ∃ ψ : 𝓓(Ω, ℝ), (∀ x, 0 ≤ ψ x) ∧ (∀ x, ψ x ≤ 1) ∧ (∀ x ∈ K, ψ x = 1) ∧
      tsupport ψ ⊆ (↑) '' W n := by
    obtain ⟨ψ, hψ, hrange, hone, hcpt, hsupp⟩ :=
      (hK.image continuous_subtype_val).exists_contDiff_cutoff
        (Ω.isOpen.isOpenMap_subtype_val _ (hWo n)) (image_mono (hKW n))
    exact ⟨⟨ψ, hψ, hcpt, hsupp.trans (Subtype.coe_image_subset _ _)⟩,
      fun x => (hrange ⟨x, rfl⟩).1, fun x => (hrange ⟨x, rfl⟩).2,
      fun x hx => interior_subset (hone ⟨x, hx, rfl⟩), hsupp⟩
  choose ψ hψ0 hψ1 hψK hψW using hcut
  have hψ_zero (n : ℕ) (x : Ω) (hx : x ∉ W n) : ψ n x = 0 :=
    image_eq_zero_of_notMem_tsupport fun hx' => hx <| by
      obtain ⟨y, hy, hyx⟩ := hψW n hx'
      rwa [← Subtype.val_injective hyx]
  -- The pairings with `ψ n` converge to the integral over `K`, by dominated convergence.
  have hlim : Tendsto (fun n => ∫ x, ψ n x * h x ∂ρ) atTop (𝓝 (∫ x in K, h x ∂ρ)) := by
    rw [← integral_indicator hK.measurableSet]
    refine tendsto_integral_of_dominated_convergence (L.indicator fun x => ‖h x‖)
      (fun n => ((ψ n).continuous.comp continuous_subtype_val).aestronglyMeasurable.mul
        hh.aestronglyMeasurable)
      ((integrable_indicator_iff hL.measurableSet).2 (hh.integrableOn_isCompact hL).norm)
      (fun n => ae_of_all _ fun x => ?_) (ae_of_all _ fun x => ?_)
    · by_cases hx : x ∈ W n
      · rw [indicator_of_mem (interior_subset hx.1), norm_mul]
        exact mul_le_of_le_one_left (norm_nonneg _)
          (by simpa [abs_of_nonneg (hψ0 n x)] using hψ1 n x)
      · simpa [hψ_zero n x hx] using indicator_nonneg (fun y _ => norm_nonneg (h y)) x
    · by_cases hx : x ∈ K
      · simp [hψK _ x hx, indicator_of_mem hx]
      · obtain ⟨n, hn⟩ : ∃ n, x ∉ W n := by simpa [← hWK] using hx
        rw [indicator_of_notMem hx]
        exact tendsto_const_nhds.congr' <| eventually_atTop.2
          ⟨n, fun m hm => by simp [hψ_zero m x fun h => hn (hWanti hm h)]⟩
  -- The weights of the neighbourhoods converge to the weight of `K`, by continuity from above.
  have hlimk : Tendsto (fun n => ∫⁻ x in W n, k x ∂ρ) atTop (𝓝 (∫⁻ x in K, k x ∂ρ)) := by
    have h := tendsto_measure_iInter_atTop (μ := ρ.withDensity k)
      (fun n => (hWo n).measurableSet.nullMeasurableSet) hWanti
      ⟨0, by
        rw [withDensity_apply _ (hWo 0).measurableSet]
        exact ne_top_of_le_ne_top (hk L hL)
          (lintegral_mono_set (interior_subset.trans' inter_subset_left))⟩
    rw [hWK, withDensity_apply _ hK.measurableSet] at h
    refine h.congr fun n => ?_
    simp [withDensity_apply _ (hWo n).measurableSet]
  exact le_of_tendsto_of_tendsto' ((continuous_enorm.tendsto _).comp hlim) hlimk
    fun n => H _ (hψ0 n) (hψ1 n) _ (hWo n) (hψW n)

/-- The scalar case: a bound on pairings with nonnegative test functions bounds `|h|`. -/
private theorem ae_enorm_le_of_forall_nonneg (hh : LocallyIntegrable h ρ) (hkm : Measurable k)
    (hk : ∀ K, IsCompact K → ∫⁻ x in K, k x ∂ρ ≠ ∞)
    (H : ∀ ψ : 𝓓(Ω, ℝ), (∀ x, 0 ≤ ψ x) → (∀ x, ψ x ≤ 1) → ∀ W : Set Ω, IsOpen W →
      tsupport ψ ⊆ (↑) '' W → ‖∫ x, ψ x * h x ∂ρ‖ₑ ≤ ∫⁻ x in W, k x ∂ρ) :
    ∀ᵐ x ∂ρ, ‖h x‖ₑ ≤ k x := by
  have := Ω.isOpen.locallyCompactSpace
  have hB {L B : Set Ω} (hL : IsCompact L) (hBm : MeasurableSet B) (hBL : B ⊆ L) :=
    enorm_setIntegral_le_of_forall_isClosed_subset ((hh.integrableOn_isCompact hL).mono_set hBL)
      hBm fun F hFB hFc =>
        enorm_setIntegral_isCompact_le hh hk H (hL.of_isClosed_subset hFc (hFB.trans hBL))
  -- It suffices to prove the bound on each compact set of an exhaustion of `Ω`.
  rw [← Measure.restrict_univ (μ := ρ), ← iUnion_compactCovering, ae_restrict_iUnion_iff]
  intro n
  set L := compactCovering Ω n
  have hL : IsCompact L := isCompact_compactCovering Ω n
  have hint : Integrable h (ρ.restrict L) := hh.integrableOn_isCompact hL
  have hkint : Integrable (fun x => (k x).toReal) (ρ.restrict L) :=
    integrable_toReal_of_lintegral_ne_top hkm.aemeasurable (hk L hL)
  -- On every measurable set, `|∫ h| ≤ ∫ k`, so `k - h` and `k + h` are nonnegative.
  have hset (B : Set Ω) (hBm : MeasurableSet B) :
      |∫ x in B, h x ∂ρ.restrict L| ≤ ∫ x in B, (k x).toReal ∂ρ.restrict L := by
    rw [Measure.restrict_restrict hBm]
    have hfin : ∫⁻ x in B ∩ L, k x ∂ρ ≠ ∞ :=
      ne_top_of_le_ne_top (hk L hL) (lintegral_mono_set inter_subset_right)
    rw [integral_toReal hkm.aemeasurable (ae_lt_top' hkm.aemeasurable hfin),
      ← ENNReal.ofReal_le_iff_le_toReal hfin, ← Real.enorm_eq_ofReal_abs]
    exact hB hL (hBm.inter hL.measurableSet) inter_subset_right
  have h₁ := ae_nonneg_of_forall_setIntegral_nonneg (hkint.sub hint) fun B hBm _ => by
    simp only [Pi.sub_apply]
    rw [integral_sub hkint.integrableOn hint.integrableOn, sub_nonneg]
    exact (le_abs_self _).trans (hset B hBm)
  have h₂ := ae_nonneg_of_forall_setIntegral_nonneg (hkint.add hint) fun B hBm _ => by
    simp only [Pi.add_apply]
    rw [integral_add hkint.integrableOn hint.integrableOn, ← neg_le_iff_add_nonneg']
    exact neg_le.1 ((neg_le_abs _).trans (hset B hBm))
  filter_upwards [h₁, h₂] with x h₁ h₂
  rw [Real.enorm_eq_ofReal_abs]
  refine (ENNReal.ofReal_le_ofReal (abs_le.2 ⟨?_, ?_⟩)).trans ENNReal.ofReal_toReal_le
  · simp only [Pi.add_apply, Pi.zero_apply] at h₂
    linarith
  · simp only [Pi.sub_apply, Pi.zero_apply] at h₁
    linarith

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [SeparableSpace F]

/-- **A density bounded on test vector fields is pointwise bounded.** Let `h : Ω → F` be locally
integrable for a measure `ρ` on `Ω`, and let `k` be a measurable weight with finite integral over
every compact subset of `Ω`. If for every open `U ⊆ Ω` and every test vector field `φ` supported
in `U` with `‖φ x‖ ≤ 1` we have `|∫ ⟪φ x, h x⟫ ∂ρ| ≤ ∫⁻ x in U, k x ∂ρ`, then `‖h x‖ ≤ k x` for
`ρ`-almost every `x`. -/
theorem ae_enorm_le_of_forall_enorm_integral_inner_le {h : Ω → F} (hh : LocallyIntegrable h ρ)
    (hkm : Measurable k) (hk : ∀ K, IsCompact K → ∫⁻ x in K, k x ∂ρ ≠ ∞)
    (H : ∀ U : Opens E, U ≤ Ω → ∀ φ : 𝓓(Ω, F), tsupport φ ⊆ U → (∀ x, ‖φ x‖ ≤ 1) →
      ‖∫ x, ⟪φ x, h x⟫ ∂ρ‖ₑ ≤ ∫⁻ x in (↑) ⁻¹' (U : Set E), k x ∂ρ) :
    ∀ᵐ x ∂ρ, ‖h x‖ₑ ≤ k x := by
  have := Ω.isOpen.locallyCompactSpace
  -- Each component `⟪w, h⟫` is bounded by `‖w‖ k`.
  have hw (w : F) : ∀ᵐ x ∂ρ, ‖⟪w, h x⟫‖ₑ ≤ ‖w‖ₑ * k x := by
    refine ae_enorm_le_of_forall_nonneg
      (locallyIntegrable_iff.2 fun K hK => Integrable.const_inner w (hh.integrableOn_isCompact hK))
      (hkm.const_mul _) (fun K hK => by
        rw [lintegral_const_mul _ hkm]
        exact ENNReal.mul_ne_top enorm_ne_top (hk K hK))
      fun ψ hψ0 hψ1 W hW hψW => ?_
    rw [lintegral_const_mul _ hkm]
    rcases eq_or_ne w 0 with rfl | hw0
    · simp
    -- Test against the vector field `ψ ‖w‖⁻¹ w`.
    let φ : 𝓓(Ω, F) :=
      TestFunction.postcompCLM (ContinuousLinearMap.toSpanSingleton ℝ (‖w‖⁻¹ • w)) ψ
    have hφ (x : E) : φ x = ψ x • (‖w‖⁻¹ • w) := by simp [φ]
    have hint : ∫ x, ⟪φ x, h x⟫ ∂ρ = ‖w‖⁻¹ * ∫ x, ψ x * ⟪w, h x⟫ ∂ρ := by
      rw [← integral_const_mul]
      congr 1 with x
      simp only [hφ, inner_smul_left, RCLike.conj_to_real]
      ring
    have hφfun : (φ : E → F) = fun x => ψ x • (‖w‖⁻¹ • w) := funext hφ
    have hφs : tsupport φ ⊆ tsupport ψ := by
      rw [hφfun]
      exact tsupport_smul_subset_left _ _
    have hU := H ⟨(↑) '' W, Ω.isOpen.isOpenMap_subtype_val W hW⟩ (Subtype.coe_image_subset _ _)
      φ (hφs.trans hψW) fun x => by
        rw [hφ, norm_smul, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 hw0),
          mul_one, Real.norm_of_nonneg (hψ0 x)]
        exact hψ1 x
    rw [hint, enorm_mul, enorm_inv (by simpa using hw0), enorm_norm, Opens.coe_mk,
      preimage_image_eq W Subtype.val_injective] at hU
    calc ‖∫ x, ψ x * ⟪w, h x⟫ ∂ρ‖ₑ
        = ‖w‖ₑ * (‖w‖ₑ⁻¹ * ‖∫ x, ψ x * ⟪w, h x⟫ ∂ρ‖ₑ) := by
          rw [← mul_assoc, ENNReal.mul_inv_cancel (by simpa using hw0) enorm_ne_top, one_mul]
      _ ≤ ‖w‖ₑ * ∫⁻ x in W, k x ∂ρ := by gcongr
  -- Combine the bounds along a dense sequence of directions.
  filter_upwards [ae_all_iff.2 fun n => hw (denseSeq F n)] with x hx
  rcases eq_top_or_lt_top (k x) with hkx | hkx
  · simp [hkx]
  lift k x to ℝ≥0 using hkx.ne with q hq
  have hle (w : F) : ‖⟪w, h x⟫‖ ≤ ‖w‖ * q := by
    refine (denseRange_denseSeq F).induction_on w
      (isClosed_le (continuous_id.inner continuous_const).norm
        (continuous_norm.mul continuous_const))
      fun n => ?_
    have := hx n
    rw [enorm_eq_nnnorm, enorm_eq_nnnorm, ← ENNReal.coe_mul, ENNReal.coe_le_coe] at this
    exact_mod_cast this
  have hsq := hle (h x)
  rw [real_inner_self_eq_norm_sq, Real.norm_of_nonneg (sq_nonneg _), sq] at hsq
  rw [enorm_eq_nnnorm, ENNReal.coe_le_coe, ← NNReal.coe_le_coe, coe_nnnorm]
  rcases (norm_nonneg (h x)).eq_or_lt with h0 | h0
  · rw [← h0]
    exact q.2
  · exact le_of_mul_le_mul_left hsq h0

end TauCeti
