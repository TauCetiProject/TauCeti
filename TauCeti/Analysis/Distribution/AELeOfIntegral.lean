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
import TauCeti.Analysis.Distribution.TestFunction.PartitionOfUnity
import TauCeti.MeasureTheory.Integral.Bochner.Regular
import TauCeti.Topology.MetricSpace.Thickening

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
compact set, and the scalar case follows by comparing set integrals.

The vector case is proved more generally for a density `h : Ω → StrongDual ℝ F` with values in the
normed dual of a separable real normed space, paired with test vector fields by evaluation,
`x ↦ h x (φ x)`, and bounded in the dual norm: it tests the scalar components `x ↦ h x w` for `w`
in a countable dense subset of `F`. This is the form needed for currents, whose densities with
respect to their mass measures take values in the dual of the space of forms with its comass norm.
The inner product statement is its special case through `innerSL`.

The same scalar argument, with `k` the positive part of `h`, shows that a scalar density whose
pairings with nonnegative test functions are nonnegative is itself nonnegative almost everywhere
(`TauCeti.ae_nonneg_of_forall_integral_mul_nonneg`).

## Main declarations

* `TauCeti.ae_enorm_le_of_forall_enorm_integral_apply_le`: the pointwise bound `‖h‖ ≤ k` in the
  dual norm.
* `TauCeti.ae_enorm_le_of_forall_enorm_integral_inner_le`: the pointwise bound `‖h‖ ≤ k` for an
  inner product space.
* `TauCeti.ae_nonneg_of_forall_integral_mul_nonneg`: nonnegativity from nonnegative pairings.

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

/-- The pairings of `h` with cutoffs `ψ n` supported in shrinking neighbourhoods `W n ⊆ L` of a
compact set `K`, equal to one on `K`, converge to the integral of `h` over `K`, by dominated
convergence. -/
private theorem tendsto_integral_testFunction_mul {K L : Set Ω} {W : ℕ → Set Ω}
    {ψ : ℕ → 𝓓(Ω, ℝ)} (hh : LocallyIntegrable h ρ) (hK : IsCompact K) (hL : IsCompact L)
    (hWL : ∀ n, W n ⊆ L) (hWanti : Antitone W) (hWK : ⋂ n, W n = K)
    (hψ0 : ∀ n x, 0 ≤ ψ n x) (hψ1 : ∀ n x, ψ n x ≤ 1) (hψK : ∀ n, ∀ x ∈ K, ψ n x = 1)
    (hψ_zero : ∀ n (x : Ω), x ∉ W n → ψ n x = 0) :
    Tendsto (fun n => ∫ x, ψ n x * h x ∂ρ) atTop (𝓝 (∫ x in K, h x ∂ρ)) := by
  rw [← integral_indicator hK.measurableSet]
  refine tendsto_integral_of_dominated_convergence (L.indicator fun x => ‖h x‖)
    (fun n => ((ψ n).continuous.comp continuous_subtype_val).aestronglyMeasurable.mul
      hh.aestronglyMeasurable)
    ((integrable_indicator_iff hL.measurableSet).2 (hh.integrableOn_isCompact hL).norm)
    (fun n => ae_of_all _ fun x => ?_) (ae_of_all _ fun x => ?_)
  · by_cases hx : x ∈ W n
    · rw [indicator_of_mem (hWL n hx), norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _)
        (by simpa [abs_of_nonneg (hψ0 n x)] using hψ1 n x)
    · simpa [hψ_zero n x hx] using indicator_nonneg (fun y _ => norm_nonneg (h y)) x
  · by_cases hx : x ∈ K
    · simp [hψK _ x hx, indicator_of_mem hx]
    · obtain ⟨n, hn⟩ : ∃ n, x ∉ W n := by simpa [← hWK] using hx
      rw [indicator_of_notMem hx]
      exact tendsto_const_nhds.congr' <| eventually_atTop.2
        ⟨n, fun m hm => by simp [hψ_zero m x fun h => hn (hWanti hm h)]⟩

/-- The bound on pairings with nonnegative test functions bounds the integral of `h` over every
compact set. -/
private theorem enorm_setIntegral_isCompact_le (hh : LocallyIntegrable h ρ)
    (hk : ∀ K, IsCompact K → ∫⁻ x in K, k x ∂ρ ≠ ∞)
    (H : ∀ ψ : 𝓓(Ω, ℝ), (∀ x, 0 ≤ ψ x) → (∀ x, ψ x ≤ 1) → ∀ W : Set Ω, IsOpen W →
      tsupport ψ ⊆ (↑) '' W → ‖∫ x, ψ x * h x ∂ρ‖ₑ ≤ ∫⁻ x in W, k x ∂ρ)
    {K : Set Ω} (hK : IsCompact K) : ‖∫ x in K, h x ∂ρ‖ₑ ≤ ∫⁻ x in K, k x ∂ρ := by
  have := Ω.isOpen.locallyCompactSpace
  obtain ⟨L, hL, hKL⟩ := exists_compact_superset hK
  obtain ⟨W, hWo, hWL, hKW, hWanti, hWK⟩ := hK.isClosed.exists_antitone_isOpen_iInter_eq hKL
  have hcut (n : ℕ) : ∃ ψ : 𝓓(Ω, ℝ), (∀ x, 0 ≤ ψ x) ∧ (∀ x, ψ x ≤ 1) ∧ (∀ x ∈ K, ψ x = 1) ∧
      tsupport ψ ⊆ (↑) '' W n := by
    obtain ⟨ψ, h01, h1, hsupp⟩ := TestFunction.exists_cutoff_tsupport_subset
      (hK.image continuous_subtype_val) (Ω.isOpen.isOpenMap_subtype_val _ (hWo n))
      (image_mono (hKW n)) (Subtype.coe_image_subset _ _)
    exact ⟨ψ, fun x => (h01 x).1, fun x => (h01 x).2,
      fun x hx => h1.self_of_nhdsSet x ⟨x, hx, rfl⟩, hsupp⟩
  choose ψ hψ0 hψ1 hψK hψW using hcut
  have hψ_zero (n : ℕ) (x : Ω) (hx : x ∉ W n) : ψ n x = 0 :=
    image_eq_zero_of_notMem_tsupport fun hx' => hx <| by
      obtain ⟨y, hy, hyx⟩ := hψW n hx'
      rwa [← Subtype.val_injective hyx]
  have hlim := tendsto_integral_testFunction_mul hh hK hL hWL hWanti hWK hψ0 hψ1 hψK hψ_zero
  -- The weights of the neighbourhoods converge to the weight of `K`, by continuity from above.
  have hlimk : Tendsto (fun n => ∫⁻ x in W n, k x ∂ρ) atTop (𝓝 (∫⁻ x in K, k x ∂ρ)) := by
    have h := tendsto_measure_iInter_atTop (μ := ρ.withDensity k)
      (fun n => (hWo n).measurableSet.nullMeasurableSet) hWanti
      ⟨0, by
        rw [withDensity_apply _ (hWo 0).measurableSet]
        exact ne_top_of_le_ne_top (hk L hL) (lintegral_mono_set (hWL 0))⟩
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

/-- **A density with nonnegative pairings is nonnegative.** If `h : Ω → ℝ` is locally integrable
for a measure `ρ` on `Ω` and `0 ≤ ∫ ψ x * h x ∂ρ` for every nonnegative test function `ψ` on `Ω`,
then `0 ≤ h x` for `ρ`-almost every `x`. -/
theorem ae_nonneg_of_forall_integral_mul_nonneg (hh : LocallyIntegrable h ρ)
    (H : ∀ ψ : 𝓓(Ω, ℝ), (∀ x, 0 ≤ ψ x) → 0 ≤ ∫ x, ψ x * h x ∂ρ) :
    ∀ᵐ x ∂ρ, 0 ≤ h x := by
  have := Ω.isOpen.locallyCompactSpace
  -- Bound `|h|` by the positive part of a measurable representative `g` of `h`.
  set g := hh.aestronglyMeasurable.mk h
  have hg : h =ᵐ[ρ] g := hh.aestronglyMeasurable.ae_eq_mk
  have hgm : Measurable g := hh.aestronglyMeasurable.stronglyMeasurable_mk.measurable
  have hle : ∀ᵐ x ∂ρ, ‖h x‖ₑ ≤ ENNReal.ofReal (g x) := by
    refine ae_enorm_le_of_forall_nonneg hh (ENNReal.measurable_ofReal.comp hgm)
      (fun K hK => ne_top_of_le_ne_top ((hh.congr hg).integrableOn_isCompact hK).2.ne
        (lintegral_mono fun x => ?_)) fun ψ hψ0 hψ1 W hW hψW => ?_
    · rw [Real.enorm_eq_ofReal_abs]
      exact ENNReal.ofReal_le_ofReal (le_abs_self _)
    have hψ (x : Ω) (hx : x ∉ W) : ψ x = 0 := image_eq_zero_of_notMem_tsupport fun hx' => hx <| by
      obtain ⟨y, hy, hyx⟩ := hψW hx'
      rwa [← Subtype.val_injective hyx]
    -- `ψ h ≤ (h⁺ on W)`, and the integral of a function is at most that of its positive part.
    have hpt : ∀ᵐ x : Ω ∂ρ,
        ENNReal.ofReal (ψ x * h x) ≤ W.indicator (fun x => ENNReal.ofReal (g x)) x := by
      filter_upwards [hg] with x hx
      by_cases hxW : x ∈ W
      · rw [indicator_of_mem hxW, ← hx]
        refine ENNReal.ofReal_le_ofReal_iff'.2 ?_
        rcases le_or_gt (h x) 0 with h0 | h0
        · exact Or.inr (mul_nonpos_of_nonneg_of_nonpos (hψ0 x) h0)
        · exact Or.inl (mul_le_of_le_one_left h0.le (hψ1 x))
      · simp [hψ x hxW]
    rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (H ψ hψ0), ← lintegral_indicator hW.measurableSet]
    refine le_trans ?_ (lintegral_mono_ae hpt)
    by_cases hint : Integrable (fun x : Ω => ψ x * h x) ρ
    · rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hint]
      exact (ENNReal.ofReal_le_ofReal (sub_le_self _ ENNReal.toReal_nonneg)).trans
        ENNReal.ofReal_toReal_le
    · simp [integral_undef hint]
  filter_upwards [hle, hg] with x hx hxg
  rw [← hxg, Real.enorm_eq_ofReal_abs] at hx
  rcases ENNReal.ofReal_le_ofReal_iff'.1 hx with h' | h'
  · exact (abs_nonneg _).trans h'
  · exact (abs_nonpos_iff.1 h').ge

section Dual

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [SeparableSpace F]

/-- **A dual-valued density bounded on test vector fields is pointwise bounded.** Let
`h : Ω → StrongDual ℝ F` be locally integrable for a measure `ρ` on `Ω`, and let `k` be a measurable
weight with finite integral over every compact subset of `Ω`. If for every open `U ⊆ Ω` and every
test vector field `φ` supported in `U` with `‖φ x‖ ≤ 1` we have
`|∫ h x (φ x) ∂ρ| ≤ ∫⁻ x in U, k x ∂ρ`, then the dual norm satisfies `‖h x‖ ≤ k x` for
`ρ`-almost every `x`. -/
theorem ae_enorm_le_of_forall_enorm_integral_apply_le {h : Ω → StrongDual ℝ F}
    (hh : LocallyIntegrable h ρ) (hkm : Measurable k)
    (hk : ∀ K, IsCompact K → ∫⁻ x in K, k x ∂ρ ≠ ∞)
    (H : ∀ U : Opens E, U ≤ Ω → ∀ φ : 𝓓(Ω, F), tsupport φ ⊆ U → (∀ x, ‖φ x‖ ≤ 1) →
      ‖∫ x, h x (φ x) ∂ρ‖ₑ ≤ ∫⁻ x in (↑) ⁻¹' (U : Set E), k x ∂ρ) :
    ∀ᵐ x ∂ρ, ‖h x‖ₑ ≤ k x := by
  have := Ω.isOpen.locallyCompactSpace
  -- Each component `h · w` is bounded by `‖w‖ k`.
  have hw (w : F) : ∀ᵐ x ∂ρ, ‖h x w‖ₑ ≤ ‖w‖ₑ * k x := by
    refine ae_enorm_le_of_forall_nonneg
      (locallyIntegrable_iff.2 fun K hK =>
        (hh.integrableOn_isCompact hK).apply_continuousLinearMap w)
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
    have hint : ∫ x, h x (φ x) ∂ρ = ‖w‖⁻¹ * ∫ x, ψ x * h x w ∂ρ := by
      rw [← integral_const_mul]
      congr 1 with x
      simp only [hφ, map_smul, smul_eq_mul]
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
    calc ‖∫ x, ψ x * h x w ∂ρ‖ₑ
        = ‖w‖ₑ * (‖w‖ₑ⁻¹ * ‖∫ x, ψ x * h x w ∂ρ‖ₑ) := by
          rw [← mul_assoc, ENNReal.mul_inv_cancel (by simpa using hw0) enorm_ne_top, one_mul]
      _ ≤ ‖w‖ₑ * ∫⁻ x in W, k x ∂ρ := by gcongr
  -- Combine the bounds along a dense sequence of directions.
  filter_upwards [ae_all_iff.2 fun n => hw (denseSeq F n)] with x hx
  rcases eq_top_or_lt_top (k x) with hkx | hkx
  · simp [hkx]
  lift k x to ℝ≥0 using hkx.ne with q hq
  have hle (w : F) : ‖h x w‖ ≤ q * ‖w‖ := by
    refine (denseRange_denseSeq F).induction_on w
      (isClosed_le (h x).continuous.norm (continuous_const.mul continuous_norm)) fun n => ?_
    have := hx n
    rw [enorm_eq_nnnorm, enorm_eq_nnnorm, ← ENNReal.coe_mul, ENNReal.coe_le_coe] at this
    rw [mul_comm]
    exact_mod_cast this
  rw [enorm_eq_nnnorm, ENNReal.coe_le_coe, ← NNReal.coe_le_coe, coe_nnnorm]
  exact (h x).opNorm_le_bound q.2 hle

end Dual

section Inner

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [SeparableSpace F]

/-- **A density bounded on test vector fields is pointwise bounded.** Let `h : Ω → F` be locally
integrable for a measure `ρ` on `Ω`, with values in a separable real inner product space `F`, and
let `k` be a measurable weight with finite integral over every compact subset of `Ω`. If for every
open `U ⊆ Ω` and every test vector field `φ` supported in `U` with `‖φ x‖ ≤ 1` we have
`|∫ ⟪φ x, h x⟫ ∂ρ| ≤ ∫⁻ x in U, k x ∂ρ`, then `‖h x‖ ≤ k x` for `ρ`-almost every `x`. -/
theorem ae_enorm_le_of_forall_enorm_integral_inner_le {h : Ω → F} (hh : LocallyIntegrable h ρ)
    (hkm : Measurable k) (hk : ∀ K, IsCompact K → ∫⁻ x in K, k x ∂ρ ≠ ∞)
    (H : ∀ U : Opens E, U ≤ Ω → ∀ φ : 𝓓(Ω, F), tsupport φ ⊆ U → (∀ x, ‖φ x‖ ≤ 1) →
      ‖∫ x, ⟪φ x, h x⟫ ∂ρ‖ₑ ≤ ∫⁻ x in (↑) ⁻¹' (U : Set E), k x ∂ρ) :
    ∀ᵐ x ∂ρ, ‖h x‖ₑ ≤ k x := by
  have := Ω.isOpen.locallyCompactSpace
  -- Apply the dual version to the Riesz dual `innerSL ℝ (h x)`, which has the same norm.
  have hh' : LocallyIntegrable (fun x => innerSL ℝ (h x)) ρ :=
    locallyIntegrable_iff.2 fun K hK => (innerSL ℝ).integrable_comp (hh.integrableOn_isCompact hK)
  filter_upwards [ae_enorm_le_of_forall_enorm_integral_apply_le hh' hkm hk fun U hU φ hφU hφ => by
    simpa only [innerSL_apply_apply, real_inner_comm] using H U hU φ hφU hφ] with x hx
  rwa [← enorm_norm, innerSL_apply_norm, enorm_norm] at hx

end Inner

end TauCeti
