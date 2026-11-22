/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Analysis.Calculus.BumpFunction.Normed
public import Mathlib.Analysis.Convolution
public import Mathlib.Analysis.Distribution.TestFunction
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.Normed.Affine.MazurUlam
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Measure.OpenPos
public import TauCeti.Analysis.Distribution.TestFunction.Postcomp
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import TauCeti.MeasureTheory.Function.Lp.ApproximateIdentity
import TauCeti.MeasureTheory.Function.LpSeminorm.ContinuousOn
import TauCeti.Topology.UniformSpace.UniformConvergence.ENorm

/-!
# Inner-product pairings and Riesz transport on test functions

Let `Ω` be an open set of a real normed space `E` and `V` a real inner product space. A test
function `φ ∈ 𝓓^{n}(Ω, V)` pairs with a field `w : E → V` through the inner product, and the
integrals `∫ ⟪φ, w⟫` are the natural way to test a vector-valued equation. This file records that
these pairings, and those with the directional derivatives of `φ` (`1 ≤ n`), are integrable for
locally integrable `w`, that they pass to `L¹`, uniform-operator, and `Lᵖ` mollification limits on
any set containing the support of `φ`, and proves the fundamental lemma of the calculus of
variations in this form: a locally integrable field is determined almost everywhere on `Ω` by its
pairings with `𝓓(Ω, V)`.

For real or complex Hilbert coefficients, `TestFunction.rieszEquiv` is a real continuous
linear equivalence to dual-valued tests, conjugating the coefficient scalar action. The original
test topologies and every finite regularity order and infinity are retained.
`TestFunction.eq_of_forall_integral_inner_eq` separates tests by their spatial inner pairings
for any Borel measure finite on compact sets and positive on nonempty open sets; it needs no
completeness of the coefficient space.

## Main results

* `TestFunction.integrable_inner`: `x ↦ ⟪φ x, w x⟫` is integrable for `φ ∈ 𝓓^{n}(Ω, V)` and `w`
  locally integrable on `Ω`.
* `TestFunction.integrable_inner_fderiv`: `x ↦ ⟪∂_v φ x, w x⟫` is integrable for `φ ∈ 𝓓^{n}(Ω, V)`
  (`1 ≤ n`) and `w` locally integrable on `Ω`.
* `TestFunction.tendsto_integral_inner_of_tendsto_lintegral_enorm_sub`: `∫ ⟪φ, g i⟫ → ∫ ⟪φ, g₀⟫`
  when `g i → g₀` in `L¹` on a set containing `tsupport φ`.
* `TestFunction.tendsto_integral_inner_clm_of_tendstoUniformlyOn`:
  `∫ ⟪φ, A i · (u ·)⟫ → ∫ ⟪φ, B · (u ·)⟫` when `A i` is eventually continuous on `tsupport φ`,
  `A i → B` uniformly on `tsupport φ`, and `u` is locally integrable on `Ω`.
* `TestFunction.tendsto_integral_inner_bilin_normed_convolution`:
  `∫ ⟪φ, B ((ρ i ⋆ 1_W U) ·) (u ·)⟫` converges to `∫ ⟪φ, B (U ·) (u ·)⟫` when `U ∈ Lᵖ(W)`,
  `u ∈ L^q(W)` and `p⁻¹ + q⁻¹ ≤ 1`.
* `TauCeti.ae_eq_of_forall_integral_inner_eq`: two locally integrable fields with the same
  pairings against every `φ ∈ 𝓓(Ω, V)` agree almost everywhere on `Ω`. The target `V` need only
  be complete; the proof tests against `ψ • c` for scalar test functions `ψ` and a constant
  vector `c`.
* `TauCeti.ae_eq_of_forall_integral_inner_eq_rclike`: the same for fields valued in an inner
  product space over `𝕜 = ℝ` or `ℂ`, paired through the `𝕜`-valued inner product.
* `TauCeti.eq_of_forall_integral_inner_eq_of_continuous`: two continuous fields with the same
  pairings `∫ ⟪φ, ·⟫_𝕜` against every test function on `E` are equal, for a measure finite on
  compact sets and charging every nonempty open set.
-/

public section

open Filter MeasureTheory Set TopologicalSpace
open scoped ContDiff Convolution Distributions ENNReal InnerProductSpace Topology

section RealPairings

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [OpensMeasurableSpace E] {μ : Measure E} {Ω : Opens E}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]

namespace TestFunction

/-- A `C^n` test function paired with a locally integrable field is integrable. -/
theorem integrable_inner {n : ℕ∞} {w : E → V} (hw : LocallyIntegrableOn w Ω μ)
    (φ : 𝓓^{n}(Ω, V)) : Integrable (fun x => ⟪(φ : E → V) x, w x⟫_ℝ) μ :=
  φ.integrable_bilin (innerSL ℝ) hw

/-- A directional derivative of a `C^n` test function (`1 ≤ n`), paired with a locally integrable
field, is integrable. -/
theorem integrable_inner_fderiv {n : ℕ∞} {w : E → V} (hw : LocallyIntegrableOn w Ω μ)
    (φ : 𝓓^{n}(Ω, V)) (v : E) (hn : 1 ≤ n := by simp) :
    Integrable (fun x => ⟪fderiv ℝ (φ : E → V) x v, w x⟫_ℝ) μ := by
  have hn0 : (0 : ℕ∞) + 1 ≤ n := by simpa using hn
  have hne : (n : WithTop ℕ∞) ≠ 0 := mod_cast (zero_lt_one.trans_le hn).ne'
  refine ((lineDerivCLM ℝ v φ : 𝓓^{0}(Ω, V)).integrable_inner hw).congr (.of_forall fun x => ?_)
  dsimp only
  rw [lineDerivCLM_apply_of_le hn0, (φ.contDiff.differentiable hne x).lineDeriv_eq_fderiv]

omit [OpensMeasurableSpace E] in
/-- If `g i → g₀` in `L¹(s)` on a set `s` containing the topological support of `φ`, then the
inner-product pairings `∫ x, ⟪φ x, g i x⟫_ℝ ∂μ` converge to `∫ x, ⟪φ x, g₀ x⟫_ℝ ∂μ`.
The approximating pairings need only be eventually integrable, and the limiting pairing needs
only to be almost everywhere strongly measurable. -/
theorem tendsto_integral_inner_of_tendsto_lintegral_enorm_sub {n : ℕ∞} {ι : Type*}
    {l : Filter ι} {s : Set E} (φ : 𝓓^{n}(Ω, V)) (hφs : tsupport (φ : E → V) ⊆ s)
    {g : ι → E → V} {g₀ : E → V}
    (hg : ∀ᶠ i in l, Integrable (fun x => ⟪(φ : E → V) x, g i x⟫_ℝ) μ)
    (hg₀ : AEStronglyMeasurable (fun x => ⟪(φ : E → V) x, g₀ x⟫_ℝ) μ)
    (hlim : Tendsto (fun i => ∫⁻ x in s, ‖g i x - g₀ x‖ₑ ∂μ) l (𝓝 0)) :
    Tendsto (fun i => ∫ x, ⟪(φ : E → V) x, g i x⟫_ℝ ∂μ) l
      (𝓝 (∫ x, ⟪(φ : E → V) x, g₀ x⟫_ℝ ∂μ)) := by
  obtain ⟨M, hM⟩ := φ.continuous.bounded_above_of_compact_support φ.hasCompactSupport
  have hlimM : Tendsto (fun i => ENNReal.ofReal M * ∫⁻ x in s, ‖g i x - g₀ x‖ₑ ∂μ) l (𝓝 0) := by
    simpa using ENNReal.Tendsto.const_mul hlim (Or.inr ENNReal.ofReal_ne_top)
  refine tendsto_integral_of_L1 _ hg₀ hg (tendsto_of_tendsto_of_tendsto_of_le_of_le
    tendsto_const_nhds hlimM (fun _ => zero_le) fun i => ?_)
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine (lintegral_mono fun x => ?_).trans (lintegral_indicator_le _ _)
  by_cases hxs : x ∈ s
  · rw [Set.indicator_of_mem hxs, ← inner_sub_right, Real.eNorm_eq_ofReal_abs,
      ← ofReal_norm, ← ENNReal.ofReal_mul ((norm_nonneg _).trans (hM x))]
    exact ENNReal.ofReal_le_ofReal <| (abs_real_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_right (hM x) (norm_nonneg _))
  · simp [Set.indicator_of_notMem hxs, image_eq_zero_of_notMem_tsupport fun h => hxs (hφs h)]

/-- Pairing a `C^n` test function `φ` against `x ↦ A i x (u x)` converges to
`∫ x, ⟪φ x, B x (u x)⟫_ℝ ∂μ` when `A i → B` uniformly on `tsupport φ`, `A i` is eventually
continuous on `tsupport φ`, and `u` is locally integrable on `Ω`. -/
theorem tendsto_integral_inner_clm_of_tendstoUniformlyOn {n : ℕ∞}
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {ι : Type*} {l : Filter ι}
    (φ : 𝓓^{n}(Ω, V)) {u : E → F} (hu : LocallyIntegrableOn u Ω μ)
    {A : ι → E → F →L[ℝ] V} {B : E → F →L[ℝ] V}
    (hA : ∀ᶠ i in l, ContinuousOn (A i) (tsupport (φ : E → V)))
    (hunif : TendstoUniformlyOn A B l (tsupport (φ : E → V))) :
    Tendsto (fun i => ∫ x, ⟪(φ : E → V) x, A i x (u x)⟫_ℝ ∂μ) l
      (𝓝 (∫ x, ⟪(φ : E → V) x, B x (u x)⟫_ℝ ∂μ)) := by
  rcases eq_or_neBot l with rfl | _
  · exact tendsto_bot
  set K := tsupport (φ : E → V)
  have hKm : MeasurableSet K := (isClosed_tsupport _).measurableSet
  have huK : IntegrableOn u K μ :=
    hu.integrableOn_compact_subset φ.tsupport_subset φ.hasCompactSupport
  have hint {C : E → F →L[ℝ] V} (hC : ContinuousOn C K) :
      Integrable (fun x => ⟪(φ : E → V) x, C x (u x)⟫_ℝ) μ :=
    (integrableOn_iff_integrable_of_support_subset
      fun _ hx => subset_tsupport _ fun h0 => hx (by simp [h0])).1 <|
      memLp_one_iff_integrable.1 <| (innerSL ℝ).memLp_of_bilin 1 φ.memLp_top <|
        (ContinuousLinearMap.id ℝ (F →L[ℝ] V)).memLp_of_bilin 1
          (hC.memLp_top_restrict_of_subset_isCompact φ.hasCompactSupport hKm subset_rfl)
          (memLp_one_iff_integrable.2 huK)
  have hsup : Tendsto (fun i => (⨆ y ∈ K, ‖A i y - B y‖ₑ) * ∫⁻ x in K, ‖u x‖ₑ ∂μ) l (𝓝 0) := by
    simpa using ENNReal.Tendsto.mul_const hunif.tendsto_iSup_enorm_sub (Or.inr huK.2.ne)
  refine φ.tendsto_integral_inner_of_tendsto_lintegral_enorm_sub subset_rfl
    (hA.mono fun _ => hint) (hint (hunif.continuousOn hA.frequently)).aestronglyMeasurable
    (tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsup
      (fun _ => zero_le) fun i => ?_)
  rw [← lintegral_const_mul'' _ huK.aestronglyMeasurable.eNorm]
  refine setLIntegral_mono' hKm fun x hx => ?_
  rw [← sub_apply]
  have h1 : ‖(A i x - B x) (u x)‖ₑ ≤ ‖A i x - B x‖ₑ * ‖u x‖ₑ := by
    simpa only [← ofReal_norm, ENNReal.ofReal_mul (norm_nonneg _)] using
      ENNReal.ofReal_le_ofReal ((A i x - B x).le_opNorm (u x))
  exact h1.trans (by gcongr; exact le_biSup (fun y => ‖A i y - B y‖ₑ) hx)

omit [OpensMeasurableSpace E] in
/-- Pairing a `C^n` test function supported in a null-measurable set `W` against
`x ↦ B (((ρ i).normed μ ⋆ 1_W U) x) (u x)` converges to `∫ x, ⟪φ x, B (U x) (u x)⟫_ℝ ∂μ` when
`U ∈ Lᵖ(W)`, `u ∈ L^q(W)` and `p⁻¹ + q⁻¹ ≤ 1` (allowing `p = ∞` or `q = ∞`). -/
theorem tendsto_integral_inner_bilin_normed_convolution
    [FiniteDimensional ℝ E] [BorelSpace E] [μ.IsAddHaarMeasure]
    {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] {n : ℕ∞}
    (B : F →L[ℝ] G →L[ℝ] V) {p q : ℝ≥0∞} (hpq : p⁻¹ + q⁻¹ ≤ 1)
    {W : Set E} (hW : NullMeasurableSet W μ) (φ : 𝓓^{n}(Ω, V))
    (hφW : tsupport (φ : E → V) ⊆ W) {U : E → F} (hU : MemLp U p (μ.restrict W))
    {u : E → G} (hu : MemLp u q (μ.restrict W))
    {ι : Type*} {l : Filter ι} {ρ : ι → ContDiffBump (0 : E)}
    (hρ : Tendsto (fun i => (ρ i).rOut) l (𝓝 0)) :
    Tendsto (fun i => ∫ x, ⟪(φ : E → V) x,
        B (((ρ i).normed μ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] W.indicator U) x)
          (u x)⟫_ℝ ∂μ)
      l (𝓝 (∫ x, ⟪(φ : E → V) x, B (U x) (u x)⟫_ℝ ∂μ)) := by
  set p' : ℝ≥0∞ := (1 - p⁻¹)⁻¹
  have hp1 : p⁻¹ ≤ 1 := le_self_add.trans hpq
  have : p.HolderConjugate p' := ⟨by rw [inv_inv, inv_one, add_tsub_cancel_of_le hp1]⟩
  have hp'q : p' ≤ q := by
    rw [← inv_inv q]
    exact ENNReal.inv_le_inv.2 <|
      (ENNReal.add_sub_cancel_left (ne_top_of_le_ne_top ENNReal.one_ne_top hp1)).symm.trans_le
        (tsub_le_tsub_right hpq p⁻¹)
  set K : Set E := tsupport (φ : E → V)
  have hKm : NullMeasurableSet K μ := (isClosed_tsupport _).measurableSet.nullMeasurableSet
  have : IsFiniteMeasure (μ.restrict K) :=
    isFiniteMeasure_restrict.2 φ.hasCompactSupport.measure_lt_top.ne
  have huK : MemLp u p' (μ.restrict K) :=
    (hu.mono_measure (Measure.restrict_mono hφW le_rfl)).mono_exponent hp'q
  let C : V →L[ℝ] G →L[ℝ] F →L[ℝ] ℝ :=
    ((ContinuousLinearMap.compL ℝ F V ℝ).comp (innerSL ℝ)).bilinearComp
      (ContinuousLinearMap.id ℝ V) B.flip
  have ha : MemLp (fun x => C ((φ : E → V) x) (K.indicator u x)) p' μ :=
    C.memLp_of_bilin p' φ.memLp_top ((memLp_indicator_iff_restrict hKm).2 huK)
  have hlim := (ContinuousLinearMap.id ℝ (F →L[ℝ] ℝ)).tendsto_integral_bilin_normed_convolution
    hρ ha ((memLp_indicator_iff_restrict hW).2 hU)
  have hpt (x : E) (y : F) :
      C ((φ : E → V) x) (K.indicator u x) y = ⟪(φ : E → V) x, B y (u x)⟫_ℝ := by
    by_cases hx : x ∈ K
    · simp [C, hx]
    · simp [C, image_eq_zero_of_notMem_tsupport hx]
  have hlim_rhs : ∫ x, ⟪(φ : E → V) x, B (W.indicator U x) (u x)⟫_ℝ ∂μ =
      ∫ x, ⟪(φ : E → V) x, B (U x) (u x)⟫_ℝ ∂μ :=
    integral_congr_ae (.of_forall fun x => by
      by_cases hx : x ∈ W
      · simp [hx]
      · simp [image_eq_zero_of_notMem_tsupport fun h => hx (hφW h)])
  simpa only [ContinuousLinearMap.id_apply, hpt, hlim_rhs] using hlim

end TestFunction

namespace TauCeti

variable [CompleteSpace V] [FiniteDimensional ℝ E] [BorelSpace E]

/-- The **fundamental lemma** for vector-valued test functions: locally integrable `g, h` on the
open set `Ω` with `∫ ⟪φ, g⟫ = ∫ ⟪φ, h⟫` for every `φ ∈ 𝓓(Ω, V)` agree almost everywhere on
`Ω`. -/
theorem ae_eq_of_forall_integral_inner_eq {g h : E → V} (hg : LocallyIntegrableOn g Ω μ)
    (hh : LocallyIntegrableOn h Ω μ)
    (H : ∀ φ : 𝓓(Ω, V), ∫ x, ⟪(φ : E → V) x, g x⟫_ℝ ∂μ = ∫ x, ⟪(φ : E → V) x, h x⟫_ℝ ∂μ) :
    g =ᵐ[μ.restrict Ω] h := by
  have hgh : LocallyIntegrableOn (g - h) Ω μ := hg.sub hh
  have key := IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero Ω.isOpen hgh
    fun ψ hψ hψc hψΩ => by
      set w := ∫ x, ψ x • (g - h) x ∂μ
      let ψ' : 𝓓(Ω, ℝ) := ⟨ψ, hψ, hψc, hψΩ⟩
      let Φ : 𝓓(Ω, V) := TestFunction.postcompCLM (ContinuousLinearMap.toSpanSingleton ℝ w) ψ'
      have hΦ := H Φ
      have hint : Integrable (fun x => ψ x • (g - h) x) μ :=
        ψ'.integrable_smul hgh
      have : ⟪w, w⟫_ℝ = 0 := by
        calc ⟪w, w⟫_ℝ = ∫ x, ⟪w, ψ x • (g - h) x⟫_ℝ ∂μ := (integral_inner hint w).symm
          _ = ∫ x, ⟪(Φ : E → V) x, g x⟫_ℝ ∂μ - ∫ x, ⟪(Φ : E → V) x, h x⟫_ℝ ∂μ := by
            rw [← integral_sub (Φ.integrable_inner hg) (Φ.integrable_inner hh)]
            refine integral_congr_ae (.of_forall fun x => ?_)
            simp [Φ, ψ', inner_smul_left, inner_smul_right, inner_sub_right, mul_sub]
          _ = 0 := sub_eq_zero.2 hΦ
      exact inner_self_eq_zero.1 this
  rw [Filter.EventuallyEq, ae_restrict_iff' Ω.isOpen.measurableSet]
  filter_upwards [key] with x hx hxΩ
  exact sub_eq_zero.1 (hx hxΩ)

/-- The **fundamental lemma** for fields valued in an inner product space `F` over `𝕜 = ℝ` or `ℂ`:
locally integrable `g, h` on the open set `Ω` with `∫ ⟪φ, g⟫_𝕜 = ∫ ⟪φ, h⟫_𝕜` for every
`φ ∈ 𝓓(Ω, F)` agree almost everywhere on `Ω`. -/
theorem ae_eq_of_forall_integral_inner_eq_rclike {𝕜 F : Type*} [RCLike 𝕜] [NormedAddCommGroup F]
    [InnerProductSpace 𝕜 F] [NormedSpace ℝ F] [IsScalarTower ℝ 𝕜 F] [CompleteSpace F]
    {g h : E → F} (hg : LocallyIntegrableOn g Ω μ) (hh : LocallyIntegrableOn h Ω μ)
    (H : ∀ φ : 𝓓(Ω, F), ∫ x, ⟪(φ : E → F) x, g x⟫_𝕜 ∂μ = ∫ x, ⟪(φ : E → F) x, h x⟫_𝕜 ∂μ) :
    g =ᵐ[μ.restrict Ω] h := by
  have hsmul (r : ℝ) (a b : F) : ⟪r • a, b⟫_𝕜 = r • ⟪a, b⟫_𝕜 := by
    rw [← algebraMap_smul 𝕜 r a, RCLike.algebraMap_eq_ofReal, inner_smul_real_left]
  -- The real parts of the pairings form the underlying real inner product. It is built by hand,
  -- rather than as `InnerProductSpace.rclikeToReal`, so that it extends the given
  -- `[NormedSpace ℝ F]` on which `𝓓(Ω, F)` depends instead of the restricted-scalars structure.
  let _ : InnerProductSpace ℝ F :=
    { inner a b := RCLike.re ⟪a, b⟫_𝕜
      norm_sq_eq_re_inner a := by simp [sq]
      conj_inner_symm a b := by simp [inner_re_symm]
      add_left a b c := by simp [inner_add_left]
      smul_left a b r := by simp [hsmul, RCLike.smul_re] }
  -- The pairing `⟪·, ·⟫_𝕜` is real bilinear, so it is integrable against test functions.
  let B : F →L[ℝ] F →L[ℝ] 𝕜 := LinearMap.mkContinuous₂
    (LinearMap.mk₂ ℝ (fun a b ↦ ⟪a, b⟫_𝕜) inner_add_left hsmul inner_add_right
      fun r a b ↦ by rw [← inner_conj_symm, hsmul, RCLike.conj_smul, inner_conj_symm]) 1
    fun a b ↦ by simpa using norm_inner_le_norm (𝕜 := 𝕜) a b
  have hB (a b : F) : B a b = ⟪a, b⟫_𝕜 := by
    simp only [B, LinearMap.mkContinuous₂_apply, LinearMap.mk₂_apply]
  have hre (a b : F) : ⟪a, b⟫_ℝ = RCLike.re ⟪a, b⟫_𝕜 := rfl
  refine ae_eq_of_forall_integral_inner_eq hg hh fun φ ↦ ?_
  have hint {f : E → F} (hf : LocallyIntegrableOn f Ω μ) :
      Integrable (fun x ↦ ⟪(φ : E → F) x, f x⟫_𝕜) μ := by
    simpa only [hB] using φ.integrable_bilin B hf
  simp only [hre]
  rw [integral_re (hint hg), integral_re (hint hh), H φ]

/-- The **fundamental lemma** for continuous fields valued in an inner product space `F` over
`𝕜 = ℝ` or `ℂ`: continuous `g, h : E → F` with `∫ ⟪φ, g⟫_𝕜 = ∫ ⟪φ, h⟫_𝕜` for every `φ ∈ 𝓓(E, F)`
are equal, for a measure finite on compact sets and charging every nonempty open set. -/
theorem eq_of_forall_integral_inner_eq_of_continuous {𝕜 F : Type*} [RCLike 𝕜]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [NormedSpace ℝ F] [IsScalarTower ℝ 𝕜 F]
    [CompleteSpace F] [IsFiniteMeasureOnCompacts μ] [μ.IsOpenPosMeasure] {g h : E → F}
    (hg : Continuous g) (hh : Continuous h)
    (H : ∀ φ : 𝓓((⊤ : Opens E), F),
      ∫ x, ⟪(φ : E → F) x, g x⟫_𝕜 ∂μ = ∫ x, ⟪(φ : E → F) x, h x⟫_𝕜 ∂μ) :
    g = h := by
  have hae := ae_eq_of_forall_integral_inner_eq_rclike
    (hg.locallyIntegrable.locallyIntegrableOn _) (hh.locallyIntegrable.locallyIntegrableOn _) H
  rw [Opens.coe_top, Measure.restrict_univ] at hae
  exact (hg.ae_eq_iff_eq μ hh).1 hae

end TauCeti

end RealPairings

noncomputable section

open TopologicalSpace ComplexConjugate MeasureTheory
open scoped Distributions

namespace TestFunction

variable {𝕜 E V : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [InnerProductSpace 𝕜 V] [CompleteSpace V]
  {n : ℕ∞} {Ω : Opens E}

/-- Native Riesz transport of coefficient values, for the original test-function topologies.
The equivalence is real-linear and conjugates the coefficient scalar action. -/
def rieszEquiv : 𝓓^{n}(Ω, V) ≃L[ℝ] 𝓓^{n}(Ω, StrongDual 𝕜 V) :=
  postcompCLE ((InnerProductSpace.toDual 𝕜 V).toIsometryEquiv
    |>.toRealLinearIsometryEquivOfMapZero (map_zero (InnerProductSpace.toDual 𝕜 V))
    |>.toContinuousLinearEquiv)

/-- Riesz transport evaluates to the original `𝕜` Hilbert pairing. -/
@[simp]
theorem rieszEquiv_apply (u : 𝓓^{n}(Ω, V)) (x : E) (v : V) :
    rieszEquiv u x v = inner 𝕜 (u x) v := by
  simp only [rieszEquiv, postcompCLE_apply, LinearIsometryEquiv.coe_toContinuousLinearEquiv]
  have he := IsometryEquiv.coe_toRealLinearIsometryEquivOfMapZero
    (InnerProductSpace.toDual 𝕜 V).toIsometryEquiv (map_zero (InnerProductSpace.toDual 𝕜 V))
  exact (congrArg (fun L : V → StrongDual 𝕜 V ↦ L (u x) v) he).trans
    InnerProductSpace.toDual_apply_apply

/-- The inverse native map recovers the Riesz representative of every original dual-valued test. -/
@[simp]
theorem rieszEquiv_symm_apply (φ : 𝓓^{n}(Ω, StrongDual 𝕜 V)) (x : E) (v : V) :
    inner 𝕜 (rieszEquiv.symm φ x) v = φ x v := by
  have h := congrArg (fun q : 𝓓^{n}(Ω, StrongDual 𝕜 V) ↦ q x v)
    (rieszEquiv.apply_symm_apply φ)
  simpa only [rieszEquiv_apply] using h

/-- Native Riesz transport conjugates the original `𝕜` test action. -/
theorem rieszEquiv_smul (c : 𝕜) (u : 𝓓^{n}(Ω, V)) :
    rieszEquiv (𝕜 := 𝕜) (c • u) = conj c • rieszEquiv (𝕜 := 𝕜) u := by
  apply TestFunction.ext
  intro x
  apply ContinuousLinearMap.ext
  intro y
  simp only [rieszEquiv_apply, smul_apply, inner_smul_left]
  rfl

/-- The inverse Riesz transport has the same conjugate-scalar action. -/
theorem rieszEquiv_symm_smul (c : 𝕜) (φ : 𝓓^{n}(Ω, StrongDual 𝕜 V)) :
    (rieszEquiv (𝕜 := 𝕜) (V := V)).symm (c • φ) =
      conj c • (rieszEquiv (𝕜 := 𝕜) (V := V)).symm φ := by
  apply (rieszEquiv (𝕜 := 𝕜) (V := V)).injective
  rw [ContinuousLinearEquiv.apply_symm_apply, rieszEquiv_smul,
    starRingEnd_self_apply, ContinuousLinearEquiv.apply_symm_apply]

omit [CompleteSpace V] in
/-- Native tests are separated by their spatial Hilbert pairings. The measure need only be
finite on compact sets and charge every nonempty open set; no finite-dimensional base is needed. -/
theorem eq_of_forall_integral_inner_eq [MeasurableSpace E] [BorelSpace E] {μ : Measure E}
    [IsFiniteMeasureOnCompacts μ] [Measure.IsOpenPosMeasure μ] {f g : 𝓓^{n}(Ω, V)}
    (h : ∀ u : 𝓓^{n}(Ω, V), (∫ x, inner 𝕜 (u x) (f x) ∂μ) =
      ∫ x, inner 𝕜 (u x) (g x) ∂μ) : f = g := by
  have hint (a b : 𝓓^{n}(Ω, V)) : Integrable (fun x ↦ inner 𝕜 (a x) (b x)) μ :=
    (a.continuous.inner b.continuous).integrable_of_hasCompactSupport
      (a.hasCompactSupport.mono fun x hx hz ↦ hx (by simp [hz]))
  let d := f - g
  have hz : (∫ x, inner 𝕜 (d x) (d x) ∂μ) = 0 := by
    have he (x : E) : inner 𝕜 (d x) (d x) =
        inner 𝕜 (d x) (f x) - inner 𝕜 (d x) (g x) := inner_sub_right _ _ _
    simp_rw [he]
    rw [integral_sub (hint d f) (hint d g), h d, sub_self]
  have hi : Integrable (fun x ↦ ‖d x‖ ^ 2) μ :=
    (d.continuous.norm.pow 2).integrable_of_hasCompactSupport
      (by
        have hc := d.hasCompactSupport.comp_left
          (g := fun v : V ↦ ‖v‖ ^ 2) (by simp)
        exact hc)
  have hnorm : (∫ x, ‖d x‖ ^ 2 ∂μ) = 0 := by
    have hr := congrArg (RCLike.re : 𝕜 → ℝ) hz
    rw [← integral_re (hint d d)] at hr
    simpa only [inner_self_eq_norm_sq_to_K, RCLike.re_ofReal_pow, map_zero] using hr
  have hae := (integral_eq_zero_iff_of_nonneg (fun x ↦ sq_nonneg ‖d x‖) hi).mp hnorm
  have hdz : (d : E → V) =ᵐ[μ] 0 := by
    filter_upwards [hae] with x hx
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp hx)
  have hde : (d : E → V) = 0 := (d.continuous.ae_eq_iff_eq μ continuous_zero).mp hdz
  apply sub_eq_zero.mp
  apply TestFunction.ext
  intro x
  exact congrFun hde x

end TestFunction
