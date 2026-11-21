/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import TauCeti.Analysis.Normed.Module.Ball.Retraction
public import TauCeti.MeasureTheory.Function.DecreasingRearrangement
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import TauCeti.MeasureTheory.Function.Lorentz
import TauCeti.MeasureTheory.Function.Lp.DominatedConvergence
import TauCeti.MeasureTheory.Measure.Haar.MultHaar

/-!
# Dyadic layers of an `Lᵖ` function

Let `g ∈ Lᵖ(X, μ; E)` with `1 ≤ p < ∞`, and let `f* = μ.decreasingRearrangement ‖g‖ₑ` be the
decreasing rearrangement of its modulus. The levels `f*(2ᵏ)`, `k ∈ ℤ`, decrease with `k`: at most
measure `2ᵏ` of `X` lies above the height `f*(2ᵏ)`. Cutting `g` at these heights decomposes it into
**dyadic layers**

`g = ∑ₖ gₖ`,  `gₖ = R_{f*(2ᵏ)} g - R_{f*(2ᵏ⁺¹)} g`,

where `R_r g` is the radial retraction of `g` at height `r`, which truncates the modulus of `g` at
`r` without changing its direction (`MeasureTheory.Lp.radialRetraction`). The layer `gₖ` is the
part of `g` between the heights `f*(2ᵏ⁺¹)` and `f*(2ᵏ)`, so

* it is bounded by `f*(2ᵏ)` (`MeasureTheory.Lp.enorm_dyadicLayer_le`);
* it vanishes where `‖g‖ ≤ f*(2ᵏ⁺¹)`, a set whose complement has measure at most `2ᵏ⁺¹`, so
  `‖gₖ‖_s ≤ 2^{(k+1)/s} f*(2ᵏ)` for every exponent `s` (`MeasureTheory.Lp.eLpNorm_dyadicLayer_le`);
* the layers between two indices telescope to a difference of two retractions
  (`MeasureTheory.Lp.sum_range_dyadicLayer`), and the partial sums converge to `g` in `Lᵖ`
  (`MeasureTheory.Lp.tendsto_sum_range_dyadicLayer`).

The size of the layers is measured by the Lorentz gauge: for `0 < q ≤ 2`,

`∑ₖ (2^{k/q} f*(2ᵏ))² ≤ 2^{2/q} (log 2)⁻¹ ‖g‖_q²`

(`TauCeti.tsum_rpow_mul_decreasingRearrangement_sq_le`), the dyadic form of the embedding of `L^q`
into the Lorentz class `L^{q,2}`. So the layers form an atomic decomposition of `g`: atoms of height
`f*(2ᵏ)` supported on sets of measure `2ᵏ⁺¹`, with square summable normalized heights. The endpoint
Strichartz estimate (`TauCeti.Analysis.PDE.Strichartz.Endpoint`) applies it at each time to a
function of space and time.

For that application the layers must depend measurably on the function they decompose. The
distribution function `g ↦ μ {c < ‖g‖ₑ}`, and hence `g ↦ f*(s)`, is lower semicontinuous on `Lᵖ`
(`MeasureTheory.Lp.lowerSemicontinuous_measure_setOf_lt_enorm`,
`MeasureTheory.Lp.lowerSemicontinuous_decreasingRearrangement_enorm`), and the radial retraction is
a continuous function of the function at a fixed height; writing the retraction at height `r > 0`
as the rescaled retraction at height `1` makes it measurable in a measurable height. So for an
almost everywhere strongly measurable family `F : β → Lᵖ`, the levels `b ↦ f*_{F b}(s)` are almost
everywhere measurable and the layers `b ↦ (F b)ₖ` are almost everywhere strongly measurable
(`MeasureTheory.AEStronglyMeasurable.dyadicLayer`).

## Main declarations

* `MeasureTheory.Lp.radialRetraction`: the radial retraction of an `Lᵖ` function at a height.
* `MeasureTheory.Lp.dyadicLayer`: the `k`-th dyadic layer of an `Lᵖ` function.
* `MeasureTheory.Lp.enorm_dyadicLayer_le`, `MeasureTheory.Lp.dyadicLayer_eq_zero_of_enorm_le`,
  `MeasureTheory.Lp.eLpNorm_dyadicLayer_le`: size and support of a layer.
* `MeasureTheory.Lp.tendsto_sum_range_dyadicLayer`: the layers sum to the function, with partial
  sums of norm at most its norm (`MeasureTheory.Lp.norm_sum_range_dyadicLayer_le`).
* `TauCeti.tsum_rpow_mul_decreasingRearrangement_sq_le`: square summability of the normalized
  levels.
* `MeasureTheory.AEStronglyMeasurable.dyadicLayer`: measurability of the layers of a family.

## References

* M. Keel and T. Tao, *Endpoint Strichartz estimates*, Amer. J. Math. 120 (1998), 955–980.
* L. Grafakos, *Classical Fourier Analysis*, 3rd ed., GTM 249, Springer, 2014, §1.4.
-/

public noncomputable section

open Filter Set Topology
open scoped ENNReal NNReal

namespace MeasureTheory

variable {X E : Type*} {mX : MeasurableSpace X} {μ : Measure X} [NormedAddCommGroup E]
  {p : ℝ≥0∞}

namespace Lp

/-! ### Lower semicontinuity of the distribution function -/

/-- The distribution function `g ↦ μ {c < ‖g‖ₑ}` is lower semicontinuous on `Lᵖ`: a sequence
converging in `Lᵖ` has a subsequence converging almost everywhere, along which the superlevel sets
of the limit are eventually covered. -/
theorem lowerSemicontinuous_measure_setOf_lt_enorm [Fact (1 ≤ p)] (c : ℝ≥0∞) :
    LowerSemicontinuous fun g : Lp E p μ ↦ μ {x | c < ‖g x‖ₑ} := by
  rw [lowerSemicontinuous_iff_isClosed_preimage]
  intro y
  refine isClosed_of_closure_subset fun g hg ↦ ?_
  obtain ⟨u, hu, hlim⟩ := mem_closure_iff_seq_limit.1 hg
  have hp : p ≠ 0 := (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne'
  obtain ⟨ns, -, hae⟩ := (tendstoInMeasure_of_tendsto_eLpNorm hp
    ((Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ _).1 hlim)).exists_seq_tendsto_ae
  set A : ℕ → Set X := fun N ↦ ⋂ i ≥ N, {x | c < ‖u (ns i) x‖ₑ}
  have hA : Monotone A := fun N M hNM _ hx ↦
    mem_iInter₂.2 fun i hi ↦ mem_iInter₂.1 hx i (hNM.trans hi)
  have hsub : {x | c < ‖g x‖ₑ} ≤ᵐ[μ] ⋃ N, A N := by
    filter_upwards [hae] with x hx hcx
    obtain ⟨N, hN⟩ := eventually_atTop.1 (hx.eNorm.eventually (lt_mem_nhds hcx))
    exact mem_iUnion.2 ⟨N, mem_iInter₂.2 hN⟩
  calc μ {x | c < ‖g x‖ₑ} ≤ μ (⋃ N, A N) := measure_mono_ae hsub
    _ = ⨆ N, μ (A N) := hA.measure_iUnion
    _ ≤ y := iSup_le fun N ↦ (measure_mono (iInter₂_subset N le_rfl)).trans (hu (ns N))

/-- The decreasing rearrangement `g ↦ f*(s)` of the modulus is lower semicontinuous on `Lᵖ`. -/
theorem lowerSemicontinuous_decreasingRearrangement_enorm [Fact (1 ≤ p)] (s : ℝ) :
    LowerSemicontinuous fun g : Lp E p μ ↦ μ.decreasingRearrangement (fun x ↦ ‖g x‖ₑ) s :=
  fun g _ hc ↦ (lowerSemicontinuous_measure_setOf_lt_enorm _ g _
    (μ.lt_decreasingRearrangement_iff.1 hc)).mono fun _ h ↦ μ.lt_decreasingRearrangement_iff.2 h

/-- For an almost everywhere strongly measurable family `F : β → Lᵖ`, the decreasing
rearrangements `b ↦ f*_{F b}(s)` of the moduli are almost everywhere measurable. -/
theorem _root_.MeasureTheory.AEStronglyMeasurable.aemeasurable_decreasingRearrangement_enorm
    [Fact (1 ≤ p)] {β : Type*} [MeasurableSpace β] {ν : Measure β} {F : β → Lp E p μ}
    (hF : AEStronglyMeasurable F ν) (s : ℝ) :
    AEMeasurable (fun b ↦ μ.decreasingRearrangement (fun x ↦ ‖F b x‖ₑ) s) ν := by
  borelize ↥(Lp E p μ)
  exact (lowerSemicontinuous_decreasingRearrangement_enorm s).measurable.comp_aemeasurable
    hF.aemeasurable

/-! ### Size of the decreasing rearrangement of an `Lᵖ` function -/

/-- Chebyshev's inequality for the decreasing rearrangement: `s f*(s)ᵖ ≤ ‖g‖_pᵖ`. -/
theorem ofReal_mul_decreasingRearrangement_rpow_le (hp0 : p ≠ 0) (hp : p ≠ ∞) (g : Lp E p μ)
    (s : ℝ) : ENNReal.ofReal s * μ.decreasingRearrangement (fun x ↦ ‖g x‖ₑ) s ^ p.toReal ≤
      eLpNorm g p μ ^ p.toReal := by
  have hp' : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  have hg : AEMeasurable (fun x ↦ ‖g x‖ₑ ^ p.toReal) μ :=
    (Lp.aestronglyMeasurable g).eNorm.pow_const _
  rw [← μ.decreasingRearrangement_rpow _ hp']
  calc _ ≤ ∫⁻ t in Ioc 0 s, μ.decreasingRearrangement (fun x ↦ ‖g x‖ₑ ^ p.toReal) t :=
        μ.mul_decreasingRearrangement_le_setLIntegral_Ioc _ s
    _ ≤ ∫⁻ t in Ioi 0, μ.decreasingRearrangement (fun x ↦ ‖g x‖ₑ ^ p.toReal) t :=
        lintegral_mono_set Ioc_subset_Ioi_self
    _ = ∫⁻ x, ‖g x‖ₑ ^ p.toReal ∂μ := μ.lintegral_decreasingRearrangement hg
    _ = eLpNorm g p μ ^ p.toReal := by
        rw [eLpNorm_eq_lintegral_rpow_eNorm_toReal hp0 hp (Lp.aestronglyMeasurable g),
          ← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hp'.ne', ENNReal.rpow_one]

/-- The decreasing rearrangement of an `Lᵖ` function, `p < ∞`, is finite at positive arguments. -/
theorem decreasingRearrangement_lt_top (hp0 : p ≠ 0) (hp : p ≠ ∞) (g : Lp E p μ) {s : ℝ}
    (hs : 0 < s) : μ.decreasingRearrangement (fun x ↦ ‖g x‖ₑ) s < ∞ := by
  have hp' : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  have h := ofReal_mul_decreasingRearrangement_rpow_le hp0 hp g s
  have hlt : ENNReal.ofReal s * μ.decreasingRearrangement (fun x ↦ ‖g x‖ₑ) s ^ p.toReal < ∞ :=
    h.trans_lt (ENNReal.rpow_lt_top_of_nonneg hp'.le (Lp.eLpNorm_ne_top g))
  rw [ENNReal.mul_lt_top_iff] at hlt
  rcases hlt with ⟨-, hlt⟩ | h0 | h0
  · exact (ENNReal.rpow_lt_top_iff_of_pos hp').1 hlt
  · simp [ENNReal.ofReal_eq_zero, hs.not_ge] at h0
  · exact ((ENNReal.rpow_eq_zero_iff_of_pos hp').1 h0).symm ▸ ENNReal.zero_lt_top

/-- The decreasing rearrangement of an `Lᵖ` function, `p < ∞`, tends to zero at infinity. -/
theorem tendsto_decreasingRearrangement_atTop_nhds_zero (hp0 : p ≠ 0) (hp : p ≠ ∞)
    (g : Lp E p μ) :
    Tendsto (μ.decreasingRearrangement fun x ↦ ‖g x‖ₑ) atTop (𝓝 0) := by
  have hp' : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  set M := eLpNorm g p μ ^ p.toReal
  have hM : M ≠ ∞ := (ENNReal.rpow_lt_top_of_nonneg hp'.le (Lp.eLpNorm_ne_top g)).ne
  -- `f*(s) ≤ (M / s) ^ (1 / p)`, which tends to `0`.
  have hbound : ∀ᶠ s in atTop, μ.decreasingRearrangement (fun x ↦ ‖g x‖ₑ) s ≤
      (M / ENNReal.ofReal s) ^ p.toReal⁻¹ := by
    filter_upwards [eventually_gt_atTop 0] with s hs
    rw [← ENNReal.rpow_le_rpow_iff hp', ← ENNReal.rpow_mul, inv_mul_cancel₀ hp'.ne',
      ENNReal.rpow_one, ENNReal.le_div_iff_mul_le (Or.inl (by simpa using hs))
        (Or.inl ENNReal.ofReal_ne_top), mul_comm]
    exact ofReal_mul_decreasingRearrangement_rpow_le hp0 hp g s
  have hlim : Tendsto (fun s : ℝ ↦ (M / ENNReal.ofReal s) ^ p.toReal⁻¹) atTop (𝓝 0) := by
    have h : Tendsto (fun s : ℝ ↦ M / ENNReal.ofReal s) atTop (𝓝 0) := by
      simpa using ENNReal.Tendsto.const_div
        (ENNReal.tendsto_ofReal_atTop) (Or.inr hM)
    simpa [ENNReal.zero_rpow_of_pos (inv_pos.2 hp')] using h.ennrpow_const p.toReal⁻¹
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun _ ↦ bot_le) hbound

/-- The levels `f*(2ᵏ)` decrease with `k`. -/
private theorem toNNReal_decreasingRearrangement_succ_le (hp0 : p ≠ 0) (hp : p ≠ ∞)
    (g : Lp E p μ) (k : ℤ) :
    (μ.decreasingRearrangement (fun x ↦ ‖g x‖ₑ) ((2 : ℝ) ^ (k + 1))).toNNReal ≤
      (μ.decreasingRearrangement (fun x ↦ ‖g x‖ₑ) ((2 : ℝ) ^ k)).toNNReal :=
  ENNReal.toNNReal_mono (decreasingRearrangement_lt_top hp0 hp g (zpow_pos two_pos k)).ne
    (μ.antitone_decreasingRearrangement _ (zpow_le_zpow_right₀ one_le_two (by omega)))

/-! ### The radial retraction of an `Lᵖ` function -/

variable [NormedSpace ℝ E]

/-- The **radial retraction** of `g ∈ Lᵖ` at height `r`: the function
`x ↦ min 1 (r / ‖g x‖) • g x`, which truncates the modulus of `g` at `r` and keeps its
direction. -/
def radialRetraction (r : ℝ≥0) (g : Lp E p μ) : Lp E p μ :=
  (TauCeti.lipschitzWith_radialRetraction (E := E) r.coe_nonneg).compLp
    (TauCeti.radialRetraction_of_norm_eq_zero (_root_.norm_zero (E := E))) g

theorem coeFn_radialRetraction (r : ℝ≥0) (g : Lp E p μ) :
    radialRetraction r g =ᵐ[μ] fun x ↦ TauCeti.radialRetraction r (g x) :=
  LipschitzWith.coeFn_compLp _ _ _

/-- At a fixed height, the radial retraction is a continuous function on `Lᵖ`. -/
theorem continuous_radialRetraction [Fact (1 ≤ p)] (r : ℝ≥0) :
    Continuous (radialRetraction (μ := μ) (E := E) (p := p) r) :=
  (TauCeti.lipschitzWith_radialRetraction (E := E) r.coe_nonneg).continuous_compLp
    (TauCeti.radialRetraction_of_norm_eq_zero (_root_.norm_zero (E := E)))

/-- The radial retraction at height `r` is the retraction at height `1` conjugated by the dilation
by `r`. -/
theorem radialRetraction_eq_smul (r : ℝ≥0) (g : Lp E p μ) :
    radialRetraction r g = (r : ℝ) • radialRetraction 1 ((r : ℝ)⁻¹ • g : Lp E p μ) := by
  refine Lp.ext_iff.2 ?_
  filter_upwards [coeFn_radialRetraction r g,
    Lp.coeFn_smul (r : ℝ) (radialRetraction 1 ((r : ℝ)⁻¹ • g : Lp E p μ)),
    coeFn_radialRetraction 1 ((r : ℝ)⁻¹ • g : Lp E p μ), Lp.coeFn_smul (r : ℝ)⁻¹ g]
    with x h1 h2 h3 h4
  rw [h1, h2, Pi.smul_apply, h3, h4, Pi.smul_apply, NNReal.coe_one]
  exact TauCeti.radialRetraction_eq_smul_radialRetraction_one r.coe_nonneg _

/-- For an almost everywhere measurable height `r` and an almost everywhere strongly measurable
family `F : β → Lᵖ`, the radial retractions `b ↦ R_{r b} (F b)` form an almost everywhere strongly
measurable family. -/
theorem _root_.MeasureTheory.AEStronglyMeasurable.radialRetraction [Fact (1 ≤ p)] {β : Type*}
    [MeasurableSpace β] {ν : Measure β} {r : β → ℝ≥0} {F : β → Lp E p μ}
    (hr : AEMeasurable r ν) (hF : AEStronglyMeasurable F ν) :
    AEStronglyMeasurable (fun b ↦ Lp.radialRetraction (r b) (F b)) ν := by
  rw [show (fun b ↦ Lp.radialRetraction (r b) (F b)) = fun b ↦ (r b : ℝ) •
    Lp.radialRetraction 1 ((r b : ℝ)⁻¹ • F b : Lp E p μ) from
    funext fun b ↦ radialRetraction_eq_smul _ _]
  have hr' : AEMeasurable (fun b ↦ (r b : ℝ)) ν := measurable_coe_nnreal_real.comp_aemeasurable hr
  exact hr'.aestronglyMeasurable.smul ((continuous_radialRetraction 1).comp_aestronglyMeasurable
    (hr'.inv.aestronglyMeasurable.smul hF))

/-! ### Dyadic layers -/

/-- The **`k`-th dyadic layer** of `g ∈ Lᵖ`: the part of `g` between the heights `f*(2ᵏ⁺¹)` and
`f*(2ᵏ)`, where `f*` is the decreasing rearrangement of `‖g‖ₑ`. It is the difference of the radial
retractions of `g` at these two heights. -/
def dyadicLayer (k : ℤ) (g : Lp E p μ) : Lp E p μ :=
  radialRetraction (μ.decreasingRearrangement (fun x ↦ ‖g x‖ₑ) ((2 : ℝ) ^ k)).toNNReal g -
    radialRetraction (μ.decreasingRearrangement (fun x ↦ ‖g x‖ₑ) ((2 : ℝ) ^ (k + 1))).toNNReal g

theorem dyadicLayer_def (k : ℤ) (g : Lp E p μ) :
    dyadicLayer k g =
      radialRetraction (μ.decreasingRearrangement (fun x ↦ ‖g x‖ₑ) ((2 : ℝ) ^ k)).toNNReal g -
      radialRetraction (μ.decreasingRearrangement (fun x ↦ ‖g x‖ₑ) ((2 : ℝ) ^ (k + 1))).toNNReal
        g := (rfl)

/-- The `k`-th dyadic layers of an almost everywhere strongly measurable family `F : β → Lᵖ`
form an almost everywhere strongly measurable family. -/
theorem _root_.MeasureTheory.AEStronglyMeasurable.dyadicLayer [Fact (1 ≤ p)] {β : Type*}
    [MeasurableSpace β] {ν : Measure β} {F : β → Lp E p μ} (hF : AEStronglyMeasurable F ν)
    (k : ℤ) : AEStronglyMeasurable (fun b ↦ dyadicLayer k (F b)) ν :=
  (AEStronglyMeasurable.radialRetraction
    (hF.aemeasurable_decreasingRearrangement_enorm _).ennreal_toNNReal hF).sub
    (AEStronglyMeasurable.radialRetraction
      (hF.aemeasurable_decreasingRearrangement_enorm _).ennreal_toNNReal hF)

theorem coeFn_dyadicLayer (k : ℤ) (g : Lp E p μ) :
    dyadicLayer k g =ᵐ[μ] fun x ↦
      TauCeti.radialRetraction
          (μ.decreasingRearrangement (fun x ↦ ‖g x‖ₑ) ((2 : ℝ) ^ k)).toNNReal (g x) -
        TauCeti.radialRetraction
          (μ.decreasingRearrangement (fun x ↦ ‖g x‖ₑ) ((2 : ℝ) ^ (k + 1))).toNNReal (g x) := by
  filter_upwards [Lp.coeFn_sub (radialRetraction _ g) (radialRetraction _ g),
    coeFn_radialRetraction (μ.decreasingRearrangement (fun x ↦ ‖g x‖ₑ) ((2 : ℝ) ^ k)).toNNReal g,
    coeFn_radialRetraction
      (μ.decreasingRearrangement (fun x ↦ ‖g x‖ₑ) ((2 : ℝ) ^ (k + 1))).toNNReal g]
    with x h h1 h2
  rw [dyadicLayer_def, h, Pi.sub_apply, h1, h2]

/-- The `k`-th dyadic layer of `g` is bounded by `f*(2ᵏ)`. -/
theorem enorm_dyadicLayer_le (hp0 : p ≠ 0) (hp : p ≠ ∞) (k : ℤ) (g : Lp E p μ) :
    ∀ᵐ x ∂μ, ‖dyadicLayer k g x‖ₑ ≤ μ.decreasingRearrangement (fun x ↦ ‖g x‖ₑ) ((2 : ℝ) ^ k) := by
  filter_upwards [coeFn_dyadicLayer k g] with x hx
  have h := TauCeti.norm_radialRetraction_sub_radialRetraction_le (NNReal.coe_nonneg _)
    (NNReal.coe_le_coe.2 (toNNReal_decreasingRearrangement_succ_le hp0 hp g k)) (g x)
  rw [hx, ← ofReal_norm]
  refine (ENNReal.ofReal_le_ofReal (h.trans (min_le_right _ _))).trans ?_
  rw [ENNReal.ofReal_coe_nnreal]
  exact ENNReal.coe_toNNReal_le_self

/-- The `k`-th dyadic layer of `g` is bounded by `‖g‖`. -/
theorem enorm_dyadicLayer_le_enorm (hp0 : p ≠ 0) (hp : p ≠ ∞) (k : ℤ) (g : Lp E p μ) :
    ∀ᵐ x ∂μ, ‖dyadicLayer k g x‖ₑ ≤ ‖g x‖ₑ := by
  filter_upwards [coeFn_dyadicLayer k g] with x hx
  rw [hx]
  exact eNorm_le_iff_norm_le.2 ((TauCeti.norm_radialRetraction_sub_radialRetraction_le
    (NNReal.coe_nonneg _) (NNReal.coe_le_coe.2 (toNNReal_decreasingRearrangement_succ_le hp0 hp g
      k)) (g x)).trans (min_le_left _ _))

/-- The `k`-th dyadic layer of `g` vanishes where `‖g‖ₑ ≤ f*(2ᵏ⁺¹)`. -/
theorem dyadicLayer_eq_zero_of_enorm_le (hp0 : p ≠ 0) (hp : p ≠ ∞) (k : ℤ) (g : Lp E p μ) :
    ∀ᵐ x ∂μ, ‖g x‖ₑ ≤ μ.decreasingRearrangement (fun x ↦ ‖g x‖ₑ) ((2 : ℝ) ^ (k + 1)) →
      dyadicLayer k g x = 0 := by
  filter_upwards [coeFn_dyadicLayer k g] with x hx hle
  rw [hx, sub_eq_zero]
  refine TauCeti.radialRetraction_eq_radialRetraction_of_norm_le ?_
    (NNReal.coe_le_coe.2 (toNNReal_decreasingRearrangement_succ_le hp0 hp g k))
  rw [← ofReal_norm, ← ENNReal.ofReal_toReal
    (decreasingRearrangement_lt_top hp0 hp g (zpow_pos two_pos (k + 1))).ne] at hle
  exact (ENNReal.ofReal_le_ofReal_iff ENNReal.toReal_nonneg).1 hle

/-- **The size of a dyadic layer.** For every exponent `s`, the `k`-th dyadic layer of `g` has
`‖gₖ‖_s ≤ (2ᵏ⁺¹) ^ (1 / s) f*(2ᵏ)`: it is bounded by `f*(2ᵏ)` and supported in the set
`{f*(2ᵏ⁺¹) < ‖g‖}`, of measure at most `2ᵏ⁺¹`. -/
theorem eLpNorm_dyadicLayer_le (hp0 : p ≠ 0) (hp : p ≠ ∞) (k : ℤ) (g : Lp E p μ) (s : ℝ≥0∞) :
    eLpNorm (dyadicLayer k g) s μ ≤
      ENNReal.ofReal ((2 : ℝ) ^ (k + 1)) ^ s.toReal⁻¹ *
        μ.decreasingRearrangement (fun x ↦ ‖g x‖ₑ) ((2 : ℝ) ^ k) := by
  set a := μ.decreasingRearrangement (fun x ↦ ‖g x‖ₑ) ((2 : ℝ) ^ k)
  set S := {x | μ.decreasingRearrangement (fun x ↦ ‖g x‖ₑ) ((2 : ℝ) ^ (k + 1)) < ‖g x‖ₑ}
  have hS : MeasurableSet S :=
    measurableSet_lt measurable_const (Lp.stronglyMeasurable g).eNorm
  have hind : (dyadicLayer k g : X → E) =ᵐ[μ] S.indicator (dyadicLayer k g) := by
    filter_upwards [dyadicLayer_eq_zero_of_enorm_le hp0 hp k g] with x hx
    by_cases hxS : x ∈ S
    · rw [indicator_of_mem hxS]
    · rw [indicator_of_notMem hxS, hx (not_lt.1 hxS)]
  have ha : a ≠ ∞ := (decreasingRearrangement_lt_top hp0 hp g (zpow_pos two_pos k)).ne
  rw [eLpNorm_congr_ae hind, eLpNorm_indicator_eq_eLpNorm_restrict hS.nullMeasurableSet]
  refine (eLpNorm_le_of_ae_bound (C := a.toReal) (Lp.aestronglyMeasurable _).restrict
    (ae_restrict_of_ae ((enorm_dyadicLayer_le hp0 hp k g).mono fun x hx ↦ ?_))).trans ?_
  · rw [← ENNReal.ofReal_le_ofReal_iff ENNReal.toReal_nonneg, ofReal_norm,
      ENNReal.ofReal_toReal ha]
    exact hx
  · rw [Measure.restrict_apply_univ, ENNReal.ofReal_toReal ha]
    gcongr
    exact μ.measure_setOf_decreasingRearrangement_lt_le _ _

/-- The dyadic layers of `g` with indices `-N ≤ k < N` add up to the difference of the radial
retractions of `g` at the heights `f*(2⁻ᴺ)` and `f*(2ᴺ)`. -/
theorem sum_range_dyadicLayer (N : ℕ) (g : Lp E p μ) :
    ∑ i ∈ Finset.range (2 * N), dyadicLayer ((i : ℤ) - N) g =
      radialRetraction (μ.decreasingRearrangement (fun x ↦ ‖g x‖ₑ) ((2 : ℝ) ^ (-(N : ℤ)))).toNNReal
          g -
        radialRetraction (μ.decreasingRearrangement (fun x ↦ ‖g x‖ₑ) ((2 : ℝ) ^ (N : ℤ))).toNNReal
          g := by
  have h := Finset.sum_range_sub' (fun i : ℕ ↦ radialRetraction
    (μ.decreasingRearrangement (fun x ↦ ‖g x‖ₑ) ((2 : ℝ) ^ ((i : ℤ) - N))).toNNReal g) (2 * N)
  convert h using 3 with i
  · rw [dyadicLayer_def]
    congr 5
    push_cast
    ring
  · congr 4
    simp
  · congr 4
    push_cast
    ring

/-- The partial sums of the dyadic layers of `g` have norm at most `‖g‖`. -/
theorem norm_sum_range_dyadicLayer_le (hp0 : p ≠ 0) (hp : p ≠ ∞) (N : ℕ) (g : Lp E p μ) :
    ‖∑ i ∈ Finset.range (2 * N), dyadicLayer ((i : ℤ) - N) g‖ ≤ ‖g‖ := by
  set f := fun x ↦ ‖g x‖ₑ
  have hle : (μ.decreasingRearrangement f ((2 : ℝ) ^ (N : ℤ))).toNNReal ≤
      (μ.decreasingRearrangement f ((2 : ℝ) ^ (-(N : ℤ)))).toNNReal :=
    ENNReal.toNNReal_mono (decreasingRearrangement_lt_top hp0 hp g (zpow_pos two_pos _)).ne
      (μ.antitone_decreasingRearrangement _ (zpow_le_zpow_right₀ one_le_two (by omega)))
  rw [sum_range_dyadicLayer]
  refine Lp.norm_le_norm_of_ae_le ?_
  filter_upwards [Lp.coeFn_sub (radialRetraction _ g) (radialRetraction _ g),
    coeFn_radialRetraction (μ.decreasingRearrangement f ((2 : ℝ) ^ (-(N : ℤ)))).toNNReal g,
    coeFn_radialRetraction (μ.decreasingRearrangement f ((2 : ℝ) ^ (N : ℤ))).toNNReal g]
    with x h h1 h2
  rw [h, Pi.sub_apply, h1, h2]
  exact (TauCeti.norm_radialRetraction_sub_radialRetraction_le (NNReal.coe_nonneg _)
    (NNReal.coe_le_coe.2 hle) (g x)).trans (min_le_left _ _)

/-- Radial retractions of a fixed vector depend continuously on a nonnegative height. -/
private theorem tendsto_radialRetraction_of_tendsto (v : E) {ρ : ℕ → ℝ} {ρ₀ : ℝ}
    (h : Tendsto ρ atTop (𝓝 ρ₀)) (hρ : ∀ N, 0 ≤ ρ N) :
    Tendsto (fun N ↦ TauCeti.radialRetraction (ρ N) v) atTop
      (𝓝 (TauCeti.radialRetraction ρ₀ v)) := by
  have hρ₀ : 0 ≤ ρ₀ := ge_of_tendsto' h hρ
  have hc := ((continuous_id.max continuous_const).radialRetraction (f := fun _ : ℝ ↦ v)
    (fun _ ↦ le_max_right _ 0) continuous_const).tendsto ρ₀
  simpa [Function.comp_def, max_eq_left (hρ _), max_eq_left hρ₀] using hc.comp h

/-- The radial retraction of `v` at a height `r ≥ 0` is its retraction at `min r ‖v‖`. -/
private theorem radialRetraction_min_norm (r : ℝ) (v : E) :
    TauCeti.radialRetraction r v = TauCeti.radialRetraction (min r ‖v‖) v := by
  rcases le_total r ‖v‖ with h | h
  · rw [min_eq_left h]
  · rw [min_eq_right h, TauCeti.radialRetraction_eq_radialRetraction_of_norm_le le_rfl h]

/-- A difference of two radial retractions of `v`, minus `v`, has norm at most `3 ‖v‖`. -/
private theorem norm_radialRetraction_sub_radialRetraction_sub_le (a b : ℝ≥0) (v : E) :
    ‖TauCeti.radialRetraction a v - TauCeti.radialRetraction b v - v‖ ≤ 3 * ‖v‖ := by
  have h1 := TauCeti.norm_radialRetraction (NNReal.coe_nonneg a) v
  have h2 := TauCeti.norm_radialRetraction (NNReal.coe_nonneg b) v
  calc _ ≤ ‖TauCeti.radialRetraction a v‖ + ‖TauCeti.radialRetraction b v‖ + ‖v‖ := by
        refine (norm_sub_le _ _).trans ?_
        gcongr
        exact norm_sub_le _ _
    _ ≤ ‖v‖ + ‖v‖ + ‖v‖ := by
        rw [h1, h2]
        gcongr <;> exact min_le_left _ _
    _ = 3 * ‖v‖ := by ring

/-- If the upper heights `hi N` converge to a limit at least `‖v‖` and the lower heights `lo N`
converge to `0`, then `R_{hi N} v - R_{lo N} v → v`. -/
private theorem tendsto_radialRetraction_sub_radialRetraction (v : E) {hi : ℕ → ℝ≥0∞}
    {L : ℝ≥0∞} (hfin : ∀ N, hi N ≠ ∞) (hhi : Tendsto hi atTop (𝓝 L)) (hle : ‖v‖ₑ ≤ L)
    {lo : ℕ → ℝ≥0} (hlo : Tendsto (fun N ↦ (lo N : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun N ↦ TauCeti.radialRetraction (hi N).toNNReal v -
      TauCeti.radialRetraction (lo N) v) atTop (𝓝 v) := by
  -- Cut the upper heights at `‖v‖`, where they converge to `‖v‖`.
  have hmin : Tendsto (fun N ↦ (min (hi N) ‖v‖ₑ).toReal) atTop (𝓝 ‖v‖) := by
    have h := (ENNReal.tendsto_toReal (min_lt_of_right_lt eNorm_lt_top).ne).comp
      (hhi.min (tendsto_const_nhds (x := ‖v‖ₑ)))
    rw [min_eq_right hle, toReal_eNorm] at h
    exact h
  have hupper : Tendsto (fun N ↦ TauCeti.radialRetraction (hi N).toNNReal v) atTop (𝓝 v) := by
    have h := tendsto_radialRetraction_of_tendsto v hmin fun _ ↦ ENNReal.toReal_nonneg
    rw [TauCeti.radialRetraction_of_norm_le le_rfl] at h
    refine h.congr fun N ↦ ?_
    rw [ENNReal.toReal_min (hfin N) eNorm_ne_top, toReal_eNorm, ← radialRetraction_min_norm,
      ENNReal.coe_toNNReal_eq_toReal]
  have hlower : Tendsto (fun N ↦ TauCeti.radialRetraction (lo N) v) atTop (𝓝 0) := by
    have h := tendsto_radialRetraction_of_tendsto v hlo fun N ↦ NNReal.coe_nonneg _
    simpa [TauCeti.radialRetraction_def] using h
  simpa using hupper.sub hlower

/-- **The dyadic layers of an `Lᵖ` function sum to it**, `1 ≤ p < ∞`. -/
theorem tendsto_sum_range_dyadicLayer [Fact (1 ≤ p)] (hp : p ≠ ∞) (g : Lp E p μ) :
    Tendsto (fun N : ℕ ↦ ∑ i ∈ Finset.range (2 * N), dyadicLayer ((i : ℤ) - N) g) atTop
      (𝓝 g) := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne'
  set f := fun x ↦ ‖g x‖ₑ
  set hi : ℕ → ℝ≥0∞ := fun N ↦ μ.decreasingRearrangement f ((2 : ℝ) ^ (-(N : ℤ)))
  set lo : ℕ → ℝ≥0 := fun N ↦ (μ.decreasingRearrangement f ((2 : ℝ) ^ (N : ℤ))).toNNReal
  simp_rw [sum_range_dyadicLayer]
  rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm']
  -- The lower heights tend to `0`, the upper heights to the essential supremum of `‖g‖ₑ`.
  have hlo : Tendsto (fun N ↦ (lo N : ℝ)) atTop (𝓝 0) := by
    have h := (tendsto_decreasingRearrangement_atTop_nhds_zero hp0 hp g).comp
      (tendsto_pow_atTop_atTop_of_one_lt (one_lt_two (α := ℝ)))
    have h' := (ENNReal.tendsto_toNNReal ENNReal.zero_ne_top).comp h
    simpa [lo, Function.comp_def] using NNReal.tendsto_coe.2 h'
  have hhi : Tendsto hi atTop (𝓝 (essSup f μ)) := by
    refine (μ.tendsto_decreasingRearrangement_nhdsGT_zero f).comp
      (tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun N ↦ zpow_pos two_pos _⟩)
    have h := (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (2 : ℝ)⁻¹) (by norm_num)
      (by norm_num))
    simpa [Function.comp_def, zpow_neg, zpow_natCast, inv_pow] using h
  have hcoe : ∀ᵐ x ∂μ, ∀ N : ℕ,
      (radialRetraction (hi N).toNNReal g - radialRetraction (lo N) g : Lp E p μ) x =
        TauCeti.radialRetraction (hi N).toNNReal (g x) -
          TauCeti.radialRetraction (lo N) (g x) := by
    rw [ae_all_iff]
    intro N
    filter_upwards [Lp.coeFn_sub (radialRetraction (hi N).toNNReal g) (radialRetraction (lo N) g),
      coeFn_radialRetraction (hi N).toNNReal g, coeFn_radialRetraction (lo N) g]
      with x h h1 h2
    rw [h, Pi.sub_apply, h1, h2]
  -- Dominated convergence, with the bound `3 ‖g‖`.
  refine TauCeti.tendsto_eLpNorm_sub_of_ae_tendsto (C := 3) hp
    (Eventually.of_forall fun N ↦ Lp.aestronglyMeasurable _) (Lp.memLp g)
    (Eventually.of_forall fun N ↦ hcoe.mono fun x hx ↦ ?_) ?_
  · rw [hx N, ← ofReal_norm, ← ofReal_norm, ENNReal.coe_ofNat, ← ENNReal.ofReal_ofNat 3,
      ← ENNReal.ofReal_mul (by norm_num)]
    exact ENNReal.ofReal_le_ofReal (norm_radialRetraction_sub_radialRetraction_sub_le _ _ _)
  · filter_upwards [hcoe, ae_le_essSup (f := f)] with x hx hle
    exact (tendsto_radialRetraction_sub_radialRetraction (g x)
      (fun N ↦ (decreasingRearrangement_lt_top hp0 hp g (zpow_pos two_pos _)).ne) hhi hle
      hlo).congr fun N ↦ (hx N).symm

end Lp

end MeasureTheory

/-! ### Square summability of the dyadic levels -/

namespace TauCeti

open MeasureTheory

variable {X E : Type*} {mX : MeasurableSpace X} {μ : Measure X} [NormedAddCommGroup E]

/-- Dyadic sum and Lorentz gauge: with `φ(t) = t^{1/q} f*(t)`, the shifted levels
`2^{(k-1)/q} f*(2ᵏ)` have squared sum at most `(log 2)⁻¹ ∫ φ² dt / t`. -/
private theorem ofReal_log_two_mul_tsum_le_eLpNorm_multHaar {f : X → E} {q : ℝ≥0∞}
    (hq : 0 < q.toReal) :
    ENNReal.ofReal (Real.log 2) * ∑' k : ℤ, (ENNReal.ofReal ((2 : ℝ) ^ (k - 1)) ^ q.toReal⁻¹ *
        μ.decreasingRearrangement (fun x ↦ ‖f x‖ₑ) ((2 : ℝ) ^ k)) ^ (2 : ℝ) ≤
      eLpNorm (fun t ↦ ENNReal.ofReal (t ^ q.toReal⁻¹) *
        μ.decreasingRearrangement (fun x ↦ ‖f x‖ₑ) t) 2 multHaar ^ (2 : ℝ) := by
  set φ : ℝ → ℝ≥0∞ := fun t ↦ ENNReal.ofReal (t ^ q.toReal⁻¹) *
    μ.decreasingRearrangement (fun x ↦ ‖f x‖ₑ) t
  have hφ2 : ∫⁻ t, φ t ^ (2 : ℝ) ∂multHaar = eLpNorm φ 2 multHaar ^ (2 : ℝ) := by
    rw [eLpNorm_eq_eLpNorm' two_ne_zero ENNReal.ofNat_ne_top
      (μ.measurable_rpow_mul_decreasingRearrangement _ _).aestronglyMeasurable]
    simpa using lintegral_rpow_eNorm_eq_rpow_eLpNorm' (f := φ) (μ := multHaar) two_pos
  -- On `[2ᵏ⁻¹, 2ᵏ)` the `k`-th term is at most `φ²`.
  have hcmp := ofReal_mul_tsum_int_le_lintegral_multHaar (b := 2) (c := 2⁻¹) (μ := 1)
    one_le_two (by norm_num) (f := fun t ↦ φ t ^ (2 : ℝ))
    (g := fun k ↦ (ENNReal.ofReal ((2 : ℝ) ^ (k - 1)) ^ q.toReal⁻¹ *
      μ.decreasingRearrangement (fun x ↦ ‖f x‖ₑ) ((2 : ℝ) ^ k)) ^ (2 : ℝ)) fun k r hr ↦ by
      have hk : (2 : ℝ)⁻¹ * 2 ^ ((1 : ℝ) * k) = 2 ^ (k - 1) := by
        rw [one_mul, Real.rpow_intCast, zpow_sub₀ two_ne_zero, zpow_one, mul_comm, div_eq_mul_inv]
      have hk' : (2 : ℝ)⁻¹ * 2 ^ ((1 : ℝ) * k + |1|) = 2 ^ k := by
        rw [abs_one, one_mul, Real.rpow_add two_pos, Real.rpow_intCast, Real.rpow_one]
        field_simp
      rw [hk, hk'] at hr
      simp only [φ]
      rw [ENNReal.ofReal_rpow_of_nonneg (zpow_pos two_pos _).le (inv_nonneg.2 hq.le)]
      gcongr ?_ ^ _
      exact mul_le_mul' (ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow (zpow_pos two_pos _).le hr.1
        (inv_nonneg.2 hq.le))) (μ.antitone_decreasingRearrangement _ hr.2.le)
  rwa [abs_one, one_mul, hφ2] at hcmp

/-- `(2^{k/q} a)² = 2^{2/q} (2^{(k-1)/q} a)²`. -/
private theorem ofReal_two_zpow_rpow_mul_rpow_two {q : ℝ} (hq : 0 < q) (k : ℤ) (a : ℝ≥0∞) :
    (ENNReal.ofReal ((2 : ℝ) ^ k) ^ q⁻¹ * a) ^ (2 : ℝ) =
      ENNReal.ofReal (2 ^ (2 / q)) * (ENNReal.ofReal ((2 : ℝ) ^ (k - 1)) ^ q⁻¹ * a) ^ (2 : ℝ) := by
  have h2k : (2 : ℝ) ^ k = 2 * 2 ^ (k - 1) := by
    rw [zpow_sub₀ two_ne_zero, zpow_one]
    field_simp
  rw [h2k, ENNReal.ofReal_mul zero_le_two, ENNReal.mul_rpow_of_nonneg _ _ (inv_nonneg.2 hq.le),
    mul_assoc, ENNReal.mul_rpow_of_nonneg _ _ zero_le_two, ← ENNReal.rpow_mul,
    ENNReal.ofReal_rpow_of_nonneg zero_le_two (by positivity), inv_mul_eq_div]

/-- **Square summability of the normalized dyadic levels.** For `0 < q ≤ 2` and an almost
everywhere strongly measurable `f`, the levels `f*(2ᵏ)` of the decreasing rearrangement of `‖f‖ₑ`
satisfy

`∑ₖ (2^{k/q} f*(2ᵏ))² ≤ 2^{2/q} (log 2)⁻¹ ‖f‖_q²`.

The left side is a dyadic discretization of the square of the Lorentz gauge `‖f‖_{q,2}`, which is
at most `‖f‖_q` since `q ≤ 2`. -/
theorem tsum_rpow_mul_decreasingRearrangement_sq_le {f : X → E} (hf : AEStronglyMeasurable f μ)
    {q : ℝ≥0∞} (hq0 : q ≠ 0) (hq2 : q ≤ 2) :
    ∑' k : ℤ, (ENNReal.ofReal ((2 : ℝ) ^ k) ^ q.toReal⁻¹ *
        μ.decreasingRearrangement (fun x ↦ ‖f x‖ₑ) ((2 : ℝ) ^ k)) ^ (2 : ℝ) ≤
      ENNReal.ofReal (2 ^ (2 / q.toReal) / Real.log 2) * eLpNorm f q μ ^ (2 : ℝ) := by
  have hqtop : q ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofNat_ne_top hq2
  have hq : 0 < q.toReal := ENNReal.toReal_pos hq0 hqtop
  have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
  -- The Lorentz gauge `‖f‖_{q,2}` is at most `‖f‖_q`.
  have hlor : eLpNorm (fun t ↦ ENNReal.ofReal (t ^ q.toReal⁻¹) *
      μ.decreasingRearrangement (fun x ↦ ‖f x‖ₑ) t) 2 multHaar ≤ eLpNorm f q μ := by
    have h := eLorentzNorm_le_of_exponent_le (f := f) (μ := μ) hq0 hqtop hq0 hq2
    rw [eLorentzNorm_self, div_self hq.ne', Real.one_rpow, ENNReal.ofReal_one, one_mul,
      eLorentzNorm_eq_eLpNorm hf hq0] at h
    simpa [ENNReal.toReal_inv] using h
  rw [tsum_congr fun k ↦ ofReal_two_zpow_rpow_mul_rpow_two hq k
    (μ.decreasingRearrangement (fun x ↦ ‖f x‖ₑ) ((2 : ℝ) ^ k)), ENNReal.tsum_mul_left]
  calc _ ≤ ENNReal.ofReal (2 ^ (2 / q.toReal)) * ((ENNReal.ofReal (Real.log 2))⁻¹ *
        eLpNorm (fun t ↦ ENNReal.ofReal (t ^ q.toReal⁻¹) *
          μ.decreasingRearrangement (fun x ↦ ‖f x‖ₑ) t) 2 multHaar ^ (2 : ℝ)) := by
        gcongr
        rw [← ENNReal.div_eq_inv_mul, ENNReal.le_div_iff_mul_le (Or.inl (by simpa using hlog))
          (Or.inl ENNReal.ofReal_ne_top), mul_comm]
        exact ofReal_log_two_mul_tsum_le_eLpNorm_multHaar hq
    _ ≤ ENNReal.ofReal (2 ^ (2 / q.toReal)) *
          ((ENNReal.ofReal (Real.log 2))⁻¹ * eLpNorm f q μ ^ (2 : ℝ)) := by
        gcongr
    _ = _ := by
        rw [← mul_assoc, ← ENNReal.ofReal_inv_of_pos hlog, ← ENNReal.ofReal_mul (by positivity),
          ← div_eq_mul_inv]

end TauCeti
