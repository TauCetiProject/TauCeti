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
  obtain ⟨ns, -, hae⟩ := (tendstoInMeasure_of_tendsto_Lp hlim).exists_seq_tendsto_ae
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

/-! ### The dyadic levels -/

/-- The levels `f*(2ᵏ)` decrease with `k`. -/
private theorem toNNReal_decreasingRearrangement_zpow_le (hp0 : p ≠ 0) (g : Lp E p μ) {k l : ℤ}
    (hkl : k ≤ l) :
    (μ.decreasingRearrangement (fun x ↦ ‖g x‖ₑ) ((2 : ℝ) ^ l)).toNNReal ≤
      (μ.decreasingRearrangement (fun x ↦ ‖g x‖ₑ) ((2 : ℝ) ^ k)).toNNReal :=
  ENNReal.toNNReal_mono
    ((Lp.memLp g).decreasingRearrangement_lt_top hp0 (zpow_pos two_pos k)).ne
    (μ.antitone_decreasingRearrangement _ (zpow_le_zpow_right₀ one_le_two hkl))

/-- The level `f*(2ᵏ⁺¹)` is at most `f*(2ᵏ)`, as real numbers. -/
private theorem coe_toNNReal_decreasingRearrangement_succ_le (hp0 : p ≠ 0) (g : Lp E p μ)
    (k : ℤ) :
    ((μ.decreasingRearrangement (fun x ↦ ‖g x‖ₑ) ((2 : ℝ) ^ (k + 1))).toNNReal : ℝ) ≤
      (μ.decreasingRearrangement (fun x ↦ ‖g x‖ₑ) ((2 : ℝ) ^ k)).toNNReal :=
  NNReal.coe_le_coe.2 (toNNReal_decreasingRearrangement_zpow_le hp0 g (Int.le_add_one le_rfl))

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

/-- A difference of two radial retractions of `g` is, almost everywhere, the pointwise difference
of the radial retractions of the values of `g`. -/
theorem coeFn_radialRetraction_sub (a b : ℝ≥0) (g : Lp E p μ) :
    radialRetraction a g - radialRetraction b g =ᵐ[μ]
      fun x ↦ TauCeti.radialRetraction a (g x) - TauCeti.radialRetraction b (g x) := by
  filter_upwards [Lp.coeFn_sub (radialRetraction a g) (radialRetraction b g),
    coeFn_radialRetraction a g, coeFn_radialRetraction b g] with x h h1 h2
  rw [h, Pi.sub_apply, h1, h2]

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
          (μ.decreasingRearrangement (fun x ↦ ‖g x‖ₑ) ((2 : ℝ) ^ (k + 1))).toNNReal (g x) :=
  coeFn_radialRetraction_sub _ _ g

/-- The `k`-th dyadic layer of `g` is bounded by both `‖g‖` and `f*(2ᵏ)`. -/
theorem norm_dyadicLayer_le_min (hp0 : p ≠ 0) (k : ℤ) (g : Lp E p μ) :
    ∀ᵐ x ∂μ, ‖dyadicLayer k g x‖ ≤
      min ‖g x‖ (μ.decreasingRearrangement (fun x ↦ ‖g x‖ₑ) ((2 : ℝ) ^ k)).toNNReal := by
  filter_upwards [coeFn_dyadicLayer k g] with x hx
  rw [hx]
  exact TauCeti.norm_radialRetraction_sub_radialRetraction_le (NNReal.coe_nonneg _)
    (coe_toNNReal_decreasingRearrangement_succ_le hp0 g k) (g x)

/-- The `k`-th dyadic layer of `g` is bounded by `f*(2ᵏ)`. -/
theorem enorm_dyadicLayer_le (hp0 : p ≠ 0) (k : ℤ) (g : Lp E p μ) :
    ∀ᵐ x ∂μ, ‖dyadicLayer k g x‖ₑ ≤ μ.decreasingRearrangement (fun x ↦ ‖g x‖ₑ) ((2 : ℝ) ^ k) := by
  filter_upwards [norm_dyadicLayer_le_min hp0 k g] with x hx
  rw [← ofReal_norm]
  refine (ENNReal.ofReal_le_ofReal (hx.trans (min_le_right _ _))).trans ?_
  rw [ENNReal.ofReal_coe_nnreal]
  exact ENNReal.coe_toNNReal_le_self

/-- The `k`-th dyadic layer of `g` is bounded by `‖g‖`. -/
theorem enorm_dyadicLayer_le_enorm (hp0 : p ≠ 0) (k : ℤ) (g : Lp E p μ) :
    ∀ᵐ x ∂μ, ‖dyadicLayer k g x‖ₑ ≤ ‖g x‖ₑ := by
  filter_upwards [norm_dyadicLayer_le_min hp0 k g] with x hx
  exact eNorm_le_iff_norm_le.2 (hx.trans (min_le_left _ _))

/-- The `k`-th dyadic layer of `g` vanishes where `‖g‖ₑ ≤ f*(2ᵏ⁺¹)`. -/
theorem dyadicLayer_eq_zero_of_enorm_le (hp0 : p ≠ 0) (k : ℤ) (g : Lp E p μ) :
    ∀ᵐ x ∂μ, ‖g x‖ₑ ≤ μ.decreasingRearrangement (fun x ↦ ‖g x‖ₑ) ((2 : ℝ) ^ (k + 1)) →
      dyadicLayer k g x = 0 := by
  filter_upwards [coeFn_dyadicLayer k g] with x hx hle
  rw [← ofReal_norm, ← ENNReal.ofReal_toReal
    ((Lp.memLp g).decreasingRearrangement_lt_top hp0 (zpow_pos two_pos (k + 1))).ne] at hle
  have h : ‖g x‖ ≤
      (μ.decreasingRearrangement (fun x ↦ ‖g x‖ₑ) ((2 : ℝ) ^ (k + 1))).toNNReal :=
    (ENNReal.ofReal_le_ofReal_iff ENNReal.toReal_nonneg).1 hle
  rw [hx, TauCeti.radialRetraction_of_norm_le h, TauCeti.radialRetraction_of_norm_le
    (h.trans (coe_toNNReal_decreasingRearrangement_succ_le hp0 g k)), sub_self]

/-- **The size of a dyadic layer.** For every exponent `s`, the `k`-th dyadic layer of `g` has
`‖gₖ‖_s ≤ (2ᵏ⁺¹) ^ (1 / s) f*(2ᵏ)`: it is bounded by `f*(2ᵏ)` and supported in the set
`{f*(2ᵏ⁺¹) < ‖g‖}`, of measure at most `2ᵏ⁺¹`. -/
theorem eLpNorm_dyadicLayer_le (hp0 : p ≠ 0) (k : ℤ) (g : Lp E p μ) (s : ℝ≥0∞) :
    eLpNorm (dyadicLayer k g) s μ ≤
      ENNReal.ofReal ((2 : ℝ) ^ (k + 1)) ^ s.toReal⁻¹ *
        μ.decreasingRearrangement (fun x ↦ ‖g x‖ₑ) ((2 : ℝ) ^ k) := by
  set a := μ.decreasingRearrangement (fun x ↦ ‖g x‖ₑ) ((2 : ℝ) ^ k)
  set S := {x | μ.decreasingRearrangement (fun x ↦ ‖g x‖ₑ) ((2 : ℝ) ^ (k + 1)) < ‖g x‖ₑ}
  have hS : MeasurableSet S :=
    measurableSet_lt measurable_const (Lp.stronglyMeasurable g).eNorm
  have hind : (dyadicLayer k g : X → E) =ᵐ[μ] S.indicator (dyadicLayer k g) := by
    filter_upwards [dyadicLayer_eq_zero_of_enorm_le hp0 k g] with x hx
    by_cases hxS : x ∈ S
    · rw [indicator_of_mem hxS]
    · rw [indicator_of_notMem hxS, hx (not_lt.1 hxS)]
  have ha : a ≠ ∞ := ((Lp.memLp g).decreasingRearrangement_lt_top hp0 (zpow_pos two_pos k)).ne
  rw [eLpNorm_congr_ae hind, eLpNorm_indicator_eq_eLpNorm_restrict hS.nullMeasurableSet]
  refine (eLpNorm_le_of_ae_bound (C := a.toReal) (Lp.aestronglyMeasurable _).restrict
    (ae_restrict_of_ae ((enorm_dyadicLayer_le hp0 k g).mono fun x hx ↦ ?_))).trans ?_
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
  rw [Finset.sum_congr rfl fun i _ ↦ by rw [dyadicLayer_def,
      show (i : ℤ) - N + 1 = ((i + 1 : ℕ) : ℤ) - N by push_cast; ring],
    Finset.sum_range_sub' (fun i : ℕ ↦ radialRetraction
      (μ.decreasingRearrangement (fun x ↦ ‖g x‖ₑ) ((2 : ℝ) ^ ((i : ℤ) - N))).toNNReal g)]
  push_cast
  ring_nf

/-- The partial sums of the dyadic layers of `g` have norm at most `‖g‖`. -/
theorem norm_sum_range_dyadicLayer_le (hp0 : p ≠ 0) (N : ℕ) (g : Lp E p μ) :
    ‖∑ i ∈ Finset.range (2 * N), dyadicLayer ((i : ℤ) - N) g‖ ≤ ‖g‖ := by
  rw [sum_range_dyadicLayer]
  refine Lp.norm_le_norm_of_ae_le ?_
  filter_upwards [coeFn_radialRetraction_sub _ _ g] with x h
  rw [h]
  exact (TauCeti.norm_radialRetraction_sub_radialRetraction_le (NNReal.coe_nonneg _)
    (NNReal.coe_le_coe.2 (toNNReal_decreasingRearrangement_zpow_le hp0 g
      (by omega : -(N : ℤ) ≤ N))) (g x)).trans (min_le_left _ _)

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
    have h := hmin.radialRetraction (Eventually.of_forall fun _ ↦ ENNReal.toReal_nonneg)
      (tendsto_const_nhds (x := v))
    rw [TauCeti.radialRetraction_of_norm_le le_rfl] at h
    refine h.congr fun N ↦ ?_
    rw [ENNReal.toReal_min (hfin N) eNorm_ne_top, toReal_eNorm, TauCeti.radialRetraction_min_norm,
      ENNReal.coe_toNNReal_eq_toReal]
  have hlower : Tendsto (fun N ↦ TauCeti.radialRetraction (lo N) v) atTop (𝓝 0) := by
    have h := hlo.radialRetraction (Eventually.of_forall fun N ↦ NNReal.coe_nonneg _)
      (tendsto_const_nhds (x := v))
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
    have h := ((Lp.memLp g).tendsto_decreasingRearrangement_atTop_nhds_zero hp0 hp).comp
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
    exact fun N ↦ coeFn_radialRetraction_sub _ _ g
  -- Dominated convergence, with the bound `3 ‖g‖`.
  refine TauCeti.tendsto_eLpNorm_sub_of_ae_tendsto (C := 3) hp
    (Eventually.of_forall fun N ↦ Lp.aestronglyMeasurable _) (Lp.memLp g)
    (Eventually.of_forall fun N ↦ hcoe.mono fun x hx ↦ ?_) ?_
  · rw [hx N, ← ofReal_norm, ← ofReal_norm, ENNReal.coe_ofNat, ← ENNReal.ofReal_ofNat 3,
      ← ENNReal.ofReal_mul (by norm_num)]
    exact ENNReal.ofReal_le_ofReal (norm_radialRetraction_sub_radialRetraction_sub_le _ _ _)
  · filter_upwards [hcoe, ae_le_essSup (f := f)] with x hx hle
    exact (tendsto_radialRetraction_sub_radialRetraction (g x)
      (fun N ↦ ((Lp.memLp g).decreasingRearrangement_lt_top hp0 (zpow_pos two_pos _)).ne)
      hhi hle hlo).congr fun N ↦ (hx N).symm

end Lp

end MeasureTheory
