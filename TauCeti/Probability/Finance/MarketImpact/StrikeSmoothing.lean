/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Convex.Function
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Convex.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import TauCeti.MeasureTheory.Function.LocallyIntegrable
import TauCeti.MeasureTheory.Integral.Bochner.Cumulative
import TauCeti.MeasureTheory.Integral.IntervalIntegral.Primitive

/-!
# Call payoffs smoothed over the strike

A basket of calls whose strikes are spread with a density `ζ` over `(0, ∞)` pays

`h(x) = ∫_{K > 0} (x - K)⁺ ζ(K) dK`

at spot `x` (`TauCeti.Finance.strikeSmoothedCallPayoff`). Spreading the strike replaces the kink
of a single call payoff by a payoff whose second derivative is the strike density, which is what
makes these payoffs admissible terminal data for pricing equations that need smooth payoffs, such
as the nonlinear pricing equation of market clearing with program trading.

Only strikes below the spot contribute, so `h(x) = ∫_{0 < K ≤ x} (x - K) ζ(K) dK`
(`TauCeti.Finance.strikeSmoothedCallPayoff_eq_setIntegral`). In particular `h` vanishes at and
below zero, and beyond the strike support it is the affine function `x ∫ ζ - ∫ K ζ(K) dK` of the
mass and the first moment of `ζ`
(`TauCeti.Finance.strikeSmoothedCallPayoff_eq_mul_integral_Ioi_sub`).

Where `ζ` is integrable on `(0, x]`, `h(x)` is the second primitive `∫₀ˣ F` of `ζ`, where
`F(u) = ∫_{0 < K ≤ u} ζ(K) dK` is the payoff of the same mixture of digital options
(`TauCeti.Finance.strikeSmoothedCallPayoff_eq_intervalIntegral`). Assume only that `ζ` is locally
integrable on `[0, ∞)`; it may take either sign. Then:

* `h` is differentiable everywhere, with delta `h'(x) = F(x)`
  (`TauCeti.Finance.hasDerivAt_strikeSmoothedCallPayoff`);
* at every positive spot where `ζ` is continuous, the gamma is the strike density,
  `h''(x) = ζ(x)` (`TauCeti.Finance.deriv_deriv_strikeSmoothedCallPayoff`);
* a density that is almost everywhere nonnegative on `(0, ∞)` gives a convex payoff
  (`TauCeti.Finance.convexOn_strikeSmoothedCallPayoff`).

The payoff is linear in the strike density: it commutes with scaling and negation of `ζ`
(`TauCeti.Finance.strikeSmoothedCallPayoff_smul`, `TauCeti.Finance.strikeSmoothedCallPayoff_neg`),
and at spot `x` it is additive in densities integrable on `(0, x]`
(`TauCeti.Finance.strikeSmoothedCallPayoff_add`). Without nonnegativity the payoff therefore need
not be convex: negating `ζ` negates `h`.

## References

* R. Sircar, G. Papanicolaou, *General Black–Scholes models accounting for increased market
  volatility from hedging strategies*, Applied Mathematical Finance 5 (1998), 45–82, §2.7.2.
-/

public section

noncomputable section

open MeasureTheory Set
open scoped Topology

namespace TauCeti.Finance

variable {ζ : ℝ → ℝ} {x : ℝ}

/-- The payoff `h(x) = ∫_{K > 0} (x - K)⁺ ζ(K) dK` at spot `x` of a basket of calls whose strikes
are spread over `(0, ∞)` with density `ζ`. -/
def strikeSmoothedCallPayoff (ζ : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ K in Ioi 0, (x - K)⁺ * ζ K

/-- Unfold the strike-smoothed call payoff. -/
theorem strikeSmoothedCallPayoff_def (ζ : ℝ → ℝ) (x : ℝ) :
    strikeSmoothedCallPayoff ζ x = ∫ K in Ioi 0, (x - K)⁺ * ζ K :=
  (rfl)

/-- The zero strike density gives the zero payoff. -/
@[simp]
theorem strikeSmoothedCallPayoff_zero_left : strikeSmoothedCallPayoff 0 = 0 := by
  ext x
  simp [strikeSmoothedCallPayoff_def]

/-- Scaling the strike density scales the strike-smoothed call payoff. -/
@[simp]
theorem strikeSmoothedCallPayoff_smul (c : ℝ) (ζ : ℝ → ℝ) :
    strikeSmoothedCallPayoff (c • ζ) = c • strikeSmoothedCallPayoff ζ := by
  ext x
  simp only [strikeSmoothedCallPayoff_def, Pi.smul_apply, smul_eq_mul, ← integral_const_mul]
  exact integral_congr_ae (Filter.Eventually.of_forall fun K => mul_left_comm _ _ _)

/-- Negating the strike density negates the strike-smoothed call payoff. -/
@[simp]
theorem strikeSmoothedCallPayoff_neg (ζ : ℝ → ℝ) :
    strikeSmoothedCallPayoff (-ζ) = -strikeSmoothedCallPayoff ζ := by
  ext x
  simp [strikeSmoothedCallPayoff_def, integral_neg]

/-- Only the strikes `0 < K ≤ x` contribute to the strike-smoothed call payoff at spot `x`. -/
theorem strikeSmoothedCallPayoff_eq_setIntegral (ζ : ℝ → ℝ) (x : ℝ) :
    strikeSmoothedCallPayoff ζ x = ∫ K in Ioc 0 x, (x - K) * ζ K := by
  rw [strikeSmoothedCallPayoff_def,
    setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi Ioc_subset_Ioi_self]
  · refine setIntegral_congr_fun measurableSet_Ioc fun K hK => ?_
    rw [posPart_eq_self.2 (sub_nonneg.2 hK.2)]
  · intro K hK
    have hxK : x < K := not_le.1 fun h => hK.2 ⟨hK.1, h⟩
    rw [posPart_eq_zero.2 (sub_nonpos.2 hxK.le), zero_mul]

/-- The strike-smoothed call payoff at spot `x` is additive in strike densities that are
integrable on `(0, x]`. -/
theorem strikeSmoothedCallPayoff_add {ζ₁ ζ₂ : ℝ → ℝ} (hζ₁ : IntegrableOn ζ₁ (Ioc 0 x))
    (hζ₂ : IntegrableOn ζ₂ (Ioc 0 x)) :
    strikeSmoothedCallPayoff (ζ₁ + ζ₂) x =
      strikeSmoothedCallPayoff ζ₁ x + strikeSmoothedCallPayoff ζ₂ x := by
  have hint (f : ℝ → ℝ) (hf : IntegrableOn f (Ioc 0 x)) :
      IntegrableOn (fun K => (x - K) * f K) (Ioc 0 x) :=
    (((integrableOn_Icc_iff_integrableOn_Ioc).2 hf).continuousOn_mul
      (continuous_const.sub continuous_id).continuousOn isCompact_Icc).mono_set
      Ioc_subset_Icc_self
  simp only [strikeSmoothedCallPayoff_eq_setIntegral, Pi.add_apply, mul_add]
  exact integral_add (hint ζ₁ hζ₁) (hint ζ₂ hζ₂)

/-- The strike-smoothed call payoff vanishes at and below zero spot. -/
theorem strikeSmoothedCallPayoff_of_nonpos (hx : x ≤ 0) : strikeSmoothedCallPayoff ζ x = 0 := by
  rw [strikeSmoothedCallPayoff_eq_setIntegral, Ioc_eq_empty (not_lt.2 hx),
    Measure.restrict_empty, integral_zero_measure]

/-- The strike-smoothed call payoff at spot `x` is `x` times the strike mass below `x` minus the
first strike moment below `x`. -/
theorem strikeSmoothedCallPayoff_eq_mul_integral_Ioc_sub (hζ : IntegrableOn ζ (Ioc 0 x)) :
    strikeSmoothedCallPayoff ζ x = x * (∫ K in Ioc 0 x, ζ K) - ∫ K in Ioc 0 x, K * ζ K := by
  have hKζ : IntegrableOn (fun K => K * ζ K) (Ioc 0 x) :=
    (((integrableOn_Icc_iff_integrableOn_Ioc).2 hζ).continuousOn_mul continuousOn_id
      isCompact_Icc).mono_set Ioc_subset_Icc_self
  rw [strikeSmoothedCallPayoff_eq_setIntegral, ← integral_const_mul,
    ← integral_sub (hζ.const_mul x) hKζ]
  exact setIntegral_congr_fun measurableSet_Ioc fun K _ => by ring

/-- **Beyond the strike support** the strike-smoothed call payoff is affine: if the strike density
vanishes above `x`, the payoff at `x` is `x` times the strike mass minus the first strike
moment. -/
theorem strikeSmoothedCallPayoff_eq_mul_integral_Ioi_sub (hζ : IntegrableOn ζ (Ioc 0 x))
    (hζx : EqOn ζ 0 (Ioi x)) :
    strikeSmoothedCallPayoff ζ x = x * (∫ K in Ioi 0, ζ K) - ∫ K in Ioi 0, K * ζ K := by
  have hIoi (f : ℝ → ℝ) (hf : ∀ K, ζ K = 0 → f K = 0) :
      ∫ K in Ioi 0, f K = ∫ K in Ioc 0 x, f K :=
    setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi Ioc_subset_Ioi_self
      fun K hK => hf K (hζx (not_le.1 fun h => hK.2 ⟨hK.1, h⟩))
  rw [hIoi ζ fun _ h => h, hIoi _ fun K h => by rw [h, mul_zero],
    strikeSmoothedCallPayoff_eq_mul_integral_Ioc_sub hζ]

/-- The strike-smoothed call payoff is the second primitive of the strike density: it is the
integral from `0` to `x` of the payoff `u ↦ ∫_{0 < K ≤ u} ζ(K) dK` of the same mixture of
digital options. -/
theorem strikeSmoothedCallPayoff_eq_intervalIntegral (hζ : IntegrableOn ζ (Ioc 0 x)) :
    strikeSmoothedCallPayoff ζ x = ∫ u in 0..x, ∫ K in Ioc 0 u, ζ K := by
  rcases le_or_gt x 0 with hx | hx
  · rw [strikeSmoothedCallPayoff_of_nonpos hx, intervalIntegral.integral_of_ge hx,
      eq_comm, neg_eq_zero]
    refine setIntegral_eq_zero_of_forall_eq_zero fun u hu => ?_
    rw [Ioc_eq_empty (not_lt.2 hu.2), Measure.restrict_empty, integral_zero_measure]
  -- Integrate by parts against the primitive of `ζ`, with the weight `φ(u) = u`.
  have hparts := TauCeti.intervalIntegral.integral_deriv_smul_primitive_eq_sub_of_le (𝕜 := ℝ)
    (φ := id) hx.le contDiff_id
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hx.le).2 hζ)
  simp only [deriv_id, id_eq, smul_eq_mul, one_mul] at hparts
  rw [strikeSmoothedCallPayoff_eq_mul_integral_Ioc_sub hζ,
    ← intervalIntegral.integral_of_le hx.le, ← intervalIntegral.integral_of_le hx.le, ← hparts]
  refine intervalIntegral.integral_congr fun u hu => ?_
  rw [uIcc_of_le hx.le] at hu
  exact intervalIntegral.integral_of_le hu.1

/-- The **delta** of the strike-smoothed call payoff at any spot `x` is the payoff
`∫_{0 < K ≤ x} ζ(K) dK` of the same mixture of digital options. -/
theorem hasDerivAt_strikeSmoothedCallPayoff (hζ : LocallyIntegrableOn ζ (Ici 0)) (x : ℝ) :
    HasDerivAt (strikeSmoothedCallPayoff ζ) (∫ K in Ioc 0 x, ζ K) x := by
  have h : strikeSmoothedCallPayoff ζ = fun y => ∫ u in 0..y, ∫ K in Ioc 0 u, ζ K :=
    funext fun y => strikeSmoothedCallPayoff_eq_intervalIntegral (hζ.integrableOn_Ioc_of_Ici y)
  rw [h]
  exact ((continuous_integral_Ioc hζ.integrableOn_Ioc_of_Ici).integral_hasStrictDerivAt 0
    x).hasDerivAt

/-- The strike-smoothed call payoff of a locally integrable strike density is differentiable. -/
theorem differentiable_strikeSmoothedCallPayoff (hζ : LocallyIntegrableOn ζ (Ici 0)) :
    Differentiable ℝ (strikeSmoothedCallPayoff ζ) :=
  fun x => (hasDerivAt_strikeSmoothedCallPayoff hζ x).differentiableAt

/-- The delta of the strike-smoothed call payoff is the digital-mixture payoff
`x ↦ ∫_{0 < K ≤ x} ζ(K) dK`. -/
theorem deriv_strikeSmoothedCallPayoff (hζ : LocallyIntegrableOn ζ (Ici 0)) :
    deriv (strikeSmoothedCallPayoff ζ) = fun x => ∫ K in Ioc 0 x, ζ K :=
  funext fun x => (hasDerivAt_strikeSmoothedCallPayoff hζ x).deriv

/-- At a positive spot where the strike density is continuous, the delta of the strike-smoothed
call payoff has derivative the strike density there. -/
theorem hasDerivAt_deriv_strikeSmoothedCallPayoff (hζ : LocallyIntegrableOn ζ (Ici 0))
    (hx : 0 < x) (hζx : ContinuousAt ζ x) :
    HasDerivAt (deriv (strikeSmoothedCallPayoff ζ)) (ζ x) x := by
  rw [deriv_strikeSmoothedCallPayoff hζ]
  have hnear : (fun u => ∫ K in Ioc 0 u, ζ K) =ᶠ[𝓝 x] fun u => ∫ K in 0..u, ζ K :=
    Filter.eventually_of_mem (Ioi_mem_nhds hx) fun u hu =>
      (intervalIntegral.integral_of_le (le_of_lt hu)).symm
  have hmeas : StronglyMeasurableAtFilter ζ (𝓝 x) :=
    ⟨Ioo 0 (x + 1), Ioo_mem_nhds hx (by linarith),
      ((hζ.integrableOn_Ioc_of_Ici (x + 1)).mono_set Ioo_subset_Ioc_self).aestronglyMeasurable⟩
  exact (intervalIntegral.integral_hasDerivAt_right
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hx.le).2 (hζ.integrableOn_Ioc_of_Ici x))
    hmeas hζx).congr_of_eventuallyEq hnear

/-- The **gamma** of the strike-smoothed call payoff is the strike density: at every positive spot
where `ζ` is continuous, `h''(x) = ζ(x)`. -/
theorem deriv_deriv_strikeSmoothedCallPayoff (hζ : LocallyIntegrableOn ζ (Ici 0)) (hx : 0 < x)
    (hζx : ContinuousAt ζ x) : deriv (deriv (strikeSmoothedCallPayoff ζ)) x = ζ x :=
  (hasDerivAt_deriv_strikeSmoothedCallPayoff hζ hx hζx).deriv

/-- A strike density that is almost everywhere nonnegative on `(0, ∞)` gives a convex
strike-smoothed call payoff. -/
theorem convexOn_strikeSmoothedCallPayoff (hζ : LocallyIntegrableOn ζ (Ici 0))
    (hζ0 : 0 ≤ᵐ[volume.restrict (Ioi 0)] ζ) :
    ConvexOn ℝ univ (strikeSmoothedCallPayoff ζ) := by
  refine Monotone.convexOn_univ_of_deriv (differentiable_strikeSmoothedCallPayoff hζ) ?_
  rw [deriv_strikeSmoothedCallPayoff hζ]
  intro u v huv
  refine setIntegral_mono_set (hζ.integrableOn_Ioc_of_Ici v)
    (ae_restrict_of_ae_restrict_of_subset Ioc_subset_Ioi_self hζ0)
    (Filter.Eventually.of_forall fun K hK => ⟨hK.1, hK.2.trans huv⟩)

end TauCeti.Finance
