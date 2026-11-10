/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Finance.SimpleStrategy.Basic
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Representation independence of elementary trading gains

The elementary integral depends on the holding process, not on its finite-grid
presentation. In fact, equality Lebesgue-almost everywhere in time suffices, path by
path, for equality of the gains against **any** price path. Different grids, repeated
dates and empty strategies are allowed. No continuity, variation, measurability or
moment hypothesis on the price is needed.

`simpleGains_congr_on_horizon_of_ae_eq` is the finite-horizon statement.
`simpleGains_congr_of_ae_eq` gives equality at all times from time-a.e. equality on the whole
line. The product-measure forms turn time-product-a.e. equality into equality
of the gain processes outside one common sample-null set, either on a finite horizon
or at all times. Thus elementary gains
respect the equivalence of integrands used in stochastic-integral completion.

The proof interpolates the finitely many sampled price values by a polynomial using
Mathlib's `Lagrange.interpolate`. The existing `simpleGains_eq_integral` then reduces
representation independence to congruence of ordinary Lebesgue integrals. The
interpolating polynomial is only a proof device; the actual price need not be smooth.

## References

* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second
  edition, §3.2, for elementary predictable integrands and their integrals.
-/

public section
noncomputable section

open MeasureTheory Finset Set

namespace TauCeti.Finance

variable {Ω : Type*} {τ ρ : ℕ → ℝ} {n m : ℕ}
  {a b : ℕ → Ω → ℝ} {X Y : ℝ → Ω → ℝ}

private theorem simpleGains_polynomial_eq_integral (p : Polynomial ℝ) {c t : ℝ}
    (hτ : MonotoneOn τ (Set.Iic n)) (hc : c ≤ τ 0) (ω : Ω) :
    simpleGains τ n a (fun x _ ↦ p.eval x) t ω =
      ∫ u in c..t, simpleHolding τ n a u ω * p.derivative.eval u := by
  apply simpleGains_eq_integral hτ hc ω
  · exact p.derivative.differentiable.continuous.integrableOn_Icc
  · intro x _
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun y _ ↦ p.hasDerivAt y) (p.derivative.differentiable.continuous.intervalIntegrable _ _)]
    ring

/-- Equal holdings almost everywhere on the trading horizon give equal elementary gains,
even with different grids and an arbitrary price path. The lower endpoint precedes both
strategies; the upper endpoint is the time at which gains are compared. -/
theorem simpleGains_congr_on_horizon_of_ae_eq {c t : ℝ}
    (hτ : MonotoneOn τ (Set.Iic n)) (hρ : MonotoneOn ρ (Set.Iic m))
    (hcτ : c ≤ τ 0) (hcρ : c ≤ ρ 0) (ω : Ω)
    (hab : (fun u ↦ simpleHolding τ n a u ω) =ᵐ[volume.restrict (Ioc c t)]
      (fun u ↦ simpleHolding ρ m b u ω)) :
    simpleGains τ n a X t ω = simpleGains ρ m b X t ω := by
  rcases lt_or_ge t c with htc | hct
  · rw [simpleGains_of_le hτ (htc.le.trans hcτ), simpleGains_of_le hρ (htc.le.trans hcρ)]
  let nodes := (range (n + 1)).image (fun j ↦ min (τ j) t) ∪
    (range (m + 1)).image (fun j ↦ min (ρ j) t)
  let p : Polynomial ℝ := Lagrange.interpolate nodes id (fun x ↦ X x ω)
  have hp (x : ℝ) (hx : x ∈ nodes) : p.eval x = X x ω :=
    Lagrange.eval_interpolate_at_node _ (fun _ _ _ _ h ↦ h) hx
  have hτp : simpleGains τ n a X t ω =
      simpleGains τ n a (fun x _ ↦ p.eval x) t ω :=
    simpleGains_congr_price ω fun j hj ↦ (hp _ (mem_union_left _
      (mem_image.mpr ⟨j, mem_range.mpr (by omega), rfl⟩))).symm
  have hρp : simpleGains ρ m b X t ω =
      simpleGains ρ m b (fun x _ ↦ p.eval x) t ω :=
    simpleGains_congr_price ω fun j hj ↦ (hp _ (mem_union_right _
      (mem_image.mpr ⟨j, mem_range.mpr (by omega), rfl⟩))).symm
  rw [hτp, hρp, simpleGains_polynomial_eq_integral p hτ hcτ,
    simpleGains_polynomial_eq_integral p hρ hcρ]
  apply intervalIntegral.integral_congr_ae_restrict
  rw [uIoc_of_le hct]
  exact hab.mono fun u hu ↦ congrArg (· * p.derivative.eval u) hu

/-- Time-a.e. equal simple holdings have identical gains at every time, against any price.
The exceptional time set can depend on the fixed sample `ω`. -/
theorem simpleGains_congr_of_ae_eq (hτ : MonotoneOn τ (Set.Iic n))
    (hρ : MonotoneOn ρ (Set.Iic m))
    (ω : Ω) (hab : (fun u ↦ simpleHolding τ n a u ω) =ᵐ[volume]
      (fun u ↦ simpleHolding ρ m b u ω)) (t : ℝ) :
    simpleGains τ n a X t ω = simpleGains ρ m b X t ω := by
  exact simpleGains_congr_on_horizon_of_ae_eq hτ hρ
    (min_le_left (τ 0) (ρ 0)) (min_le_right (τ 0) (ρ 0)) ω (ae_restrict_of_ae hab)

/-- Equality for time-product measure on a finite horizon gives equality of gains throughout
that horizon on one common sample-full event, not merely at each deterministic time. -/
theorem simpleGains_congr_on_horizon_of_ae_eq_prod
    {mΩ : MeasurableSpace Ω} {P : Measure Ω} [SFinite P] {c T : ℝ}
    (hτ : MonotoneOn τ (Set.Iic n)) (hρ : MonotoneOn ρ (Set.Iic m))
    (hcτ : c ≤ τ 0) (hcρ : c ≤ ρ 0)
    (hab : Function.uncurry (simpleHolding τ n a)
      =ᵐ[(volume.restrict (Ioc c T)).prod P] Function.uncurry (simpleHolding ρ m b)) :
    ∀ᵐ ω ∂P, ∀ t ∈ Icc c T, simpleGains τ n a X t ω = simpleGains ρ m b X t ω := by
  have hswap := Measure.ae_ae_of_ae_prod
    (Measure.measurePreserving_swap.quasiMeasurePreserving.ae hab)
  filter_upwards [hswap] with ω hω
  intro t ht
  exact simpleGains_congr_on_horizon_of_ae_eq hτ hρ hcτ hcρ ω
    (ae_restrict_of_ae_restrict_of_subset (Ioc_subset_Ioc_right ht.2) hω)

/-- Time-product-a.e. equal simple holdings give gains equal simultaneously at every time
outside one sample-null set. This is stronger than equality at each fixed time and does
not require continuous price paths or a complete filtration. -/
theorem simpleGains_congr_of_ae_eq_prod {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    [SFinite P] (hτ : MonotoneOn τ (Set.Iic n)) (hρ : MonotoneOn ρ (Set.Iic m))
    (hab : Function.uncurry (simpleHolding τ n a) =ᵐ[volume.prod P]
      Function.uncurry (simpleHolding ρ m b)) :
    ∀ᵐ ω ∂P, ∀ t, simpleGains τ n a X t ω = simpleGains ρ m b X t ω := by
  have hswap := Measure.ae_ae_of_ae_prod
    (Measure.measurePreserving_swap.quasiMeasurePreserving.ae hab)
  exact hswap.mono fun ω hω t ↦ simpleGains_congr_of_ae_eq hτ hρ ω hω t

end TauCeti.Finance
