/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.BrownianMotion.GridExponential.Basic
public import TauCeti.Probability.BrownianMotion.Integral.Energy.Congruence
public import TauCeti.Probability.Finance.SimpleStrategy.Congruence

/-!
# Grid-independent elementary exponential densities

An elementary normalized exponential is the exponential of the elementary gain minus
half its square energy. Both terms depend only on the time-a.e. holding process, not on
its finite-grid presentation. Thus refining a grid or changing heights on empty intervals
leaves its likelihood unchanged. The two grids may even have different terminal dates:
zero holdings beyond the last active interval make that distinction immaterial.

The congruence is pathwise for an arbitrary driving path, and time-product-a.e. equality
of holdings gives sample-a.e. equality of likelihoods. Neither Brownian laws nor bounded
heights are needed. These results allow elementary predictable approximations to be
compared on common refinements without changing the densities being approximated.

## References

* I. Karatzas, S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, §3.5.
-/

public section

open MeasureTheory Real Finset Set TauCeti.Finance
open scoped NNReal

namespace TauCeti.Probability

variable {Ω : Type*} {τ ρ : ℕ → ℝ≥0} {a b : ℕ → Ω → ℝ} {n m : ℕ}
  {W : ℝ≥0 → Ω → ℝ}

/-- A grid likelihood is the exponential of its terminal elementary gain minus half its
pathwise square energy. -/
theorem gridExponential_eq_exp_simpleGains_sub_energy
    (hτ : MonotoneOn τ (Set.Iic n)) (ω : Ω) :
    gridExponential τ a W n ω =
      exp (simpleGains τ n a W (τ n) ω - elementaryEnergy τ a n ω / 2) := by
  rw [gridExponential_def, simpleGains_apply_eq_sum hτ le_rfl, elementaryEnergy_def,
    sum_sub_distrib, sum_div]

/-- Time-a.e. equality of elementary holdings preserves the normalized exponential,
for different grids and an arbitrary driving path. -/
theorem gridExponential_congr_of_ae_eq (hτ : MonotoneOn τ (Set.Iic n))
    (hρ : MonotoneOn ρ (Set.Iic m)) (ω : Ω)
    (hab : (fun t ↦ simpleHolding τ n a t ω) =ᵐ[TauCeti.nnvolume]
      (fun t ↦ simpleHolding ρ m b t ω)) :
    gridExponential τ a W n ω = gridExponential ρ b W m ω := by
  have hg := simpleGains_congr_of_ae_eq_nnvolume (X := W) hτ hρ ω hab (max (τ n) (ρ m))
  rw [simpleGains_of_ge hτ (le_max_left _ _),
    simpleGains_of_ge hρ (le_max_right _ _)] at hg
  rw [gridExponential_eq_exp_simpleGains_sub_energy hτ,
    gridExponential_eq_exp_simpleGains_sub_energy hρ, hg,
    elementaryEnergy_congr_of_ae_eq hτ hρ ω hab]

/-- Equality for time-product measure gives equality of the elementary likelihoods outside
one sample-null set, for any driving process. -/
theorem gridExponential_congr_of_ae_eq_prod {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    [SFinite P] (hτ : MonotoneOn τ (Set.Iic n)) (hρ : MonotoneOn ρ (Set.Iic m))
    (hab : Function.uncurry (simpleHolding τ n a) =ᵐ[TauCeti.nnvolume.prod P]
      Function.uncurry (simpleHolding ρ m b)) :
    gridExponential τ a W n =ᵐ[P] gridExponential ρ b W m := by
  have hswap := Measure.ae_ae_of_ae_prod
    (Measure.measurePreserving_swap.quasiMeasurePreserving.ae hab)
  exact hswap.mono fun ω hω ↦ gridExponential_congr_of_ae_eq hτ hρ ω hω

end TauCeti.Probability
