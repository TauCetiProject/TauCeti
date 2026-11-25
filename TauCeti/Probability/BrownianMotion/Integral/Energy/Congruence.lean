/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.BrownianMotion.Integral.Energy.Bound
public import TauCeti.Probability.Finance.SimpleStrategy.Energy
public import TauCeti.MeasureTheory.Measure.NNReal
import TauCeti.Analysis.Normed.Group.Real

/-!
# Representation independence of elementary square energy

The finite sum `elementaryEnergy` is the actual lower square-energy integral of its
holding on the nonnegative half-line. Consequently it depends only on the time-a.e.
class of the holding, even when the two presentations have different grids and terminal
dates. This is the energy congruence used to compare elementary exponential densities
before taking limits. No Brownian, filtration or moment hypotheses are needed.

## References

* I. Karatzas, S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, §§3.2 and 3.5.
-/

public section

open MeasureTheory Finset Set TauCeti.Finance
open scoped ENNReal NNReal

namespace TauCeti.Probability

variable {Ω : Type*} {τ ρ : ℕ → ℝ≥0} {a b : ℕ → Ω → ℝ} {n m : ℕ}

/-- Elementary energy is the lower square-energy integral over the full time half-line.
In particular the lower integral is finite for every sample, without moment hypotheses. -/
theorem lintegral_enorm_sq_simpleHolding_nnvolume (hτ : MonotoneOn τ (Set.Iic n)) (ω : Ω) :
    ∫⁻ t, ‖simpleHolding τ n a t ω‖ₑ ^ 2 ∂TauCeti.nnvolume =
      ENNReal.ofReal (elementaryEnergy τ a n ω) := by
  rw [Measure.lintegral_enorm_sq_simpleHolding _ hτ (fun _ _ ↦ measurableSet_Ioc),
    elementaryEnergy_def, ENNReal.ofReal_sum_of_nonneg]
  · refine sum_congr rfl fun i _ ↦ ?_
    rw [TauCeti.nnvolume_apply, NNReal.image_coe_Ioc, Real.volume_Ioc,
      Real.enorm_sq_eq_ofReal_sq, ENNReal.ofReal_mul (sq_nonneg _)]
  · intro i hi
    exact mul_nonneg (sq_nonneg _) (sub_nonneg.mpr (NNReal.coe_le_coe.mpr
      (hτ (mem_range.mp hi).le (mem_range.mp hi) (Nat.le_succ i))))

/-- Time-a.e. equal elementary holdings have identical pathwise square energies,
independently of their grids. -/
theorem elementaryEnergy_congr_of_ae_eq (hτ : MonotoneOn τ (Set.Iic n))
    (hρ : MonotoneOn ρ (Set.Iic m)) (ω : Ω)
    (hab : (fun t ↦ simpleHolding τ n a t ω) =ᵐ[TauCeti.nnvolume]
      (fun t ↦ simpleHolding ρ m b t ω)) :
    elementaryEnergy τ a n ω = elementaryEnergy ρ b m ω := by
  have he : ENNReal.ofReal (elementaryEnergy τ a n ω) =
      ENNReal.ofReal (elementaryEnergy ρ b m ω) := by
    rw [← lintegral_enorm_sq_simpleHolding_nnvolume hτ,
      ← lintegral_enorm_sq_simpleHolding_nnvolume hρ]
    exact lintegral_congr_ae (hab.fun_comp fun x : ℝ ↦ ‖x‖ₑ ^ 2)
  simpa only [ENNReal.toReal_ofReal (elementaryEnergy_nonneg hτ ω),
    ENNReal.toReal_ofReal (elementaryEnergy_nonneg hρ ω)] using congrArg ENNReal.toReal he

/-- Time-product-a.e. equal elementary holdings have a.e. equal square energies.
No measurability or moment conditions on the heights are required for this implication. -/
theorem elementaryEnergy_congr_of_ae_eq_prod {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    [SFinite P] (hτ : MonotoneOn τ (Set.Iic n)) (hρ : MonotoneOn ρ (Set.Iic m))
    (hab : Function.uncurry (simpleHolding τ n a) =ᵐ[TauCeti.nnvolume.prod P]
      Function.uncurry (simpleHolding ρ m b)) :
    elementaryEnergy τ a n =ᵐ[P] elementaryEnergy ρ b m := by
  have hswap := Measure.ae_ae_of_ae_prod
    (Measure.measurePreserving_swap.quasiMeasurePreserving.ae hab)
  exact hswap.mono fun ω hω ↦ elementaryEnergy_congr_of_ae_eq hτ hρ ω hω

end TauCeti.Probability
