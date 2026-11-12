/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.BrownianMotion.PolynomialGrowth
public import TauCeti.Probability.Martingale.Local.SquareIntegrable

/-!
# Polynomial growth removes localization from candidate prices

Suppose a strongly adapted, right-continuous candidate value process is already a local
martingale, and its absolute value is bounded by `A (1 + S_(t ∧ T)^p)` for a positive
geometric Brownian stock. Then it is a true martingale and every value is square integrable.
The exponent may be any real number. Neither usual filtration conditions nor deterministic
Markov dependence of the candidate are required.

For a classical price of polynomial growth, apply the criterion to the discounted price,
stopped at maturity. The deterministic discount factor is bounded on the finite horizon and
can be absorbed into the growth constant. An Itô argument must first establish the local
martingale property; growth by itself does not imply it. Continuity at maturity is needed
when establishing the path regularity of this stopped extension. These results do not assert
self-financing or replication.

## References

* I. Karatzas and S. E. Shreve, *Methods of Mathematical Finance*, Springer, 1998, §2.4.
* S. E. Shreve, *Stochastic Calculus for Finance II*, Springer, 2004, §6.4.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real Set
open scoped NNReal ENNReal

namespace TauCeti.Probability.IsFilteredPreBrownianReal

variable {Ω : Type*} {m : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℝ≥0 m}
  {W X : ℝ≥0 → Ω → ℝ} {s A μ σ p : ℝ} {T : ℝ≥0}

/-- A strongly adapted, almost surely right-continuous local martingale with a uniform
polynomial bound in a positive geometric Brownian stock stopped at maturity is a true
martingale. Together with `memLp_two_of_geometricBrownianMotion_bound`, this verifies the
square-integrable true-martingale condition for a discounted candidate price once its local
Itô identity and terminal extension have been established. -/
theorem martingale_of_locally_martingale_of_geometricBrownianMotion_bound
    (hW : IsFilteredPreBrownianReal ℱ W P)
    (hcont : ∀ᵐ ω ∂P, ∀ t < T, ContinuousWithinAt (fun u ↦ W u ω) (Ioi t) t)
    (hs : 0 < s) (hX : StronglyAdapted ℱ X)
    (hlocal : Locally (fun Y ↦ Martingale Y ℱ P) ℱ X P)
    (hcontX : ∀ᵐ ω ∂P, ∀ t, ContinuousWithinAt (fun u ↦ X u ω) (Ioi t) t)
    (hbound : ∀ᵐ ω ∂P, ∀ t,
      |X t ω| ≤ A * (1 + geometricBrownianMotion s μ σ W (min t T) ω ^ p)) :
    Martingale X ℱ P := by
  have := (hW.hasLaw_eval 0).isProbabilityMeasure
  apply hX.martingale_of_locally_martingale_of_lintegral_iSup_norm_sq_lt_top hlocal
    (fun _ ↦ hcontX.mono fun ω hω t _ ↦ hω t)
  simpa only [Real.norm_eq_abs, sq_abs] using
    hW.lintegral_iSup_sq_lt_top_of_geometricBrownianMotion_bound hcont hs hbound

end TauCeti.Probability.IsFilteredPreBrownianReal
