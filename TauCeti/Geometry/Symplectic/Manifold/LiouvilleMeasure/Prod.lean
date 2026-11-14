/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Measure.Prod
public import TauCeti.Geometry.Symplectic.Manifold.LiouvilleMeasure.Basic

/-!
# The Liouville measure of a product

Let `σ` be a two-form on a manifold `M` of dimension `2 n` and `τ` a two-form on a manifold `N` of
dimension `2 m`. The Liouville measure of the product form `σ ⊕ τ = pr₁^* σ + pr₂^* τ` on `M × N`
is the product of the Liouville measures of the factors:

`|(σ ⊕ τ)ⁿ⁺ᵐ / (n + m)!| = |σⁿ / n!| ⊗ |τᵐ / m!|`

(`TauCeti.SmoothTwoForm.liouvilleMeasure_prod`). The volume form of `σ ⊕ τ` takes the value
`(σⁿ / n!)(v) (τᵐ / m!)(w)` on product frames
(`TauCeti.SmoothTwoForm.volumeForm_prod_apply_sumElim`), and the measure of such a top form is the
product measure (`TauCeti.RoughForm.measure_eq_prod`). The
normalization `ωⁿ / n!` is what makes this multiplicative. Neither nondegeneracy nor closedness of
the forms is needed.

## Main results

* `TauCeti.SmoothTwoForm.liouvilleMeasure_prod`: the Liouville measure of a product form is the
  product of the Liouville measures.

## References

* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Section 30.1 (the Liouville measure).
* D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford University
  Press, 2017, Chapter 3 (the volume form `ωⁿ / n!`).
-/

public section

noncomputable section

open Module MeasureTheory
open scoped ContDiff Manifold

namespace TauCeti

namespace SmoothTwoForm

variable {E H M F H' N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] [TopologicalSpace H']
  {J : ModelWithCorners ℝ F H'} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]
  [MeasurableSpace N] [BorelSpace N] [SecondCountableTopology N] {n m : ℕ}
  [hn : Fact (finrank ℝ E = 2 * n)] [hm : Fact (finrank ℝ F = 2 * m)]
  [Fact (finrank ℝ (E × F) = 2 * (n + m))]

/-- **The Liouville measure of a product is the product of the Liouville measures.** For
two-forms `σ` on a manifold of dimension `2 n` and `τ` on a manifold of dimension `2 m`, the
Liouville measure `|(σ ⊕ τ)ⁿ⁺ᵐ / (n + m)!|` of the product form is the product measure
`|σⁿ / n!| ⊗ |τᵐ / m!|`. -/
theorem liouvilleMeasure_prod (σ : SmoothTwoForm I M) (τ : SmoothTwoForm J N) :
    (σ.prod τ).liouvilleMeasure (n + m) = (σ.liouvilleMeasure n).prod (τ.liouvilleMeasure m) := by
  rw [liouvilleMeasure_def, liouvilleMeasure_def, liouvilleMeasure_def]
  exact RoughForm.measure_eq_prod (mul_add 2 n m).symm
    ((σ.volumeForm n).isSmoothForm.of_le bot_le) ((τ.volumeForm m).isSmoothForm.of_le bot_le)
    (volumeForm_prod_apply_sumElim σ τ)

end SmoothTwoForm

end TauCeti
