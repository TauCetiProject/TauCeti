/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Manifold.DuistermaatHeckman
public import TauCeti.Geometry.Symplectic.Manifold.Prod
public import TauCeti.LinearAlgebra.Dimension.FactFinrank
import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Measure.Prod

/-!
# The Liouville measure of a product

Let `σ` and `τ` be two-forms on second-countable manifolds `M` and `N` modelled on spaces of
dimensions `2 n` and `2 m`. The product `M × N` carries the product form
`σ ⊕ τ = pr₁^* σ + pr₂^* τ` (`TauCeti.SmoothTwoForm.prod`), and its Liouville measure is the
product of the Liouville measures of the factors
(`TauCeti.SmoothTwoForm.liouvilleMeasure_prod`):

`|(σ ⊕ τ)^(n + m) / (n + m)!| = |σⁿ / n!| ⊗ |τᵐ / m!|`.

The volume form `(σ ⊕ τ)^(n + m) / (n + m)!` takes the value `(σⁿ / n!)(u) · (τᵐ / m!)(w)` on the
tangent vectors `(uᵢ, 0)` followed by `(0, wⱼ)`
(`TauCeti.SmoothTwoForm.volumeForm_prod_apply_append`), and the measure of a top form factoring in
this way on product frames is the product measure (`TauCeti.RoughForm.measure_eq_prod`). No
nondegeneracy is needed: a degenerate factor makes both sides vanish where it degenerates.

Pushing forward along a product map `μ × ν`, such as the moment map `(μ, ν)` of the product of
two Hamiltonian torus actions, gives the product of the Duistermaat–Heckman measures
(`TauCeti.SmoothTwoForm.duistermaatHeckmanMeasure_prod`).

## Main results

* `TauCeti.SmoothTwoForm.liouvilleMeasure_prod`: the Liouville measure of a product is the product
  of the Liouville measures.
* `TauCeti.SmoothTwoForm.duistermaatHeckmanMeasure_prod`: the Duistermaat–Heckman measure of a
  product map is the product of the Duistermaat–Heckman measures.

## References

* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Section 30.1 (the Liouville and Duistermaat–Heckman measures).
-/

public section

noncomputable section

open Module MeasureTheory Set
open scoped Manifold ContDiff

namespace TauCeti.SmoothTwoForm

variable {E H M F H' N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] [TopologicalSpace H']
  {J : ModelWithCorners ℝ F H'} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]
  {n m : ℕ}

section Measure

variable [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]
  [MeasurableSpace N] [BorelSpace N] [SecondCountableTopology N]
  [Fact (finrank ℝ E = 2 * n)] [Fact (finrank ℝ F = 2 * m)]

/-- **The Liouville measure of a product is the product of the Liouville measures.** For two-forms
`σ` and `τ` on second-countable manifolds modelled on spaces of dimensions `2 n` and `2 m`, the
Liouville measure `|(σ ⊕ τ)^(n + m) / (n + m)!|` of the product form on `M × N` is the product
measure of `|σⁿ / n!|` and `|τᵐ / m!|`. Neither form needs to be nondegenerate. -/
@[simp]
theorem liouvilleMeasure_prod (σ : SmoothTwoForm I M) (τ : SmoothTwoForm J N) :
    (prod σ τ).liouvilleMeasure (n + m) = (σ.liouvilleMeasure n).prod (τ.liouvilleMeasure m) := by
  rw [liouvilleMeasure_def, liouvilleMeasure_def, liouvilleMeasure_def]
  exact RoughForm.measure_eq_prod (Nat.mul_add 2 n m).symm
    ((σ.volumeForm n).isSmoothForm.of_le bot_le) ((τ.volumeForm m).isSmoothForm.of_le bot_le)
    fun x y v w ↦ volumeForm_prod_apply_append σ τ (x, y) v w

/-- **The Duistermaat–Heckman measure of a product.** For measurable maps `μ` on `M` and `ν` on
`N`, such as the moment maps of two Hamiltonian torus actions, the Duistermaat–Heckman measure of
`σ ⊕ τ` and the product map `μ × ν` is the product of the Duistermaat–Heckman measures of `μ` and
of `ν`. -/
theorem duistermaatHeckmanMeasure_prod {G G' : Type*} [MeasurableSpace G] [MeasurableSpace G']
    (σ : SmoothTwoForm I M) (τ : SmoothTwoForm J N) {μ : M → G} {ν : N → G'}
    (hμ : Measurable μ) (hν : Measurable ν) :
    (prod σ τ).duistermaatHeckmanMeasure (n + m) (Prod.map μ ν) =
      (σ.duistermaatHeckmanMeasure n μ).prod (τ.duistermaatHeckmanMeasure m ν) := by
  rw [duistermaatHeckmanMeasure_def, duistermaatHeckmanMeasure_def,
    duistermaatHeckmanMeasure_def, liouvilleMeasure_prod, Measure.map_prod_map _ _ hμ hν]

end Measure

end TauCeti.SmoothTwoForm
