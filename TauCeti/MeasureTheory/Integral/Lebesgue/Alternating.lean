/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Module.Alternating.TopDegree
public import TauCeti.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.LinearAlgebra.Basis.Prod
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Measure.Prod
import TauCeti.MeasureTheory.Integral.Bochner.Alternating

/-!
# Absolute alternating-form Lebesgue integrals over products

A basis determines a real top-degree coefficient and normalized Haar measure, and the Lebesgue
integral of the absolute value of a coefficient does not depend on the basis
(`Module.Basis.addHaar_withDensity_ofReal_abs_apply_eq`). Over a product of measurable sets, such
an integral whose integrand factors in a product basis is therefore the product of the factor
integrals, since the Haar measure of a product basis is the product of the Haar measures.

## Main results

* `Module.Basis.setLIntegral_ofReal_abs_apply_prod`: over a product set, a coefficient integral
  whose integrand factors in a product basis is the product of the factor integrals.
-/

public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace Module.Basis

variable {E F ι ι' κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] [Fintype ι] [Fintype ι'] [Fintype κ]

/-- A top-form coefficient integral over a product set whose integrand factors in the product
basis, reindexed along any `e : ι ⊕ ι' ≃ κ`, is the product of the factor integrals. The Borel
structure on `E × F` is arbitrary, so this applies to the chart measurable structure of
`TauCeti.RoughForm.measure`. -/
theorem setLIntegral_ofReal_abs_apply_prod [MeasurableSpace F] [BorelSpace F]
    [mEF : MeasurableSpace (E × F)] [BorelSpace (E × F)] (e : ι ⊕ ι' ≃ κ)
    (b₀ : Basis κ ℝ (E × F)) (b₁ : Basis ι ℝ E) (b₂ : Basis ι' ℝ F)
    {A₁ : Set E} {A₂ : Set F} (hA₁ : MeasurableSet A₁) (hA₂ : MeasurableSet A₂)
    (ψ : E × F → (E × F) [⋀^κ]→L[ℝ] ℝ) {f : E → ℝ≥0∞} {g : F → ℝ≥0∞}
    (hf : AEMeasurable f (b₁.addHaar.restrict A₁)) (hg : AEMeasurable g (b₂.addHaar.restrict A₂))
    (hψ : ∀ z ∈ A₁ ×ˢ A₂, ENNReal.ofReal |ψ z ((b₁.prod b₂).reindex e)| = f z.1 * g z.2) :
    ∫⁻ z in A₁ ×ˢ A₂, ENNReal.ofReal |ψ z b₀| ∂b₀.addHaar =
      (∫⁻ y in A₁, f y ∂b₁.addHaar) * ∫⁻ z in A₂, g z ∂b₂.addHaar := by
  have : FiniteDimensional ℝ F := b₂.finiteDimensional_of_finite
  obtain rfl : mEF = Prod.instMeasurableSpace :=
    BorelSpace.measurable_eq.trans (Prod.borelSpace (α := E) (β := F)).measurable_eq.symm
  rw [← withDensity_apply _ (hA₁.prod hA₂),
    addHaar_withDensity_ofReal_abs_apply_eq ((b₁.prod b₂).reindex e) b₀ ψ,
    withDensity_apply _ (hA₁.prod hA₂), setLIntegral_congr_fun (hA₁.prod hA₂) hψ,
    addHaar_reindex, prod_addHaar, ← Measure.prod_restrict, lintegral_prod_mul hf hg]

end Module.Basis
