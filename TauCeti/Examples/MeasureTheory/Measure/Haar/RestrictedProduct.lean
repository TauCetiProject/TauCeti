/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.Haar.RestrictedProduct.Basic

import TauCeti.Algebra.BigOperators.Finprod

/-!
# Changing finitely many local normalizations of a restricted Haar product

Three instances of `TauCeti.restrictedHaar_eq_finprod_smul`, which rescales the normalized
restricted Haar product `restrictedHaar B μ` when the local Haar measures are rescaled by
`c i • μ i`:

* unit local scalars preserve the measure (`TauCeti.restrictedHaar_eq_of_eq_one_smul`);
* rescaling one local factor by `2` rescales the restricted product by `2`
  (`TauCeti.restrictedHaar_eq_two_smul_of_mulSingle`);
* rescaling two local factors by `2` and `1 / 2` preserves the restricted product
  (`TauCeti.restrictedHaar_eq_of_mulSingle_two_mul_mulSingle_inv`).
-/

public section

open Filter MeasureTheory MeasureTheory.Measure
open scoped NNReal RestrictedProduct

namespace TauCeti

variable {ι : Type*} [Countable ι] [DecidableEq ι]
  {G : ι → Type*} [∀ i, Group (G i)] [∀ i, TopologicalSpace (G i)]
  [∀ i, IsTopologicalGroup (G i)] [∀ i, LocallyCompactSpace (G i)]
  [∀ i, SecondCountableTopology (G i)] [∀ i, MeasurableSpace (G i)] [∀ i, BorelSpace (G i)]
  {K : ι → Type*} [∀ i, SetLike (K i) (G i)] [∀ i, SubgroupClass (K i) (G i)]
  (B : ∀ i, K i) [Fact (∀ i, IsOpen (B i : Set (G i)))]
  (μ : ∀ i, Measure (G i)) [∀ i, (μ i).IsHaarMeasure] (hμB : ∀ᶠ i in cofinite, μ i (B i) = 1)
  (μ' : ∀ i, Measure (G i)) [∀ i, (μ' i).IsHaarMeasure] (hμ'B : ∀ᶠ i in cofinite, μ' i (B i) = 1)

omit [DecidableEq ι] in
/-- Unit local scalars preserve the restricted Haar product. -/
theorem restrictedHaar_eq_of_eq_one_smul (hμ' : ∀ i, μ' i = (1 : ℝ≥0) • μ i) :
    restrictedHaar B μ' hμ'B = restrictedHaar B μ hμB := by
  rw [restrictedHaar_eq_finprod_smul B μ hμB μ' hμ'B 1 hμ', Pi.one_def, finprod_one, one_smul]

/-- Rescaling the local Haar measure at one index by `2` rescales the restricted Haar product
by `2`. -/
theorem restrictedHaar_eq_two_smul_of_mulSingle (j : ι)
    (hμ' : ∀ i, μ' i = (Pi.mulSingle j 2 : ι → ℝ≥0) i • μ i) :
    restrictedHaar B μ' hμ'B = (2 : ℝ≥0) • restrictedHaar B μ hμB := by
  rw [restrictedHaar_eq_finprod_smul B μ hμB μ' hμ'B _ hμ', finprod_mulSingle]

/-- Rescaling the local Haar measures at two indices by `2` and `1 / 2` preserves the restricted
Haar product. -/
theorem restrictedHaar_eq_of_mulSingle_two_mul_mulSingle_inv (j k : ι)
    (hμ' : ∀ i, μ' i = ((Pi.mulSingle j 2 : ι → ℝ≥0) i * (Pi.mulSingle k 2⁻¹ : ι → ℝ≥0) i) • μ i) :
    restrictedHaar B μ' hμ'B = restrictedHaar B μ hμB := by
  rw [restrictedHaar_eq_finprod_smul B μ hμB μ' hμ'B _ hμ',
    finprod_mul_distrib ((Set.finite_singleton j).subset Pi.mulSupport_mulSingle_subset)
      ((Set.finite_singleton k).subset Pi.mulSupport_mulSingle_subset),
    finprod_mulSingle, finprod_mulSingle, mul_inv_cancel₀ two_ne_zero, one_smul]

end TauCeti
