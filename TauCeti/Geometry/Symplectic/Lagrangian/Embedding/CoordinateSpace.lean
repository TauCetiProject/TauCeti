/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Complex.CoordinateSpace
public import TauCeti.Geometry.Symplectic.Lagrangian.Embedding.Basic

/-!
# The real locus as a Lagrangian embedding

For a finite index type `ι`, the real locus `ι → ℝ` in complex coordinate space `ι → ℂ` is a
Lagrangian embedding for the standard symplectic form `ω₀ = Σ_j ds_j ∧ dt_j` and for each of its
nonzero multiples `c ω₀`.

`TauCeti.Geometry.Symplectic.Complex.CoordinateSpace` proves the linear statement, that the real
subspace is Lagrangian for `ω₀`. This file lifts it to the manifold-level predicate
`IsLagrangianEmbedding`, giving the flat coordinate model of an embedded Lagrangian submanifold.
The nonzero rescalings are kept because the sign of `c` matters downstream: `c = 1` pairs with
the complex structure `I`, which `ω₀` tames, while `c = -1` pairs with `-I`, which `-ω₀` tames,
and both comparisons recover that the real locus is totally real.

## Main results

* `TauCeti.isLagrangianEmbedding_realLocus_rescale`: the real locus is a Lagrangian embedding for
  every nonzero multiple `c ω₀`.
* `TauCeti.isLagrangianEmbedding_realLocus`: the case `c = 1`.

## References

* D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford, 2017,
  Sections 2.1 and 3.4.
-/

public noncomputable section

open scoped Manifold ContDiff

namespace TauCeti

variable {ι : Type*} [Fintype ι]

/-- The real locus in complex coordinate space is a Lagrangian embedding for every nonzero
multiple `c Σ_j ds_j ∧ dt_j` of the standard symplectic form. -/
theorem isLagrangianEmbedding_realLocus_rescale (c : ℝ) (hc : c ≠ 0) :
    (SymplecticForm.isNondegenerate_constSmooth
        ((stdComplexPiSymplecticForm ι).rescale c hc)).IsLagrangianEmbedding
      𝓘(ℝ, ι → ℝ) (ContinuousLinearMap.piMap fun _ : ι ↦ Complex.ofRealCLM) :=
  (SmoothTwoForm.IsNondegenerate.isLagrangianEmbedding_iff_of_isSmoothEmbedding
    (ContinuousLinearMap.isSmoothEmbedding_of_injective
      (Function.Injective.piMap fun _ ↦ Complex.ofReal_injective))).2
    ((SymplecticForm.isLagrangianMap_continuousLinearMap_iff _ _).2
      ((SymplecticForm.isLagrangian_rescale_iff _ _).2
        isLagrangian_stdComplexPiSymplecticForm_range_ofReal))

/-- The real locus in complex coordinate space is a Lagrangian embedding for the standard
symplectic form `Σ_j ds_j ∧ dt_j`: the case `c = 1` of `isLagrangianEmbedding_realLocus_rescale`. -/
theorem isLagrangianEmbedding_realLocus :
    (SymplecticForm.isNondegenerate_constSmooth
        (stdComplexPiSymplecticForm ι)).IsLagrangianEmbedding
      𝓘(ℝ, ι → ℝ) (ContinuousLinearMap.piMap fun _ : ι ↦ Complex.ofRealCLM) := by
  simpa using isLagrangianEmbedding_realLocus_rescale (ι := ι) 1 one_ne_zero

end TauCeti
