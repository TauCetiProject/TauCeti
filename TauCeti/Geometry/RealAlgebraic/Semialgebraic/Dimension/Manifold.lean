/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.RealAlgebraic.Semialgebraic.Dimension.Basic
public import TauCeti.LinearAlgebra.Complex.Finrank

/-!
# Semialgebraic dimension of manifolds

A nonempty subset of real coordinate space that is a topological manifold has dimension equal
to the real dimension of its model space. Thus the dimension computed by cylindrical algebraic
decompositions agrees with smooth real manifold dimension, and with twice complex manifold
dimension, whenever the subset is semialgebraic.

Only charts for the subspace topology are needed: no smoothness, semialgebraicity of the charts,
compactness, or countability assumption enters the comparison. The charts must be modelled on a
whole finite-dimensional vector space, rather than a half-space. This result does not identify
the dimension of singular analytic germs.

## References

* J. Bochnak, M. Coste, M.-F. Roy, *Real Algebraic Geometry*, Section 2.8.
-/

public section

open Module Set Topology

namespace TauCeti

variable {n : ℕ} {s : Set (Fin n → ℝ)}

/-- The dimension of a nonempty subset that is a topological manifold, with its subspace topology,
is the real dimension of its model space. In particular, this compares CAD dimension with smooth
manifold dimension for semialgebraic submanifolds. -/
theorem semialgebraicDim_eq_finrank_of_chartedSpace
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [ChartedSpace E s] (hs : s.Nonempty) : semialgebraicDim s = finrank ℝ E := by
  obtain ⟨x, hx⟩ := hs
  let x₀ : s := ⟨x, hx⟩
  let e := chartAt E x₀
  let c := (Module.finBasis ℝ E).equivFun.toContinuousLinearEquiv.toHomeomorph
  have hsource : Nonempty e.source := ⟨⟨x₀, mem_chart_source E x₀⟩⟩
  refine le_antisymm (semialgebraicDim_le_iff.mpr fun t ht htne d f hf ↦ ?_) ?_
  · -- Restrict a candidate Euclidean cell to a chart of the manifold containing one of its points.
    obtain ⟨y, hy⟩ := htne
    let i : t → s := inclusion ht
    let φ := chartAt E (i ⟨y, hy⟩)
    let U : Set t := i ⁻¹' φ.source
    have hU : IsOpen U := φ.open_source.preimage (continuous_inclusion ht)
    have : Nonempty U := ⟨⟨⟨y, hy⟩, mem_chart_source E (i ⟨y, hy⟩)⟩⟩
    let j : U → φ.source := φ.source.codRestrict (i ∘ Subtype.val) (fun z ↦ z.2)
    have hj : IsEmbedding j :=
      ((IsEmbedding.inclusion ht).comp IsEmbedding.subtypeVal).codRestrict _ _
    have hdim := (hf.comp hU.isOpenEmbedding_subtypeVal).finrank_le_of_isEmbedding
      (φ.isOpenEmbedding_restrict.isEmbedding.comp hj)
    have hdim' : d ≤ finrank ℝ E := by simpa only [finrank_fin_fun] using hdim
    exact_mod_cast hdim'
  · -- A single nonempty chart supplies a cell of the full model dimension inside `s`.
    exact le_semialgebraicDim
      (IsEmbedding.subtypeVal.comp IsEmbedding.subtypeVal)
      (by rintro _ ⟨z, rfl⟩; exact z.1.2)
      (c.isOpenEmbedding.comp e.isOpenEmbedding_restrict)

/-- For a nonempty subset of real coordinate space with complex manifold charts, its dimension
is twice the complex dimension of the model space. No differentiability of chart transitions is
needed for this dimension comparison. -/
theorem semialgebraicDim_eq_two_mul_finrank_of_complex_chartedSpace
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    [ChartedSpace E s] (hs : s.Nonempty) :
    semialgebraicDim s = (2 * finrank ℂ E : ℕ) := by
  rw [semialgebraicDim_eq_finrank_of_chartedSpace E hs,
    finrank_real_eq_two_mul_finrank_complex]

end TauCeti
