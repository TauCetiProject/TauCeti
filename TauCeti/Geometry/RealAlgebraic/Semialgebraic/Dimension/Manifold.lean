/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Analytic.Submanifold.Basic
public import TauCeti.Geometry.RealAlgebraic.Semialgebraic.Dimension.Basic
public import TauCeti.LinearAlgebra.Complex.Finrank

/-!
# Semialgebraic dimension of manifolds

A nonempty subset of real coordinate space that is a topological manifold has dimension equal
to the real dimension of its model space. Thus the dimension computed by cylindrical algebraic
decompositions agrees with smooth real manifold dimension, with analytic submanifold dimension
(`TauCeti.IsAnalyticSubmanifold.semialgebraicDim_eq`), and with twice complex manifold dimension,
whenever the subset is semialgebraic.

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

/-- A `d`-dimensional analytic submanifold of `ℝ ^ n` has semialgebraic dimension `d`, even
without assuming that the submanifold is semialgebraic. -/
theorem IsAnalyticSubmanifold.semialgebraicDim_eq {d : ℕ} (hs : IsAnalyticSubmanifold d s) :
    semialgebraicDim s = d := by
  -- In any analytic chart `e` of `s`, reading the first `d` coordinates of `e` is an open
  -- embedding of `s ∩ e.source` into `Fin d → ℝ`.
  have chartOpenEmbedding {e : OpenPartialHomeomorph (Fin n → ℝ) (Fin n → ℝ)}
      (he : IsAnalyticChart d s e) :
      IsOpenEmbedding (fun z : ↑(s ∩ e.source) ↦ firstCoords ℝ n d (e z.1)) := by
    let W : Set (Fin d → ℝ) := firstCoords ℝ d n ⁻¹' e.target
    have hW : IsOpen W := e.open_target.preimage (firstCoords ℝ d n).continuous
    have hto (z : ↑(s ∩ e.source)) : firstCoords ℝ n d (e z.1) ∈ W := by
      rw [mem_preimage, he.firstCoords_firstCoords_apply z.2.2 z.2.1]
      exact e.map_source z.2.2
    have hinv (u : W) : e.symm (firstCoords ℝ d n u.1) ∈ s ∩ e.source :=
      ⟨(he.mem_iff (e.map_target u.2)).2 fun i hi ↦ by
          rw [e.right_inv u.2]
          exact firstCoords_apply_of_le u.1 hi,
        e.map_target u.2⟩
    let φ : ↑(s ∩ e.source) ≃ₜ W :=
      { toFun := fun z ↦ ⟨firstCoords ℝ n d (e z.1), hto z⟩
        invFun := fun u ↦ ⟨e.symm (firstCoords ℝ d n u.1), hinv u⟩
        left_inv := fun z ↦ Subtype.ext (he.symm_firstCoords_firstCoords_apply z.2.2 z.2.1)
        right_inv := fun u ↦ Subtype.ext (by simp [e.right_inv u.2, hs.le])
        continuous_toFun := ((firstCoords ℝ n d).continuous.comp
          (e.continuousOn.comp_continuous continuous_subtype_val fun z ↦ z.2.2)).subtype_mk hto
        continuous_invFun := (e.continuousOn_symm.comp_continuous
          ((firstCoords ℝ d n).continuous.comp continuous_subtype_val)
          fun u ↦ u.2).subtype_mk hinv }
    exact hW.isOpenEmbedding_subtypeVal.comp φ.isOpenEmbedding
  refine le_antisymm (semialgebraicDim_le_iff.2 fun t ht htne k f hf ↦ ?_) ?_
  · obtain ⟨y, hy⟩ := htne
    obtain ⟨e, hye, he⟩ := hs.exists_isAnalyticChart y (ht hy)
    let U : Set t := Subtype.val ⁻¹' e.source
    have hU : IsOpen U := e.open_source.preimage continuous_subtype_val
    have : Nonempty U := ⟨⟨⟨y, hy⟩, hye⟩⟩
    let j : U → ↑(s ∩ e.source) :=
      (s ∩ e.source).codRestrict (Subtype.val ∘ Subtype.val) fun z ↦ ⟨ht z.1.2, z.2⟩
    have hj : IsEmbedding j :=
      (IsEmbedding.subtypeVal.comp IsEmbedding.subtypeVal).codRestrict _ _
    have hdim := (hf.comp hU.isOpenEmbedding_subtypeVal).finrank_le_of_isEmbedding
      ((chartOpenEmbedding he).isEmbedding.comp hj)
    have hdim' : k ≤ d := by simpa only [finrank_fin_fun] using hdim
    exact_mod_cast hdim'
  · obtain ⟨x, hx⟩ := hs.nonempty
    obtain ⟨e, hxe, he⟩ := hs.exists_isAnalyticChart x hx
    have : Nonempty ↑(s ∩ e.source) := ⟨⟨x, hx, hxe⟩⟩
    exact le_semialgebraicDim IsEmbedding.subtypeVal
      (by rintro _ ⟨z, rfl⟩; exact z.2.1) (chartOpenEmbedding he)

end TauCeti
