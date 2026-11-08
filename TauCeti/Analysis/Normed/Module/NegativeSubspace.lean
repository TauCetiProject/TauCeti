/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.FiniteDimensional
public import Mathlib.LinearAlgebra.Prod

/-!
# Graph coordinates for negative subspaces

For the normalized quadratic form `Q(u,v) = -‖u‖² + ‖v‖²`, strict negativity at every
nonzero vector of a subspace is equivalent to `‖v‖ < ‖u‖`; such a subspace is called
*split-negative* (`Submodule.IsSplitNegative`). It projects
injectively to the first factor. When its dimension equals that of the first factor,
it is the graph of a unique continuous linear map `A` with `‖A‖ < 1`.

These are the graph coordinates used to compare negative spaces in Morse charts. Their
parameter domain is the open operator-norm unit ball, rather than the closed ball: a
map of norm one can have a null vector in its graph. The classification also applies
to a real normed first factor and a real seminormed second factor; only in inner product
spaces is `Q` a quadratic form. Only the first factor needs to be finite dimensional.

The main result is
`Submodule.existsUnique_eq_graph_iff_finrank_eq_and_isSplitNegative`. The preceding dimension
bound and the final maximality theorem explain why subspaces of this dimension are
maximal among negative subspaces. The statements include a zero-dimensional first factor.

## References

* J. Milnor, *Morse Theory*, Princeton University Press, 1963, §3, change of negative spaces
  in the comparison of Morse coordinates.

The graph construction uses Mathlib's `Submodule.exists_eq_graph` (the vertical line test).
-/

public section

open Function

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [SeminormedAddCommGroup F] [NormedSpace ℝ F]

namespace Submodule

variable {W W' : Submodule ℝ (E × F)}

/-- A submodule `W` of `E × F` is *split-negative* if the split indefinite form
`Q(u, v) = -‖u‖² + ‖v‖²` is negative on every nonzero vector of `W`: `‖v‖ < ‖u‖` for every
nonzero `(u, v) ∈ W`. -/
def IsSplitNegative (W : Submodule ℝ (E × F)) : Prop :=
  ∀ w ∈ W, w ≠ 0 → ‖w.2‖ < ‖w.1‖

theorem isSplitNegative_iff : W.IsSplitNegative ↔ ∀ w ∈ W, w ≠ 0 → ‖w.2‖ < ‖w.1‖ :=
  Iff.rfl

@[simp]
theorem isSplitNegative_bot : (⊥ : Submodule ℝ (E × F)).IsSplitNegative := by
  intro w hw hw0
  exact absurd ((mem_bot ℝ).1 hw) hw0

/-- A submodule of a split-negative subspace is split-negative. -/
theorem IsSplitNegative.mono (hW : W.IsSplitNegative) (h : W' ≤ W) : W'.IsSplitNegative :=
  fun w hw ↦ hW w (h hw)

/-- A nonzero vector of a split-negative subspace has nonzero first component. -/
theorem IsSplitNegative.fst_ne_zero (hW : W.IsSplitNegative) {w : E × F} (hw : w ∈ W)
    (hw0 : w ≠ 0) : w.1 ≠ 0 := by
  intro h
  have := hW w hw hw0
  rw [h, norm_zero] at this
  exact (norm_nonneg _).not_gt this

/-- A split-negative subspace meets the positive factor `0 × F` only in `0`. -/
theorem IsSplitNegative.disjoint_ker_fst (hW : W.IsSplitNegative) :
    Disjoint W (LinearMap.ker (LinearMap.fst ℝ E F)) := by
  rw [disjoint_def]
  intro w hw hw'
  by_contra hw0
  exact hW.fst_ne_zero hw hw0 hw'

/-- The graph of a linear map `T : E → F` is split-negative exactly when `T` strictly decreases
the norm of every nonzero vector. -/
theorem isSplitNegative_graph_iff (T : E →ₗ[ℝ] F) :
    (LinearMap.graph T).IsSplitNegative ↔ ∀ u, u ≠ 0 → ‖T u‖ < ‖u‖ := by
  refine ⟨fun h u hu ↦ h (u, T u) rfl fun h0 ↦ hu congr(($h0).1), fun h w hw hw0 ↦ ?_⟩
  rw [LinearMap.mem_graph_iff] at hw
  rw [hw]
  refine h _ fun h1 ↦ hw0 (Prod.ext h1 ?_)
  rw [hw, h1, map_zero, Prod.snd_zero]

/-- A split-negative subspace projects injectively to the negative factor. No
finite-dimensionality is needed for this implication. -/
theorem IsSplitNegative.injective_fst (hW : W.IsSplitNegative) :
    Injective ((LinearMap.fst ℝ E F).comp W.subtype) := by
  apply LinearMap.ker_eq_bot.mp
  rw [LinearMap.ker_eq_bot']
  intro z hz
  apply Subtype.ext
  by_contra hne
  exact hW.fst_ne_zero z.property hne (by
    simpa only [LinearMap.comp_apply, LinearMap.fst_apply, Submodule.subtype_apply] using hz)

end Submodule

namespace ContinuousLinearMap

/-- A graph is strictly negative for `-‖u‖² + ‖v‖²` exactly when its operator has norm
strictly less than one. Finite-dimensionality is essential for the reverse implication. -/
theorem opNorm_lt_one_iff_isSplitNegative_graph [FiniteDimensional ℝ E] (A : E →L[ℝ] F) :
    ‖A‖ < 1 ↔ A.toLinearMap.graph.IsSplitNegative := by
  rw [A.opNorm_lt_iff zero_lt_one, Submodule.isSplitNegative_graph_iff]
  simp only [ContinuousLinearMap.coe_coe, one_mul]

end ContinuousLinearMap

namespace Submodule

variable [FiniteDimensional ℝ E] {W V : Submodule ℝ (E × F)}

/-- Every split-negative subspace is finite dimensional, even if the positive factor is
infinite dimensional. -/
theorem IsSplitNegative.finiteDimensional (hW : W.IsSplitNegative) : FiniteDimensional ℝ W :=
  FiniteDimensional.of_injective _ hW.injective_fst

/-- The dimension of a split-negative subspace is at most that of the negative factor. -/
theorem IsSplitNegative.finrank_le (hW : W.IsSplitNegative) :
    Module.finrank ℝ W ≤ Module.finrank ℝ E :=
  LinearMap.finrank_le_finrank_of_injective hW.injective_fst

/-- A split-negative subspace of full negative dimension is the graph of a strict contraction. -/
theorem IsSplitNegative.exists_eq_graph_of_finrank_eq (hW : W.IsSplitNegative)
    (hdim : Module.finrank ℝ W = Module.finrank ℝ E) :
    ∃ A : E →L[ℝ] F, ‖A‖ < 1 ∧ W = A.toLinearMap.graph := by
  have := hW.finiteDimensional
  have hinj := hW.injective_fst
  have hsurj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hinj
  obtain ⟨A, hA⟩ := W.exists_eq_graph ⟨hinj, hsurj⟩
  refine ⟨A.toContinuousLinearMap, ?_, hA⟩
  exact A.toContinuousLinearMap.opNorm_lt_one_iff_isSplitNegative_graph.mpr (hA ▸ hW)

/-- The full-dimensional split-negative subspaces are exactly the graphs of unique operators in
the open operator-norm unit ball. This is the global graph-coordinate classification. -/
theorem existsUnique_eq_graph_iff_finrank_eq_and_isSplitNegative (W : Submodule ℝ (E × F)) :
    (∃! A : E →L[ℝ] F, ‖A‖ < 1 ∧ W = A.toLinearMap.graph) ↔
      Module.finrank ℝ W = Module.finrank ℝ E ∧ W.IsSplitNegative := by
  constructor
  · rintro ⟨A, ⟨hA, rfl⟩, -⟩
    refine ⟨?_, A.opNorm_lt_one_iff_isSplitNegative_graph.mp hA⟩
    rw [LinearMap.graph_eq_range_prod]
    apply LinearMap.finrank_range_of_inj
    intro u v huv
    exact congrArg Prod.fst huv
  · rintro ⟨hdim, hW⟩
    obtain ⟨A, hA, hgraph⟩ := hW.exists_eq_graph_of_finrank_eq hdim
    refine ⟨A, ⟨hA, hgraph⟩, fun B hB ↦ ?_⟩
    ext u
    have hu : (u, B u) ∈ A.toLinearMap.graph := by
      rw [← hgraph, hB.2]
      simp
    exact (LinearMap.mem_graph_iff _ _).mp hu

/-- A full-dimensional subspace of a split-negative subspace is all of it: a full-dimensional
split-negative subspace cannot be enlarged while remaining split-negative. -/
theorem IsSplitNegative.eq_of_le_of_finrank_eq (hV : V.IsSplitNegative) (hWV : W ≤ V)
    (hdim : Module.finrank ℝ W = Module.finrank ℝ E) : W = V := by
  have := hV.finiteDimensional
  apply Submodule.eq_of_le_of_finrank_le hWV
  rw [hdim]
  exact hV.finrank_le

end Submodule
