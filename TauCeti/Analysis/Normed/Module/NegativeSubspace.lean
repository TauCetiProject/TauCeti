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
nonzero vector of a subspace is equivalent to `‖v‖ < ‖u‖`. Such a subspace projects
injectively to the first factor. When its dimension equals that of the first factor,
it is the graph of a unique continuous linear map `A` with `‖A‖ < 1`.

These are the graph coordinates used to compare negative spaces in Morse charts. Their
parameter domain is the open operator-norm unit ball, rather than the closed ball: a
map of norm one can have a null vector in its graph. The classification also applies
to a real normed first factor and a real seminormed second factor; only in inner product
spaces is `Q` a quadratic form. Only the first factor needs to be finite dimensional.

The main result is
`Submodule.existsUnique_eq_graph_iff_finrank_eq_and_norm_snd_lt`. The preceding dimension
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

namespace ContinuousLinearMap

/-- A graph is strictly negative for `-‖u‖² + ‖v‖²` exactly when its operator has norm
strictly less than one. Finite-dimensionality is essential for the reverse implication. -/
theorem opNorm_lt_one_iff_forall_mem_graph_norm_snd_lt [FiniteDimensional ℝ E]
    (A : E →L[ℝ] F) :
    ‖A‖ < 1 ↔ ∀ z ∈ A.toLinearMap.graph, z ≠ 0 → ‖z.2‖ < ‖z.1‖ := by
  rw [A.opNorm_lt_iff zero_lt_one]
  constructor
  · intro h z hz hne
    have hzA := (LinearMap.mem_graph_iff _ _).mp hz
    have hfst : z.1 ≠ 0 := by
      intro hzero
      apply hne
      exact Prod.ext hzero (by simpa [hzero] using hzA)
    simpa only [hzA, ContinuousLinearMap.coe_coe, one_mul] using h z.1 hfst
  · intro h u hu
    have hne : (u, A u) ≠ (0 : E × F) := fun hz ↦ hu (congrArg Prod.fst hz)
    simpa only [one_mul] using h (u, A u) (by simp) hne

end ContinuousLinearMap

namespace Submodule

/-- A subspace lying strictly inside the negative cone projects injectively to the negative
factor. No finite-dimensionality is needed for this implication. -/
theorem injective_fst_of_norm_snd_lt (W : Submodule ℝ (E × F))
    (hW : ∀ z ∈ W, z ≠ 0 → ‖z.2‖ < ‖z.1‖) :
    Injective ((LinearMap.fst ℝ E F).comp W.subtype) := by
  apply LinearMap.ker_eq_bot.mp
  rw [LinearMap.ker_eq_bot']
  intro z hz
  apply Subtype.ext
  by_contra hne
  have hlt := hW z z.property hne
  have hfst : (z : E × F).1 = 0 := by
    simpa only [LinearMap.comp_apply, LinearMap.fst_apply, Submodule.subtype_apply] using hz
  rw [hfst, norm_zero] at hlt
  exact (not_lt_of_ge (norm_nonneg _)) hlt

variable [FiniteDimensional ℝ E]

/-- Every subspace strictly inside the negative cone is finite dimensional, even if the
positive factor is infinite dimensional. -/
theorem finiteDimensional_of_norm_snd_lt (W : Submodule ℝ (E × F))
    (hW : ∀ z ∈ W, z ≠ 0 → ‖z.2‖ < ‖z.1‖) : FiniteDimensional ℝ W :=
  FiniteDimensional.of_injective _ (W.injective_fst_of_norm_snd_lt hW)

/-- The dimension of a negative subspace is at most that of the negative factor. -/
theorem finrank_le_of_norm_snd_lt (W : Submodule ℝ (E × F))
    (hW : ∀ z ∈ W, z ≠ 0 → ‖z.2‖ < ‖z.1‖) :
    Module.finrank ℝ W ≤ Module.finrank ℝ E :=
  LinearMap.finrank_le_finrank_of_injective (W.injective_fst_of_norm_snd_lt hW)

/-- A negative subspace of full negative dimension is the graph of a strict contraction. -/
theorem exists_eq_graph_of_finrank_eq_of_norm_snd_lt (W : Submodule ℝ (E × F))
    (hdim : Module.finrank ℝ W = Module.finrank ℝ E)
    (hW : ∀ z ∈ W, z ≠ 0 → ‖z.2‖ < ‖z.1‖) :
    ∃ A : E →L[ℝ] F, ‖A‖ < 1 ∧ W = A.toLinearMap.graph := by
  have := W.finiteDimensional_of_norm_snd_lt hW
  have hinj := W.injective_fst_of_norm_snd_lt hW
  have hsurj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hinj
  obtain ⟨A, hA⟩ := W.exists_eq_graph ⟨hinj, hsurj⟩
  refine ⟨A.toContinuousLinearMap, ?_, hA⟩
  exact A.toContinuousLinearMap.opNorm_lt_one_iff_forall_mem_graph_norm_snd_lt.mpr (hA ▸ hW)

/-- The full-dimensional negative subspaces are exactly the graphs of unique operators in the
open operator-norm unit ball. This is the global graph-coordinate classification. -/
theorem existsUnique_eq_graph_iff_finrank_eq_and_norm_snd_lt (W : Submodule ℝ (E × F)) :
    (∃! A : E →L[ℝ] F, ‖A‖ < 1 ∧ W = A.toLinearMap.graph) ↔
      Module.finrank ℝ W = Module.finrank ℝ E ∧
        ∀ z ∈ W, z ≠ 0 → ‖z.2‖ < ‖z.1‖ := by
  constructor
  · rintro ⟨A, ⟨hA, rfl⟩, -⟩
    refine ⟨?_, A.opNorm_lt_one_iff_forall_mem_graph_norm_snd_lt.mp hA⟩
    rw [LinearMap.graph_eq_range_prod]
    apply LinearMap.finrank_range_of_inj
    intro u v huv
    exact congrArg Prod.fst huv
  · rintro ⟨hdim, hW⟩
    obtain ⟨A, hA, hgraph⟩ := W.exists_eq_graph_of_finrank_eq_of_norm_snd_lt hdim hW
    refine ⟨A, ⟨hA, hgraph⟩, fun B hB ↦ ?_⟩
    ext u
    have hu : (u, B u) ∈ A.toLinearMap.graph := by
      rw [← hgraph, hB.2]
      simp
    exact (LinearMap.mem_graph_iff _ _).mp hu

/-- A full-dimensional negative subspace cannot be enlarged while remaining negative. -/
theorem eq_of_le_of_finrank_eq_of_norm_snd_lt (W V : Submodule ℝ (E × F))
    (hWV : W ≤ V) (hdim : Module.finrank ℝ W = Module.finrank ℝ E)
    (hV : ∀ z ∈ V, z ≠ 0 → ‖z.2‖ < ‖z.1‖) : W = V := by
  have := V.finiteDimensional_of_norm_snd_lt hV
  apply Submodule.eq_of_le_of_finrank_le hWV
  rw [hdim]
  exact V.finrank_le_of_norm_snd_lt hV

end Submodule
