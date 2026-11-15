/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Fable 5
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-!
# Spans of orthonormal subfamilies

For a finite-index orthonormal basis and a set of indices, `spanIndices` is the
subspace spanned by the corresponding basis vectors.

## Main results

* `OrthonormalBasis.spanIndices_eq_span`: the explicit span characterization.
* `OrthonormalBasis.span_range_comp_subtypeVal_eq_spanIndices`: the restriction
  `b ∘ (↑) : s → E` of the basis to the coordinate block `s`, an orthonormal family by
  `Orthonormal.comp`, spans the selected subspace.
* `OrthonormalBasis.spanIndices_mono`: monotonicity under index-set inclusion.
* `OrthonormalBasis.mem_spanIndices_of_mem`: selected basis vectors belong to the span.
* `OrthonormalBasis.mem_spanIndices_iff`: membership means coordinates vanish
  outside the selected indices.
* `OrthonormalBasis.finrank_spanIndices_set`: dimension as set cardinality.
* `OrthonormalBasis.finrank_spanIndices`: the dimension for a finset of indices.
* `OrthonormalBasis.orthogonal_spanIndices`: orthogonal complement by index complement.

## Source

Adapted from `ForTauCeti/Analysis/InnerProductSpace/BasisSpan.lean` in the
[AIQ-Kitware DKPS formalization](https://github.com/AIQ-Kitware/aiq-dkps-formalization)
(Kitware, Inc.; Apache-2.0). The selected-span construction originates in the
Courant--Fischer development.
-/

public section

namespace OrthonormalBasis

open Module (finrank)
open scoped InnerProductSpace

variable {𝕜 E ι : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [Fintype ι]

/-- The subspace spanned by the orthonormal basis vectors `b i` for indices
`i ∈ s`. -/
noncomputable def spanIndices (b : OrthonormalBasis ι 𝕜 E) (s : Set ι) :
    Submodule 𝕜 E :=
  Submodule.span 𝕜 (b '' s)

/-- The selected subspace is the span of its basis vectors.
Use this identity to apply `Submodule.span`'s induction or universal property. -/
theorem spanIndices_eq_span (b : OrthonormalBasis ι 𝕜 E) (s : Set ι) :
    b.spanIndices s = Submodule.span 𝕜 (b '' s) := (rfl)

/-- The basis vectors indexed by the coordinate block `s`, as a family indexed by `s`, span the
selected subspace. -/
theorem span_range_comp_subtypeVal_eq_spanIndices (b : OrthonormalBasis ι 𝕜 E) (s : Set ι) :
    Submodule.span 𝕜 (Set.range (b ∘ ((↑) : s → ι))) = b.spanIndices s := by
  rw [spanIndices_eq_span, Set.range_comp, Subtype.range_coe]

/-- Selecting more indices spans more. -/
theorem spanIndices_mono (b : OrthonormalBasis ι 𝕜 E) {s t : Set ι} (h : s ⊆ t) :
    b.spanIndices s ≤ b.spanIndices t := by
  rw [b.spanIndices_eq_span s, b.spanIndices_eq_span t]
  exact Submodule.span_mono (Set.image_mono h)

/-- A selected basis vector lies in the span of its index set. -/
theorem mem_spanIndices_of_mem (b : OrthonormalBasis ι 𝕜 E) {s : Set ι} {i : ι}
    (hi : i ∈ s) : b i ∈ b.spanIndices s := by
  rw [b.spanIndices_eq_span]
  exact Submodule.subset_span ⟨i, hi, rfl⟩

/-- Membership in the span of a selected subfamily is exactly the vanishing of
the coordinates outside the selection. -/
@[simp]
theorem mem_spanIndices_iff (b : OrthonormalBasis ι 𝕜 E)
    {s : Set ι} {x : E} :
    x ∈ b.spanIndices s ↔ ∀ i ∉ s, b.repr x i = 0 := by
  rw [b.spanIndices_eq_span, ← b.coe_toBasis, b.toBasis.mem_span_image]
  simp [Set.subset_def, not_imp_comm]

/-- A vector in the span of a selected subfamily has zero coordinate at any
index outside the selection. -/
theorem repr_eq_zero_of_mem_spanIndices (b : OrthonormalBasis ι 𝕜 E)
    {s : Set ι} {x : E} (hx : x ∈ b.spanIndices s) {i : ι} (hi : i ∉ s) :
    b.repr x i = 0 :=
  b.mem_spanIndices_iff.mp hx i hi

/-- The span of a selected set of basis vectors has dimension equal to the
number of selected indices. -/
theorem finrank_spanIndices_set (b : OrthonormalBasis ι 𝕜 E) (s : Set ι) :
    finrank 𝕜 (b.spanIndices s) = s.ncard := by
  rw [b.spanIndices_eq_span,
    finrank_span_set_eq_ncard (b.orthonormal.linearIndependent.linearIndepOn s).id_image,
    Set.ncard_image_of_injective s b.orthonormal.linearIndependent.injective]

/-- The span of a selected subfamily has dimension the number of selected
indices. -/
theorem finrank_spanIndices (b : OrthonormalBasis ι 𝕜 E) (s : Finset ι) :
    finrank 𝕜 (b.spanIndices ↑s) = s.card := by
  rw [b.finrank_spanIndices_set, Set.ncard_coe_finset]

/-- The span of the basis vectors with index below `n` has rank at most `n`. -/
theorem rank_spanIndices_val_lt_le {m : ℕ} (b : OrthonormalBasis (Fin m) 𝕜 E) (n : ℕ) :
    Module.rank 𝕜 (b.spanIndices ↑({i | (i : ℕ) < n} : Finset (Fin m))) ≤ n := by
  let := Module.Finite.of_basis b.toBasis
  rw [← Module.finrank_eq_rank, b.finrank_spanIndices, Fin.card_filter_val_lt]
  exact_mod_cast min_le_right m n

/-- The orthogonal complement of the span of a selected subfamily is the span
of the complementary subfamily. -/
theorem orthogonal_spanIndices (b : OrthonormalBasis ι 𝕜 E) (s : Set ι) :
    (b.spanIndices s)ᗮ = b.spanIndices sᶜ := by
  ext x
  rw [b.mem_spanIndices_iff, b.spanIndices_eq_span]
  -- Membership in `Kᗮ` is, by definition, membership in `K.orthogonalBilin (innerₛₗ 𝕜)`, for which
  -- the simp lemma `Submodule.mem_orthogonalBilin_span` reduces to the spanning vectors.
  change x ∈ (Submodule.span 𝕜 (b '' s)).orthogonalBilin (innerₛₗ 𝕜) ↔ _
  simp [b.repr_apply_apply]

/-- A vector orthogonal to the first `n` basis vectors lies in the remaining span. -/
theorem mem_spanIndices_le_of_mem_orthogonal {m : ℕ} (b : OrthonormalBasis (Fin m) 𝕜 E)
    {n : ℕ} {x : E}
    (hx : x ∈ (b.spanIndices ↑({i | (i : ℕ) < n} : Finset (Fin m)))ᗮ) :
    x ∈ b.spanIndices {i | n ≤ (i : ℕ)} := by
  refine b.spanIndices_mono (fun i hi ↦ ?_) ((b.orthogonal_spanIndices _).le hx)
  simpa using hi

end OrthonormalBasis

end
