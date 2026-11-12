/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Fable 5, GPT-6
-/
module

public import TauCeti.Analysis.InnerProductSpace.BasisSpan
public import TauCeti.Analysis.InnerProductSpace.Orthonormal.Family

/-!
# Projections onto selected orthonormal-basis spans

Parseval's identity for a finite orthonormal family computes the squared norm
of the projection onto a coordinate block. The complementary coordinate block
spans the orthogonal complement of the selected span.

## Main result

* `OrthonormalBasis.norm_starProjection_orthogonal_spanIndices_sq`: the
  complementary projection norm as a sum of squared inner products.

## Source

The selected-span construction is adapted from the AIQ-Kitware DKPS
formalization (`ForTauCeti/Analysis/InnerProductSpace/BasisSpan.lean`,
Apache-2.0). This proof specializes the orthonormal-family Parseval identity.
-/

public section

namespace OrthonormalBasis

open scoped InnerProductSpace

variable {𝕜 E ι : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [Fintype ι]

/-- The squared norm of the orthogonal projection onto the complement of a
selected coordinate block equals the sum of squared inner products with the
complementary basis vectors. -/
theorem norm_starProjection_orthogonal_spanIndices_sq [DecidableEq ι]
    (b : OrthonormalBasis ι 𝕜 E) (s : Finset ι) (x : E) :
    letI : FiniteDimensional 𝕜 E := Module.Finite.of_basis b.toBasis
    ‖(b.spanIndices (↑s : Set ι))ᗮ.starProjection x‖ ^ 2 =
      ∑ k ∈ sᶜ, ‖⟪b k, x⟫_𝕜‖ ^ 2 := by
  have : FiniteDimensional 𝕜 E := Module.Finite.of_basis b.toBasis
  have hcompl :
      Submodule.span 𝕜 (Set.range (b ∘ ((↑) : (sᶜ : Finset ι) → ι))) =
        (b.spanIndices (↑s : Set ι))ᗮ := by
    rw [b.orthogonal_spanIndices, ← Finset.coe_compl,
      b.span_range_comp_subtypeVal_eq_spanIndices]
  rw [(b.orthonormal.comp _ Subtype.val_injective).norm_starProjection_sq_eq_sum hcompl]
  exact Finset.sum_coe_sort sᶜ fun k ↦ ‖⟪b k, x⟫_𝕜‖ ^ 2

end OrthonormalBasis
