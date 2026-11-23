/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Vectors with finite-dimensional span of images

For a family of linear maps `T : ι → M →ₗ[k] N` over a field, the vectors `x` whose images
`T i x` span a finite-dimensional subspace form a submodule `TauCeti.finiteSpanRangeSubmodule T`.
The `G`-finite vectors of a representation `ρ` (`Representation.gFiniteSubmodule`) are the case of
the family `ρ`. For the family of right translations of continuous functions on a topological
monoid, this submodule contains the representative functions
(`TauCeti.finiteDimensional_span_range_comp_mulRight`).

## Main definitions

* `TauCeti.finiteSpanRangeSubmodule T`: the submodule of vectors `x` whose images `T i x` span a
  finite-dimensional subspace.

## Main statements

* `TauCeti.mem_finiteSpanRangeSubmodule`: membership unfolds to finite-dimensionality of the span.
-/

public section

namespace TauCeti

variable {k ι M N : Type*} [Field k] [AddCommGroup M] [Module k M] [AddCommGroup N] [Module k N]

/-- For a family of linear maps `T`, the vectors `x` whose images `T i x` span a finite-dimensional
subspace form a submodule. -/
def finiteSpanRangeSubmodule (T : ι → M →ₗ[k] N) : Submodule k M where
  carrier := {x | FiniteDimensional k (Submodule.span k (Set.range fun i => T i x))}
  zero_mem' := Submodule.finiteDimensional_of_le (S₂ := ⊥)
    (Submodule.span_le.2 (Set.range_subset_iff.2 fun i => by simp))
  add_mem' {x y} hx hy := by
    rw [Set.mem_ofPred_eq] at hx hy ⊢
    refine Submodule.finiteDimensional_of_le (S₂ := Submodule.span k (Set.range fun i => T i x) ⊔
      Submodule.span k (Set.range fun i => T i y)) (Submodule.span_le.2 ?_)
    rintro _ ⟨i, rfl⟩
    simp only [SetLike.mem_coe, map_add]
    exact Submodule.add_mem_sup (Submodule.subset_span ⟨i, rfl⟩) (Submodule.subset_span ⟨i, rfl⟩)
  smul_mem' c x hx := by
    rw [Set.mem_ofPred_eq] at hx ⊢
    refine Submodule.finiteDimensional_of_le
      (S₂ := Submodule.span k (Set.range fun i => T i x)) (Submodule.span_le.2 ?_)
    rintro _ ⟨i, rfl⟩
    simp only [SetLike.mem_coe, map_smul]
    exact Submodule.smul_mem _ c (Submodule.subset_span ⟨i, rfl⟩)

/-- Membership in `finiteSpanRangeSubmodule T`: the images `T i x` span a finite-dimensional
subspace. -/
@[simp]
theorem mem_finiteSpanRangeSubmodule {T : ι → M →ₗ[k] N} {x : M} :
    x ∈ finiteSpanRangeSubmodule T ↔
      FiniteDimensional k (Submodule.span k (Set.range fun i => T i x)) :=
  (Iff.rfl)

end TauCeti
