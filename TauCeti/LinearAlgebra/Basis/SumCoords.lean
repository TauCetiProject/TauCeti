/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.Algebra.Module.BigOperators

/-!
# The sum of the coordinates in a basis

For a basis `b`, the linear functional `Module.Basis.sumCoords b` sends a vector to the sum of its
coordinates. For the standard basis of a monoid algebra this is the augmentation. This file records
its image and kernel.

## Main statements

* `Module.Basis.sumCoords_surjective`: the coordinate sum is surjective when the index type is
  nonempty.
* `Module.Basis.exists_repr_ne_of_ne_zero_of_sumCoords_eq_zero`: a nonzero vector whose
  coordinates sum to zero has two distinct coordinates, if the number of basis vectors is a
  regular element of the scalars.
* `Module.Basis.ker_sumCoords_eq_span`: the kernel of the coordinate sum is spanned by the
  differences of the basis vectors from a fixed one.
-/

public section

namespace Module.Basis

variable {ι R M : Type*}

section Semiring

variable [Semiring R] [AddCommMonoid M] [Module R M]

/-- The sum of the coordinates is surjective when the index type is nonempty. -/
theorem sumCoords_surjective [Nonempty ι] (b : Basis ι R M) :
    Function.Surjective b.sumCoords := fun a =>
  ⟨a • b (Classical.arbitrary ι), by simp⟩

/-- A nonzero vector whose coordinates sum to zero has two different coordinates, provided the
number of basis vectors is a regular element of the scalars.

No nonemptiness assumption on `ι` is needed. -/
theorem exists_repr_ne_of_ne_zero_of_sumCoords_eq_zero [Fintype ι] (b : Basis ι R M) {v : M}
    (hcard : IsLeftRegular (Fintype.card ι : R)) (hv0 : v ≠ 0) (hv : b.sumCoords v = 0) :
    ∃ i j : ι, i ≠ j ∧ b.repr v i ≠ b.repr v j := by
  by_contra! hcon
  refine hv0 (b.repr.map_eq_zero_iff.mp (Finsupp.ext fun i => hcard ?_))
  -- Constant coordinates have sum `Fintype.card ι` times their common value.
  have hall : ∀ j, b.repr v j = b.repr v i := fun j =>
    (eq_or_ne j i).elim (fun h => h ▸ rfl) (hcon j i)
  rw [coe_sumCoords_of_fintype] at hv
  simpa [hall] using hv

end Semiring

/-- The kernel of the coordinate sum is spanned by the differences of the basis vectors from a
fixed one. -/
theorem ker_sumCoords_eq_span [Ring R] [AddCommGroup M] [Module R M] (b : Basis ι R M) (i₀ : ι) :
    LinearMap.ker b.sumCoords = Submodule.span R (Set.range fun i => b i - b i₀) := by
  refine le_antisymm (fun v hv => ?_) (Submodule.span_le.mpr ?_)
  · rw [Finsupp.mem_span_range_iff_exists_finsupp]
    refine ⟨b.repr v, ?_⟩
    have hsum := b.linearCombination_repr v
    rw [LinearMap.mem_ker, coe_sumCoords] at hv
    simp only [Finsupp.linearCombination_apply, Finsupp.sum, id_eq] at hsum hv ⊢
    simp [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, hsum, hv]
  · rintro _ ⟨i, rfl⟩
    simp [-coe_sumCoords, sumCoords_self_apply]

end Module.Basis
