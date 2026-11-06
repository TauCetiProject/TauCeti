/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.Algebra.BigOperators.Fin

/-!
# Linear independence of a concatenated family

Let `f : M →ₗ[R] N` be a linear map. If a family `a` of vectors of `M` is linearly independent and
killed by `f`, and the images under `f` of a second family `b` are linearly independent, then the
concatenation `Fin.append a b` is linearly independent. This is how a basis is assembled along an
exact sequence `0 → U → V → W`: a basis of `U` followed by lifts to `V` of a basis of the image.

## Main results

* `LinearIndependent.fin_append_of_map_eq_zero`: the concatenation of a linearly independent
  family in the kernel of `f` with a family whose image under `f` is linearly independent is
  linearly independent.
-/

public section

open Function

/-- **Linear independence along a linear map.** If `a` is a linearly independent family killed by
`f`, and the images under `f` of the family `b` are linearly independent, then the concatenation
`Fin.append a b` is linearly independent. -/
theorem LinearIndependent.fin_append_of_map_eq_zero {R M N : Type*} [Ring R] [AddCommGroup M]
    [Module R M] [AddCommGroup N] [Module R N] {m n : ℕ} {a : Fin m → M} {b : Fin n → M}
    (f : M →ₗ[R] N) (ha : LinearIndependent R a) (hfa : ∀ i, f (a i) = 0)
    (hb : LinearIndependent R (f ∘ b)) : LinearIndependent R (Fin.append a b) := by
  rw [Fintype.linearIndependent_iff] at ha hb ⊢
  intro g hg
  rw [Fin.sum_univ_add] at hg
  simp only [Fin.append_left, Fin.append_right] at hg
  -- Applying `f` kills the first block, so the coefficients of the second block vanish.
  have hright : ∀ j, g (Fin.natAdd m j) = 0 :=
    hb _ (by simpa [map_add, map_sum, map_smul, hfa] using congrArg f hg)
  have hleft : ∀ j, g (Fin.castAdd n j) = 0 := ha _ (by simpa [hright] using hg)
  intro i
  cases i using Fin.addCases with
  | left j => exact hleft j
  | right j => exact hright j
