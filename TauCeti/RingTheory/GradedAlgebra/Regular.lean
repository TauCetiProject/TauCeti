/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.GradedAlgebra.Basic

/-!
# Cancelling a homogeneous regular element in a graded ring

In a graded ring, multiplication by a homogeneous element `a` of degree `i` shifts every
homogeneous component by `i`. If `a` is moreover left regular, then the components of `b` can be
read off from those of `a * b`; in particular, if `a * b` is homogeneous of degree `i + j`, then
`b` is homogeneous of degree `j`. For instance, dividing a homogeneous polynomial by a linear form
that divides it produces a homogeneous polynomial of one degree less.

## Main results

* `TauCeti.GradedAlgebra.mem_of_mul_mem_add_of_isLeftRegular`: if `a ∈ 𝒜 i` is left regular and
  `a * b ∈ 𝒜 (i + j)`, then `b ∈ 𝒜 j`.
-/

public section

namespace TauCeti.GradedAlgebra

open DirectSum

variable {A ι σ : Type*} [AddLeftCancelMonoid ι] [DecidableEq ι] [Semiring A] [SetLike σ A]
  [AddSubmonoidClass σ A] (𝒜 : ι → σ) [GradedRing 𝒜]

/-- **Cancelling a homogeneous regular factor.** If `a` is homogeneous of degree `i` and left
regular, and `a * b` is homogeneous of degree `i + j`, then `b` is homogeneous of degree `j`. -/
theorem mem_of_mul_mem_add_of_isLeftRegular {a b : A} {i j : ι} (ha : a ∈ 𝒜 i)
    (hreg : IsLeftRegular a) (hab : a * b ∈ 𝒜 (i + j)) : b ∈ 𝒜 j := by
  -- Every component of `b` away from degree `j` is killed by `a`, hence vanishes.
  have hk (k : ι) (hk : k ≠ j) : decompose 𝒜 b k = 0 := Subtype.ext <| by
    rw [ZeroMemClass.coe_zero, ← hreg.mul_left_eq_zero_iff,
      ← coe_decompose_mul_add_of_left_mem 𝒜 ha,
      decompose_of_mem_ne 𝒜 hab ((add_right_injective i).ne hk.symm)]
  have hb : decompose 𝒜 b = DirectSum.of _ j (decompose 𝒜 b j) := by
    ext k : 1
    by_cases hkj : k = j
    · subst hkj
      rw [DirectSum.of_eq_same]
    · rw [hk k hkj, DirectSum.of_eq_of_ne _ _ _ hkj]
  rw [← (decompose 𝒜).symm_apply_apply b, hb, decompose_symm_of]
  exact (decompose 𝒜 b j).2

end TauCeti.GradedAlgebra
