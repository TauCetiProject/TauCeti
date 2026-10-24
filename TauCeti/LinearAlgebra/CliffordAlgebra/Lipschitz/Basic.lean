/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.CliffordAlgebra.Inversion
public import TauCeti.LinearAlgebra.CliffordAlgebra.Vectors
public import Mathlib.LinearAlgebra.CliffordAlgebra.SpinGroup
import TauCeti.RingTheory.GradedAlgebra.Basic

/-!
# Vector generators of the Lipschitz group

This file packages a vector of invertible quadratic norm as a Clifford-algebra unit and records
the corresponding generator membership and inverse coercion facts, together with the triviality
of the Lipschitz group of the zero module.  The twisted-conjugation action itself is defined in
`Lipschitz.Action`.

Since the generators are vectors, and the inverse of a homogeneous unit is homogeneous, every
element of the Lipschitz group is homogeneous for the `ℤ/2`-grading `CliffordAlgebra.evenOdd` of
the Clifford algebra.

## Main definitions

* `CliffordAlgebra.unitι Q v` is the unit represented by a vector `v` of invertible norm.
* `CliffordAlgebra.unitι_mem_lipschitzGroup` records that this unit generates the Lipschitz group.
* `CliffordAlgebra.coe_unitι_inv` computes its inverse as a vector.
* `CliffordAlgebra.lipschitzGroup_eq_bot` records that the Lipschitz group of the zero module is
  trivial.
* `lipschitzGroup.exists_mem_evenOdd`: every element of the Lipschitz group is homogeneous of
  some parity.
-/

public section

universe u v

namespace CliffordAlgebra

variable {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
  (Q : QuadraticForm R M)

/-- A vector of invertible norm, as a unit of the Clifford algebra. -/
def unitι (v : M) [Invertible (Q v)] : (CliffordAlgebra Q)ˣ :=
  letI := invertibleιOfInvertible Q v
  unitOfInvertible (ι Q v)

variable {Q}

@[simp]
theorem coe_unitι (v : M) [Invertible (Q v)] : (unitι Q v : CliffordAlgebra Q) = ι Q v := by
  rw [unitι]
  rfl

/-- The inverse of a vector of invertible norm `v` is the vector `⅟(Q v) • v`. -/
@[simp]
theorem coe_unitι_inv (v : M) [Invertible (Q v)] :
    (((unitι Q v)⁻¹ : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) = ι Q (⅟(Q v) • v) := by
  let _ := invertibleιOfInvertible Q v
  rw [← invOf_ι Q v]
  exact Units.inv_eq_of_mul_eq_one_left (by rw [coe_unitι, invOf_mul_self])

/-- The vectors of invertible norm are the generators of the Lipschitz group. -/
theorem unitι_mem_lipschitzGroup (v : M) [Invertible (Q v)] : unitι Q v ∈ lipschitzGroup Q := by
  unfold lipschitzGroup
  exact Subgroup.subset_closure ⟨v, (coe_unitι v).symm⟩

/-- The Lipschitz group of a quadratic form on the zero module is trivial: its only vector is `0`,
which is not a unit unless the Clifford algebra is itself trivial. -/
theorem lipschitzGroup_eq_bot [Subsingleton M] : lipschitzGroup Q = ⊥ := by
  rw [lipschitzGroup, Subgroup.closure_eq_bot_iff]
  rintro x ⟨m, hm⟩
  rw [Subsingleton.elim m 0, map_zero] at hm
  have : Subsingleton (CliffordAlgebra Q) := subsingleton_of_zero_eq_one (by
    rw [← x.mul_inv, ← hm, zero_mul])
  exact Subsingleton.elim x 1

/-- **Elements of the Lipschitz group are homogeneous.** Every element of the Lipschitz group lies
in one of the two pieces of the `ℤ/2`-grading of the Clifford algebra, being a product of vectors
and their inverses. -/
theorem _root_.lipschitzGroup.exists_mem_evenOdd {x : (CliffordAlgebra Q)ˣ}
    (hx : x ∈ lipschitzGroup Q) : ∃ p : ZMod 2, (x : CliffordAlgebra Q) ∈ evenOdd Q p := by
  induction hx using Subgroup.closure_induction'' with
  | mem x hx =>
    obtain ⟨m, hm⟩ := hx
    exact ⟨1, hm ▸ ι_mem_evenOdd_one Q m⟩
  | inv_mem x hx =>
    -- The inverse of the odd unit `x` is odd: cancel `x` from `x * x⁻¹ = 1 ∈ evenOdd Q (1 + 1)`.
    obtain ⟨m, hm⟩ := hx
    refine ⟨1, TauCeti.GradedAlgebra.mem_of_mul_mem_add_of_isLeftRegular (evenOdd Q)
      (hm ▸ ι_mem_evenOdd_one Q m) x.isUnit.isRegular.left ?_⟩
    rw [Units.mul_inv]
    exact SetLike.one_mem_graded (evenOdd Q)
  | one => exact ⟨0, SetLike.GradedOne.one_mem⟩
  | mul x y _ _ hx hy =>
    obtain ⟨p, hp⟩ := hx
    obtain ⟨q, hq⟩ := hy
    exact ⟨p + q, SetLike.GradedMul.mul_mem hp hq⟩

end CliffordAlgebra
