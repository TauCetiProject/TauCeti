/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Vectors
public import Mathlib.LinearAlgebra.CliffordAlgebra.SpinGroup

/-!
# Vector generators of the Lipschitz group

This file packages a vector of invertible quadratic norm as a Clifford-algebra unit and records
the corresponding generator membership and inverse coercion facts.  The twisted-conjugation
action itself is defined in `Lipschitz.Action`.

## Main definitions

* `CliffordAlgebra.unitι Q v` is the unit represented by a vector `v` of invertible norm.
* `CliffordAlgebra.unitι_mem_lipschitzGroup` records that this unit generates the Lipschitz group.
* `CliffordAlgebra.coe_unitι_inv` computes its inverse as a vector.
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

end CliffordAlgebra
