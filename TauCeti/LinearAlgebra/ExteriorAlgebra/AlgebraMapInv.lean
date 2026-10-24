/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis
-- Private: `CliffordAlgebra.contractRight_ι_mul` and
-- `Module.Basis.exteriorAlgebra_eq_prod_map_sort` are used only inside proofs.
import TauCeti.LinearAlgebra.CliffordAlgebra.Contraction
import TauCeti.LinearAlgebra.ExteriorAlgebra.Contraction

/-!
# The constant term of an exterior algebra element

Mathlib's `ExteriorAlgebra.algebraMapInv : ExteriorAlgebra R M →ₐ[R] R` is the algebra
homomorphism killing every generator; it reads off the degree-zero component, the left inverse of
`algebraMap`. This file records how it interacts with the operations that the exterior algebra
inherits from being the Clifford algebra of the zero form: the grade involution and reversion
preserve the constant term, and contracting from the left or from the right against a linear
functional produces the same constant term.

These are the facts that make the scalar part of a Clifford algebra, read through
`CliffordAlgebra.equivExterior`, invariant under the grade involution and reversion, and
cyclic.

## Main results

* `ExteriorAlgebra.algebraMapInv_ι`: generators have constant term zero.
* `ExteriorAlgebra.algebraMapInv_involute` and `ExteriorAlgebra.algebraMapInv_reverse`: the grade
  involution and reversion preserve the constant term.
* `ExteriorAlgebra.algebraMapInv_contractRight`: left and right contraction against the same
  functional have the same constant term.
* `Module.Basis.exteriorAlgebra_repr_empty`: the constant term is the coordinate at the empty index
  set in the basis `Module.Basis.ExteriorAlgebra` attached to any basis of `M`.
-/

public section

universe u v

namespace ExteriorAlgebra

open CliffordAlgebra

variable {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]

/-- A generator of the exterior algebra has constant term zero. -/
@[simp]
theorem algebraMapInv_ι (m : M) : algebraMapInv (ι R m) = 0 := by
  simp [algebraMapInv]

/-- The grade involution preserves the constant term. -/
@[simp]
theorem algebraMapInv_involute (x : ExteriorAlgebra R M) :
    algebraMapInv (involute x) = algebraMapInv x := by
  have h : algebraMapInv.comp (involute (Q := (0 : QuadraticForm R M))) = algebraMapInv :=
    CliffordAlgebra.hom_ext <| LinearMap.ext fun m => by simp
  exact AlgHom.congr_fun h x

/-- Reversion preserves the constant term. -/
@[simp]
theorem algebraMapInv_reverse (x : ExteriorAlgebra R M) :
    algebraMapInv (reverse x) = algebraMapInv x := by
  induction x using CliffordAlgebra.left_induction with
  | algebraMap r => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | ι_mul x m _ =>
    rw [reverse.map_mul, reverse_ι, map_mul, map_mul]
    simp

/-- Contracting from the right or from the left against the same functional `d` gives the same
constant term: both are `d` evaluated on the degree-one component. -/
theorem algebraMapInv_contractRight (d : Module.Dual R M) (x : ExteriorAlgebra R M) :
    algebraMapInv (contractRight x d) = algebraMapInv (contractLeft d x) := by
  induction x using CliffordAlgebra.left_induction with
  | algebraMap r => simp
  | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]
  | ι_mul x m _ =>
    rw [contractRight_ι_mul, contractLeft_ι_mul]
    simp

/-- **The constant term is the coordinate at the empty index set** in the exterior-algebra basis
attached to any basis `b` of `M`: every other basis vector is a product of at least one generator,
so has constant term zero. -/
@[simp]
theorem _root_.Module.Basis.exteriorAlgebra_repr_empty {I : Type*} [LinearOrder I]
    (b : Module.Basis I R M) (x : ExteriorAlgebra R M) :
    b.ExteriorAlgebra.repr x ∅ = algebraMapInv x := by
  refine LinearMap.congr_fun (b.ExteriorAlgebra.ext (f₁ := b.ExteriorAlgebra.coord ∅)
    (f₂ := algebraMapInv.toLinearMap) fun s ↦ ?_) x
  rw [Module.Basis.coord_apply, Module.Basis.repr_self, AlgHom.toLinearMap_apply,
    Module.Basis.exteriorAlgebra_eq_prod_map_sort, map_list_prod, List.map_map, List.map_map]
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp
  · rw [Finsupp.single_apply, ite_eq_right hs.ne_empty, eq_comm]
    obtain ⟨i, hi⟩ := hs
    exact List.prod_eq_zero (List.mem_map.mpr ⟨i, (Finset.mem_sort _).mpr hi, by simp⟩)

end ExteriorAlgebra
