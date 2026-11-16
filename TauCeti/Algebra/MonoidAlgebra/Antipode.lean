/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.HopfAlgebra.MonoidAlgebra
public import TauCeti.Algebra.MonoidAlgebra.SubgroupCharSum

/-!
# The antipode of a group algebra

The group algebra `k[G]` of a group is a Hopf algebra whose antipode `S` is the linear extension
of inversion, `S(g) = g⁻¹` (`MonoidAlgebra.antipode_single`); it reverses products. This file
records how `S` interacts with the operations that move elements between group algebras: it
commutes with mapping the coefficients along a ring homomorphism `k → K` and with transporting
along an isomorphism of groups, and it fixes the character sum `∑_{h ∈ H} χ(h) h` of a character
that takes the same value on `h` and `h⁻¹`.

Through `v · g = g⁻¹ v`, a representation becomes a right module over `k[G]`, and an element `x`
acts on the right as `S(x)` acts on the left. This is how the antipode enters tensor products
over a group algebra; the norm element and the signed sum of a subgroup of a permutation group,
the two factors of a Young symmetrizer, are both fixed by `S`.

## Main results

* `MonoidAlgebra.antipode_mapRingHom`, `MonoidAlgebra.antipode_mapAlgHom` and
  `MonoidAlgebra.antipode_domCongr`: the antipode commutes with mapping the coefficients and with
  transport along a group isomorphism.
* `TauCeti.antipode_subgroupCharSum`: the antipode fixes `∑_{h ∈ H} χ(h) h` when `χ(h⁻¹) = χ(h)`
  on `H`.
-/

public section

namespace MonoidAlgebra

/-- The antipode commutes with mapping the coefficients of a group algebra along a ring
homomorphism. -/
@[simp]
theorem antipode_mapRingHom {k K G : Type*} [CommSemiring k] [CommSemiring K] [Group G]
    (f : k →+* K) (x : MonoidAlgebra k G) :
    HopfAlgebra.antipode K (mapRingHom G f x) = mapRingHom G f (HopfAlgebra.antipode k x) := by
  induction x using induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | single g r => simp

/-- The antipode commutes with mapping the coefficients of a group algebra along an algebra
homomorphism. -/
@[simp]
theorem antipode_mapAlgHom {R A B G : Type*} [CommSemiring R] [CommSemiring A] [CommSemiring B]
    [Algebra R A] [Algebra R B] [Group G] (f : A →ₐ[R] B) (x : MonoidAlgebra A G) :
    HopfAlgebra.antipode B (mapAlgHom G f x) = mapAlgHom G f (HopfAlgebra.antipode A x) :=
  antipode_mapRingHom f.toRingHom x

/-- The antipode commutes with transport along an isomorphism of groups. -/
@[simp]
theorem antipode_domCongr {R S A G H : Type*} [CommSemiring R] [CommSemiring S] [Semiring A]
    [HopfAlgebra R A] [Algebra S A] [Group G] [Group H] (e : G ≃* H) (x : MonoidAlgebra A G) :
    HopfAlgebra.antipode R (domCongr S A e x) = domCongr S A e (HopfAlgebra.antipode R x) := by
  induction x using induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | single g r => simp

end MonoidAlgebra

namespace TauCeti

/-- **The antipode fixes a character sum** `∑_{h ∈ H} χ(h) h` when the character takes the same
value on each element of `H` and on its inverse, as the trivial character and the sign character
of a permutation group do. -/
theorem antipode_subgroupCharSum {k G : Type*} [CommSemiring k] [Group G] (χ : G →* k)
    (H : Subgroup G) [Fintype H] (hχ : ∀ h ∈ H, χ h⁻¹ = χ h) :
    HopfAlgebra.antipode k (subgroupCharSum χ H) = subgroupCharSum χ H := by
  rw [subgroupCharSum_def, map_sum]
  refine Fintype.sum_equiv (Equiv.inv H) _ _ fun h => ?_
  simp [MonoidAlgebra.of_apply, hχ h h.2]

end TauCeti
