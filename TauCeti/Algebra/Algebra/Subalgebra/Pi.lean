/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Pi
public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.IntegralClosure.Algebra.Defs
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.Group.Pi.Units
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic

/-!
# Subalgebras of product algebras

This file collects structural results about subalgebras of product algebras `∀ i, B i` and `ι → K`.

## Units in subalgebras of integral algebras and finite products

Let `O` be a commutative ring, `B` a commutative `O`-algebra integral over `O`, and
`A : Subalgebra O B` an `O`-subalgebra. Since `O → B` is integral, the inclusion `A ↪ B` is also
integral and injective, hence a local homomorphism (`RingHom.IsIntegral.isLocalHom`). Therefore
an element `y ∈ A` is a unit in `A` if and only if `(y : B)` is a unit in `B`
(`Subalgebra.isUnit_iff_isUnit_val_of_isIntegral`).

In particular, for a family `B : ι → Type*` of commutative `O`-algebras with `∀ i, B i` integral
over `O`, `y ∈ A` is a unit in `A` if and only if every coordinate `y i` is a unit in `B i`
(`Subalgebra.isUnit_iff_forall_isUnit_apply_of_isIntegral`). When `ι` is finite and each `B i` is
a finite `O`-module, the product `∀ i, B i` is finite and hence integral over `O`, yielding the
finite-product criterion `Subalgebra.isUnit_iff_forall_isUnit_apply` and the homogeneous
finite-product criterion `Subalgebra.isUnit_iff_isUnit_prod`.

## Point-separating subalgebras of a finite product of a field

For a field `K` and a finite type `ι`, a subalgebra of `ι → K` that separates the points of `ι`
(Mathlib's `Set.SeparatesPoints`) is everything (`Subalgebra.eq_top_of_separatesPoints`). This
is the finite, purely algebraic form of the Stone–Weierstrass theorem. The proof is Lagrange
interpolation: for each `j ≠ i` some affine function of an element of the subalgebra is `1` at
`i` and `0` at `j`, and the product of these is the indicator `Pi.single i 1` of `i`
(`Subalgebra.single_one_mem_of_separatesPoints`).

## Main results

* `Subalgebra.isUnit_iff_isUnit_val_of_isIntegral`: an element of a subalgebra of an integral
  `O`-algebra `B` is a unit in the subalgebra if and only if it is a unit in `B`.
* `Subalgebra.isUnit_iff_forall_isUnit_apply_of_isIntegral`: an element of a subalgebra of an
  integral product algebra `∀ i, B i` is a unit if and only if all of its coordinates are units.
* `Subalgebra.isUnit_iff_forall_isUnit_apply`: an element of a subalgebra of a finite product
  `∀ i, B i` of finite `O`-algebras is a unit if and only if all of its coordinates are units.
* `Subalgebra.isUnit_iff_isUnit_prod`: product criterion for units in a subalgebra of `ι → B` for
  a finite `O`-algebra `B` (in particular `ι → O`).
* `Subalgebra.single_one_mem_of_separatesPoints`: a point-separating subalgebra of `ι → K`
  contains every indicator `Pi.single i 1`.
* `Subalgebra.eq_top_of_separatesPoints`: finite Stone–Weierstrass theorem.
-/

public section

namespace Subalgebra

section IsUnit

variable {O : Type*} [CommRing O]

/-- **Units in a subalgebra of an integral algebra**: if `B` is integral over `O` and
`A : Subalgebra O B`, an element `y ∈ A` is a unit in `A` if and only if `(y : B)` is a unit in
`B`. -/
theorem isUnit_iff_isUnit_val_of_isIntegral {B : Type*} [CommRing B] [Algebra O B]
    [Algebra.IsIntegral O B] {A : Subalgebra O B} {y : A} :
    IsUnit y ↔ IsUnit (y : B) := by
  have hint : (A.val : A →+* B).IsIntegral :=
    RingHom.IsIntegral.tower_top (algebraMap O A) (A.val : A →+* B) <| by
      simpa [A.val.comp_algebraMap] using
        (algebraMap_isIntegral_iff.mpr (inferInstance : Algebra.IsIntegral O B))
  have : IsLocalHom (A.val : A →+* B) := hint.isLocalHom Subtype.val_injective
  exact (isUnit_map_iff (A.val : A →+* B) y).symm

/-- **Units in a subalgebra of an integral product algebra**: if `∀ i, B i` is integral over `O`
and `A : Subalgebra O (∀ i, B i)`, an element `y ∈ A` is a unit in `A` if and only if every
coordinate `y i` is a unit in `B i`. -/
theorem isUnit_iff_forall_isUnit_apply_of_isIntegral {ι : Type*} {B : ι → Type*}
    [∀ i, CommRing (B i)] [∀ i, Algebra O (B i)] [Algebra.IsIntegral O (∀ i, B i)]
    {A : Subalgebra O (∀ i, B i)} {y : A} :
    IsUnit y ↔ ∀ i : ι, IsUnit ((y : ∀ i, B i) i) :=
  isUnit_iff_isUnit_val_of_isIntegral.trans Pi.isUnit_iff

/-- **Units in a subalgebra of a finite product**: for a finite index type `ι`, finite
`O`-algebras `B i`, and a subalgebra `A : Subalgebra O (∀ i, B i)`, an element `y ∈ A` is a unit in
`A` if and only if every coordinate `y i` is a unit in `B i`. -/
theorem isUnit_iff_forall_isUnit_apply [Finite ι] {B : ι → Type*} [∀ i, CommRing (B i)]
    [∀ i, Algebra O (B i)] [∀ i, Module.Finite O (B i)] {A : Subalgebra O (∀ i, B i)} {y : A} :
    IsUnit y ↔ ∀ i : ι, IsUnit ((y : ∀ i, B i) i) := by
  have : Algebra.IsIntegral O (∀ i, B i) := Algebra.IsIntegral.of_finite O (∀ i, B i)
  exact isUnit_iff_forall_isUnit_apply_of_isIntegral

/-- **Product criterion for units in a subalgebra of a finite product**: for a finite index type
`ι`, a finite `O`-algebra `B`, and `A : Subalgebra O (ι → B)`, `y ∈ A` is a unit in `A` if and only
if the product `∏ i, y i` is a unit in `B`. -/
theorem isUnit_iff_isUnit_prod [Fintype ι] {B : Type*} [CommRing B] [Algebra O B]
    [Module.Finite O B] {A : Subalgebra O (ι → B)} {y : A} :
    IsUnit y ↔ IsUnit (∏ i : ι, (y : ι → B) i) := by
  rw [isUnit_iff_forall_isUnit_apply, IsUnit.prod_univ_iff]

end IsUnit

section SeparatesPoints

variable {K ι : Type*} [Field K] [Finite ι] {S : Subalgebra K (ι → K)}

/-- A subalgebra of `ι → K` that separates the points of the finite type `ι` contains the
indicator function of each point. -/
theorem single_one_mem_of_separatesPoints [DecidableEq ι]
    (h : (S : Set (ι → K)).SeparatesPoints) (i : ι) : Pi.single i (1 : K) ∈ S := by
  have := Fintype.ofFinite ι
  -- for each `j ≠ i`, a function in `S` that is `1` at `i` and `0` at `j`
  have hfactor : ∀ j, ∃ g ∈ S, g i = 1 ∧ (i ≠ j → g j = 0) := by
    intro j
    by_cases hij : i = j
    · exact ⟨1, S.one_mem, rfl, fun h => absurd hij h⟩
    obtain ⟨f, hf, hfij⟩ := h hij
    refine ⟨(f i - f j)⁻¹ • (f - algebraMap K _ (f j)),
      S.smul_mem (S.sub_mem hf (S.algebraMap_mem _)) _, ?_, fun _ => ?_⟩ <;>
    simp only [Pi.smul_apply, Pi.sub_apply, Pi.algebraMap_apply, Algebra.algebraMap_self,
      RingHom.id_apply, smul_eq_mul, sub_self, mul_zero, inv_mul_cancel₀ (sub_ne_zero.mpr hfij)]
  choose g hgS hgi hgj using hfactor
  -- Lagrange interpolation: the indicator of `i` is the product of these functions
  have hprod : Pi.single i 1 = ∏ j, g j := by
    funext k
    rw [Finset.prod_apply]
    by_cases hk : k = i
    · subst hk
      rw [Pi.single_eq_same, eq_comm]
      exact Finset.prod_eq_one fun j _ => hgi j
    · rw [Pi.single_eq_of_ne hk, eq_comm]
      exact Finset.prod_eq_zero (Finset.mem_univ k) (hgj k (Ne.symm hk))
  exact hprod ▸ S.prod_mem fun j _ => hgS j

/-- **Finite Stone–Weierstrass theorem.** A subalgebra of `ι → K` that separates the points of
the finite type `ι` is `⊤`. -/
theorem eq_top_of_separatesPoints (h : (S : Set (ι → K)).SeparatesPoints) : S = ⊤ := by
  classical
  have := Fintype.ofFinite ι
  refine eq_top_iff.mpr fun f _ => ?_
  rw [← Finset.univ_sum_single f]
  refine S.sum_mem fun i _ => ?_
  rw [← mul_one (f i), ← smul_eq_mul, Pi.single_smul']
  exact S.smul_mem (single_one_mem_of_separatesPoints h i) _

end SeparatesPoints

end Subalgebra
