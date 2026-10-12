/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.GrothendieckGroup.Finrank
public import TauCeti.RepresentationTheory.GrothendieckGroup.GroupAlgebra.Induction
public import TauCeti.RepresentationTheory.GrothendieckGroup.GroupAlgebra.Ring
public import TauCeti.GroupTheory.Index.PrimePart
import TauCeti.RepresentationTheory.AsModule

/-!
# Dimension and induction in the Grothendieck group of a group algebra

For a finite group `G` over a field `k`, dimension sends the unit of `G₀(k[G])` to one.
Induction from a subgroup `S` multiplies dimension by the index `[G : S]`. In particular,
every class induced from `S` has dimension divisible by this index, even for virtual classes
of negative dimension and in characteristic dividing the group order.

The induction formula transports `TauCeti.finrank_indFDRep` through the existing dictionary
between finite-dimensional representations and finitely generated group-algebra modules.
These dimension constraints detect necessary multipliers in induction theorems.

## References

* J.-P. Serre, *Linear Representations of Finite Groups*, §7.1 and §14.1.
-/

public section

open scoped MonoidAlgebra

namespace TauCeti

universe u

section Monoid

variable {k G : Type u} [Field k] [Monoid G] [Finite G]

/-- The dimension of the unit of the group-algebra Grothendieck ring is one. -/
@[simp]
theorem finrankK0_one :
    finrankK0 k k[G] (1 : ExactK0 (finiteModulesExactStructure k[G])) = 1 := by
  rw [exactK0_one_eq_of_trivial, finrankK0_of]
  exact_mod_cast ((Representation.finrank_moduleCat_asModule
    (Representation.trivial k G k)).trans
    (Module.finrank_self k))

/-- The class of a finite-dimensional representation has its usual dimension under the
group-algebra dictionary. -/
theorem finrankK0_fdRepK0RingEquiv_of (V : FDRep k G) :
    finrankK0 k k[G] (fdRepK0RingEquiv k G (ExactK0.of V)) = Module.finrank k V := by
  rw [fdRepK0RingEquiv_of, finrankK0_of]
  -- `finrankK0_of` uses the scalar structure supplied by the bundled module, so the
  -- dimension comparison must use the bundled-module transport rather than `asModuleEquiv`.
  exact_mod_cast Representation.finrank_moduleCat_asModule V.ρ

end Monoid

variable {k G : Type u} [Field k] [Group G] [Finite G]

/-- Induction multiplies the dimension of any virtual class by the subgroup index. -/
@[simp]
theorem finrankK0_indK0 (S : Subgroup G)
    (x : ExactK0 (finiteModulesExactStructure k[S])) :
    finrankK0 k k[G] (indK0 k S x) = (S.index : ℤ) * finrankK0 k k[S] x := by
  obtain ⟨y, rfl⟩ := (fdRepK0RingEquiv k S).surjective x
  induction y using ExactK0.induction_on with
  | zero => simp
  | of V =>
    rw [finrankK0_fdRepK0RingEquiv_of, fdRepK0RingEquiv_of, indK0_of_indFDRep,
      ← fdRepK0RingEquiv_of, finrankK0_fdRepK0RingEquiv_of, finrank_indFDRep, Nat.cast_mul]
  | add a b ha hb => simp_all [mul_add]
  | neg a ha => simp_all

/-- The dimension of an induced class is divisible by the subgroup index. -/
theorem index_dvd_finrankK0_of_mem_range_indK0 (S : Subgroup G)
    {x : ExactK0 (finiteModulesExactStructure k[G])} (hx : x ∈ (indK0 k S).range) :
    (S.index : ℤ) ∣ finrankK0 k k[G] x := by
  obtain ⟨y, rfl⟩ := hx
  exact ⟨finrankK0 k k[S] y, finrankK0_indK0 S y⟩

end TauCeti

namespace Subgroup

open TauCeti
open scoped MonoidAlgebra

/-- A class induced from a subgroup of order prime to `p` has dimension divisible by
the `p`-part of the group order, in every characteristic. -/
theorem ordProj_dvd_finrankK0_indK0 {k G : Type u} [Field k] [Group G] [Finite G]
    (S : Subgroup G) {p : ℕ} (hp : p.Prime) (hS : ¬ p ∣ Nat.card S)
    (y : ExactK0 (finiteModulesExactStructure k[S])) :
    (ordProj[p] (Nat.card G) : ℤ) ∣ finrankK0 k k[G] (indK0 k S y) := by
  rw [finrankK0_indK0]
  exact dvd_mul_of_dvd_left (Int.natCast_dvd_natCast.mpr
    (S.ordProj_natCard_dvd_index hp hS)) _

end Subgroup
