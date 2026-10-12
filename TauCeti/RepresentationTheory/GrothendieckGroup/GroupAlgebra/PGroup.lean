/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.GrothendieckGroup.GroupAlgebra.PowerOrder
public import TauCeti.RepresentationTheory.GrothendieckGroup.GroupAlgebra.Finrank

/-!
# The Grothendieck group of a finite `p`-group in characteristic `p`

Let `G` be a finite `p`-group and `k` a field of characteristic `p`. Every simple `k[G]`-module
is isomorphic to the trivial line. Consequently the dimension homomorphism identifies the exact
Grothendieck group of finitely generated `k[G]`-modules with `ℤ`: the class of any module is its
dimension times the class of the trivial line. These are exact-sequence relations, so they also
apply to modules which are not direct sums of trivial representations.

Induction from any subgroup `S` has image exactly the classes of dimension divisible by
`[G : S]`. In particular, an integer multiple of the trivial class is induced from the
trivial subgroup if and only if the group order divides that integer. Thus the group order
is the least positive induction multiplier for a `p`-group in characteristic `p`.

The simple-module statement specializes `TauCeti.nonempty_linearEquiv_trivial_of_forall_pow_eq_one`
from `TauCeti/RepresentationTheory/GrothendieckGroup/GroupAlgebra/PowerOrder.lean`. The
Grothendieck-group statements specialize `TauCeti.eq_finrankK0_smul_of_finrank_eq_one` and
`TauCeti.finrankK0Equiv`, using the trivial representation's existing `asModule` construction
rather than another model of the trivial module.

## Main results

* `TauCeti.nonempty_linearEquiv_trivial_of_isPGroup`: every simple module is the trivial line.
* `TauCeti.eq_finrankK0_smul_trivial_of_isPGroup`: dimension determines every class.
* `TauCeti.pGroupFinrankK0Equiv`: dimension is an additive equivalence with `ℤ`.
* `TauCeti.mem_range_indK0_iff_of_isPGroup`: the image of induction is detected by dimension.
* `TauCeti.nsmul_one_mem_range_indK0_bot_iff_of_isPGroup`: the optimal induction multiplier.

## References

* J.-P. Serre, *Linear Representations of Finite Groups*, Part III, §14.
* P. Webb, *A Course in Finite Group Representation Theory*.
-/

public section

open scoped MonoidAlgebra ModuleCat

namespace TauCeti

universe u v

variable {k : Type u} {G : Type v} [Field k] [Group G] [Finite G]
  (p : ℕ) [Fact p.Prime] [CharP k p]

/-- Every simple module over the group algebra of a finite `p`-group in characteristic `p`
is isomorphic to the trivial one-dimensional module. No finite-generation hypothesis on the
module is necessary. -/
theorem nonempty_linearEquiv_trivial_of_isPGroup (hG : IsPGroup p G)
    (M : Type*) [AddCommGroup M] [Module k M] [Module k[G] M] [IsScalarTower k k[G] M]
    [IsSimpleModule k[G] M] :
    Nonempty (M ≃ₗ[k[G]] (Representation.trivial k G k).asModule) := by
  apply nonempty_linearEquiv_trivial_of_forall_pow_eq_one p M
  intro g
  obtain ⟨n, hn⟩ := hG g
  exact ⟨n, fun x ↦ by simp [hn, ← MonoidAlgebra.one_def]⟩

/-- A simple module over a finite `p`-group algebra in characteristic `p` has dimension one. -/
theorem finrank_eq_one_of_isSimpleModule_of_isPGroup (hG : IsPGroup p G)
    (M : ModuleCat k[G]) [IsSimpleModule k[G] M] : Module.finrank k M = 1 := by
  obtain ⟨e⟩ := nonempty_linearEquiv_trivial_of_isPGroup (k := k) p hG M
  exact (e.restrictScalars k).finrank_eq.trans
    ((Representation.trivial k G k).asModuleEquiv.finrank_eq.trans (Module.finrank_self k))

-- The exact structure and its universe convention require the group and field in one universe.
variable {G : Type u} [Group G] [Finite G]

/-- The trivial line is an exhaustive family of simple group-algebra modules for a finite
`p`-group in characteristic `p`. -/
theorem isExhaustiveSimpleFamily_trivial_of_isPGroup (hG : IsPGroup p G) :
    IsExhaustiveSimpleFamily (fun _ : Unit ↦
      FGModuleCat.of k[G] (Representation.trivial k G k).asModule) := by
  rw [isExhaustiveSimpleFamily_iff]
  intro M hM
  let := hM
  exact ⟨(), nonempty_linearEquiv_trivial_of_isPGroup p hG M⟩

/-- In the exact Grothendieck group of a finite `p`-group in characteristic `p`, every class
is its (integer-valued) dimension times the class of the trivial line. -/
theorem eq_finrankK0_smul_trivial_of_isPGroup (hG : IsPGroup p G)
    (x : ExactK0 (finiteModulesExactStructure k[G])) :
    x = finrankK0 k k[G] x •
      ExactK0.of (FGModuleCat.of k[G] (Representation.trivial k G k).asModule) := by
  let : IsArtinianRing k[G] := IsArtinianRing.of_finite k k[G]
  apply eq_finrankK0_smul_of_finrank_eq_one k k[G] _
    (isExhaustiveSimpleFamily_trivial_of_isPGroup p hG)
  exact finrank_eq_one_of_isSimpleModule_of_isPGroup p hG _

/-- Dimension identifies the exact Grothendieck group of a finite `p`-group in characteristic
`p` with `ℤ`. Its inverse sends an integer to that multiple of the trivial line's class. -/
noncomputable def pGroupFinrankK0Equiv (hG : IsPGroup p G) :
    ExactK0 (finiteModulesExactStructure k[G]) ≃+ ℤ := by
  letI : IsArtinianRing k[G] := IsArtinianRing.of_finite k k[G]
  exact finrankK0Equiv k k[G] _ (isExhaustiveSimpleFamily_trivial_of_isPGroup p hG)
    (finrank_eq_one_of_isSimpleModule_of_isPGroup p hG _)

/-- The dimension equivalence agrees with the dimension homomorphism. -/
@[simp]
theorem pGroupFinrankK0Equiv_apply (hG : IsPGroup p G)
    (x : ExactK0 (finiteModulesExactStructure k[G])) :
    pGroupFinrankK0Equiv p hG x = finrankK0 k k[G] x := by
  let : IsArtinianRing k[G] := IsArtinianRing.of_finite k k[G]
  unfold pGroupFinrankK0Equiv
  exact finrankK0Equiv_apply _ _ _ _ _ _

/-- The inverse dimension equivalence sends an integer to a multiple of the trivial class. -/
@[simp]
theorem pGroupFinrankK0Equiv_symm_apply (hG : IsPGroup p G) (n : ℤ) :
    (pGroupFinrankK0Equiv p hG).symm n = n •
      ExactK0.of (FGModuleCat.of k[G] (Representation.trivial k G k).asModule) := by
  rw [eq_finrankK0_smul_trivial_of_isPGroup p hG ((pGroupFinrankK0Equiv p hG).symm n),
    ← pGroupFinrankK0Equiv_apply p hG, AddEquiv.apply_symm_apply]

/-- For a finite `p`-group in characteristic `p`, induction of the trivial class from `S`
is the index of `S` times the trivial class of the whole group. -/
theorem indK0_one_eq_index_nsmul_of_isPGroup (hG : IsPGroup p G) (S : Subgroup G) :
    indK0 k S 1 = S.index • (1 : ExactK0 (finiteModulesExactStructure k[G])) := by
  apply (pGroupFinrankK0Equiv p hG).injective
  simp only [pGroupFinrankK0Equiv_apply]
  rw [finrankK0_indK0, map_nsmul, finrankK0_one, finrankK0_one]
  simp

/-- For a finite `p`-group in characteristic `p`, a virtual class is induced from `S`
exactly when its dimension is divisible by the index of `S`. -/
theorem mem_range_indK0_iff_of_isPGroup (hG : IsPGroup p G) (S : Subgroup G)
    (x : ExactK0 (finiteModulesExactStructure k[G])) :
    x ∈ (indK0 k S).range ↔ (S.index : ℤ) ∣ finrankK0 k k[G] x := by
  refine ⟨index_dvd_finrankK0_of_mem_range_indK0 S, ?_⟩
  rintro ⟨n, hn⟩
  refine ⟨n • 1, ?_⟩
  rw [map_zsmul, indK0_one_eq_index_nsmul_of_isPGroup p hG]
  apply (pGroupFinrankK0Equiv p hG).injective
  simp only [pGroupFinrankK0Equiv_apply]
  rw [map_zsmul, map_nsmul, finrankK0_one]
  simpa [mul_comm] using hn.symm

/-- An integer multiple of the trivial class of a finite `p`-group in characteristic `p`
is induced from the trivial subgroup exactly when the group order divides the multiplier. -/
theorem zsmul_one_mem_range_indK0_bot_iff_of_isPGroup (hG : IsPGroup p G) (n : ℤ) :
    n • (1 : ExactK0 (finiteModulesExactStructure k[G])) ∈
      (indK0 k (⊥ : Subgroup G)).range ↔ (Nat.card G : ℤ) ∣ n := by
  rw [mem_range_indK0_iff_of_isPGroup p hG, map_zsmul, finrankK0_one]
  simp [Subgroup.index_bot]

/-- The group order is the least positive multiplier for induction from the trivial
subgroup of a finite `p`-group in characteristic `p`: precisely its multiples work. -/
theorem nsmul_one_mem_range_indK0_bot_iff_of_isPGroup (hG : IsPGroup p G) (n : ℕ) :
    n • (1 : ExactK0 (finiteModulesExactStructure k[G])) ∈
      (indK0 k (⊥ : Subgroup G)).range ↔ Nat.card G ∣ n := by
  simpa only [natCast_zsmul, Int.natCast_dvd_natCast] using
    zsmul_one_mem_range_indK0_bot_iff_of_isPGroup (k := k) p hG (n : ℤ)

end TauCeti
