/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.GrothendieckGroup.Finrank
public import TauCeti.RepresentationTheory.Irreducible
public import TauCeti.RepresentationTheory.PGroupInvariants
import TauCeti.RepresentationTheory.OfModule
import TauCeti.RepresentationTheory.AsModule

/-!
# The Grothendieck group of a finite `p`-group in characteristic `p`

Let `G` be a finite `p`-group and `k` a field of characteristic `p`. Every simple `k[G]`-module
is isomorphic to the trivial line. Consequently the dimension homomorphism identifies the exact
Grothendieck group of finitely generated `k[G]`-modules with `ℤ`: the class of any module is its
dimension times the class of the trivial line. These are exact-sequence relations, so they also
apply to modules which are not direct sums of trivial representations.

The simple-module statement uses the invariant-vector theorem from
`TauCeti/RepresentationTheory/PGroupInvariants.lean`. The Grothendieck-group statements specialize
`TauCeti.eq_finrankK0_smul_of_finrank_eq_one` and `TauCeti.finrankK0Equiv`, using the trivial
representation's existing `asModule` construction rather than another model of the trivial module.

## Main results

* `TauCeti.nonempty_linearEquiv_trivial_of_isPGroup`: every simple module is the trivial line.
* `TauCeti.eq_finrankK0_smul_trivial_of_isPGroup`: dimension determines every class.
* `TauCeti.pGroupFinrankK0Equiv`: dimension is an additive equivalence with `ℤ`.

## References

* J.-P. Serre, *Linear Representations of Finite Groups*, Part III, §14.
* P. Webb, *A Course in Finite Group Representation Theory*.
-/

public section

namespace TauCeti

open scoped MonoidAlgebra ModuleCat

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
  let ρ := Representation.ofModule' (k := k) (G := G) M
  have hρ : ρ.IsIrreducible := Representation.isIrreducible_ofModule'_iff M |>.mpr inferInstance
  have hpow : ∀ g : G, ∃ n : ℕ, ρ g ^ p ^ n = 1 := by
    intro g
    obtain ⟨n, hn⟩ := hG g
    exact ⟨n, by rw [← map_pow, hn, map_one]⟩
  have htriv := hρ.eq_trivial_of_forall_pow_eq_one p hpow
  have hdim := hρ.finrank_eq_one_of_forall_pow_eq_one p hpow
  have := hρ.finiteDimensional
  let e := LinearEquiv.ofFinrankEq M k (hdim.trans (Module.finrank_self k).symm)
  have he : ρ.Equiv (Representation.trivial k G k) := Representation.Equiv.mk e (by
    intro g
    rw [htriv]
    ext x
    simp)
  exact ⟨(Representation.ofModule'AsModuleEquiv M).symm.trans
    (Representation.asModuleLinearEquivOfEquiv he)⟩

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

end TauCeti
