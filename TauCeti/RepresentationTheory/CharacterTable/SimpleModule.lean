/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.CharacterTable.Table
import TauCeti.RepresentationTheory.AsModule
import TauCeti.RepresentationTheory.OfModule

/-!
# Simple `k[G]`-modules are the chosen irreducible models

Let `G` be a finite group and `k` an algebraically closed field in which `|G|` is invertible, and
let `Zᵢ = TauCeti.irreducibleRepresentation k i` be the chosen irreducible representations, one for
each row `i` of the character table. Every simple `k[G]`-module, with carrier in any universe, is
isomorphic to exactly one of the modules attached to the `Zᵢ`. This is the lookup assigning its
class to a simple summand of a representation.

## Main results

* `TauCeti.existsUnique_nonempty_linearEquiv_irreducibleRepresentation`: every simple
  `k[G]`-module, in any universe, is isomorphic to `Zᵢ` for exactly one `i`.
-/

public section

open scoped MonoidAlgebra

universe u v w

namespace TauCeti

variable (k : Type u) {G : Type v} [Field k] [IsAlgClosed k] [Group G] [Finite G]
  [Invertible (Nat.card G : k)]

/-- **Every simple `k[G]`-module is one of the chosen irreducible models**, and only one: for a
simple `k[G]`-module `N` whose `k`-module structure is the restricted one, there is exactly one row
`i` of the character table with `N ≅ Zᵢ` as `k[G]`-modules. The module `N` may lie in any universe,
not only in that of `k`. -/
theorem existsUnique_nonempty_linearEquiv_irreducibleRepresentation (N : Type w) [AddCommGroup N]
    [Module k N] [Module k[G] N] [IsScalarTower k k[G] N] [IsSimpleModule k[G] N] :
    ∃! i : Fin (Nat.card (ConjClasses G)),
      Nonempty (N ≃ₗ[k[G]] (irreducibleRepresentation k i).asModule) := by
  have : (_root_.Representation.ofModule' (k := k) (G := G) N).IsIrreducible :=
    (Representation.isIrreducible_ofModule'_iff N).mpr inferInstance
  obtain ⟨i, ⟨φ⟩⟩ := ClassFunction.exists_nonempty_equiv (irreducibleRepresentation k)
    (pairwise_isEmpty_equiv_irreducibleRepresentation k) (by simp)
    (_root_.Representation.ofModule' (k := k) (G := G) N)
  refine ⟨i, ⟨(Representation.ofModule'AsModuleEquiv N).symm ≪≫ₗ
    Representation.asModuleLinearEquivOfEquiv φ⟩, fun j ⟨e⟩ ↦ ?_⟩
  by_contra hji
  exact (pairwise_isEmpty_equiv_irreducibleRepresentation k hji).elim
    (Representation.equivOfAsModuleLinearEquiv (e.symm ≪≫ₗ
      (Representation.ofModule'AsModuleEquiv N).symm ≪≫ₗ
      Representation.asModuleLinearEquivOfEquiv φ))

end TauCeti
