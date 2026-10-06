/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CharP.Defs
public import Mathlib.GroupTheory.PGroup
public import Mathlib.RepresentationTheory.Invariants
public import Mathlib.RepresentationTheory.Irreducible
public import Mathlib.RingTheory.Nilpotent.Defs
-- Non-public: `Module.End.isNilpotent_sub_one_of_pow_expChar_pow_eq_one` is the characteristic-`p`
-- dictionary between `p`-power order and unipotence, applied here to the operators `ρ g`.
import TauCeti.Algebra.CharP.LinearMaps
-- Non-public: Kolchin's theorem, in both its vector and its line form, is what the fixed-vector
-- statements below specialize.
import TauCeti.LinearAlgebra.Eigenspace.JointEigenvector.Kolchin
-- Non-public: `Representation.IsIrreducible.eq_trivial_of_invariants_ne_bot` and its dimension form
-- are what the irreducible corollaries apply, and `Representation.IsIrreducible.nontrivial`
-- supplies the nontriviality they need.
import TauCeti.RepresentationTheory.Invariants
import TauCeti.RepresentationTheory.Irreducible
-- Non-public: `IsPGroup.exists_pow_pow_eq_one_map` is what gives the operators of a representation
-- of a `p`-group their `p`-power order.
import TauCeti.GroupTheory.PGroup

/-!
# Fixed vectors of a finite-dimensional representation of `p`-power order in characteristic `p`

Let `k` be a field of exponential characteristic `p`.  The endomorphism algebra of a nonzero
`k`-module has the same exponential characteristic, because `k` acts faithfully on it, so an
operator satisfying `f ^ p ^ n = 1` has `f - 1` nilpotent
(`Module.End.isNilpotent_sub_one_of_pow_expChar_pow_eq_one`).  A representation in which every
element acts with `p`-power order is therefore a representation by unipotent operators, and
Kolchin's theorem (`Representation.exists_common_fixed_vector_of_isUnipotent`) fixes a nonzero
vector of a finite-dimensional carrier.  No finiteness is asked of the acting monoid, and the
corollaries for a `p`-group hold for an infinite `p`-group.

This complements `TauCeti/RepresentationTheory/PGroupInvariants.lean`, which proves the same
conclusion for a **finite** group over a commutative ring of characteristic `p` with no
finiteness hypothesis on the module, by an orbit count rather than by Kolchin's theorem.  Neither
statement subsumes the other: the results here allow an infinite acting monoid, at the cost of
asking the module to be finite-dimensional over a field, while there the module is arbitrary and
the group must be finite.

## Main results

* `Representation.exists_common_fixed_vector_of_forall_pow_expChar_pow_eq_one`: **a nonzero
  finite-dimensional representation of a monoid in which every element acts with `p`-power order,
  over a field of exponential characteristic `p`, fixes a nonzero vector**, with
  `Representation.exists_fixed_submodule_finrank_eq_one_of_forall_pow_expChar_pow_eq_one` its
  fixed-line form.
* `Representation.invariants_ne_bot_of_forall_pow_expChar_pow_eq_one`: the submodule form of that
  fixed vector, for a group.
* `Representation.IsIrreducible.eq_trivial_of_forall_pow_expChar_pow_eq_one` and
  `Representation.IsIrreducible.finrank_eq_one_of_forall_pow_expChar_pow_eq_one`: **such a
  representation is irreducible only if it is the trivial representation on a line**.
* `Representation.exists_common_fixed_vector_of_isPGroup`,
  `Representation.invariants_ne_bot_of_isPGroup`,
  `Representation.IsIrreducible.eq_trivial_of_isPGroup` and
  `Representation.IsIrreducible.finrank_eq_one_of_isPGroup`: the specializations to a `p`-group,
  which need not be finite.

## References

* A. Borel, *Linear Algebraic Groups*, §4.8, for Kolchin's theorem.
* J. L. Alperin, *Local Representation Theory*, Cambridge University Press (1986), for the
  characteristic-`p` statement that the trivial module is the only simple module of a `p`-group.
-/

public section

namespace Representation

universe u v w

section Monoid

variable {k : Type u} {H : Type v} {V : Type w} [Field k] [Monoid H] [AddCommGroup V] [Module k V]
  (p : ℕ) [ExpChar k p]

/-- **In exponential characteristic `p`, a representation in which every element acts with `p`-power
order is a representation by unipotent operators.** This is
`Module.End.isNilpotent_sub_one_of_pow_expChar_pow_eq_one` applied to each operator `ρ g`, and it is
the hypothesis Kolchin's theorem consumes. -/
theorem forall_isNilpotent_sub_one_of_forall_pow_expChar_pow_eq_one (ρ : Representation k H V)
    (hρ : ∀ g : H, ∃ n : ℕ, ρ g ^ p ^ n = 1) : ∀ g : H, IsNilpotent (ρ g - 1) := fun g =>
  (hρ g).elim fun n hn => Module.End.isNilpotent_sub_one_of_pow_expChar_pow_eq_one p n hn

/-- **A nonzero finite-dimensional representation in which every element acts with `p`-power order,
over a field of exponential characteristic `p`, fixes a nonzero vector.** It is a representation by
unipotent operators, so this is a consequence of Kolchin's theorem
(`Representation.exists_common_fixed_vector_of_isUnipotent`).  The acting monoid is arbitrary, in
particular it may be infinite, where the orbit-counting
`Representation.exists_ne_zero_apply_eq_self_of_forall_pow_eq_one` asks for a finite group; the
price is the finite dimensionality of the carrier, which that theorem does not need. -/
theorem exists_common_fixed_vector_of_forall_pow_expChar_pow_eq_one [FiniteDimensional k V]
    [Nontrivial V] (ρ : Representation k H V) (hρ : ∀ g : H, ∃ n : ℕ, ρ g ^ p ^ n = 1) :
    ∃ v : V, v ≠ 0 ∧ ∀ g : H, ρ g v = v :=
  ρ.exists_common_fixed_vector_of_isUnipotent
    (ρ.forall_isNilpotent_sub_one_of_forall_pow_expChar_pow_eq_one p hρ)

/-- The fixed-line form of
`Representation.exists_common_fixed_vector_of_forall_pow_expChar_pow_eq_one`: such a representation
fixes a line pointwise, the first step of an invariant complete flag. -/
theorem exists_fixed_submodule_finrank_eq_one_of_forall_pow_expChar_pow_eq_one
    [FiniteDimensional k V] [Nontrivial V] (ρ : Representation k H V)
    (hρ : ∀ g : H, ∃ n : ℕ, ρ g ^ p ^ n = 1) :
    ∃ q : Submodule k V, Module.finrank k q = 1 ∧ ∀ g : H, ∀ y ∈ q, ρ g y = y :=
  ρ.exists_fixed_submodule_finrank_eq_one_of_isUnipotent
    (ρ.forall_isNilpotent_sub_one_of_forall_pow_expChar_pow_eq_one p hρ)

end Monoid

section Invariants

variable {k : Type u} {G : Type v} {V : Type w} [Field k] [Group G] [AddCommGroup V] [Module k V]
  (p : ℕ) [ExpChar k p] [FiniteDimensional k V]

/-- The submodule form of
`Representation.exists_common_fixed_vector_of_forall_pow_expChar_pow_eq_one`: the invariants of such
a representation are nonzero.  This is the infinite-group counterpart of
`Representation.invariants_ne_bot_of_forall_pow_eq_one`, which drops the finite dimensionality of
the module and asks instead that the group be finite. -/
theorem invariants_ne_bot_of_forall_pow_expChar_pow_eq_one [Nontrivial V]
    (ρ : Representation k G V) (hρ : ∀ g : G, ∃ n : ℕ, ρ g ^ p ^ n = 1) : ρ.invariants ≠ ⊥ := by
  obtain ⟨v, hv0, hv⟩ := ρ.exists_common_fixed_vector_of_forall_pow_expChar_pow_eq_one p hρ
  exact (Submodule.ne_bot_iff _).2 ⟨v, (ρ.mem_invariants v).2 hv, hv0⟩

/-- **A finite-dimensional irreducible representation in which every element acts with `p`-power
order, over a field of exponential characteristic `p`, is the trivial representation.** It has a
nonzero invariant vector, and a nontrivial irreducible representation has none.  The acting group
need not be finite, where `Representation.IsIrreducible.eq_trivial_of_forall_pow_eq_one` asks for a
finite group but not for a finite-dimensional module. -/
theorem IsIrreducible.eq_trivial_of_forall_pow_expChar_pow_eq_one {ρ : Representation k G V}
    (h : ρ.IsIrreducible) (hρ : ∀ g : G, ∃ n : ℕ, ρ g ^ p ^ n = 1) : ρ = trivial k G V :=
  have := h.nontrivial
  h.eq_trivial_of_invariants_ne_bot (ρ.invariants_ne_bot_of_forall_pow_expChar_pow_eq_one p hρ)

/-- **Such an irreducible representation is a line**, an irreducible representation of any other
dimension having no nonzero invariant vector. -/
theorem IsIrreducible.finrank_eq_one_of_forall_pow_expChar_pow_eq_one
    {ρ : Representation k G V} (h : ρ.IsIrreducible)
    (hρ : ∀ g : G, ∃ n : ℕ, ρ g ^ p ^ n = 1) : Module.finrank k V = 1 :=
  have := h.nontrivial
  h.finrank_eq_one_of_invariants_ne_bot (ρ.invariants_ne_bot_of_forall_pow_expChar_pow_eq_one p hρ)

/-- **A nonzero finite-dimensional representation of a `p`-group over a field of exponential
characteristic `p` fixes a nonzero vector.** The group is not assumed finite. -/
theorem exists_common_fixed_vector_of_isPGroup [Nontrivial V] (hG : IsPGroup p G)
    (ρ : Representation k G V) : ∃ v : V, v ≠ 0 ∧ ∀ g : G, ρ g v = v :=
  ρ.exists_common_fixed_vector_of_forall_pow_expChar_pow_eq_one p
    (hG.exists_pow_pow_eq_one_map ρ)

/-- The submodule form of `Representation.exists_common_fixed_vector_of_isPGroup`: the invariants
of such a representation are nonzero. -/
theorem invariants_ne_bot_of_isPGroup [Nontrivial V] (hG : IsPGroup p G)
    (ρ : Representation k G V) : ρ.invariants ≠ ⊥ :=
  ρ.invariants_ne_bot_of_forall_pow_expChar_pow_eq_one p (hG.exists_pow_pow_eq_one_map ρ)

/-- The specialization of
`Representation.IsIrreducible.eq_trivial_of_forall_pow_expChar_pow_eq_one` to a `p`-group: **a
finite-dimensional irreducible representation of a `p`-group in exponential characteristic `p` is
the trivial representation.** -/
theorem IsIrreducible.eq_trivial_of_isPGroup {ρ : Representation k G V} (h : ρ.IsIrreducible)
    (hG : IsPGroup p G) : ρ = trivial k G V :=
  h.eq_trivial_of_forall_pow_expChar_pow_eq_one p (hG.exists_pow_pow_eq_one_map ρ)

/-- **Such an irreducible representation of a `p`-group is a line.** -/
theorem IsIrreducible.finrank_eq_one_of_isPGroup {ρ : Representation k G V} (h : ρ.IsIrreducible)
    (hG : IsPGroup p G) : Module.finrank k V = 1 :=
  h.finrank_eq_one_of_forall_pow_expChar_pow_eq_one p (hG.exists_pow_pow_eq_one_map ρ)

end Invariants

end Representation
