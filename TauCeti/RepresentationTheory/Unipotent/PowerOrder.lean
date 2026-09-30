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
-- Non-public: `TauCeti.isNilpotent_sub_one_of_pow_expChar_pow_eq_one` and its converse
-- `TauCeti.exists_pow_char_pow_eq_one_of_isNilpotent_sub_one` are the ring-level dictionary between
-- unipotence and `p`-power order, applied inside proofs only.
import TauCeti.Algebra.CharP.Unipotent
-- Non-public: `Module.charP_end`, and `expChar_of_injective_algebraMap` from the `CharP.Algebra`
-- file it imports, transfer the characteristic of `k` to its endomorphism algebra, which is where
-- that dictionary is read.
import Mathlib.Algebra.CharP.LinearMaps
-- Non-public: Kolchin's theorem, in both its vector and its line form, is what the fixed-vector
-- statements below specialize.
import TauCeti.LinearAlgebra.Eigenspace.JointEigenvector.Kolchin
-- Non-public: `Representation.IsIrreducible.invariants_eq_bot` and its dimension form are what the
-- irreducible corollaries contradict, and `Representation.IsIrreducible.nontrivial` supplies the
-- nontriviality they need.
import TauCeti.RepresentationTheory.Invariants
import TauCeti.RepresentationTheory.Irreducible

/-!
# Fixed vectors of a finite-dimensional representation of `p`-power order in characteristic `p`

Let `k` be a field of exponential characteristic `p`.  The endomorphism algebra of a nonzero
`k`-module has the same exponential characteristic, because `k` embeds into it, so an operator
satisfying `f ^ p ^ n = 1` has `f - 1` nilpotent
(`TauCeti.isNilpotent_sub_one_of_pow_expChar_pow_eq_one`).  A representation in which every element
acts with `p`-power order is therefore a representation by unipotent operators, and Kolchin's
theorem (`Representation.exists_common_fixed_vector_of_isUnipotent`) fixes a nonzero vector of a
finite-dimensional carrier.  No finiteness is asked of the acting monoid, and the corollaries for a
`p`-group hold for an infinite `p`-group.

Only that one implication is needed for the fixed vector, so the fixed-vector and `p`-group results
ask only for `ExpChar k p`.  The converse — a unipotent operator has `p`-power order — needs `p`
prime and the characteristic exactly `p`, and only the equivalence
`Representation.isNilpotent_sub_one_iff_exists_pow_eq_one` assumes that.

This complements `TauCeti/RepresentationTheory/PGroupInvariants.lean`, which proves the same
conclusion for a **finite** group over a commutative ring of characteristic `p` with no
finiteness hypothesis on the module, by an orbit count rather than by Kolchin's theorem.  Neither
statement subsumes the other: here the module must be finite-dimensional over a field and the
acting monoid may be infinite, there the module is arbitrary and the group must be finite.  The
irreducibility results below are accordingly the infinite-group counterparts of
`Representation.IsIrreducible.eq_trivial_of_forall_pow_eq_one`.  Because that file has already
taken the `_of_forall_pow_eq_one` names for its finite-group statements, and neither trio subsumes
the other, the ones here carry the `expChar` of their characteristic hypothesis in their names.

## Main results

* `Representation.isNilpotent_sub_one_of_pow_expChar_pow_eq_one`: in exponential characteristic `p`
  an operator of `p`-power order is unipotent, with
  `Representation.isNilpotent_sub_one_iff_exists_pow_eq_one` the equivalence it is half of in prime
  characteristic `p`.
* `Representation.exists_common_fixed_vector_of_forall_pow_eq_one`: **a nonzero finite-dimensional
  representation of a monoid in which every element acts with `p`-power order, over a field of
  exponential characteristic `p`, fixes a nonzero vector**, with
  `Representation.exists_fixed_submodule_finrank_eq_one_of_forall_pow_eq_one` its fixed-line form.
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

/-- **In exponential characteristic `p`, an operator of `p`-power order is unipotent.** Over a
nonzero module this is the ring-level `TauCeti.isNilpotent_sub_one_of_pow_expChar_pow_eq_one` read
in the endomorphism algebra, whose exponential characteristic is that of `k` because `k` embeds into
it by `algebraMap`; over a zero module every endomorphism is zero. -/
theorem isNilpotent_sub_one_of_pow_expChar_pow_eq_one (p n : ℕ) [ExpChar k p]
    (ρ : Representation k H V) {g : H} (h : ρ g ^ p ^ n = 1) : IsNilpotent (ρ g - 1) := by
  rcases subsingleton_or_nontrivial V with _ | _
  · exact ⟨0, LinearMap.ext fun x => Subsingleton.elim _ _⟩
  · obtain ⟨v, hv⟩ := exists_ne (0 : V)
    have hinj : Function.Injective (algebraMap k (Module.End k V)) := by
      refine (injective_iff_map_eq_zero _).2 fun c hc => ?_
      have hcv : c • v = 0 := by simpa using congrArg (fun f : Module.End k V => f v) hc
      exact (smul_eq_zero.1 hcv).resolve_right hv
    have : ExpChar (Module.End k V) p := expChar_of_injective_algebraMap hinj p
    exact TauCeti.isNilpotent_sub_one_of_pow_expChar_pow_eq_one p n h

/-- **In prime characteristic `p`, an operator of a representation is unipotent exactly when it has
`p`-power order.** Over a nonzero module the converse of
`Representation.isNilpotent_sub_one_of_pow_expChar_pow_eq_one` is the ring-level
`TauCeti.exists_pow_char_pow_eq_one_of_isNilpotent_sub_one` read in the endomorphism algebra, whose
characteristic is that of `k` by `Module.charP_end`; over a zero module both sides hold because
every endomorphism is zero. -/
theorem isNilpotent_sub_one_iff_exists_pow_eq_one (p : ℕ) [Fact p.Prime] [CharP k p]
    (ρ : Representation k H V) (g : H) :
    IsNilpotent (ρ g - 1) ↔ ∃ n : ℕ, ρ g ^ p ^ n = 1 := by
  refine ⟨fun h => ?_, fun ⟨n, hn⟩ => ρ.isNilpotent_sub_one_of_pow_expChar_pow_eq_one p n hn⟩
  rcases subsingleton_or_nontrivial V with _ | _
  · exact ⟨1, by rw [pow_one]; exact Subsingleton.elim _ _⟩
  · have hchar : CharP (Module.End k V) p := by
      obtain ⟨v, hv⟩ := exists_ne (0 : V)
      refine Module.charP_end ⟨v, eq_bot_iff.2 fun r hr => ?_⟩
      rw [Ideal.mem_torsionOf_iff] at hr
      simpa [hv] using hr
    exact TauCeti.exists_pow_char_pow_eq_one_of_isNilpotent_sub_one p h

variable (p : ℕ) [ExpChar k p]

/-- **Kolchin's theorem in exponential characteristic `p`: a nonzero finite-dimensional
representation in which every element acts with `p`-power order fixes a nonzero vector.** The acting
monoid is arbitrary; in particular it may be infinite, which is what distinguishes this from the
orbit-counting `Representation.exists_ne_zero_apply_eq_self_of_forall_pow_eq_one` for a finite
group. -/
theorem exists_common_fixed_vector_of_forall_pow_eq_one [FiniteDimensional k V] [Nontrivial V]
    (ρ : Representation k H V) (hρ : ∀ g : H, ∃ n : ℕ, ρ g ^ p ^ n = 1) :
    ∃ v : V, v ≠ 0 ∧ ∀ g : H, ρ g v = v :=
  ρ.exists_common_fixed_vector_of_isUnipotent fun g =>
    (hρ g).elim fun _ hn => ρ.isNilpotent_sub_one_of_pow_expChar_pow_eq_one p _ hn

/-- The fixed-line form of `Representation.exists_common_fixed_vector_of_forall_pow_eq_one`: such a
representation fixes a line pointwise, the first step of an invariant complete flag. -/
theorem exists_fixed_submodule_finrank_eq_one_of_forall_pow_eq_one [FiniteDimensional k V]
    [Nontrivial V] (ρ : Representation k H V) (hρ : ∀ g : H, ∃ n : ℕ, ρ g ^ p ^ n = 1) :
    ∃ q : Submodule k V, Module.finrank k q = 1 ∧ ∀ g : H, ∀ y ∈ q, ρ g y = y :=
  ρ.exists_fixed_submodule_finrank_eq_one_of_isUnipotent fun g =>
    (hρ g).elim fun _ hn => ρ.isNilpotent_sub_one_of_pow_expChar_pow_eq_one p _ hn

end Monoid

section Invariants

variable {k : Type u} {G : Type v} {V : Type w} [Field k] [Group G] [AddCommGroup V] [Module k V]
  (p : ℕ)

/-- In a representation of a `p`-group every element acts with `p`-power order, because `ρ` is a
monoid homomorphism. -/
private theorem forall_pow_eq_one_of_isPGroup (hG : IsPGroup p G) (ρ : Representation k G V) :
    ∀ g : G, ∃ n : ℕ, ρ g ^ p ^ n = 1 := fun g =>
  (hG g).elim fun n hn => ⟨n, by rw [← map_pow, hn, map_one]⟩

variable [ExpChar k p] [FiniteDimensional k V]

/-- The submodule form of `Representation.exists_common_fixed_vector_of_forall_pow_eq_one`: the
invariants of such a representation are nonzero.  This is the infinite-group counterpart of
`Representation.invariants_ne_bot_of_forall_pow_eq_one`, which drops the finite dimensionality of
the module and asks instead that the group be finite. -/
theorem invariants_ne_bot_of_forall_pow_expChar_pow_eq_one [Nontrivial V]
    (ρ : Representation k G V) (hρ : ∀ g : G, ∃ n : ℕ, ρ g ^ p ^ n = 1) : ρ.invariants ≠ ⊥ := by
  obtain ⟨v, hv0, hv⟩ := ρ.exists_common_fixed_vector_of_forall_pow_eq_one p hρ
  refine fun h => hv0 ?_
  have hmem : v ∈ ρ.invariants := hv
  rwa [h, Submodule.mem_bot] at hmem

/-- **A finite-dimensional irreducible representation in which every element acts with `p`-power
order, over a field of exponential characteristic `p`, is the trivial representation.** It has a
nonzero invariant vector, and a nontrivial irreducible representation has none.  The acting group
need not be finite, which is what this adds to
`Representation.IsIrreducible.eq_trivial_of_forall_pow_eq_one`. -/
theorem IsIrreducible.eq_trivial_of_forall_pow_expChar_pow_eq_one {ρ : Representation k G V}
    (h : ρ.IsIrreducible) (hρ : ∀ g : G, ∃ n : ℕ, ρ g ^ p ^ n = 1) : ρ = trivial k G V :=
  have := h.nontrivial
  not_not.1 fun hne =>
    ρ.invariants_ne_bot_of_forall_pow_expChar_pow_eq_one p hρ (h.invariants_eq_bot hne)

/-- **Such an irreducible representation is a line**, an irreducible representation of any other
dimension having no nonzero invariant vector. -/
theorem IsIrreducible.finrank_eq_one_of_forall_pow_expChar_pow_eq_one
    {ρ : Representation k G V} (h : ρ.IsIrreducible)
    (hρ : ∀ g : G, ∃ n : ℕ, ρ g ^ p ^ n = 1) : Module.finrank k V = 1 :=
  have := h.nontrivial
  not_not.1 fun hne =>
    ρ.invariants_ne_bot_of_forall_pow_expChar_pow_eq_one p hρ
      (h.invariants_eq_bot_of_finrank_ne_one hne)

/-- **A nonzero finite-dimensional representation of a `p`-group over a field of exponential
characteristic `p` fixes a nonzero vector.** The group is not assumed finite. -/
theorem exists_common_fixed_vector_of_isPGroup [Nontrivial V] (hG : IsPGroup p G)
    (ρ : Representation k G V) : ∃ v : V, v ≠ 0 ∧ ∀ g : G, ρ g v = v :=
  ρ.exists_common_fixed_vector_of_forall_pow_eq_one p (forall_pow_eq_one_of_isPGroup p hG ρ)

/-- The submodule form of `Representation.exists_common_fixed_vector_of_isPGroup`: the invariants
of such a representation are nonzero. -/
theorem invariants_ne_bot_of_isPGroup [Nontrivial V] (hG : IsPGroup p G)
    (ρ : Representation k G V) : ρ.invariants ≠ ⊥ :=
  ρ.invariants_ne_bot_of_forall_pow_expChar_pow_eq_one p (forall_pow_eq_one_of_isPGroup p hG ρ)

/-- The specialization of
`Representation.IsIrreducible.eq_trivial_of_forall_pow_expChar_pow_eq_one` to a `p`-group: **a
finite-dimensional irreducible representation of a `p`-group in exponential characteristic `p` is
the trivial representation.** -/
theorem IsIrreducible.eq_trivial_of_isPGroup {ρ : Representation k G V} (h : ρ.IsIrreducible)
    (hG : IsPGroup p G) : ρ = trivial k G V :=
  h.eq_trivial_of_forall_pow_expChar_pow_eq_one p (forall_pow_eq_one_of_isPGroup p hG ρ)

/-- **Such an irreducible representation of a `p`-group is a line.** -/
theorem IsIrreducible.finrank_eq_one_of_isPGroup {ρ : Representation k G V} (h : ρ.IsIrreducible)
    (hG : IsPGroup p G) : Module.finrank k V = 1 :=
  h.finrank_eq_one_of_forall_pow_expChar_pow_eq_one p (forall_pow_eq_one_of_isPGroup p hG ρ)

end Invariants

end Representation
