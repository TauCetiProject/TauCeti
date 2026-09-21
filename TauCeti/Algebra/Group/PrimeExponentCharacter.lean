/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Group.TypeTags.Hom
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.GroupTheory.Exponent
public import Mathlib.GroupTheory.Index
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Characters of a group of prime exponent

Let `p` be a prime and let `A` be a group whose elements commute and satisfy `a ^ p = 1`. Its
additive shadow `Additive A` is then a vector space over the field `ZMod p`, so the coordinate
functionals separate its points; translated back through the type-tag adjunction
`AddMonoidHom.toMultiplicativeRight`, those functionals are the homomorphisms
`A →* Multiplicative (ZMod p)`. This file records the resulting separation statement.

Commutativity is carried by the `IsMulCommutative` mixin rather than a `CommGroup` instance because
the intended consumers are quotients `G ⧸ N` of a group by a normal subgroup containing the
commutator subgroup and all `p`-th powers.

No finiteness is needed: a vector space over a field has a basis regardless of its dimension.
Mathlib's separation theorem for finite commutative groups,
`CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity`, does not cover this: it needs the
target to contain enough roots of unity of the exponent of the group, and `ZMod p` contains no
`p`-th root of unity other than `1`.

## Main results

* `TauCeti.exists_monoidHom_multiplicative_zmod_apply_ne_one`: for `x ≠ 1` there is a
  homomorphism `A →* Multiplicative (ZMod p)` not killing `x`.
* `TauCeti.exists_subgroup_index_eq_prime_and_notMem`: every nonidentity element is avoided by a
  subgroup of index `p`.
* `TauCeti.exists_index_eq_two_notMem_of_exponent_dvd_two`: the exponent-two specialization.
-/

public section

namespace TauCeti

/-- **Characters with values in `ZMod p` separate the points of a group of exponent `p`.**
If the elements of `A` commute and satisfy `a ^ p = 1` for a prime `p`, then every `x ≠ 1` is
detected by a homomorphism `A →* Multiplicative (ZMod p)`. Its kernel is a normal subgroup of
index `p` avoiding `x`. -/
theorem exists_monoidHom_multiplicative_zmod_apply_ne_one {A : Type*} [Group A] {p : ℕ}
    [Fact p.Prime] [IsMulCommutative A] (hpow : ∀ a : A, a ^ p = 1) {x : A} (hx : x ≠ 1) :
    ∃ φ : A →* Multiplicative (ZMod p), φ x ≠ 1 := by
  let _ : CommGroup A := { ‹Group A› with mul_comm := mul_comm' }
  -- `AddCommGroup.zmodModule` is a `match` on `p`, so as a local instance it blocks the
  -- coercion of a `ZMod p`-linear map to a function; obtaining it through `Nonempty` (legitimate
  -- since the goal is a proposition) keeps it opaque and unblocks that coercion.
  obtain ⟨_⟩ : Nonempty (Module (ZMod p) (Additive A)) :=
    ⟨AddCommGroup.zmodModule fun a ↦ Additive.toMul.injective (by simpa using hpow a.toMul)⟩
  have hx0 : (Additive.ofMul x : Additive A) ≠ 0 := by simpa using hx
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_ne_zero (ZMod p) hx0
  exact ⟨AddMonoidHom.toMultiplicativeRight f.toAddMonoidHom, by simpa using hf⟩

/-- The kernel of a homomorphism to a group of prime order has index that prime when the
homomorphism does not kill some element. -/
theorem index_ker_eq_prime_of_apply_ne_one {A M : Type*} [Group A] [Group M] {p : ℕ}
    [Fact p.Prime] (hcard : Nat.card M = p) (χ : A →* M) {x : A} (hx : χ x ≠ 1) :
    χ.ker.index = p := by
  have hdvd : Nat.card χ.range ∣ Nat.card M := Subgroup.card_subgroup_dvd_card _
  rw [hcard] at hdvd
  have hne : Nat.card χ.range ≠ 1 := fun h ↦ hx <| by
    have hmem : χ x ∈ χ.range := ⟨x, rfl⟩
    rwa [Subgroup.card_eq_one.mp h, Subgroup.mem_bot] at hmem
  exact (Subgroup.index_ker χ).trans
    (((Fact.out : p.Prime).eq_one_or_self_of_dvd _ hdvd).resolve_left hne)

/-- **Index-`p` subgroups separate the points of a commutative group of exponent `p`.** -/
theorem exists_subgroup_index_eq_prime_and_notMem {A : Type*} [Group A] {p : ℕ}
    [Fact p.Prime] [IsMulCommutative A] (hpow : ∀ a : A, a ^ p = 1) {x : A} (hx : x ≠ 1) :
    ∃ H : Subgroup A, H.index = p ∧ x ∉ H := by
  obtain ⟨φ, hφ⟩ := exists_monoidHom_multiplicative_zmod_apply_ne_one hpow hx
  refine ⟨φ.ker, ?_, ?_⟩
  · have _ : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
    have hcard : Nat.card (Multiplicative (ZMod p)) = p := by
      rw [Nat.card_congr Multiplicative.toAdd, Nat.card_eq_fintype_card, ZMod.card]
    exact index_ker_eq_prime_of_apply_ne_one hcard φ hφ
  · simpa [MonoidHom.mem_ker] using hφ

/-- **Index-two subgroups separate the points of a group of exponent two.** In a group all of whose
elements square to `1`, every `σ ≠ 1` lies outside some subgroup of index `2`. -/
theorem exists_index_eq_two_notMem_of_exponent_dvd_two {G : Type*} [Group G]
    (hexp : Monoid.exponent G ∣ 2) {σ : G} (hσ : σ ≠ 1) :
    ∃ H : Subgroup G, H.index = 2 ∧ σ ∉ H := by
  have hsquare : ∀ g : G, g ^ 2 = 1 :=
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hexp
  let _ : IsMulCommutative G := ⟨⟨fun a b ↦
    Commute.of_orderOf_dvd_two (fun g ↦ orderOf_dvd_of_pow_eq_one (hsquare g)) a b⟩⟩
  exact exists_subgroup_index_eq_prime_and_notMem hsquare hσ

end TauCeti
