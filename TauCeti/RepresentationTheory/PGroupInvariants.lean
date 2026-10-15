/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Invariants
public import Mathlib.RepresentationTheory.Irreducible
public import Mathlib.GroupTheory.PGroup
-- Non-public: `Representation.IsIrreducible.nontrivial` supplies the nontriviality that the
-- normal-subgroup corollary needs.
import TauCeti.RepresentationTheory.Irreducible
-- Non-public: `AddCommGroup.zmodModule` makes a `p`-torsion abelian group a `ZMod p`-module, used
-- only to build a finite invariant set inside a proof.
import Mathlib.Algebra.Module.ZMod
-- Non-public: `Module.finite_of_finite`, `Module.natCard_eq_pow_finrank` and the field structure of
-- `ZMod p` are what make that set finite and count it.
import Mathlib.RingTheory.Finiteness.Cardinality
import Mathlib.FieldTheory.Finiteness
import Mathlib.Algebra.Field.ZMod

/-!
# Invariants of a representation whose elements have `p`-power order in characteristic `p`

Over a commutative ring `k` of characteristic `p`, a representation `ρ` of a finite group on a
nonzero module, in which every `ρ g` has order a power of `p`, always has a nonzero invariant
vector: `Representation.invariants_ne_bot_of_forall_pow_eq_one`. No finiteness or dimension
hypothesis on the module is needed, and `k` may be infinite. Over a field this is the modular
counterpart of the characteristic-free `Representation.IsIrreducible.invariants_eq_bot`, which
says that a nontrivial irreducible representation has no nonzero invariant vector; together they
say that such a representation is irreducible only if it is the trivial representation on a line.
Equivalently: over a field of characteristic `p`, the trivial module is the only irreducible
module of a finite `p`-group. That corollary is
`Representation.IsIrreducible.eq_trivial_of_forall_pow_expChar_pow_eq_one` in
`TauCeti/RepresentationTheory/Unipotent/PowerOrder.lean`, stated for a finite-dimensional
representation of any group; an irreducible representation of a finite group is
finite-dimensional (`Representation.IsIrreducible.finiteDimensional`).

A finite normal `p`-subgroup of an arbitrary group acts trivially on every irreducible
representation in characteristic `p`: its nonzero invariant subspace is stable under the
whole group and must be the entire representation. This reduces the classification of simple
representations to the quotient by such a subgroup.

The whole-group invariant-vector statements assume the acting group is finite. For an infinite
group, the analogous statement is Kolchin's theorem, which fixes a vector of a
*finite-dimensional* vector space under a group of unipotent operators. The normal-subgroup
corollary here requires finiteness only of the subgroup.

## Main results

* `Representation.invariants_ne_bot_of_forall_pow_eq_one`: **a representation of a finite group
  over a ring of characteristic `p`, all of whose elements act with `p`-power order, has a nonzero
  invariant vector**, with `Representation.exists_ne_zero_apply_eq_self_of_forall_pow_eq_one` its
  elementwise form.
* `Representation.IsIrreducible.comp_eq_trivial_of_isPGroup`: a finite normal `p`-subgroup
  acts trivially on an irreducible representation in characteristic `p`.

## References

The statement is classical: over a field of characteristic `p` the group algebra of a finite
`p`-group is a local ring, so the trivial module is its only irreducible module. Textbook accounts
are in J. L. Alperin, *Local Representation Theory*, Cambridge University Press (1986), and
P. Webb, *A Course in Finite Group Representation Theory*, Cambridge University Press (2016).
-/

public section

namespace Representation

universe u v w

section CommRing

variable {k : Type u} {G : Type v} {V : Type w} [CommRing k] [Group G]
  [AddCommGroup V] [Module k V] (p : ℕ) [Fact p.Prime]

/-- The `ZMod p`-span of the orbit of a nonzero vector is a finite invariant set whose cardinality
`p` divides. It is delivered as a set because only its cardinality, its zero element and its
invariance are used downstream. -/
private theorem exists_finite_stable_set [CharP k p] [Finite G] (ρ : Representation k G V)
    {v : V} (hv : v ≠ 0) :
    ∃ A : Set V, A.Finite ∧ (0 : V) ∈ A ∧ v ∈ A ∧ p ∣ Nat.card A ∧
      ∀ g : G, ∀ x ∈ A, ρ g x ∈ A := by
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hptors : ∀ x : V, p • x = 0 := fun x => by
    rw [← Nat.cast_smul_eq_nsmul k, CharP.cast_eq_zero, zero_smul]
  have _izmod : Module (ZMod p) V := AddCommGroup.zmodModule hptors
  obtain ⟨N, hN⟩ : ∃ N : Submodule (ZMod p) V,
      N = Submodule.span (ZMod p) (Set.range fun g : G => ρ g v) := ⟨_, rfl⟩
  -- the span of a finite set over a finite field is a finite set
  have : Module.Finite (ZMod p) ↥N := by
    rw [hN]; exact Module.Finite.span_of_finite _ (Set.finite_range _)
  have : Finite ↥N := Module.finite_of_finite (ZMod p)
  have hvN : v ∈ N := by
    rw [hN]; exact Submodule.subset_span ⟨1, by simp⟩
  have : Nontrivial ↥N := ⟨⟨⟨v, hvN⟩, 0, by simpa [Submodule.mk_eq_zero] using hv⟩⟩
  -- its cardinality is a positive power of `p`, the vector `v` contributing the positivity
  have hcard : Nat.card ↥N = p ^ Module.finrank (ZMod p) ↥N := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod p), Nat.card_zmod]
  have hrank : Module.finrank (ZMod p) ↥N ≠ 0 := Module.finrank_pos.ne'
  refine ⟨(N : Set V), Set.toFinite _, N.zero_mem, hvN, hcard ▸ dvd_pow_self p hrank, ?_⟩
  -- `ρ g` is additive, hence `ZMod p`-linear, and permutes the spanning orbit
  intro g x hx
  have hle : N ≤ N.comap ((ρ g).toAddMonoidHom.toZModLinearMap p) := by
    rw [hN, Submodule.span_le]
    rintro _ ⟨h, rfl⟩
    simp only [SetLike.mem_coe, Submodule.mem_comap, AddMonoidHom.coe_toZModLinearMap,
      LinearMap.toAddMonoidHom_coe]
    exact Submodule.subset_span ⟨g * h, by simp⟩
  exact hle hx

/-- A group acting with `p`-power orders on a finite invariant set whose cardinality `p` divides
fixes a nonzero vector, because the zero vector is a fixed point it cannot be alone. -/
private theorem exists_ne_zero_mem_invariants_of_stable (ρ : Representation k G V)
    (hρ : ∀ g : G, ∃ n : ℕ, ρ g ^ p ^ n = 1) {A : Set V} (hAfin : A.Finite) (hA0 : (0 : V) ∈ A)
    (hpA : p ∣ Nat.card A) (hstab : ∀ g : G, ∀ x ∈ A, ρ g x ∈ A) :
    ∃ v ∈ ρ.invariants, v ≠ 0 := by
  have : Finite A := hAfin.to_subtype
  -- the restricted action of `G` on `A`; `hsmul` and `hφ` are its two defining evaluations
  let _ : SMul G A := ⟨fun g x => ⟨ρ g x, hstab g x x.2⟩⟩
  have hsmul : ∀ (g : G) (x : A), ((g • x : A) : V) = ρ g x := fun _ _ => rfl
  let _ : MulAction G A :=
    { one_smul := fun x => Subtype.ext (by rw [hsmul]; simp)
      mul_smul := fun g h x =>
        Subtype.ext (by rw [hsmul, hsmul, hsmul, map_mul]; exact Module.End.mul_apply _ _ _) }
  have hφ : ∀ (g : G) (x : A), ((MulAction.toPermHom G A g x : A) : V) = ρ g x := fun _ _ => rfl
  -- the image of `G` in the permutations of `A` is a `p`-group
  have hPG : IsPGroup p (MulAction.toPermHom G A).range := by
    intro σ
    obtain ⟨g, hg⟩ := σ.2
    obtain ⟨n, hn⟩ := hρ g
    refine ⟨n, Subtype.ext ?_⟩
    simp only [Subgroup.coe_pow, OneMemClass.coe_one]
    rw [← hg, ← map_pow]
    ext x
    rw [hφ, map_pow, hn]
    exact Module.End.one_apply _
  -- the zero vector is a fixed point, so the orbit count produces a second one
  have h0 : (⟨0, hA0⟩ : A) ∈ MulAction.fixedPoints (MulAction.toPermHom G A).range A := by
    intro σ
    obtain ⟨g, hg⟩ := σ.2
    refine Subtype.ext ?_
    -- a subgroup of the permutations acts through the ambient permutation, which `hφ` evaluates
    have hval : ((σ • (⟨0, hA0⟩ : A) : A) : V) = ((σ : Equiv.Perm A) ⟨0, hA0⟩ : A) := rfl
    rw [hval, ← hg, hφ]
    simp
  obtain ⟨b, hb, hne⟩ :=
    hPG.exists_fixed_point_of_prime_dvd_card_of_fixed_point (α := A) hpA h0
  refine ⟨(b : V), fun g => ?_, fun h => hne (Subtype.ext h.symm)⟩
  -- the element of the image named by `g` acts as `ρ g`, again by the definition of the action
  exact congrArg Subtype.val (hb ⟨MulAction.toPermHom G A g, g, rfl⟩)

/-- **A representation of a finite group in which every element acts with `p`-power order, over a
ring of characteristic `p`, has a nonzero invariant vector.** Neither finite generation nor finite
dimensionality of the module is assumed, and `k` may be infinite. -/
theorem invariants_ne_bot_of_forall_pow_eq_one [CharP k p] [Finite G] [Nontrivial V]
    (ρ : Representation k G V) (hρ : ∀ g : G, ∃ n : ℕ, ρ g ^ p ^ n = 1) :
    ρ.invariants ≠ ⊥ := by
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  obtain ⟨A, hAfin, hA0, -, hpA, hstab⟩ := exists_finite_stable_set p ρ hv
  obtain ⟨w, hw, hwne⟩ := exists_ne_zero_mem_invariants_of_stable p ρ hρ hAfin hA0 hpA hstab
  exact fun h => hwne (by simpa [h] using hw)

/-- The elementwise form of `Representation.invariants_ne_bot_of_forall_pow_eq_one`: a nonzero
vector fixed by every group element. -/
theorem exists_ne_zero_apply_eq_self_of_forall_pow_eq_one [CharP k p] [Finite G] [Nontrivial V]
    (ρ : Representation k G V) (hρ : ∀ g : G, ∃ n : ℕ, ρ g ^ p ^ n = 1) :
    ∃ v : V, v ≠ 0 ∧ ∀ g : G, ρ g v = v := by
  obtain ⟨v, hv, hv0⟩ :=
    (Submodule.ne_bot_iff _).1 (ρ.invariants_ne_bot_of_forall_pow_eq_one p hρ)
  exact ⟨v, hv0, hv⟩

end CommRing

section NormalSubgroup

variable {k : Type u} {G : Type v} {V : Type w} [Field k] [Group G]
  [AddCommGroup V] [Module k V] (p : ℕ) [Fact p.Prime] [CharP k p]

/-- A finite normal `p`-subgroup acts trivially on every irreducible representation in
characteristic `p`. The ambient group and the representation need not be finite. -/
theorem IsIrreducible.comp_eq_trivial_of_isPGroup {ρ : Representation k G V}
    (hρ : ρ.IsIrreducible) (N : Subgroup G) [N.Normal] [Finite N]
    (hN : IsPGroup p N) : ρ.comp N.subtype = trivial k N V := by
  have := hρ.nontrivial
  let W : Subrepresentation ρ :=
    ⟨Representation.invariants (ρ.comp N.subtype), ρ.le_comap_invariants N⟩
  have hW : W ≠ ⊥ := by
    intro h
    apply invariants_ne_bot_of_forall_pow_eq_one p (ρ.comp N.subtype)
      (fun g ↦ by
        obtain ⟨n, hn⟩ := hN g
        exact ⟨n, by rw [← map_pow, hn, map_one]⟩)
    exact congrArg Subrepresentation.toSubmodule h
  let := hρ
  have htop : W = ⊤ := (IsSimpleOrder.eq_bot_or_eq_top W).resolve_left hW
  ext g v
  have hv : v ∈ W.toSubmodule := by rw [htop]; trivial
  exact hv g

end NormalSubgroup

end Representation
