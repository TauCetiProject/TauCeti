/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Index
public import TauCeti.RepresentationTheory.Induction.Clifford.Equivalence

/-!
# The dimension form of Clifford's theorem

Let `N` be a normal subgroup of a group `G` and let `W` be an irreducible finite-dimensional
representation of `G` over an algebraically closed field.  Clifford's theorem describes the
restriction of `W` to `N` as `e` copies of each of the `[G : inertia V]` distinct conjugates of
one irreducible constituent `V`.  Counting dimensions turns that description into the identity

`dim W = e * [G : inertia V] * dim V`,

so in particular the index of the inertia group divides `dim W`.  That index divides `[G : N]` as
well, because `N ≤ inertia V`, so whenever `dim W` and `[G : N]` are **coprime** the index is `1`:
the inertia group is everything, there is a single constituent, and the character of `W` on `N` is
`e` times that of `V`.  A subgroup of index two and an irreducible of odd dimension are coprime in
that sense, which is the case arising for `alternatingGroup α ◁ Equiv.Perm α`, complementary to the
linear-character computation of
`TauCeti/RepresentationTheory/Induction/Clifford/Alternating.lean`, where the inertia group is as
*small* as Clifford theory allows.

## Main statements

* `FDRep.clifford_restrict_finrank`: **Clifford's theorem, dimension form**, packaging the
  constituent together with its decomposition of `Res_N W`, the multiplicity and the identity
  `dim W = e * [G : inertia V] * dim V` as natural numbers.
* `FDRep.clifford_restrict_inertia_eq_top_of_coprime`: when the dimension of `W` is **coprime**
  to `[G : N]`, the restriction of `W` to `N` is isomorphic to `e` copies of a single constituent
  `V` whose inertia group is all of `G`, the character of `W` on `N` being `e` times that of `V`
  and `dim W = e * dim V`.

## References

* I. M. Isaacs, *Character Theory of Finite Groups*, Chapter 6.
-/

public section

open CategoryTheory

universe u v

namespace FDRep

open TauCeti

variable {k : Type u} {G : Type v} [Field k] [Group G] {N : Subgroup G} [N.Normal]

/-- **Clifford's theorem, dimension form.**  The dimension of an irreducible representation of `G`
is the common multiplicity `e` of the constituents of its restriction to `N`, times the number
`[G : inertia V]` of those constituents, times the dimension of one of them.

The decomposition `Res_N W ≅ V.cliffordSum e` that `FDRep.clifford_restrict_iso` supplies is
returned alongside the identity, so that `V` is exhibited as a constituent of the restriction and
not merely named by it.

In particular the index of the inertia group of a constituent divides the dimension of `W`; that
is the arithmetic that `FDRep.clifford_restrict_inertia_eq_top_of_coprime` exploits. -/
theorem clifford_restrict_finrank [IsAlgClosed k] (W : FDRep k G) [Simple W] :
    ∃ (V : FDRep k N) (_ : Simple V) (hfinite : Finite (G ⧸ inertia V)),
      let _ := hfinite
      ∃ e : ℕ, e ≠ 0 ∧ Nonempty (resFDRep N W ≅ V.cliffordSum e) ∧
        Module.finrank k W = e * (inertia V).index * Module.finrank k V := by
  obtain ⟨V, hV, hfinite, e, he, ⟨iso⟩⟩ := W.clifford_restrict_iso (N := N)
  let _ : Finite (G ⧸ inertia V) := hfinite
  refine ⟨V, hV, hfinite, e, he, ⟨iso⟩, ?_⟩
  have h : Module.finrank k W = Module.finrank k (V.cliffordSum e) :=
    (isoToLinearEquiv iso).finrank_eq
  rw [finrank_cliffordSum, ← Subgroup.index_eq_card] at h
  rw [h]
  ring

/-- **Clifford theory when the dimension is coprime to the index.**  If the dimension of an
irreducible `W : FDRep k G` is coprime to `[G : N]`, then `Res_N W` is isomorphic to `e` copies of
a single irreducible constituent `V` whose inertia group is all of `G`; consequently the character
of `W` on `N` is `e` times that of `V`, and `dim W = e * dim V`.

The number of constituents is the index `[G : inertia V]`, which divides `[G : N]` because
`N ≤ inertia V`, and divides `dim W` by the dimension identity that
`FDRep.clifford_restrict_finrank` records.  Coprimality leaves it no value but `1`, so
`inertia V = ⊤` and `V.cliffordSum e` has a single conjugate summand.

An irreducible of odd dimension over a subgroup of index two is the instance of this that arises
for `alternatingGroup α ◁ Equiv.Perm α`, complementary to
`TauCeti.inertia_ofLinearCharacter_alternatingGroup`, where a linear character of the alternating
group has the *smallest* inertia group instead. -/
theorem clifford_restrict_inertia_eq_top_of_coprime [IsAlgClosed k] (W : FDRep k G) [Simple W]
    (hcop : Nat.Coprime (Module.finrank k W) N.index) :
    ∃ (V : FDRep k N) (_ : Simple V) (hfinite : Finite (G ⧸ inertia V)),
      let _ := hfinite
      ∃ e : ℕ, e ≠ 0 ∧ inertia V = ⊤ ∧ Nonempty (resFDRep N W ≅ V.cliffordSum e) ∧
        Module.finrank k W = e * Module.finrank k V ∧
        ∀ n : N, W.character (n : G) = (e : k) * V.character n := by
  obtain ⟨V, hV, hfinite, e, he, ⟨iso⟩, hdim⟩ := W.clifford_restrict_finrank (N := N)
  let _ : Finite (G ⧸ inertia V) := hfinite
  -- The index of the inertia group divides both the dimension and the index of `N`.
  have hdvdW : (inertia V).index ∣ Module.finrank k W :=
    ⟨e * Module.finrank k V, by rw [hdim]; ring⟩
  have hdvdN : (inertia V).index ∣ N.index := Subgroup.index_dvd_of_le (le_inertia V)
  have hone : (inertia V).index = 1 := Nat.eq_one_of_dvd_coprimes hcop hdvdW hdvdN
  have htop : inertia V = ⊤ := Subgroup.index_eq_one.1 hone
  -- A single inertia coset means a single summand, whose conjugate of `V` is `V` again.
  have hsub : Subsingleton (G ⧸ inertia V) := by
    rw [htop]
    exact QuotientGroup.subsingleton_quotient_top
  let _ : Unique (G ⧸ inertia V) := uniqueOfSubsingleton (QuotientGroup.mk (1 : G))
  have hiso : conjNormalFDRep (Quotient.out (default : G ⧸ inertia V)) V ≅ V :=
    (mem_inertia_iff.1 (htop ▸ Subgroup.mem_top _)).some
  refine ⟨V, hV, hfinite, e, he, htop, ⟨iso⟩, by rw [hdim, hone, mul_one], fun n ↦ ?_⟩
  have hchar := congrFun (char_iso iso) n
  rw [character_resFDRep, character_cliffordSum, finsum_unique,
    congrFun (char_iso hiso) n] at hchar
  exact hchar

end FDRep
