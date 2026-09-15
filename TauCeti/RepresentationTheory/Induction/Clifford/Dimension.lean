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

so in particular the index of the inertia group divides `dim W`, and so does the dimension of the
constituent.  That index divides `[G : N]` as well, because `N ≤ inertia V`, so the number of
distinct conjugates occurring is constrained from two sides at once: by the degree of `W` and by
the index of `N`, neither constraint mentioning the multiplicity `e`.

Two special cases follow from that arithmetic.  Whenever `dim W` and `[G : N]` are **coprime** the
index is `1`: the inertia group is everything, there is a single constituent, and the character of
`W` on `N` is `e` times that of `V`.  A subgroup of index two and an irreducible of odd dimension
are coprime in that sense, which is the case arising for `alternatingGroup α ◁ Equiv.Perm α`,
complementary to the linear-character computation of
`TauCeti/RepresentationTheory/Induction/Clifford/Alternating.lean`, where the inertia group is as
*small* as Clifford theory allows.  And when `dim W = 1` the right-hand side of the dimension
identity is a product of natural numbers equal to `1`, so every factor is `1`: a linear character
of `G` restricts to a linear character of `N` that the whole group fixes.

## Main statements

* `FDRep.clifford_restrict_finrank`: **Clifford's theorem, dimension form**, packaging the
  constituent together with its decomposition of `Res_N W`, the multiplicity and the identity
  `dim W = e * [G : inertia V] * dim V` as natural numbers.
* `FDRep.clifford_restrict_dvd_finrank`: the divisibilities that identity contains,
  `[G : inertia V] ∣ dim W` and `dim V ∣ dim W`, together with `[G : inertia V] ∣ [G : N]` and the
  count `[G : inertia V] ∣ dim W / (e * dim V)` with the multiplicity divided out, stated for a
  constituent `V` supplied with its decomposition of `Res_N W`.
* `FDRep.clifford_restrict_inertia_eq_top_of_coprime`: when the dimension of `W` is **coprime**
  to `[G : N]`, the restriction of `W` to `N` is isomorphic to `e` copies of a single constituent
  `V` whose inertia group is all of `G`, the character of `W` on `N` being `e` times that of `V`
  and `dim W = e * dim V`.
* `FDRep.clifford_restrict_inertia_eq_top_of_finrank_eq_one`: a one-dimensional representation of
  `G` restricts to a one-dimensional representation of `N` whose inertia group is all of `G`, the
  restriction being a single copy of it.

## References

* I. M. Isaacs, *Character Theory of Finite Groups*, Chapter 6.
* C. W. Curtis and I. Reiner, *Representation Theory of Finite Groups and Associative Algebras*,
  §49.
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
is the arithmetic that `FDRep.clifford_restrict_dvd_finrank` reads off and that
`FDRep.clifford_restrict_inertia_eq_top_of_coprime` exploits. -/
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

/-- **The divisibilities in Clifford's theorem.**  For an irreducible constituent `V` of the
restriction of an irreducible `W` to a normal subgroup, both the index of the inertia group of `V`
and the dimension of `V` divide the dimension of `W`; the index divides `[G : N]`, and it divides
the quotient `dim W / (e * dim V)` that the dimension identity leaves.

The decomposition `Res_N W ≅ V.cliffordSum e` is carried along from
`FDRep.clifford_restrict_finrank`, so that `V` is exhibited as a constituent of the restriction and
the divisibilities are read as statements about that constituent rather than about some unrelated
irreducible representation of `N`.

This is the form in which the dimension identity of `FDRep.clifford_restrict_finrank` is used.  The
number of distinct conjugates occurring in the restriction is `[G : inertia V]`, and it is
constrained from two sides at once: by the degree of `W`, through the dimension identity, and by
the index of `N`, through `TauCeti.le_inertia`.  Neither constraint mentions the multiplicity `e`,
which the last divisibility divides out instead: `dim W / (e * dim V)` is the roadmap's form of the
count of distinct conjugates. -/
theorem clifford_restrict_dvd_finrank [IsAlgClosed k] (W : FDRep k G) [Simple W] :
    ∃ (V : FDRep k N) (_ : Simple V) (hfinite : Finite (G ⧸ inertia V)),
      let _ := hfinite
      ∃ e : ℕ, e ≠ 0 ∧ Nonempty (resFDRep N W ≅ V.cliffordSum e) ∧
        (inertia V).index ∣ Module.finrank k W ∧ Module.finrank k V ∣ Module.finrank k W ∧
          (inertia V).index ∣ N.index ∧
            (inertia V).index ∣ Module.finrank k W / (e * Module.finrank k V) := by
  obtain ⟨V, hV, hfinite, e, he, hiso, hdim⟩ := W.clifford_restrict_finrank (N := N)
  let _ : Finite (G ⧸ inertia V) := hfinite
  refine ⟨V, hV, hfinite, e, he, hiso, ⟨e * Module.finrank k V, by rw [hdim]; ring⟩,
    ⟨e * (inertia V).index, by rw [hdim]; ring⟩, Subgroup.index_dvd_of_le (le_inertia V), ?_⟩
  rcases Nat.eq_zero_or_pos (e * Module.finrank k V) with hzero | hpos
  · simp [hzero]
  · rw [show Module.finrank k W = e * Module.finrank k V * (inertia V).index by rw [hdim]; ring,
      Nat.mul_div_cancel_left _ hpos]

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

/-- **A linear character restricts to an invariant linear character.**  If `W` is one-dimensional,
then an irreducible constituent of its restriction to a normal subgroup is one-dimensional and is
fixed by the conjugation action of the whole group, its inertia group being all of `G`.

The right-hand side of the dimension identity of `FDRep.clifford_restrict_finrank` is a product of
natural numbers, so its being `1` forces each of the three factors to be `1`.  The multiplicity is
therefore `1` too, and the decomposition `Res_N W ≅ V.cliffordSum 1` exhibiting `V` as the
constituent is returned alongside. -/
theorem clifford_restrict_inertia_eq_top_of_finrank_eq_one [IsAlgClosed k] (W : FDRep k G)
    [Simple W] (hW : Module.finrank k W = 1) :
    ∃ (V : FDRep k N) (_ : Simple V) (hfinite : Finite (G ⧸ inertia V)),
      let _ := hfinite
      Nonempty (resFDRep N W ≅ V.cliffordSum 1) ∧ inertia V = ⊤ ∧
        Module.finrank k V = 1 := by
  obtain ⟨V, hV, hfinite, e, -, hiso, hdim⟩ := W.clifford_restrict_finrank (N := N)
  let _ : Finite (G ⧸ inertia V) := hfinite
  rw [hW] at hdim
  obtain ⟨hleft, hright⟩ := mul_eq_one.mp hdim.symm
  obtain ⟨he, hindex⟩ := mul_eq_one.mp hleft
  subst he
  exact ⟨V, hV, hfinite, hiso, Subgroup.index_eq_one.mp hindex, hright⟩

end FDRep
