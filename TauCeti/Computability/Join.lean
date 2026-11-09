/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Computability.TuringDegree
import TauCeti.Computability.RecursiveIn

/-!
# The parity join of sets

The join of two sets of naturals is `A ⊕ B = {2x : x ∈ A} ∪ {2x + 1 : x ∈ B}`: the even numbers
carry `A` and the odd numbers carry `B`. Its degree is the least upper bound of the degrees of `A`
and `B`: each of `A` and `B` reduces to `A ⊕ B`, by a computable injective change of input, and
an oracle computing both `A` and `B` computes `A ⊕ B`, by consulting `A` or `B` at `n / 2`
according to the parity of `n`.

The join is the standard way to combine two sets into one oracle. For instance, the two halves
of a disjoint c.e. splitting of `B` have join of the same degree as `B`.

## Main definitions

* `Set.join`: the parity join `A ⊕ B` of two sets of naturals.

## Main results

* `Set.mem_join`: membership in the join, read off from the parity and the half of a number.
* `Set.oneOneReducible_join_left`, `Set.oneOneReducible_join_right`: each set one-one reduces to
  the join.
* `Set.join_turingReducible_iff`: the join reduces to an oracle exactly when both sets do.
* `Set.isLUB_degree_join`: in Mathlib's quotient of partial functions, the degree of the join is
  the least upper bound of the degrees of the two sets.

## References

* R. I. Soare, *Recursively Enumerable Sets and Degrees*, Springer, 1987, Chapter III.2.
* T. Duve, [Mathlib PR #37062](https://github.com/leanprover-community/mathlib4/pull/37062),
  *feat(Computability): Turing join and semilattice structure on Turing degrees*. The shape of
  this API (left and right reductions to the join, and its least upper bound property) follows
  the join of partial functions proposed there; here everything is stated for set oracles.
-/

public section

namespace Set

/-- The **parity join** `A ⊕ B = {2x : x ∈ A} ∪ {2x + 1 : x ∈ B}` of two sets of naturals. -/
def join (A B : Set ℕ) : Set ℕ :=
  (fun x => 2 * x) '' A ∪ (fun x => 2 * x + 1) '' B

variable {A B : Set ℕ}

/-- An even number `n` is in `A ⊕ B` when `n / 2 ∈ A`, and an odd number when `n / 2 ∈ B`. -/
theorem mem_join {n : ℕ} : n ∈ A.join B ↔ n % 2 = 0 ∧ n / 2 ∈ A ∨ n % 2 = 1 ∧ n / 2 ∈ B := by
  simp only [join, mem_union, mem_image]
  constructor
  · rintro (⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩)
    · exact Or.inl ⟨by omega, by simpa using hx⟩
    · exact Or.inr ⟨by omega, by simpa [Nat.mul_add_div] using hx⟩
  · rintro (⟨hn, h⟩ | ⟨hn, h⟩)
    · exact Or.inl ⟨n / 2, h, by omega⟩
    · exact Or.inr ⟨n / 2, h, by omega⟩

/-- `2x ∈ A ⊕ B` exactly when `x ∈ A`. -/
@[simp]
theorem two_mul_mem_join {x : ℕ} : 2 * x ∈ A.join B ↔ x ∈ A := by
  simp [mem_join]

/-- `2x + 1 ∈ A ⊕ B` exactly when `x ∈ B`. -/
@[simp]
theorem two_mul_add_one_mem_join {x : ℕ} : 2 * x + 1 ∈ A.join B ↔ x ∈ B := by
  simp [mem_join, Nat.mul_add_div]

/-- `A` one-one reduces to `A ⊕ B`, by `x ↦ 2x`. -/
theorem oneOneReducible_join_left : OneOneReducible (· ∈ A) (· ∈ A.join B) :=
  ⟨fun x => 2 * x, (Primrec.nat_mul.comp (Primrec.const 2) Primrec.id).to_comp,
    fun x y (h : 2 * x = 2 * y) => by omega, fun _ => two_mul_mem_join.symm⟩

/-- `B` one-one reduces to `A ⊕ B`, by `x ↦ 2x + 1`. -/
theorem oneOneReducible_join_right : OneOneReducible (· ∈ B) (· ∈ A.join B) :=
  ⟨fun x => 2 * x + 1,
    (Primrec.succ.comp (Primrec.nat_mul.comp (Primrec.const 2) Primrec.id)).to_comp,
    fun x y (h : 2 * x + 1 = 2 * y + 1) => by omega, fun _ => two_mul_add_one_mem_join.symm⟩

/-- `A` is Turing reducible to `A ⊕ B`. -/
theorem turingReducible_join_left : TuringReducible A.oracle (A.join B).oracle :=
  oneOneReducible_join_left.to_many_one.turingReducible_oracle

/-- `B` is Turing reducible to `A ⊕ B`. -/
theorem turingReducible_join_right : TuringReducible B.oracle (A.join B).oracle :=
  oneOneReducible_join_right.to_many_one.turingReducible_oracle

/-- If `A` and `B` are Turing reducible to an oracle `g`, so is `A ⊕ B`: consult `A` or `B` at
`n / 2` according to the parity of `n`. -/
theorem join_turingReducible {g : ℕ →. ℕ} (hA : TuringReducible A.oracle g)
    (hB : TuringReducible B.oracle g) : TuringReducible (A.join B).oracle g := by
  classical
  have hhalf : Nat.Primrec fun n => n / 2 :=
    Primrec.nat_iff.1 (Primrec.nat_div.comp Primrec.id (Primrec.const 2))
  -- on `Nat.pair n (Nat.pair a b)`, return `a` for even `n` and `b` for odd `n`
  have hsel : Nat.Primrec fun p : ℕ =>
      if p.unpair.1 % 2 = 0 then p.unpair.2.unpair.1 else p.unpair.2.unpair.2 :=
    Primrec.nat_iff.1 <| Primrec.ite
      (Primrec.eq.comp (Primrec.nat_mod.comp (Primrec.fst.comp Primrec.unpair) (Primrec.const 2))
        (Primrec.const 0))
      (Primrec.fst.comp <| Primrec.unpair.comp <| Primrec.snd.comp Primrec.unpair)
      (Primrec.snd.comp <| Primrec.unpair.comp <| Primrec.snd.comp Primrec.unpair)
  have h := (Nat.Primrec.id.recursiveIn.pair (((RecursiveIn.iff_nat.1 hA).comp_primrec hhalf).pair
    ((RecursiveIn.iff_nat.1 hB).comp_primrec hhalf))).map_primrec hsel
  refine RecursiveIn.iff_nat.2 (h.of_eq fun n => ?_)
  rcases Nat.mod_two_eq_zero_or_one n with hn | hn <;>
    simp [Seq.seq, indicator_apply, mem_join, hn]

/-- `A ⊕ B` is Turing reducible to an oracle `g` exactly when both `A` and `B` are. -/
theorem join_turingReducible_iff {g : ℕ →. ℕ} :
    TuringReducible (A.join B).oracle g ↔
      TuringReducible A.oracle g ∧ TuringReducible B.oracle g :=
  ⟨fun h => ⟨turingReducible_join_left.trans h, turingReducible_join_right.trans h⟩,
    fun h => join_turingReducible h.1 h.2⟩

/-- `A ∪ B` is Turing reducible to `A ⊕ B`. -/
theorem union_turingReducible_join : TuringReducible (A ∪ B).oracle (A.join B).oracle :=
  union_turingReducible turingReducible_join_left turingReducible_join_right

/-- In Mathlib's quotient of partial functions, the degree represented by `A ⊕ B` is the least
upper bound of the degrees represented by `A` and `B`, among all degrees. -/
theorem isLUB_degree_join (A B : Set ℕ) :
    IsLUB {toAntisymmetrization TuringReducible A.oracle,
        toAntisymmetrization TuringReducible B.oracle}
      (toAntisymmetrization TuringReducible (A.join B).oracle) := by
  refine ⟨?_, fun d hd => ?_⟩
  · rintro _ (rfl | rfl)
    · exact TauCeti.turingDegree_le_iff.2 turingReducible_join_left
    · exact TauCeti.turingDegree_le_iff.2 turingReducible_join_right
  · induction d using Antisymmetrization.induction_on with | h g => ?_
    simp only [upperBounds_insert, upperBounds_singleton, mem_inter_iff, mem_Ici,
      TauCeti.turingDegree_le_iff] at hd
    exact TauCeti.turingDegree_le_iff.2 (join_turingReducible hd.1 hd.2)

end Set
