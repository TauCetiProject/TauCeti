/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Indicator
public import Mathlib.Computability.Reduce
public import Mathlib.Computability.TuringDegree
import TauCeti.Computability.RecursiveIn

/-!
# Set oracles and the Turing join

Mathlib's `TuringReducible` compares partial functions `ℕ →. ℕ`. A set of naturals is used as an
oracle through its characteristic function: `A.oracle` is the total partial function with values
`A.indicator 1`, answering `1` on `A` and `0` off it. Turing reducibility of sets is Turing
reducibility of these oracles.

The **Turing join** `f.turingJoin g` of two partial functions answers `f` on even inputs and `g` on
odd inputs, and records the side in the parity of its output. It is the least upper bound of `f` and
`g` for Turing reducibility, which makes Mathlib's `TuringDegree` a join-semilattice. For sets, the
**parity join** `A.turingJoin B = {2 * x | x ∈ A} ∪ {2 * x + 1 | x ∈ B}` has an oracle Turing
equivalent to the Turing join of the two oracles, so it is the least upper bound of `A` and `B`
among sets, and its degree is the supremum of their degrees.

## Main definitions

* `Set.oracle`: the characteristic function of a set of naturals, as an oracle.
* `PFun.turingJoin`: the Turing join of two partial functions `ℕ →. ℕ`.
* `Set.turingJoin`: the parity join of two sets of naturals.
* The `SemilatticeSup` instance on `TuringDegree`, whose supremum is induced by the Turing join.

## Main results

* `ManyOneReducible.turingReducible_oracle`: a many-one reduction of sets gives a Turing reduction
  of their oracles.
* `TuringReducible.turingJoin_left`, `TuringReducible.turingJoin_right`,
  `PFun.turingJoin_turingReducible_iff`: the Turing join is the least upper bound for Turing
  reducibility.
* `Set.oracle_turingJoin_turingEquivalent`: the oracle of the parity join of two sets is Turing
  equivalent to the Turing join of their oracles.
* `Set.oracle_turingJoin_turingReducible_iff`: the parity join is the least upper bound of two sets
  for Turing reducibility.
* `TuringDegree.toAntisymmetrization_oracle_turingJoin`: the degree of the parity join of two sets
  is the supremum of their degrees.

## References

* R. I. Soare, *Recursively Enumerable Sets and Degrees*, Springer, 1987, Chapters III.1 and
  III.2.
* The Turing join of partial functions, coding both its input and its output by parity, its
  least-upper-bound lemmas and the `SemilatticeSup` instance on `TuringDegree` follow Tanner Duve's
  Mathlib pull request 37062.
-/

public section

open scoped Computability

namespace Set

/-- The oracle of a set of naturals: its characteristic function `A.indicator 1`, as a total
partial function. -/
noncomputable def oracle (A : Set ℕ) : ℕ →. ℕ :=
  fun n => Part.some (A.indicator 1 n)

/-- The oracle of `A` answers `A.indicator 1 n` at `n`. -/
@[simp]
theorem oracle_apply (A : Set ℕ) (n : ℕ) : A.oracle n = Part.some (A.indicator 1 n) :=
  (rfl)

end Set

/-- A many-one reduction of sets of naturals gives a Turing reduction of their oracles: query the
oracle of `B` at the image of the input. -/
theorem ManyOneReducible.turingReducible_oracle {A B : Set ℕ}
    (h : ManyOneReducible (· ∈ A) (· ∈ B)) : TuringReducible A.oracle B.oracle := by
  obtain ⟨f, hf, hAB⟩ := h
  refine RecursiveIn.iff_nat.2 <|
    ((Nat.RecursiveIn.oracle _ rfl).comp (Partrec.nat_iff.1 hf).recursiveIn).of_eq fun n =>
    (Part.bind_some _ _).trans ?_
  by_cases hn : n ∈ A
  · simp [hn, (hAB n).1 hn]
  · simp [hn, mt (hAB n).2 hn]

/-! ### The Turing join of partial functions -/

namespace PFun

/-- The **Turing join** of two partial functions `ℕ →. ℕ`. It sends `2 * n` to `2 * y` for each
value `y` of `f n`, and `2 * n + 1` to `2 * y + 1` for each value `y` of `g n`: the parity of the
input selects the side, and the parity of the output records it. -/
def turingJoin (f g : ℕ →. ℕ) : ℕ →. ℕ :=
  fun n => bif n.bodd then (g n.div2).map (2 * · + 1) else (f n.div2).map (2 * ·)

/-- The Turing join answers `f` on even inputs, doubling its values. -/
@[simp]
theorem turingJoin_two_mul (f g : ℕ →. ℕ) (n : ℕ) :
    f.turingJoin g (2 * n) = (f n).map (2 * ·) := by
  simp [turingJoin, Nat.div2_val]

/-- The Turing join answers `g` on odd inputs, sending each value `y` to `2 * y + 1`. -/
@[simp]
theorem turingJoin_two_mul_add_one (f g : ℕ →. ℕ) (n : ℕ) :
    f.turingJoin g (2 * n + 1) = (g n).map (2 * · + 1) := by
  simp [turingJoin, Nat.div2_val, Nat.bodd_mul]

end PFun

/-- A partial function is Turing reducible to its Turing join with any other: query the join at
`2 * n` and halve the answer. -/
theorem TuringReducible.turingJoin_left (f g : ℕ →. ℕ) : f ≤ᵀ f.turingJoin g := by
  refine RecursiveIn.iff_nat.2 <|
    (((Nat.RecursiveIn.oracle _ rfl).comp_primrec
      (Primrec.nat_iff.1 Primrec.nat_double)).map_primrec
      (Primrec.nat_iff.1 Primrec.nat_div2)).of_eq fun n => ?_
  simp [Part.map_map, Function.comp_def, Nat.div2_val, Part.map_id']

/-- A partial function is Turing reducible to the Turing join of any other with it: query the join
at `2 * n + 1` and halve the answer. -/
theorem TuringReducible.turingJoin_right (f g : ℕ →. ℕ) : g ≤ᵀ f.turingJoin g := by
  refine RecursiveIn.iff_nat.2 <|
    (((Nat.RecursiveIn.oracle _ rfl).comp_primrec
      (Primrec.nat_iff.1 Primrec.nat_double_succ)).map_primrec
      (Primrec.nat_iff.1 Primrec.nat_div2)).of_eq fun n => ?_
  simp [Part.map_map, Function.comp_def, Nat.div2_val, Part.map_id']

namespace PFun

variable {f g h : ℕ →. ℕ}

/-- The Turing join of two partial functions reducible to `h` is reducible to `h`: on input `n`,
run the reduction of `f` or of `g` at `n.div2` according to the parity of `n`. -/
theorem turingJoin_turingReducible (hf : f ≤ᵀ h) (hg : g ≤ᵀ h) : f.turingJoin g ≤ᵀ h := by
  have hd := Primrec.nat_iff.1 Primrec.nat_div2
  exact RecursiveIn.iff_nat.2 <| Nat.RecursiveIn.cond Computable.nat_bodd
    (((RecursiveIn.iff_nat.1 hg).comp_primrec hd).map_primrec
      (Primrec.nat_iff.1 Primrec.nat_double_succ))
    (((RecursiveIn.iff_nat.1 hf).comp_primrec hd).map_primrec
      (Primrec.nat_iff.1 Primrec.nat_double))

/-- **The Turing join is the least upper bound** for Turing reducibility: it is reducible to `h`
exactly when both of its sides are. -/
theorem turingJoin_turingReducible_iff : f.turingJoin g ≤ᵀ h ↔ f ≤ᵀ h ∧ g ≤ᵀ h :=
  ⟨fun hfg => ⟨(TuringReducible.turingJoin_left f g).trans hfg,
    (TuringReducible.turingJoin_right f g).trans hfg⟩,
    fun ⟨hf, hg⟩ => turingJoin_turingReducible hf hg⟩

end PFun

/-- The Turing join is monotone for Turing reducibility in both arguments. -/
theorem TuringReducible.turingJoin {f f' g g' : ℕ →. ℕ} (hf : f ≤ᵀ f') (hg : g ≤ᵀ g') :
    f.turingJoin g ≤ᵀ f'.turingJoin g' :=
  PFun.turingJoin_turingReducible (hf.trans (turingJoin_left f' g'))
    (hg.trans (turingJoin_right f' g'))

/-- The Turing join respects Turing equivalence in both arguments. -/
theorem TuringEquivalent.turingJoin {f f' g g' : ℕ →. ℕ} (hf : f ≡ᵀ f') (hg : g ≡ᵀ g') :
    f.turingJoin g ≡ᵀ f'.turingJoin g' :=
  ⟨hf.1.turingJoin hg.1, hf.2.turingJoin hg.2⟩

/-! ### Turing degrees form a join-semilattice -/

namespace TuringDegree

/-- The order on Turing degrees is Turing reducibility of representatives. This holds by the
definition of the order on `TuringDegree`, which Mathlib induces from `TuringReducible`. -/
@[simp]
theorem toAntisymmetrization_le_toAntisymmetrization_iff {f g : ℕ →. ℕ} :
    toAntisymmetrization TuringReducible f ≤ toAntisymmetrization TuringReducible g ↔ f ≤ᵀ g :=
  Iff.rfl

/-- Turing degrees form a join-semilattice: the supremum of the degrees of `f` and `g` is the degree
of their Turing join. -/
instance instSemilatticeSup : SemilatticeSup TuringDegree where
  sup := Quotient.map₂ PFun.turingJoin fun _ _ hf _ _ hg => TuringEquivalent.turingJoin hf hg
  le_sup_left a b := by
    induction a using Antisymmetrization.ind with | _ f
    induction b using Antisymmetrization.ind with | _ g
    exact toAntisymmetrization_le_toAntisymmetrization_iff.2 (.turingJoin_left f g)
  le_sup_right a b := by
    induction a using Antisymmetrization.ind with | _ f
    induction b using Antisymmetrization.ind with | _ g
    exact toAntisymmetrization_le_toAntisymmetrization_iff.2 (.turingJoin_right f g)
  sup_le a b c := by
    induction a using Antisymmetrization.ind with | _ f
    induction b using Antisymmetrization.ind with | _ g
    induction c using Antisymmetrization.ind with | _ h
    simp only [toAntisymmetrization_le_toAntisymmetrization_iff]
    exact PFun.turingJoin_turingReducible

/-- The supremum of the degrees of `f` and `g` is the degree of their Turing join. -/
@[simp]
theorem toAntisymmetrization_sup_toAntisymmetrization (f g : ℕ →. ℕ) :
    toAntisymmetrization TuringReducible f ⊔ toAntisymmetrization TuringReducible g =
      toAntisymmetrization TuringReducible (f.turingJoin g) :=
  (rfl)

end TuringDegree

/-! ### The parity join of sets -/

namespace Set

/-- The **parity join** `{2 * x | x ∈ A} ∪ {2 * x + 1 | x ∈ B}` of two sets of naturals. -/
def turingJoin (A B : Set ℕ) : Set ℕ :=
  (2 * ·) '' A ∪ (2 * · + 1) '' B

variable {A B : Set ℕ} {n : ℕ}

/-- An even number `2 * n` lies in the parity join of `A` and `B` exactly when `n ∈ A`. -/
@[simp]
theorem two_mul_mem_turingJoin : 2 * n ∈ A.turingJoin B ↔ n ∈ A := by
  simp only [turingJoin, mem_union, mem_image]
  grind

/-- An odd number `2 * n + 1` lies in the parity join of `A` and `B` exactly when `n ∈ B`. -/
@[simp]
theorem two_mul_add_one_mem_turingJoin : 2 * n + 1 ∈ A.turingJoin B ↔ n ∈ B := by
  simp only [turingJoin, mem_union, mem_image]
  grind

/-- A number `n` lies in the parity join of `A` and `B` exactly when `n.div2` lies in `B` if `n` is
odd, and in `A` if `n` is even. -/
theorem mem_turingJoin : n ∈ A.turingJoin B ↔ n.div2 ∈ cond n.bodd B A := by
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' n <;> simp [Nat.div2_val, Nat.bodd_mul]

/-- The oracle of the parity join of two sets is Turing equivalent to the Turing join of their
oracles. -/
theorem oracle_turingJoin_turingEquivalent (A B : Set ℕ) :
    (A.turingJoin B).oracle ≡ᵀ A.oracle.turingJoin B.oracle := by
  refine ⟨RecursiveIn.iff_nat.2 <| ((Nat.RecursiveIn.oracle _ rfl).map_primrec
    (Primrec.nat_iff.1 Primrec.nat_div2)).of_eq fun n => ?_,
    PFun.turingJoin_turingReducible
      (ManyOneReducible.turingReducible_oracle ⟨(2 * ·), ?_, fun _ => ?_⟩)
      (ManyOneReducible.turingReducible_oracle ⟨(2 * · + 1), ?_, fun _ => ?_⟩)⟩
  · obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' n
    · by_cases hm : m ∈ A <;> simp [hm, Nat.div2_val]
    · by_cases hm : m ∈ B <;> simp [hm, Nat.div2_val]
  · exact Primrec.nat_double.to_comp
  · simp
  · exact Primrec.nat_double_succ.to_comp
  · simp

/-- The oracle of `A` is Turing reducible to the oracle of the parity join of `A` and `B`. -/
theorem oracle_turingReducible_turingJoin_left (A B : Set ℕ) :
    A.oracle ≤ᵀ (A.turingJoin B).oracle :=
  (TuringReducible.turingJoin_left _ _).trans (oracle_turingJoin_turingEquivalent A B).2

/-- The oracle of `B` is Turing reducible to the oracle of the parity join of `A` and `B`. -/
theorem oracle_turingReducible_turingJoin_right (A B : Set ℕ) :
    B.oracle ≤ᵀ (A.turingJoin B).oracle :=
  (TuringReducible.turingJoin_right _ _).trans (oracle_turingJoin_turingEquivalent A B).2

/-- **The parity join is the least upper bound** of two sets for Turing reducibility: its oracle is
reducible to `h` exactly when the oracles of both sets are. -/
theorem oracle_turingJoin_turingReducible_iff {h : ℕ →. ℕ} :
    (A.turingJoin B).oracle ≤ᵀ h ↔ A.oracle ≤ᵀ h ∧ B.oracle ≤ᵀ h :=
  ⟨fun hAB => ⟨(oracle_turingReducible_turingJoin_left A B).trans hAB,
    (oracle_turingReducible_turingJoin_right A B).trans hAB⟩,
    fun ⟨hA, hB⟩ => (oracle_turingJoin_turingEquivalent A B).1.trans
      (PFun.turingJoin_turingReducible hA hB)⟩

end Set

/-- The degree of the parity join of two sets is the supremum of their degrees. -/
theorem TuringDegree.toAntisymmetrization_oracle_turingJoin (A B : Set ℕ) :
    toAntisymmetrization TuringReducible (A.turingJoin B).oracle =
      toAntisymmetrization TuringReducible A.oracle ⊔
        toAntisymmetrization TuringReducible B.oracle := by
  rw [toAntisymmetrization_sup_toAntisymmetrization, toAntisymmetrization_eq]
  exact Set.oracle_turingJoin_turingEquivalent A B
