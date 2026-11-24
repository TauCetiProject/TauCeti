/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Indicator
public import Mathlib.Computability.Reduce
public import Mathlib.Computability.TuringDegree
public import TauCeti.Data.Nat.Pairing
import TauCeti.Computability.RE
import TauCeti.Computability.RecursiveIn

/-!
# Set oracles, the Turing join and the least degree

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

Turing reducibility of sets is insensitive to complements and to computable changes of
presentation: a set is Turing equivalent to its complement, to its preimage and image under a
computable permutation of the naturals, and its part in a column `{⟨x, e⟩ | x : ℕ}` is Turing
equivalent to its `e`-th section. The least Turing degree consists of the partial computable
functions; on sets, it is the degree of the computable sets.

## Main definitions

* `Set.oracle`: the characteristic function of a set of naturals, as an oracle.
* `PFun.turingJoin`: the Turing join of two partial functions `ℕ →. ℕ`.
* `Set.turingJoin`: the parity join of two sets of naturals.
* The `SemilatticeSup` instance on `TuringDegree`, whose supremum is induced by the Turing join.
* The `OrderBot` instance on `TuringDegree`, whose least element is the degree of `∅`.

## Main results

* `ManyOneReducible.turingReducible_oracle`, `OneOneReducible.turingReducible_oracle`: a many-one
  or one-one reduction of sets gives a Turing reduction of their oracles.
* `TuringReducible.turingJoin_left`, `TuringReducible.turingJoin_right`,
  `PFun.turingJoin_turingReducible_iff`: the Turing join is the least upper bound for Turing
  reducibility.
* `Set.oracle_turingJoin_turingEquivalent`: the oracle of the parity join of two sets is Turing
  equivalent to the Turing join of their oracles.
* `Set.oracle_turingJoin_turingReducible_iff`: the parity join is the least upper bound of two sets
  for Turing reducibility.
* `TuringDegree.toAntisymmetrization_oracle_turingJoin`: the degree of the parity join of two sets
  is the supremum of their degrees.
* `Set.partrec_oracle_iff`: partial computability of a set oracle is equivalent to computability
  of membership.
* `Set.turingReducible_empty_iff`: reducibility to the empty oracle characterizes computable sets.
* `TauCeti.turingReducible_oracle_empty_iff`: reducibility to the empty oracle characterizes partial
  computable functions.
* `Set.union_turingReducible`, `TuringReducible.inter_oracle`: if two sets reduce to an oracle, so
  do their union and their intersection.
* `ComputablePred.oracle_turingReducible`: a computable set reduces to every oracle.
* `Set.oracle_compl_turingEquivalent`, `Set.toAntisymmetrization_oracle_compl`: a set and its
  complement are Turing equivalent, and have the same degree.
* `ManyOneEquiv.turingEquivalent_oracle`, `ManyOneEquiv.toAntisymmetrization_oracle_eq`:
  many-one equivalent sets are Turing equivalent, and have the same degree.
* `Set.oracle_preimage_turingReducible`: the preimage of a set under a computable function
  reduces to the set, so a computable preimage cannot raise the degree.
* `Set.oracle_preimage_turingEquivalent`, `Set.oracle_image_turingEquivalent`,
  `Set.toAntisymmetrization_oracle_preimage_equiv`, `Set.toAntisymmetrization_oracle_image_equiv`:
  the preimage and the image of a set under a computable permutation of the naturals are Turing
  equivalent to the set, and have its degree.
* `Set.oracle_image_turingEquivalent_of_leftInverse`,
  `Set.toAntisymmetrization_oracle_image_of_leftInverse`: more generally, the image of a set under
  a computable function with a computable left inverse and computable range is Turing equivalent
  to the set, and has its degree.
* `Set.oracle_inter_pairColumn_turingEquivalent`,
  `Set.toAntisymmetrization_oracle_inter_pairColumn`: the part of a set in a column is Turing
  equivalent to the corresponding section, and has the same degree.
* `TauCeti.toAntisymmetrization_eq_bot_iff`: the least degree consists of the partial
  computable functions.
* `Function.turingEquivalent_oracle_preimage_unpair_graph`: graph coding, a total function is
  Turing equivalent to the set of codes `Nat.pair x (g x)` of its graph.

## References

* R. I. Soare, *Recursively Enumerable Sets and Degrees*, Springer, 1987, Chapters III.1 and
  III.2.
* The Turing join of partial functions, coding both its input and its output by parity, its
  least-upper-bound lemmas and the `SemilatticeSup` instance on `TuringDegree` follow Tanner Duve's
  Mathlib pull request 37062.
-/

public section

open scoped Computability

namespace TauCeti

/-- The order on degrees represented by partial functions is Turing reducibility. -/
@[simp]
theorem turingDegree_le_iff {f g : ℕ →. ℕ} :
    toAntisymmetrization TuringReducible f ≤ toAntisymmetrization TuringReducible g ↔
      TuringReducible f g := by
  -- Mathlib's generic quotient-order lemma requires its private partial-function preorder.
  -- The lifted degree order on representatives is definitionally Iff.rfl.
  exact Iff.rfl

end TauCeti

namespace Set

/-- The oracle of a set of naturals: its characteristic function `A.indicator 1`, as a total
partial function. -/
noncomputable def oracle (A : Set ℕ) : ℕ →. ℕ :=
  fun n => Part.some (A.indicator 1 n)

/-- The oracle of `A` answers `A.indicator 1 n` at `n`. -/
@[simp]
theorem oracle_apply (A : Set ℕ) (n : ℕ) : A.oracle n = Part.some (A.indicator 1 n) :=
  (rfl)

/-- The oracle of `A` is its characteristic function `A.indicator 1`, lifted to a partial
function. -/
theorem oracle_eq_indicator (A : Set ℕ) :
    A.oracle = ((A.indicator 1 : ℕ → ℕ) : ℕ →. ℕ) :=
  (rfl)

/-- A set's characteristic function is computable in its own oracle. -/
theorem computableIn_indicator (A : Set ℕ) : ComputableIn {A.oracle} (A.indicator 1 : ℕ → ℕ) :=
  RecursiveIn.of_eq (RecursiveIn.oracle A.oracle rfl) fun n => A.oracle_apply n

/-- Reducing a set oracle is equivalent to computing its characteristic function. -/
theorem turingReducible_iff_computableIn_indicator (A : Set ℕ) (O : ℕ →. ℕ) :
    TuringReducible A.oracle O ↔ ComputableIn {O} (A.indicator 1 : ℕ → ℕ) := by
  rw [TuringReducible, funext A.oracle_apply, ComputableIn]

/-- The empty set answers zero on every input. -/
@[simp]
theorem oracle_empty : (∅ : Set ℕ).oracle = fun _ => Part.some 0 := by
  ext n
  simp

/-- A set oracle is partial computable exactly when membership in the set is computable. -/
@[simp]
theorem partrec_oracle_iff (A : Set ℕ) : Partrec A.oracle ↔ ComputablePred (· ∈ A) := by
  classical
  constructor
  · intro h
    have hχ : Computable (A.indicator 1 : ℕ → ℕ) :=
      h.of_eq_tot fun n => by simp
    refine Computable.computablePred <|
      (Primrec.beq.to_comp.comp hχ (Computable.const 1)).of_eq fun n => ?_
    by_cases hn : n ∈ A <;> simp [hn]
  · intro h
    exact ((h.ite (Computable.const 1) (Computable.const 0)).partrec).of_eq fun n => by
      by_cases hn : n ∈ A <;> simp [hn]

/-- The empty set oracle is Turing reducible to every partial function. -/
theorem empty_turingReducible (g : ℕ →. ℕ) : TuringReducible (∅ : Set ℕ).oracle g := by
  rw [oracle_empty]
  exact (Computable.const 0).partrec.turingReducible

end Set

/-- A partial function is Turing reducible to the empty oracle exactly when it is partial
computable. This is a `simp↓` lemma so that it fires before `Set.oracle_empty`. -/
@[simp↓]
theorem TauCeti.turingReducible_oracle_empty_iff {f : ℕ →. ℕ} :
    TuringReducible f (∅ : Set ℕ).oracle ↔ Partrec f := by
  rw [TuringReducible, Set.oracle_empty]
  exact TauCeti.recursiveIn_const_iff

namespace Set

/-- A set is Turing reducible to the empty oracle exactly when its membership is computable. -/
theorem turingReducible_empty_iff (A : Set ℕ) :
    TuringReducible A.oracle (∅ : Set ℕ).oracle ↔ ComputablePred (· ∈ A) :=
  TauCeti.turingReducible_oracle_empty_iff.trans (partrec_oracle_iff A)

/-- If `A` and `B` are Turing reducible to an oracle `g`, so is `A ∪ B`: take the maximum of the
two answers. -/
theorem union_turingReducible {A B : Set ℕ} {g : ℕ →. ℕ} (hA : TuringReducible A.oracle g)
    (hB : TuringReducible B.oracle g) : TuringReducible (A ∪ B).oracle g := by
  classical
  have h := ((RecursiveIn.iff_nat.1 hA).pair (RecursiveIn.iff_nat.1 hB)).map_primrec
    (g := fun p => max p.unpair.1 p.unpair.2) <| Primrec.nat_iff.1 <|
      Primrec.nat_max.comp (Primrec.fst.comp Primrec.unpair) (Primrec.snd.comp Primrec.unpair)
  refine RecursiveIn.iff_nat.2 (h.of_eq fun n => ?_)
  by_cases hnA : n ∈ A <;> by_cases hnB : n ∈ B <;> simp [Seq.seq, hnA, hnB]

end Set

/-- A computable set is Turing reducible to every oracle. -/
theorem ComputablePred.oracle_turingReducible {A : Set ℕ} (hA : ComputablePred (· ∈ A))
    (g : ℕ →. ℕ) : TuringReducible A.oracle g :=
  ((Set.partrec_oracle_iff A).2 hA).turingReducible

namespace Set

/-! ### Complement invariance -/

/-- The complement of a set is Turing reducible to the set. -/
theorem oracle_compl_turingReducible (A : Set ℕ) : TuringReducible Aᶜ.oracle A.oracle := by
  classical
  rw [turingReducible_iff_computableIn_indicator]
  refine RecursiveIn.of_eq (ComputableIn.comp (f := fun p : ℕ × ℕ => p.1 - p.2)
    Primrec.nat_sub.computableIn ((ComputableIn.const 1).pair (computableIn_indicator A)))
    fun n => ?_
  by_cases hn : n ∈ A <;> simp [hn]

/-- **Complement invariance.** A set and its complement are Turing equivalent. -/
theorem oracle_compl_turingEquivalent (A : Set ℕ) : TuringEquivalent Aᶜ.oracle A.oracle :=
  ⟨A.oracle_compl_turingReducible, by simpa using Aᶜ.oracle_compl_turingReducible⟩

/-- The complement of `A` is Turing reducible to an oracle exactly when `A` is. -/
@[simp]
theorem oracle_compl_turingReducible_iff {A : Set ℕ} {g : ℕ →. ℕ} :
    TuringReducible Aᶜ.oracle g ↔ TuringReducible A.oracle g :=
  ⟨(A.oracle_compl_turingEquivalent.2.trans ·), (A.oracle_compl_turingEquivalent.1.trans ·)⟩

/-- A partial function is Turing reducible to the complement of `A` exactly when it is Turing
reducible to `A`. -/
@[simp]
theorem turingReducible_oracle_compl_iff {A : Set ℕ} {f : ℕ →. ℕ} :
    TuringReducible f Aᶜ.oracle ↔ TuringReducible f A.oracle :=
  ⟨(·.trans A.oracle_compl_turingEquivalent.1), (·.trans A.oracle_compl_turingEquivalent.2)⟩

end Set

/-- If `A` and `B` are Turing reducible to an oracle `g`, so is `A ∩ B`. -/
theorem TuringReducible.inter_oracle {A B : Set ℕ} {g : ℕ →. ℕ} (hA : TuringReducible A.oracle g)
    (hB : TuringReducible B.oracle g) : TuringReducible (A ∩ B).oracle g := by
  rw [← compl_compl (A ∩ B), Set.compl_inter, Set.oracle_compl_turingReducible_iff]
  exact Set.union_turingReducible (Set.oracle_compl_turingReducible_iff.2 hA)
    (Set.oracle_compl_turingReducible_iff.2 hB)

namespace Function

/-- **Graph coding.** A total function on the naturals is Turing equivalent to the set coding its
graph by `Nat.pair`. So the degree of every total function is the degree of a set. -/
theorem turingEquivalent_oracle_preimage_unpair_graph (g : ℕ → ℕ) :
    (fun x => Part.some (g x)) ≡ᵀ (Nat.unpair ⁻¹' g.graph).oracle := by
  classical
  have hmem (n : ℕ) : n ∈ Nat.unpair ⁻¹' g.graph ↔ g n.unpair.1 = n.unpair.2 :=
    Set.mem_preimage.trans mem_graph
  constructor
  · -- `g x` is the least `y` whose pair with `x` lies in the graph
    have hzero : ComputableIn₂ {(Nat.unpair ⁻¹' g.graph).oracle}
        fun x y => 1 - (Nat.unpair ⁻¹' g.graph).indicator 1 (Nat.pair x y) :=
      ComputableIn.comp (f := fun p : ℕ × ℕ => p.1 - p.2) Primrec.nat_sub.computableIn₂ <|
        (ComputableIn.const 1).pair
          ((Set.computableIn_indicator _).comp Primrec₂.natPair.computableIn₂)
    refine RecursiveIn.iff_nat.2 <| (ComputableIn₂.iff_nat.1 hzero).rfind.of_eq_tot fun x =>
      Nat.mem_rfind.2 ⟨by simp [hmem], fun {y} hy => by simp [hmem, hy.ne']⟩
  · apply ((Nat.unpair ⁻¹' g.graph).turingReducible_iff_computableIn_indicator _).2
    have hg : ComputableIn {fun x => Part.some (g x)} g := RecursiveIn.oracle _ rfl
    have h := (Primrec.ite Primrec.eq (Primrec.const 1) (Primrec.const 0)).computableIn.comp
      ((hg.comp (Primrec.fst.comp Primrec.unpair).computableIn).pair
        (Primrec.snd.comp Primrec.unpair).computableIn)
    refine RecursiveIn.of_eq h fun n => ?_
    by_cases hn : g n.unpair.1 = n.unpair.2 <;> simp [hmem, hn]

end Function

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

/-- A one-one reduction of sets of naturals gives a Turing reduction of their oracles. -/
theorem OneOneReducible.turingReducible_oracle {A B : Set ℕ}
    (h : OneOneReducible (· ∈ A) (· ∈ B)) : TuringReducible A.oracle B.oracle :=
  h.to_many_one.turingReducible_oracle

/-- Many-one equivalent sets of naturals have Turing equivalent oracles. -/
theorem ManyOneEquiv.turingEquivalent_oracle {A B : Set ℕ} (h : ManyOneEquiv (· ∈ A) (· ∈ B)) :
    TuringEquivalent A.oracle B.oracle :=
  ⟨h.1.turingReducible_oracle, h.2.turingReducible_oracle⟩

/-- Many-one equivalent sets of naturals have the same Turing degree. -/
theorem ManyOneEquiv.toAntisymmetrization_oracle_eq {A B : Set ℕ}
    (h : ManyOneEquiv (· ∈ A) (· ∈ B)) :
    toAntisymmetrization TuringReducible A.oracle =
      toAntisymmetrization TuringReducible B.oracle :=
  (toAntisymmetrization_eq TuringReducible _ _).2 h.turingEquivalent_oracle

/-! ### Computable changes of presentation and columns -/

namespace Set

/-- The preimage of a set under a computable function is Turing reducible to the set. -/
theorem oracle_preimage_turingReducible (A : Set ℕ) {f : ℕ → ℕ} (hf : Computable f) :
    TuringReducible (f ⁻¹' A).oracle A.oracle :=
  (ManyOneReducible.mk (· ∈ A) hf).turingReducible_oracle

/-- The preimage of a set under a computable permutation of the naturals is Turing equivalent to
the set. -/
theorem oracle_preimage_turingEquivalent (A : Set ℕ) {e : ℕ ≃ ℕ} (he : e.Computable) :
    TuringEquivalent (e ⁻¹' A).oracle A.oracle :=
  (ManyOneEquiv.of_equiv (p := (· ∈ A)) he).turingEquivalent_oracle

/-- The preimage of a set under a computable permutation of the naturals has the degree of the
set. -/
theorem toAntisymmetrization_oracle_preimage_equiv (A : Set ℕ) {e : ℕ ≃ ℕ} (he : e.Computable) :
    toAntisymmetrization TuringReducible (e ⁻¹' A).oracle =
      toAntisymmetrization TuringReducible A.oracle :=
  (toAntisymmetrization_eq TuringReducible _ _).2 (A.oracle_preimage_turingEquivalent he)

/-- The image of a set under a computable function `f` with a computable left inverse `g` and
computable range is Turing equivalent to the set: `n ∈ f '' A` exactly when `n ∈ range f` and
`g n ∈ A`, and `x ∈ A` exactly when `f x ∈ f '' A`. -/
theorem oracle_image_turingEquivalent_of_leftInverse (A : Set ℕ) {f g : ℕ → ℕ}
    (hf : Computable f) (hg : Computable g) (hgf : Function.LeftInverse g f)
    (hrange : ComputablePred (· ∈ range f)) : TuringEquivalent (f '' A).oracle A.oracle :=
  ⟨hgf.image_eq A ▸ (hrange.oracle_turingReducible _).inter_oracle
      (A.oracle_preimage_turingReducible hg),
    by simpa only [hgf.injective.preimage_image] using (f '' A).oracle_preimage_turingReducible hf⟩

/-- The image of a set under a computable function with a computable left inverse and computable
range has the degree of the set. -/
theorem toAntisymmetrization_oracle_image_of_leftInverse (A : Set ℕ) {f g : ℕ → ℕ}
    (hf : Computable f) (hg : Computable g) (hgf : Function.LeftInverse g f)
    (hrange : ComputablePred (· ∈ range f)) :
    toAntisymmetrization TuringReducible (f '' A).oracle =
      toAntisymmetrization TuringReducible A.oracle :=
  (toAntisymmetrization_eq TuringReducible _ _).2
    (A.oracle_image_turingEquivalent_of_leftInverse hf hg hgf hrange)

/-- The image of a set under a computable permutation of the naturals is Turing equivalent to the
set. -/
theorem oracle_image_turingEquivalent (A : Set ℕ) {e : ℕ ≃ ℕ} (he : e.Computable) :
    TuringEquivalent (e '' A).oracle A.oracle :=
  A.oracle_image_turingEquivalent_of_leftInverse he.1 he.2 e.left_inv <|
    ComputablePred.computable_iff.2 ⟨fun _ => true, Computable.const true, by ext; simp⟩

/-- The image of a set under a computable permutation of the naturals has the degree of the
set. -/
theorem toAntisymmetrization_oracle_image_equiv (A : Set ℕ) {e : ℕ ≃ ℕ} (he : e.Computable) :
    toAntisymmetrization TuringReducible (e '' A).oracle =
      toAntisymmetrization TuringReducible A.oracle :=
  (toAntisymmetrization_eq TuringReducible _ _).2 (A.oracle_image_turingEquivalent he)

/-- **Computable invariance of columns.** The part of a set lying in the column
`e.pairColumn = {⟨x, e⟩ | x : ℕ}` is Turing equivalent to its `e`-th section
`{x | ⟨x, e⟩ ∈ A}`. -/
theorem oracle_inter_pairColumn_turingEquivalent (A : Set ℕ) (e : ℕ) :
    TuringEquivalent (A ∩ e.pairColumn).oracle ((Nat.pair · e) ⁻¹' A).oracle := by
  -- the part of `A` in the column is the image of the section under `(Nat.pair · e)`
  rw [Nat.pairColumn_eq_range_pair, ← image_preimage_eq_inter_range]
  exact oracle_image_turingEquivalent_of_leftInverse _
    (Primrec₂.natPair.comp Primrec.id (Primrec.const e)).to_comp
    (Primrec.fst.comp Primrec.unpair).to_comp (fun x => by simp)
    (Nat.pairColumn_eq_range_pair e ▸ e.computablePred_mem_pairColumn)

/-- The part of a set lying in the column `e.pairColumn` has the degree of its `e`-th section
`{x | ⟨x, e⟩ ∈ A}`. -/
theorem toAntisymmetrization_oracle_inter_pairColumn (A : Set ℕ) (e : ℕ) :
    toAntisymmetrization TuringReducible (A ∩ e.pairColumn).oracle =
      toAntisymmetrization TuringReducible ((Nat.pair · e) ⁻¹' A).oracle :=
  (toAntisymmetrization_eq TuringReducible _ _).2 (A.oracle_inter_pairColumn_turingEquivalent e)

end Set

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
  exact RecursiveIn.iff_nat.2 <| Nat.RecursiveIn.cond Computable.nat_bodd.computableIn
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

/-- Turing degrees form a join-semilattice: the supremum of the degrees of `f` and `g` is the degree
of their Turing join. -/
instance instSemilatticeSup : SemilatticeSup TuringDegree where
  sup := Quotient.map₂ PFun.turingJoin fun _ _ hf _ _ hg => TuringEquivalent.turingJoin hf hg
  le_sup_left a b := by
    induction a using Antisymmetrization.ind with | _ f
    induction b using Antisymmetrization.ind with | _ g
    exact TauCeti.turingDegree_le_iff.2 (.turingJoin_left f g)
  le_sup_right a b := by
    induction a using Antisymmetrization.ind with | _ f
    induction b using Antisymmetrization.ind with | _ g
    exact TauCeti.turingDegree_le_iff.2 (.turingJoin_right f g)
  sup_le a b c := by
    induction a using Antisymmetrization.ind with | _ f
    induction b using Antisymmetrization.ind with | _ g
    induction c using Antisymmetrization.ind with | _ h
    simp only [TauCeti.turingDegree_le_iff]
    exact PFun.turingJoin_turingReducible

/-- The supremum of the degrees of `f` and `g` is the degree of their Turing join. -/
@[simp]
theorem toAntisymmetrization_sup_toAntisymmetrization (f g : ℕ →. ℕ) :
    toAntisymmetrization TuringReducible f ⊔ toAntisymmetrization TuringReducible g =
      toAntisymmetrization TuringReducible (f.turingJoin g) :=
  (rfl)

/-- The least Turing degree is the degree of the computable sets, represented by the empty set. -/
noncomputable instance instOrderBot : OrderBot TuringDegree where
  bot := toAntisymmetrization TuringReducible (∅ : Set ℕ).oracle
  bot_le a := by
    induction a using Antisymmetrization.ind with | _ f
    exact TauCeti.turingDegree_le_iff.2 (Set.empty_turingReducible f)

end TuringDegree

namespace TauCeti

/-- The degree of the empty set is the least degree. -/
@[simp↓]
theorem toAntisymmetrization_oracle_empty :
    toAntisymmetrization TuringReducible (∅ : Set ℕ).oracle = ⊥ :=
  (rfl)

/-- **The least degree** consists of the partial computable functions. -/
@[simp]
theorem toAntisymmetrization_eq_bot_iff {f : ℕ →. ℕ} :
    toAntisymmetrization TuringReducible f = ⊥ ↔ Partrec f := by
  rw [← le_bot_iff, ← toAntisymmetrization_oracle_empty, turingDegree_le_iff]
  exact turingReducible_oracle_empty_iff

end TauCeti

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

/-- The degree of the complement of a set is the degree of the set. -/
@[simp]
theorem Set.toAntisymmetrization_oracle_compl (A : Set ℕ) :
    toAntisymmetrization TuringReducible Aᶜ.oracle =
      toAntisymmetrization TuringReducible A.oracle :=
  (toAntisymmetrization_eq TuringReducible _ _).2 A.oracle_compl_turingEquivalent
