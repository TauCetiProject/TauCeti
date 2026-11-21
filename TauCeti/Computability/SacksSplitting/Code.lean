/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Computability.SacksSplitting.Low
public import TauCeti.Computability.Split
public import Mathlib.Order.Comparable

/-!
# Uniform c.e. codes for Sacks splitting

Running Sacks's stage machine on the canonical simulation stages `W_{c₀,s}` and `W_{c₁,s}`
(`Nat.Partrec.Code.domStage`) gives finite approximations `halfStage c₀.domStage c₁.domStage b s`
whose binary finite-set codes are primitive recursive uniformly in `(c₀, c₁, s, b)`. Unbounded
search for entry into those stages compiles via `Nat.Partrec.Code.curry` to total primitive
recursive operators `splitCode b c₀ c₁` on ordinary program codes and `splitIndex b i j` on
numerical indices.

Unconditional properties are kept separate from those requiring a noncomputable target:

* for **all** codes `c₀` and `c₁`, the domain of `splitCode b c₀ c₁` is
  `splitHalf c₀.domStage c₁.domStage b`, the two domains are disjoint with union `W_{c₀}` and
  parity join Turing equivalent to `W_{c₀}`, and `Nat.Partrec.Code.splitProgram` applied to
  `(splitCode b c₀ c₁, splitCode (!b) c₀ c₁)` computes the `b`-half relative to `W_{c₀}`;
* when `W_{c₁}` is **noncomputable**, both output domains are low and neither computes `W_{c₁}`,
  and self-splitting `splitCode b c c` produces Turing incomparable halves;
* fixing a code `k₀` for `(∅ : Set ℕ).jump`, the primitive recursive pair
  `(fun c => splitCode false k₀ c, fun c => splitCode true k₀ c)` partitions `(∅ : Set ℕ).jump`
  for all `c`, with both domains low and at least one Turing incomparable with `W_c` whenever `W_c`
  is noncomputable and incomplete [S, VII.3.7 and p. 125], without asserting a computable selector
  between the two halves.

No computable operator extracting lowness-reduction indices uniformly from `c₁` is asserted.

## Main definitions

* `TauCeti.SacksSplitting.splitCode`: primitive recursive operator sending `(b, c₀, c₁)` to an
  ordinary program code whose domain is `splitHalf c₀.domStage c₁.domStage b`.
* `TauCeti.SacksSplitting.splitIndex`: numerical counterpart on `Denumerable.ofNat` code indices.

## Main results

* `TauCeti.SacksSplitting.primrec_stage_domStage`,
  `TauCeti.SacksSplitting.primrec_halfStage_domStage`,
  `TauCeti.SacksSplitting.primrec_halfStage_domStage_ofNat`: uniform primitive recursiveness of the
  canonical Sacks-splitting stage tables.
* `TauCeti.SacksSplitting.primrec_splitCode`, `TauCeti.SacksSplitting.primrec₂_splitCode`:
  `splitCode` is primitive recursive uniformly in the side and both input codes.
* `TauCeti.SacksSplitting.setOf_dom_eval_splitCode`,
  `TauCeti.SacksSplitting.disjoint_dom_eval_splitCode`,
  `TauCeti.SacksSplitting.dom_eval_splitCode_false_union_true`,
  `TauCeti.SacksSplitting.eval_splitProgram_splitCode`,
  `TauCeti.SacksSplitting.turingEquivalent_dom_eval_join_splitCode`: unconditional domain,
  disjointness, union, uniform split-reduction, and join-equivalence identities for all `c₀, c₁`.
* `TauCeti.SacksSplitting.low_dom_eval_splitCode`,
  `TauCeti.SacksSplitting.not_turingReducible_dom_eval_splitCode`,
  `TauCeti.SacksSplitting.incompRel_dom_eval_splitCode_self`,
  `TauCeti.SacksSplitting.exists_primrec_code_pair_incompRel_of_incomplete`: lowness, cone
  avoidance, self-splitting incomparability, and the uniform primitive recursive pair for
  incomplete targets.

## References

* R. I. Soare, *Recursively Enumerable Sets and Degrees*, Springer, 1987, Theorem VII.3.2,
  Remark VII.3.3, and Corollaries VII.3.4 and VII.3.7, pp. 124–126.
-/

public section

open Encodable Denumerable TauCeti.Enumeration

namespace TauCeti.SacksSplitting

/-! ### Uniform stage tables on canonical enumerations -/

section StageTable

open Primrec

/-- The binary codes of the stage pairs on canonical approximations `W_{c₀,s}` and `W_{c₁,s}` are
primitive recursive uniformly in `(c₀, c₁)` and `s`. -/
theorem primrec_stage_domStage :
    Primrec fun p : (Nat.Partrec.Code × Nat.Partrec.Code) × ℕ =>
      (Finset.equivBitIndices.symm (stage p.1.1.domStage p.1.2.domStage p.2).1,
        Finset.equivBitIndices.symm (stage p.1.1.domStage p.1.2.domStage p.2).2) :=
  primrec₂_stage
    (Nat.Partrec.Code.primrec_domStage.comp ((fst.comp fst).pair snd)).to₂
    (Nat.Partrec.Code.primrec_domStage.comp ((snd.comp fst).pair snd)).to₂

/-- The binary finite-set code of `halfStage c₀.domStage c₁.domStage b s` is primitive recursive
uniformly in `((c₀, c₁), s, b)`. -/
theorem primrec_halfStage_domStage :
    Primrec fun p : (Nat.Partrec.Code × Nat.Partrec.Code) × ℕ × Bool =>
      Finset.equivBitIndices.symm (halfStage p.1.1.domStage p.1.2.domStage p.2.2 p.2.1) :=
  (primrec₂_halfStage
    (B := fun q : Nat.Partrec.Code × Nat.Partrec.Code => q.1.domStage)
    (C := fun q : Nat.Partrec.Code × Nat.Partrec.Code => q.2.domStage)
    (Nat.Partrec.Code.primrec_domStage.comp ((fst.comp fst).pair snd)).to₂
    (Nat.Partrec.Code.primrec_domStage.comp ((snd.comp fst).pair snd)).to₂).comp
    (fst.pair (snd.comp snd)) (fst.comp snd)

/-- On numerical code indices, the binary finite-set code of Sacks's stage table is primitive
recursive uniformly in `((i, j), s, b)`. -/
theorem primrec_halfStage_domStage_ofNat :
    Primrec fun p : (ℕ × ℕ) × ℕ × Bool =>
      Finset.equivBitIndices.symm
        (halfStage (ofNat Nat.Partrec.Code p.1.1).domStage
          (ofNat Nat.Partrec.Code p.1.2).domStage p.2.2 p.2.1) :=
  primrec_halfStage_domStage.comp
    ((((Primrec.ofNat Nat.Partrec.Code).comp (fst.comp fst)).pair
      ((Primrec.ofNat Nat.Partrec.Code).comp (snd.comp fst))).pair snd)

/-- Membership in `halfStage c₀.domStage c₁.domStage b s` is primitive recursive uniformly in
`((c₀, c₁), s, b)` and the candidate element `x`. -/
theorem primrecRel_mem_halfStage_domStage :
    PrimrecRel fun (p : (Nat.Partrec.Code × Nat.Partrec.Code) × ℕ × Bool) (x : ℕ) =>
      x ∈ halfStage p.1.1.domStage p.1.2.domStage p.2.2 p.2.1 :=
  (mem_equivBitIndices.comp (primrec_halfStage_domStage.comp fst) snd).primrecRel.of_eq
    fun _ _ => by simp

end StageTable

/-! ### Uniform output-code transformations -/

/-- Least-stage search for entry of `q.2` into `halfStage q.1.2.1.domStage q.1.2.2.domStage q.1.1`.
-/
private noncomputable def splitCodeSearch
    (q : (Bool × Nat.Partrec.Code × Nat.Partrec.Code) × ℕ) : Part ℕ :=
  Nat.rfind fun s =>
    Part.some (decide (q.2 ∈ halfStage q.1.2.1.domStage q.1.2.2.domStage q.1.1 s))

private theorem partrec_splitCodeSearch : Partrec splitCodeSearch := by
  have hmem : Primrec₂ fun (q : (Bool × Nat.Partrec.Code × Nat.Partrec.Code) × ℕ) (s : ℕ) =>
      decide (q.2 ∈ halfStage q.1.2.1.domStage q.1.2.2.domStage q.1.1 s) :=
    primrecRel_mem_halfStage_domStage.decide.comp
      ((Primrec.snd.comp (Primrec.fst.comp Primrec.fst)).pair
        (Primrec.snd.pair (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))))
      (Primrec.snd.comp Primrec.fst)
  exact Partrec.rfind hmem.to_comp.partrec₂

/-- A fixed ordinary code implementing `splitCodeSearch` on encoded tuples. -/
private noncomputable def splitCodeSearchCode : Nat.Partrec.Code :=
  (Nat.Partrec.Code.exists_code.1 partrec_splitCodeSearch).choose

private theorem eval_splitCodeSearchCode (n : ℕ) :
    splitCodeSearchCode.eval n =
      Part.bind (decode (α := (Bool × Nat.Partrec.Code × Nat.Partrec.Code) × ℕ) n)
        fun q => (splitCodeSearch q).map encode :=
  congrFun (Nat.Partrec.Code.exists_code.1 partrec_splitCodeSearch).choose_spec n

/-- **Uniform output code of Sacks splitting.** Given a side `b` and ordinary program codes `c₀`
and `c₁`, `splitCode b c₀ c₁` searches for the least stage `s` at which its input enters
`halfStage c₀.domStage c₁.domStage b s`. Its domain is `splitHalf c₀.domStage c₁.domStage b` for
every pair `(c₀, c₁)`. -/
noncomputable def splitCode (b : Bool) (c₀ c₁ : Nat.Partrec.Code) : Nat.Partrec.Code :=
  Nat.Partrec.Code.curry splitCodeSearchCode (encode (b, c₀, c₁))

/-- `splitCode` is primitive recursive uniformly in `(b, c₀, c₁)`. -/
theorem primrec_splitCode :
    Primrec fun p : Bool × Nat.Partrec.Code × Nat.Partrec.Code => splitCode p.1 p.2.1 p.2.2 :=
  Nat.Partrec.Code.primrec₂_curry.comp (Primrec.const splitCodeSearchCode) Primrec.encode

/-- For each side `b`, `splitCode b` is a primitive recursive binary code operator. -/
theorem primrec₂_splitCode (b : Bool) : Primrec₂ (splitCode b) :=
  (primrec_splitCode.comp ((Primrec.const b).pair Primrec.id)).to₂

/-- `splitCode b c₀ c₁` halts on `x` if and only if `x` belongs to the `b`-half of the canonical
Sacks splitting of `c₀` against `c₁`. No hypothesis on `c₀` or `c₁` is needed. -/
theorem dom_eval_splitCode {b : Bool} {c₀ c₁ : Nat.Partrec.Code} {x : ℕ} :
    ((splitCode b c₀ c₁).eval x).Dom ↔ x ∈ splitHalf c₀.domStage c₁.domStage b := by
  have henc : Nat.pair (encode (b, c₀, c₁)) x = encode ((b, c₀, c₁), x) := by simp
  rw [splitCode, Nat.Partrec.Code.eval_curry, henc, eval_splitCodeSearchCode, encodek]
  simpa [splitCodeSearch] using
    Nat.rfind_dom (p := fun s => Part.some (decide (x ∈ halfStage c₀.domStage c₁.domStage b s)))

/-- The domain `W_{splitCode b c₀ c₁}` is `splitHalf c₀.domStage c₁.domStage b` for all `c₀, c₁`. -/
@[simp]
theorem setOf_dom_eval_splitCode (b : Bool) (c₀ c₁ : Nat.Partrec.Code) :
    {x | ((splitCode b c₀ c₁).eval x).Dom} = splitHalf c₀.domStage c₁.domStage b :=
  Set.ext fun _ => dom_eval_splitCode

/-! ### Unconditional partition and split-reduction properties -/

/-- For **all** codes `c₀` and `c₁`, the domains of `splitCode false c₀ c₁` and
`splitCode true c₀ c₁` are disjoint. -/
theorem disjoint_dom_eval_splitCode (c₀ c₁ : Nat.Partrec.Code) :
    Disjoint {x | ((splitCode false c₀ c₁).eval x).Dom}
      {x | ((splitCode true c₀ c₁).eval x).Dom} := by
  rw [setOf_dom_eval_splitCode, setOf_dom_eval_splitCode]
  exact disjoint_splitHalf c₀.domStage c₁.domStage

/-- For **all** codes `c₀` and `c₁`, the domains of `splitCode false c₀ c₁` and
`splitCode true c₀ c₁` have union `W_{c₀}`. -/
theorem dom_eval_splitCode_false_union_true (c₀ c₁ : Nat.Partrec.Code) :
    {x | ((splitCode false c₀ c₁).eval x).Dom} ∪ {x | ((splitCode true c₀ c₁).eval x).Dom} =
      {x | (c₀.eval x).Dom} := by
  rw [setOf_dom_eval_splitCode, setOf_dom_eval_splitCode, splitHalf_false_union_splitHalf_true,
    Nat.Partrec.Code.stageLimit_domStage]

/-- **Uniform split reduction.** For **all** codes `c₀` and `c₁` and either side `b`, the oracle
program `Nat.Partrec.Code.splitProgram (splitCode b c₀ c₁) (splitCode (!b) c₀ c₁)` computes
`splitHalf c₀.domStage c₁.domStage b` relative to `W_{c₀}`. -/
theorem eval_splitProgram_splitCode (b : Bool) (c₀ c₁ : Nat.Partrec.Code) :
    Oracle.Single.Code.eval {x | (c₀.eval x).Dom}.oracle
      (Nat.Partrec.Code.splitProgram (splitCode b c₀ c₁) (splitCode (!b) c₀ c₁)) =
        (splitHalf c₀.domStage c₁.domStage b).oracle := by
  cases b
  · have h := Nat.Partrec.Code.eval_splitProgram (disjoint_dom_eval_splitCode c₀ c₁)
    rwa [dom_eval_splitCode_false_union_true, setOf_dom_eval_splitCode] at h
  · have h := Nat.Partrec.Code.eval_splitProgram (disjoint_dom_eval_splitCode c₀ c₁).symm
    rwa [Set.union_comm, dom_eval_splitCode_false_union_true, setOf_dom_eval_splitCode] at h

/-- For **all** codes `c₀` and `c₁`, `W_{c₀}` is Turing equivalent to the parity join of the two
output domains `W_{splitCode false c₀ c₁}` and `W_{splitCode true c₀ c₁}` [S, VII.3.3]. -/
theorem turingEquivalent_dom_eval_join_splitCode (c₀ c₁ : Nat.Partrec.Code) :
    TuringEquivalent {x | (c₀.eval x).Dom}.oracle
      ({x | ((splitCode false c₀ c₁).eval x).Dom}.join
        {x | ((splitCode true c₀ c₁).eval x).Dom}).oracle := by
  rw [← dom_eval_splitCode_false_union_true c₀ c₁]
  exact (disjoint_dom_eval_splitCode c₀ c₁).turingEquivalent_union_join
    (splitCode false c₀ c₁).rePred_dom_eval (splitCode true c₀ c₁).rePred_dom_eval

/-- When `W_{c₀}` is not low, the parity join of `W_{splitCode false c₀ c₁}` and
`W_{splitCode true c₀ c₁}` is not low, for any target code `c₁`. -/
theorem not_low_join_dom_eval_splitCode {c₀ : Nat.Partrec.Code} (c₁ : Nat.Partrec.Code)
    (hnl : ¬{x | (c₀.eval x).Dom}.Low) :
    ¬({x | ((splitCode false c₀ c₁).eval x).Dom}.join
      {x | ((splitCode true c₀ c₁).eval x).Dom}).Low := fun h =>
  hnl ((Set.low_congr (turingEquivalent_dom_eval_join_splitCode c₀ c₁)).2 h)

/-! ### Promised lowness and cone avoidance for noncomputable targets -/

private theorem not_computablePred_mem_stageLimit_domStage {c : Nat.Partrec.Code}
    (hnc : ¬ComputablePred fun x => (c.eval x).Dom) :
    ¬ComputablePred (· ∈ stageLimit c.domStage) := by
  rwa [Nat.Partrec.Code.stageLimit_domStage]

section NoncomputableTarget

variable {c₁ : Nat.Partrec.Code} (hnc : ¬ComputablePred fun x => (c₁.eval x).Dom)
include hnc

/-- When `W_{c₁}` is noncomputable, both output domains `W_{splitCode b c₀ c₁}` are low. -/
theorem low_dom_eval_splitCode (b : Bool) (c₀ : Nat.Partrec.Code) :
    {x | ((splitCode b c₀ c₁).eval x).Dom}.Low := by
  rw [setOf_dom_eval_splitCode]
  exact low_splitHalf c₀.computable_domStage c₁.monotone_domStage c₁.computable_domStage
    (not_computablePred_mem_stageLimit_domStage hnc) b

/-- When `W_{c₁}` is noncomputable, neither output domain `W_{splitCode b c₀ c₁}` computes
`W_{c₁}`. -/
theorem not_turingReducible_dom_eval_splitCode (b : Bool) (c₀ : Nat.Partrec.Code) :
    ¬TuringReducible {x | (c₁.eval x).Dom}.oracle
      {x | ((splitCode b c₀ c₁).eval x).Dom}.oracle := by
  rw [setOf_dom_eval_splitCode, ← Nat.Partrec.Code.stageLimit_domStage]
  exact not_turingReducible_splitHalf c₀.computable_domStage c₁.monotone_domStage
    c₁.computable_domStage (not_computablePred_mem_stageLimit_domStage hnc) b

end NoncomputableTarget

/-- When `W_c` is noncomputable, the domains of `splitCode false c c` and `splitCode true c c` are
Turing incomparable [S, VII.3.4]. -/
theorem incompRel_dom_eval_splitCode_self {c : Nat.Partrec.Code}
    (hnc : ¬ComputablePred fun x => (c.eval x).Dom) :
    IncompRel TuringReducible {x | ((splitCode false c c).eval x).Dom}.oracle
      {x | ((splitCode true c c).eval x).Dom}.oracle := by
  have hu := dom_eval_splitCode_false_union_true c c
  exact ⟨fun h => not_turingReducible_dom_eval_splitCode hnc true c
      (hu ▸ Set.union_turingReducible h (.refl _)),
    fun h => not_turingReducible_dom_eval_splitCode hnc false c
      (hu ▸ Set.union_turingReducible (.refl _) h)⟩

/-- Given a code `k₀` for `(∅ : Set ℕ).jump` and a code `c` whose domain `W_c` is noncomputable
and incomplete, at least one side `b` of `splitCode b k₀ c` has a low domain Turing incomparable
with `W_c` [S, VII.3.7]. -/
theorem exists_side_incompRel_splitCode_of_incomplete {k₀ c : Nat.Partrec.Code}
    (hk₀ : {x | (k₀.eval x).Dom} = (∅ : Set ℕ).jump)
    (hnc : ¬ComputablePred fun x => (c.eval x).Dom)
    (hinc : ¬TuringReducible (∅ : Set ℕ).jump.oracle {x | (c.eval x).Dom}.oracle) :
    ∃ b : Bool, {x | ((splitCode b k₀ c).eval x).Dom}.Low ∧
      IncompRel TuringReducible {x | ((splitCode b k₀ c).eval x).Dom}.oracle
        {x | (c.eval x).Dom}.oracle := by
  by_contra! hall
  have hred (b : Bool) :
      TuringReducible {x | ((splitCode b k₀ c).eval x).Dom}.oracle {x | (c.eval x).Dom}.oracle := by
    by_contra hnr
    exact hall b (low_dom_eval_splitCode hnc b k₀)
      ⟨hnr, not_turingReducible_dom_eval_splitCode hnc b k₀⟩
  have heq := turingEquivalent_dom_eval_join_splitCode k₀ c
  rw [hk₀] at heq
  exact hinc (heq.1.trans (Set.join_turingReducible (hred false) (hred true)))

/-- **Uniform code-pair form of [S, VII.3.7 and p. 125].** There is a pair of primitive recursive
code transformations `(f₀, f₁)` whose domains partition `(∅ : Set ℕ).jump` for **every** code `c`,
such that whenever `W_c` is noncomputable and incomplete, both domains are low and **at least one**
of them is Turing incomparable with `W_c`. Following Soare's remark on p. 125, the pair
`(f₀ c, f₁ c)` is uniform in `c`, whereas no computable selector choosing a single successful half
is claimed. -/
theorem exists_primrec_code_pair_incompRel_of_incomplete :
    ∃ f₀ f₁ : Nat.Partrec.Code → Nat.Partrec.Code, Primrec f₀ ∧ Primrec f₁ ∧
      (∀ c, Disjoint {x | ((f₀ c).eval x).Dom} {x | ((f₁ c).eval x).Dom} ∧
        {x | ((f₀ c).eval x).Dom} ∪ {x | ((f₁ c).eval x).Dom} = (∅ : Set ℕ).jump) ∧
      ∀ c, (¬ComputablePred fun x => (c.eval x).Dom) →
        ¬TuringReducible (∅ : Set ℕ).jump.oracle {x | (c.eval x).Dom}.oracle →
        {x | ((f₀ c).eval x).Dom}.Low ∧ {x | ((f₁ c).eval x).Dom}.Low ∧
          (IncompRel TuringReducible {x | ((f₀ c).eval x).Dom}.oracle {x | (c.eval x).Dom}.oracle ∨
            IncompRel TuringReducible {x | ((f₁ c).eval x).Dom}.oracle
              {x | (c.eval x).Dom}.oracle) := by
  obtain ⟨k₀, hk₀⟩ := rePred_iff_exists_code.1 Set.rePred_mem_jump_empty
  have hk₀' : {x | (k₀.eval x).Dom} = (∅ : Set ℕ).jump := Set.ext fun x => (hk₀ x).symm
  refine ⟨fun c => splitCode false k₀ c, fun c => splitCode true k₀ c,
    (primrec₂_splitCode false).comp (Primrec.const k₀) Primrec.id,
    (primrec₂_splitCode true).comp (Primrec.const k₀) Primrec.id,
    fun c => ⟨disjoint_dom_eval_splitCode k₀ c,
      (dom_eval_splitCode_false_union_true k₀ c).trans hk₀'⟩,
    fun c hnc hinc => ⟨low_dom_eval_splitCode hnc false k₀, low_dom_eval_splitCode hnc true k₀, ?_⟩⟩
  obtain ⟨b, -, hincb⟩ := exists_side_incompRel_splitCode_of_incomplete hk₀' hnc hinc
  cases b
  · exact Or.inl hincb
  · exact Or.inr hincb

/-! ### Numerical index operator -/

/-- **Uniform numerical index of Sacks splitting:** the encoded program index of `splitCode` applied
to the codes numbered `i` and `j`. -/
noncomputable def splitIndex (b : Bool) (i j : ℕ) : ℕ :=
  encode (splitCode b (ofNat Nat.Partrec.Code i) (ofNat Nat.Partrec.Code j))

/-- Definitional expansion of `splitIndex`. -/
theorem splitIndex_def (b : Bool) (i j : ℕ) :
    splitIndex b i j = encode (splitCode b (ofNat Nat.Partrec.Code i) (ofNat Nat.Partrec.Code j)) :=
  (rfl)

/-- `splitIndex` is primitive recursive uniformly in `(b, i, j)`. -/
theorem primrec_splitIndex : Primrec fun p : Bool × ℕ × ℕ => splitIndex p.1 p.2.1 p.2.2 :=
  Primrec.encode.comp <| primrec_splitCode.comp <|
    Primrec.fst.pair
      (((Primrec.ofNat Nat.Partrec.Code).comp (Primrec.fst.comp Primrec.snd)).pair
        ((Primrec.ofNat Nat.Partrec.Code).comp (Primrec.snd.comp Primrec.snd)))

/-- For each side `b`, `splitIndex b` is a primitive recursive binary index transformation. -/
theorem primrec₂_splitIndex (b : Bool) : Primrec₂ (splitIndex b) :=
  (primrec_splitIndex.comp ((Primrec.const b).pair Primrec.id)).to₂

/-- Decoding `splitIndex b i j` recovers `splitCode` on the decoded input programs. -/
@[simp]
theorem ofNat_splitIndex (b : Bool) (i j : ℕ) :
    ofNat Nat.Partrec.Code (splitIndex b i j) =
      splitCode b (ofNat Nat.Partrec.Code i) (ofNat Nat.Partrec.Code j) :=
  ofNat_encode _

end TauCeti.SacksSplitting
