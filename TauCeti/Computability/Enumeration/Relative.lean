/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Computability.Enumeration.Serialization
public import TauCeti.Computability.Hierarchy.One
public import TauCeti.Computability.SingleOracle.Stage
import TauCeti.Computability.Primrec.FiniteSet

/-!
# Relative finite-stage enumerations and uniform stage comparisons

For an oracle program `c : TauCeti.Oracle.Single.Code` and oracle answers `σ : ℕ → Option ℕ`,
`c.domStage σ s` is the normalized finite stage `W_{c,s}^σ`: the inputs on which `c` halts at
stage `s` under `TauCeti.Oracle.Single.Code.evalStage`. By Soare's stage bounds, every member is
below `s` and `c.domStage σ s = ∅` whenever `s ≤ encode c`.

When `σ` fixes the answers of a set oracle `Z` (or a total oracle `O`), these stages start empty,
increase with `s`, and have limit `(Code.eval Z.oracle c).Dom`. Their binary finite-set codes are
primitive recursive uniformly in any primitive-recursive family of finite oracle answers (such as
finite oracle strings or binary-coded finite sets), and `Z`-computable uniformly in the program
and the stage. Relative serialization produces uniformly `Z`-computable single-entry stages,
characterizing `IsSigma Z 1` predicates on `ℕ` as limits of `Z`-computable monotone finite stages
(with or without serialization).

To compare two finite-stage enumerations `A` and `B`, `TauCeti.Enumeration.stageCompare A B s`
searches for the least stage `t` with `A s ⊆ B t`. Its actual domain is `{s | ∃ t, A s ⊆ B t}`,
it is uniformly recursive in the oracle and stage parameters without any totality or monotonicity
premise, and under monotonicity of `B` totality characterizes `stageLimit A ⊆ stageLimit B`.

## Main definitions

* `TauCeti.Oracle.Single.Code.domStage`: the normalized finite stage `W_{c,s}^σ` of the domain of
  an oracle program `c` against oracle answers `σ`.
* `TauCeti.Enumeration.stageCompare`: partial least-stage comparison map searching for the first
  stage `t` with `A s ⊆ B t`.

## Main results

* `TauCeti.Oracle.Single.Code.monotone_domStage`,
  `TauCeti.Oracle.Single.Code.stageLimit_domStage`: the stages start empty, increase, and limit
  to the domain of the oracle program.
* `TauCeti.Oracle.Single.Code.primrec_domStage`,
  `TauCeti.Oracle.Single.Code.computableIn_domStage_setAnswers`: uniform effectivity of the
  binary finite-set codes of relative stages.
* `TauCeti.Enumeration.computableIn_serializedStage`: relative serialization preserves uniform
  oracle-computability of binary finite-set codes.
* `TauCeti.Enumeration.isSigma_one_iff_exists_stages`,
  `TauCeti.Enumeration.isSigma_one_iff_exists_serialized_stages`: relative stage characterizations
  of Σ⁰₁ predicates on `ℕ`.
* `TauCeti.Enumeration.stageLimit_subset_iff_forall_stageCompare_dom`,
  `TauCeti.Enumeration.recursiveIn_stageCompare`,
  `TauCeti.Enumeration.computableIn_stageCompare_get`: uniform stage comparison and its totality
  corollary witnessing inclusion and equality of limiting sets.

## References

* R. I. Soare, *Recursively Enumerable Sets and Degrees*, Springer, 1987, Chapters II.1–2 and III.1.
-/

public section

open Encodable TauCeti.ArithmeticalHierarchy TauCeti.Enumeration

namespace TauCeti.Oracle.Single.Code

/-- The normalized finite stage `W_{c,s}^σ` of the domain of an oracle program `c` against oracle
answers `σ`: the inputs on which `evalStage σ s c` succeeds. -/
def domStage (c : Code) (σ : ℕ → Option ℕ) (s : ℕ) : Finset ℕ :=
  (Finset.range s).filter fun x => (evalStage σ s c x).isSome

variable {σ τ : ℕ → Option ℕ} {c : Code} {s x : ℕ}

/-- A number belongs to `c.domStage σ s` exactly when `evalStage σ s c` succeeds on it. -/
@[simp]
theorem mem_domStage : x ∈ c.domStage σ s ↔ (evalStage σ s c x).isSome := by
  rw [domStage, Finset.mem_filter, Finset.mem_range, and_iff_right_iff_imp]
  intro h
  obtain ⟨d, hd⟩ := Option.isSome_iff_exists.mp h
  exact evalStage_input_lt hd

/-- Every input enumerated by stage `s` is strictly below `s`. -/
theorem domStage_subset_range (c : Code) (σ : ℕ → Option ℕ) (s : ℕ) :
    c.domStage σ s ⊆ Finset.range s :=
  Finset.filter_subset _ _

/-- Stage zero has no successful computations, so the stages start empty. -/
@[simp]
theorem domStage_zero (c : Code) (σ : ℕ → Option ℕ) : c.domStage σ 0 = ∅ := by
  simp [domStage]

/-- Programs whose index is at least `s` enumerate nothing by stage `s`. -/
theorem domStage_eq_empty_of_le_encode (hs : s ≤ encode c) : c.domStage σ s = ∅ := by
  ext x
  simp [evalStage_eq_none_of_le_encode hs]

/-- For fixed oracle answers, the normalized domain stages increase with the stage. -/
theorem monotone_domStage (c : Code) (σ : ℕ → Option ℕ) : Monotone (c.domStage σ) := by
  intro s t hst x
  simp only [mem_domStage, Option.isSome_iff_exists]
  exact fun ⟨d, hd⟩ => ⟨d, evalStage_mono hst hd⟩

/-- Agreement of oracle answers below `s` preserves the finite stage `W_{c,s}^σ`. -/
theorem domStage_eq_of_eqOn (hστ : Set.EqOn σ τ (Set.Iio s)) :
    c.domStage σ s = c.domStage τ s := by
  ext x
  simp [evalStage_eq_of_eqOn hστ]

/-- Against a total oracle `O`, stage `s` of the domain depends only on the first `s` answers of
`O`. -/
theorem domStage_range_map (O : ℕ → ℕ) (c : Code) (s : ℕ) :
    c.domStage (fun z => ((List.range s).map O)[z]?) s =
      c.domStage (fun z => some (O z)) s := by
  ext x
  simp only [mem_domStage, evalStage_range_map]

/-- When `σ` supplies exactly the values of the oracle `O`, the limit of `c.domStage σ` is the
domain of `eval O c`. -/
theorem stageLimit_domStage {O : ℕ →. ℕ} (hσ : ∀ z y, σ z = some y ↔ y ∈ O z) (c : Code) :
    stageLimit (c.domStage σ) = (eval O c).Dom := by
  ext x
  simp only [mem_stageLimit, mem_domStage, Option.isSome_iff_exists, PFun.mem_dom,
    mem_eval_iff_exists_evalStage hσ]
  exact ⟨fun ⟨s, d, hd⟩ => ⟨d.output, s, d, hd, rfl⟩, fun ⟨_, s, d, hd, _⟩ => ⟨s, d, hd⟩⟩

/-- A number belongs to the domain of `eval O c` exactly when it enters `c.domStage σ` at some
stage, provided `σ` supplies exactly the values of `O`. -/
theorem exists_mem_domStage_iff {O : ℕ →. ℕ} (hσ : ∀ z y, σ z = some y ↔ y ∈ O z) :
    (∃ s, x ∈ c.domStage σ s) ↔ x ∈ (eval O c).Dom := by
  rw [← mem_stageLimit, stageLimit_domStage hσ]

/-- The limit of the domain stages against a total oracle `O` is the domain of `eval O c`. -/
@[simp]
theorem stageLimit_domStage_total (O : ℕ → ℕ) (c : Code) :
    stageLimit (c.domStage (fun z => some (O z))) = (eval (O : ℕ →. ℕ) c).Dom :=
  stageLimit_domStage (by simp [eq_comm]) c

/-- The limit of the domain stages against a set oracle `Z` is the domain of `eval Z.oracle c`. -/
@[simp]
theorem stageLimit_domStage_setAnswers (Z : Set ℕ) (c : Code) :
    stageLimit (c.domStage (setAnswers Z)) = (eval Z.oracle c).Dom :=
  stageLimit_domStage (by simp [eq_comm]) c

/-- For a query-free program, the relative domain stages have the same limit as Mathlib's ordinary
code domain stages, for every oracle answer table `σ`. -/
theorem stageLimit_domStage_toSingleOracleCode (σ : ℕ → Option ℕ) (c : Nat.Partrec.Code) :
    stageLimit (c.toSingleOracleCode.domStage σ) = stageLimit c.domStage := by
  let O : ℕ →. ℕ := fun z => Part.ofOption (σ z)
  rw [stageLimit_domStage (O := O) (by simp [O, Part.mem_ofOption]),
    eval_toSingleOracleCode, Nat.Partrec.Code.stageLimit_domStage]
  rfl

section Effectivity

open Primrec

variable {α : Type*} [Primcodable α]

/-- Membership in normalized domain stages is primitive recursive, uniformly in any
primitive-recursive family of oracle answers, the program, the stage, and the number. -/
theorem primrecRel_mem_domStage {σ : α → ℕ → Option ℕ} (hσ : Primrec₂ σ) :
    PrimrecRel fun (p : α × Code × ℕ) x => x ∈ p.2.1.domStage (σ p.1) p.2.2 := by
  have heval : Primrec₂ fun (p : α × Code × ℕ) x => (evalStage (σ p.1) p.2.2 p.2.1 x).isSome :=
    option_isSome.comp <| (primrec_evalStage hσ).comp <|
      (fst.comp fst).pair <| (snd.comp (snd.comp fst)).pair <|
        (fst.comp (snd.comp fst)).pair snd
  exact (Primrec.eq.comp heval (const true)).of_eq fun p => by simp

/-- Binary finite-set codes of normalized domain stages are primitive recursive, uniformly in any
primitive-recursive family of oracle answers, the program, and the stage. -/
theorem primrec_domStage {σ : α → ℕ → Option ℕ} (hσ : Primrec₂ σ) :
    Primrec fun p : α × Code × ℕ => Finset.equivBitIndices.symm (p.2.1.domStage (σ p.1) p.2.2) := by
  have hstage : Primrec fun p : α × Code × ℕ => p.2.2 := snd.comp snd
  have hpred : Primrec₂ fun (p : α × Code × ℕ) x => (evalStage (σ p.1) p.2.2 p.2.1 x).isSome :=
    option_isSome.comp <| (primrec_evalStage hσ).comp <|
      (fst.comp fst).pair <| (snd.comp (snd.comp fst)).pair <|
        (fst.comp (snd.comp fst)).pair snd
  refine (Primrec.nat_filterBitIndices
    (nat_sub.comp (nat_pow.comp (const 2) hstage) (const 1)) hstage hpred).of_eq fun p => ?_
  apply Finset.equivBitIndices.injective
  ext x
  simp [Nat.testBit_two_pow_sub_one, domStage]

/-- Binary finite-set codes of domain stages against finite oracle strings are primitive recursive
in the string, the program, and the stage. -/
theorem primrec_domStage_list :
    Primrec fun p : List ℕ × Code × ℕ =>
      Finset.equivBitIndices.symm (p.2.1.domStage (fun z => p.1[z]?) p.2.2) :=
  primrec_domStage list_getElem?

/-- Binary finite-set codes of domain stages against binary-coded finite sets are primitive
recursive in the finite-set code, the program, and the stage. -/
theorem primrec_domStage_equivBitIndices :
    Primrec fun p : ℕ × Code × ℕ =>
      Finset.equivBitIndices.symm
        (p.2.1.domStage (setAnswers (Finset.equivBitIndices p.1)) p.2.2) :=
  primrec_domStage primrec₂_setAnswers_equivBitIndices

/-- Binary finite-set codes of domain stages against a uniformly oracle-computable family of total
oracles are oracle-computable, uniformly in the family parameter, the program, and the stage. -/
theorem computableIn_domStage {G : Set (ℕ →. ℕ)} {σ : α → ℕ → ℕ} (hσ : ComputableIn₂ G σ) :
    ComputableIn G fun p : α × Code × ℕ =>
      Finset.equivBitIndices.symm (p.2.1.domStage (fun z => some (σ p.1 z)) p.2.2) := by
  have hpref : ComputableIn G fun p : α × Code × ℕ => (List.range p.2.2).map (σ p.1) :=
    hσ.list_range_map.comp (ComputableIn.fst.pair (ComputableIn.snd.comp ComputableIn.snd))
  exact RecursiveIn.of_eq (primrec_domStage_list.computableIn.comp (hpref.pair ComputableIn.snd))
    fun p => congrArg (fun D => Part.some (Finset.equivBitIndices.symm D))
      (domStage_range_map (σ p.1) p.2.1 p.2.2)

/-- For a total oracle `O`, binary finite-set codes of `O`-relative domain stages are computable in
`O`, uniformly in the program and the stage. -/
theorem computableIn_domStage_total (O : ℕ → ℕ) :
    ComputableIn {(O : ℕ →. ℕ)} fun p : Code × ℕ =>
      Finset.equivBitIndices.symm (p.1.domStage (fun z => some (O z)) p.2) := by
  have hO : ComputableIn {(O : ℕ →. ℕ)} O :=
    RecursiveIn.of_eq (RecursiveIn.oracle (O : ℕ →. ℕ) rfl) fun _ => rfl
  have hO₂ : ComputableIn₂ {(O : ℕ →. ℕ)} (fun (_ : Unit) z => O z) :=
    hO.comp ComputableIn.snd
  exact RecursiveIn.of_eq
    ((computableIn_domStage hO₂).comp ((ComputableIn.const ()).pair ComputableIn.id))
    fun _ => rfl

/-- For a set oracle `Z`, binary finite-set codes of `Z`-relative domain stages are computable in
`Z`, uniformly in the program and the stage. -/
theorem computableIn_domStage_setAnswers (Z : Set ℕ) :
    ComputableIn {Z.oracle} fun p : Code × ℕ =>
      Finset.equivBitIndices.symm (p.1.domStage (setAnswers Z) p.2) := by
  have hZ : ComputableIn₂ {Z.oracle} (fun (_ : Unit) z => Z.indicator 1 z) :=
    Z.computableIn_indicator.comp ComputableIn.snd
  have hfun : (fun z => some (Z.indicator 1 z)) = setAnswers Z :=
    funext fun z => (setAnswers_apply Z z).symm
  exact RecursiveIn.of_eq
    ((computableIn_domStage hZ).comp ((ComputableIn.const ()).pair ComputableIn.id)) fun p => by
      simp only [id_eq, hfun]

end Effectivity

end TauCeti.Oracle.Single.Code

namespace TauCeti.Enumeration

open TauCeti.Oracle.Single

/-! ### Relative serialization and stage characterizations -/

/-- Binary codes of serialized stages are oracle-computable, uniformly in all parameters of the
source stages, without monotonicity or infinitude assumptions. -/
theorem computableIn_serializedStage {α : Type*} [Primcodable α] {G : Set (ℕ →. ℕ)}
    {A : α → ℕ → Finset ℕ}
    (hA : ComputableIn G fun p : α × ℕ => Finset.equivBitIndices.symm (A p.1 p.2)) :
    ComputableIn G fun p : α × ℕ => Finset.equivBitIndices.symm (serializedStage (A p.1) p.2) := by
  have hunpair : ComputableIn G fun p : (α × ℕ) × (ℕ × ℕ) => p.2.1.unpair :=
    Primrec.unpair.computableIn.comp (ComputableIn.fst.comp ComputableIn.snd)
  have hcode : ComputableIn G fun p : (α × ℕ) × (ℕ × ℕ) =>
      Finset.equivBitIndices.symm (A p.1.1 p.2.1.unpair.2) :=
    hA.comp ((ComputableIn.fst.comp ComputableIn.fst).pair (ComputableIn.snd.comp hunpair))
  have hmem : ComputableIn G fun p : (α × ℕ) × (ℕ × ℕ) =>
      decide (p.2.1.unpair.1 ∈ A p.1.1 p.2.1.unpair.2) :=
    RecursiveIn.of_eq
      (Primrec.mem_equivBitIndices.decide.computableIn.comp
        (hcode.pair (ComputableIn.fst.comp hunpair))) fun p => by simp
  have hcond : Primrec fun q : Bool × ℕ × ℕ => bif q.1 then q.2.1 ||| 2 ^ q.2.2 else q.2.1 :=
    Primrec.cond Primrec.fst
      (Primrec.nat_lor.comp (Primrec.fst.comp Primrec.snd)
        (Primrec.nat_pow.comp (Primrec.const 2) (Primrec.snd.comp Primrec.snd)))
      (Primrec.fst.comp Primrec.snd)
  have hstep : ComputableIn₂ G fun (p : α × ℕ) (q : ℕ × ℕ) =>
      if q.1.unpair.1 ∈ A p.1 q.1.unpair.2 then q.2 ||| 2 ^ q.1.unpair.1 else q.2 :=
    RecursiveIn.of_eq
      (hcond.computableIn.comp
        (hmem.pair ((ComputableIn.snd.comp ComputableIn.snd).pair
          (ComputableIn.fst.comp hunpair)))) fun p => by simp
  refine RecursiveIn.of_eq (ComputableIn.nat_rec ComputableIn.snd (ComputableIn.const 0) hstep) ?_
  rintro ⟨a, s⟩
  congr 1
  induction s with
  | zero => simp
  | succ s ih =>
    simp only [ih, serializedStage_succ]
    split_ifs with h
    · exact (Finset.equivBitIndices_symm_insert _ _).symm
    · rfl

/-- The canonical `Z`-relative c.e. domain enumerations have uniformly `Z`-computable serialized
stages. -/
theorem computableIn_serializedStage_domStage_setAnswers (Z : Set ℕ) :
    ComputableIn {Z.oracle} fun p : Code × ℕ =>
      Finset.equivBitIndices.symm (serializedStage (p.1.domStage (Code.setAnswers Z)) p.2) :=
  computableIn_serializedStage (A := fun c : Code => c.domStage (Code.setAnswers Z))
    (Code.computableIn_domStage_setAnswers Z)

/-- The limit of finite stages whose binary codes are `Z`-computable is Σ⁰₁ relative to `Z`. -/
theorem isSigma_one_mem_stageLimit {Z : Set ℕ} {A : ℕ → Finset ℕ}
    (hA : ComputableIn {Z.oracle} fun s => Finset.equivBitIndices.symm (A s)) :
    IsSigma Z 1 fun x => x ∈ stageLimit A := by
  refine isSigma_one_iff.2 ⟨fun p => decide (p.1 ∈ A p.2), ?_, fun x => by simp⟩
  exact RecursiveIn.of_eq
    (Primrec.mem_equivBitIndices.decide.computableIn.comp
      ((hA.comp ComputableIn.snd).pair ComputableIn.fst)) fun p => by simp

/-- A predicate on `ℕ` is Σ⁰₁ relative to `Z` if and only if it is the limit of increasing finite
stages, starting empty, whose binary finite-set codes are `Z`-computable. -/
theorem isSigma_one_iff_exists_stages {Z : Set ℕ} {p : ℕ → Prop} :
    IsSigma Z 1 p ↔ ∃ A : ℕ → Finset ℕ, Monotone A ∧ A 0 = ∅ ∧
      ComputableIn {Z.oracle} (fun s => Finset.equivBitIndices.symm (A s)) ∧
      stageLimit A = {x | p x} := by
  constructor
  · intro hp
    obtain ⟨c, hc⟩ := isSigma_one_iff_exists_code.1 hp
    refine ⟨c.domStage (Code.setAnswers Z), c.monotone_domStage _, c.domStage_zero _,
      (Code.computableIn_domStage_setAnswers Z).comp
        ((ComputableIn.const c).pair ComputableIn.id), ?_⟩
    rw [Code.stageLimit_domStage_setAnswers]
    ext x
    exact (hc x).symm
  · rintro ⟨A, -, -, hA, hlim⟩
    exact (isSigma_one_mem_stageLimit hA).of_eq fun x => by rw [hlim, Set.mem_ofPred_eq]

/-- A predicate on `ℕ` is Σ⁰₁ relative to `Z` if and only if it is the limit of increasing
`Z`-computable finite stages starting empty with at most one new entry per stage. -/
theorem isSigma_one_iff_exists_serialized_stages {Z : Set ℕ} {p : ℕ → Prop} :
    IsSigma Z 1 p ↔ ∃ A : ℕ → Finset ℕ, Monotone A ∧ A 0 = ∅ ∧
      (∀ s, (fresh A s).card ≤ 1) ∧
      ComputableIn {Z.oracle} (fun s => Finset.equivBitIndices.symm (A s)) ∧
      stageLimit A = {x | p x} := by
  constructor
  · intro hp
    obtain ⟨c, hc⟩ := isSigma_one_iff_exists_code.1 hp
    refine ⟨serializedStage (c.domStage (Code.setAnswers Z)), monotone_serializedStage _,
      serializedStage_zero _, card_fresh_serializedStage_le_one _,
      (computableIn_serializedStage_domStage_setAnswers Z).comp
        ((ComputableIn.const c).pair ComputableIn.id), ?_⟩
    rw [stageLimit_serializedStage, Code.stageLimit_domStage_setAnswers]
    ext x
    exact (hc x).symm
  · rintro ⟨A, hmono, hzero, -, hA, hlim⟩
    exact isSigma_one_iff_exists_stages.2 ⟨A, hmono, hzero, hA, hlim⟩

/-! ### Uniform stage comparison -/

/-- Partial stage comparison: the least stage `t` at which `B t` contains every element of `A s`.
Defined whenever such a stage exists, without requiring totality or monotonicity in the
definition. -/
def stageCompare (A B : ℕ → Finset ℕ) (s : ℕ) : Part ℕ :=
  Nat.rfind (PFun.lift fun t => decide (A s ⊆ B t))

/-- `stageCompare A B s` returns the least stage `t` with `A s ⊆ B t`. -/
@[simp]
theorem mem_stageCompare {A B : ℕ → Finset ℕ} {s t : ℕ} :
    t ∈ stageCompare A B s ↔ A s ⊆ B t ∧ ∀ t' < t, ¬ A s ⊆ B t' := by
  rw [stageCompare, Nat.mem_rfind]
  simp

/-- Any value returned by `stageCompare A B s` is a stage at which `B` contains `A s`. -/
theorem subset_of_mem_stageCompare {A B : ℕ → Finset ℕ} {s t : ℕ} (h : t ∈ stageCompare A B s) :
    A s ⊆ B t :=
  (mem_stageCompare.1 h).1

/-- `stageCompare A B s` is defined exactly when some stage of `B` contains `A s`. -/
@[simp]
theorem stageCompare_dom {A B : ℕ → Finset ℕ} {s : ℕ} :
    (stageCompare A B s).Dom ↔ ∃ t, A s ⊆ B t := by
  rw [stageCompare, Nat.rfind_dom]
  simp

/-- If `B` is monotone and `stageLimit A ⊆ stageLimit B`, then `stageCompare A B` is total. -/
theorem stageCompare_dom_of_stageLimit_subset {A B : ℕ → Finset ℕ} (hB : Monotone B)
    (hsub : stageLimit A ⊆ stageLimit B) (s : ℕ) : (stageCompare A B s).Dom := by
  have hfin : ∀ F : Finset ℕ, (F : Set ℕ) ⊆ stageLimit B → ∃ t, F ⊆ B t := by
    intro F
    induction F using Finset.induction_on with
    | empty => intro _; exact ⟨0, Finset.empty_subset _⟩
    | insert a F _ ih =>
      intro hF
      obtain ⟨t₁, ht₁⟩ := mem_stageLimit.1 (hF (Finset.mem_insert_self a F))
      obtain ⟨t₂, ht₂⟩ := ih fun x hx => hF (Finset.mem_insert_of_mem hx)
      exact ⟨max t₁ t₂, Finset.insert_subset (hB (le_max_left _ _) ht₁)
        (ht₂.trans (hB (le_max_right _ _)))⟩
  exact stageCompare_dom.2 (hfin (A s) fun x hx => hsub (subset_stageLimit A s hx))

/-- For monotone `B`, inclusion of limiting sets is equivalent to totality of `stageCompare A B`. -/
theorem stageLimit_subset_iff_forall_stageCompare_dom {A B : ℕ → Finset ℕ} (hB : Monotone B) :
    stageLimit A ⊆ stageLimit B ↔ ∀ s, (stageCompare A B s).Dom := by
  refine ⟨fun hsub s => stageCompare_dom_of_stageLimit_subset hB hsub s, fun hdom x hx => ?_⟩
  obtain ⟨s, hs⟩ := mem_stageLimit.1 hx
  obtain ⟨t, ht⟩ := stageCompare_dom.1 (hdom s)
  exact mem_stageLimit.2 ⟨t, ht hs⟩

/-- For monotone enumerations, equality of limiting sets is equivalent to totality of both
directions of `stageCompare`. -/
theorem stageLimit_eq_iff_forall_stageCompare_dom {A B : ℕ → Finset ℕ} (hA : Monotone A)
    (hB : Monotone B) :
    stageLimit A = stageLimit B ↔
      (∀ s, (stageCompare A B s).Dom) ∧ (∀ s, (stageCompare B A s).Dom) := by
  rw [Set.Subset.antisymm_iff, stageLimit_subset_iff_forall_stageCompare_dom hB,
    stageLimit_subset_iff_forall_stageCompare_dom hA]

/-- Stage comparison is recursive in `G`, uniformly in all parameters of the two enumerations. -/
theorem recursiveIn_stageCompare {α : Type*} [Primcodable α] {G : Set (ℕ →. ℕ)}
    {A B : α → ℕ → Finset ℕ}
    (hA : ComputableIn G fun p : α × ℕ => Finset.equivBitIndices.symm (A p.1 p.2))
    (hB : ComputableIn G fun p : α × ℕ => Finset.equivBitIndices.symm (B p.1 p.2)) :
    RecursiveIn G fun p : α × ℕ => stageCompare (A p.1) (B p.1) p.2 := by
  -- Test `A a s ⊆ B a t` via binary codes: `m &&& n = m`.
  have hsub_iff (D₁ D₂ : Finset ℕ) :
      (Finset.equivBitIndices.symm D₁ &&& Finset.equivBitIndices.symm D₂ =
        Finset.equivBitIndices.symm D₁) ↔ D₁ ⊆ D₂ := by
    rw [← Finset.equivBitIndices.injective.eq_iff, Finset.equivBitIndices_land,
      Equiv.apply_symm_apply, Equiv.apply_symm_apply, Finset.inter_eq_left]
  have htest : ComputableIn G fun q : (α × ℕ) × ℕ =>
      if A q.1.1 q.1.2 ⊆ B q.1.1 q.2 then 0 else 1 := by
    have hm : ComputableIn G fun q : (α × ℕ) × ℕ => Finset.equivBitIndices.symm (A q.1.1 q.1.2) :=
      hA.comp ComputableIn.fst
    have hn : ComputableIn G fun q : (α × ℕ) × ℕ => Finset.equivBitIndices.symm (B q.1.1 q.2) :=
      hB.comp ((ComputableIn.fst.comp ComputableIn.fst).pair ComputableIn.snd)
    have hcmp : Primrec fun p : ℕ × ℕ => if p.1 &&& p.2 = p.1 then 0 else 1 :=
      Primrec.ite (Primrec.eq.comp Primrec.nat_land Primrec.fst)
        (Primrec.const 0) (Primrec.const 1)
    exact RecursiveIn.of_eq (hcmp.computableIn.comp (hm.pair hn)) fun q => by
      simp only [hsub_iff]
  unfold ComputableIn RecursiveIn at htest
  unfold RecursiveIn
  refine htest.rfind.of_eq fun n => ?_
  cases e : decode (α := α × ℕ) n with
  | none =>
    simpa [e, decode_prod_val] using Nat.rfind_zero_none (fun _ => Part.none) rfl
  | some p =>
    simp only [decode_prod_val, Nat.unpair_pair, decode_nat, Option.map_some, e, Option.bind_some,
      Part.map_some, Part.map_eq_map, Part.coe_some, Part.bind_some, stageCompare]
    congr 1
    funext t
    split_ifs with h <;> simp [h]

/-- Stage comparison is partial computable, uniformly in all parameters of the two enumerations. -/
theorem partrec_stageCompare {α : Type*} [Primcodable α] {A B : α → ℕ → Finset ℕ}
    (hA : Computable fun p : α × ℕ => Finset.equivBitIndices.symm (A p.1 p.2))
    (hB : Computable fun p : α × ℕ => Finset.equivBitIndices.symm (B p.1 p.2)) :
    Partrec fun p : α × ℕ => stageCompare (A p.1) (B p.1) p.2 :=
  recursiveIn_empty_iff.1 (recursiveIn_stageCompare hA.computableIn hB.computableIn)

/-- Totality corollary: whenever `stageCompare` is total across a uniformly oracle-computable
family of pairs of enumerations, the resulting stage-transfer map is total and oracle-computable. -/
theorem computableIn_stageCompare_get {α : Type*} [Primcodable α] {G : Set (ℕ →. ℕ)}
    {A B : α → ℕ → Finset ℕ}
    (hA : ComputableIn G fun p : α × ℕ => Finset.equivBitIndices.symm (A p.1 p.2))
    (hB : ComputableIn G fun p : α × ℕ => Finset.equivBitIndices.symm (B p.1 p.2))
    (hdom : ∀ a s, (stageCompare (A a) (B a) s).Dom) :
    ComputableIn G fun p : α × ℕ => (stageCompare (A p.1) (B p.1) p.2).get (hdom p.1 p.2) :=
  (recursiveIn_stageCompare hA hB).of_eq_tot fun p => Part.get_mem (hdom p.1 p.2)

/-- Two monotone oracle-computable enumerations with the same limiting set admit total
oracle-computable stage-comparison maps witnessing both inclusions `A s ⊆ B (f s)` and
`B s ⊆ A (g s)`. -/
theorem exists_computableIn_stage_comparison {G : Set (ℕ →. ℕ)} {A B : ℕ → Finset ℕ}
    (hA_mono : Monotone A) (hB_mono : Monotone B)
    (hA : ComputableIn G fun s => Finset.equivBitIndices.symm (A s))
    (hB : ComputableIn G fun s => Finset.equivBitIndices.symm (B s))
    (heq : stageLimit A = stageLimit B) :
    ∃ f g : ℕ → ℕ, ComputableIn G f ∧ ComputableIn G g ∧
      (∀ s, A s ⊆ B (f s)) ∧ (∀ s, B s ⊆ A (g s)) := by
  have hdomAB : ∀ (_ : Unit) s, (stageCompare A B s).Dom :=
    fun _ s => stageCompare_dom_of_stageLimit_subset hB_mono heq.le s
  have hdomBA : ∀ (_ : Unit) s, (stageCompare B A s).Dom :=
    fun _ s => stageCompare_dom_of_stageLimit_subset hA_mono heq.ge s
  have hf := (computableIn_stageCompare_get (A := fun _ : Unit => A) (B := fun _ : Unit => B)
    (hA.comp ComputableIn.snd) (hB.comp ComputableIn.snd) hdomAB).comp
    ((ComputableIn.const ()).pair ComputableIn.id)
  have hg := (computableIn_stageCompare_get (A := fun _ : Unit => B) (B := fun _ : Unit => A)
    (hB.comp ComputableIn.snd) (hA.comp ComputableIn.snd) hdomBA).comp
    ((ComputableIn.const ()).pair ComputableIn.id)
  exact ⟨_, _, hf, hg, fun s => subset_of_mem_stageCompare (Part.get_mem (hdomAB () s)),
    fun s => subset_of_mem_stageCompare (Part.get_mem (hdomBA () s))⟩

end TauCeti.Enumeration
