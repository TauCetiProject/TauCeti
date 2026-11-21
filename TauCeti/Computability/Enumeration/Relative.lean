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
# Relative finite-stage enumerations

For an oracle program `c : TauCeti.Oracle.Single.Code` and oracle answers `σ : ℕ → Option ℕ`,
`c.domStage σ s` is the normalized finite stage `W_{c,s}^σ`: the inputs on which `c` halts at
stage `s` under `TauCeti.Oracle.Single.Code.evalStage`. By Soare's stage bounds, every member is
below `s` and `c.domStage σ s = ∅` whenever `s ≤ encode c`.

When `σ` fixes the answers of a set oracle `Z` (or a total oracle `O`), these stages start empty,
increase with `s`, and have limit `(Code.eval Z.oracle c).Dom`. Their binary finite-set codes are
primitive recursive uniformly in any primitive-recursive family of finite oracle answers (such as
finite oracle strings or binary-coded finite sets), and `Z`-computable uniformly in the program
and the stage. Applying `TauCeti.Enumeration.serializedStage` yields uniformly `Z`-computable
single-entry stages, characterizing `IsSigma Z 1` predicates on `ℕ` as limits of `Z`-computable
monotone finite stages (with or without serialization).

## Main definitions

* `TauCeti.Oracle.Single.Code.domStage`: the normalized finite stage `W_{c,s}^σ` of the domain of
  an oracle program `c` against oracle answers `σ`.

## Main results

* `TauCeti.Oracle.Single.Code.monotone_domStage`,
  `TauCeti.Oracle.Single.Code.stageLimit_domStage`: the stages start empty, increase, and limit
  to the domain of the oracle program.
* `TauCeti.Oracle.Single.Code.primrec₂_evalStage_isSome`,
  `TauCeti.Oracle.Single.Code.primrecRel_mem_domStage`,
  `TauCeti.Oracle.Single.Code.primrec_domStage`,
  `TauCeti.Oracle.Single.Code.computableIn_domStage_setAnswers`: uniform effectivity of the
  normalized stages and their binary finite-set codes.
* `TauCeti.Enumeration.computableIn_serializedStage_domStage_setAnswers`: relative serialization
  produces uniformly `Z`-computable domain stages.
* `TauCeti.Enumeration.isSigma_one_mem_stageLimit`,
  `TauCeti.Enumeration.isSigma_one_mem_stageLimit_of_equivBitIndices`: limits of finite stages
  with `Z`-computable membership (in particular, `Z`-computable binary codes) are Σ⁰₁ relative
  to `Z`.
* `TauCeti.Enumeration.isSigma_one_iff_exists_stages`,
  `TauCeti.Enumeration.isSigma_one_iff_exists_serialized_stages`: relative stage characterizations
  of Σ⁰₁ predicates on `ℕ`.

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

/-- Halting of bounded oracle simulation is primitive recursive in any primitive-recursive family
of oracle answers, the program, the stage, and the input. -/
theorem primrec₂_evalStage_isSome {σ : α → ℕ → Option ℕ} (hσ : Primrec₂ σ) :
    Primrec₂ fun (p : α × Code × ℕ) x => (evalStage (σ p.1) p.2.2 p.2.1 x).isSome :=
  option_isSome.comp <| (primrec_evalStage hσ).comp <|
    (fst.comp fst).pair <| (snd.comp (snd.comp fst)).pair <|
      (fst.comp (snd.comp fst)).pair snd

/-- Membership in normalized domain stages is primitive recursive, uniformly in any
primitive-recursive family of oracle answers, the program, the stage, and the number. -/
theorem primrecRel_mem_domStage {σ : α → ℕ → Option ℕ} (hσ : Primrec₂ σ) :
    PrimrecRel fun (p : α × Code × ℕ) x => x ∈ p.2.1.domStage (σ p.1) p.2.2 :=
  (Primrec.eq.comp (primrec₂_evalStage_isSome hσ) (const true)).of_eq fun p => by simp

/-- Binary finite-set codes of normalized domain stages are primitive recursive, uniformly in any
primitive-recursive family of oracle answers, the program, and the stage. -/
theorem primrec_domStage {σ : α → ℕ → Option ℕ} (hσ : Primrec₂ σ) :
    Primrec fun p : α × Code × ℕ => Finset.equivBitIndices.symm (p.2.1.domStage (σ p.1) p.2.2) :=
  (Primrec.equivBitIndices_symm_filter_range (snd.comp snd)
    (primrec₂_evalStage_isSome hσ)).of_eq fun _ => rfl

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

/-- The canonical `Z`-relative c.e. domain enumerations have uniformly `Z`-computable serialized
stages. -/
theorem computableIn_serializedStage_domStage_setAnswers (Z : Set ℕ) :
    ComputableIn {Z.oracle} fun p : Code × ℕ =>
      Finset.equivBitIndices.symm (serializedStage (p.1.domStage (Code.setAnswers Z)) p.2) :=
  computableIn_serializedStage (A := fun c : Code => c.domStage (Code.setAnswers Z))
    (Code.computableIn_domStage_setAnswers Z)

/-- The limit of finite stages whose membership relation is `Z`-computable is Σ⁰₁ relative to
`Z`. -/
theorem isSigma_one_mem_stageLimit {Z : Set ℕ} {A : ℕ → Finset ℕ}
    (hA : ComputableIn {Z.oracle} fun p : ℕ × ℕ => decide (p.1 ∈ A p.2)) :
    IsSigma Z 1 fun x => x ∈ stageLimit A :=
  isSigma_one_iff.2 ⟨fun p => decide (p.1 ∈ A p.2), hA, fun x => by simp⟩

/-- Membership in finite stages is oracle-computable, uniformly in the element and the stage,
when their binary finite-set codes are oracle-computable. -/
theorem computableIn_mem_of_computableIn_equivBitIndices {G : Set (ℕ →. ℕ)} {A : ℕ → Finset ℕ}
    (hA : ComputableIn G fun s => Finset.equivBitIndices.symm (A s)) :
    ComputableIn G fun p : ℕ × ℕ => decide (p.1 ∈ A p.2) :=
  RecursiveIn.of_eq
    (Primrec.mem_equivBitIndices.decide.computableIn.comp
      ((hA.comp ComputableIn.snd).pair ComputableIn.fst)) fun p => by simp

/-- The limit of finite stages whose binary codes are `Z`-computable is Σ⁰₁ relative to `Z`. -/
theorem isSigma_one_mem_stageLimit_of_equivBitIndices {Z : Set ℕ} {A : ℕ → Finset ℕ}
    (hA : ComputableIn {Z.oracle} fun s => Finset.equivBitIndices.symm (A s)) :
    IsSigma Z 1 fun x => x ∈ stageLimit A :=
  isSigma_one_mem_stageLimit (computableIn_mem_of_computableIn_equivBitIndices hA)

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
    exact (isSigma_one_mem_stageLimit_of_equivBitIndices hA).of_eq fun x => by
      rw [hlim, Set.mem_ofPred_eq]

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

end TauCeti.Enumeration
