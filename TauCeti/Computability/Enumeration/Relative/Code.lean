/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Computability.Enumeration.Stage
public import TauCeti.Computability.RecursiveIn
public import TauCeti.Computability.SingleOracle.Stage

/-!
# Relative finite-stage domain enumerations of oracle programs

For an oracle program `c : TauCeti.Oracle.Single.Code` and oracle answers `σ : ℕ → Option ℕ`,
`c.domStage σ s` is the normalized finite stage `W_{c,s}^σ`: the inputs on which `c` halts at
stage `s` under `TauCeti.Oracle.Single.Code.evalStage`. By Soare's stage bounds, every member is
below `s` and `c.domStage σ s = ∅` whenever `s ≤ encode c`.

When `σ` fixes the answers of a set oracle `Z` (or a total oracle `O`), these stages start empty,
increase with `s`, and have limit `(Code.eval Z.oracle c).Dom`. Their binary finite-set codes are
primitive recursive uniformly in any primitive-recursive family of finite oracle answers (such as
finite oracle strings or binary-coded finite sets), and uniformly `G`-computable in the family
parameter, program, and stage for any `G`-computable family of optional oracle answers.

Serialization, bridge lemmas to ordinary `Nat.Partrec.Code.domStage`, and `Σ⁰₁` stage
characterizations live downstream in `TauCeti.Computability.Enumeration.Relative.Basic`.

## Main definitions

* `TauCeti.Oracle.Single.Code.domStage`: the normalized finite stage `W_{c,s}^σ` of the domain of
  an oracle program `c` against oracle answers `σ`.

## Main results

* `TauCeti.Oracle.Single.Code.domStage_def`, `TauCeti.Oracle.Single.Code.mem_domStage`,
  `TauCeti.Oracle.Single.Code.domStage_subset_range`,
  `TauCeti.Oracle.Single.Code.domStage_zero`,
  `TauCeti.Oracle.Single.Code.domStage_eq_empty_of_le_encode`: definition and basic stage bounds.
* `TauCeti.Oracle.Single.Code.monotone_domStage`,
  `TauCeti.Oracle.Single.Code.domStage_eq_of_eqOn`,
  `TauCeti.Oracle.Single.Code.domStage_range_map_option`,
  `TauCeti.Oracle.Single.Code.domStage_range_map`,
  `TauCeti.Oracle.Single.Code.stageLimit_domStage`: monotonicity, prefix agreement, and domain
  limit.
* `TauCeti.Oracle.Single.Code.primrecRel_mem_domStage`,
  `TauCeti.Oracle.Single.Code.primrec_domStage`,
  `TauCeti.Oracle.Single.Code.computableIn_domStage`,
  `TauCeti.Oracle.Single.Code.computableIn_domStage_total`,
  `TauCeti.Oracle.Single.Code.computableIn_domStage_setAnswers`: uniform effectivity of the
  normalized stages and their binary finite-set codes.

## References

* R. I. Soare, *Recursively Enumerable Sets and Degrees*, Springer, 1987, Chapters II.1–2 and III.1.
-/

public section

open Encodable TauCeti.Enumeration

namespace TauCeti.Oracle.Single.Code

/-- The normalized finite stage `W_{c,s}^σ` of the domain of an oracle program `c` against oracle
answers `σ`: the inputs on which `evalStage σ s c` succeeds. -/
def domStage (c : Code) (σ : ℕ → Option ℕ) (s : ℕ) : Finset ℕ :=
  (Finset.range s).filter fun x => (evalStage σ s c x).isSome

/-- Unfolding equation for `domStage` as a filtered initial interval. -/
theorem domStage_def (c : Code) (σ : ℕ → Option ℕ) (s : ℕ) :
    c.domStage σ s = (Finset.range s).filter fun x => (evalStage σ s c x).isSome := by
  rw [domStage]

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

/-- Against optional oracle answers `σ`, stage `s` of the domain depends only on the first `s`
answers of `σ`. -/
theorem domStage_range_map_option (σ : ℕ → Option ℕ) (c : Code) (s : ℕ) :
    c.domStage (fun z => (((List.range s).map σ)[z]?).bind id) s =
      c.domStage σ s :=
  domStage_eq_of_eqOn fun z hz => by simp [Set.mem_Iio.1 hz]

/-- Against a total oracle `O`, stage `s` of the domain depends only on the first `s` answers of
`O`. -/
theorem domStage_range_map (O : ℕ → ℕ) (c : Code) (s : ℕ) :
    c.domStage (fun z => ((List.range s).map O)[z]?) s =
      c.domStage (fun z => some (O z)) s := by
  have h : (fun z : ℕ => ((List.range s).map O)[z]?) =
      fun z => (((List.range s).map (some ∘ O))[z]?).bind id := by
    funext z
    rw [List.getElem?_map, List.getElem?_map, Option.bind_map]
    exact Option.map_eq_bind
  rw [h]
  exact domStage_range_map_option (some ∘ O) c s

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

section Effectivity

open Primrec

variable {α : Type*} [Primcodable α]

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

/-- Binary finite-set codes of domain stages against a uniformly oracle-computable family of
optional oracle answers are oracle-computable, uniformly in the family parameter, the program, and
the stage. -/
theorem computableIn_domStage {G : Set (ℕ →. ℕ)} {σ : α → ℕ → Option ℕ}
    (hσ : ComputableIn₂ G σ) :
    ComputableIn G fun p : α × Code × ℕ =>
      Finset.equivBitIndices.symm (p.2.1.domStage (σ p.1) p.2.2) := by
  have hp : ComputableIn G (fun p : α × Code × ℕ => (List.range p.2.2).map (σ p.1)) :=
    hσ.list_range_map.comp (ComputableIn.fst.pair (ComputableIn.snd.comp ComputableIn.snd))
  have hlookup : Primrec₂ fun (l : List (Option ℕ)) z => l[z]?.bind id :=
    (Primrec.option_bind₁ Primrec.id).comp Primrec.list_getElem?
  exact RecursiveIn.of_eq ((primrec_domStage hlookup).computableIn.comp (hp.pair ComputableIn.snd))
    fun p => congrArg (fun S => Part.some (Finset.equivBitIndices.symm S))
      (domStage_range_map_option (σ p.1) p.2.1 p.2.2)

/-- For a total oracle `O`, binary finite-set codes of `O`-relative domain stages are computable in
`O`, uniformly in the program and the stage. -/
theorem computableIn_domStage_total (O : ℕ → ℕ) :
    ComputableIn {(O : ℕ →. ℕ)} fun p : Code × ℕ =>
      Finset.equivBitIndices.symm (p.1.domStage (fun z => some (O z)) p.2) := by
  have hO : ComputableIn {(O : ℕ →. ℕ)} O :=
    RecursiveIn.of_eq (RecursiveIn.oracle (O : ℕ →. ℕ) rfl) fun _ => rfl
  have hO₂ : ComputableIn₂ {(O : ℕ →. ℕ)} (fun (_ : Unit) z => some (O z)) :=
    Primrec.option_some.computableIn.comp (hO.comp ComputableIn.snd)
  exact RecursiveIn.of_eq
    ((computableIn_domStage hO₂).comp ((ComputableIn.const ()).pair ComputableIn.id))
    fun _ => rfl

/-- For a set oracle `Z`, binary finite-set codes of `Z`-relative domain stages are computable in
`Z`, uniformly in the program and the stage. -/
theorem computableIn_domStage_setAnswers (Z : Set ℕ) :
    ComputableIn {Z.oracle} fun p : Code × ℕ =>
      Finset.equivBitIndices.symm (p.1.domStage (setAnswers Z) p.2) := by
  have htot : ComputableIn {Z.oracle} fun p : Code × ℕ =>
      Finset.equivBitIndices.symm (p.1.domStage (fun z => some (Z.indicator 1 z)) p.2) :=
    Set.oracle_eq_indicator Z ▸ computableIn_domStage_total (Z.indicator 1)
  exact RecursiveIn.of_eq htot fun p =>
    congrArg (fun σ => Part.some (Finset.equivBitIndices.symm (p.1.domStage σ p.2)))
      (funext fun z => (setAnswers_apply Z z).symm)

end Effectivity

end TauCeti.Oracle.Single.Code
