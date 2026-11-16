/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Computability.Hierarchy.NormalForm.BoundedQuantifiers
public import TauCeti.Computability.Hierarchy.Totality
import TauCeti.Computability.SingleOracle.Primrec
import TauCeti.Data.PFun.Basic

/-!
# Jump compilers, Σ⁰₁ domain correspondence, and normal-form boundary examples

This file connects displayed `NormalForm` codes at prefix `QuantifierPrefix.sigma 0` uniformly to
oracle-program domains and `Set.jump` (`toDomCode`, `jumpQuery`, `ofDomCode`, `ofDomQuery`,
`jumpNormalForm`), and proves the two L3.2 boundary results: `totality Z` versus single halting
queries (`totalityNormalForm`, `not_exists_low_normalForm_totality`,
`not_exists_computable_sigma_zero_query_totality`), and decidable rule checking versus theoremhood
(`InferenceSystem`, `NormalForm.deductiveClosure`, `haltingInferenceSystem`).

## References

* R. I. Soare, *Recursively Enumerable Sets and Degrees*, Springer, 1987, Chapters III.2, IV.1,
  and IV.3.
-/

public section

open Encodable Denumerable Primrec TauCeti.Oracle.Single

namespace TauCeti.ArithmeticalHierarchy

namespace NormalForm

/-! ### Query-free total helper codes from primitive-recursive functions -/

private noncomputable def primrecCode {g : ℕ → ℕ} (hg : Primrec g) : Code :=
  (Nat.Partrec.Code.exists_code.1 hg.to_comp.partrec).choose.toSingleOracleCode
@[simp] private theorem eval_primrecCode {g : ℕ → ℕ} (hg : Primrec g) (O : ℕ →. ℕ) (n : ℕ) :
    Code.eval O (primrecCode hg) n = Part.some (g n) := by
  simpa [primrecCode] using
    congrFun (Nat.Partrec.Code.exists_code.1 hg.to_comp.partrec).choose_spec n

private def defaultTuple : (k : ℕ) → ArityTuple k
  | 0 => () | 1 => 0 | k + 2 => (defaultTuple (k + 1), 0)

private noncomputable def mapCode (k₁ k₂ : ℕ) {f : ArityTuple k₁ → ArityTuple k₂}
    (hf : Primrec f) : Code :=
  primrecCode <| Primrec.encode.comp <|
    hf.comp (option_getD.comp Primrec.decode (const (defaultTuple k₁)))
private theorem exists_eval_mapCode (O : ℕ →. ℕ) (k₁ k₂ : ℕ) {f : ArityTuple k₁ → ArityTuple k₂}
    (hf : Primrec f) (a : ℕ) : ∃ b : ℕ, Code.eval O (mapCode k₁ k₂ hf) a = Part.some b :=
  ⟨_, eval_primrecCode _ O a⟩
private theorem eval_mapCode (O : ℕ →. ℕ) (k₁ k₂ : ℕ) {f : ArityTuple k₁ → ArityTuple k₂}
    (hf : Primrec f) (xs : ArityTuple k₁) :
    Code.eval O (mapCode k₁ k₂ hf) (encode xs) = Part.some (encode (f xs)) := by
  simp [mapCode, encodek]

private noncomputable abbrev qfCode (k : ℕ) {b : ArityTuple k → Bool} (hb : Primrec b) :
    NormalForm := ⟨.qf, k, mapCode k 1 (Primrec.encode.comp hb)⟩
private theorem valid_qfCode {Z : Set ℕ} {k : ℕ} {b : ArityTuple k → Bool} (hb : Primrec b) :
    (qfCode k hb).Valid Z := by
  rw [valid_iff_validAux]; by_cases hk : k = 0 <;> simp [mapCode, hk, validDepth_zero]
private theorem evalTuple_qfCode {Z : Set ℕ} {k : ℕ} {b : ArityTuple k → Bool} (hb : Primrec b)
    (xs : ArityTuple k) : (qfCode k hb).EvalTuple Z xs ↔ b xs = true := by
  cases hbx : b xs <;> simp [mapCode, evalTuple_iff_holdsCode, encodek, hbx]

/-! ### Uniform Σ⁰₁ ↔ oracle-program domain ↔ jump compilers -/

/-- Compile a `sigma 0` normal-form code into an oracle program searching for the least witness `y`
making its Boolean matrix evaluate to `true`. -/
def toDomCode (c : NormalForm) : Code :=
  .comp (.rfind' (.comp notBoolCode c.matrix)) (.pair idCode .zero)

theorem primrec_toDomCode : Primrec toDomCode :=
  Code.primrec₂_comp.comp
    (Code.primrec_rfind'.comp (Code.primrec₂_comp.comp (const notBoolCode) primrec_matrix))
    (const (Code.pair idCode .zero))

/-- Compile a `sigma 0` normal-form code and an encoded tuple `a` into a program whose self-halting
membership `encode (c.jumpQuery a) ∈ Z.jump` tests `c.HoldsCode Z a`. -/
def jumpQuery (c : NormalForm) (a : ℕ) : Code :=
  .comp c.toDomCode (Nat.Partrec.Code.const a).toSingleOracleCode

theorem primrec₂_jumpQuery : Primrec₂ jumpQuery :=
  Code.primrec₂_comp.comp (primrec_toDomCode.comp fst)
    (Nat.Partrec.Code.primrec_toSingleOracleCode.comp (Nat.Partrec.Code.primrec_const.comp snd))

theorem jumpQuery_injective_right (c : NormalForm) : Function.Injective c.jumpQuery :=
  fun _ _ h => by
    simp only [jumpQuery, Code.comp.injEq] at h
    exact Nat.Partrec.Code.const_inj (Nat.Partrec.Code.toSingleOracleCode_injective h.2)

@[simp] theorem eval_jumpQuery (O : ℕ →. ℕ) (c : NormalForm) (a x : ℕ) :
    Code.eval O (c.jumpQuery a) x = Code.eval O c.toDomCode a := by
  simp [jumpQuery, Nat.Partrec.Code.eval_const, PFun.some_bind]

/-- On inputs where a `sigma 0` matrix is valid, `toDomCode` halts iff `HoldsCode` holds. -/
theorem dom_eval_toDomCode_iff_of_validAux {Z : Set ℕ} {c : NormalForm} {a : ℕ}
    (hp : c.pref = .sigma 0) (hv : ValidAux Z c.matrix c.pref a) :
    (Code.eval Z.oracle c.toDomCode a).Dom ↔ c.HoldsCode Z a := by
  have hva : ∀ y, ValidDepth Z c.matrix 0 (Nat.pair a y) := by simpa [hp] using hv
  choose b hbeq using fun y => (validDepth_zero Z c.matrix (Nat.pair a y)).1 (hva y)
  let fb : ℕ →. Bool := fun y => Part.some (b y)
  have hrf : Code.eval Z.oracle c.toDomCode a = Nat.rfind fb := by
    rw [toDomCode, Code.eval_comp, show Code.eval Z.oracle (.pair idCode .zero) a =
      Part.some (Nat.pair a 0) by simp [Seq.seq], PFun.some_bind, Code.eval_rfind']
    have hfun : (Nat.rfind fun n => (fun m => m = 0) <$>
        Code.eval Z.oracle (notBoolCode.comp c.matrix) (Nat.pair a (n + 0))) = Nat.rfind fb := by
      congr 1; funext y; rw [add_zero]; cases hby : b y <;> simp [fb, hbeq y, hby, PFun.some_bind]
    rw [hfun]; ext; simp
  rw [hrf, Nat.rfind_dom]
  simp only [fb, holdsCode_iff, hp, holdsAux_eq_holdsBlock, QuantifierPrefix.startsExists_sigma,
    QuantifierPrefix.depth_sigma, holdsBlock_true_succ, holdsBlock_zero]
  refine ⟨fun ⟨y, hy, _⟩ => ⟨y, ?_⟩, fun ⟨y, hy⟩ =>
    ⟨y, Part.mem_some_iff.2 (by rwa [hbeq y, Part.mem_some_iff, encode_inj] at hy),
      fun _ => trivial⟩⟩
  rw [hbeq y, (Part.mem_some_iff.1 hy).symm]; exact Part.mem_some _

@[simp] theorem Valid.dom_eval_toDomCode_iff {Z : Set ℕ} {c : NormalForm} (hc : c.Valid Z)
    (hp : c.pref = .sigma 0) (xs : ArityTuple c.arity) :
    (Code.eval Z.oracle c.toDomCode (encode xs)).Dom ↔ c.EvalTuple Z xs :=
  (dom_eval_toDomCode_iff_of_validAux hp ((valid_iff Z c).1 hc xs)).trans
    (evalTuple_iff_holdsCode Z c xs).symm

theorem Valid.encode_jumpQuery_mem_jump_iff {Z : Set ℕ} {c : NormalForm} (hc : c.Valid Z)
    (hp : c.pref = .sigma 0) (xs : ArityTuple c.arity) :
    encode (c.jumpQuery (encode xs)) ∈ Z.jump ↔ c.EvalTuple Z xs := by
  simpa [Set.mem_jump] using hc.dom_eval_toDomCode_iff hp xs

/-! ### Uniform bounded-halting matrix for `ofDomCode` -/

private theorem oracle_eq_indicator (Z : Set ℕ) :
    Z.oracle = ((Z.indicator 1 : ℕ → ℕ) : ℕ →. ℕ) := funext fun _ => by simp

private noncomputable def oraclePrefixCode : Code :=
  let step := primrecCode <| Primrec.encode.comp <| list_concat.comp
    ((Primrec.ofNat (List ℕ)).comp (fst.comp Primrec.unpair)) (snd.comp Primrec.unpair)
  .prec .zero (.comp step (.pair (.comp .right .right) (.comp .oracle (.comp .left .right))))

private theorem eval_oraclePrefixCode (O : ℕ → ℕ) (a k : ℕ) :
    Code.eval (O : ℕ →. ℕ) oraclePrefixCode (Nat.pair a k) =
      Part.some (encode ((List.range k).map O)) := by
  induction k with
  | zero => simp [oraclePrefixCode]
  | succ k ih =>
    dsimp only [oraclePrefixCode] at ih ⊢
    rw [Code.eval_prec_succ, ih]; simp [Seq.seq, List.range_succ]

private def boundedHaltBool (p : ℕ × ℕ × List ℕ) : Bool :=
  (Code.evaln (fun z => p.2.2[z]?) p.2.1 (ofNat Code p.1.unpair.1) p.1.unpair.2).isSome
private theorem primrec_boundedHaltBool : Primrec boundedHaltBool :=
  option_isSome.comp <| Code.primrec_evaln_list.comp <| (snd.comp snd).pair <|
    (fst.comp snd).pair <| ((Primrec.ofNat Code).comp (fst.comp (Primrec.unpair.comp fst))).pair
      (snd.comp (Primrec.unpair.comp fst))

private noncomputable def boundedHaltMatrix : Code :=
  let u1 := Primrec.unpair.comp (fst.comp Primrec.unpair)
  let chk := primrecCode <| Primrec.encode.comp <| primrec_boundedHaltBool.comp <|
    (fst.comp u1).pair ((snd.comp u1).pair
      ((Primrec.ofNat (List ℕ)).comp (snd.comp Primrec.unpair)))
  .comp chk (.pair (.pair .left .right) oraclePrefixCode)

/-- Uniformly compile an oracle program `c : Code` into a unary `sigma 0` normal-form code whose
predicate relative to every `Z : Set ℕ` is `(Code.eval Z.oracle c ·).Dom`. -/
noncomputable def ofDomCode (c : Code) : NormalForm :=
  ⟨.sigma 0, 1, .comp boundedHaltMatrix
    (.pair (.pair (Nat.Partrec.Code.const (encode c)).toSingleOracleCode .left) .right)⟩

/-- Uniformly compile an individual halting instance `(c, x)` into a nullary `sigma 0` normal-form
code representing `(Code.eval Z.oracle c x).Dom` relative to every `Z : Set ℕ`. -/
noncomputable def ofDomQuery (c : Code) (x : ℕ) : NormalForm :=
  (ofDomCode c).preimage 0 (Nat.Partrec.Code.const x).toSingleOracleCode

/-- Oracle-independent unary `sigma 0` normal-form code defining `Z.jump` relative to every
`Z : Set ℕ`. -/
noncomputable def jumpNormalForm : NormalForm :=
  (ofDomCode Code.universal).preimage 1 (.pair idCode idCode)

@[simp] theorem pref_ofDomCode (c : Code) : (ofDomCode c).pref = .sigma 0 := (rfl)
@[simp] theorem arity_ofDomCode (c : Code) : (ofDomCode c).arity = 1 := (rfl)
@[simp] theorem pref_ofDomQuery (c : Code) (x : ℕ) : (ofDomQuery c x).pref = .sigma 0 := by
  simp [ofDomQuery]
@[simp] theorem arity_ofDomQuery (c : Code) (x : ℕ) : (ofDomQuery c x).arity = 0 := by
  simp [ofDomQuery]
@[simp] theorem pref_jumpNormalForm : jumpNormalForm.pref = .sigma 0 := by simp [jumpNormalForm]
@[simp] theorem arity_jumpNormalForm : jumpNormalForm.arity = 1 := by simp [jumpNormalForm]

theorem primrec_ofDomCode : Primrec ofDomCode := by
  have hcst := Nat.Partrec.Code.primrec_toSingleOracleCode.comp
    (Nat.Partrec.Code.primrec_const.comp (Primrec.encode (α := Code)))
  have harg := Code.primrec₂_pair.comp
    (Code.primrec₂_pair.comp hcst (const Code.left)) (const Code.right)
  exact primrec₃_mk (const (QuantifierPrefix.sigma 0)) (const 1)
    (Code.primrec₂_comp.comp (const boundedHaltMatrix) harg)
theorem primrec₂_ofDomQuery : Primrec₂ ofDomQuery :=
  primrec₃_preimage (primrec_ofDomCode.comp fst) (const 0)
    (Nat.Partrec.Code.primrec_toSingleOracleCode.comp (Nat.Partrec.Code.primrec_const.comp snd))

private theorem eval_matrix_ofDomCode (Z : Set ℕ) (c : Code) (x k : ℕ) :
    Code.eval Z.oracle (ofDomCode c).matrix (Nat.pair x k) =
      Part.some (encode (Code.evaln
        (fun z => ((List.range k).map (Z.indicator 1))[z]?) k c x).isSome) := by
  have harg : Code.eval Z.oracle
      (.pair (.pair (Nat.Partrec.Code.const (encode c)).toSingleOracleCode .left) .right)
      (Nat.pair x k) = Part.some (Nat.pair (Nat.pair (encode c) x) k) := by
    simp [Seq.seq, Nat.Partrec.Code.eval_const]
  rw [ofDomCode, Code.eval_comp, harg, PFun.some_bind, oracle_eq_indicator Z]
  simp [boundedHaltMatrix, boundedHaltBool, eval_oraclePrefixCode, Seq.seq]

theorem valid_ofDomCode (Z : Set ℕ) (c : Code) : (ofDomCode c).Valid Z := by
  rw [valid_iff]; intro x; simp [validAux_eq_validDepth, eval_matrix_ofDomCode]

@[simp] theorem evalTuple_ofDomCode (Z : Set ℕ) (c : Code) (x : ArityTuple 1) :
    (ofDomCode c).EvalTuple Z x ↔ (Code.eval Z.oracle c x).Dom := by
  simp only [evalTuple_iff_holdsCode, holdsCode_iff, pref_ofDomCode, holdsAux_eq_holdsBlock,
    QuantifierPrefix.startsExists_sigma, QuantifierPrefix.depth_sigma, holdsBlock_true_succ,
    holdsBlock_zero, encode_nat, eval_matrix_ofDomCode, Part.mem_some_iff, encode_inj]
  rw [oracle_eq_indicator Z, Part.dom_iff_mem]
  simp only [Code.mem_eval_iff_exists_evaln_range_map, List.getElem?_map]
  exact ⟨fun ⟨k, h⟩ => let ⟨d, hd⟩ := Option.isSome_iff_exists.1 h.symm; ⟨d.output, k, d, hd, rfl⟩,
    fun ⟨_, k, d, hd, _⟩ => ⟨k, by rw [hd]; rfl⟩⟩

theorem valid_ofDomQuery (Z : Set ℕ) (c : Code) (x : ℕ) : (ofDomQuery c x).Valid Z :=
  (valid_ofDomCode Z c).preimage_of_forall (by simp) fun _ =>
    ⟨x, by simp [Nat.Partrec.Code.eval_const]⟩
@[simp] theorem evalTuple_ofDomQuery (Z : Set ℕ) (c : Code) (x : ℕ) (u : ArityTuple 0) :
    (ofDomQuery c x).EvalTuple Z u ↔ (Code.eval Z.oracle c x).Dom :=
  (evalTuple_preimage (c := ofDomCode c) (k := 0) (l := 1) (ys := (x : ArityTuple 1))
    (by simp [Nat.Partrec.Code.eval_const, encode_nat])).trans (evalTuple_ofDomCode Z c x)

theorem valid_jumpNormalForm (Z : Set ℕ) : jumpNormalForm.Valid Z :=
  (valid_ofDomCode Z Code.universal).preimage_of_forall (by simp) fun a =>
    ⟨Nat.pair a a, by simp [Seq.seq]⟩
@[simp] theorem evalTuple_jumpNormalForm (Z : Set ℕ) (e : ArityTuple 1) :
    jumpNormalForm.EvalTuple Z e ↔ e ∈ Z.jump := by
  rw [jumpNormalForm, evalTuple_preimage (c := ofDomCode Code.universal) (k := 1) (l := 1)
    (ys := (Nat.pair e e : ArityTuple 1)) (by simp [Seq.seq, encode_nat]),
    evalTuple_ofDomCode, Set.mem_jump]
  simp [oracle_eq_indicator Z]

end NormalForm

/-! ### Boundary example 1: `totality Z` versus single halting queries -/

/-- Oracle-independent unary `pi 1` (Π⁰₂) normal-form code representing `totality Z` relative to
every `Z : Set ℕ`. -/
noncomputable def totalityNormalForm : NormalForm :=
  ((NormalForm.ofDomCode Code.universal).preimage 2 NormalForm.idCode).bindForall

@[simp] theorem pref_totalityNormalForm : totalityNormalForm.pref = .pi 1 := by
  simp [totalityNormalForm]
@[simp] theorem arity_totalityNormalForm : totalityNormalForm.arity = 1 := by
  simp [totalityNormalForm]

theorem valid_totalityNormalForm (Z : Set ℕ) : totalityNormalForm.Valid Z :=
  ((NormalForm.valid_ofDomCode Z Code.universal).preimage_of_forall (by simp) fun p =>
    ⟨p, NormalForm.eval_idCode Z.oracle p⟩).bindForall

@[simp] theorem evalTuple_totalityNormalForm (Z : Set ℕ) (e : ArityTuple 1) :
    totalityNormalForm.EvalTuple Z e ↔ e ∈ totality Z := by
  have hinner := (NormalForm.valid_ofDomCode Z Code.universal).preimage_of_forall (k := 2)
    (f := NormalForm.idCode) (by simp) fun p => ⟨p, NormalForm.eval_idCode Z.oracle p⟩
  rw [totalityNormalForm, hinner.evalTuple_bindForall (by simp) e, mem_totality]
  refine forall_congr' fun x => ?_
  rw [NormalForm.evalTuple_preimage (c := NormalForm.ofDomCode Code.universal) (k := 2) (l := 1)
    (ys := (Nat.pair e x : ArityTuple 1)) (by simp [encode_nat]), NormalForm.evalTuple_ofDomCode]
  simp [NormalForm.oracle_eq_indicator Z]

/-- **Totality prefix boundary.** Relative to any oracle `Z`, no valid unary normal-form code with
prefix `qf`, `sigma 0`, `pi 0`, or `sigma 1` defines `totality Z`. -/
theorem not_exists_low_normalForm_totality (Z : Set ℕ) {p : QuantifierPrefix}
    (hp : p ∈ ({.qf, .sigma 0, .pi 0, .sigma 1} : Set QuantifierPrefix)) :
    ¬∃ c : NormalForm, c.pref = p ∧ c.arity = 1 ∧ c.Valid Z ∧
      ∀ e : ArityTuple 1, c.EvalTuple Z e ↔ e ∈ totality Z := by
  rintro ⟨c, hpref, har, hc, heq⟩
  refine not_isSigma_two_totality (Z := Z) ?_
  rcases hp with rfl | rfl | rfl | rfl
  · exact ((hc.isSigma_evalTuple (n := 0) (by simp [hpref]) har).of_eq heq).of_le (by omega)
  · exact ((hc.isSigma_evalTuple (n := 1) (by simp [hpref]) har).of_eq heq).succ
  · exact ((hc.isPi_evalTuple (n := 1) (by simp [hpref]) har).of_eq heq).sigma_succ
  · exact (hc.isSigma_evalTuple (n := 2) (by simp [hpref]) har).of_eq heq

/-- **Totality versus single halting queries.** No computable family `g : ℕ → NormalForm` of
`Z`-valid nullary `sigma 0` codes can decide `e ∈ totality Z`. -/
theorem not_exists_computable_sigma_zero_query_totality (Z : Set ℕ) :
    ¬∃ g : ℕ → NormalForm, Computable g ∧
      ∀ e, (g e).pref = .sigma 0 ∧ (g e).arity = 0 ∧ (g e).Valid Z ∧
        ((g e).EvalTuple Z (k := 0) () ↔ e ∈ totality Z) := by
  rintro ⟨g, hg, hspec⟩
  refine not_manyOneReducible_totality_jump (Z := Z) ⟨fun e => encode ((g e).jumpQuery 0),
    Computable.encode.comp (NormalForm.primrec₂_jumpQuery.to_comp.comp hg (Computable.const 0)),
    fun e => ?_⟩
  obtain ⟨hp, har, hv, hev⟩ := hspec e
  have hv0 : NormalForm.ValidAux Z (g e).matrix (g e).pref 0 := by
    simpa [har] using NormalForm.valid_iff_validAux.1 hv
  have hj : encode ((g e).jumpQuery 0) ∈ Z.jump ↔ (g e).HoldsCode Z 0 := by
    simpa [Set.mem_jump] using NormalForm.dom_eval_toDomCode_iff_of_validAux hp hv0
  exact ((by simpa [NormalForm.evalTuple_iff_holdsCode] using hev :
    (g e).HoldsCode Z 0 ↔ e ∈ totality Z)).symm.trans hj.symm

/-! ### Boundary example 2: Axiom/rule checking versus c.e. deductive closure -/

/-- A finitary inference system on `ℕ`-coded formulas. -/
@[ext]
structure InferenceSystem where
  /-- Boolean test for whether `x` is an axiom. -/
  isAxiom : ℕ → Bool
  /-- Boolean test for whether `x` follows in one step from the premise list `ps`. -/
  infer : List ℕ → ℕ → Bool

namespace InferenceSystem

/-- Inductive derivability in `S` from axioms by iterated finitary rule applications. -/
inductive Derivable (S : InferenceSystem) : ℕ → Prop
  | axiom_mem {x : ℕ} : S.isAxiom x = true → S.Derivable x
  | step {ps : List ℕ} {x : ℕ} :
      (∀ p ∈ ps, S.Derivable p) → S.infer ps x = true → S.Derivable x

/-- The deductive closure (set of theorems) of `S`. -/
def closure (S : InferenceSystem) : Set ℕ := {x | S.Derivable x}

@[simp] theorem mem_closure {S : InferenceSystem} {x : ℕ} : x ∈ S.closure ↔ S.Derivable x := Iff.rfl

/-- Every step `k < d.length` is either an axiom of `S` or follows by `S.infer` from conclusions
appearing in `d.take k`. -/
def ValidStepsList (S : InferenceSystem) (d : List (List ℕ × ℕ)) : Prop :=
  ∀ k < d.length,
    S.isAxiom (d.getD k ([], 0)).2 = true ∨
      ((∀ p ∈ (d.getD k ([], 0)).1, p ∈ (d.take k).map Prod.snd) ∧
        S.infer (d.getD k ([], 0)).1 (d.getD k ([], 0)).2 = true)

/-- `d` is a valid finite derivation of `x` in `S` if `S.ValidStepsList d` holds and `x` appears
among the conclusions of `d`. -/
def IsDerivation (S : InferenceSystem) (d : List (List ℕ × ℕ)) (x : ℕ) : Prop :=
  S.ValidStepsList d ∧ x ∈ d.map Prod.snd

private theorem validStepsList_append {S : InferenceSystem} {d₁ d₂ : List (List ℕ × ℕ)}
    (h₁ : S.ValidStepsList d₁) (h₂ : S.ValidStepsList d₂) :
    S.ValidStepsList (d₁ ++ d₂) := fun k hk => by
  rw [List.length_append] at hk
  by_cases hk₁ : k < d₁.length
  · simpa [List.getD_eq_getElem?_getD, List.getElem?_append_left hk₁,
      List.take_append_of_le_length (Nat.le_of_lt hk₁)] using h₁ k hk₁
  · have hle := Nat.le_of_not_lt hk₁
    have hget : (d₁ ++ d₂).getD k ([], 0) = d₂.getD (k - d₁.length) ([], 0) := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_append_right hle]
    rw [hget, List.take_append, List.map_append]
    exact (h₂ (k - d₁.length) (by omega)).imp id fun ⟨hp, hi⟩ =>
      ⟨fun p hp' => List.mem_append_right _ (hp p hp'), hi⟩

/-- Soundness and completeness of finite derivations for `S.closure`. -/
theorem exists_isDerivation_iff_mem_closure (S : InferenceSystem) (x : ℕ) :
    (∃ d, S.IsDerivation d x) ↔ x ∈ S.closure := by
  refine ⟨?_, ?_⟩
  · rintro ⟨d, hsteps, hxmem⟩
    have hall : ∀ k < d.length, S.Derivable (d.getD k ([], 0)).2 := fun k =>
      Nat.strongRecOn k fun k ih hk => (hsteps k hk).elim Derivable.axiom_mem fun ⟨hp, hinf⟩ =>
        Derivable.step (fun p hp_mem => by
          obtain ⟨st, hst, rfl⟩ := List.mem_map.1 (hp p hp_mem)
          obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hst
          have hik : i < k := by simpa [Nat.le_of_lt hk] using hi
          have hid : i < d.length := Nat.lt_trans hik hk
          simpa [List.getD_eq_getElem?_getD, hid] using ih i hik hid) hinf
    obtain ⟨st, hst, rfl⟩ := List.mem_map.1 hxmem
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hst
    simpa [List.getD_eq_getElem?_getD, hk] using hall k hk
  · intro hx; induction hx with
    | @axiom_mem y hy =>
      exact ⟨[([], y)], ⟨(fun | 0, _ => Or.inl hy | _ + 1, hk => nomatch hk), by simp⟩⟩
    | @step ps y _ hinf ih =>
      have hlist : ∀ l : List ℕ, (∀ p ∈ l, ∃ d, S.IsDerivation d p) →
          ∃ d, S.ValidStepsList d ∧ ∀ p ∈ l, p ∈ d.map Prod.snd := fun l => by
        induction l with
        | nil => exact fun _ => ⟨[], fun _ hk => absurd hk (Nat.not_lt_zero _), by simp⟩
        | cons p l ihl =>
          intro hl; obtain ⟨d₁, hs₁, hm₁⟩ := hl p List.mem_cons_self
          obtain ⟨d₂, hs₂, hm₂⟩ := ihl fun _ hq => hl _ (List.mem_cons_of_mem _ hq)
          exact ⟨d₁ ++ d₂, validStepsList_append hs₁ hs₂, fun _ hq =>
            (List.mem_cons.1 hq).elim (fun e => by simp [e, hm₁]) (fun hq' => by simp [hm₂ _ hq'])⟩
      obtain ⟨d, hds, hmem⟩ := hlist ps ih
      refine ⟨d ++ [(ps, y)], ⟨fun k hk => ?_, by simp⟩⟩
      rw [List.length_append, List.length_singleton] at hk
      rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk₁ | rfl
      · simpa [List.getD_eq_getElem?_getD, List.getElem?_append_left hk₁,
          List.take_append_of_le_length (Nat.le_of_lt hk₁)] using hds k hk₁
      · simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right (Nat.le_refl _),
          Nat.sub_self, List.getElem?_cons_zero, Option.getD_some, List.take_left]
        exact Or.inr ⟨hmem, hinf⟩

end InferenceSystem

/-! ### Uniform normal-form compiler for deductive closure -/

private def getDeriv (w : ℕ) : List (List ℕ × ℕ) := (decode (α := List (List ℕ × ℕ)) w).getD []
private theorem primrec_getDeriv : Primrec getDeriv := option_getD.comp Primrec.decode (const [])
private theorem primrec_derivStep : Primrec₂ fun (w k : ℕ) => (getDeriv w).getD k ([], 0) :=
  (list_getD ([], 0)).comp (primrec_getDeriv.comp fst) snd
private theorem primrecRel_mem_nat : PrimrecRel (· ∈ · : ℕ → List ℕ → Prop) :=
  ((PrimrecRel.exists_mem_list Primrec.eq).comp₂ Primrec₂.right Primrec₂.left).of_eq
    fun _ _ => by simp

private theorem primrec_dcPrems : Primrec fun t : ArityTuple 3 =>
    decide (∀ p ∈ ((getDeriv t.1.2).getD t.2 ([], 0)).1,
      p ∈ ((getDeriv t.1.2).take t.2).map Prod.snd) :=
  ((PrimrecRel.forall_mem_list primrecRel_mem_nat).comp
    (fst.comp (primrec_derivStep.comp (snd.comp fst) snd))
    (list_map (list_take.comp snd (primrec_getDeriv.comp (snd.comp fst)))
      (snd.comp snd).to₂)).decide
private theorem primrec_dcInf : Primrec (fun t : ArityTuple 3 =>
    ((encode ((getDeriv t.1.2).getD t.2 ([], 0)).1,
      ((getDeriv t.1.2).getD t.2 ([], 0)).2) : ArityTuple 2)) :=
  let hst := primrec_derivStep.comp (snd.comp fst) snd
  (Primrec.encode.comp (fst.comp hst)).pair (snd.comp hst)
private theorem primrec_dcAx : Primrec (fun t : ArityTuple 3 =>
    (((getDeriv t.1.2).getD t.2 ([], 0)).2 : ArityTuple 1)) :=
  snd.comp (primrec_derivStep.comp (snd.comp fst) snd)
private theorem primrec_dcAllS : Primrec (fun t : ArityTuple 2 =>
    ((t, (getDeriv t.2).length) : ArityTuple 3)) :=
  (Primrec.id.pair (list_length.comp (primrec_getDeriv.comp snd))).of_eq fun _ => rfl
private theorem primrec_dcHit : Primrec fun t : ArityTuple 2 =>
    decide (t.1 ∈ (getDeriv t.2).map Prod.snd) :=
  (primrecRel_mem_nat.comp fst (list_map (primrec_getDeriv.comp snd) (snd.comp snd).to₂)).decide

private noncomputable abbrev dcAllPremsCode : NormalForm := NormalForm.qfCode 3 primrec_dcPrems
private noncomputable abbrev dcHitCode : NormalForm := NormalForm.qfCode 2 primrec_dcHit

/-- Uniformly compile a unary `qf` normal-form code `axCode` for `S.isAxiom` and a binary `qf`
normal-form code `infCode` for `S.infer` into a unary `sigma 0` normal-form code for `S.closure`. -/
noncomputable def NormalForm.deductiveClosure (axCode infCode : NormalForm) : NormalForm :=
  let cInfStep := infCode.preimage 3 (NormalForm.mapCode 3 2 primrec_dcInf)
  let cAxStep := axCode.preimage 3 (NormalForm.mapCode 3 1 primrec_dcAx)
  let cStepOk := cAxStep.or (dcAllPremsCode.and cInfStep)
  let cAllSteps := cStepOk.forallLt.preimage 2 (NormalForm.mapCode 2 3 primrec_dcAllS)
  (cAllSteps.and dcHitCode).bindExists

theorem NormalForm.primrec₂_deductiveClosure : Primrec₂ NormalForm.deductiveClosure := by
  have hInf := primrec₃_preimage (α := NormalForm × NormalForm) snd (const 3)
    (const (NormalForm.mapCode 3 2 primrec_dcInf))
  have hAx := primrec₃_preimage (α := NormalForm × NormalForm) fst (const 3)
    (const (NormalForm.mapCode 3 1 primrec_dcAx))
  have hStep := primrec₂_or.comp hAx (primrec₂_and.comp (const dcAllPremsCode) hInf)
  have hAll := primrec₃_preimage (primrec_forallLt.comp hStep) (const 2)
    (const (NormalForm.mapCode 2 3 primrec_dcAllS))
  exact (primrec_bindExists.comp (primrec₂_and.comp hAll (const dcHitCode))).to₂

@[simp] theorem NormalForm.pref_deductiveClosure_of_qf {axCode infCode : NormalForm}
    (hax : axCode.pref = .qf) :
    (NormalForm.deductiveClosure axCode infCode).pref = .sigma 0 := by
  simp [NormalForm.deductiveClosure, hax]

@[simp] theorem NormalForm.arity_deductiveClosure (axCode infCode : NormalForm) :
    (NormalForm.deductiveClosure axCode infCode).arity = 1 := by simp [NormalForm.deductiveClosure]

/-- `NormalForm.deductiveClosure` produces a valid unary `sigma 0` normal-form code whose
`EvalTuple` computes `S.closure` from valid `qf` codes for `S.isAxiom` and `S.infer`. -/
theorem NormalForm.valid_and_evalTuple_deductiveClosure {Z : Set ℕ} {S : InferenceSystem}
    {axCode infCode : NormalForm} (haxv : axCode.Valid Z) (hinfv : infCode.Valid Z)
    (hax_pref : axCode.pref = .qf) (hinf_pref : infCode.pref = .qf)
    (hax_ar : axCode.arity = 1) (hinf_ar : infCode.arity = 2)
    (hax_eq : ∀ y : ArityTuple 1, axCode.EvalTuple Z y ↔ S.isAxiom y = true)
    (hinf_eq : ∀ (ps : List ℕ) (y : ℕ),
      infCode.EvalTuple Z (k := 2) (encode ps, y) ↔ S.infer ps y = true) :
    (NormalForm.deductiveClosure axCode infCode).Valid Z ∧
      ∀ x : ArityTuple 1, (NormalForm.deductiveClosure axCode infCode).EvalTuple Z x ↔
        x ∈ S.closure := by
  rcases axCode with ⟨pax, aax, max_⟩; rcases infCode with ⟨pinf, ainf, minf⟩
  dsimp only at hax_pref hinf_pref hax_ar hinf_ar; subst hax_pref hinf_pref hax_ar hinf_ar
  let infP := ({ pref := .qf, arity := 2, matrix := minf } : NormalForm).preimage 3
    (mapCode 3 2 primrec_dcInf)
  let axP := ({ pref := .qf, arity := 1, matrix := max_ } : NormalForm).preimage 3
    (mapCode 3 1 primrec_dcAx)
  let allS := (axP.or (dcAllPremsCode.and infP)).forallLt.preimage 2 (mapCode 2 3 primrec_dcAllS)
  have hvAllP : dcAllPremsCode.Valid Z := NormalForm.valid_qfCode primrec_dcPrems
  have hvInf := hinfv.preimage_of_forall (k := 3) (by simp)
    (NormalForm.exists_eval_mapCode Z.oracle 3 2 primrec_dcInf)
  have hvAx := haxv.preimage_of_forall (k := 3) (by simp)
    (NormalForm.exists_eval_mapCode Z.oracle 3 1 primrec_dcAx)
  have hvPInf := hvAllP.and hvInf (by simp) (by simp)
  have hvStep := hvAx.or hvPInf (by simp) (by simp)
  have hvAllS := hvStep.forallLt.preimage_of_forall (k := 2) (by simp)
    (NormalForm.exists_eval_mapCode Z.oracle 2 3 primrec_dcAllS)
  have hvHit : dcHitCode.Valid Z := NormalForm.valid_qfCode primrec_dcHit
  refine ⟨(hvAllS.and hvHit (by simp) (by simp)).bindExists, fun x => ?_⟩
  dsimp only [NormalForm.deductiveClosure]
  rw [NormalForm.evalTuple_bindExists (by simp) x, ← S.exists_isDerivation_iff_mem_closure x]
  have hbody (w : ℕ) :
      (allS.and dcHitCode).EvalTuple Z (k := 2) (x, w) ↔ S.IsDerivation (getDeriv w) x := by
    refine (hvAllS.evalTuple_and (k := 2) hvHit (by simp) (by simp) (by simp) (x, w)).trans
      (and_congr ?_
        ((NormalForm.evalTuple_qfCode (k := 2) primrec_dcHit (x, w)).trans decide_eq_true_iff))
    rw [NormalForm.evalTuple_preimage (k := 2) (l := 3)
        (NormalForm.eval_mapCode Z.oracle 2 3 primrec_dcAllS (x, w)),
      hvStep.evalTuple_forallLt (k := 2) (by simp) (x, w) (getDeriv w).length]
    refine forall_congr' fun k => imp_congr_right fun _ => ?_
    rw [hvAx.evalTuple_or (k := 3) hvPInf (by simp) (by simp) (by simp) ((x, w), k),
      NormalForm.evalTuple_preimage (k := 3) (l := 1)
        (NormalForm.eval_mapCode Z.oracle 3 1 primrec_dcAx ((x, w), k)),
      hax_eq (((getDeriv w).getD k ([], 0)).2)]
    refine or_congr_right ?_
    rw [hvAllP.evalTuple_and (k := 3) hvInf (by simp) (by simp) (by simp) ((x, w), k),
      NormalForm.evalTuple_preimage (k := 3) (l := 2)
        (NormalForm.eval_mapCode Z.oracle 3 2 primrec_dcInf ((x, w), k)),
      hinf_eq ((getDeriv w).getD k ([], 0)).1 ((getDeriv w).getD k ([], 0)).2]
    exact and_congr_left' <|
      (NormalForm.evalTuple_qfCode (k := 3) primrec_dcPrems ((x, w), k)).trans decide_eq_true_iff
  exact ⟨fun ⟨w, hw⟩ => ⟨getDeriv w, (hbody w).1 hw⟩,
    fun ⟨d, hd⟩ => ⟨encode d, (hbody (encode d)).2 (by simpa [getDeriv] using hd)⟩⟩

/-! ### Concrete inference system with decidable axiom/rule tests and undecidable closure -/

private def haltEmptyAt (s e : ℕ) : Bool :=
  (Code.evaln (fun z => ((List.range s).map (fun _ => 0))[z]?) s (ofNat Code e) e).isSome
private theorem primrec₂_haltEmptyAt : Primrec₂ haltEmptyAt :=
  option_isSome.comp <| Code.primrec_evaln_list.comp <|
    (list_map (list_range.comp fst) (const 0).to₂).pair <|
      fst.pair (((Primrec.ofNat Code).comp snd).pair snd)

/-- Concrete inference system whose single axiom is `0`, deriving `2 * (s + 1)` from `[2 * s]` and
`2 * e + 1` from `[2 * s]` when program `e` halts on `e` within fuel `s` against `∅`. -/
def haltingInferenceSystem : InferenceSystem where
  isAxiom x := x == 0
  infer ps x :=
    match ps with
    | [p] => if x % 2 = 0 then p + 2 == x else (p % 2 == 0) && haltEmptyAt (p / 2) (x / 2)
    | _ => false

theorem primrec_isAxiom_haltingInferenceSystem : Primrec haltingInferenceSystem.isAxiom :=
  Primrec.beq.comp .id (const 0)

theorem primrec₂_infer_haltingInferenceSystem : Primrec₂ haltingInferenceSystem.infer := by
  dsimp only [Primrec₂]
  have hp : Primrec fun q : List ℕ × ℕ => q.1.head?.getD 0 :=
    option_getD.comp (list_head?.comp fst) (const 0)
  have hsingle := Primrec.ite (Primrec.eq.comp (nat_mod.comp snd (const 2)) (const 0))
    (Primrec.beq.comp (nat_add.comp hp (const 2)) snd)
    (Primrec.and.comp (Primrec.beq.comp (nat_mod.comp hp (const 2)) (const 0))
      (primrec₂_haltEmptyAt.comp (nat_div.comp hp (const 2)) (nat_div.comp snd (const 2))))
  refine (Primrec.ite (Primrec.eq.comp (list_length.comp fst) (const 1))
    hsingle (const false)).of_eq fun ⟨ps, _⟩ => ?_
  rcases ps with _ | ⟨_, _ | ⟨_, _⟩⟩ <;> rfl

theorem odd_mem_closure_haltingInferenceSystem_iff (e : ℕ) :
    2 * e + 1 ∈ haltingInferenceSystem.closure ↔ e ∈ (∅ : Set ℕ).jump := by
  have heven : ∀ s, haltingInferenceSystem.Derivable (2 * s) := fun s => by
    induction s with
    | zero => exact .axiom_mem rfl
    | succ s ihs =>
      exact .step (ps := [2 * s]) (fun _ hp => List.mem_singleton.1 hp ▸ ihs)
        (by simp [haltingInferenceSystem, Nat.mul_mod_right]; omega)
  let O₀ : ℕ → ℕ := fun _ => 0
  have hO : (∅ : Set ℕ).oracle = (O₀ : ℕ →. ℕ) := funext fun _ => by simp [O₀]
  have hsound : ∀ {x}, haltingInferenceSystem.Derivable x →
      x % 2 = 0 ∨ x / 2 ∈ (∅ : Set ℕ).jump := by
    intro x hx; induction hx with
    | @axiom_mem y hy =>
      obtain rfl : y = 0 := (by simpa [haltingInferenceSystem] using hy); exact .inl rfl
    | @step ps y _ hinf _ =>
      by_cases hy2 : y % 2 = 0
      · exact Or.inl hy2
      · rcases ps with _ | ⟨p, _ | _⟩
        · nomatch hinf
        · have hh : p % 2 = 0 ∧ haltEmptyAt (p / 2) (y / 2) = true := by
            simpa [haltingInferenceSystem, hy2] using hinf
          obtain ⟨d, hd⟩ := Option.isSome_iff_exists.1 hh.2
          rw [Set.mem_jump, hO, Part.dom_iff_mem]
          exact Or.inr ⟨d.output, Code.mem_eval_iff_exists_evaln_range_map.2 ⟨p / 2, d, hd, rfl⟩⟩
        · nomatch hinf
  refine ⟨fun h => (hsound h).elim (fun hm => by omega) (fun hj => by
      rwa [show (2 * e + 1) / 2 = e by omega] at hj), fun he => ?_⟩
  rcases Part.dom_iff_mem.1 (by simpa [Set.mem_jump, hO] using he) with ⟨_, hmem⟩
  obtain ⟨s, d, hd, _⟩ := Code.mem_eval_iff_exists_evaln_range_map.1 hmem
  have hhalt : haltEmptyAt s e = true := by dsimp only [O₀] at hd; unfold haltEmptyAt; rw [hd]; rfl
  exact InferenceSystem.Derivable.step (ps := [2 * s])
    (fun _ hp => List.mem_singleton.1 hp ▸ heven s)
    (by simp [haltingInferenceSystem, show (2 * e + 1) % 2 = 1 by omega,
      show (2 * e + 1) / 2 = e by omega, Nat.mul_mod_right, hhalt])

/-- **Deductive closure boundary.** `haltingInferenceSystem` admits `∅`-valid `qf` codes for its
axiom and rule checks and hence a `∅`-valid `sigma 0` code for its closure, yet no `∅`-valid `qf`
code defines `haltingInferenceSystem.closure`. -/
theorem exists_sigma_zero_and_not_exists_qf_closure_haltingInferenceSystem :
    (∃ c : NormalForm, c.pref = .sigma 0 ∧ c.arity = 1 ∧ c.Valid ∅ ∧
      ∀ x : ArityTuple 1, c.EvalTuple ∅ x ↔ x ∈ haltingInferenceSystem.closure) ∧
    ¬∃ c : NormalForm, c.pref = .qf ∧ c.arity = 1 ∧ c.Valid ∅ ∧
      ∀ x : ArityTuple 1, c.EvalTuple ∅ x ↔ x ∈ haltingInferenceSystem.closure := by
  refine ⟨?_, ?_⟩
  · let axCode := NormalForm.qfCode 1 primrec_isAxiom_haltingInferenceSystem
    have hb_inf : Primrec fun t : ArityTuple 2 =>
        haltingInferenceSystem.infer ((decode (α := List ℕ) t.1).getD []) t.2 :=
      primrec₂_infer_haltingInferenceSystem.comp
        (option_getD.comp (Primrec.decode.comp fst) (const [])) snd
    let infCode := NormalForm.qfCode 2 hb_inf
    have h := NormalForm.valid_and_evalTuple_deductiveClosure (Z := ∅) (S := haltingInferenceSystem)
      (NormalForm.valid_qfCode primrec_isAxiom_haltingInferenceSystem)
      (NormalForm.valid_qfCode hb_inf) rfl rfl rfl rfl
      (NormalForm.evalTuple_qfCode primrec_isAxiom_haltingInferenceSystem)
      (fun ps y => (NormalForm.evalTuple_qfCode (k := 2) hb_inf (encode ps, y)).trans (by simp))
    exact ⟨NormalForm.deductiveClosure axCode infCode, NormalForm.pref_deductiveClosure_of_qf rfl,
      NormalForm.arity_deductiveClosure axCode infCode, h.1, h.2⟩
  · rintro ⟨c, hpref, har, hc, heq⟩
    have h0 : IsSigma ∅ 0 (· ∈ haltingInferenceSystem.closure) :=
      (hc.isSigma_evalTuple (n := 0) (by simp [hpref]) har).of_eq heq
    obtain ⟨b, hb, hbeq⟩ := isSigma_zero_iff.1
      ((h0.preimage Primrec.nat_double_succ.computableIn).of_eq
        odd_mem_closure_haltingInferenceSystem_iff)
    have hb_part : Partrec fun e : ℕ => Part.some (b e) :=
      hb.partrec_of_oracle fun g hg => by
        rw [Set.mem_singleton_iff.1 hg, Set.oracle_empty]; exact Partrec.const' 0
    exact (∅ : Set ℕ).not_computablePred_mem_jump
      ((Computable.computablePred (Partrec.of_eq_tot hb_part fun _ => Part.mem_some _)).of_eq hbeq)

end TauCeti.ArithmeticalHierarchy
