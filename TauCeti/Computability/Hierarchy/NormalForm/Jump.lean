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

This file connects displayed `NormalForm` codes at prefix `QuantifierPrefix.sigma 0` (representing
Σ⁰₁) uniformly to oracle-program domains and `Set.jump`, and establishes two concrete boundary
phenomena for normal-form compilation:

1. **Uniform Σ⁰₁ ↔ program-domain ↔ jump compilers.** `NormalForm.toDomCode` and
   `NormalForm.jumpQuery` compile any `sigma 0` normal-form code primitive recursively into an
   oracle program whose halting domain (respectively, `Z.jump` membership) coincides with
   `NormalForm.EvalTuple Z`. Conversely, `NormalForm.ofDomCode`, `NormalForm.ofDomQuery`, and
   `NormalForm.jumpNormalForm` compile program domains, individual halting queries, and `Z.jump`
   uniformly across all oracles `Z : Set ℕ` into valid `sigma 0` normal-form codes.
2. **Totality (`totality Z`) versus single halting queries.** Combining `ofDomCode`, `preimage`,
   and `bindForall` produces a single oracle-independent `pi 1` (Π⁰₂) normal-form code
   `totalityNormalForm` valid relative to every `Z : Set ℕ`. By contrast, for every `Z`, no valid
   unary normal-form code with prefix `qf`, `sigma 0`, `pi 0`, or `sigma 1` defines `totality Z`,
   and no computable family of valid nullary `sigma 0` codes compiles `e ∈ totality Z` into single
   halting queries.
3. **Decidable axiom/rule checking versus theoremhood (`InferenceSystem`).** Given an inference
   system `S` with quantifier-free (`qf`) codes for `S.isAxiom` and `S.infer`, the uniform compiler
   `NormalForm.deductiveClosure` produces a valid `sigma 0` (Σ⁰₁) normal-form code for `S.closure`
   by bounded-quantifier verification of finite derivations followed by `bindExists`. The concrete
   system `haltingInferenceSystem` has primitive-recursive (hence `∅`-valid `qf`) axiom and rule
   checks while its deductive closure computes `(∅ : Set ℕ).jump` on odd inputs and therefore
   admits no `∅`-valid `qf` normal-form code.

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

@[simp]
private theorem eval_primrecCode {g : ℕ → ℕ} (hg : Primrec g) (O : ℕ →. ℕ) (n : ℕ) :
    Code.eval O (primrecCode hg) n = Part.some (g n) := by
  have h := (Nat.Partrec.Code.exists_code.1 hg.to_comp.partrec).choose_spec
  simpa [primrecCode] using congrFun h n

private def defaultTuple : (k : ℕ) → ArityTuple k
  | 0 => ()
  | 1 => 0
  | k + 2 => (defaultTuple (k + 1), 0)

private noncomputable def qfCode (k : ℕ) {b : ArityTuple k → Bool} (hb : Primrec b) :
    NormalForm :=
  ⟨.qf, k, primrecCode <| Primrec.encode.comp <|
    hb.comp (option_getD.comp Primrec.decode (const (defaultTuple k)))⟩

private theorem valid_qfCode {Z : Set ℕ} {k : ℕ} {b : ArityTuple k → Bool} (hb : Primrec b) :
    (qfCode k hb).Valid Z := by
  rw [valid_iff_validAux]
  by_cases hk : k = 0 <;> simp [qfCode, hk, validDepth_zero]

private theorem evalTuple_qfCode {Z : Set ℕ} {k : ℕ} {b : ArityTuple k → Bool} (hb : Primrec b)
    (xs : ArityTuple k) :
    (qfCode k hb).EvalTuple Z xs ↔ b xs = true := by
  cases hbx : b xs <;> simp [qfCode, evalTuple_iff_holdsCode, encodek, hbx]

private noncomputable def mapCode (k₁ k₂ : ℕ) {f : ArityTuple k₁ → ArityTuple k₂}
    (hf : Primrec f) : Code :=
  primrecCode <| Primrec.encode.comp <|
    hf.comp (option_getD.comp Primrec.decode (const (defaultTuple k₁)))

private theorem exists_eval_mapCode (O : ℕ →. ℕ) {k₁ k₂ : ℕ} {f : ArityTuple k₁ → ArityTuple k₂}
    (hf : Primrec f) (a : ℕ) :
    ∃ b : ℕ, Code.eval O (mapCode k₁ k₂ hf) a = Part.some b :=
  ⟨_, eval_primrecCode _ O a⟩

private theorem eval_mapCode (O : ℕ →. ℕ) {k₁ k₂ : ℕ} {f : ArityTuple k₁ → ArityTuple k₂}
    (hf : Primrec f) (xs : ArityTuple k₁) :
    Code.eval O (mapCode k₁ k₂ hf) (encode xs) = Part.some (encode (f xs)) := by
  simp [mapCode, encodek]

/-! ### Uniform Σ⁰₁ ↔ oracle-program domain ↔ jump compilers -/

/-- Compile a `sigma 0` normal-form code into an oracle program searching for the least witness `y`
making its Boolean matrix evaluate to `true` (negated so `0 = encode false` signals success to
`Code.rfind'`). -/
def toDomCode (c : NormalForm) : Code :=
  .comp (.rfind' (.comp notBoolCode c.matrix)) (.pair idCode .zero)

/-- `toDomCode` is primitive recursive. -/
theorem primrec_toDomCode : Primrec toDomCode :=
  Code.primrec₂_comp.comp
    (Code.primrec_rfind'.comp (Code.primrec₂_comp.comp (const notBoolCode) primrec_matrix))
    (const (Code.pair idCode .zero))

/-- Compile a `sigma 0` normal-form code and an encoded tuple `a` into a program whose self-halting
membership `encode (c.jumpQuery a) ∈ Z.jump` tests `c.HoldsCode Z a`. -/
def jumpQuery (c : NormalForm) (a : ℕ) : Code :=
  .comp c.toDomCode (Nat.Partrec.Code.const a).toSingleOracleCode

/-- `jumpQuery` is primitive recursive in both the normal-form code and the encoded input. -/
theorem primrec₂_jumpQuery : Primrec₂ jumpQuery :=
  Code.primrec₂_comp.comp (primrec_toDomCode.comp fst)
    (Nat.Partrec.Code.primrec_toSingleOracleCode.comp
      (Nat.Partrec.Code.primrec_const.comp snd))

/-- `jumpQuery` is injective in its input parameter `a`. -/
theorem jumpQuery_injective_right (c : NormalForm) : Function.Injective c.jumpQuery := by
  intro a b h
  simp only [jumpQuery, Code.comp.injEq] at h
  exact Nat.Partrec.Code.const_inj (Nat.Partrec.Code.toSingleOracleCode_injective h.2)

@[simp]
theorem eval_jumpQuery (O : ℕ →. ℕ) (c : NormalForm) (a x : ℕ) :
    Code.eval O (c.jumpQuery a) x = Code.eval O c.toDomCode a := by
  simp [jumpQuery, Nat.Partrec.Code.eval_const, PFun.some_bind]

/-- On inputs where a `sigma 0` matrix is valid, `toDomCode` halts if and only if `HoldsCode`
holds. -/
theorem dom_eval_toDomCode_iff_of_validAux {Z : Set ℕ} {c : NormalForm} {a : ℕ}
    (hp : c.pref = .sigma 0) (hv : ValidAux Z c.matrix c.pref a) :
    (Code.eval Z.oracle c.toDomCode a).Dom ↔ c.HoldsCode Z a := by
  have hva : ∀ y, ValidDepth Z c.matrix 0 (Nat.pair a y) := by
    simpa [hp] using hv
  have hb : ∀ y, ∃ b : Bool,
      Code.eval Z.oracle c.matrix (Nat.pair a y) = Part.some (encode b) :=
    fun y => (validDepth_zero Z c.matrix (Nat.pair a y)).1 (hva y)
  choose b hbeq using hb
  let fb : ℕ →. Bool := fun y => Part.some (b y)
  have hrf : Code.eval Z.oracle c.toDomCode a = Nat.rfind fb := by
    have hpair : Code.eval Z.oracle (.pair idCode .zero) a = Part.some (Nat.pair a 0) := by
      simp [Seq.seq]
    rw [toDomCode, Code.eval_comp, hpair, PFun.some_bind, Code.eval_rfind']
    have hfun : (Nat.rfind fun n => (fun m => m = 0) <$>
        Code.eval Z.oracle (notBoolCode.comp c.matrix) (Nat.pair a (n + 0))) = Nat.rfind fb := by
      congr 1
      funext y
      rw [add_zero]
      cases hby : b y <;> simp [fb, hbeq y, hby, PFun.some_bind]
    rw [hfun]
    ext x
    simp
  rw [hrf, Nat.rfind_dom]
  simp only [fb, holdsCode_iff, hp, holdsAux_eq_holdsBlock, QuantifierPrefix.startsExists_sigma,
    QuantifierPrefix.depth_sigma, holdsBlock_true_succ, holdsBlock_zero]
  constructor
  · rintro ⟨y, hy, -⟩
    have hy' : b y = true := (Part.mem_some_iff.1 hy).symm
    refine ⟨y, ?_⟩
    rw [hbeq y, hy']
    exact Part.mem_some _
  · rintro ⟨y, hy⟩
    rw [hbeq y, Part.mem_some_iff, encode_inj] at hy
    exact ⟨y, Part.mem_some_iff.2 hy, fun _ => trivial⟩

/-- On valid `sigma 0` normal forms, `toDomCode` halts on `encode xs` exactly when `EvalTuple Z xs`
holds. -/
@[simp]
theorem Valid.dom_eval_toDomCode_iff {Z : Set ℕ} {c : NormalForm} (hc : c.Valid Z)
    (hp : c.pref = .sigma 0) (xs : ArityTuple c.arity) :
    (Code.eval Z.oracle c.toDomCode (encode xs)).Dom ↔ c.EvalTuple Z xs :=
  (dom_eval_toDomCode_iff_of_validAux hp ((valid_iff Z c).1 hc xs)).trans
    (evalTuple_iff_holdsCode Z c xs).symm

/-- On valid `sigma 0` normal forms, `encode (c.jumpQuery (encode xs)) ∈ Z.jump` holds if and only
if `c.EvalTuple Z xs` holds. -/
theorem Valid.encode_jumpQuery_mem_jump_iff {Z : Set ℕ} {c : NormalForm} (hc : c.Valid Z)
    (hp : c.pref = .sigma 0) (xs : ArityTuple c.arity) :
    encode (c.jumpQuery (encode xs)) ∈ Z.jump ↔ c.EvalTuple Z xs := by
  simpa [Set.mem_jump] using hc.dom_eval_toDomCode_iff hp xs

/-! ### Uniform bounded-halting matrix for `ofDomCode` -/

private noncomputable def oraclePrefixCode : Code :=
  let appendCode := primrecCode (g := fun m : ℕ =>
      encode (ofNat (List ℕ) m.unpair.1 ++ [m.unpair.2])) <|
    Primrec.encode.comp <| list_append.comp
      ((Primrec.ofNat (List ℕ)).comp (fst.comp Primrec.unpair))
      (list_cons.comp (snd.comp Primrec.unpair) (const []))
  .prec .zero (.comp appendCode (.pair (.comp .right .right) (.comp .oracle (.comp .left .right))))

private theorem eval_oraclePrefixCode (O : ℕ → ℕ) (a k : ℕ) :
    Code.eval (O : ℕ →. ℕ) oraclePrefixCode (Nat.pair a k) =
      Part.some (encode ((List.range k).map O)) := by
  induction k with
  | zero => simp [oraclePrefixCode]
  | succ k ih =>
    dsimp only [oraclePrefixCode] at ih ⊢
    rw [Code.eval_prec_succ, ih]
    simp [Seq.seq, List.range_succ]

private def boundedHaltBool (p : ℕ × ℕ × List ℕ) : Bool :=
  (Code.evaln (fun z => p.2.2[z]?) p.2.1 (ofNat Code p.1.unpair.1) p.1.unpair.2).isSome

private theorem primrec_boundedHaltBool : Primrec boundedHaltBool :=
  option_isSome.comp <| Code.primrec_evaln_list.comp <|
    (snd.comp snd).pair <| (fst.comp snd).pair <|
      ((Primrec.ofNat Code).comp (fst.comp (Primrec.unpair.comp fst))).pair
        (snd.comp (Primrec.unpair.comp fst))

private noncomputable def boundedHaltMatrix : Code :=
  let checkCode := primrecCode (g := fun m : ℕ =>
      encode (boundedHaltBool (m.unpair.1.unpair.1, m.unpair.1.unpair.2,
        ofNat (List ℕ) m.unpair.2))) <|
    Primrec.encode.comp <| primrec_boundedHaltBool.comp <|
      (fst.comp (Primrec.unpair.comp (fst.comp Primrec.unpair))).pair <|
        (snd.comp (Primrec.unpair.comp (fst.comp Primrec.unpair))).pair <|
          (Primrec.ofNat (List ℕ)).comp (snd.comp Primrec.unpair)
  .comp checkCode (.pair (.pair .left .right) oraclePrefixCode)

private theorem eval_boundedHaltMatrix (Z : Set ℕ) (e x k : ℕ) :
    Code.eval Z.oracle boundedHaltMatrix (Nat.pair (Nat.pair e x) k) =
      Part.some (encode (Code.evaln
        (fun z => ((List.range k).map (Z.indicator 1))[z]?) k (ofNat Code e) x).isSome) := by
  have hZ : Z.oracle = ((Z.indicator 1 : ℕ → ℕ) : ℕ →. ℕ) := funext fun n => by simp
  rw [hZ]
  simp [boundedHaltMatrix, boundedHaltBool, eval_oraclePrefixCode, Seq.seq]

/-- Uniformly compile an oracle program `c : Code` into a unary `sigma 0` normal-form code whose
predicate relative to every `Z : Set ℕ` is the halting domain `(Code.eval Z.oracle c ·).Dom`. -/
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

/-- `ofDomCode` is primitive recursive. -/
theorem primrec_ofDomCode : Primrec ofDomCode := by
  have hcst : Primrec fun c : Code =>
      (Nat.Partrec.Code.const (encode c)).toSingleOracleCode :=
    Nat.Partrec.Code.primrec_toSingleOracleCode.comp
      (Nat.Partrec.Code.primrec_const.comp Primrec.encode)
  have harg := Code.primrec₂_pair.comp
    (Code.primrec₂_pair.comp hcst (const Code.left)) (const Code.right)
  exact primrec₃_mk (const (QuantifierPrefix.sigma 0)) (const 1)
    (Code.primrec₂_comp.comp (const boundedHaltMatrix) harg)

/-- `ofDomQuery` is primitive recursive in `(c, x)`. -/
theorem primrec₂_ofDomQuery : Primrec₂ ofDomQuery :=
  primrec₃_preimage (primrec_ofDomCode.comp fst) (const 0)
    (Nat.Partrec.Code.primrec_toSingleOracleCode.comp
      (Nat.Partrec.Code.primrec_const.comp snd))

/-- `ofDomCode c` is semantically valid relative to every oracle `Z`. -/
theorem valid_ofDomCode (Z : Set ℕ) (c : Code) : (ofDomCode c).Valid Z := by
  rw [valid_iff_validAux]
  simp only [ofDomCode, Nat.one_ne_zero, ↓reduceIte, validAux_eq_validDepth,
    QuantifierPrefix.depth_sigma, validDepth_succ, validDepth_zero]
  intro x k
  have harg : Code.eval Z.oracle
      (.pair (.pair (Nat.Partrec.Code.const (encode c)).toSingleOracleCode .left) .right)
      (Nat.pair x k) = Part.some (Nat.pair (Nat.pair (encode c) x) k) := by
    simp [Seq.seq, Nat.Partrec.Code.eval_const]
  rw [Code.eval_comp, harg, PFun.some_bind, eval_boundedHaltMatrix]
  exact ⟨_, rfl⟩

/-- `ofDomCode c` evaluates on `x` to `(Code.eval Z.oracle c x).Dom`, uniformly in `Z`. -/
@[simp]
theorem evalTuple_ofDomCode (Z : Set ℕ) (c : Code) (x : ArityTuple 1) :
    (ofDomCode c).EvalTuple Z x ↔ (Code.eval Z.oracle c x).Dom := by
  have hZ : Z.oracle = ((Z.indicator 1 : ℕ → ℕ) : ℕ →. ℕ) := funext fun n => by simp
  have heval : ∀ k, Code.eval Z.oracle (ofDomCode c).matrix (Nat.pair x k) =
      Part.some (encode (Code.evaln
        (fun z => ((List.range k).map (Z.indicator 1))[z]?) k c x).isSome) := fun k => by
    have harg : Code.eval Z.oracle
        (.pair (.pair (Nat.Partrec.Code.const (encode c)).toSingleOracleCode .left) .right)
        (Nat.pair x k) = Part.some (Nat.pair (Nat.pair (encode c) x) k) := by
      simp [Seq.seq, Nat.Partrec.Code.eval_const]
    simpa [ofDomCode, harg, PFun.some_bind] using eval_boundedHaltMatrix Z (encode c) x k
  simp only [evalTuple_iff_holdsCode, holdsCode_iff, pref_ofDomCode, holdsAux_eq_holdsBlock,
    QuantifierPrefix.startsExists_sigma, QuantifierPrefix.depth_sigma, holdsBlock_true_succ,
    holdsBlock_zero, encode_nat, heval, Part.mem_some_iff, encode_inj]
  rw [hZ, Part.dom_iff_mem]
  simp only [Code.mem_eval_iff_exists_evaln_range_map, List.getElem?_map]
  exact ⟨fun ⟨k, h⟩ => by
      obtain ⟨d, hd⟩ := Option.isSome_iff_exists.1 h.symm
      exact ⟨d.output, k, d, hd, rfl⟩,
    fun ⟨_, k, d, hd, _⟩ => ⟨k, by rw [hd]; rfl⟩⟩

/-- `ofDomQuery c x` is semantically valid relative to every oracle `Z`. -/
theorem valid_ofDomQuery (Z : Set ℕ) (c : Code) (x : ℕ) : (ofDomQuery c x).Valid Z :=
  (valid_ofDomCode Z c).preimage_of_forall (by simp) fun _ =>
    ⟨x, by simp [Nat.Partrec.Code.eval_const]⟩

/-- `ofDomQuery c x` evaluates on `()` to `(Code.eval Z.oracle c x).Dom`. -/
@[simp]
theorem evalTuple_ofDomQuery (Z : Set ℕ) (c : Code) (x : ℕ) (u : ArityTuple 0) :
    (ofDomQuery c x).EvalTuple Z u ↔ (Code.eval Z.oracle c x).Dom := by
  have hev : Code.eval Z.oracle (Nat.Partrec.Code.const x).toSingleOracleCode (encode u) =
      Part.some (encode (x : ArityTuple 1)) := by
    simp [Nat.Partrec.Code.eval_const, encode_nat]
  exact (evalTuple_preimage (c := ofDomCode c) (k := 0) (l := 1) hev).trans
    (evalTuple_ofDomCode Z c x)

/-- `jumpNormalForm` is semantically valid relative to every oracle `Z`. -/
theorem valid_jumpNormalForm (Z : Set ℕ) : jumpNormalForm.Valid Z :=
  (valid_ofDomCode Z Code.universal).preimage_of_forall (by simp) fun a =>
    ⟨Nat.pair a a, by simp [Seq.seq]⟩

/-- `jumpNormalForm` evaluates on `e` to `e ∈ Z.jump`, uniformly in `Z`. -/
@[simp]
theorem evalTuple_jumpNormalForm (Z : Set ℕ) (e : ArityTuple 1) :
    jumpNormalForm.EvalTuple Z e ↔ e ∈ Z.jump := by
  have hev : Code.eval Z.oracle (.pair idCode idCode) (encode e) =
      Part.some (encode (Nat.pair e e : ArityTuple 1)) := by
    simp [Seq.seq, encode_nat]
  have hZ : Z.oracle = ((Z.indicator 1 : ℕ → ℕ) : ℕ →. ℕ) := funext fun n => by simp
  rw [jumpNormalForm, evalTuple_preimage (c := ofDomCode Code.universal) (k := 1) (l := 1) hev,
    evalTuple_ofDomCode, Set.mem_jump]
  simp [hZ]

end NormalForm

/-! ### Boundary example 1: `totality Z` versus single halting queries -/

/-- Oracle-independent unary `pi 1` (Π⁰₂) normal-form code representing `totality Z` relative to
every `Z : Set ℕ`, constructed via `NormalForm.ofDomCode`, `preimage`, and `bindForall`. -/
noncomputable def totalityNormalForm : NormalForm :=
  ((NormalForm.ofDomCode Code.universal).preimage 2 NormalForm.idCode).bindForall

@[simp] theorem pref_totalityNormalForm : totalityNormalForm.pref = .pi 1 := by
  simp [totalityNormalForm]
@[simp] theorem arity_totalityNormalForm : totalityNormalForm.arity = 1 := by
  simp [totalityNormalForm]

/-- `totalityNormalForm` is semantically valid relative to every oracle `Z`. -/
theorem valid_totalityNormalForm (Z : Set ℕ) : totalityNormalForm.Valid Z :=
  ((NormalForm.valid_ofDomCode Z Code.universal).preimage_of_forall (by simp) fun p =>
    ⟨p, NormalForm.eval_idCode Z.oracle p⟩).bindForall

/-- `totalityNormalForm` evaluates on `e` to `e ∈ totality Z` for every oracle `Z`. -/
@[simp]
theorem evalTuple_totalityNormalForm (Z : Set ℕ) (e : ArityTuple 1) :
    totalityNormalForm.EvalTuple Z e ↔ e ∈ totality Z := by
  have hinner := (NormalForm.valid_ofDomCode Z Code.universal).preimage_of_forall (k := 2)
    (f := NormalForm.idCode) (by simp) fun p => ⟨p, NormalForm.eval_idCode Z.oracle p⟩
  rw [totalityNormalForm, hinner.evalTuple_bindForall (by simp) e, mem_totality]
  refine forall_congr' fun x => ?_
  have hev : Code.eval Z.oracle NormalForm.idCode (encode (e.snoc x)) =
      Part.some (encode (Nat.pair e x : ArityTuple 1)) := by
    simp [encode_nat]
  have hZ : Z.oracle = ((Z.indicator 1 : ℕ → ℕ) : ℕ →. ℕ) := funext fun n => by simp
  rw [NormalForm.evalTuple_preimage (c := NormalForm.ofDomCode Code.universal)
      (k := 2) (l := 1) hev,
    NormalForm.evalTuple_ofDomCode]
  simp [hZ]

/-- **Totality prefix boundary.** Relative to any oracle `Z`, no valid unary normal-form code with
prefix `qf` (Δ⁰₀), `sigma 0` (Σ⁰₁), `pi 0` (Π⁰₁), or `sigma 1` (Σ⁰₂) defines `totality Z`. -/
theorem not_exists_low_normalForm_totality (Z : Set ℕ) {p : QuantifierPrefix}
    (hp : p ∈ ({.qf, .sigma 0, .pi 0, .sigma 1} : Set QuantifierPrefix)) :
    ¬∃ c : NormalForm, c.pref = p ∧ c.arity = 1 ∧ c.Valid Z ∧
      ∀ e : ArityTuple 1, c.EvalTuple Z e ↔ e ∈ totality Z := by
  rintro ⟨c, hpref, har, hc, heq⟩
  rcases hp with rfl | rfl | rfl | rfl
  · have h0 : IsSigma Z 0 (· ∈ totality Z) :=
      (hc.isSigma_evalTuple (n := 0) (by simp [hpref]) har).of_eq heq
    exact not_isSigma_two_totality (h0.of_le (by omega))
  · have h1 : IsSigma Z 1 (· ∈ totality Z) :=
      (hc.isSigma_evalTuple (n := 1) (by simp [hpref]) har).of_eq heq
    exact not_isSigma_two_totality h1.succ
  · have h1 : IsPi Z 1 (· ∈ totality Z) :=
      (hc.isPi_evalTuple (n := 1) (by simp [hpref]) har).of_eq heq
    exact not_isSigma_two_totality h1.sigma_succ
  · have h2 : IsSigma Z 2 (· ∈ totality Z) :=
      (hc.isSigma_evalTuple (n := 2) (by simp [hpref]) har).of_eq heq
    exact not_isSigma_two_totality h2

/-- **Totality versus single halting queries.** Unlike individual halting instances `(c, x)` —
which compile uniformly via `NormalForm.ofDomQuery` to valid nullary `sigma 0` codes and single
`Z.jump` queries — no computable family `g : ℕ → NormalForm` of `Z`-valid nullary `sigma 0` codes
can decide `e ∈ totality Z`. -/
theorem not_exists_computable_sigma_zero_query_totality (Z : Set ℕ) :
    ¬∃ g : ℕ → NormalForm, Computable g ∧
      ∀ e, (g e).pref = .sigma 0 ∧ (g e).arity = 0 ∧ (g e).Valid Z ∧
        ((g e).EvalTuple Z (k := 0) () ↔ e ∈ totality Z) := by
  rintro ⟨g, hg, hspec⟩
  refine not_manyOneReducible_totality_jump (Z := Z)
    ⟨fun e => encode ((g e).jumpQuery 0),
      Computable.encode.comp
        (NormalForm.primrec₂_jumpQuery.to_comp.comp hg (Computable.const 0)),
      fun e => ?_⟩
  obtain ⟨hp, har, hv, hev⟩ := hspec e
  have hv0 : NormalForm.ValidAux Z (g e).matrix (g e).pref 0 := by
    have hiff := NormalForm.valid_iff_validAux.1 hv
    simpa [har] using hiff
  have hj : encode ((g e).jumpQuery 0) ∈ Z.jump ↔ (g e).HoldsCode Z 0 := by
    simpa [Set.mem_jump] using NormalForm.dom_eval_toDomCode_iff_of_validAux hp hv0
  have hev0 : (g e).HoldsCode Z 0 ↔ e ∈ totality Z := by
    simpa [NormalForm.evalTuple_iff_holdsCode] using hev
  exact hev0.symm.trans hj.symm

/-! ### Boundary example 2: Axiom/rule checking versus c.e. deductive closure -/

/-- A finitary inference system on `ℕ`-coded formulas, specified by a Boolean axiom test `isAxiom`
and a Boolean one-step inference relation `infer` from a finite list of premises. -/
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
def closure (S : InferenceSystem) : Set ℕ :=
  {x | S.Derivable x}

@[simp]
theorem mem_closure {S : InferenceSystem} {x : ℕ} : x ∈ S.closure ↔ S.Derivable x := Iff.rfl

/-- Every step `k < d.length` is either an axiom of `S` or follows by `S.infer` from conclusions at
strictly earlier indices `i < k`. -/
def ValidStepsList (S : InferenceSystem) (d : List (List ℕ × ℕ)) : Prop :=
  ∀ k < d.length,
    S.isAxiom (d.getD k ([], 0)).2 = true ∨
      ((∀ j < (d.getD k ([], 0)).1.length, ∃ i < k,
          (d.getD i ([], 0)).2 = (d.getD k ([], 0)).1.getD j 0) ∧
        S.infer (d.getD k ([], 0)).1 (d.getD k ([], 0)).2 = true)

/-- `d` is a valid finite derivation of `x` in `S` if `S.ValidStepsList d` holds and `x` appears
among the conclusions of `d`. -/
def IsDerivation (S : InferenceSystem) (d : List (List ℕ × ℕ)) (x : ℕ) : Prop :=
  S.ValidStepsList d ∧ x ∈ d.map Prod.snd

private theorem validStepsList_append {S : InferenceSystem} {d₁ d₂ : List (List ℕ × ℕ)}
    (h₁ : S.ValidStepsList d₁) (h₂ : S.ValidStepsList d₂) :
    S.ValidStepsList (d₁ ++ d₂) := by
  intro k hk
  rw [List.length_append] at hk
  by_cases hk₁ : k < d₁.length
  · have hget : (d₁ ++ d₂).getD k ([], 0) = d₁.getD k ([], 0) := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hk₁]
    rw [hget]
    rcases h₁ k hk₁ with hax | ⟨hprems, hinf⟩
    · exact Or.inl hax
    · refine Or.inr ⟨fun j hj => ?_, hinf⟩
      obtain ⟨i, hik, hi⟩ := hprems j hj
      have hi₁ : i < d₁.length := Nat.lt_trans hik hk₁
      refine ⟨i, hik, ?_⟩
      simpa [List.getD_eq_getElem?_getD, List.getElem?_append_left hi₁] using hi
  · have hle : d₁.length ≤ k := Nat.le_of_not_lt hk₁
    have hk₂ : k - d₁.length < d₂.length := by omega
    have hget : (d₁ ++ d₂).getD k ([], 0) = d₂.getD (k - d₁.length) ([], 0) := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_append_right hle]
    rw [hget]
    rcases h₂ (k - d₁.length) hk₂ with hax | ⟨hprems, hinf⟩
    · exact Or.inl hax
    · refine Or.inr ⟨fun j hj => ?_, hinf⟩
      obtain ⟨i, hik, hi⟩ := hprems j hj
      refine ⟨d₁.length + i, by omega, ?_⟩
      have hle' : d₁.length ≤ d₁.length + i := Nat.le_add_right _ _
      simpa [List.getD_eq_getElem?_getD, List.getElem?_append_right hle'] using hi

/-- Soundness and completeness of finite derivations for `S.closure`. -/
theorem exists_isDerivation_iff_mem_closure (S : InferenceSystem) (x : ℕ) :
    (∃ d, S.IsDerivation d x) ↔ x ∈ S.closure := by
  constructor
  · rintro ⟨d, hsteps, hxmem⟩
    have hall : ∀ k, k < d.length → S.Derivable (d.getD k ([], 0)).2 := by
      intro k
      induction k using Nat.strong_induction_on with
      | _ k ih =>
        intro hk
        rcases hsteps k hk with hax | ⟨hprems, hinf⟩
        · exact Derivable.axiom_mem hax
        · refine Derivable.step (fun p hp => ?_) hinf
          obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hp
          obtain ⟨i, hik, hi⟩ := hprems j hj
          have hget : (d.getD k ([], 0)).1.getD j 0 = (d.getD k ([], 0)).1[j] := by
            rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]
          rw [← hget, ← hi]
          exact ih i hik (Nat.lt_trans hik hk)
    obtain ⟨st, hst, rfl⟩ := List.mem_map.1 hxmem
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hst
    have hget : d.getD k ([], 0) = d[k] := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some]
    have h := hall k hk
    rwa [hget] at h
  · intro hx
    induction hx with
    | @axiom_mem y hy =>
      exact ⟨[([], y)], ⟨fun k hk => by
        obtain rfl : k = 0 := by simpa using hk
        exact Or.inl hy, by simp⟩⟩
    | @step ps y _ hinf ih =>
      have hlist : ∀ l : List ℕ, (∀ p ∈ l, ∃ d, S.IsDerivation d p) →
          ∃ d, S.ValidStepsList d ∧ ∀ p ∈ l, p ∈ d.map Prod.snd := by
        intro l hl
        induction l with
        | nil => exact ⟨[], fun _ hk => absurd hk (Nat.not_lt_zero _), by simp⟩
        | cons p l ihl =>
          obtain ⟨d₁, hs₁, hm₁⟩ := hl p List.mem_cons_self
          obtain ⟨d₂, hs₂, hm₂⟩ := ihl fun q hq => hl q (List.mem_cons_of_mem _ hq)
          refine ⟨d₁ ++ d₂, validStepsList_append hs₁ hs₂, ?_⟩
          intro q hq
          rcases List.mem_cons.1 hq with rfl | hq
          · exact List.mem_map.2 <| let ⟨s, hs, he⟩ := List.mem_map.1 hm₁
              ⟨s, List.mem_append_left _ hs, he⟩
          · exact List.mem_map.2 <| let ⟨s, hs, he⟩ := List.mem_map.1 (hm₂ q hq)
              ⟨s, List.mem_append_right _ hs, he⟩
      obtain ⟨d, hds, hmem⟩ := hlist ps ih
      refine ⟨d ++ [(ps, y)], ⟨?_, by simp⟩⟩
      intro k hk
      rw [List.length_append, List.length_singleton] at hk
      rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk₁ | rfl
      · have hget : (d ++ [(ps, y)]).getD k ([], 0) = d.getD k ([], 0) := by
          simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hk₁]
        rw [hget]
        rcases hds k hk₁ with hax | ⟨hprems, hi'⟩
        · exact Or.inl hax
        · refine Or.inr ⟨fun j hj => ?_, hi'⟩
          obtain ⟨i, hik, hi⟩ := hprems j hj
          have hi₁ : i < d.length := Nat.lt_trans hik hk₁
          exact ⟨i, hik,
            by simpa [List.getD_eq_getElem?_getD, List.getElem?_append_left hi₁] using hi⟩
      · have hget : (d ++ [(ps, y)]).getD d.length ([], 0) = (ps, y) := by
          simp [List.getD_eq_getElem?_getD]
        rw [hget]
        refine Or.inr ⟨fun j hj => ?_, hinf⟩
        have hp_mem : ps[j] ∈ d.map Prod.snd := hmem ps[j] (List.getElem_mem hj)
        obtain ⟨st, hst, hsteq⟩ := List.mem_map.1 hp_mem
        obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hst
        refine ⟨i, hi, ?_⟩
        simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi,
          List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hj, hsteq]

end InferenceSystem

/-! ### Uniform normal-form compiler for deductive closure -/

private def getDeriv (w : ℕ) : List (List ℕ × ℕ) :=
  (decode (α := List (List ℕ × ℕ)) w).getD []

private theorem primrec_getDeriv : Primrec getDeriv :=
  option_getD.comp Primrec.decode (const [])

private theorem primrec_derivStep :
    Primrec₂ fun (w k : ℕ) => (getDeriv w).getD k ([], 0) :=
  (list_getD ([], 0)).comp (primrec_getDeriv.comp fst) snd

private theorem primrec_dcMatch : Primrec fun t : ArityTuple 5 =>
    (((getDeriv t.1.1.1.2).getD t.2 ([], 0)).2 ==
      ((getDeriv t.1.1.1.2).getD t.1.1.2 ([], 0)).1.getD t.1.2 0) := by
  have hw : Primrec fun t : ArityTuple 5 => t.1.1.1.2 := snd.comp (fst.comp (fst.comp fst))
  have hk : Primrec fun t : ArityTuple 5 => t.1.1.2 := snd.comp (fst.comp fst)
  have hj : Primrec fun t : ArityTuple 5 => t.1.2 := snd.comp fst
  have hi : Primrec fun t : ArityTuple 5 => t.2 := snd
  exact Primrec.beq.comp (snd.comp (primrec_derivStep.comp hw hi))
    ((list_getD 0).comp (fst.comp (primrec_derivStep.comp hw hk)) hj)

private theorem primrec_dcPrem : Primrec (fun t : ArityTuple 4 => ((t, t.1.2) : ArityTuple 5)) :=
  (Primrec.id.pair (snd.comp fst)).of_eq fun _ => rfl

private theorem primrec_dcAllP : Primrec (fun t : ArityTuple 3 =>
    ((t, ((getDeriv t.1.2).getD t.2 ([], 0)).1.length) : ArityTuple 4)) :=
  (Primrec.id.pair (list_length.comp (fst.comp (primrec_derivStep.comp (snd.comp fst) snd)))).of_eq
    fun _ => rfl

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
    let ys := (getDeriv t.2).map Prod.snd
    decide (ys.idxOf t.1 < ys.length) := by
  have hys : Primrec fun t : ArityTuple 2 => (getDeriv t.2).map Prod.snd :=
    list_map (primrec_getDeriv.comp snd) (snd.comp snd)
  have hx : Primrec fun t : ArityTuple 2 => t.1 := fst
  exact (PrimrecPred.decide (nat_lt.comp (list_idxOf.comp hx hys) (list_length.comp hys))).of_eq
    fun _ => rfl

private noncomputable def dcAllPremsCode : NormalForm :=
  (((NormalForm.qfCode 5 primrec_dcMatch).existsLt).preimage 4
    (NormalForm.mapCode 4 5 primrec_dcPrem)).forallLt.preimage 3
    (NormalForm.mapCode 3 4 primrec_dcAllP)

private noncomputable def dcHitCode : NormalForm :=
  NormalForm.qfCode 2 primrec_dcHit

/-- Uniformly compile a unary `qf` normal-form code `axCode` for `S.isAxiom` and a binary `qf`
normal-form code `infCode` for `S.infer` (on encoded premise lists) into a unary `sigma 0` (Σ⁰₁)
normal-form code for `S.closure`, using bounded quantifiers (`existsLt`, `forallLt`), Boolean
connectives (`and`, `or`), `preimage`, and one outer existential quantifier (`bindExists`). -/
noncomputable def NormalForm.deductiveClosure (axCode infCode : NormalForm) : NormalForm :=
  let cInfStep := infCode.preimage 3 (NormalForm.mapCode 3 2 primrec_dcInf)
  let cAxStep := axCode.preimage 3 (NormalForm.mapCode 3 1 primrec_dcAx)
  let cStepOk := cAxStep.or (dcAllPremsCode.and cInfStep)
  let cAllSteps := cStepOk.forallLt.preimage 2 (NormalForm.mapCode 2 3 primrec_dcAllS)
  (cAllSteps.and dcHitCode).bindExists

/-- `NormalForm.deductiveClosure` is primitive recursive in `(axCode, infCode)`. -/
theorem NormalForm.primrec₂_deductiveClosure : Primrec₂ NormalForm.deductiveClosure := by
  have hInf : Primrec fun p : NormalForm × NormalForm =>
      p.2.preimage 3 (NormalForm.mapCode 3 2 primrec_dcInf) :=
    primrec₃_preimage snd (const 3) (const (NormalForm.mapCode 3 2 primrec_dcInf))
  have hAx : Primrec fun p : NormalForm × NormalForm =>
      p.1.preimage 3 (NormalForm.mapCode 3 1 primrec_dcAx) :=
    primrec₃_preimage fst (const 3) (const (NormalForm.mapCode 3 1 primrec_dcAx))
  have hStep := primrec₂_or.comp hAx (primrec₂_and.comp (const dcAllPremsCode) hInf)
  have hAll := primrec₃_preimage (primrec_forallLt.comp hStep) (const 2)
    (const (NormalForm.mapCode 2 3 primrec_dcAllS))
  exact (primrec_bindExists.comp (primrec₂_and.comp hAll (const dcHitCode))).to₂

@[simp]
theorem NormalForm.pref_deductiveClosure_of_qf {axCode infCode : NormalForm}
    (hax : axCode.pref = .qf) :
    (NormalForm.deductiveClosure axCode infCode).pref = .sigma 0 := by
  simp [NormalForm.deductiveClosure, hax]

@[simp]
theorem NormalForm.arity_deductiveClosure (axCode infCode : NormalForm) :
    (NormalForm.deductiveClosure axCode infCode).arity = 1 := by
  simp [NormalForm.deductiveClosure, dcHitCode, NormalForm.qfCode]

/-- `NormalForm.deductiveClosure` produces a valid unary `sigma 0` normal-form code whose
`EvalTuple` computes `S.closure` whenever `qf` codes `axCode` and `infCode` validly compute
`S.isAxiom` and `S.infer`. -/
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
  rcases axCode with ⟨pax, aax, max_⟩
  rcases infCode with ⟨pinf, ainf, minf⟩
  dsimp only at hax_pref hinf_pref hax_ar hinf_ar
  subst hax_pref hinf_pref hax_ar hinf_ar
  have hvMatch : (NormalForm.qfCode 5 primrec_dcMatch).Valid Z :=
    NormalForm.valid_qfCode primrec_dcMatch
  have hvPrem : (((NormalForm.qfCode 5 primrec_dcMatch).existsLt).preimage 4
      (NormalForm.mapCode 4 5 primrec_dcPrem)).Valid Z :=
    hvMatch.existsLt.preimage_of_forall (by simp [NormalForm.qfCode])
      (NormalForm.exists_eval_mapCode Z.oracle primrec_dcPrem)
  have hvAllP : dcAllPremsCode.Valid Z :=
    hvPrem.forallLt.preimage_of_forall (by simp)
      (NormalForm.exists_eval_mapCode Z.oracle primrec_dcAllP)
  let cInfStep := (NormalForm.mk .qf 2 minf).preimage 3 (NormalForm.mapCode 3 2 primrec_dcInf)
  have hvInf : cInfStep.Valid Z :=
    hinfv.preimage_of_forall (by simp) (NormalForm.exists_eval_mapCode Z.oracle primrec_dcInf)
  let cAxStep := (NormalForm.mk .qf 1 max_).preimage 3 (NormalForm.mapCode 3 1 primrec_dcAx)
  have hvAx : cAxStep.Valid Z :=
    haxv.preimage_of_forall (by simp) (NormalForm.exists_eval_mapCode Z.oracle primrec_dcAx)
  have hvAllPAndInf : (dcAllPremsCode.and cInfStep).Valid Z :=
    hvAllP.and hvInf (by simp [dcAllPremsCode, NormalForm.qfCode, cInfStep])
      (by simp [dcAllPremsCode, cInfStep])
  let cStepOk := cAxStep.or (dcAllPremsCode.and cInfStep)
  have hvStep : cStepOk.Valid Z :=
    hvAx.or hvAllPAndInf (by simp [cAxStep, dcAllPremsCode, NormalForm.qfCode])
      (by simp [cAxStep, dcAllPremsCode])
  let cAllSteps := cStepOk.forallLt.preimage 2 (NormalForm.mapCode 2 3 primrec_dcAllS)
  have hvAllS : cAllSteps.Valid Z :=
    hvStep.forallLt.preimage_of_forall (by simp [cStepOk, cAxStep])
      (NormalForm.exists_eval_mapCode Z.oracle primrec_dcAllS)
  have hvHit : dcHitCode.Valid Z := NormalForm.valid_qfCode primrec_dcHit
  have hpAllP : dcAllPremsCode.pref = .qf := by simp [dcAllPremsCode, NormalForm.qfCode]
  have haAllP : dcAllPremsCode.arity = 3 := by simp [dcAllPremsCode]
  have hpInf : cInfStep.pref = .qf := by simp [cInfStep]
  have haInf : cInfStep.arity = 3 := by simp [cInfStep]
  have hpAx : cAxStep.pref = .qf := by simp [cAxStep]
  have haAx : cAxStep.arity = 3 := by simp [cAxStep]
  have hpStep : cStepOk.pref = .qf := by simp [cStepOk, hpAx]
  have haStep : cStepOk.arity = 3 := by simp [cStepOk, haAx]
  have hpAllS : cAllSteps.pref = .qf := by simp [cAllSteps, hpStep]
  have haAllS : cAllSteps.arity = 2 := by simp [cAllSteps]
  have hpHit : dcHitCode.pref = .qf := by simp [dcHitCode, NormalForm.qfCode]
  have haHit : dcHitCode.arity = 2 := by simp [dcHitCode, NormalForm.qfCode]
  have hvConj : (cAllSteps.and dcHitCode).Valid Z :=
    hvAllS.and hvHit (hpHit.trans hpAllS.symm) (haHit.trans haAllS.symm)
  refine ⟨hvConj.bindExists, fun x => ?_⟩
  dsimp only [NormalForm.deductiveClosure]
  rw [NormalForm.evalTuple_bindExists (by simp) x,
    ← S.exists_isDerivation_iff_mem_closure x]
  have hbody : ∀ w : ℕ, (cAllSteps.and dcHitCode).EvalTuple Z (k := 2) (x, w) ↔
      S.IsDerivation (getDeriv w) x := fun w => by
    rw [hvAllS.evalTuple_and (k := 2) hvHit (hpHit.trans hpAllS.symm) haAllS haHit (x, w)]
    dsimp only [InferenceSystem.IsDerivation, InferenceSystem.ValidStepsList]
    apply and_congr
    · rw [NormalForm.evalTuple_preimage (k := 2) (l := 3)
          (NormalForm.eval_mapCode Z.oracle primrec_dcAllS (x, w)),
        hvStep.evalTuple_forallLt (k := 2) haStep (x, w) (getDeriv w).length]
      refine forall_congr' fun k => imp_congr_right fun _ => ?_
      rw [hvAx.evalTuple_or (k := 3) hvAllPAndInf (by simp [hpAllP, hpAx])
          haAx (by simp [haAllP]) ((x, w), k),
        NormalForm.evalTuple_preimage (k := 3) (l := 1)
          (NormalForm.eval_mapCode Z.oracle primrec_dcAx ((x, w), k)),
        hax_eq (((getDeriv w).getD k ([], 0)).2)]
      apply or_congr_right
      rw [hvAllP.evalTuple_and (k := 3) hvInf (hpInf.trans hpAllP.symm)
          haAllP haInf ((x, w), k),
        NormalForm.evalTuple_preimage (k := 3) (l := 2)
          (NormalForm.eval_mapCode Z.oracle primrec_dcInf ((x, w), k)),
        hinf_eq ((getDeriv w).getD k ([], 0)).1 ((getDeriv w).getD k ([], 0)).2]
      apply and_congr_left'
      dsimp only [dcAllPremsCode]
      rw [NormalForm.evalTuple_preimage (k := 3) (l := 4)
          (NormalForm.eval_mapCode Z.oracle primrec_dcAllP ((x, w), k)),
        hvPrem.evalTuple_forallLt (k := 3) (by simp) ((x, w), k)
          ((getDeriv w).getD k ([], 0)).1.length]
      refine forall_congr' fun j => imp_congr_right fun _ => ?_
      rw [NormalForm.evalTuple_preimage (k := 4) (l := 5)
          (NormalForm.eval_mapCode Z.oracle primrec_dcPrem (((x, w), k), j)),
        hvMatch.evalTuple_existsLt (k := 4) (by simp [NormalForm.qfCode]) (((x, w), k), j) k]
      refine exists_congr fun i => and_congr_right fun _ => ?_
      rw [NormalForm.evalTuple_qfCode (k := 5) primrec_dcMatch ((((x, w), k), j), i), beq_iff_eq]
    · dsimp only [dcHitCode]
      rw [NormalForm.evalTuple_qfCode (k := 2) primrec_dcHit (x, w), decide_eq_true_eq,
        List.idxOf_lt_length_iff]
  constructor
  · rintro ⟨w, hw⟩
    exact ⟨getDeriv w, (hbody w).1 hw⟩
  · rintro ⟨d, hd⟩
    refine ⟨encode d, (hbody (encode d)).2 ?_⟩
    simpa [getDeriv] using hd

/-! ### Concrete inference system with decidable axiom/rule tests and undecidable closure -/

private def haltEmptyAt (s e : ℕ) : Bool :=
  (Code.evaln (fun z => ((List.range s).map (fun _ => 0))[z]?) s (ofNat Code e) e).isSome

private theorem primrec₂_haltEmptyAt : Primrec₂ haltEmptyAt :=
  option_isSome.comp <| Code.primrec_evaln_list.comp <|
    (list_map (list_range.comp fst) (const 0).to₂).pair <|
      fst.pair (((Primrec.ofNat Code).comp snd).pair snd)

/-- Concrete inference system whose single axiom is `0`, whose rules derive `2 * (s + 1)` from
`[2 * s]` and `2 * e + 1` from `[2 * s]` whenever program `e` halts on `e` within fuel `s` against
the empty oracle. Both `isAxiom` and `infer` are primitive recursive, while odd theorems encode the
halting set `(∅ : Set ℕ).jump`. -/
def haltingInferenceSystem : InferenceSystem where
  isAxiom x := x == 0
  infer ps x :=
    match ps with
    | [p] => if x % 2 = 0 then p + 2 == x else (p % 2 == 0) && haltEmptyAt (p / 2) (x / 2)
    | _ => false

/-- `haltingInferenceSystem.isAxiom` is primitive recursive. -/
theorem primrec_isAxiom_haltingInferenceSystem : Primrec haltingInferenceSystem.isAxiom :=
  Primrec.beq.comp .id (const 0)

/-- `haltingInferenceSystem.infer` is primitive recursive. -/
theorem primrec₂_infer_haltingInferenceSystem : Primrec₂ haltingInferenceSystem.infer := by
  dsimp only [Primrec₂]
  have hsingle : Primrec fun q : List ℕ × ℕ =>
      let p := q.1.head?.getD 0
      let x := q.2
      if x % 2 = 0 then p + 2 == x else (p % 2 == 0) && haltEmptyAt (p / 2) (x / 2) := by
    have hp : Primrec fun q : List ℕ × ℕ => q.1.head?.getD 0 :=
      option_getD.comp (list_head?.comp fst) (const 0)
    have hx : Primrec fun q : List ℕ × ℕ => q.2 := snd
    exact Primrec.ite (Primrec.eq.comp (nat_mod.comp hx (const 2)) (const 0))
      (Primrec.beq.comp (nat_add.comp hp (const 2)) hx)
      (Primrec.and.comp (Primrec.beq.comp (nat_mod.comp hp (const 2)) (const 0))
        (primrec₂_haltEmptyAt.comp (nat_div.comp hp (const 2)) (nat_div.comp hx (const 2))))
  refine (Primrec.ite (Primrec.eq.comp (list_length.comp fst) (const 1))
    hsingle (const false)).of_eq fun ⟨ps, x⟩ => ?_
  rcases ps with _ | ⟨p, _ | ⟨q, rest⟩⟩ <;> rfl

/-- On odd inputs `2 * e + 1`, membership in `haltingInferenceSystem.closure` coincides with
membership in `(∅ : Set ℕ).jump`. -/
theorem odd_mem_closure_haltingInferenceSystem_iff (e : ℕ) :
    2 * e + 1 ∈ haltingInferenceSystem.closure ↔ e ∈ (∅ : Set ℕ).jump := by
  have heven : ∀ s, haltingInferenceSystem.Derivable (2 * s) := by
    intro s
    induction s with
    | zero => exact .axiom_mem rfl
    | succ s ih =>
      refine .step (ps := [2 * s]) (fun p hp => ?_) ?_
      · rcases List.mem_singleton.1 hp with rfl; exact ih
      · have hmod : 2 * (s + 1) % 2 = 0 := by omega
        have hadd : (2 * s + 2 == 2 * (s + 1)) = true := by simp; omega
        simp [haltingInferenceSystem, hmod, hadd]
  let O₀ : ℕ → ℕ := fun _ => 0
  have hO : (∅ : Set ℕ).oracle = (O₀ : ℕ →. ℕ) := funext fun n => by simp [O₀]
  have hsound :
      ∀ {x}, haltingInferenceSystem.Derivable x → x % 2 = 0 ∨ x / 2 ∈ (∅ : Set ℕ).jump := by
    intro x hx
    induction hx with
    | @axiom_mem y hy =>
      have hy0 : y = 0 := by simpa [haltingInferenceSystem] using hy
      exact Or.inl (by simp [hy0])
    | @step ps y _ hinf _ =>
      by_cases hy2 : y % 2 = 0
      · exact Or.inl hy2
      · rcases ps with _ | ⟨p, _ | _⟩
        · simp [haltingInferenceSystem] at hinf
        · simp only [haltingInferenceSystem, hy2, ↓reduceIte, Bool.and_eq_true, beq_iff_eq] at hinf
          obtain ⟨_, hhalt⟩ := hinf
          dsimp only [haltEmptyAt] at hhalt
          obtain ⟨d, hd⟩ := Option.isSome_iff_exists.1 hhalt
          refine Or.inr ?_
          rw [Set.mem_jump, hO, Part.dom_iff_mem]
          exact ⟨d.output, Code.mem_eval_iff_exists_evaln_range_map.2 ⟨p / 2, d, hd, rfl⟩⟩
        · simp [haltingInferenceSystem] at hinf
  constructor
  · intro h
    rcases hsound h with hmod | hjump
    · omega
    · have hdiv : (2 * e + 1) / 2 = e := by omega
      rwa [hdiv] at hjump
  · intro he
    rw [Set.mem_jump, hO, Part.dom_iff_mem] at he
    obtain ⟨_, hmem⟩ := he
    obtain ⟨s, d, hd, _⟩ := Code.mem_eval_iff_exists_evaln_range_map.1 hmem
    refine InferenceSystem.Derivable.step (ps := [2 * s])
      (fun p hp => by rcases List.mem_singleton.1 hp with rfl; exact heven s) ?_
    have hodd : ¬(2 * e + 1) % 2 = 0 := by omega
    have hpeven : 2 * s % 2 = 0 := by omega
    have hsdiv : 2 * s / 2 = s := by omega
    have hediv : (2 * e + 1) / 2 = e := by omega
    dsimp only [O₀] at hd
    simp only [haltingInferenceSystem, hodd, ↓reduceIte, hpeven, hsdiv, hediv, haltEmptyAt,
      hd, beq_self_eq_true, Option.isSome_some, Bool.and_self]

/-- **Deductive closure boundary.** `haltingInferenceSystem` admits valid `qf` normal-form codes
relative to `∅` for both its axiom test and its rule check — and therefore a valid `sigma 0` (Σ⁰₁)
normal-form code for `haltingInferenceSystem.closure` via `NormalForm.deductiveClosure` — yet no
valid `qf` (Δ⁰₀ / decidable) normal-form code relative to `∅` defines
`haltingInferenceSystem.closure`. -/
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
    have h := NormalForm.valid_and_evalTuple_deductiveClosure (Z := ∅)
      (S := haltingInferenceSystem) (NormalForm.valid_qfCode primrec_isAxiom_haltingInferenceSystem)
      (NormalForm.valid_qfCode hb_inf) rfl rfl rfl rfl
      (fun y => NormalForm.evalTuple_qfCode primrec_isAxiom_haltingInferenceSystem y)
      (fun ps y => (NormalForm.evalTuple_qfCode (k := 2) hb_inf (encode ps, y)).trans (by simp))
    exact ⟨NormalForm.deductiveClosure axCode infCode,
      NormalForm.pref_deductiveClosure_of_qf rfl,
      NormalForm.arity_deductiveClosure axCode infCode, h.1, h.2⟩
  · rintro ⟨c, hpref, har, hc, heq⟩
    have h0 : IsSigma ∅ 0 (· ∈ haltingInferenceSystem.closure) :=
      (hc.isSigma_evalTuple (n := 0) (by simp [hpref]) har).of_eq heq
    have hf : Primrec fun e : ℕ => 2 * e + 1 :=
      nat_add.comp (nat_mul.comp (const 2) .id) (const 1)
    have hjump : IsSigma ∅ 0 (· ∈ (∅ : Set ℕ).jump) :=
      (h0.preimage hf.computableIn).of_eq odd_mem_closure_haltingInferenceSystem_iff
    obtain ⟨b, hb, hbeq⟩ := isSigma_zero_iff.1 hjump
    have hb_part : Partrec fun e : ℕ => Part.some (b e) :=
      hb.partrec_of_oracle fun g hg => by
        rw [Set.mem_singleton_iff.1 hg, Set.oracle_empty]
        exact Partrec.const' 0
    have hb_comp : Computable b := Partrec.of_eq_tot hb_part fun e => Part.mem_some _
    exact (∅ : Set ℕ).not_computablePred_mem_jump
      ((Computable.computablePred hb_comp).of_eq hbeq)

end TauCeti.ArithmeticalHierarchy
