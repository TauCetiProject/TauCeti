/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Computability.Hierarchy.NormalForm.Basic
import TauCeti.Data.PFun.Basic

/-!
# Uniform primitive-recursive compilers on displayed normal-form codes

This file constructs primitive-recursive code transformations on `NormalForm` preserving
`NormalForm.Valid` and implementing logical operations on `NormalForm.EvalTuple`: computable
preimages (`preimage`), dummy-quantifier level-raising (`toSigmaSucc`, `toPiSucc`, `raiseSigma`,
`raisePi`), contraction-aware variable binding (`bindExists`, `bindForall`), and prenex conjunction
and disjunction (`and`, `or`).

## References

* R. I. Soare, *Recursively Enumerable Sets and Degrees*, Springer, 1987, Chapter IV.1.
-/

public section

open Encodable Denumerable Primrec TauCeti.Oracle.Single

namespace TauCeti.ArithmeticalHierarchy.NormalForm

/-! ### Basic query-free combinators -/

/-- Query-free identity program `n ↦ Nat.pair n.unpair.1 n.unpair.2 = n`. -/
def idCode : Code := .pair .left .right
@[simp] theorem eval_idCode (O : ℕ →. ℕ) (n : ℕ) :
    Code.eval O idCode n = Part.some n := by simp [idCode, Seq.seq]

/-- Query-free Boolean conjunction program on `Nat.pair (encode b₁) (encode b₂)`. -/
def andBoolCode : Code := .prec .zero .left
@[simp] theorem eval_andBoolCode (O : ℕ →. ℕ) (b₁ b₂ : Bool) :
    Code.eval O andBoolCode (Nat.pair (encode b₁) (encode b₂)) = Part.some (encode (b₁ && b₂)) := by
  cases b₂; · simp [andBoolCode]
  change Code.eval O (.prec .zero .left) (Nat.pair (encode b₁) (0 + 1)) = _
  rw [Code.eval_prec_succ]; simp

/-- Query-free Boolean disjunction program on `Nat.pair (encode b₁) (encode b₂)`. -/
def orBoolCode : Code := .prec idCode (.comp .succ .zero)
@[simp] theorem eval_orBoolCode (O : ℕ →. ℕ) (b₁ b₂ : Bool) :
    Code.eval O orBoolCode (Nat.pair (encode b₁) (encode b₂)) = Part.some (encode (b₁ || b₂)) := by
  cases b₂; · simp [orBoolCode]
  change Code.eval O (.prec idCode (.comp .succ .zero)) (Nat.pair (encode b₁) (0 + 1)) = _
  rw [Code.eval_prec_succ]; simp

/-! ### Base-code lifting and computable preimages -/

/-- One step of lifting a base-code program across a bound quantifier:
`Nat.pair a y ↦ Nat.pair (f a) y`. -/
def stepLift (f : Code) : Code := .pair (.comp f .left) .right
theorem primrec_stepLift : Primrec stepLift :=
  Code.primrec₂_pair.comp (Code.primrec₂_comp.comp .id (const Code.left)) (const Code.right)

/-- Lift a base-code transformation `f` across `d` inner number quantifiers. -/
def liftBase (d : ℕ) (f : Code) : Code := stepLift^[d] f
@[simp] theorem liftBase_zero (f : Code) : liftBase 0 f = f := (rfl)
@[simp] theorem liftBase_succ (d : ℕ) (f : Code) :
    liftBase (d + 1) f = liftBase d (stepLift f) := (rfl)
theorem primrec₂_liftBase : Primrec₂ liftBase :=
  (nat_iterate fst snd (primrec_stepLift.comp snd).to₂).to₂

private theorem eval_stepLift {O : ℕ →. ℕ} {f : Code} {a b : ℕ}
    (hf : Code.eval O f a = Part.some b) (y : ℕ) :
    Code.eval O (stepLift f) (Nat.pair a y) = Part.some (Nat.pair b y) := by
  simp [stepLift, Seq.seq, hf]

/-- Precomposing a matrix with `liftBase d f` transfers `ValidDepth` along `f`. -/
theorem validDepth_comp_liftBase_iff {Z : Set ℕ} {m : Code} :
    ∀ {d : ℕ} {f : Code} {a b : ℕ}, Code.eval Z.oracle f a = Part.some b →
      (ValidDepth Z (.comp m (liftBase d f)) d a ↔ ValidDepth Z m d b)
  | 0, _, _, _, hf => by simp [hf, PFun.some_bind]
  | d + 1, _, _, _, hf => by
    simp only [liftBase_succ, validDepth_succ]
    exact forall_congr' fun y => validDepth_comp_liftBase_iff (eval_stepLift hf y)

/-- Precomposing a matrix with `liftBase d f` transfers `HoldsBlock` along `f`. -/
theorem holdsBlock_comp_liftBase_iff {Z : Set ℕ} {m : Code} :
    ∀ {d : ℕ} {ex : Bool} {f : Code} {a b : ℕ}, Code.eval Z.oracle f a = Part.some b →
      (HoldsBlock Z (.comp m (liftBase d f)) ex d a ↔ HoldsBlock Z m ex d b)
  | 0, _, _, _, _, hf => by simp [hf, PFun.some_bind]
  | d + 1, true, _, _, _, hf => by
    simp only [liftBase_succ, holdsBlock_true_succ]
    exact exists_congr fun y => holdsBlock_comp_liftBase_iff (ex := false) (eval_stepLift hf y)
  | d + 1, false, _, _, _, hf => by
    simp only [liftBase_succ, holdsBlock_false_succ]
    exact forall_congr' fun y => holdsBlock_comp_liftBase_iff (ex := true) (eval_stepLift hf y)

/-- Pull back a normal-form code `c` to free arity `k` along an oracle program `f` computing a map
on encoded free tuples. -/
def preimage (c : NormalForm) (k : ℕ) (f : Code) : NormalForm :=
  ⟨c.pref, k, .comp c.matrix (liftBase c.pref.depth f)⟩
@[simp] theorem pref_preimage (c : NormalForm) (k : ℕ) (f : Code) :
    (c.preimage k f).pref = c.pref := (rfl)
@[simp] theorem arity_preimage (c : NormalForm) (k : ℕ) (f : Code) :
    (c.preimage k f).arity = k := (rfl)
@[simp] theorem matrix_preimage (c : NormalForm) (k : ℕ) (f : Code) :
    (c.preimage k f).matrix = .comp c.matrix (liftBase c.pref.depth f) := (rfl)

theorem primrec₃_preimage {α : Type*} [Primcodable α] {c : α → NormalForm} {k : α → ℕ}
    {f : α → Code} (hc : Primrec c) (hk : Primrec k) (hf : Primrec f) :
    Primrec fun a => (c a).preimage (k a) (f a) :=
  primrec₃_mk (primrec_pref.comp hc) hk <|
    Code.primrec₂_comp.comp (primrec_matrix.comp hc)
      (primrec₂_liftBase.comp (QuantifierPrefix.primrec_depth.comp (primrec_pref.comp hc)) hf)

theorem Valid.preimage {Z : Set ℕ} {c : NormalForm} {k : ℕ} {f : Code} (hc : c.Valid Z)
    (hf : ∀ xs : ArityTuple k, ∃ ys : ArityTuple c.arity,
      Code.eval Z.oracle f (encode xs) = Part.some (encode ys)) :
    (c.preimage k f).Valid Z := by
  rw [valid_iff]; simp only [pref_preimage, matrix_preimage, validAux_eq_validDepth]
  intro xs; obtain ⟨ys, hys⟩ := hf xs
  exact (validDepth_comp_liftBase_iff hys).2 (by simpa using (valid_iff Z c).1 hc ys)

theorem Valid.preimage_of_forall {Z : Set ℕ} {c : NormalForm} {k : ℕ} {f : Code}
    (hc : c.Valid Z) (hpos : c.arity ≠ 0)
    (hf : ∀ a : ℕ, ∃ b : ℕ, Code.eval Z.oracle f a = Part.some b) :
    (c.preimage k f).Valid Z := by
  have hcv : ∀ b : ℕ, ValidDepth Z c.matrix c.pref.depth b := by
    simpa [hpos] using valid_iff_validAux.1 hc
  rw [valid_iff]; simp only [pref_preimage, matrix_preimage, validAux_eq_validDepth]
  intro xs; obtain ⟨b, hb⟩ := hf (encode xs); exact (validDepth_comp_liftBase_iff hb).2 (hcv b)

theorem evalTuple_preimage {Z : Set ℕ} {c : NormalForm} {k l : ℕ} {f : Code}
    {xs : ArityTuple k} {ys : ArityTuple l}
    (hf : Code.eval Z.oracle f (encode xs) = Part.some (encode ys)) :
    (c.preimage k f).EvalTuple Z xs ↔ c.EvalTuple Z ys := by
  simpa [evalTuple_iff_holdsCode] using holdsBlock_comp_liftBase_iff hf

/-! ### Dummy-quantifier insertion and level-raising compilers -/

private theorem validDepth_comp_left_iff {Z : Set ℕ} {m : Code} :
    ∀ {d a : ℕ}, ValidDepth Z (.comp m .left) (d + 1) a ↔ ValidDepth Z m d a
  | 0, _ => by simp [PFun.some_bind]
  | d + 1, a => (validDepth_succ Z _ (d + 1) a).trans <|
      (forall_congr' fun _ => validDepth_comp_left_iff).trans (validDepth_succ Z m d a).symm

private theorem holdsBlock_comp_left_iff {Z : Set ℕ} {m : Code} :
    ∀ {d : ℕ} {ex : Bool} {a : ℕ},
      HoldsBlock Z (.comp m .left) ex (d + 1) a ↔ HoldsBlock Z m ex d a
  | 0, true, _ | 0, false, _ => by simp [PFun.some_bind]
  | d + 1, true, _ => by
    simp only [holdsBlock_true_succ]
    exact exists_congr fun _ => holdsBlock_comp_left_iff (d := d) (ex := false)
  | d + 1, false, _ => by
    simp only [holdsBlock_false_succ]
    exact forall_congr' fun _ => holdsBlock_comp_left_iff (d := d) (ex := true)

private theorem validDepth_comp_liftBase_left_iff {Z : Set ℕ} {m : Code} (d a : ℕ) :
    ValidDepth Z (.comp m (liftBase d .left)) (d + 1) a ↔ ValidDepth Z m d a := by
  have step (y : ℕ) : ValidDepth Z (.comp m (liftBase d .left)) d (Nat.pair a y) ↔
      ValidDepth Z m d a := validDepth_comp_liftBase_iff (by simp)
  simp [step]

private theorem holdsBlock_comp_liftBase_left_iff {Z : Set ℕ} {m : Code} (ex : Bool) (d a : ℕ) :
    HoldsBlock Z (.comp m (liftBase d .left)) ex (d + 1) a ↔ HoldsBlock Z m (!ex) d a := by
  have step (b : Bool) (y : ℕ) : HoldsBlock Z (.comp m (liftBase d .left)) b d (Nat.pair a y) ↔
      HoldsBlock Z m b d a := holdsBlock_comp_liftBase_iff (by simp)
  cases ex <;> simp [step]

/-- Insert one dummy quantifier to turn `c` into an equivalent normal form of prefix
`sigmaOf (c.pref.depth + 1)`. -/
def toSigmaSucc (c : NormalForm) : NormalForm :=
  ⟨.sigma c.pref.depth, c.arity,
    match c.pref with
    | .pi n => .comp c.matrix (liftBase (n + 1) .left)
    | _ => .comp c.matrix .left⟩

/-- Insert one dummy quantifier to turn `c` into an equivalent normal form of prefix
`piOf (c.pref.depth + 1)`, defined dual to `toSigmaSucc`. -/
def toPiSucc (c : NormalForm) : NormalForm := c.not.toSigmaSucc.not

@[simp] theorem pref_toSigmaSucc (c : NormalForm) :
    c.toSigmaSucc.pref = .sigmaOf (c.pref.depth + 1) := by simp [toSigmaSucc]
@[simp] theorem arity_toSigmaSucc (c : NormalForm) : c.toSigmaSucc.arity = c.arity := (rfl)
@[simp] theorem pref_toPiSucc (c : NormalForm) : c.toPiSucc.pref = .piOf (c.pref.depth + 1) := by
  simp [toPiSucc]
@[simp] theorem arity_toPiSucc (c : NormalForm) : c.toPiSucc.arity = c.arity := by simp [toPiSucc]

theorem primrec_toSigmaSucc : Primrec toSigmaSucc := by
  have hm : Primrec fun c : NormalForm =>
      match c.pref with
      | .pi n => Code.comp c.matrix (liftBase (n + 1) .left)
      | _ => Code.comp c.matrix .left :=
    (QuantifierPrefix.primrec_casesOn primrec_pref
      (Code.primrec₂_comp.comp primrec_matrix (const Code.left))
      (Code.primrec₂_comp.comp (primrec_matrix.comp fst) (const Code.left)).to₂
      (Code.primrec₂_comp.comp (primrec_matrix.comp fst)
        (primrec₂_liftBase.comp (Primrec.succ.comp snd) (const Code.left))).to₂).of_eq
      fun c => by cases c.pref <;> rfl
  exact primrec₃_mk
    (QuantifierPrefix.primrec_sigma.comp (QuantifierPrefix.primrec_depth.comp primrec_pref))
    primrec_arity hm
theorem primrec_toPiSucc : Primrec toPiSucc :=
  primrec_not.comp (primrec_toSigmaSucc.comp primrec_not)

theorem Valid.toSigmaSucc {Z : Set ℕ} {c : NormalForm} (hc : c.Valid Z) :
    c.toSigmaSucc.Valid Z := by
  rcases c with ⟨_ | n | n, k, m⟩ <;> rw [valid_iff] at hc ⊢ <;>
    dsimp only [NormalForm.toSigmaSucc] at hc ⊢ <;> intro xs <;> have h := hc xs
  · simp only [validAux_eq_validDepth, QuantifierPrefix.depth_qf,
      QuantifierPrefix.depth_sigma] at h ⊢; exact validDepth_comp_left_iff.2 h
  · simp only [validAux_eq_validDepth, QuantifierPrefix.depth_sigma] at h ⊢
    exact validDepth_comp_left_iff.2 h
  · simp only [validAux_eq_validDepth, QuantifierPrefix.depth_pi,
      QuantifierPrefix.depth_sigma] at h ⊢
    exact (validDepth_comp_liftBase_left_iff (n + 1) (encode xs)).2 h
theorem Valid.toPiSucc {Z : Set ℕ} {c : NormalForm} (hc : c.Valid Z) : c.toPiSucc.Valid Z :=
  hc.not.toSigmaSucc.not

@[simp] theorem evalTuple_toSigmaSucc (Z : Set ℕ) (c : NormalForm) {k : ℕ} (xs : ArityTuple k) :
    c.toSigmaSucc.EvalTuple Z xs ↔ c.EvalTuple Z xs := by
  simp only [evalTuple_iff_holdsCode, holdsCode_iff, holdsAux_eq_holdsBlock]
  cases hp : c.pref with
  | qf => simp [toSigmaSucc, hp]
  | sigma n =>
    simpa [toSigmaSucc, hp] using
      holdsBlock_comp_left_iff (Z := Z) (m := c.matrix) (d := n + 1) (ex := true) (a := encode xs)
  | pi n =>
    simpa [toSigmaSucc, hp] using
      holdsBlock_comp_liftBase_left_iff (Z := Z) (m := c.matrix) true (n + 1) (encode xs)
@[simp] theorem Valid.evalTuple_toPiSucc {Z : Set ℕ} {c : NormalForm} {k : ℕ} (hc : c.Valid Z)
    (hk : c.arity = k) (xs : ArityTuple k) :
    c.toPiSucc.EvalTuple Z xs ↔ c.EvalTuple Z xs := by
  classical
  rw [NormalForm.toPiSucc, hc.not.toSigmaSucc.evalTuple_not (by simp [hk]) xs,
    evalTuple_toSigmaSucc Z c.not xs, hc.evalTuple_not hk xs, Classical.not_not]

/-- Uniformly raise `c` to prefix `sigmaOf m` whenever `c.pref = sigmaOf n` with `n ≤ m` or
`c.pref.depth < m`. -/
def raiseSigma (c : NormalForm) (m : ℕ) : NormalForm := toSigmaSucc^[m - c.pref.depth] c

/-- Uniformly raise `c` to prefix `piOf m` whenever `c.pref = piOf n` with `n ≤ m` or
`c.pref.depth < m`, defined dual to `raiseSigma`. -/
def raisePi (c : NormalForm) (m : ℕ) : NormalForm := (c.not.raiseSigma m).not

theorem primrec₂_raiseSigma : Primrec₂ raiseSigma :=
  (nat_iterate (nat_sub.comp snd (QuantifierPrefix.primrec_depth.comp (primrec_pref.comp fst)))
    fst (primrec_toSigmaSucc.comp snd).to₂).to₂
theorem primrec₂_raisePi : Primrec₂ raisePi :=
  (primrec_not.comp (primrec₂_raiseSigma.comp (primrec_not.comp fst) snd)).to₂

private theorem iterate_toSigmaSucc_props :
    ∀ (t : ℕ) (c : NormalForm),
      (toSigmaSucc^[t + 1] c).pref = .sigmaOf (c.pref.depth + t + 1) ∧
      (toSigmaSucc^[t] c).arity = c.arity ∧
      (∀ {Z}, c.Valid Z → (toSigmaSucc^[t] c).Valid Z) ∧
      (∀ (Z : Set ℕ) {k : ℕ} (xs : ArityTuple k),
        (toSigmaSucc^[t] c).EvalTuple Z xs ↔ c.EvalTuple Z xs)
  | 0, _ => ⟨by simp, rfl, id, fun _ {_} _ => Iff.rfl⟩
  | t + 1, c => by
    obtain ⟨hp, har, hv, hev⟩ := iterate_toSigmaSucc_props t c.toSigmaSucc
    refine ⟨?_, by simp [har], fun h => hv h.toSigmaSucc,
      fun Z {k} xs => (hev Z xs).trans (evalTuple_toSigmaSucc Z c xs)⟩
    rw [Function.iterate_succ_apply, hp]; congr 1
    simp only [pref_toSigmaSucc, QuantifierPrefix.depth_sigmaOf]; omega

@[simp] theorem arity_raiseSigma (c : NormalForm) (m : ℕ) : (c.raiseSigma m).arity = c.arity :=
  (iterate_toSigmaSucc_props (m - c.pref.depth) c).2.1
@[simp] theorem arity_raisePi (c : NormalForm) (m : ℕ) : (c.raisePi m).arity = c.arity := by
  simp [raisePi]
theorem pref_raiseSigma_of_depth_lt {m : ℕ} {c : NormalForm} (hlt : c.pref.depth < m) :
    (c.raiseSigma m).pref = .sigmaOf m := by
  obtain ⟨t, ht⟩ := Nat.exists_eq_add_of_lt hlt
  rw [raiseSigma, show m - c.pref.depth = t + 1 by omega, (iterate_toSigmaSucc_props t c).1]
  congr 1; omega
theorem pref_raiseSigma_of_sigmaOf {n m : ℕ} {c : NormalForm} (hp : c.pref = .sigmaOf n)
    (hnm : n ≤ m) : (c.raiseSigma m).pref = .sigmaOf m := by
  rcases Nat.eq_or_lt_of_le hnm with rfl | hlt
  · simp [raiseSigma, hp]
  · exact pref_raiseSigma_of_depth_lt (by simpa [hp] using hlt)
theorem pref_raisePi_of_piOf {n m : ℕ} {c : NormalForm} (hp : c.pref = .piOf n)
    (hnm : n ≤ m) : (c.raisePi m).pref = .piOf m := by
  simp [raisePi, pref_raiseSigma_of_sigmaOf (c := c.not) (by simp [hp]) hnm]
theorem pref_raisePi_of_depth_lt {m : ℕ} {c : NormalForm} (hlt : c.pref.depth < m) :
    (c.raisePi m).pref = .piOf m := by
  simp [raisePi, pref_raiseSigma_of_depth_lt (c := c.not) (by simpa using hlt)]
theorem Valid.raiseSigma {Z : Set ℕ} {c : NormalForm} (m : ℕ) (hc : c.Valid Z) :
    (c.raiseSigma m).Valid Z := (iterate_toSigmaSucc_props (m - c.pref.depth) c).2.2.1 hc
theorem Valid.raisePi {Z : Set ℕ} {c : NormalForm} (m : ℕ) (hc : c.Valid Z) :
    (c.raisePi m).Valid Z := (hc.not.raiseSigma m).not
@[simp] theorem evalTuple_raiseSigma (Z : Set ℕ) (c : NormalForm) (m : ℕ) {k : ℕ}
    (xs : ArityTuple k) : (c.raiseSigma m).EvalTuple Z xs ↔ c.EvalTuple Z xs :=
  (iterate_toSigmaSucc_props (m - c.pref.depth) c).2.2.2 Z xs
@[simp] theorem Valid.evalTuple_raisePi {Z : Set ℕ} {c : NormalForm} {m k : ℕ} (hc : c.Valid Z)
    (hk : c.arity = k) (xs : ArityTuple k) :
    (c.raisePi m).EvalTuple Z xs ↔ c.EvalTuple Z xs := by
  classical
  rw [NormalForm.raisePi, (hc.not.raiseSigma m).evalTuple_not (by simp [hk]) xs,
    evalTuple_raiseSigma Z c.not m xs, hc.evalTuple_not hk xs, Classical.not_not]

/-! ### Variable binding and quantifier contraction -/

private def reassocCode : Code := .pair (.pair .left (.comp .left .right)) (.comp .right .right)
@[simp] private theorem eval_reassocCode (O : ℕ →. ℕ) (a w : ℕ) :
    Code.eval O reassocCode (Nat.pair a w) =
      Part.some (Nat.pair (Nat.pair a w.unpair.1) w.unpair.2) := by simp [reassocCode, Seq.seq]

private def bindStep : QuantifierPrefix → Code → Code
  | .sigma n, m => .comp m (liftBase n reassocCode)
  | _, m => m

private theorem validAux_bindStep_iff {Z : Set ℕ} (p : QuantifierPrefix) (m : Code) (a : ℕ) :
    ValidAux Z (bindStep p m) p.addExists a ↔ ∀ y, ValidAux Z m p (Nat.pair a y) := by
  match p with
  | .qf | .pi _ => simp [bindStep]
  | .sigma n =>
    simp only [bindStep, validAux_eq_validDepth, QuantifierPrefix.addExists_sigma,
      QuantifierPrefix.depth_sigma, validDepth_succ]
    refine ⟨fun h y z => ?_, fun h w => (validDepth_comp_liftBase_iff
      (eval_reassocCode Z.oracle a w)).2 (h w.unpair.1 w.unpair.2)⟩
    simpa using (validDepth_comp_liftBase_iff
      (eval_reassocCode Z.oracle a (Nat.pair y z))).1 (h (Nat.pair y z))

private theorem holdsAux_bindStep_iff {Z : Set ℕ} (p : QuantifierPrefix) (m : Code) (a : ℕ) :
    HoldsAux Z (bindStep p m) p.addExists a ↔ ∃ y, HoldsAux Z m p (Nat.pair a y) := by
  match p with
  | .qf | .pi _ => simp [bindStep]
  | .sigma n =>
    simp only [bindStep, holdsAux_eq_holdsBlock, QuantifierPrefix.addExists_sigma,
      QuantifierPrefix.startsExists_sigma, QuantifierPrefix.depth_sigma, holdsBlock_true_succ]
    exact ⟨fun ⟨w, hw⟩ => ⟨w.unpair.1, w.unpair.2,
        (holdsBlock_comp_liftBase_iff (eval_reassocCode Z.oracle a w)).1 hw⟩,
      fun ⟨y, z, hyz⟩ => ⟨Nat.pair y z, (holdsBlock_comp_liftBase_iff
        (eval_reassocCode Z.oracle a (Nat.pair y z))).2 (by simpa using hyz)⟩⟩

/-- Bind the last free numerical variable of `c` (when `c.arity ≥ 1`) with an existential
quantifier, contracting adjacent existential quantifiers via `Nat.pair`. -/
def bindExists (c : NormalForm) : NormalForm :=
  if c.arity = 0 then c
  else
    let m := if c.arity = 1 then .comp c.matrix (liftBase c.pref.depth .right) else c.matrix
    ⟨c.pref.addExists, c.arity - 1, bindStep c.pref m⟩

/-- Bind the last free numerical variable of `c` (when `c.arity ≥ 1`) with a universal
quantifier, contracting adjacent universal quantifiers via De Morgan duality. -/
def bindForall (c : NormalForm) : NormalForm := if c.arity = 0 then c else c.not.bindExists.not

@[simp] theorem arity_bindExists (c : NormalForm) : c.bindExists.arity = c.arity - 1 := by
  by_cases h : c.arity = 0 <;> simp [bindExists, h]
@[simp] theorem pref_bindExists_of_pos {c : NormalForm} (h : 0 < c.arity) :
    c.bindExists.pref = c.pref.addExists := by simp [bindExists, Nat.ne_of_gt h]
@[simp] theorem arity_bindForall (c : NormalForm) : c.bindForall.arity = c.arity - 1 := by
  by_cases h : c.arity = 0 <;> simp [bindForall, h]
@[simp] theorem pref_bindForall_of_pos {c : NormalForm} (h : 0 < c.arity) :
    c.bindForall.pref = c.pref.addForall := by simp [bindForall, Nat.ne_of_gt h, h]

theorem primrec_bindExists : Primrec bindExists := by
  let mFn : NormalForm → Code := fun c =>
    if c.arity = 1 then .comp c.matrix (liftBase c.pref.depth .right) else c.matrix
  have hm : Primrec mFn := Primrec.ite (Primrec.eq.comp primrec_arity (const 1))
    (Code.primrec₂_comp.comp primrec_matrix
      (primrec₂_liftBase.comp (QuantifierPrefix.primrec_depth.comp primrec_pref)
        (const Code.right))) primrec_matrix
  have hstep : Primrec fun c : NormalForm => bindStep c.pref (mFn c) :=
    (QuantifierPrefix.primrec_casesOn primrec_pref hm
      (Code.primrec₂_comp.comp (hm.comp fst)
        (primrec₂_liftBase.comp snd (const reassocCode))).to₂
      (hm.comp fst).to₂).of_eq fun c => by cases c.pref <;> rfl
  exact Primrec.ite (Primrec.eq.comp primrec_arity (const 0)) .id <|
    primrec₃_mk (QuantifierPrefix.primrec_addExists.comp primrec_pref)
      (nat_sub.comp primrec_arity (const 1)) hstep
theorem primrec_bindForall : Primrec bindForall :=
  Primrec.ite (Primrec.eq.comp primrec_arity (const 0)) .id
    (primrec_not.comp (primrec_bindExists.comp primrec_not))

theorem Valid.bindExists {Z : Set ℕ} {c : NormalForm} (hc : c.Valid Z) : c.bindExists.Valid Z := by
  rcases c with ⟨p, _ | _ | k, m⟩
  · exact hc
  · change Valid Z ⟨p.addExists, 0, bindStep p (m.comp (liftBase p.depth .right))⟩
    rw [valid_iff] at hc ⊢; intro ⟨⟩
    rw [show encode () = 0 from rfl, validAux_bindStep_iff]; intro y
    have h := hc y; rw [validAux_eq_validDepth] at h ⊢
    exact (validDepth_comp_liftBase_iff (f := .right) (a := Nat.pair 0 y) (b := y) (by simp)).2 h
  · have hcv : ∀ b : ℕ, ValidAux Z m p b := by simpa using valid_iff_validAux.1 hc
    change Valid Z ⟨p.addExists, k + 1, bindStep p m⟩
    rw [valid_iff]; intro xs
    exact (validAux_bindStep_iff p m (encode xs)).2 fun y => hcv (Nat.pair (encode xs) y)

theorem evalTuple_bindExists {Z : Set ℕ} {c : NormalForm} {k : ℕ} (hk : c.arity = k + 1)
    (xs : ArityTuple k) :
    c.bindExists.EvalTuple Z xs ↔ ∃ y : ℕ, c.EvalTuple Z (ArityTuple.snoc xs y) := by
  rcases c with ⟨p, ar, m⟩; dsimp only at hk; subst ar
  rcases k with _ | k
  · cases xs; rw [evalTuple_iff_holdsCode, holdsCode_iff]
    change HoldsAux Z (bindStep p (m.comp (liftBase p.depth .right))) p.addExists (encode ()) ↔ _
    rw [holdsAux_bindStep_iff]; exact exists_congr fun y => by
      simpa [evalTuple_iff_holdsCode, ArityTuple.encode_snoc_zero] using
        holdsBlock_comp_liftBase_iff (Z := Z) (m := m) (f := .right)
          (a := Nat.pair (encode ()) y) (b := y) (by simp)
  · simpa [evalTuple_iff_holdsCode, bindExists] using holdsAux_bindStep_iff p m (encode xs)

theorem Valid.bindForall {Z : Set ℕ} {c : NormalForm} (hc : c.Valid Z) : c.bindForall.Valid Z := by
  by_cases h : c.arity = 0 <;> simp [NormalForm.bindForall, h, hc, hc.not.bindExists.not]

theorem Valid.evalTuple_bindForall {Z : Set ℕ} {c : NormalForm} {k : ℕ} (hc : c.Valid Z)
    (hk : c.arity = k + 1) (xs : ArityTuple k) :
    c.bindForall.EvalTuple Z xs ↔ ∀ y : ℕ, c.EvalTuple Z (ArityTuple.snoc xs y) := by
  classical
  rw [show c.bindForall = c.not.bindExists.not by simp [NormalForm.bindForall, hk],
    (hc.not.bindExists).evalTuple_not (by simp [hk]) xs,
    evalTuple_bindExists (by simpa using hk) xs, not_exists]
  exact forall_congr' fun y =>
    (not_congr (hc.evalTuple_not hk (ArityTuple.snoc xs y))).trans Classical.not_not

/-! ### Prenex conjunction and disjunction -/

private def stepMergeLeft (f : Code) : Code := .pair (.comp f .left) (.comp .left .right)
private def stepMergeRight (f : Code) : Code := .pair (.comp f .left) (.comp .right .right)
private theorem primrec₂_iterate_code {s : Code → Code} (hs : Primrec s) :
    Primrec₂ fun (d : ℕ) (f : Code) => s^[d] f :=
  (nat_iterate fst snd (hs.comp snd).to₂).to₂

/-- Prenex conjunction of two normal-form codes sharing `c₁.pref` and `c₁.arity`. -/
def and (c₁ c₂ : NormalForm) : NormalForm :=
  ⟨c₁.pref, c₁.arity, .comp andBoolCode
    (.pair (.comp c₁.matrix (stepMergeLeft^[c₁.pref.depth] idCode))
           (.comp c₂.matrix (stepMergeRight^[c₁.pref.depth] idCode)))⟩

/-- Prenex disjunction of two normal-form codes sharing `c₁.pref` and `c₁.arity`. -/
def or (c₁ c₂ : NormalForm) : NormalForm := (c₁.not.and c₂.not).not

@[simp] theorem pref_and (c₁ c₂ : NormalForm) : (c₁.and c₂).pref = c₁.pref := (rfl)
@[simp] theorem arity_and (c₁ c₂ : NormalForm) : (c₁.and c₂).arity = c₁.arity := (rfl)
@[simp] theorem pref_or (c₁ c₂ : NormalForm) : (c₁.or c₂).pref = c₁.pref := by simp [or]
@[simp] theorem arity_or (c₁ c₂ : NormalForm) : (c₁.or c₂).arity = c₁.arity := by simp [or]

theorem primrec₂_and : Primrec₂ and := by
  have hd : Primrec fun p : NormalForm × NormalForm => p.1.pref.depth :=
    QuantifierPrefix.primrec_depth.comp (primrec_pref.comp fst)
  have hside (r : Code) : Primrec fun p : NormalForm × NormalForm =>
      (fun f => Code.pair (.comp f .left) r)^[p.1.pref.depth] idCode :=
    (primrec₂_iterate_code (Code.primrec₂_pair.comp
      (Code.primrec₂_comp.comp .id (const Code.left)) (const r))).comp hd (const idCode)
  have hl := Code.primrec₂_comp.comp (primrec_matrix.comp fst) (hside (.comp .left .right))
  have hr := Code.primrec₂_comp.comp (primrec_matrix.comp snd) (hside (.comp .right .right))
  exact (primrec₃_mk (primrec_pref.comp fst) (primrec_arity.comp fst)
    (Code.primrec₂_comp.comp (const andBoolCode) (Code.primrec₂_pair.comp hl hr))).to₂
theorem primrec₂_or : Primrec₂ or :=
  (primrec_not.comp (primrec₂_and.comp (primrec_not.comp fst) (primrec_not.comp snd))).to₂

private theorem valid_and_holds_merge_and {Z : Set ℕ} {m₁ m₂ : Code} :
    ∀ {d : ℕ} {ex : Bool} {f₁ f₂ : Code} {b a₁ a₂ : ℕ},
      Code.eval Z.oracle f₁ b = Part.some a₁ →
      Code.eval Z.oracle f₂ b = Part.some a₂ →
      ValidDepth Z m₁ d a₁ → ValidDepth Z m₂ d a₂ →
      let M := .comp andBoolCode
        (.pair (.comp m₁ (stepMergeLeft^[d] f₁)) (.comp m₂ (stepMergeRight^[d] f₂)))
      ValidDepth Z M d b ∧
        (HoldsBlock Z M ex d b ↔ HoldsBlock Z m₁ ex d a₁ ∧ HoldsBlock Z m₂ ex d a₂)
  | 0, _, f₁, f₂, b, a₁, a₂, hf₁, hf₂, hv₁, hv₂ => by
    obtain ⟨b₁, hb₁⟩ := (validDepth_zero Z m₁ a₁).1 hv₁
    obtain ⟨b₂, hb₂⟩ := (validDepth_zero Z m₂ a₂).1 hv₂
    have heval : Code.eval Z.oracle (.comp andBoolCode (.pair (.comp m₁ f₁) (.comp m₂ f₂))) b =
        Part.some (encode (b₁ && b₂)) := by simp [Seq.seq, hf₁, hf₂, hb₁, hb₂, PFun.some_bind]
    refine ⟨(validDepth_zero Z _ b).2 ⟨b₁ && b₂, heval⟩, ?_⟩
    simp only [Function.iterate_zero, id_eq, holdsBlock_zero, heval, hb₁, hb₂]
    cases b₁ <;> cases b₂ <;> simp
  | d + 1, ex, f₁, f₂, b, a₁, a₂, hf₁, hf₂, hv₁, hv₂ => by
    have step (w : ℕ) := valid_and_holds_merge_and (d := d) (ex := !ex)
      (f₁ := stepMergeLeft f₁) (f₂ := stepMergeRight f₂) (b := Nat.pair b w)
      (by simp [stepMergeLeft, Seq.seq, hf₁]) (by simp [stepMergeRight, Seq.seq, hf₂])
      ((validDepth_succ Z m₁ d a₁).1 hv₁ w.unpair.1)
      ((validDepth_succ Z m₂ d a₂).1 hv₂ w.unpair.2)
    simp only [Function.iterate_succ_apply]
    refine ⟨(validDepth_succ Z _ d b).2 fun w => (step w).1, ?_⟩
    cases ex with
    | true =>
      simp only [holdsBlock_true_succ]
      exact ⟨fun ⟨w, hw⟩ =>
          let ⟨h₁, h₂⟩ := (step w).2.1 hw; ⟨⟨w.unpair.1, h₁⟩, ⟨w.unpair.2, h₂⟩⟩,
        fun ⟨⟨u, hu⟩, ⟨v, hv⟩⟩ =>
          ⟨Nat.pair u v, (step (Nat.pair u v)).2.2 (by simpa using ⟨hu, hv⟩)⟩⟩
    | false =>
      simp only [holdsBlock_false_succ]
      exact ⟨fun hw => ⟨fun u => by simpa using ((step (Nat.pair u 0)).2.1 (hw _)).1,
          fun v => by simpa using ((step (Nat.pair 0 v)).2.1 (hw _)).2⟩,
        fun ⟨hu, hv⟩ w => (step w).2.2 ⟨hu w.unpair.1, hv w.unpair.2⟩⟩

theorem Valid.and {Z : Set ℕ} {c₁ c₂ : NormalForm} (hc₁ : c₁.Valid Z) (hc₂ : c₂.Valid Z)
    (hp : c₂.pref = c₁.pref) (ha : c₂.arity = c₁.arity) : (c₁.and c₂).Valid Z := by
  rcases c₁ with ⟨p, k, m₁⟩; rcases c₂ with ⟨p₂, k₂, m₂⟩; dsimp only at hp ha; subst p₂ k₂
  rw [valid_iff] at hc₁ hc₂ ⊢; dsimp only [NormalForm.and] at hc₁ hc₂ ⊢; intro xs
  have h₁ := hc₁ xs; have h₂ := hc₂ xs; rw [validAux_eq_validDepth] at h₁ h₂ ⊢
  exact (valid_and_holds_merge_and (ex := p.startsExists) (eval_idCode Z.oracle _)
    (eval_idCode Z.oracle _) h₁ h₂).1
@[simp] theorem Valid.evalTuple_and {Z : Set ℕ} {c₁ c₂ : NormalForm} {k : ℕ} (hc₁ : c₁.Valid Z)
    (hc₂ : c₂.Valid Z) (hp : c₂.pref = c₁.pref) (ha₁ : c₁.arity = k) (ha₂ : c₂.arity = k)
    (xs : ArityTuple k) :
    (c₁.and c₂).EvalTuple Z xs ↔ c₁.EvalTuple Z xs ∧ c₂.EvalTuple Z xs := by
  rcases c₁ with ⟨p, k₁, m₁⟩; rcases c₂ with ⟨p₂, k₂, m₂⟩
  dsimp only at hp ha₁ ha₂; subst p₂ k₁ k₂
  simpa [NormalForm.and, evalTuple_iff_holdsCode] using
    (valid_and_holds_merge_and (ex := p.startsExists)
      (eval_idCode Z.oracle _) (eval_idCode Z.oracle _)
      (by simpa using (valid_iff Z _).1 hc₁ xs) (by simpa using (valid_iff Z _).1 hc₂ xs)).2
theorem Valid.or {Z : Set ℕ} {c₁ c₂ : NormalForm} (hc₁ : c₁.Valid Z) (hc₂ : c₂.Valid Z)
    (hp : c₂.pref = c₁.pref) (ha : c₂.arity = c₁.arity) : (c₁.or c₂).Valid Z :=
  (hc₁.not.and hc₂.not (by simp [hp]) (by simp [ha])).not
@[simp] theorem Valid.evalTuple_or {Z : Set ℕ} {c₁ c₂ : NormalForm} {k : ℕ} (hc₁ : c₁.Valid Z)
    (hc₂ : c₂.Valid Z) (hp : c₂.pref = c₁.pref) (ha₁ : c₁.arity = k) (ha₂ : c₂.arity = k)
    (xs : ArityTuple k) :
    (c₁.or c₂).EvalTuple Z xs ↔ c₁.EvalTuple Z xs ∨ c₂.EvalTuple Z xs := by
  classical
  have hand_v := hc₁.not.and hc₂.not (by simp [hp]) (by simp [ha₁, ha₂])
  rw [NormalForm.or, hand_v.evalTuple_not (by simp [ha₁]) xs,
    hc₁.not.evalTuple_and hc₂.not (by simp [hp]) (by simp [ha₁]) (by simp [ha₂]) xs,
    hc₁.evalTuple_not ha₁ xs, hc₂.evalTuple_not ha₂ xs]
  tauto

end TauCeti.ArithmeticalHierarchy.NormalForm
