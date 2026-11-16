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

Where `TauCeti.Computability.Hierarchy.Closure` proves that arithmetical pointclasses are closed
under preimage, Boolean connectives, level inclusions, and quantifier contraction, Post's theorem
and effective reductions require **uniform code transformations**: primitive-recursive maps
transforming `NormalForm` codes directly without consulting the oracle, while preserving
`NormalForm.Valid` and implementing the intended logical operation on `NormalForm.EvalTuple`.

All matrix transformations follow a structural accumulator pattern matching `NormalForm.ValidDepth`
and `NormalForm.HoldsBlock`: a base-code transformation `f : Code` is lifted across `d` alternating
number quantifiers by iterating `f ↦ .pair (.comp f .left) .right` (`NormalForm.liftBase`). Dual
operations (`toPiSucc`, `raisePi`, `bindForall`, `or`) factor through `NormalForm.not`:

* `NormalForm.preimage`: pull back free parameters along an oracle program computing a total map.
* `NormalForm.toSigmaSucc`, `NormalForm.toPiSucc`, `NormalForm.raiseSigma`, `NormalForm.raisePi`:
  insert dummy quantifiers to raise a normal-form code to higher existential or universal levels.
* `NormalForm.bindExists`, `NormalForm.bindForall`: bind the last free numerical variable and
  contract adjacent like quantifiers via `Nat.pair`.
* `NormalForm.and`, `NormalForm.or`: prenex conjunction and disjunction on matching prefix and
  arity.

Bounded number quantifiers (`existsLt`, `forallLt`, `existsLe`, `forallLe`) build on these
combinators in `TauCeti.Computability.Hierarchy.NormalForm.BoundedQuantifiers`.

## References

* R. I. Soare, *Recursively Enumerable Sets and Degrees*, Springer, 1987, Chapter IV.1.
-/

public section

open Encodable Denumerable Primrec TauCeti.Oracle.Single

namespace TauCeti.ArithmeticalHierarchy.NormalForm

/-! ### Basic query-free combinators -/

/-- Query-free identity program `n ↦ Nat.pair n.unpair.1 n.unpair.2 = n`. -/
def idCode : Code :=
  .pair .left .right

/-- `idCode` returns its input unchanged relative to every partial oracle. -/
@[simp]
theorem eval_idCode (O : ℕ →. ℕ) (n : ℕ) :
    Code.eval O idCode n = Part.some n := by
  simp [idCode, Seq.seq]

/-- Query-free Boolean conjunction program on `Nat.pair (encode b₁) (encode b₂)`. -/
def andBoolCode : Code :=
  .prec .zero .left

/-- `andBoolCode` computes `encode (b₁ && b₂)` on paired encoded Booleans. -/
@[simp]
theorem eval_andBoolCode (O : ℕ →. ℕ) (b₁ b₂ : Bool) :
    Code.eval O andBoolCode (Nat.pair (encode b₁) (encode b₂)) = Part.some (encode (b₁ && b₂)) := by
  cases b₂ with
  | false => simp [andBoolCode]
  | true =>
    change Code.eval O (.prec .zero .left) (Nat.pair (encode b₁) (0 + 1)) =
      Part.some (encode (b₁ && true))
    rw [Code.eval_prec_succ]
    simp

/-- Query-free Boolean disjunction program on `Nat.pair (encode b₁) (encode b₂)`. -/
def orBoolCode : Code :=
  .prec idCode (.comp .succ .zero)

/-- `orBoolCode` computes `encode (b₁ || b₂)` on paired encoded Booleans. -/
@[simp]
theorem eval_orBoolCode (O : ℕ →. ℕ) (b₁ b₂ : Bool) :
    Code.eval O orBoolCode (Nat.pair (encode b₁) (encode b₂)) = Part.some (encode (b₁ || b₂)) := by
  cases b₂ with
  | false => simp [orBoolCode]
  | true =>
    change Code.eval O (.prec idCode (.comp .succ .zero)) (Nat.pair (encode b₁) (0 + 1)) =
      Part.some (encode (b₁ || true))
    rw [Code.eval_prec_succ]
    simp

/-! ### Base-code lifting and computable preimages -/

/-- One step of lifting a base-code program across a bound quantifier: `Nat.pair a y ↦
Nat.pair (f a) y`. -/
def stepLift (f : Code) : Code :=
  .pair (.comp f .left) .right

/-- `stepLift` is primitive recursive. -/
theorem primrec_stepLift : Primrec stepLift :=
  Code.primrec₂_pair.comp (Code.primrec₂_comp.comp .id (const Code.left)) (const Code.right)

/-- Lift a base-code transformation `f` across `d` inner number quantifiers. -/
def liftBase (d : ℕ) (f : Code) : Code :=
  stepLift^[d] f

@[simp]
theorem liftBase_zero (f : Code) : liftBase 0 f = f :=
  (rfl)

@[simp]
theorem liftBase_succ (d : ℕ) (f : Code) : liftBase (d + 1) f = liftBase d (stepLift f) :=
  (rfl)

/-- `liftBase` is primitive recursive in the depth and program. -/
theorem primrec₂_liftBase : Primrec₂ liftBase :=
  (nat_iterate fst snd (primrec_stepLift.comp snd).to₂).to₂

private theorem eval_stepLift {O : ℕ →. ℕ} {f : Code} {a b : ℕ}
    (hf : Code.eval O f a = Part.some b) (y : ℕ) :
    Code.eval O (stepLift f) (Nat.pair a y) = Part.some (Nat.pair b y) := by
  simp [stepLift, Seq.seq, hf]

/-- Precomposing a matrix with `liftBase d f` transfers `ValidDepth` along `f`. -/
theorem validDepth_comp_liftBase_iff {Z : Set ℕ} {m : Code} :
    ∀ {d : ℕ} {f : Code} {a b : ℕ},
      Code.eval Z.oracle f a = Part.some b →
        (ValidDepth Z (.comp m (liftBase d f)) d a ↔ ValidDepth Z m d b)
  | 0, _, _, _, hf => by
    simp [hf, PFun.some_bind]
  | d + 1, _, _, _, hf => by
    simp only [liftBase_succ, validDepth_succ]
    exact forall_congr' fun y => validDepth_comp_liftBase_iff (eval_stepLift hf y)

/-- Precomposing a matrix with `liftBase d f` transfers `HoldsBlock` along `f`. -/
theorem holdsBlock_comp_liftBase_iff {Z : Set ℕ} {m : Code} :
    ∀ {d : ℕ} {ex : Bool} {f : Code} {a b : ℕ},
      Code.eval Z.oracle f a = Part.some b →
        (HoldsBlock Z (.comp m (liftBase d f)) ex d a ↔ HoldsBlock Z m ex d b)
  | 0, _, _, _, _, hf => by
    simp [hf, PFun.some_bind]
  | d + 1, true, _, _, _, hf => by
    simp only [liftBase_succ, holdsBlock_true_succ]
    exact exists_congr fun y => holdsBlock_comp_liftBase_iff (ex := false) (eval_stepLift hf y)
  | d + 1, false, _, _, _, hf => by
    simp only [liftBase_succ, holdsBlock_false_succ]
    exact forall_congr' fun y => holdsBlock_comp_liftBase_iff (ex := true) (eval_stepLift hf y)

/-- Pull back a normal-form code `c` to free arity `k` along an oracle program `f` computing a map
on encoded free tuples. -/
def preimage (c : NormalForm) (k : ℕ) (f : Code) : NormalForm where
  pref := c.pref
  arity := k
  matrix := .comp c.matrix (liftBase c.pref.depth f)

@[simp] theorem pref_preimage (c : NormalForm) (k : ℕ) (f : Code) :
    (c.preimage k f).pref = c.pref := (rfl)
@[simp] theorem arity_preimage (c : NormalForm) (k : ℕ) (f : Code) :
    (c.preimage k f).arity = k := (rfl)
@[simp] theorem matrix_preimage (c : NormalForm) (k : ℕ) (f : Code) :
    (c.preimage k f).matrix = .comp c.matrix (liftBase c.pref.depth f) := (rfl)

/-- `NormalForm.preimage` is primitive recursive in all three arguments. -/
theorem primrec₃_preimage {α : Type*} [Primcodable α] {c : α → NormalForm} {k : α → ℕ}
    {f : α → Code} (hc : Primrec c) (hk : Primrec k) (hf : Primrec f) :
    Primrec fun a => (c a).preimage (k a) (f a) :=
  primrec₃_mk (primrec_pref.comp hc) hk <|
    Code.primrec₂_comp.comp (primrec_matrix.comp hc)
      (primrec₂_liftBase.comp (QuantifierPrefix.primrec_depth.comp (primrec_pref.comp hc)) hf)

/-- Pulling back along a program that maps every `k`-tuple to some `c.arity`-tuple preserves
validity relative to `Z`. -/
theorem Valid.preimage {Z : Set ℕ} {c : NormalForm} {k : ℕ} {f : Code} (hc : c.Valid Z)
    (hf : ∀ xs : ArityTuple k, ∃ ys : ArityTuple c.arity,
      Code.eval Z.oracle f (encode xs) = Part.some (encode ys)) :
    (c.preimage k f).Valid Z := by
  rw [valid_iff]
  simp only [pref_preimage, matrix_preimage, validAux_eq_validDepth]
  intro xs
  obtain ⟨ys, hys⟩ := hf xs
  exact (validDepth_comp_liftBase_iff hys).2 (by simpa using (valid_iff Z c).1 hc ys)

/-- Pulling back a positive-arity valid normal form along any total `Z`-computable map on `ℕ`
preserves validity. -/
theorem Valid.preimage_of_forall {Z : Set ℕ} {c : NormalForm} {k : ℕ} {f : Code}
    (hc : c.Valid Z) (hpos : c.arity ≠ 0)
    (hf : ∀ a : ℕ, ∃ b : ℕ, Code.eval Z.oracle f a = Part.some b) :
    (c.preimage k f).Valid Z := by
  have hcv : ∀ b : ℕ, ValidDepth Z c.matrix c.pref.depth b := by
    have h := valid_iff_validAux.1 hc
    simpa [hpos] using h
  rw [valid_iff_validAux]
  simp only [arity_preimage, pref_preimage, matrix_preimage, validAux_eq_validDepth]
  split_ifs with hk0
  · obtain ⟨b, hb⟩ := hf 0
    exact (validDepth_comp_liftBase_iff hb).2 (hcv b)
  · intro a
    obtain ⟨b, hb⟩ := hf a
    exact (validDepth_comp_liftBase_iff hb).2 (hcv b)

/-- `preimage` evaluates on `xs` as `c` evaluates on the image tuple `ys`. -/
theorem evalTuple_preimage {Z : Set ℕ} {c : NormalForm} {k l : ℕ} {f : Code}
    {xs : ArityTuple k} {ys : ArityTuple l}
    (hf : Code.eval Z.oracle f (encode xs) = Part.some (encode ys)) :
    (c.preimage k f).EvalTuple Z xs ↔ c.EvalTuple Z ys := by
  simpa [evalTuple_iff_holdsCode] using holdsBlock_comp_liftBase_iff hf

/-! ### Dummy-quantifier insertion and level-raising compilers -/

private theorem validDepth_comp_left_iff {Z : Set ℕ} {m : Code} :
    ∀ {d a : ℕ}, ValidDepth Z (.comp m .left) (d + 1) a ↔ ValidDepth Z m d a
  | 0, a => by
    simp only [validDepth_succ, validDepth_zero, Code.eval_comp, Code.eval_left, Nat.unpair_pair,
      PFun.some_bind]
    exact ⟨fun h => h 0, fun h _ => h⟩
  | d + 1, a => by
    rw [validDepth_succ, validDepth_succ (m := m)]
    exact forall_congr' fun y => validDepth_comp_left_iff (d := d) (a := Nat.pair a y)

private theorem holdsBlock_comp_left_iff {Z : Set ℕ} {m : Code} :
    ∀ {d : ℕ} {ex : Bool} {a : ℕ},
      HoldsBlock Z (.comp m .left) ex (d + 1) a ↔ HoldsBlock Z m ex d a
  | 0, true, a => by
    simp only [holdsBlock_true_succ, holdsBlock_zero, Code.eval_comp, Code.eval_left,
      Nat.unpair_pair, PFun.some_bind]
    exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨0, h⟩⟩
  | 0, false, a => by
    simp only [holdsBlock_false_succ, holdsBlock_zero, Code.eval_comp, Code.eval_left,
      Nat.unpair_pair, PFun.some_bind]
    exact ⟨fun h => h 0, fun h _ => h⟩
  | d + 1, true, a => by
    simp only [holdsBlock_true_succ]
    exact exists_congr fun y => holdsBlock_comp_left_iff (d := d) (ex := false)
  | d + 1, false, a => by
    simp only [holdsBlock_false_succ]
    exact forall_congr' fun y => holdsBlock_comp_left_iff (d := d) (ex := true)

private theorem validDepth_comp_liftBase_left_iff {Z : Set ℕ} {m : Code} (d a : ℕ) :
    ValidDepth Z (.comp m (liftBase d .left)) (d + 1) a ↔ ValidDepth Z m d a := by
  rw [validDepth_succ]
  have step (y : ℕ) : ValidDepth Z (.comp m (liftBase d .left)) d (Nat.pair a y) ↔
      ValidDepth Z m d a :=
    validDepth_comp_liftBase_iff (by simp)
  simp only [step]
  exact ⟨fun h => h 0, fun h _ => h⟩

private theorem holdsBlock_comp_liftBase_left_iff {Z : Set ℕ} {m : Code} (ex : Bool) (d a : ℕ) :
    HoldsBlock Z (.comp m (liftBase d .left)) ex (d + 1) a ↔ HoldsBlock Z m (!ex) d a := by
  cases ex with
  | true =>
    rw [holdsBlock_true_succ, Bool.not_true]
    have step (y : ℕ) : HoldsBlock Z (.comp m (liftBase d .left)) false d (Nat.pair a y) ↔
        HoldsBlock Z m false d a :=
      holdsBlock_comp_liftBase_iff (by simp)
    simp only [step]
    exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨0, h⟩⟩
  | false =>
    rw [holdsBlock_false_succ, Bool.not_false]
    have step (y : ℕ) : HoldsBlock Z (.comp m (liftBase d .left)) true d (Nat.pair a y) ↔
        HoldsBlock Z m true d a :=
      holdsBlock_comp_liftBase_iff (by simp)
    simp only [step]
    exact ⟨fun h => h 0, fun h _ => h⟩

/-- Insert one dummy quantifier to turn `c` into an equivalent normal form of prefix
`sigma c.pref.depth = sigmaOf (c.pref.depth + 1)`. -/
def toSigmaSucc (c : NormalForm) : NormalForm :=
  match c.pref with
  | .qf => ⟨.sigma 0, c.arity, .comp c.matrix .left⟩
  | .sigma n => ⟨.sigma (n + 1), c.arity, .comp c.matrix .left⟩
  | .pi n => ⟨.sigma (n + 1), c.arity, .comp c.matrix (liftBase (n + 1) .left)⟩

/-- Insert one dummy quantifier to turn `c` into an equivalent normal form of prefix
`pi c.pref.depth = piOf (c.pref.depth + 1)`, defined dual to `toSigmaSucc`. -/
def toPiSucc (c : NormalForm) : NormalForm :=
  c.not.toSigmaSucc.not

@[simp]
theorem pref_toSigmaSucc (c : NormalForm) :
    c.toSigmaSucc.pref = .sigmaOf (c.pref.depth + 1) := by
  cases h : c.pref <;> simp [toSigmaSucc, h]

@[simp]
theorem arity_toSigmaSucc (c : NormalForm) : c.toSigmaSucc.arity = c.arity := by
  cases h : c.pref <;> simp [toSigmaSucc, h]

@[simp]
theorem pref_toPiSucc (c : NormalForm) :
    c.toPiSucc.pref = .piOf (c.pref.depth + 1) := by
  simp [toPiSucc]

@[simp]
theorem arity_toPiSucc (c : NormalForm) : c.toPiSucc.arity = c.arity := by
  simp [toPiSucc]

/-- `toSigmaSucc` is primitive recursive. -/
theorem primrec_toSigmaSucc : Primrec toSigmaSucc := by
  have hm : Primrec fun c : NormalForm =>
      QuantifierPrefix.casesOn (motive := fun _ => Code) c.pref
        (.comp c.matrix .left)
        (fun _ => .comp c.matrix .left)
        (fun n => .comp c.matrix (liftBase (n + 1) .left)) :=
    QuantifierPrefix.primrec_casesOn primrec_pref
      (Code.primrec₂_comp.comp primrec_matrix (const Code.left))
      (Code.primrec₂_comp.comp (primrec_matrix.comp fst) (const Code.left)).to₂
      (Code.primrec₂_comp.comp (primrec_matrix.comp fst)
        (primrec₂_liftBase.comp (Primrec.succ.comp snd) (const Code.left))).to₂
  refine (primrec₃_mk
    (QuantifierPrefix.primrec_sigma.comp (QuantifierPrefix.primrec_depth.comp primrec_pref))
    primrec_arity hm).of_eq fun c => ?_
  cases h : c.pref <;> simp [toSigmaSucc, h]

/-- `toPiSucc` is primitive recursive. -/
theorem primrec_toPiSucc : Primrec toPiSucc :=
  primrec_not.comp (primrec_toSigmaSucc.comp primrec_not)

/-- `toSigmaSucc` preserves semantic validity. -/
theorem Valid.toSigmaSucc {Z : Set ℕ} {c : NormalForm} (hc : c.Valid Z) :
    c.toSigmaSucc.Valid Z := by
  have step (a : ℕ) (ha : ValidAux Z c.matrix c.pref a) :
      ValidAux Z c.toSigmaSucc.matrix c.toSigmaSucc.pref a := by
    cases hp : c.pref with
    | qf =>
      have ha' : ValidDepth Z c.matrix 0 a := by simpa [hp] using ha
      simpa [NormalForm.toSigmaSucc, hp] using validDepth_comp_left_iff.2 ha'
    | sigma n =>
      have ha' : ValidDepth Z c.matrix (n + 1) a := by simpa [hp] using ha
      simpa [NormalForm.toSigmaSucc, hp] using validDepth_comp_left_iff.2 ha'
    | pi n =>
      have ha' : ValidDepth Z c.matrix (n + 1) a := by simpa [hp] using ha
      simpa [NormalForm.toSigmaSucc, hp] using (validDepth_comp_liftBase_left_iff (n + 1) a).2 ha'
  rw [valid_iff_validAux] at hc ⊢
  simp only [arity_toSigmaSucc]
  by_cases h0 : c.arity = 0
  · simp only [h0, ↓reduceIte] at hc ⊢
    exact step 0 hc
  · simp only [h0, ↓reduceIte] at hc ⊢
    exact fun a => step a (hc a)

/-- `toPiSucc` preserves semantic validity. -/
theorem Valid.toPiSucc {Z : Set ℕ} {c : NormalForm} (hc : c.Valid Z) :
    c.toPiSucc.Valid Z :=
  hc.not.toSigmaSucc.not

/-- `toSigmaSucc` preserves `EvalTuple` for every oracle and tuple. -/
@[simp]
theorem evalTuple_toSigmaSucc (Z : Set ℕ) (c : NormalForm) {k : ℕ} (xs : ArityTuple k) :
    c.toSigmaSucc.EvalTuple Z xs ↔ c.EvalTuple Z xs := by
  rw [evalTuple_iff_holdsCode, evalTuple_iff_holdsCode, holdsCode_iff, holdsCode_iff,
    holdsAux_eq_holdsBlock, holdsAux_eq_holdsBlock]
  cases hp : c.pref with
  | qf =>
    simp [toSigmaSucc, hp]
  | sigma n =>
    have h := holdsBlock_comp_left_iff (Z := Z) (m := c.matrix) (d := n + 1) (ex := true)
      (a := encode xs)
    simpa [toSigmaSucc, hp] using h
  | pi n =>
    have h := holdsBlock_comp_liftBase_left_iff (Z := Z) (m := c.matrix) true (n + 1) (encode xs)
    simpa [toSigmaSucc, hp] using h

/-- `toPiSucc` preserves `EvalTuple` on valid normal forms. -/
@[simp]
theorem Valid.evalTuple_toPiSucc {Z : Set ℕ} {c : NormalForm} {k : ℕ} (hc : c.Valid Z)
    (hk : c.arity = k) (xs : ArityTuple k) :
    c.toPiSucc.EvalTuple Z xs ↔ c.EvalTuple Z xs := by
  classical
  have h1 : c.not.toSigmaSucc.arity = k := by simp [hk]
  rw [NormalForm.toPiSucc, hc.not.toSigmaSucc.evalTuple_not h1 xs,
    evalTuple_toSigmaSucc Z c.not xs, hc.evalTuple_not hk xs, Classical.not_not]

/-- Uniformly raise `c` to prefix `sigmaOf m` whenever `c.pref = sigmaOf n` with `n ≤ m` or
`c.pref.depth < m`. -/
def raiseSigma (c : NormalForm) (m : ℕ) : NormalForm :=
  toSigmaSucc^[m - c.pref.depth] c

/-- Uniformly raise `c` to prefix `piOf m` whenever `c.pref = piOf n` with `n ≤ m` or
`c.pref.depth < m`, defined dual to `raiseSigma`. -/
def raisePi (c : NormalForm) (m : ℕ) : NormalForm :=
  (c.not.raiseSigma m).not

/-- `raiseSigma` is primitive recursive in the normal-form code and target level. -/
theorem primrec₂_raiseSigma : Primrec₂ raiseSigma :=
  (nat_iterate
    (nat_sub.comp snd (QuantifierPrefix.primrec_depth.comp (primrec_pref.comp fst)))
    fst (primrec_toSigmaSucc.comp snd).to₂).to₂

/-- `raisePi` is primitive recursive in the normal-form code and target level. -/
theorem primrec₂_raisePi : Primrec₂ raisePi :=
  (primrec_not.comp (primrec₂_raiseSigma.comp (primrec_not.comp fst) snd)).to₂

private theorem iterate_toSigmaSucc_props :
    ∀ (t : ℕ) (c : NormalForm),
      (toSigmaSucc^[t + 1] c).pref = .sigmaOf (c.pref.depth + t + 1) ∧
      (toSigmaSucc^[t] c).arity = c.arity ∧
      (∀ {Z}, c.Valid Z → (toSigmaSucc^[t] c).Valid Z) ∧
      (∀ (Z : Set ℕ) {k : ℕ} (xs : ArityTuple k),
        (toSigmaSucc^[t] c).EvalTuple Z xs ↔ c.EvalTuple Z xs)
  | 0, c => ⟨by simp, rfl, fun h => h, fun _ {_} _ => Iff.rfl⟩
  | t + 1, c => by
    obtain ⟨hp, har, hv, hev⟩ := iterate_toSigmaSucc_props t c.toSigmaSucc
    refine ⟨?_, ?_, fun h => hv h.toSigmaSucc,
      fun Z {k} xs => (hev Z xs).trans (evalTuple_toSigmaSucc Z c xs)⟩
    · rw [Function.iterate_succ_apply, hp]
      congr 1
      simp only [pref_toSigmaSucc, QuantifierPrefix.depth_sigmaOf]
      omega
    · simp [har]

@[simp]
theorem arity_raiseSigma (c : NormalForm) (m : ℕ) : (c.raiseSigma m).arity = c.arity :=
  (iterate_toSigmaSucc_props (m - c.pref.depth) c).2.1

@[simp]
theorem arity_raisePi (c : NormalForm) (m : ℕ) : (c.raisePi m).arity = c.arity := by
  simp [raisePi]

/-- `c.raiseSigma m` has prefix `sigmaOf m` when `c.pref = sigmaOf n` with `n ≤ m`. -/
theorem pref_raiseSigma_of_sigmaOf {n m : ℕ} {c : NormalForm} (hp : c.pref = .sigmaOf n)
    (hnm : n ≤ m) : (c.raiseSigma m).pref = .sigmaOf m := by
  rcases Nat.eq_or_lt_of_le hnm with rfl | hlt
  · simp [raiseSigma, hp]
  · obtain ⟨t, ht⟩ := Nat.exists_eq_add_of_lt hlt
    have hsub : m - c.pref.depth = t + 1 := by simp [hp]; omega
    rw [raiseSigma, hsub, (iterate_toSigmaSucc_props t c).1]
    congr 1
    simp [hp]
    omega

/-- `c.raiseSigma m` has prefix `sigmaOf m` whenever `c.pref.depth < m` (in particular for
`piOf n` with `n < m`). -/
theorem pref_raiseSigma_of_depth_lt {m : ℕ} {c : NormalForm} (hlt : c.pref.depth < m) :
    (c.raiseSigma m).pref = .sigmaOf m := by
  obtain ⟨t, ht⟩ := Nat.exists_eq_add_of_lt hlt
  have hsub : m - c.pref.depth = t + 1 := by omega
  rw [raiseSigma, hsub, (iterate_toSigmaSucc_props t c).1]
  congr 1
  omega

/-- `c.raisePi m` has prefix `piOf m` when `c.pref = piOf n` with `n ≤ m`. -/
theorem pref_raisePi_of_piOf {n m : ℕ} {c : NormalForm} (hp : c.pref = .piOf n)
    (hnm : n ≤ m) : (c.raisePi m).pref = .piOf m := by
  have hp' : c.not.pref = .sigmaOf n := by simp [hp]
  simp [raisePi, pref_raiseSigma_of_sigmaOf hp' hnm]

/-- `c.raisePi m` has prefix `piOf m` whenever `c.pref.depth < m` (in particular for `sigmaOf n`
with `n < m`). -/
theorem pref_raisePi_of_depth_lt {m : ℕ} {c : NormalForm} (hlt : c.pref.depth < m) :
    (c.raisePi m).pref = .piOf m := by
  have hlt' : c.not.pref.depth < m := by simpa using hlt
  simp [raisePi, pref_raiseSigma_of_depth_lt hlt']

/-- `raiseSigma` preserves semantic validity. -/
theorem Valid.raiseSigma {Z : Set ℕ} {c : NormalForm} (m : ℕ) (hc : c.Valid Z) :
    (c.raiseSigma m).Valid Z :=
  (iterate_toSigmaSucc_props (m - c.pref.depth) c).2.2.1 hc

/-- `raisePi` preserves semantic validity. -/
theorem Valid.raisePi {Z : Set ℕ} {c : NormalForm} (m : ℕ) (hc : c.Valid Z) :
    (c.raisePi m).Valid Z :=
  (hc.not.raiseSigma m).not

/-- `raiseSigma` preserves `EvalTuple`. -/
@[simp]
theorem evalTuple_raiseSigma (Z : Set ℕ) (c : NormalForm) (m : ℕ) {k : ℕ} (xs : ArityTuple k) :
    (c.raiseSigma m).EvalTuple Z xs ↔ c.EvalTuple Z xs :=
  (iterate_toSigmaSucc_props (m - c.pref.depth) c).2.2.2 Z xs

/-- `raisePi` preserves `EvalTuple` on valid normal forms. -/
@[simp]
theorem Valid.evalTuple_raisePi {Z : Set ℕ} {c : NormalForm} {m k : ℕ} (hc : c.Valid Z)
    (hk : c.arity = k) (xs : ArityTuple k) :
    (c.raisePi m).EvalTuple Z xs ↔ c.EvalTuple Z xs := by
  classical
  have h1 : (c.not.raiseSigma m).arity = k := by simp [hk]
  rw [NormalForm.raisePi, (hc.not.raiseSigma m).evalTuple_not h1 xs,
    evalTuple_raiseSigma Z c.not m xs, hc.evalTuple_not hk xs, Classical.not_not]

/-! ### Variable binding and quantifier contraction -/

private def reassocCode : Code :=
  .pair (.pair .left (.comp .left .right)) (.comp .right .right)

@[simp]
private theorem eval_reassocCode (O : ℕ →. ℕ) (a w : ℕ) :
    Code.eval O reassocCode (Nat.pair a w) =
      Part.some (Nat.pair (Nat.pair a w.unpair.1) w.unpair.2) := by
  simp [reassocCode, Seq.seq]

/-- Bind the last free numerical variable of `c` (when `c.arity ≥ 1`) with an existential
quantifier, contracting adjacent existential quantifiers via `Nat.pair`. Leaves nullary codes
unchanged. -/
def bindExists (c : NormalForm) : NormalForm :=
  match c.arity with
  | 0 => c
  | 1 =>
    match c.pref with
    | .qf => ⟨.sigma 0, 0, .comp c.matrix .right⟩
    | .sigma n => ⟨.sigma n, 0, .comp c.matrix (liftBase n .right)⟩
    | .pi n => ⟨.sigma (n + 1), 0, .comp c.matrix (liftBase (n + 1) .right)⟩
  | k + 2 =>
    match c.pref with
    | .qf => ⟨.sigma 0, k + 1, c.matrix⟩
    | .sigma n => ⟨.sigma n, k + 1, .comp c.matrix (liftBase n reassocCode)⟩
    | .pi n => ⟨.sigma (n + 1), k + 1, c.matrix⟩

/-- Bind the last free numerical variable of `c` (when `c.arity ≥ 1`) with a universal
quantifier, contracting adjacent universal quantifiers via De Morgan duality. Leaves nullary codes
unchanged. -/
def bindForall (c : NormalForm) : NormalForm :=
  if c.arity = 0 then c else c.not.bindExists.not

@[simp]
theorem arity_bindExists (c : NormalForm) : c.bindExists.arity = c.arity - 1 := by
  rcases h : c.arity with _ | _ | k <;> cases hp : c.pref <;> simp [bindExists, h, hp]

@[simp]
theorem pref_bindExists_of_pos {c : NormalForm} (h : 0 < c.arity) :
    c.bindExists.pref = c.pref.addExists := by
  rcases ha : c.arity with _ | _ | k
  · omega
  · cases hp : c.pref <;> simp [bindExists, ha, hp]
  · cases hp : c.pref <;> simp [bindExists, ha, hp]

@[simp]
theorem arity_bindForall (c : NormalForm) : c.bindForall.arity = c.arity - 1 := by
  by_cases h : c.arity = 0 <;> simp [bindForall, h]

@[simp]
theorem pref_bindForall_of_pos {c : NormalForm} (h : 0 < c.arity) :
    c.bindForall.pref = c.pref.addForall := by
  have hne : c.arity ≠ 0 := by omega
  have hpos' : 0 < c.not.arity := by simpa using h
  simp [bindForall, hne, pref_bindExists_of_pos hpos']

/-- `bindExists` is primitive recursive. -/
theorem primrec_bindExists : Primrec bindExists := by
  have hm1 : Primrec fun c : NormalForm =>
      QuantifierPrefix.casesOn (motive := fun _ => Code) c.pref
        (.comp c.matrix .right)
        (fun n => .comp c.matrix (liftBase n .right))
        (fun n => .comp c.matrix (liftBase (n + 1) .right)) :=
    QuantifierPrefix.primrec_casesOn primrec_pref
      (Code.primrec₂_comp.comp primrec_matrix (const Code.right))
      (Code.primrec₂_comp.comp (primrec_matrix.comp fst)
        (primrec₂_liftBase.comp snd (const Code.right))).to₂
      (Code.primrec₂_comp.comp (primrec_matrix.comp fst)
        (primrec₂_liftBase.comp (Primrec.succ.comp snd) (const Code.right))).to₂
  have hm2 : Primrec fun c : NormalForm =>
      QuantifierPrefix.casesOn (motive := fun _ => Code) c.pref
        c.matrix
        (fun n => .comp c.matrix (liftBase n reassocCode))
        (fun _ => c.matrix) :=
    QuantifierPrefix.primrec_casesOn primrec_pref
      primrec_matrix
      (Code.primrec₂_comp.comp (primrec_matrix.comp fst)
        (primrec₂_liftBase.comp snd (const reassocCode))).to₂
      (primrec_matrix.comp fst).to₂
  have hc1 := primrec₃_mk (QuantifierPrefix.primrec_addExists.comp primrec_pref) (const 0) hm1
  have hc2 := primrec₃_mk (QuantifierPrefix.primrec_addExists.comp primrec_pref)
    (nat_sub.comp primrec_arity (const 1)) hm2
  refine (Primrec.ite (Primrec.eq.comp primrec_arity (const 0)) .id
    (Primrec.ite (Primrec.eq.comp primrec_arity (const 1)) hc1 hc2)).of_eq fun c => ?_
  rcases ha : c.arity with _ | _ | k <;> cases hp : c.pref <;>
    simp [bindExists, ha, hp]

/-- `bindForall` is primitive recursive. -/
theorem primrec_bindForall : Primrec bindForall :=
  Primrec.ite (Primrec.eq.comp primrec_arity (const 0)) .id
    (primrec_not.comp (primrec_bindExists.comp primrec_not))

/-- `bindExists` preserves semantic validity relative to `Z`. -/
theorem Valid.bindExists {Z : Set ℕ} {c : NormalForm} (hc : c.Valid Z) :
    c.bindExists.Valid Z := by
  rcases ha : c.arity with _ | _ | k
  · have hdef : c.bindExists = c := by simp [NormalForm.bindExists, ha]
    rwa [hdef]
  · have hcv : ∀ y : ℕ, ValidDepth Z c.matrix c.pref.depth y := by
      have h := valid_iff_validAux.1 hc
      simpa [ha] using h
    rw [valid_iff_validAux]
    have har0 : c.bindExists.arity = 0 := by simp [ha]
    simp only [har0, ↓reduceIte]
    cases hp : c.pref with
    | qf =>
      simp only [hp, QuantifierPrefix.depth_qf] at hcv
      simpa [NormalForm.bindExists, ha, hp, PFun.some_bind] using hcv
    | sigma n =>
      simp only [hp, QuantifierPrefix.depth_sigma] at hcv
      simp only [NormalForm.bindExists, ha, hp, validAux_eq_validDepth,
        QuantifierPrefix.depth_sigma, validDepth_succ]
      intro w
      have hw : ValidDepth Z c.matrix n (Nat.pair w.unpair.1 w.unpair.2) :=
        (validDepth_succ Z c.matrix n w.unpair.1).1 (hcv w.unpair.1) w.unpair.2
      rw [Nat.pair_unpair] at hw
      exact (validDepth_comp_liftBase_iff (f := .right) (b := w) (by simp)).2 hw
    | pi n =>
      simp only [hp, QuantifierPrefix.depth_pi] at hcv
      simp only [NormalForm.bindExists, ha, hp, validAux_eq_validDepth,
        QuantifierPrefix.depth_sigma]
      rw [validDepth_succ]
      intro y
      exact (validDepth_comp_liftBase_iff (f := .right) (a := Nat.pair 0 y) (b := y)
        (by simp)).2 (hcv y)
  · have hcv : ∀ b : ℕ, ValidDepth Z c.matrix c.pref.depth b := by
      have h := valid_iff_validAux.1 hc
      simpa [ha] using h
    rw [valid_iff_validAux]
    have har_ne : c.bindExists.arity ≠ 0 := by simp [ha]
    simp only [har_ne, ↓reduceIte]
    intro a
    cases hp : c.pref with
    | qf =>
      simp only [hp, QuantifierPrefix.depth_qf] at hcv
      simpa [NormalForm.bindExists, ha, hp] using fun y : ℕ => hcv (Nat.pair a y)
    | sigma n =>
      simp only [hp, QuantifierPrefix.depth_sigma] at hcv
      simp only [NormalForm.bindExists, ha, hp, validAux_eq_validDepth,
        QuantifierPrefix.depth_sigma, validDepth_succ]
      intro w
      have hw : ValidDepth Z c.matrix n (Nat.pair (Nat.pair a w.unpair.1) w.unpair.2) :=
        (validDepth_succ Z c.matrix n (Nat.pair a w.unpair.1)).1 (hcv (Nat.pair a w.unpair.1))
          w.unpair.2
      exact (validDepth_comp_liftBase_iff (eval_reassocCode Z.oracle a w)).2 hw
    | pi n =>
      simp only [hp, QuantifierPrefix.depth_pi] at hcv
      simpa [NormalForm.bindExists, ha, hp] using fun y : ℕ => hcv (Nat.pair a y)

/-- `bindExists` implements existential quantification over the last free numerical variable. -/
theorem evalTuple_bindExists {Z : Set ℕ} {c : NormalForm} {k : ℕ} (hk : c.arity = k + 1)
    (xs : ArityTuple k) :
    c.bindExists.EvalTuple Z xs ↔ ∃ y : ℕ, c.EvalTuple Z (ArityTuple.snoc xs y) := by
  rcases k with _ | k
  · cases xs
    cases hp : c.pref with
    | qf =>
      simp [bindExists, evalTuple_iff_holdsCode, hk, hp, PFun.some_bind]
    | sigma n =>
      simp only [bindExists, hk, hp, evalTuple_iff_holdsCode, holdsCode_iff, holdsAux_eq_holdsBlock,
        QuantifierPrefix.startsExists_sigma, QuantifierPrefix.depth_sigma, holdsBlock_true_succ]
      constructor
      · intro ⟨w, hw⟩
        have hw' := (holdsBlock_comp_liftBase_iff (f := .right) (b := w) (by simp)).1 hw
        exact ⟨w.unpair.1, w.unpair.2, by simpa using hw'⟩
      · rintro ⟨y, z, hyz⟩
        have hyz' : HoldsBlock Z c.matrix false n (Nat.pair y z) := by simpa using hyz
        exact ⟨Nat.pair y z,
          (holdsBlock_comp_liftBase_iff (f := .right) (b := Nat.pair y z) (by simp)).2 hyz'⟩
    | pi n =>
      simp only [bindExists, hk, hp, evalTuple_iff_holdsCode, holdsCode_iff, holdsAux_eq_holdsBlock,
        QuantifierPrefix.startsExists_sigma, QuantifierPrefix.startsExists_pi,
        QuantifierPrefix.depth_sigma, QuantifierPrefix.depth_pi, holdsBlock_true_succ]
      exact exists_congr fun y => holdsBlock_comp_liftBase_iff (f := .right) (b := y) (by simp)
  · cases hp : c.pref with
    | qf =>
      simp [bindExists, evalTuple_iff_holdsCode, hk, hp]
    | sigma n =>
      simp only [bindExists, hk, hp, evalTuple_iff_holdsCode, holdsCode_iff, holdsAux_eq_holdsBlock,
        QuantifierPrefix.startsExists_sigma, QuantifierPrefix.depth_sigma, holdsBlock_true_succ]
      constructor
      · intro ⟨w, hw⟩
        have hw' :=
          (holdsBlock_comp_liftBase_iff (eval_reassocCode Z.oracle (encode xs) w)).1 hw
        exact ⟨w.unpair.1, w.unpair.2, hw'⟩
      · rintro ⟨y, z, hyz⟩
        refine ⟨Nat.pair y z, (holdsBlock_comp_liftBase_iff
          (eval_reassocCode Z.oracle (encode xs) (Nat.pair y z))).2 ?_⟩
        simpa using hyz
    | pi n =>
      simp [bindExists, evalTuple_iff_holdsCode, hk, hp]

/-- `bindForall` preserves semantic validity relative to `Z`. -/
theorem Valid.bindForall {Z : Set ℕ} {c : NormalForm} (hc : c.Valid Z) :
    c.bindForall.Valid Z := by
  by_cases h : c.arity = 0
  · simpa [NormalForm.bindForall, h] using hc
  · simpa [NormalForm.bindForall, h] using hc.not.bindExists.not

/-- `bindForall` implements universal quantification over the last free numerical variable on valid
normal forms. -/
theorem Valid.evalTuple_bindForall {Z : Set ℕ} {c : NormalForm} {k : ℕ} (hc : c.Valid Z)
    (hk : c.arity = k + 1) (xs : ArityTuple k) :
    c.bindForall.EvalTuple Z xs ↔ ∀ y : ℕ, c.EvalTuple Z (ArityTuple.snoc xs y) := by
  classical
  have hne : c.arity ≠ 0 := by omega
  have hnot_ar : c.not.arity = k + 1 := by simpa using hk
  have hbe_ar : c.not.bindExists.arity = k := by simp [hk]
  have hdef : c.bindForall = c.not.bindExists.not := by simp [NormalForm.bindForall, hne]
  rw [hdef, (hc.not.bindExists).evalTuple_not hbe_ar xs,
    evalTuple_bindExists hnot_ar xs, not_exists]
  exact forall_congr' fun y =>
    (not_congr (hc.evalTuple_not hk (ArityTuple.snoc xs y))).trans Classical.not_not

/-! ### Prenex conjunction and disjunction -/

private def stepMergeLeft (f : Code) : Code :=
  .pair (.comp f .left) (.comp .left .right)

private def stepMergeRight (f : Code) : Code :=
  .pair (.comp f .left) (.comp .right .right)

private theorem primrec_stepMergeLeft : Primrec stepMergeLeft :=
  Code.primrec₂_pair.comp (Code.primrec₂_comp.comp .id (const Code.left))
    (const (Code.comp .left .right))

private theorem primrec_stepMergeRight : Primrec stepMergeRight :=
  Code.primrec₂_pair.comp (Code.primrec₂_comp.comp .id (const Code.left))
    (const (Code.comp .right .right))

private def mergeLeft (d : ℕ) (f : Code) : Code :=
  stepMergeLeft^[d] f

private def mergeRight (d : ℕ) (f : Code) : Code :=
  stepMergeRight^[d] f

@[simp] private theorem mergeLeft_zero (f : Code) : mergeLeft 0 f = f := (rfl)
@[simp] private theorem mergeLeft_succ (d : ℕ) (f : Code) :
    mergeLeft (d + 1) f = mergeLeft d (stepMergeLeft f) := (rfl)
@[simp] private theorem mergeRight_zero (f : Code) : mergeRight 0 f = f := (rfl)
@[simp] private theorem mergeRight_succ (d : ℕ) (f : Code) :
    mergeRight (d + 1) f = mergeRight d (stepMergeRight f) := (rfl)

private theorem primrec₂_mergeLeft : Primrec₂ mergeLeft :=
  (nat_iterate fst snd (primrec_stepMergeLeft.comp snd).to₂).to₂

private theorem primrec₂_mergeRight : Primrec₂ mergeRight :=
  (nat_iterate fst snd (primrec_stepMergeRight.comp snd).to₂).to₂

private theorem eval_stepMergeLeft {O : ℕ →. ℕ} {f : Code} {b a₁ : ℕ}
    (hf : Code.eval O f b = Part.some a₁) (w : ℕ) :
    Code.eval O (stepMergeLeft f) (Nat.pair b w) = Part.some (Nat.pair a₁ w.unpair.1) := by
  simp [stepMergeLeft, Seq.seq, hf]

private theorem eval_stepMergeRight {O : ℕ →. ℕ} {f : Code} {b a₂ : ℕ}
    (hf : Code.eval O f b = Part.some a₂) (w : ℕ) :
    Code.eval O (stepMergeRight f) (Nat.pair b w) = Part.some (Nat.pair a₂ w.unpair.2) := by
  simp [stepMergeRight, Seq.seq, hf]

/-- Prenex conjunction of two normal-form codes sharing `c₁.pref` and `c₁.arity`. -/
def and (c₁ c₂ : NormalForm) : NormalForm where
  pref := c₁.pref
  arity := c₁.arity
  matrix := .comp andBoolCode
    (.pair (.comp c₁.matrix (mergeLeft c₁.pref.depth idCode))
           (.comp c₂.matrix (mergeRight c₁.pref.depth idCode)))

/-- Prenex disjunction of two normal-form codes sharing `c₁.pref` and `c₁.arity`, defined via
De Morgan duality. -/
def or (c₁ c₂ : NormalForm) : NormalForm :=
  (c₁.not.and c₂.not).not

@[simp] theorem pref_and (c₁ c₂ : NormalForm) : (c₁.and c₂).pref = c₁.pref := (rfl)
@[simp] theorem arity_and (c₁ c₂ : NormalForm) : (c₁.and c₂).arity = c₁.arity := (rfl)
@[simp] theorem pref_or (c₁ c₂ : NormalForm) : (c₁.or c₂).pref = c₁.pref := by simp [or]
@[simp] theorem arity_or (c₁ c₂ : NormalForm) : (c₁.or c₂).arity = c₁.arity := by simp [or]

/-- `NormalForm.and` is primitive recursive. -/
theorem primrec₂_and : Primrec₂ and := by
  have hd : Primrec fun p : NormalForm × NormalForm => p.1.pref.depth :=
    QuantifierPrefix.primrec_depth.comp (primrec_pref.comp fst)
  have hl := Code.primrec₂_comp.comp (primrec_matrix.comp fst)
    (primrec₂_mergeLeft.comp hd (const idCode))
  have hr := Code.primrec₂_comp.comp (primrec_matrix.comp snd)
    (primrec₂_mergeRight.comp hd (const idCode))
  exact (primrec₃_mk (primrec_pref.comp fst) (primrec_arity.comp fst)
    (Code.primrec₂_comp.comp (const andBoolCode) (Code.primrec₂_pair.comp hl hr))).to₂

/-- `NormalForm.or` is primitive recursive. -/
theorem primrec₂_or : Primrec₂ or :=
  (primrec_not.comp (primrec₂_and.comp (primrec_not.comp fst) (primrec_not.comp snd))).to₂

private theorem valid_and_holds_merge_and {Z : Set ℕ} {m₁ m₂ : Code} :
    ∀ {d : ℕ} {ex : Bool} {f₁ f₂ : Code} {b a₁ a₂ : ℕ},
      Code.eval Z.oracle f₁ b = Part.some a₁ →
      Code.eval Z.oracle f₂ b = Part.some a₂ →
      ValidDepth Z m₁ d a₁ →
      ValidDepth Z m₂ d a₂ →
      let M := .comp andBoolCode (.pair (.comp m₁ (mergeLeft d f₁)) (.comp m₂ (mergeRight d f₂)))
      ValidDepth Z M d b ∧
        (HoldsBlock Z M ex d b ↔ HoldsBlock Z m₁ ex d a₁ ∧ HoldsBlock Z m₂ ex d a₂)
  | 0, ex, f₁, f₂, b, a₁, a₂, hf₁, hf₂, hv₁, hv₂ => by
    obtain ⟨b₁, hb₁⟩ := (validDepth_zero Z m₁ a₁).1 hv₁
    obtain ⟨b₂, hb₂⟩ := (validDepth_zero Z m₂ a₂).1 hv₂
    have heval : Code.eval Z.oracle
        (.comp andBoolCode (.pair (.comp m₁ f₁) (.comp m₂ f₂))) b =
        Part.some (encode (b₁ && b₂)) := by
      simp [Seq.seq, hf₁, hf₂, hb₁, hb₂, PFun.some_bind]
    refine ⟨(validDepth_zero Z _ b).2 ⟨b₁ && b₂, heval⟩, ?_⟩
    simp only [mergeLeft_zero, mergeRight_zero, holdsBlock_zero, heval, hb₁, hb₂]
    cases b₁ <;> cases b₂ <;> simp
  | d + 1, ex, f₁, f₂, b, a₁, a₂, hf₁, hf₂, hv₁, hv₂ => by
    have step (w : ℕ) := valid_and_holds_merge_and (d := d) (ex := !ex)
      (eval_stepMergeLeft hf₁ w) (eval_stepMergeRight hf₂ w)
      ((validDepth_succ Z m₁ d a₁).1 hv₁ w.unpair.1)
      ((validDepth_succ Z m₂ d a₂).1 hv₂ w.unpair.2)
    refine ⟨(validDepth_succ Z _ d b).2 fun w => (step w).1, ?_⟩
    cases ex with
    | true =>
      simp only [holdsBlock_true_succ]
      constructor
      · intro ⟨w, hw⟩
        obtain ⟨h₁, h₂⟩ := (step w).2.1 hw
        exact ⟨⟨w.unpair.1, h₁⟩, ⟨w.unpair.2, h₂⟩⟩
      · rintro ⟨⟨u, hu⟩, ⟨v, hv⟩⟩
        refine ⟨Nat.pair u v, (step (Nat.pair u v)).2.2 ?_⟩
        simpa using And.intro hu hv
    | false =>
      simp only [holdsBlock_false_succ]
      constructor
      · intro hw
        refine ⟨fun u => ?_, fun v => ?_⟩
        · have h := (step (Nat.pair u 0)).2.1 (hw (Nat.pair u 0))
          simpa using h.1
        · have h := (step (Nat.pair 0 v)).2.1 (hw (Nat.pair 0 v))
          simpa using h.2
      · rintro ⟨hu, hv⟩ w
        exact (step w).2.2 ⟨hu w.unpair.1, hv w.unpair.2⟩

/-- Prenex conjunction preserves semantic validity on matching prefix and arity. -/
theorem Valid.and {Z : Set ℕ} {c₁ c₂ : NormalForm} (hc₁ : c₁.Valid Z) (hc₂ : c₂.Valid Z)
    (hp : c₂.pref = c₁.pref) (ha : c₂.arity = c₁.arity) : (c₁.and c₂).Valid Z := by
  have h1 := valid_iff_validAux.1 hc₁
  have h2 := valid_iff_validAux.1 hc₂
  rw [valid_iff_validAux]
  simp only [arity_and, pref_and, ha, hp, validAux_eq_validDepth] at h1 h2 ⊢
  split_ifs with h0
  · simp only [h0, ↓reduceIte] at h1 h2
    exact (valid_and_holds_merge_and (ex := c₁.pref.startsExists)
      (eval_idCode Z.oracle 0) (eval_idCode Z.oracle 0) h1 h2).1
  · simp only [h0, ↓reduceIte] at h1 h2
    exact fun a => (valid_and_holds_merge_and (ex := c₁.pref.startsExists)
      (eval_idCode Z.oracle a) (eval_idCode Z.oracle a) (h1 a) (h2 a)).1

/-- Prenex conjunction evaluates to logical conjunction on valid codes of matching prefix and
arity. -/
@[simp]
theorem Valid.evalTuple_and {Z : Set ℕ} {c₁ c₂ : NormalForm} {k : ℕ} (hc₁ : c₁.Valid Z)
    (hc₂ : c₂.Valid Z) (hp : c₂.pref = c₁.pref) (ha₁ : c₁.arity = k) (ha₂ : c₂.arity = k)
    (xs : ArityTuple k) :
    (c₁.and c₂).EvalTuple Z xs ↔ c₁.EvalTuple Z xs ∧ c₂.EvalTuple Z xs := by
  have h1 : ValidDepth Z c₁.matrix c₁.pref.depth (encode xs) := by
    subst ha₁
    simpa using (valid_iff Z c₁).1 hc₁ xs
  have h2 : ValidDepth Z c₂.matrix c₁.pref.depth (encode xs) := by
    subst ha₂
    simpa [hp] using (valid_iff Z c₂).1 hc₂ xs
  have hm := (valid_and_holds_merge_and (ex := c₁.pref.startsExists)
    (eval_idCode Z.oracle (encode xs)) (eval_idCode Z.oracle (encode xs)) h1 h2).2
  simpa [NormalForm.and, evalTuple_iff_holdsCode, hp] using hm

/-- Prenex disjunction preserves semantic validity on matching prefix and arity. -/
theorem Valid.or {Z : Set ℕ} {c₁ c₂ : NormalForm} (hc₁ : c₁.Valid Z) (hc₂ : c₂.Valid Z)
    (hp : c₂.pref = c₁.pref) (ha : c₂.arity = c₁.arity) : (c₁.or c₂).Valid Z :=
  (hc₁.not.and hc₂.not (by simp [hp]) (by simp [ha])).not

/-- Prenex disjunction evaluates to logical disjunction on valid codes of matching prefix and
arity. -/
@[simp]
theorem Valid.evalTuple_or {Z : Set ℕ} {c₁ c₂ : NormalForm} {k : ℕ} (hc₁ : c₁.Valid Z)
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
