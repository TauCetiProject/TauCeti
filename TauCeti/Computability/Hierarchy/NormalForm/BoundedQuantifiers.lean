/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Computability.Hierarchy.NormalForm.Compiler
import TauCeti.Data.PFun.Basic

/-!
# Bounded number-quantifier compilers on displayed normal-form codes

Bounded number quantifiers (`∃ y < t`, `∀ y < t`, `∃ y ≤ t`, `∀ y ≤ t`) preserve every level of the
arithmetical hierarchy. This file implements that closure uniformly on `NormalForm` codes via
primitive-recursive compilers `existsLt`, `forallLt`, `existsLe`, and `forallLe` preserving both
`c.pref` and `c.arity`, using finite-domain Skolemization (`nthUnpair` / `packPrefix`) across `∀`
and primitive recursion (`Code.prec`) at depth zero.

## References

* R. I. Soare, *Recursively Enumerable Sets and Degrees*, Springer, 1987, Chapter IV.1.
-/

public section

open Encodable Denumerable Primrec TauCeti.Oracle.Single

namespace TauCeti.ArithmeticalHierarchy.NormalForm

/-! ### Finite-prefix stream packing via `Nat.unpair` -/

private def tailIter (w : ℕ) : ℕ → ℕ
  | 0 => w
  | y + 1 => (tailIter w y).unpair.2
private def nthUnpair (w y : ℕ) : ℕ := (tailIter w y).unpair.1
private theorem tailIter_pair_succ (a w : ℕ) : ∀ y, tailIter (Nat.pair a w) (y + 1) = tailIter w y
  | 0 => by simp [tailIter]
  | y + 1 => by rw [tailIter, tailIter_pair_succ a w y, tailIter]

private def packPrefix : (ℕ → ℕ) → ℕ → ℕ
  | _, 0 => 0
  | z, t + 1 => Nat.pair (z 0) (packPrefix (fun y => z (y + 1)) t)
private theorem nthUnpair_packPrefix :
    ∀ {t : ℕ} (z : ℕ → ℕ) {y : ℕ}, y < t → nthUnpair (packPrefix z t) y = z y
  | 0, _, _, hy => absurd hy (Nat.not_lt_zero _)
  | _ + 1, _, 0, _ => by simp [packPrefix, nthUnpair, tailIter]
  | _ + 1, z, _ + 1, hy => by
    simpa [packPrefix, nthUnpair, tailIter_pair_succ] using
      nthUnpair_packPrefix (fun i => z (i + 1)) (Nat.lt_of_succ_lt_succ hy)

private def nthUnpairCode : Code :=
  .comp .left (.prec idCode (.comp .right (.comp .right .right)))
private theorem eval_nthUnpairCode (O : ℕ →. ℕ) (w y : ℕ) :
    Code.eval O nthUnpairCode (Nat.pair w y) = Part.some (nthUnpair w y) := by
  have htail : ∀ k, Code.eval O (.prec idCode (.comp .right (.comp .right .right)))
      (Nat.pair w k) = Part.some (tailIter w k) := fun k => by
    induction k with
    | zero => simp [tailIter]
    | succ k ih => rw [Code.eval_prec_succ, ih]; simp [tailIter, PFun.some_bind]
  simp [nthUnpairCode, nthUnpair, htail y, PFun.some_bind]

/-! ### Bounded existential state transition and base loop -/

private def stepBounded (s : Bool × Code × Code) : Bool × Code × Code :=
  let argLeft := .comp s.2.2 (.pair (.comp .left .left) .right)
  (!s.1, .comp s.2.1 .left,
    if s.1 then .pair argLeft (.comp .right .left)
    else .pair argLeft (.comp nthUnpairCode (.pair (.comp .right .left) .right)))

private theorem primrec_stepBounded : Primrec stepBounded := by
  have hex : Primrec fun s : Bool × Code × Code => s.1 := fst
  have hbc : Primrec fun s : Bool × Code × Code => s.2.1 := fst.comp snd
  have hmc : Primrec fun s : Bool × Code × Code => s.2.2 := snd.comp snd
  have hbc' := Code.primrec₂_comp.comp hbc (const Code.left)
  have harg := Code.primrec₂_comp.comp hmc (const (Code.pair (.comp .left .left) .right))
  have hmcT := Code.primrec₂_pair.comp harg (const (Code.comp .right .left))
  have hmcF := Code.primrec₂_pair.comp harg
    (const (Code.comp nthUnpairCode (.pair (.comp .right .left) .right)))
  exact (Primrec.not.comp hex).pair
    (hbc'.pair (Primrec.ite (Primrec.eq.comp hex (const true)) hmcT hmcF))

private def existsLtBase (m bc mc : Code) : Code :=
  .comp (.prec .zero (.comp orBoolCode
    (.pair (.comp .right .right) (.comp m (.comp mc (.pair .left (.comp .left .right)))))))
    (.pair idCode bc)

private theorem primrec₃_existsLtBase :
    Primrec fun t : Code × Code × Code => existsLtBase t.1 t.2.1 t.2.2 := by
  have hm : Primrec fun t : Code × Code × Code => t.1 := fst
  have hbc : Primrec fun t : Code × Code × Code => t.2.1 := fst.comp snd
  have hmc : Primrec fun t : Code × Code × Code => t.2.2 := snd.comp snd
  have hcall := Code.primrec₂_comp.comp hm
    (Code.primrec₂_comp.comp hmc (const (Code.pair .left (.comp .left .right))))
  have hstep := Code.primrec₂_comp.comp (const orBoolCode)
    (Code.primrec₂_pair.comp (const (Code.comp .right .right)) hcall)
  exact Code.primrec₂_comp.comp (Code.primrec₂_prec.comp (const Code.zero) hstep)
    (Code.primrec₂_pair.comp (const idCode) hbc)

private theorem eval_existsLtBase {Z : Set ℕ} {m bc mc : Code} {b t : ℕ} {a : ℕ → ℕ}
    (hbc : Code.eval Z.oracle bc b = Part.some t)
    (hmc : ∀ y, Code.eval Z.oracle mc (Nat.pair b y) = Part.some (a y))
    (hv : ∀ y, ValidDepth Z m 0 (a y)) :
    ∃ res : Bool, Code.eval Z.oracle (existsLtBase m bc mc) b = Part.some (encode res) ∧
      (res = true ↔ ∃ y < t, HoldsBlock Z m false 0 (a y)) := by
  classical
  let loop : Code := .prec .zero (.comp orBoolCode
    (.pair (.comp .right .right) (.comp m (.comp mc (.pair .left (.comp .left .right))))))
  have hloop : ∀ s, Code.eval Z.oracle loop (Nat.pair b s) =
      Part.some (encode (decide (∃ y < s, HoldsBlock Z m false 0 (a y)))) := fun s => by
    induction s with
    | zero => simp [loop]
    | succ s ih =>
      obtain ⟨bs, hbs⟩ := (validDepth_zero Z m (a s)).1 (hv s)
      have hbs_iff : bs = true ↔ HoldsBlock Z m false 0 (a s) := by cases bs <;> simp [hbs]
      rw [Code.eval_prec_succ, ih]; simp only [Part.bind_eq_bind, Part.bind_some]
      refine Eq.trans (b := Part.some (encode (decide (∃ y < s, HoldsBlock Z m false 0 (a y)) ||
        bs))) (by simp [Seq.seq, hmc s, hbs, PFun.some_bind]) ?_
      congr 2; exact Bool.eq_iff_iff.2 (by
        simp [Nat.lt_succ_iff_lt_or_eq, or_and_right, exists_or, hbs_iff])
  have harg : Code.eval Z.oracle (.pair idCode bc) b = Part.some (Nat.pair b t) := by
    simp [Seq.seq, hbc]
  exact ⟨decide (∃ y < t, HoldsBlock Z m false 0 (a y)),
    by simp [existsLtBase, loop, harg, hloop t, PFun.some_bind], decide_eq_true_iff⟩

private theorem valid_and_holds_stepBounded {Z : Set ℕ} {m : Code} :
    ∀ (d : ℕ) (ex : Bool) (bc mc : Code) (b t : ℕ) (a : ℕ → ℕ),
      Code.eval Z.oracle bc b = Part.some t →
      (∀ y, Code.eval Z.oracle mc (Nat.pair b y) = Part.some (a y)) →
      (∀ y, ValidDepth Z m d (a y)) →
      let s' := stepBounded^[d] (ex, bc, mc)
      let M := existsLtBase m s'.2.1 s'.2.2
      ValidDepth Z M d b ∧ (HoldsBlock Z M ex d b ↔ ∃ y < t, HoldsBlock Z m ex d (a y))
  | 0, _, bc, mc, b, t, a, hbc, hmc, hv => by
    obtain ⟨res, hres, hiff⟩ := eval_existsLtBase hbc hmc hv
    simp only [holdsBlock_zero] at hiff
    refine ⟨(validDepth_zero Z _ b).2 ⟨res, hres⟩, ?_⟩
    simp only [Function.iterate_zero, id_eq, holdsBlock_zero, hres, Part.mem_some_iff, encode_inj]
    exact ⟨fun h => hiff.1 h.symm, fun h => (hiff.2 h).symm⟩
  | d + 1, true, bc, mc, b, t, a, hbc, hmc, hv => by
    have step (w : ℕ) := valid_and_holds_stepBounded d false (.comp bc .left)
      (.pair (.comp mc (.pair (.comp .left .left) .right)) (.comp .right .left))
      (Nat.pair b w) t (fun y => Nat.pair (a y) w)
      (by simp [hbc, PFun.some_bind]) (fun y => by simp [Seq.seq, hmc y, PFun.some_bind])
      (fun y => (validDepth_succ Z m d (a y)).1 (hv y) w)
    simp only [Function.iterate_succ_apply, stepBounded, ↓reduceIte, Bool.not_true]
    refine ⟨(validDepth_succ Z _ d b).2 fun w => (step w).1, ?_⟩
    simp only [holdsBlock_true_succ]
    exact ⟨fun ⟨w, hw⟩ => let ⟨y, hyt, hyw⟩ := (step w).2.1 hw; ⟨y, hyt, w, hyw⟩,
      fun ⟨y, hyt, w, hyw⟩ => ⟨w, (step w).2.2 ⟨y, hyt, hyw⟩⟩⟩
  | d + 1, false, bc, mc, b, t, a, hbc, hmc, hv => by
    classical
    have step (w : ℕ) := valid_and_holds_stepBounded d true (.comp bc .left)
      (.pair (.comp mc (.pair (.comp .left .left) .right))
        (.comp nthUnpairCode (.pair (.comp .right .left) .right)))
      (Nat.pair b w) t (fun y => Nat.pair (a y) (nthUnpair w y))
      (by simp [hbc, PFun.some_bind])
      (fun y => by simp [Seq.seq, hmc y, eval_nthUnpairCode, PFun.some_bind])
      (fun y => (validDepth_succ Z m d (a y)).1 (hv y) (nthUnpair w y))
    simp only [Function.iterate_succ_apply, stepBounded, Bool.false_eq_true, ↓reduceIte,
      Bool.not_false]
    refine ⟨(validDepth_succ Z _ d b).2 fun w => (step w).1, ?_⟩
    simp only [holdsBlock_false_succ]
    refine ⟨fun hw => ?_, fun ⟨y, hyt, hy⟩ w => (step w).2.2 ⟨y, hyt, hy (nthUnpair w y)⟩⟩
    by_contra hnot
    choose z hz using fun y =>
      show ∃ z, y < t → ¬HoldsBlock Z m true d (Nat.pair (a y) z) from
        if hyt : y < t then
          let ⟨z, hz⟩ := not_forall.1 (fun hz => hnot ⟨y, hyt, hz⟩); ⟨z, fun _ => hz⟩
        else ⟨0, fun hyt' => absurd hyt' hyt⟩
    obtain ⟨y, hyt, hyw⟩ := (step (packPrefix z t)).2.1 (hw (packPrefix z t))
    rw [nthUnpair_packPrefix z hyt] at hyw; exact hz y hyt hyw

/-! ### Bounded quantifier compilers -/

private def succLastCode (ar : ℕ) : Code :=
  if ar = 1 then .succ else .pair .left (.comp .succ .right)
private theorem primrec_succLastCode : Primrec succLastCode :=
  Primrec.ite (Primrec.eq.comp .id (const 1)) (const Code.succ)
    (const (Code.pair .left (.comp .succ .right)))
private theorem exists_eval_succLastCode (O : ℕ →. ℕ) (ar a : ℕ) :
    ∃ b : ℕ, Code.eval O (succLastCode ar) a = Part.some b := by
  by_cases h : ar = 1
  · exact ⟨a + 1, by simp [succLastCode, h]⟩
  · exact ⟨Nat.pair a.unpair.1 (a.unpair.2 + 1), by simp [succLastCode, h, Seq.seq, PFun.some_bind]⟩
private theorem eval_succLastCode (O : ℕ →. ℕ) {ar k : ℕ} (hk : ar = k + 1)
    (xs : ArityTuple k) (t : ℕ) :
    Code.eval O (succLastCode ar) (encode (ArityTuple.snoc xs t)) =
      Part.some (encode (ArityTuple.snoc xs (t + 1))) := by
  subst hk; rcases k with _ | k
  · cases xs; simp [succLastCode]
  · simp [succLastCode, Seq.seq, PFun.some_bind]

/-- Bounded existential quantification `∃ y < t` over the last free argument of `c`, preserving
both `c.pref` and `c.arity` across all quantifier prefixes. -/
def existsLt (c : NormalForm) : NormalForm :=
  ⟨c.pref, c.arity,
    if c.arity = 0 then c.matrix
    else
      let bc : Code := if c.arity = 1 then idCode else .right
      let mc : Code := if c.arity = 1 then .right else .pair (.comp .left .left) .right
      let s' := stepBounded^[c.pref.depth] (c.pref.startsExists, bc, mc)
      existsLtBase c.matrix s'.2.1 s'.2.2⟩

/-- Bounded universal quantification `∀ y < t` over the last free argument of `c`, preserving
`c.pref` and `c.arity`. -/
def forallLt (c : NormalForm) : NormalForm := if c.arity = 0 then c else c.not.existsLt.not

/-- Bounded existential quantification `∃ y ≤ t` over the last free argument of `c`, preserving
`c.pref` and `c.arity`. -/
def existsLe (c : NormalForm) : NormalForm :=
  if c.arity = 0 then c else c.existsLt.preimage c.arity (succLastCode c.arity)

/-- Bounded universal quantification `∀ y ≤ t` over the last free argument of `c`, preserving
`c.pref` and `c.arity`. -/
def forallLe (c : NormalForm) : NormalForm :=
  if c.arity = 0 then c else c.forallLt.preimage c.arity (succLastCode c.arity)

@[simp] theorem pref_existsLt (c : NormalForm) : c.existsLt.pref = c.pref := (rfl)
@[simp] theorem arity_existsLt (c : NormalForm) : c.existsLt.arity = c.arity := (rfl)
@[simp] theorem pref_forallLt (c : NormalForm) : c.forallLt.pref = c.pref := by
  by_cases h : c.arity = 0 <;> simp [forallLt, h]
@[simp] theorem arity_forallLt (c : NormalForm) : c.forallLt.arity = c.arity := by
  by_cases h : c.arity = 0 <;> simp [forallLt, h]
@[simp] theorem pref_existsLe (c : NormalForm) : c.existsLe.pref = c.pref := by
  by_cases h : c.arity = 0 <;> simp [existsLe, h]
@[simp] theorem arity_existsLe (c : NormalForm) : c.existsLe.arity = c.arity := by
  by_cases h : c.arity = 0 <;> simp [existsLe, h]
@[simp] theorem pref_forallLe (c : NormalForm) : c.forallLe.pref = c.pref := by
  by_cases h : c.arity = 0 <;> simp [forallLe, h]
@[simp] theorem arity_forallLe (c : NormalForm) : c.forallLe.arity = c.arity := by
  by_cases h : c.arity = 0 <;> simp [forallLe, h]

theorem primrec_existsLt : Primrec existsLt := by
  have hbc := Primrec.ite (Primrec.eq.comp primrec_arity (const 1)) (const idCode)
    (const Code.right)
  have hmc := Primrec.ite (Primrec.eq.comp primrec_arity (const 1)) (const Code.right)
    (const (Code.pair (.comp .left .left) .right))
  have hs' := nat_iterate (QuantifierPrefix.primrec_depth.comp primrec_pref)
    ((QuantifierPrefix.primrec_startsExists.comp primrec_pref).pair (hbc.pair hmc))
    (primrec_stepBounded.comp snd).to₂
  have hmat := primrec₃_existsLtBase.comp
    (primrec_matrix.pair ((fst.comp (snd.comp hs')).pair (snd.comp (snd.comp hs'))))
  exact primrec₃_mk primrec_pref primrec_arity
    (Primrec.ite (Primrec.eq.comp primrec_arity (const 0)) primrec_matrix hmat)
theorem primrec_forallLt : Primrec forallLt :=
  Primrec.ite (Primrec.eq.comp primrec_arity (const 0)) .id
    (primrec_not.comp (primrec_existsLt.comp primrec_not))
theorem primrec_existsLe : Primrec existsLe :=
  Primrec.ite (Primrec.eq.comp primrec_arity (const 0)) .id
    (primrec₃_preimage primrec_existsLt primrec_arity (primrec_succLastCode.comp primrec_arity))
theorem primrec_forallLe : Primrec forallLe :=
  Primrec.ite (Primrec.eq.comp primrec_arity (const 0)) .id
    (primrec₃_preimage primrec_forallLt primrec_arity (primrec_succLastCode.comp primrec_arity))

theorem Valid.existsLt {Z : Set ℕ} {c : NormalForm} (hc : c.Valid Z) : c.existsLt.Valid Z := by
  rcases c with ⟨p, _ | _ | k, m⟩
  · exact hc
  · have hcv : ∀ y : ℕ, ValidDepth Z m p.depth y := fun y =>
      (validAux_eq_validDepth Z m p y) ▸ (valid_iff Z _).1 hc y
    change Valid Z ⟨p, 1, _⟩; rw [valid_iff]; intro t; rw [validAux_eq_validDepth]
    exact (valid_and_holds_stepBounded p.depth p.startsExists idCode .right t t id
      (eval_idCode Z.oracle t) (fun _ => by simp) hcv).1
  · have hcv : ∀ b : ℕ, ValidDepth Z m p.depth b := by simpa using valid_iff_validAux.1 hc
    change Valid Z ⟨p, k + 2, _⟩; rw [valid_iff]; intro xs; let q := encode xs
    rw [validAux_eq_validDepth]
    exact (valid_and_holds_stepBounded p.depth p.startsExists .right
      (.pair (.comp .left .left) .right) q q.unpair.2 (fun y => Nat.pair q.unpair.1 y)
      (by simp) (fun _ => by simp [Seq.seq, PFun.some_bind])
      (fun y => hcv (Nat.pair q.unpair.1 y))).1

@[simp] theorem Valid.evalTuple_existsLt {Z : Set ℕ} {c : NormalForm} {k : ℕ} (hc : c.Valid Z)
    (hk : c.arity = k + 1) (xs : ArityTuple k) (t : ℕ) :
    c.existsLt.EvalTuple Z (ArityTuple.snoc xs t) ↔
      ∃ y < t, c.EvalTuple Z (ArityTuple.snoc xs y) := by
  have hcv : ∀ b : ℕ, ValidDepth Z c.matrix c.pref.depth b := by
    have h := valid_iff_validAux.1 hc; simpa [hk] using h
  rcases k with _ | k
  · cases xs
    simpa [NormalForm.existsLt, evalTuple_iff_holdsCode, hk] using
      (valid_and_holds_stepBounded c.pref.depth c.pref.startsExists idCode .right t t id
        (eval_idCode Z.oracle t) (fun _ => by simp) hcv).2
  · simpa [NormalForm.existsLt, evalTuple_iff_holdsCode, hk] using
      (valid_and_holds_stepBounded c.pref.depth c.pref.startsExists .right
        (.pair (.comp .left .left) .right) (Nat.pair (encode xs) t) t
        (fun y => Nat.pair (encode xs) y) (by simp) (fun _ => by simp [Seq.seq, PFun.some_bind])
        (fun y => hcv (Nat.pair (encode xs) y))).2

theorem Valid.forallLt {Z : Set ℕ} {c : NormalForm} (hc : c.Valid Z) : c.forallLt.Valid Z := by
  by_cases h : c.arity = 0 <;> simp [NormalForm.forallLt, h, hc, hc.not.existsLt.not]

@[simp] theorem Valid.evalTuple_forallLt {Z : Set ℕ} {c : NormalForm} {k : ℕ} (hc : c.Valid Z)
    (hk : c.arity = k + 1) (xs : ArityTuple k) (t : ℕ) :
    c.forallLt.EvalTuple Z (ArityTuple.snoc xs t) ↔
      ∀ y < t, c.EvalTuple Z (ArityTuple.snoc xs y) := by
  classical
  rw [show c.forallLt = c.not.existsLt.not by simp [NormalForm.forallLt, hk],
    (hc.not.existsLt).evalTuple_not (by simp [hk]) (ArityTuple.snoc xs t),
    (hc.not).evalTuple_existsLt (by simpa using hk) xs t, not_exists]
  exact forall_congr' fun y => by
    rw [not_and, hc.evalTuple_not hk (ArityTuple.snoc xs y), Classical.not_not]

theorem Valid.existsLe {Z : Set ℕ} {c : NormalForm} (hc : c.Valid Z) : c.existsLe.Valid Z := by
  by_cases h0 : c.arity = 0
  · simpa [NormalForm.existsLe, h0] using hc
  · simpa [NormalForm.existsLe, h0] using
      hc.existsLt.preimage_of_forall h0 (exists_eval_succLastCode Z.oracle c.arity)

@[simp] theorem Valid.evalTuple_existsLe {Z : Set ℕ} {c : NormalForm} {k : ℕ} (hc : c.Valid Z)
    (hk : c.arity = k + 1) (xs : ArityTuple k) (t : ℕ) :
    c.existsLe.EvalTuple Z (ArityTuple.snoc xs t) ↔
      ∃ y ≤ t, c.EvalTuple Z (ArityTuple.snoc xs y) := by
  simp only [NormalForm.existsLe, hk, Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte,
    evalTuple_preimage (eval_succLastCode Z.oracle rfl xs t), hc.evalTuple_existsLt hk xs (t + 1),
    Nat.lt_succ_iff]

theorem Valid.forallLe {Z : Set ℕ} {c : NormalForm} (hc : c.Valid Z) : c.forallLe.Valid Z := by
  by_cases h0 : c.arity = 0
  · simpa [NormalForm.forallLe, h0] using hc
  · simpa [NormalForm.forallLe, h0] using
      hc.forallLt.preimage_of_forall (by simp [h0]) (exists_eval_succLastCode Z.oracle c.arity)

@[simp] theorem Valid.evalTuple_forallLe {Z : Set ℕ} {c : NormalForm} {k : ℕ} (hc : c.Valid Z)
    (hk : c.arity = k + 1) (xs : ArityTuple k) (t : ℕ) :
    c.forallLe.EvalTuple Z (ArityTuple.snoc xs t) ↔
      ∀ y ≤ t, c.EvalTuple Z (ArityTuple.snoc xs y) := by
  simp only [NormalForm.forallLe, hk, Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte,
    evalTuple_preimage (eval_succLastCode Z.oracle rfl xs t), hc.evalTuple_forallLt hk xs (t + 1),
    Nat.lt_succ_iff]

end TauCeti.ArithmeticalHierarchy.NormalForm
