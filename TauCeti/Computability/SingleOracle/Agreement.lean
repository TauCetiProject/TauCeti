/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Computability.SingleOracle.Primrec
public import TauCeti.Computability.Enumeration.Stage
public import TauCeti.Computability.TuringDegree
public import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Filter.Finite

/-!
# Length of agreement and its restraint

Run a program `c` with fuel `k` against oracle answers `σ`, and compare it with a target function
`g : ℕ → ℕ`. The run **agrees** with `g` at `x` when it succeeds there with output `g x`. The
**length of agreement** is the first argument at which the run does not agree with `g`: either it
fails there, or it succeeds with another output. A run at fuel `k` fails on every input at or above
`k`, so the length of agreement is at most `k`.

The **agreement restraint** is the largest stage use (`TauCeti.Oracle.Single.Code.stageUse`) of the
runs at the arguments up to *and including* the length of agreement, a failed run counting as use
`0`. Including the first disagreement protects a run that succeeds there with a wrong output, as
well as the agreeing runs below it.

In Sacks's constructions the answers are those of the stage `A s` of a set being built, the fuel is
the stage `s`, and the target is the characteristic function of the stage `C s` of a c.e. set.
Then the length of agreement and the agreement restraint are Soare's `ℓ(e, s)` and `r(e, s)` for
the requirement `C ≠ Φ_e^A`, and the restraint protects the numbers up to `r(e, s)`, inclusive.

## Preservation

If the answers do not change at or below the agreement restraint, every successful run at an
argument up to and including the length of agreement succeeds again with the same output and use
at any larger fuel. This needs no hypothesis on the target. If in addition the target does not
change below the length of agreement, the agreement there persists, so neither the length of
agreement nor the restraint decreases. On an interval of stages where both conditions hold at every
step, the computations, the length of agreement and the restraint therefore all persist.

Absence of injury alone is not enough to iterate: a change of the target at a small argument can
shorten the length of agreement, so that the next restraint no longer covers the use of a
computation at a larger argument. What does iterate is a fixed prefix: if the target does not
change below `n` and `n` is at most the length of agreement, then it stays so, and the computations
up to and including `n` persist.

## Effectivity

The length of agreement and the agreement restraint are primitive recursive in the fuel and the
program, uniformly in a parameter on which the answers and the target depend primitive
recursively. In particular they are primitive recursive in the binary codes of a finite stage
`A s` and a finite target stage `C s`, which makes them usable in computable stage constructions.

## Limits of stages

When the answers and the target are the stages `A s` and `C s` of monotone enumerations, run with
fuel `s`, and the program computes the limit of `C` relative to the limit of `A` below `n`, the use
principle makes the length of agreement eventually at least `n`.

## Main definitions

* `TauCeti.Oracle.Single.Code.AgreesAt`: a run succeeds with the target value.
* `TauCeti.Oracle.Single.Code.agreementLength`: the first argument without agreement.
* `TauCeti.Oracle.Single.Code.agreementRestraint`: the largest stage use up to and including the
  length of agreement.

## Main results

* `TauCeti.Oracle.Single.Code.agreementLength_eq_iff`,
  `TauCeti.Oracle.Single.Code.le_agreementLength_iff`,
  `TauCeti.Oracle.Single.Code.agreementLength_le`: the length of agreement is the first argument
  without agreement, and is at most the fuel.
* `TauCeti.Oracle.Single.Code.agreementRestraint_le_iff`,
  `TauCeti.Oracle.Single.Code.use_le_agreementRestraint`: the restraint is the least bound of the
  stage uses up to and including the length of agreement.
* `TauCeti.Oracle.Single.Code.evaln_eq_some_of_eqOn_agreementRestraint`: **preservation of
  computations** under a change of answers above the restraint.
* `TauCeti.Oracle.Single.Code.agreesAt_of_eqOn_agreementRestraint`,
  `TauCeti.Oracle.Single.Code.agreementLength_le_of_eqOn_agreementRestraint`,
  `TauCeti.Oracle.Single.Code.agreementRestraint_le_of_eqOn_agreementRestraint`: preservation of
  agreement, of the length of agreement and of the restraint when the target is also unchanged.
* `TauCeti.Oracle.Single.Code.evaln_eq_some_of_forall_Ico`,
  `TauCeti.Oracle.Single.Code.agreementLength_le_of_forall_Ico`,
  `TauCeti.Oracle.Single.Code.agreementRestraint_le_of_forall_Ico`: the same along an interval of
  stages.
* `TauCeti.Oracle.Single.Code.le_agreementLength_of_forall_Ico`,
  `TauCeti.Oracle.Single.Code.evaln_eq_some_of_forall_Ico_of_le`: persistence of a prefix of
  agreement, and of the computations up to and including it, along an interval of stages where the
  target does not change below the prefix.
* `TauCeti.Oracle.Single.Code.primrec_agreementLength`,
  `TauCeti.Oracle.Single.Code.primrec_agreementRestraint`, and their specializations
  `TauCeti.Oracle.Single.Code.primrec_agreementLength_equivBitIndices`,
  `TauCeti.Oracle.Single.Code.primrec_agreementRestraint_equivBitIndices` to binary-coded finite
  sets: the length of agreement and the restraint are primitive recursive.
* `TauCeti.Oracle.Single.Code.eventually_le_agreementLength_of_eval_eq`: if, relative to the limit
  of monotone stages `A`, the program computes the limit of monotone stages `C` below `n`, then
  the length of agreement against the stages is eventually at least `n`.

## References

* R. I. Soare, *Recursively Enumerable Sets and Degrees*, Springer, 1987, Chapter VII.3, in
  particular the definitions of `ℓ(e, s)` and `r(e, s)` and the Remark on p. 122.
-/

public section

open Set

namespace TauCeti.Oracle.Single.Code

variable {σ τ : ℕ → Option ℕ} {k k' : ℕ} {c : Code} {g g' : ℕ → ℕ} {x : ℕ} {d : Halt}

/-! ### Agreement and its length -/

/-- The run of `c` on `x` with fuel `k` against the answers `σ` **agrees** with the target `g` at
`x` when it succeeds with output `g x`. -/
def AgreesAt (σ : ℕ → Option ℕ) (k : ℕ) (c : Code) (g : ℕ → ℕ) (x : ℕ) : Prop :=
  (evaln σ k c x).map Halt.output = some (g x)

instance (σ : ℕ → Option ℕ) (k : ℕ) (c : Code) (g : ℕ → ℕ) : DecidablePred (AgreesAt σ k c g) :=
  fun x => inferInstanceAs (Decidable ((evaln σ k c x).map Halt.output = some (g x)))

/-- A run agrees with the target when it succeeds with the target value. -/
theorem agreesAt_iff : AgreesAt σ k c g x ↔ ∃ d, evaln σ k c x = some d ∧ d.output = g x := by
  simp [AgreesAt]

/-- A successful run agrees with the target exactly when its output is the target value. -/
theorem agreesAt_iff_of_evaln_eq_some (h : evaln σ k c x = some d) :
    AgreesAt σ k c g x ↔ d.output = g x := by
  simp [AgreesAt, h]

/-- A failed run does not agree with the target. -/
theorem not_agreesAt_of_evaln_eq_none (h : evaln σ k c x = none) : ¬AgreesAt σ k c g x := by
  simp [AgreesAt, h]

/-- No run agrees with the target at an argument at or above its fuel. -/
theorem not_agreesAt_of_le (h : k ≤ x) : ¬AgreesAt σ k c g x :=
  not_agreesAt_of_evaln_eq_none (evaln_eq_none_of_le h)

/-- The **length of agreement**: the first argument at which the run of `c` with fuel `k` against
the answers `σ` does not agree with the target `g`. It is at most `k`. -/
def agreementLength (σ : ℕ → Option ℕ) (k : ℕ) (c : Code) (g : ℕ → ℕ) : ℕ :=
  Nat.find (⟨k, not_agreesAt_of_le le_rfl⟩ : ∃ x, ¬AgreesAt σ k c g x)

/-- The length of agreement is the first argument without agreement. -/
theorem agreementLength_eq_iff {n : ℕ} :
    agreementLength σ k c g = n ↔ ¬AgreesAt σ k c g n ∧ ∀ x < n, AgreesAt σ k c g x := by
  simp [agreementLength, Nat.find_eq_iff]

/-- The run agrees with the target below `n` exactly when `n` is at most the length of
agreement. -/
theorem le_agreementLength_iff {n : ℕ} :
    n ≤ agreementLength σ k c g ↔ ∀ x < n, AgreesAt σ k c g x := by
  simp [agreementLength, Nat.le_find_iff]

/-- The run agrees with the target below the length of agreement. -/
theorem agreesAt_of_lt_agreementLength (hx : x < agreementLength σ k c g) : AgreesAt σ k c g x :=
  le_agreementLength_iff.1 le_rfl x hx

/-- The run does not agree with the target at the length of agreement. -/
theorem not_agreesAt_agreementLength : ¬AgreesAt σ k c g (agreementLength σ k c g) :=
  (agreementLength_eq_iff.1 rfl).1

/-- The length of agreement is at most the fuel. -/
theorem agreementLength_le : agreementLength σ k c g ≤ k :=
  Nat.find_min' _ (not_agreesAt_of_le le_rfl)

/-! ### The agreement restraint -/

/-- The **agreement restraint**: the largest stage use of the runs of `c` with fuel `k` against
the answers `σ` at the arguments up to and including the length of agreement with `g`. A failed
run counts as use `0`. -/
def agreementRestraint (σ : ℕ → Option ℕ) (k : ℕ) (c : Code) (g : ℕ → ℕ) : ℕ :=
  (Finset.range (agreementLength σ k c g + 1)).sup (stageUse σ k c)

/-- The agreement restraint is the finite maximum of the uses, including the run at the first
disagreement. -/
theorem agreementRestraint_def (σ : ℕ → Option ℕ) (k : ℕ) (c : Code) (g : ℕ → ℕ) :
    agreementRestraint σ k c g =
      (Finset.range (agreementLength σ k c g + 1)).sup (stageUse σ k c) :=
  (rfl)

/-- Equal agreement lengths and equal runs up to and including that length give equal
agreement restraints. The targets may differ. -/
theorem agreementRestraint_eq_of_evaln_eq
    (hlength : agreementLength σ k c g = agreementLength τ k' c g')
    (hruns : ∀ x ≤ agreementLength σ k c g, evaln σ k c x = evaln τ k' c x) :
    agreementRestraint σ k c g = agreementRestraint τ k' c g' := by
  simp only [agreementRestraint_def, ← hlength]
  apply Finset.sup_congr rfl
  intro x hx
  exact stageUse_congr (hruns x (Nat.le_of_lt_succ (Finset.mem_range.1 hx)))

/-- The agreement restraint is at most `b` exactly when every stage use up to and including the
length of agreement is. -/
theorem agreementRestraint_le_iff {b : ℕ} :
    agreementRestraint σ k c g ≤ b ↔ ∀ x ≤ agreementLength σ k c g, stageUse σ k c x ≤ b := by
  simp [agreementRestraint]

/-- Every stage use up to and including the length of agreement is at most the agreement
restraint. -/
theorem stageUse_le_agreementRestraint (hx : x ≤ agreementLength σ k c g) :
    stageUse σ k c x ≤ agreementRestraint σ k c g :=
  agreementRestraint_le_iff.1 le_rfl x hx

/-- The use of a successful run up to and including the length of agreement is at most the
agreement restraint. -/
theorem use_le_agreementRestraint (hx : x ≤ agreementLength σ k c g)
    (hd : evaln σ k c x = some d) : d.use ≤ agreementRestraint σ k c g :=
  stageUse_eq_of_evaln_eq_some hd ▸ stageUse_le_agreementRestraint hx

/-- The agreement restraint is at most the fuel. -/
theorem agreementRestraint_le : agreementRestraint σ k c g ≤ k :=
  agreementRestraint_le_iff.2 fun _ _ => stageUse_le

/-! ### Preservation -/

/-- **Preservation of computations.** A successful run at an argument up to and including the
length of agreement succeeds with the same output and use at any larger fuel, against any answers
that agree with `σ` at and below the agreement restraint. Nothing is assumed about the target. -/
theorem evaln_eq_some_of_eqOn_agreementRestraint (hk : k ≤ k')
    (hστ : EqOn σ τ (Iic (agreementRestraint σ k c g))) (hx : x ≤ agreementLength σ k c g)
    (hd : evaln σ k c x = some d) : evaln τ k' c x = some d :=
  evaln_mono hk <| evaln_eq_some_of_eqOn hd <| hστ.mono fun _ hz =>
    (mem_Iio.1 hz).le.trans (use_le_agreementRestraint hx hd)

/-- **Preservation of agreement.** Under the hypotheses of
`evaln_eq_some_of_eqOn_agreementRestraint`, agreement below the length of agreement persists when
the target value there does not change. -/
theorem agreesAt_of_eqOn_agreementRestraint (hk : k ≤ k')
    (hστ : EqOn σ τ (Iic (agreementRestraint σ k c g))) (hx : x < agreementLength σ k c g)
    (hg : g' x = g x) : AgreesAt τ k' c g' x := by
  obtain ⟨d, hd, hdx⟩ := agreesAt_iff.1 (agreesAt_of_lt_agreementLength hx)
  exact agreesAt_iff.2
    ⟨d, evaln_eq_some_of_eqOn_agreementRestraint hk hστ hx.le hd, hdx.trans hg.symm⟩

/-- The length of agreement does not decrease when the fuel does not decrease, the answers do not
change at or below the agreement restraint, and the target does not change below the length of
agreement. -/
theorem agreementLength_le_of_eqOn_agreementRestraint (hk : k ≤ k')
    (hστ : EqOn σ τ (Iic (agreementRestraint σ k c g)))
    (hg : ∀ x < agreementLength σ k c g, g' x = g x) :
    agreementLength σ k c g ≤ agreementLength τ k' c g' :=
  le_agreementLength_iff.2 fun x hx => agreesAt_of_eqOn_agreementRestraint hk hστ hx (hg x hx)

/-- Under the hypotheses of `agreementLength_le_of_eqOn_agreementRestraint`, the agreement
restraint does not decrease either: every run it accounts for is preserved, at an argument still
up to and including the new length of agreement. -/
theorem agreementRestraint_le_of_eqOn_agreementRestraint (hk : k ≤ k')
    (hστ : EqOn σ τ (Iic (agreementRestraint σ k c g)))
    (hg : ∀ x < agreementLength σ k c g, g' x = g x) :
    agreementRestraint σ k c g ≤ agreementRestraint τ k' c g' := by
  refine agreementRestraint_le_iff.2 fun x hx => ?_
  cases hd : evaln σ k c x with
  | none => simp [stageUse_eq_zero_of_evaln_eq_none hd]
  | some d =>
    rw [stageUse_eq_of_evaln_eq_some hd]
    exact use_le_agreementRestraint
      (hx.trans (agreementLength_le_of_eqOn_agreementRestraint hk hστ hg))
      (evaln_eq_some_of_eqOn_agreementRestraint hk hστ hx hd)

/-! ### Preservation along an interval of stages -/

section Interval

variable {σ : ℕ → ℕ → Option ℕ} {g : ℕ → ℕ → ℕ} {s t : ℕ}

/-- Along stages `σ u`, `g u` run with fuel `u`, the length of agreement does not decrease on an
interval of stages where, at every step, the answers do not change at or below the agreement
restraint and the target does not change below the length of agreement. -/
theorem agreementLength_le_of_forall_Ico (hst : s ≤ t)
    (h : ∀ u ∈ Ico s t, EqOn (σ u) (σ (u + 1)) (Iic (agreementRestraint (σ u) u c (g u))) ∧
      ∀ x < agreementLength (σ u) u c (g u), g (u + 1) x = g u x) :
    agreementLength (σ s) s c (g s) ≤ agreementLength (σ t) t c (g t) := by
  induction t, hst using Nat.le_induction with
  | base => exact le_rfl
  | succ t hst ih =>
    have ⟨hστ, hg⟩ := h t ⟨hst, t.lt_succ_self⟩
    exact (ih fun u hu => h u ⟨hu.1, hu.2.trans t.lt_succ_self⟩).trans
      (agreementLength_le_of_eqOn_agreementRestraint t.le_succ hστ hg)

/-- Under the hypotheses of `agreementLength_le_of_forall_Ico`, the agreement restraint does not
decrease on the interval. -/
theorem agreementRestraint_le_of_forall_Ico (hst : s ≤ t)
    (h : ∀ u ∈ Ico s t, EqOn (σ u) (σ (u + 1)) (Iic (agreementRestraint (σ u) u c (g u))) ∧
      ∀ x < agreementLength (σ u) u c (g u), g (u + 1) x = g u x) :
    agreementRestraint (σ s) s c (g s) ≤ agreementRestraint (σ t) t c (g t) := by
  induction t, hst using Nat.le_induction with
  | base => exact le_rfl
  | succ t hst ih =>
    have ⟨hστ, hg⟩ := h t ⟨hst, t.lt_succ_self⟩
    exact (ih fun u hu => h u ⟨hu.1, hu.2.trans t.lt_succ_self⟩).trans
      (agreementRestraint_le_of_eqOn_agreementRestraint t.le_succ hστ hg)

/-- **Persistence of a prefix of agreement.** Along stages `σ u`, `g u` run with fuel `u`, if the
run agrees with the target below `n` at stage `s`, it still does at stage `t`, provided that at
every step in between the answers do not change at or below the agreement restraint and the target
does not change below `n`. The target may change at and above `n`. -/
theorem le_agreementLength_of_forall_Ico {n : ℕ} (hst : s ≤ t)
    (h : ∀ u ∈ Ico s t, EqOn (σ u) (σ (u + 1)) (Iic (agreementRestraint (σ u) u c (g u))) ∧
      ∀ x < n, g (u + 1) x = g u x)
    (hn : n ≤ agreementLength (σ s) s c (g s)) : n ≤ agreementLength (σ t) t c (g t) := by
  induction t, hst using Nat.le_induction with
  | base => exact hn
  | succ t hst ih =>
    have ⟨hστ, hg⟩ := h t ⟨hst, t.lt_succ_self⟩
    have ih := ih fun u hu => h u ⟨hu.1, hu.2.trans t.lt_succ_self⟩
    exact le_agreementLength_iff.2 fun x hx =>
      agreesAt_of_eqOn_agreementRestraint t.le_succ hστ (hx.trans_le ih) (hg x hx)

/-- **Preservation on an interval of stages, below a fixed prefix.** Under the hypotheses of
`le_agreementLength_of_forall_Ico`, a successful run at stage `s` at an argument up to and
including `n` is a successful run at stage `t`, with the same output and use. -/
theorem evaln_eq_some_of_forall_Ico_of_le {n : ℕ} (hst : s ≤ t)
    (h : ∀ u ∈ Ico s t, EqOn (σ u) (σ (u + 1)) (Iic (agreementRestraint (σ u) u c (g u))) ∧
      ∀ x < n, g (u + 1) x = g u x)
    (hn : n ≤ agreementLength (σ s) s c (g s)) (hx : x ≤ n) (hd : evaln (σ s) s c x = some d) :
    evaln (σ t) t c x = some d := by
  induction t, hst using Nat.le_induction with
  | base => exact hd
  | succ t hst ih =>
    have h' : ∀ u ∈ Ico s t, _ := fun u hu => h u ⟨hu.1, hu.2.trans t.lt_succ_self⟩
    exact evaln_eq_some_of_eqOn_agreementRestraint t.le_succ (h t ⟨hst, t.lt_succ_self⟩).1
      (hx.trans (le_agreementLength_of_forall_Ico hst h' hn)) (ih h')

/-- **Preservation on an interval of stages.** Under the hypotheses of
`agreementLength_le_of_forall_Ico`, a successful run at stage `s` at an argument up to and
including the length of agreement is a successful run at stage `t`, with the same output and
use. -/
theorem evaln_eq_some_of_forall_Ico (hst : s ≤ t)
    (h : ∀ u ∈ Ico s t, EqOn (σ u) (σ (u + 1)) (Iic (agreementRestraint (σ u) u c (g u))) ∧
      ∀ x < agreementLength (σ u) u c (g u), g (u + 1) x = g u x)
    (hx : x ≤ agreementLength (σ s) s c (g s)) (hd : evaln (σ s) s c x = some d) :
    evaln (σ t) t c x = some d :=
  -- the length of agreement at stage `s` is a prefix on which the target does not change
  evaln_eq_some_of_forall_Ico_of_le hst (fun u hu => ⟨(h u hu).1, fun y hy => (h u hu).2 y
    (hy.trans_le (agreementLength_le_of_forall_Ico hu.1 fun v hv =>
      h v ⟨hv.1, hv.2.trans hu.2⟩))⟩) le_rfl hx hd

end Interval

/-! ### Primitive recursiveness -/

section Primrec

open Primrec

variable {α : Type*} [Primcodable α] {σ : α → ℕ → Option ℕ} {g : α → ℕ → ℕ}

/-- Agreement is primitive recursive, uniformly in a parameter `a` on which the answers `σ a` and
the target `g a` depend primitive recursively, and in the fuel, the program and the argument. -/
theorem primrecPred_agreesAt (hσ : Primrec₂ σ) (hg : Primrec₂ g) :
    PrimrecPred fun p : (α × ℕ × Code) × ℕ => AgreesAt (σ p.1.1) p.1.2.1 p.1.2.2 (g p.1.1) p.2 :=
  Primrec.eq.comp (option_map ((primrec_evaln hσ).comp
      ((fst.comp fst).pair ((fst.comp (snd.comp fst)).pair ((snd.comp (snd.comp fst)).pair snd))))
      (Halt.primrec_output.comp snd).to₂)
    (option_some.comp (hg.comp (fst.comp fst) snd)) |>.of_eq fun _ => by simp [AgreesAt]

/-- The length of agreement is primitive recursive, uniformly in a parameter `a` on which the
answers `σ a` and the target `g a` depend primitive recursively, and in the fuel and the
program. -/
theorem primrec_agreementLength (hσ : Primrec₂ σ) (hg : Primrec₂ g) :
    Primrec fun p : α × ℕ × Code => agreementLength (σ p.1) p.2.1 p.2.2 (g p.1) := by
  have hagree := primrecPred_agreesAt hσ hg
  -- the graph: no agreement at `n`, and agreement at every argument below it
  have hagree' : PrimrecRel fun (x : ℕ) (p : α × ℕ × Code) =>
      AgreesAt (σ p.1) p.2.1 p.2.2 (g p.1) x :=
    hagree.comp (snd.pair fst)
  have hgraph : PrimrecRel fun (p : α × ℕ × Code) (n : ℕ) =>
      ¬AgreesAt (σ p.1) p.2.1 p.2.2 (g p.1) n ∧
        ∀ x ∈ List.range n, AgreesAt (σ p.1) p.2.1 p.2.2 (g p.1) x :=
    hagree.not.and (hagree'.forall_mem_list.comp (list_range.comp snd) fst)
  refine of_graph ⟨fun p => p.2.1, fst.comp snd, fun p => ?_⟩
    (hgraph.of_eq fun p n => by simp [agreementLength_eq_iff])
  simpa using agreementLength_le

/-- The agreement restraint is primitive recursive, uniformly in a parameter `a` on which the
answers `σ a` and the target `g a` depend primitive recursively, and in the fuel and the
program. -/
theorem primrec_agreementRestraint (hσ : Primrec₂ σ) (hg : Primrec₂ g) :
    Primrec fun p : α × ℕ × Code => agreementRestraint (σ p.1) p.2.1 p.2.2 (g p.1) := by
  -- the largest stage use over `0, …, agreementLength`, as a fold of `max`
  have huse : Primrec₂ fun (p : α × ℕ × Code) (x : ℕ) => stageUse (σ p.1) p.2.1 p.2.2 x :=
    (primrec_stageUse hσ).comp ((fst.comp fst).pair ((fst.comp (snd.comp fst)).pair
      ((snd.comp (snd.comp fst)).pair snd)))
  refine (list_foldr (list_range.comp (Primrec.succ.comp (primrec_agreementLength hσ hg))) (const 0)
    (nat_max.comp (huse.comp fst (fst.comp snd)) (snd.comp snd)).to₂).of_eq fun p => ?_
  -- the fold of `max` is the supremum over the image of the range under `stageUse`
  dsimp only
  rw [agreementRestraint, ← List.foldr_map, ← Nat.bot_eq_zero, List.foldr_sup_eq_sup_toFinset]
  exact (congrArg (Finset.sup · id) (by ext; simp)).trans
    (Finset.sup_image (Finset.range _) (stageUse (σ p.1) p.2.1 p.2.2) id)

/-- The length of agreement of a run against a finite set, with a finite set as target, is
primitive recursive in their binary codes, the fuel and the program. -/
theorem primrec_agreementLength_equivBitIndices :
    Primrec fun p : (ℕ × ℕ) × ℕ × Code =>
      agreementLength (setAnswers (Finset.equivBitIndices p.1.1 : Set ℕ)) p.2.1 p.2.2
        ((Finset.equivBitIndices p.1.2 : Set ℕ).indicator 1) :=
  primrec_agreementLength (primrec₂_setAnswers_equivBitIndices.comp (fst.comp fst) snd).to₂
    (indicator_equivBitIndices.comp (snd.comp fst) snd).to₂

/-- The agreement restraint of a run against a finite set, with a finite set as target, is
primitive recursive in their binary codes, the fuel and the program. -/
theorem primrec_agreementRestraint_equivBitIndices :
    Primrec fun p : (ℕ × ℕ) × ℕ × Code =>
      agreementRestraint (setAnswers (Finset.equivBitIndices p.1.1 : Set ℕ)) p.2.1 p.2.2
        ((Finset.equivBitIndices p.1.2 : Set ℕ).indicator 1) :=
  primrec_agreementRestraint (primrec₂_setAnswers_equivBitIndices.comp (fst.comp fst) snd).to₂
    (indicator_equivBitIndices.comp (snd.comp fst) snd).to₂

end Primrec

/-! ### Limits of stages -/

section Limit

open Filter TauCeti.Enumeration

variable {A C : ℕ → Finset ℕ}

/-- **Agreement eventually covers every prefix.** If the program `c`, relative to the limit of
monotone stages `A`, computes the characteristic function of the limit of monotone stages `C` below
`n`, then the length of agreement of `c` against `A s` with target `C s` and fuel `s` is eventually
at least `n`. -/
theorem eventually_le_agreementLength_of_eval_eq (hA : Monotone A) (hC : Monotone C) {n : ℕ}
    (heval : ∀ x < n, eval (stageLimit A).oracle c x = (stageLimit C).oracle x) :
    ∀ᶠ s in atTop, n ≤ agreementLength (setAnswers (A s)) s c ((C s : Set ℕ).indicator 1) := by
  -- each argument below `n` eventually agrees, by the use principle
  have hx : ∀ x ∈ Iio n, ∀ᶠ s in atTop,
      AgreesAt (setAnswers (A s)) s c ((C s : Set ℕ).indicator 1) x := by
    intro x hxn
    have hmem : (stageLimit C).indicator 1 x ∈ eval (stageLimit A).oracle c x := by
      simp [heval x hxn]
    obtain ⟨k, d, hd, hout⟩ := exists_evaln_eq_some_of_mem_eval (σ := setAnswers (stageLimit A))
      (fun z y hy => by simpa [Part.mem_some_iff, eq_comm] using hy) hmem
    obtain ⟨sA, hsA⟩ := finite_prefix_stabilizes hA d.use
    obtain ⟨sC, hsC⟩ := finite_prefix_stabilizes hC (x + 1)
    filter_upwards [eventually_ge_atTop (max k (max sA sC))] with s hs
    simp only [max_le_iff] at hs
    refine agreesAt_iff.2 ⟨d, evaln_mono hs.1 (evaln_eq_some_of_eqOn hd ?_), ?_⟩
    · exact eqOn_setAnswers_iff.2 fun z hz => (hsA s hs.2.1 z hz).symm
    · exact hout.trans (indicator_eq_indicator (hsC s hs.2.2 x x.lt_succ_self).symm rfl)
  filter_upwards [(finite_Iio n).eventually_all.2 hx] with s hs
  exact le_agreementLength_iff.2 fun x hx => hs x hx

end Limit

end TauCeti.Oracle.Single.Code
