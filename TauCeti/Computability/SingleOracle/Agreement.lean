/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Computability.SingleOracle.Evaln

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
computation at a larger argument.

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

/-- The agreement restraint is at most `b` exactly when every stage use up to and including the
length of agreement is. -/
theorem agreementRestraint_le_iff {b : ℕ} :
    agreementRestraint σ k c g ≤ b ↔ ∀ x ≤ agreementLength σ k c g, stageUse σ k c x ≤ b := by
  simp [agreementRestraint, Nat.lt_succ_iff]

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

/-- **Preservation on an interval of stages.** Under the hypotheses of
`agreementLength_le_of_forall_Ico`, a successful run at stage `s` at an argument up to and
including the length of agreement is a successful run at stage `t`, with the same output and
use. -/
theorem evaln_eq_some_of_forall_Ico (hst : s ≤ t)
    (h : ∀ u ∈ Ico s t, EqOn (σ u) (σ (u + 1)) (Iic (agreementRestraint (σ u) u c (g u))) ∧
      ∀ x < agreementLength (σ u) u c (g u), g (u + 1) x = g u x)
    (hx : x ≤ agreementLength (σ s) s c (g s)) (hd : evaln (σ s) s c x = some d) :
    evaln (σ t) t c x = some d := by
  induction t, hst using Nat.le_induction with
  | base => exact hd
  | succ t hst ih =>
    have h' : ∀ u ∈ Ico s t, _ := fun u hu => h u ⟨hu.1, hu.2.trans t.lt_succ_self⟩
    exact evaln_eq_some_of_eqOn_agreementRestraint t.le_succ (h t ⟨hst, t.lt_succ_self⟩).1
      (hx.trans (agreementLength_le_of_forall_Ico hst h')) (ih h')

end Interval

end TauCeti.Oracle.Single.Code
