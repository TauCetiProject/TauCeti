/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Computability.Simple.Restrained
public import TauCeti.Computability.SingleOracle.Primrec
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# The finite-injury construction of a low simple set

This file carries out Soare's finite-injury construction of a simple set `A` [S, VII.1.1] and
proves that it is simple. The construction has two families of requirements, in the priority
order `N_0, P_0, N_1, P_1, …`:

* the positive requirement `P_i`: if `W_i` is infinite then `A` meets `W_i`;
* the negative requirement `N_e`: if `Φ_{e,s}^{A_s}(e)` converges at infinitely many stages `s`,
  then `Φ_e^A(e)` converges.

Here `Φ_{e,s}^{A_s}(e)` is the run `diagRun` of the oracle program numbered `e` on the input `e`
with fuel `s` against the finite set `A_s`, answering `1` on `A_s` and `0` outside it.

The construction is the simple-set construction `TauCeti.RestrainedSimple.stage` in which the
restraint `r(e, s)` of `N_e` is the use `diagUse` of `Φ_{e,s}^{A_s}(e)`, or `0` when this run
fails. That construction already supplies coinfiniteness and the bound of `e` injuries to `N_e`.
This file adds what depends on the diagonal restraints:

* the restraints are primitive recursive, so `A` is c.e. (`TauCeti.rePred_mem_lowSimpleSet`);
* after the last injury a convergent computation `Φ_{e,s}^{A_s}(e)` is preserved forever, so the
  diagonal stage computations and the restraints are eventually constant
  (`TauCeti.LowSimple.exists_eventually_diagRun_eq`);
* hence every positive requirement is met and `A` is simple (`TauCeti.simple_lowSimpleSet`).

Lowness of `A`, which the negative requirements are designed for, is not proved in this file.

## Main definitions

* `TauCeti.LowSimple.diagRun`, `TauCeti.LowSimple.diagUse`: the diagonal stage computation
  `Φ_{e,s}^D(e)` against a finite set `D`, and its use. Both are primitive recursive in the binary
  code of `D` (`TauCeti.LowSimple.primrec_diagRun`).
* `TauCeti.lowSimpleSet`: the constructed set, the limit of the stages
  `TauCeti.RestrainedSimple.stage TauCeti.LowSimple.diagUse`.

## References

* R. I. Soare, *Recursively Enumerable Sets and Degrees*, Springer, 1987, Theorem VII.1.1.
-/

public section

open Filter TauCeti.Enumeration TauCeti.Priority TauCeti.RestrainedSimple

namespace TauCeti

namespace LowSimple

/-- The **diagonal stage computation** `Φ_{e,s}^D(e)`: the run of the oracle program numbered `e`
on the input `e` with fuel `s`, against the finite set `D` answering `1` on `D` and `0` outside
it. A run with fuel `s` only succeeds on inputs below `s`, so it fails for `e ≥ s`, and its use is
at most `s`. -/
def diagRun (D : Finset ℕ) (s e : ℕ) : Option Oracle.Single.Code.Halt :=
  Oracle.Single.Code.evaln (fun z => some (if z ∈ D then 1 else 0)) s
    (Denumerable.ofNat Oracle.Single.Code e) e

/-- Unfolding `diagRun`. -/
theorem diagRun_def (D : Finset ℕ) (s e : ℕ) :
    diagRun D s e = Oracle.Single.Code.evaln (fun z => some (if z ∈ D then 1 else 0)) s
      (Denumerable.ofNat Oracle.Single.Code e) e :=
  (rfl)

/-- The use of the diagonal stage computation `Φ_{e,s}^D(e)`, or `0` when it fails. -/
def diagUse (D : Finset ℕ) (s e : ℕ) : ℕ :=
  ((diagRun D s e).map Oracle.Single.Code.Halt.use).getD 0

/-- The use of a convergent diagonal stage computation is the use of its run. -/
theorem diagUse_eq_of_diagRun_eq_some {D : Finset ℕ} {s e : ℕ} {d : Oracle.Single.Code.Halt}
    (h : diagRun D s e = some d) : diagUse D s e = d.use := by
  simp [diagUse, h]

/-- The use of a failed diagonal stage computation is `0`. -/
theorem diagUse_eq_zero_of_diagRun_eq_none {D : Finset ℕ} {s e : ℕ} (h : diagRun D s e = none) :
    diagUse D s e = 0 := by
  simp [diagUse, h]

end LowSimple

open LowSimple

/-- **Soare's low simple set**: the limit of the stages of the simple-set construction whose
negative requirements restrain the uses `LowSimple.diagUse` of the diagonal stage computations.
It is simple (`TauCeti.simple_lowSimpleSet`); its lowness is not proved in this file. -/
def lowSimpleSet : Set ℕ :=
  stageLimit (stage diagUse)

/-- The constructed set is the limit of the stages. -/
theorem lowSimpleSet_eq_stageLimit : lowSimpleSet = stageLimit (stage diagUse) :=
  (rfl)

/-! ### Effectivity -/

namespace LowSimple

open Primrec

/-- The diagonal stage computation `Φ_{e,s}^D(e)`, its output and use or its failure, is primitive
recursive in the binary code of `D`, the stage `s` and the index `e`. -/
theorem primrec_diagRun :
    Primrec fun q : ℕ × ℕ × ℕ => diagRun (Finset.equivBitIndices q.1) q.2.1 q.2.2 := by
  have hargs : Primrec fun q : ℕ × ℕ × ℕ =>
      (q.1, q.2.1, Denumerable.ofNat Oracle.Single.Code q.2.2, q.2.2) :=
    fst.pair ((fst.comp snd).pair (((Primrec.ofNat Oracle.Single.Code).comp (snd.comp snd)).pair
      (snd.comp snd)))
  exact (Oracle.Single.Code.primrec_evaln_equivBitIndices.comp hargs).of_eq fun q => by
    rw [diagRun]

/-- The use of the diagonal stage computation is primitive recursive in the binary code of the
finite set, the stage and the index. -/
theorem primrec_diagUse :
    Primrec fun q : ℕ × ℕ × ℕ => diagUse (Finset.equivBitIndices q.1) q.2.1 q.2.2 := by
  have huse : Primrec fun q : ℕ × ℕ × ℕ =>
      (diagRun (Finset.equivBitIndices q.1) q.2.1 q.2.2).map Oracle.Single.Code.Halt.use :=
    option_map primrec_diagRun (Oracle.Single.Code.Halt.primrec_use.comp snd).to₂
  exact option_getD.comp huse (const 0)

end LowSimple

/-- The constructed set is c.e. -/
theorem rePred_mem_lowSimpleSet : REPred (· ∈ lowSimpleSet) :=
  rePred_mem_stageLimit_stage primrec_diagUse

/-! ### Preservation -/

namespace LowSimple

/-- **Preservation.** If `N_e` is not injured at stage `s + 1`, a convergent diagonal stage
computation `Φ_{e,s}^{A_s}(e)` is still convergent at stage `s + 1`, with the same output and
use. -/
theorem diagRun_succ_eq_some {e s : ℕ} {d : Oracle.Single.Code.Halt}
    (hd : diagRun (stage diagUse s) s e = some d)
    (hinj : injuriesAt (stage diagUse) (restraint diagUse) e s = ∅) :
    diagRun (stage diagUse (s + 1)) (s + 1) e = some d := by
  rw [diagRun_def] at hd ⊢
  refine Oracle.Single.Code.evaln_eq_some_of_eqOn
    (Oracle.Single.Code.evaln_mono s.le_succ hd) fun z hz => ?_
  -- a number below the use that entered would injure `N_e`
  have hzs : z ∈ stage diagUse (s + 1) ↔ z ∈ stage diagUse s := by
    refine ⟨fun hz' => by_contra fun hzs => ?_,
      fun hzs => monotone_stage diagUse s.le_succ hzs⟩
    have : z ∈ injuriesAt (stage diagUse) (restraint diagUse) e s := mem_injuriesAt.2
      ⟨hz', hzs, _, restraint_eq_some_iff.2 rfl, by
        rw [diagUse_eq_of_diagRun_eq_some ((diagRun_def _ _ _).trans hd)]
        exact (Set.mem_Iio.1 hz).le⟩
    simp [hinj] at this
  simp [hzs]

/-- **The diagonal stage computations stabilize.** For each `e`, the run `Φ_{e,s}^{A_s}(e)` is
eventually constant: either it eventually fails forever, or from some stage on it converges
with a fixed output and use. -/
theorem exists_eventually_diagRun_eq (e : ℕ) :
    ∃ o, ∀ᶠ s in atTop, diagRun (stage diagUse s) s e = o := by
  obtain ⟨s₀, hs₀⟩ := (finite_injurySet_iff_eventually_eq_empty (monotone_stage diagUse)).1
    (finite_injurySet_and_ncard_le e).1
  by_cases h : ∃ s ≥ s₀, (diagRun (stage diagUse s) s e).isSome
  · obtain ⟨s₁, hs₁, hsome⟩ := h
    obtain ⟨d, hd⟩ := Option.isSome_iff_exists.1 hsome
    refine ⟨some d, eventually_atTop.2 ⟨s₁, fun t ht => ?_⟩⟩
    induction t, ht using Nat.le_induction with
    | base => exact hd
    | succ t ht ih => exact diagRun_succ_eq_some ih (hs₀ t (hs₁.trans ht))
  · push Not at h
    exact ⟨none, eventually_atTop.2 ⟨s₀, fun s hs => Option.not_isSome_iff_eq_none.1 (h s hs)⟩⟩

/-- **The restraints stabilize.** For each `e`, the restraint `r(e, s)` is eventually constant. -/
theorem exists_eventually_restraint_eq (e : ℕ) :
    ∃ b, ∀ᶠ s in atTop, restraint diagUse e s = some b := by
  obtain ⟨o, ho⟩ := exists_eventually_diagRun_eq e
  exact ⟨(o.map Oracle.Single.Code.Halt.use).getD 0, ho.mono fun s hs => by
    simp [diagUse, hs]⟩

end LowSimple

/-! ### Simplicity -/

/-- **The constructed set is simple.** -/
theorem simple_lowSimpleSet : lowSimpleSet.Simple :=
  simple_stageLimit_stage primrec_diagUse fun e =>
    let ⟨b, hb⟩ := exists_eventually_restraint_eq e
    ⟨b, hb.mono fun _ hs => (restraint_eq_some_iff.1 hs).le⟩

end TauCeti
