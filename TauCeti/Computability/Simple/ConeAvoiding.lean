/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Computability.Simple.Restrained
public import TauCeti.Computability.Priority.Agreement.Stabilization
public import TauCeti.Computability.Enumeration.Domain

/-!
# A simple set avoiding the cone above a noncomputable c.e. set

This file carries out Sacks's finite-injury construction of a simple set `A` with `C ≰_T A`, for a
given noncomputable c.e. set `C` [S, VII.3.1]. The requirements are, in the priority order
`N_0, P_0, N_1, P_1, …`:

* the positive requirement `P_i`: if `W_i` is infinite then `A` meets `W_i`;
* the negative requirement `N_e`: `C ≠ Φ_e^A`.

The target `C` is given by increasing finite stages `C s` whose binary codes are primitive
recursive, for instance the stages `Nat.Partrec.Code.domStage` of the domain of a program. The
construction is the simple-set construction `TauCeti.RestrainedSimple.stage` in which `N_e` holds
the agreement restraint `r(e, s)` of `Φ_e` against the stage `A_s`, with fuel `s` and target `C s`
(`TauCeti.Oracle.Single.Code.agreementRestraint`): the largest use of the computations up to and
including the length of agreement `ℓ(e, s)`. The simple-set construction supplies coinfiniteness
and the bound of `e` injuries to `N_e`. This file adds what depends on the agreement restraints:

* the restraints are primitive recursive, so `A` is c.e.
  (`TauCeti.rePred_mem_coneAvoidingSet`);
* since `N_e` is injured only finitely often, Soare's Lemma 1 turns `Φ_e^A = C` into a decision
  procedure for `C`, so every negative requirement is met when `C` is noncomputable
  (`TauCeti.ConeAvoiding.eval_ne_oracle`);
* finite injury and the limiting disagreement make the restraints eventually constant
  (`TauCeti.ConeAvoiding.exists_eventually_agreementRestraint_eq`), so every positive requirement
  is met and `A` is simple (`TauCeti.simple_coneAvoidingSet`).

## Main definitions

* `TauCeti.ConeAvoiding.agreementRestraint`: the restraint of `N_e` at stage `s` when the current
  finite set is `D`.
* `TauCeti.coneAvoidingSet`: the constructed set, the limit of the stages
  `TauCeti.RestrainedSimple.stage (TauCeti.ConeAvoiding.agreementRestraint C)`.

## Main results

* `TauCeti.simple_coneAvoidingSet`, `TauCeti.not_turingReducible_coneAvoidingSet`: the constructed
  set is simple, and the limit of `C` is not Turing reducible to it.
* `TauCeti.exists_simple_not_turingReducible`: **Sacks's theorem** [S, VII.3.1]. For every
  noncomputable c.e. set `C` there is a simple set `A` with `C ≰_T A`.
* `TauCeti.exists_simple_not_turingReducible_code`: the same, with an ordinary program whose
  domain is `A`.

## References

* R. I. Soare, *Recursively Enumerable Sets and Degrees*, Springer, 1987, Theorem VII.3.1.
-/

public section

open Filter TauCeti.Enumeration TauCeti.Priority TauCeti.RestrainedSimple

namespace TauCeti

namespace ConeAvoiding

/-- The restraint of the negative requirement `N_e : C ≠ Φ_e^A` at stage `s` when the current
finite set is `D`: the agreement restraint of the oracle program numbered `e` against the answers
of `D`, with fuel `s` and target the characteristic function of `C s`. It is at most `s`. -/
noncomputable def agreementRestraint (C : ℕ → Finset ℕ) (D : Finset ℕ) (s e : ℕ) : ℕ :=
  Oracle.Single.Code.agreementRestraint (Oracle.Single.Code.setAnswers D) s
    (Denumerable.ofNat Oracle.Single.Code e) ((C s : Set ℕ).indicator 1)

/-- Unfolding `ConeAvoiding.agreementRestraint`. -/
theorem agreementRestraint_def (C : ℕ → Finset ℕ) (D : Finset ℕ) (s e : ℕ) :
    agreementRestraint C D s e =
      Oracle.Single.Code.agreementRestraint (Oracle.Single.Code.setAnswers D) s
        (Denumerable.ofNat Oracle.Single.Code e) ((C s : Set ℕ).indicator 1) :=
  (rfl)

end ConeAvoiding

open ConeAvoiding

/-- **Sacks's simple set avoiding the cone above the limit of `C`**: the limit of the stages of the
simple-set construction whose negative requirements hold the agreement restraints
`ConeAvoiding.agreementRestraint C`. It is simple and does not compute the limit of `C` when `C`
has primitive recursive increasing stages and a noncomputable limit
(`TauCeti.simple_coneAvoidingSet`, `TauCeti.not_turingReducible_coneAvoidingSet`). -/
noncomputable def coneAvoidingSet (C : ℕ → Finset ℕ) : Set ℕ :=
  stageLimit (stage (agreementRestraint C))

/-- The constructed set is the limit of the stages. -/
theorem coneAvoidingSet_eq_stageLimit (C : ℕ → Finset ℕ) :
    coneAvoidingSet C = stageLimit (stage (agreementRestraint C)) :=
  (rfl)

variable {C : ℕ → Finset ℕ}

/-! ### Effectivity -/

namespace ConeAvoiding

open Primrec

/-- The restraint is primitive recursive in the binary code of the current finite set, the stage and
the index, when the binary codes of the target stages are primitive recursive. -/
theorem primrec_agreementRestraint (hC : Primrec fun s => Finset.equivBitIndices.symm (C s)) :
    Primrec fun q : ℕ × ℕ × ℕ =>
      agreementRestraint C (Finset.equivBitIndices q.1) q.2.1 q.2.2 := by
  have hargs : Primrec fun q : ℕ × ℕ × ℕ =>
      ((q.1, Finset.equivBitIndices.symm (C q.2.1)), q.2.1,
        Denumerable.ofNat Oracle.Single.Code q.2.2) :=
    (fst.pair (hC.comp (fst.comp snd))).pair
      ((fst.comp snd).pair ((Primrec.ofNat _).comp (snd.comp snd)))
  exact (Oracle.Single.Code.primrec_agreementRestraint_equivBitIndices.comp hargs).of_eq
    fun q => by simp [agreementRestraint]

end ConeAvoiding

/-- The constructed set is c.e. when the binary codes of the target stages are primitive
recursive. -/
theorem rePred_mem_coneAvoidingSet (hC : Primrec fun s => Finset.equivBitIndices.symm (C s)) :
    REPred (· ∈ coneAvoidingSet C) :=
  rePred_mem_stageLimit_stage (primrec_agreementRestraint hC)

/-! ### The negative requirements -/

namespace ConeAvoiding

/-- At every stage, the negative requirement `N_e` holds exactly its agreement restraint. -/
private theorem exists_restraint_eq_some_and_le (e s : ℕ) :
    ∃ b, restraint (agreementRestraint C) e s = some b ∧
      Oracle.Single.Code.agreementRestraint
        (Oracle.Single.Code.setAnswers (stage (agreementRestraint C) s)) s
        (Denumerable.ofNat Oracle.Single.Code e) ((C s : Set ℕ).indicator 1) ≤ b :=
  ⟨_, restraint_eq e s, le_rfl⟩

/-- **The negative requirements are met.** If `C` has increasing stages with primitive recursive
binary codes and a noncomputable limit, then no oracle program computes the limit of `C` relative
to the constructed set: since `N_e` is injured only finitely often, `Φ_e^A = C` would make `C`
computable by Soare's Lemma 1. -/
theorem eval_ne_oracle (hC : Monotone C)
    (hCp : Primrec fun s => Finset.equivBitIndices.symm (C s))
    (hnc : ¬ComputablePred (· ∈ stageLimit C)) (e : ℕ) :
    Oracle.Single.Code.eval (coneAvoidingSet C).oracle (Denumerable.ofNat Oracle.Single.Code e) ≠
      (stageLimit C).oracle := fun heval =>
  hnc <| Oracle.Single.Code.computablePred_mem_stageLimit_of_eval_eq
    (monotone_stage _) hC (primrec_stage (primrec_agreementRestraint hCp)).to_comp hCp.to_comp
    (exists_restraint_eq_some_and_le e) (finite_injurySet_and_ncard_le e).1 heval

/-- **The restraints stabilize.** Under the hypotheses of `ConeAvoiding.eval_ne_oracle`, the
restraint of each negative requirement along the construction is eventually constant. -/
theorem exists_eventually_agreementRestraint_eq (hC : Monotone C)
    (hCp : Primrec fun s => Finset.equivBitIndices.symm (C s))
    (hnc : ¬ComputablePred (· ∈ stageLimit C)) (e : ℕ) :
    ∃ b, ∀ᶠ s in atTop, agreementRestraint C (stage (agreementRestraint C) s) s e = b := by
  obtain ⟨_, b, hb⟩ :=
    Oracle.Single.Code.exists_eventually_agreementLength_eq_and_agreementRestraint_eq
      (monotone_stage _) hC (Eventually.of_forall (exists_restraint_eq_some_and_le e))
      (finite_injurySet_and_ncard_le e).1 (eval_ne_oracle hC hCp hnc e)
  exact ⟨b, hb.mono fun _ hs => hs.2⟩

end ConeAvoiding

/-! ### Main results -/

/-- **The constructed set is simple**, when `C` has increasing stages with primitive recursive
binary codes and a noncomputable limit. -/
theorem simple_coneAvoidingSet (hC : Monotone C)
    (hCp : Primrec fun s => Finset.equivBitIndices.symm (C s))
    (hnc : ¬ComputablePred (· ∈ stageLimit C)) : (coneAvoidingSet C).Simple :=
  simple_stageLimit_stage (primrec_agreementRestraint hCp) fun e => by
    obtain ⟨b, hb⟩ := exists_eventually_agreementRestraint_eq hC hCp hnc e
    exact ⟨b, hb.mono fun _ hs => hs.le⟩

/-- **The constructed set does not compute the limit of `C`**, when `C` has increasing stages with
primitive recursive binary codes and a noncomputable limit. -/
theorem not_turingReducible_coneAvoidingSet (hC : Monotone C)
    (hCp : Primrec fun s => Finset.equivBitIndices.symm (C s))
    (hnc : ¬ComputablePred (· ∈ stageLimit C)) :
    ¬TuringReducible (stageLimit C).oracle (coneAvoidingSet C).oracle := fun h => by
  obtain ⟨c, hc⟩ := Oracle.Single.Code.turingReducible_iff_exists_code.1 h
  exact eval_ne_oracle hC hCp hnc (Encodable.encode c) (by rwa [Denumerable.ofNat_encode])

/-- **Sacks's theorem** [S, VII.3.1], with an index: for every noncomputable c.e. set `C`, there is
an ordinary program whose domain is simple and does not compute `C`. -/
theorem exists_simple_not_turingReducible_code {C : Set ℕ} (hC : REPred (· ∈ C))
    (hnc : ¬ComputablePred (· ∈ C)) :
    ∃ d : Nat.Partrec.Code, {x | (d.eval x).Dom}.Simple ∧
      ¬TuringReducible C.oracle {x | (d.eval x).Dom}.oracle := by
  obtain ⟨c, hc⟩ := rePred_iff_exists_code.1 hC
  have hCc : stageLimit c.domStage = C := by
    rw [Nat.Partrec.Code.stageLimit_domStage]
    exact Set.ext fun x => (hc x).symm
  have hCp : Primrec fun s => Finset.equivBitIndices.symm (c.domStage s) :=
    Nat.Partrec.Code.primrec_domStage.comp ((Primrec.const c).pair Primrec.id)
  rw [← hCc] at hnc ⊢
  obtain ⟨d, hd⟩ := rePred_iff_exists_code.1 (rePred_mem_coneAvoidingSet hCp)
  have hset : {x | (d.eval x).Dom} = coneAvoidingSet c.domStage := Set.ext fun x => (hd x).symm
  refine ⟨d, ?_⟩
  rw [hset]
  exact ⟨simple_coneAvoidingSet c.monotone_domStage hCp hnc,
    not_turingReducible_coneAvoidingSet c.monotone_domStage hCp hnc⟩

/-- **Sacks's theorem** [S, VII.3.1]: for every noncomputable c.e. set `C`, there is a simple set
`A` with `C ≰_T A`. -/
theorem exists_simple_not_turingReducible {C : Set ℕ} (hC : REPred (· ∈ C))
    (hnc : ¬ComputablePred (· ∈ C)) : ∃ A : Set ℕ, A.Simple ∧ ¬TuringReducible C.oracle A.oracle :=
  let ⟨_, hd⟩ := exists_simple_not_turingReducible_code hC hnc
  ⟨_, hd⟩

end TauCeti
