/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Computability.Priority.Injury.Computable
public import Mathlib.Computability.Halting
import Mathlib.Computability.Reduce

/-!
# Regression examples: effectivity of the injury objects

The injury set of a requirement is c.e. uniformly in the requirement, but not computable uniformly
in the requirement, even when the stages and the restraints are computable.

The stages `haltStage s` enumerate the halting set `{x | (eval (ofNat Code x) 0).Dom}` of
Mathlib's `ComputablePred.halting_problem`: stage `s` holds the indices `x < s` for which the
bounded evaluator `evaln s` succeeds on input `0`. Under the constant restraint
`r e s = some e`, the injury set of `e` is the halting set cut off at `e`. The diagonal query
`e ∈ I_e` would then decide the halting set, so the injury sets are not uniformly computable,
although they are uniformly c.e. and the injury stages are uniformly computable.
-/

public section

open Nat.Partrec Nat.Partrec.Code Computable TauCeti.Priority

namespace TauCeti.HaltingInjuryExample

/-- Stage `s` of the enumeration of the halting set: the indices `x < s` for which the bounded
evaluator `evaln s` succeeds on input `0`. -/
def haltStage (s : ℕ) : Finset ℕ :=
  (Finset.range s).filter fun x => (evaln s (Denumerable.ofNat Code x) 0).isSome

/-- Membership in a stage of the enumeration of the halting set. -/
theorem mem_haltStage {s x : ℕ} :
    x ∈ haltStage s ↔ x < s ∧ (evaln s (Denumerable.ofNat Code x) 0).isSome := by
  simp [haltStage]

/-- The stages of the enumeration of the halting set are computable. -/
theorem computablePred_mem_haltStage :
    ComputablePred fun p : ℕ × ℕ => p.2 ∈ haltStage p.1 :=
  (PrimrecPred.and (Primrec.nat_lt.comp Primrec.snd Primrec.fst)
    (Primrec.eq.comp (Primrec.option_isSome.comp (primrec_evaln.comp
      ((Primrec.fst.pair ((Primrec.ofNat Code).comp Primrec.snd)).pair (Primrec.const 0))))
      (Primrec.const true))).computablePred.of_eq fun _ => mem_haltStage.symm

/-- Every halting index enters the enumeration at some stage. -/
theorem exists_mem_haltStage {x : ℕ} (h : (eval (Denumerable.ofNat Code x) 0).Dom) :
    ∃ s, x ∈ haltStage s := by
  obtain ⟨k, hk⟩ := evaln_complete.1 (Part.get_mem h)
  exact ⟨max k (x + 1), mem_haltStage.2
    ⟨by omega, Option.isSome_iff_exists.2 ⟨_, evaln_mono (le_max_left k (x + 1)) hk⟩⟩⟩

/-- Under the constant restraint `some e`, the injury set of `e` is the halting set cut off at
`e`. -/
theorem mem_injurySet_haltStage {e x : ℕ} :
    x ∈ injurySet haltStage (fun e _ => some e) e ↔
      x ≤ e ∧ (eval (Denumerable.ofNat Code x) 0).Dom := by
  simp only [mem_injurySet, mem_injuriesAt, Option.some.injEq, exists_eq_left']
  constructor
  · rintro ⟨s, hs, -, hxe⟩
    obtain ⟨-, hsome⟩ := mem_haltStage.1 hs
    obtain ⟨y, hy⟩ := Option.isSome_iff_exists.1 hsome
    exact ⟨hxe, Part.dom_iff_mem.2 ⟨y, evaln_sound hy⟩⟩
  · rintro ⟨hxe, hdom⟩
    classical
    -- the stage before the first stage containing `x`
    have hex := exists_mem_haltStage hdom
    have hpos : Nat.find hex ≠ 0 := fun h0 => by
      have h := Nat.find_spec hex
      rw [h0] at h
      simp [haltStage] at h
    refine ⟨Nat.find hex - 1, ?_, Nat.find_min hex (by omega), hxe⟩
    rw [Nat.sub_add_cancel (Nat.pos_of_ne_zero hpos)]
    exact Nat.find_spec hex

/-- The constant restraint `some e` is computable. -/
theorem computable_const_restraint : Computable₂ fun e _ : ℕ => some e :=
  (option_some.comp fst).to₂

-- The injury sets are uniformly c.e. ...
example : REPred fun p : ℕ × ℕ => p.2 ∈ injurySet haltStage (fun e _ => some e) p.1 :=
  rePred_mem_injurySet computablePred_mem_haltStage computable_const_restraint

-- ... and so are the injury stages computable ...
example : ComputablePred fun p : ℕ × ℕ => p.2 ∈ injuryStages haltStage (fun e _ => some e) p.1 :=
  computablePred_mem_injuryStages computablePred_mem_haltStage computable_const_restraint

-- ... but the injury sets are not uniformly computable: the diagonal query `e ∈ I_e` would
-- decide the halting set.
example : ¬ComputablePred fun p : ℕ × ℕ => p.2 ∈ injurySet haltStage (fun e _ => some e) p.1 :=
  fun h => ComputablePred.halting_problem 0 <| ComputablePred.computable_of_manyOneReducible
    ⟨fun c => (Encodable.encode c, Encodable.encode c), Computable.encode.pair Computable.encode,
      fun c => by rw [mem_injurySet_haltStage, Denumerable.ofNat_encode]; simp⟩ h

end TauCeti.HaltingInjuryExample
