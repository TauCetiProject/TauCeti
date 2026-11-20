/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.Computability.KleenePost
import TauCeti.Computability.SingleOracle.Probe
import TauCeti.Data.PFun.Basic

/-!
# Regression examples: the Kleene–Post construction

These examples exercise the public interface of `TauCeti.Computability.SingleOracle.BitString` and
`TauCeti.Computability.KleenePost` from a downstream module without unfolding unexposed
definitions:

* finite binary string extension, `Code.bitAnswers`, and concrete membership in
  `Code.findConvergentExt` via `Code.mem_findConvergentExt_iff`;
* concrete `diagStep` evaluation on `Code.zero`, initial stages, and parity transitions for
  `stageStep`, `stage`, `stageA`, and `stageB`;
* convergent query-free (`Code.zero`), convergent oracle-query (`Code.oracle`), and permanently
  divergent (`Code.comp (Code.diagonalProbe 0 0) Code.succ`) witnesses on both `kleenePostSetA`
  and `kleenePostSetB`;
* the Kleene–Post theorem in set and Turing-degree forms strictly between `0` and `0'`.
-/

open Denumerable Encodable TauCeti TauCeti.KleenePost TauCeti.Oracle.Single

-- Finite-extension lookup and `Code.bitAnswers` simp evaluation on a concrete binary string.
example (A : Set ℕ) (hA : A.ExtendsBits [true]) :
    0 ∈ A ∧ Code.bitAnswers [true] 0 = some 1 ∧ Code.bitAnswers [true] 1 = none ∧
      (Code.bitAnswers [true] 0).isSome = true := by
  refine ⟨(Set.extendsBits_singleton.1 hA).2 rfl, ?_, ?_, ?_⟩ <;> simp

-- Concrete evaluation of `Code.findConvergentExt` and `diagStep`: `Code.zero` halts with empty
-- suffix `[]` at fuel `1` (code `1`, while code `0` decodes to fuel `0`), yielding
-- `diagStep Code.zero [] [] = ([true], [false])`.
example :
    ([], ⟨0, 0⟩) ∈ Code.findConvergentExt Code.zero 0 [] ∧
      diagStep Code.zero [] [] = ([true], [false]) := by
  have hdec0 : decode (α := List Bool × ℕ) 0 = some ([], 0) := by simp
  have hdec1 : decode (α := List Bool × ℕ) 1 = some ([], 1) := by
    simpa [Nat.pair] using encodek (([], 1) : List Bool × ℕ)
  have hfind : ([], ⟨0, 0⟩) ∈ Code.findConvergentExt Code.zero 0 [] := by
    rw [Code.mem_findConvergentExt_iff]
    refine ⟨1, 1, hdec1, by simp [Code.evaln_succ_zero_eq_some], fun m hm δ j hdec => ?_⟩
    have hm0 : m = 0 := by omega
    subst hm0
    rw [hdec0, Option.some.injEq, Prod.mk.injEq] at hdec
    rcases hdec with ⟨rfl, rfl⟩
    simp
  exact ⟨hfind, by simpa using diagStep_of_mem_findConvergentExt (α := []) hfind⟩

-- Initial stage, `stageStep` parity simplification, `stageA`/`stageB` transitions, and
-- finite-stage membership lookup on `kleenePostSetA` and `kleenePostSetB`.
example (e : ℕ) :
    stage 1 = diagStep (ofNat Code 0) [] [] ∧
      stageA (2 * e + 1) = (diagStep (ofNat Code e) (stageA (2 * e)) (stageB (2 * e))).1 ∧
      stageB (2 * e + 1 + 1) =
        (diagStep (ofNat Code e) (stageB (2 * e + 1)) (stageA (2 * e + 1))).1 ∧
      (0 ∈ kleenePostSetA ↔ (stageA 1)[0]? = some true) ∧
      (0 ∈ kleenePostSetB ↔ (stageB 1)[0]? = some true) :=
  ⟨by rw [stage_succ, stage_zero, stageStep_zero],
    stageA_two_mul_succ e,
    stageB_two_mul_add_one_succ e,
    mem_kleenePostSetA_iff_getElem?_of_lt (lt_length_stageA_succ 0),
    mem_kleenePostSetB_iff_getElem?_of_lt (lt_length_stageB_succ 0)⟩

-- Convergent query-free witness (`Code.zero`) on both `kleenePostSetA` (even stage) and
-- `kleenePostSetB` (odd stage).
example :
    (let x := (stageA (2 * encode Code.zero)).length;
      Code.eval kleenePostSetB.oracle Code.zero x = Part.some 0 ∧
        x ∈ kleenePostSetA ∧ kleenePostSetA.oracle x = Part.some 1) ∧
    (let y := (stageB (2 * encode Code.zero + 1)).length;
      Code.eval kleenePostSetA.oracle Code.zero y = Part.some 0 ∧
        y ∈ kleenePostSetB ∧ kleenePostSetB.oracle y = Part.some 1) := by
  constructor
  · dsimp only
    set x := (stageA (2 * encode Code.zero)).length
    obtain ⟨v, hv, hne⟩ :=
      exists_mem_eval_and_oracle_kleenePostSetA_ne_of_hasConvergentExt
        (Code.hasConvergentExt_zero _ _)
    obtain rfl : v = 0 := by simpa [Code.eval_zero] using hv
    have hx : x ∈ kleenePostSetA := by
      by_contra hx
      exact hne (by simp [x, hx])
    exact ⟨Code.eval_zero x, hx, by simp [hx]⟩
  · dsimp only
    set y := (stageB (2 * encode Code.zero + 1)).length
    obtain ⟨v, hv, hne⟩ :=
      exists_mem_eval_and_oracle_kleenePostSetB_ne_of_hasConvergentExt
        (Code.hasConvergentExt_zero _ _)
    obtain rfl : v = 0 := by simpa [Code.eval_zero] using hv
    have hy : y ∈ kleenePostSetB := by
      by_contra hy
      exact hne (by simp [y, hy])
    exact ⟨Code.eval_zero y, hy, by simp [hy]⟩

-- Convergent oracle-query witness (`Code.oracle`): at the witness coordinates for the identity
-- reduction on both sides, `kleenePostSetA` and `kleenePostSetB` have opposite membership bits.
example :
    (let x := (stageA (2 * encode Code.oracle)).length;
      x ∈ kleenePostSetA ↔ x ∉ kleenePostSetB) ∧
    (let y := (stageB (2 * encode Code.oracle + 1)).length;
      y ∈ kleenePostSetB ↔ y ∉ kleenePostSetA) := by
  constructor
  · dsimp only
    set x := (stageA (2 * encode Code.oracle)).length
    have hne := eval_ne_oracle_kleenePostSetA Code.oracle
    simp only [Code.eval_oracle] at hne
    by_cases hA : x ∈ kleenePostSetA <;> by_cases hB : x ∈ kleenePostSetB <;> simp_all [x]
  · dsimp only
    set y := (stageB (2 * encode Code.oracle + 1)).length
    have hne := eval_ne_oracle_kleenePostSetB Code.oracle
    simp only [Code.eval_oracle] at hne
    by_cases hB : y ∈ kleenePostSetB <;> by_cases hA : y ∈ kleenePostSetA <;> simp_all [y]

-- Permanent-divergence witness (`Code.comp (Code.diagonalProbe 0 0) Code.succ`) on both
-- `kleenePostSetA` and `kleenePostSetB`.
example :
    let c := Code.comp (Code.diagonalProbe 0 0) Code.succ
    (let x := (stageA (2 * encode c)).length;
      Code.eval kleenePostSetB.oracle c x = Part.none ∧
        x ∉ kleenePostSetA ∧ kleenePostSetA.oracle x = Part.some 0) ∧
    (let y := (stageB (2 * encode c + 1)).length;
      Code.eval kleenePostSetA.oracle c y = Part.none ∧
        y ∉ kleenePostSetB ∧ kleenePostSetB.oracle y = Part.some 0) := by
  intro c
  have hdiv : ∀ (x : ℕ) (β : List Bool), ¬Code.HasConvergentExt c x β :=
    fun _ _ => Code.not_hasConvergentExt_iff.2 fun _ _ => by simp [c]
  exact ⟨eval_eq_none_and_notMem_kleenePostSetA_of_not_hasConvergentExt (hdiv _ _),
    eval_eq_none_and_notMem_kleenePostSetB_of_not_hasConvergentExt (hdiv _ _)⟩

-- The Kleene–Post theorem in set and Turing-degree forms strictly between `0` and `0'`.
example :
    (∃ A B : Set ℕ,
      TuringReducible A.oracle (∅ : Set ℕ).jump.oracle ∧
        TuringReducible B.oracle (∅ : Set ℕ).jump.oracle ∧
          ¬TuringReducible A.oracle B.oracle ∧ ¬TuringReducible B.oracle A.oracle) ∧
    (∃ A B : Set ℕ,
      toAntisymmetrization TuringReducible A.oracle ∈
        Set.Ioo (toAntisymmetrization TuringReducible (∅ : Set ℕ).oracle)
          (toAntisymmetrization TuringReducible (∅ : Set ℕ).jump.oracle) ∧
      toAntisymmetrization TuringReducible B.oracle ∈
        Set.Ioo (toAntisymmetrization TuringReducible (∅ : Set ℕ).oracle)
          (toAntisymmetrization TuringReducible (∅ : Set ℕ).jump.oracle) ∧
      ¬(toAntisymmetrization TuringReducible A.oracle ≤
          toAntisymmetrization TuringReducible B.oracle) ∧
      ¬(toAntisymmetrization TuringReducible B.oracle ≤
          toAntisymmetrization TuringReducible A.oracle)) :=
  ⟨kleene_post, exists_incomparable_turingDegrees_mem_Ioo⟩
