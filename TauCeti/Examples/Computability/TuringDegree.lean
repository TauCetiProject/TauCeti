/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.Computability.Jump.Basic
import TauCeti.Computability.RE

/-!
# Regression examples: Turing reducibility of sets

These examples exercise the set-level Turing reducibility API from a downstream module, through
public statements only:

* the halting set `(∅ : Set ℕ).jump` is Turing equivalent to its complement, although the
  complement is not c.e.: Turing reducibility does not see the asymmetry between a set and its
  complement;
* finite sets, the column `{⟨x, e⟩ | x : ℕ}`, and `Set.univ` have the least degree `⊥`;
* the halting set is a noncomputable subset of the computable set `Set.univ`, so inclusion does
  not give Turing reducibility;
* the parity join of a set with its complement has the degree of the set;
* the column `e` of the paired halting set `Z.pairedJump` is Turing equivalent to the halting
  domain of the program numbered `e` relative to `Z`;
* a computable change of presentation, the shift `{x | x + 1 ∈ A}`, is Turing reducible to `A`.
-/

open scoped Computability
open Encodable Denumerable TauCeti.Oracle.Single

-- The halting set is Turing equivalent to its complement ...
example : TuringEquivalent ((∅ : Set ℕ).jump)ᶜ.oracle (∅ : Set ℕ).jump.oracle :=
  Set.oracle_compl_turingEquivalent _

-- ... although the complement is not c.e., since a c.e. set with c.e. complement is computable.
example : ¬REPred (· ∈ ((∅ : Set ℕ).jump)ᶜ) := fun h =>
  Set.not_computablePred_mem_jump ∅ <|
    ComputablePred.computable_iff_re_compl_re'.2 ⟨Set.rePred_mem_jump_empty, h⟩

-- A finite set has the least degree.
example : toAntisymmetrization TuringReducible ({0, 3, 5} : Set ℕ).oracle = ⊥ := by
  simpa using (Set.toFinite ({0, 3, 5} : Set ℕ)).computablePred

-- A column `{⟨x, e⟩ | x : ℕ}` has the least degree, although it is infinite.
example (e : ℕ) : toAntisymmetrization TuringReducible e.pairColumn.oracle = ⊥ := by
  rw [TauCeti.toAntisymmetrization_eq_bot_iff, Set.partrec_oracle_iff]
  exact e.computablePred_mem_pairColumn

-- The halting set is a noncomputable subset of `Set.univ`, which has the least degree as the
-- complement of the empty set: inclusion does not give Turing reducibility.
example :
    (∅ : Set ℕ).jump ⊆ Set.univ ∧
      toAntisymmetrization TuringReducible (Set.univ : Set ℕ).oracle = ⊥ ∧
      ¬TuringReducible (∅ : Set ℕ).jump.oracle (Set.univ : Set ℕ).oracle := by
  have huniv : toAntisymmetrization TuringReducible (Set.univ : Set ℕ).oracle = ⊥ := by
    rw [← Set.compl_empty, Set.toAntisymmetrization_oracle_compl,
      TauCeti.toAntisymmetrization_oracle_empty]
  refine ⟨Set.subset_univ _, huniv, fun h => Set.not_computablePred_mem_jump ∅ ?_⟩
  have hK : toAntisymmetrization TuringReducible (∅ : Set ℕ).jump.oracle = ⊥ :=
    le_bot_iff.1 (huniv ▸ TauCeti.turingDegree_le_iff.2 h)
  simpa using hK

-- The parity join of a set with its complement has the degree of the set.
example (A : Set ℕ) :
    toAntisymmetrization TuringReducible (A.turingJoin Aᶜ).oracle =
      toAntisymmetrization TuringReducible A.oracle := by
  simp [TuringDegree.toAntisymmetrization_oracle_turingJoin]

-- The column `e` of the paired halting set `K₀^Z` is Turing equivalent to the halting domain
-- `W_e^Z` of the program numbered `e` relative to `Z`.
example (Z : Set ℕ) (e : ℕ) :
    TuringEquivalent (Z.pairedJump ∩ e.pairColumn).oracle
      {x | (Code.eval Z.oracle (ofNat Code e) x).Dom}.oracle := by
  simpa [Set.preimage, Set.pair_mem_pairedJump] using
    Set.oracle_inter_pairColumn_turingEquivalent Z.pairedJump e

-- Shifting a set down by one, a computable change of presentation, does not raise its degree.
example (A : Set ℕ) : TuringReducible ((· + 1) ⁻¹' A).oracle A.oracle :=
  A.oracle_preimage_turingReducible Computable.succ

-- `simp` characterizes reducibility to the empty oracle before unfolding the empty oracle.
example (A : Set ℕ) :
    TuringReducible A.oracle (∅ : Set ℕ).oracle ↔ ComputablePred (· ∈ A) := by
  simp
