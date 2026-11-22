/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Computability.Enumeration.Relative.Code
public import TauCeti.Computability.Enumeration.Serialization
public import TauCeti.Computability.Hierarchy.One

/-!
# Relative stage characterizations of Σ⁰₁ sets

This file combines the normalized domain stages `TauCeti.Oracle.Single.Code.domStage` from
`TauCeti.Computability.Enumeration.Relative.Code` with serialization
(`TauCeti.Computability.Enumeration.Serialization`) and the first level of the arithmetical
hierarchy (`TauCeti.Computability.Hierarchy.One`) to characterize `IsSigma Z 1` predicates on `ℕ`
as limits of `Z`-computable monotone finite stages, with or without single-entry serialization.

## Main results

* `TauCeti.Oracle.Single.Code.stageLimit_domStage_toSingleOracleCode`: query-free relative domain
  stages agree in the limit with ordinary `Nat.Partrec.Code.domStage`.
* `TauCeti.Enumeration.computableIn_serializedStage_domStage_setAnswers`: relative serialization
  produces uniformly `Z`-computable domain stages.
* `TauCeti.Enumeration.isSigma_one_mem_stageLimit`,
  `TauCeti.Enumeration.isSigma_one_mem_stageLimit_of_equivBitIndices`: limits of finite stages
  with `Z`-computable membership (in particular, `Z`-computable binary codes) are Σ⁰₁ relative
  to `Z`.
* `TauCeti.Enumeration.isSigma_one_iff_exists_stages`,
  `TauCeti.Enumeration.isSigma_one_iff_exists_serialized_stages`: relative stage characterizations
  of Σ⁰₁ predicates on `ℕ`.

## References

* R. I. Soare, *Recursively Enumerable Sets and Degrees*, Springer, 1987, Chapters II.1–2 and III.1.
-/

public section

open TauCeti.ArithmeticalHierarchy TauCeti.Oracle.Single

namespace TauCeti.Oracle.Single.Code

/-- For a query-free program, the relative domain stages have the same limit as Mathlib's ordinary
code domain stages, for every oracle answer table `σ`. -/
theorem stageLimit_domStage_toSingleOracleCode (σ : ℕ → Option ℕ) (c : Nat.Partrec.Code) :
    TauCeti.Enumeration.stageLimit (c.toSingleOracleCode.domStage σ) =
      TauCeti.Enumeration.stageLimit c.domStage := by
  let O : ℕ →. ℕ := fun z => Part.ofOption (σ z)
  rw [stageLimit_domStage (O := O) (by simp [O, Part.mem_ofOption]),
    eval_toSingleOracleCode, Nat.Partrec.Code.stageLimit_domStage]
  rfl

end TauCeti.Oracle.Single.Code

namespace TauCeti.Enumeration

/-- The canonical `Z`-relative c.e. domain enumerations have uniformly `Z`-computable serialized
stages. -/
theorem computableIn_serializedStage_domStage_setAnswers (Z : Set ℕ) :
    ComputableIn {Z.oracle} fun p : Code × ℕ =>
      Finset.equivBitIndices.symm (serializedStage (p.1.domStage (Code.setAnswers Z)) p.2) :=
  computableIn_serializedStage (A := fun c : Code => c.domStage (Code.setAnswers Z))
    (Code.computableIn_domStage_setAnswers Z)

/-- The limit of finite stages whose membership relation is `Z`-computable is Σ⁰₁ relative to
`Z`. -/
theorem isSigma_one_mem_stageLimit {Z : Set ℕ} {A : ℕ → Finset ℕ}
    (hA : ComputableIn {Z.oracle} fun p : ℕ × ℕ => decide (p.2 ∈ A p.1)) :
    IsSigma Z 1 fun x => x ∈ stageLimit A :=
  isSigma_one_iff.2 ⟨fun p => decide (p.1 ∈ A p.2),
    hA.comp (ComputableIn.snd.pair ComputableIn.fst), fun x => by simp⟩

/-- The limit of finite stages whose binary codes are `Z`-computable is Σ⁰₁ relative to `Z`. -/
theorem isSigma_one_mem_stageLimit_of_equivBitIndices {Z : Set ℕ} {A : ℕ → Finset ℕ}
    (hA : ComputableIn {Z.oracle} fun s => Finset.equivBitIndices.symm (A s)) :
    IsSigma Z 1 fun x => x ∈ stageLimit A :=
  isSigma_one_mem_stageLimit (computableIn_mem_of_computableIn_equivBitIndices hA)

/-- A predicate on `ℕ` is Σ⁰₁ relative to `Z` if and only if it is the limit of increasing finite
stages, starting empty, whose binary finite-set codes are `Z`-computable. -/
theorem isSigma_one_iff_exists_stages {Z : Set ℕ} {p : ℕ → Prop} :
    IsSigma Z 1 p ↔ ∃ A : ℕ → Finset ℕ, Monotone A ∧ A 0 = ∅ ∧
      ComputableIn {Z.oracle} (fun s => Finset.equivBitIndices.symm (A s)) ∧
      stageLimit A = {x | p x} := by
  constructor
  · intro hp
    obtain ⟨c, hc⟩ := isSigma_one_iff_exists_code.1 hp
    refine ⟨c.domStage (Code.setAnswers Z), c.monotone_domStage _, c.domStage_zero _,
      (Code.computableIn_domStage_setAnswers Z).comp
        ((ComputableIn.const c).pair ComputableIn.id), ?_⟩
    rw [Code.stageLimit_domStage_setAnswers]
    ext x
    exact (hc x).symm
  · rintro ⟨A, -, -, hA, hlim⟩
    exact (isSigma_one_mem_stageLimit_of_equivBitIndices hA).of_eq fun x => by
      rw [hlim, Set.mem_ofPred_eq]

/-- A predicate on `ℕ` is Σ⁰₁ relative to `Z` if and only if it is the limit of increasing
`Z`-computable finite stages starting empty with at most one new entry per stage. -/
theorem isSigma_one_iff_exists_serialized_stages {Z : Set ℕ} {p : ℕ → Prop} :
    IsSigma Z 1 p ↔ ∃ A : ℕ → Finset ℕ, Monotone A ∧ A 0 = ∅ ∧
      (∀ s, (fresh A s).card ≤ 1) ∧
      ComputableIn {Z.oracle} (fun s => Finset.equivBitIndices.symm (A s)) ∧
      stageLimit A = {x | p x} := by
  constructor
  · intro hp
    obtain ⟨A, -, -, hA, hlim⟩ := isSigma_one_iff_exists_stages.1 hp
    exact exists_serialized_stages_of_stages ⟨A, hA, hlim⟩
  · rintro ⟨A, hmono, hzero, -, hA, hlim⟩
    exact isSigma_one_iff_exists_stages.2 ⟨A, hmono, hzero, hA, hlim⟩

end TauCeti.Enumeration
