/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.Computability.Enumeration.Relative.Basic
import TauCeti.Computability.Enumeration.Comparison
import TauCeti.Computability.Enumeration.Closure
import TauCeti.Computability.Enumeration.Range
import TauCeti.Computability.Primrec.FiniteSet
import TauCeti.Computability.RE

/-!
# Regression examples: relative enumerations, stage comparisons, and index closure

These examples exercise `TauCeti.Computability.Enumeration.Relative.Basic`,
`TauCeti.Computability.Enumeration.Comparison`, `TauCeti.Computability.Enumeration.IndexClosure`,
`TauCeti.Computability.Enumeration.Closure`, `TauCeti.Computability.Enumeration.Range`, and
`TauCeti.Computability.RE` from a downstream module, using public APIs only:

* the empty set is c.e. and admits a partial computable range presentation without any
  nonemptiness hypothesis;
* concrete c.e. sets (finite sets, even numbers, and the halting set `(∅ : Set ℕ).jump`) combine
  under union, intersection, computable image, partial preimage, and existential projection;
* stage comparison witnesses mutual inclusion between two directed enumerations with different
  entry times (`Finset.range` and the batched enumeration `s ↦ Finset.range (2 * s)`), whereas
  without directedness of the target enumeration `stageCompare` can diverge even when the limiting
  sets coincide;
* `domStage` relative to a nontrivial oracle `Z = {0}` yields a `Z`-computable serialized stage
  presentation of every `Σ⁰₁(Z)` predicate;
* uniform oracle-program compilers (`union`, `interList`, `restrictId`, `rangeDom`, `imageDom`,
  `projDom`) and their ordinary `Nat.Partrec.Code` specializations satisfy their domain equations
  and primitive-recursiveness certificates.
-/

open TauCeti.Enumeration TauCeti.ArithmeticalHierarchy
open TauCeti.Oracle.Single (Code)

-- The empty set is the range of a partial computable function (`rePred_iff_exists_partrec_ran`
-- needs no nonemptiness hypothesis).
example : ∃ f : ℕ →. ℕ, Partrec f ∧ f.ran = ∅ := by
  have hfalse : Computable fun _ : ℕ => decide False := Computable.const false
  have hempty : REPred (· ∈ (∅ : Set ℕ)) :=
    hfalse.computablePred.to_re.of_eq fun _ => by simp
  exact rePred_iff_exists_partrec_ran.1 hempty

-- Even numbers are c.e. as a computable image, and combine with `{0, 2}` and the halting set
-- `(∅ : Set ℕ).jump` under `REPred.or`, `REPred.and`, and `REPred.exists`.
example :
    REPred (fun x : ℕ =>
      (x ∈ (fun n => 2 * n) '' Set.univ ∨ x ∈ (∅ : Set ℕ).jump) ∧
        ∃ y : ℕ, x = y + y) := by
  have htrue : Computable fun _ : ℕ => decide True := Computable.const true
  have huniv : REPred (· ∈ (Set.univ : Set ℕ)) :=
    htrue.computablePred.to_re.of_eq fun _ => by simp
  have heven : REPred (· ∈ (fun n : ℕ => 2 * n) '' Set.univ) :=
    (Primrec.nat_mul.to_comp.comp (Computable.const 2) Computable.id).rePred_mem_image huniv
  have hjump : REPred (· ∈ (∅ : Set ℕ).jump) :=
    isSigma_one_empty_iff_rePred.1 isSigma_one_jump
  have hrel : REPred (fun p : ℕ × ℕ => p.1 = p.2 + p.2) :=
    (Primrec.eq.decide.to_comp.comp Computable.fst
      (Primrec.nat_add.to_comp.comp Computable.snd Computable.snd)).computablePred.to_re.of_eq
        fun _ => by simp
  exact (heven.or hjump).and hrel.exists

-- Partial preimage of a c.e. set under a partial computable function is c.e.
example :
    REPred (· ∈ PFun.preimage (fun n : ℕ => Nat.rfind (PFun.lift fun _ => decide (n = 0)))
      (∅ : Set ℕ).jump) := by
  have htest : Computable fun p : ℕ × ℕ => decide (p.1 = 0) :=
    Primrec.eq.decide.to_comp.comp Computable.fst (Computable.const 0)
  have hf : Partrec (fun n : ℕ => Nat.rfind (PFun.lift fun _ => decide (n = 0)) : ℕ →. ℕ) :=
    (Partrec.rfind htest.partrec.to₂).of_eq fun _ => rfl
  exact hf.rePred_mem_preimage (isSigma_one_empty_iff_rePred.1 isSigma_one_jump)

-- Comparing `Finset.range` with the batched enumeration `s ↦ Finset.range (2 * s)` yields
-- computable mutual stage transfers witnessing equal limiting sets.
example :
    (∀ s, 2 * s ∈ stageCompare (fun s => Finset.range (2 * s)) Finset.range s) ∧
      ∃ f g : ℕ → ℕ, ComputableIn (∅ : Set (ℕ →. ℕ)) f ∧ ComputableIn (∅ : Set (ℕ →. ℕ)) g ∧
        (∀ s, Finset.range (2 * s) ⊆ Finset.range (f s)) ∧
        (∀ s, Finset.range s ⊆ Finset.range (2 * g s)) := by
  have hmono₁ : Monotone (fun s => Finset.range (2 * s)) :=
    fun _ _ h => Finset.range_subset_range.2 (by omega)
  have hmono₂ : Monotone Finset.range := fun _ _ h => Finset.range_subset_range.2 h
  have hlim : stageLimit (fun s => Finset.range (2 * s)) = stageLimit Finset.range := by
    ext x
    simp only [mem_stageLimit, Finset.mem_range]
    exact ⟨fun ⟨s, hs⟩ => ⟨2 * s, hs⟩, fun ⟨s, hs⟩ => ⟨s, by omega⟩⟩
  have hA : ComputableIn (∅ : Set (ℕ →. ℕ))
      fun p : Unit × ℕ => Finset.equivBitIndices.symm (Finset.range (2 * p.2)) :=
    (Primrec.equivBitIndices_symm_range.comp
      (Primrec.nat_mul.comp (Primrec.const 2) Primrec.snd)).computableIn
  have hB : ComputableIn (∅ : Set (ℕ →. ℕ))
      fun p : Unit × ℕ => Finset.equivBitIndices.symm (Finset.range p.2) :=
    (Primrec.equivBitIndices_symm_range.comp Primrec.snd).computableIn
  obtain ⟨f, g, hf, hg, hfg, hgf⟩ := exists_computableIn_stage_comparison
    (A := fun (_ : Unit) s => Finset.range (2 * s)) (B := fun (_ : Unit) => Finset.range)
    (fun _ => hmono₁.directed_le) (fun _ => hmono₂.directed_le) hA hB (fun _ => hlim)
  refine ⟨fun s => mem_stageCompare.2 ⟨Finset.Subset.rfl, fun t ht hsub => ?_⟩,
    fun s => f ((), s), fun s => g ((), s),
    hf.comp ((ComputableIn.const ()).pair ComputableIn.id),
    hg.comp ((ComputableIn.const ()).pair ComputableIn.id),
    hfg (), hgf ()⟩
  have : 2 * s ≤ t := Finset.range_subset_range.1 hsub
  omega

-- Monotonicity of the target enumeration is necessary for `stageCompare_dom_of_stageLimit_subset`:
-- two enumerations with the same limit `{0, 1}` can have an everywhere-undefined `stageCompare`
-- when `B` alternates between `{0}` and `{1}`.
example :
    stageLimit (fun _ => ({0, 1} : Finset ℕ)) =
        stageLimit (fun s => if s % 2 = 0 then {0} else {1}) ∧
      ¬ (stageCompare (fun _ => ({0, 1} : Finset ℕ))
          (fun s => if s % 2 = 0 then {0} else {1}) 0).Dom := by
  constructor
  · ext x
    simp only [mem_stageLimit, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨_, rfl | rfl⟩
      · exact ⟨0, by simp⟩
      · exact ⟨1, by simp⟩
    · rintro ⟨s, hs⟩
      split_ifs at hs
      · exact ⟨0, Or.inl (by simpa using hs)⟩
      · exact ⟨0, Or.inr (by simpa using hs)⟩
  · rw [stageCompare_dom]
    rintro ⟨t, ht⟩
    split_ifs at ht
    · have : (1 : ℕ) ∈ ({0} : Finset ℕ) := ht (by simp)
      simp at this
    · have : (0 : ℕ) ∈ ({1} : Finset ℕ) := ht (by simp)
      simp at this

-- Relative to the nontrivial oracle `Z = {0}`, `Z.jump` admits a `Z`-computable serialized stage
-- enumeration with at most one new entry per stage, and `domStage` yields its limit directly.
example :
    ∃ A : ℕ → Finset ℕ, Monotone A ∧ A 0 = ∅ ∧ (∀ s, (fresh A s).card ≤ 1) ∧
      ComputableIn {({0} : Set ℕ).oracle} (fun s => Finset.equivBitIndices.symm (A s)) ∧
      stageLimit A = ({0} : Set ℕ).jump :=
  isSigma_one_iff_exists_serialized_stages.1 (isSigma_one_jump (Z := {0}))

-- Uniform oracle-program compilers act uniformly on domains for a concrete nontrivial total oracle
-- `O n = if n = 0 then 1 else 0`, and specialize cleanly to ordinary `Nat.Partrec.Code` via
-- `toPartrecCode`.
example :
    let O : ℕ → ℕ := fun n => if n = 0 then 1 else 0
    (Code.eval (O : ℕ →. ℕ) (Code.union Code.zero Code.oracle)).Dom = Set.univ ∧
      (Code.eval (O : ℕ →. ℕ) (Code.interList [Code.zero, Code.succ])).Dom = Set.univ ∧
      (Code.eval (O : ℕ →. ℕ) (Code.rangeDom Code.oracle)).Dom = {0, 1} ∧
      (Code.eval (O : ℕ →. ℕ) (Code.projDom (Code.restrictId Code.zero))).Dom = Set.univ := by
  intro O
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Code.dom_eval_union]
    ext x
    simp [PFun.Dom]
  · rw [Code.dom_eval_interList]
    ext x
    simp [PFun.Dom]
  · rw [Code.dom_eval_rangeDom]
    ext y
    simp only [Code.eval_oracle, PFun.ran, Set.mem_ofPred_eq, PFun.coe_val, Part.mem_some_iff,
      Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨x, rfl⟩
      dsimp [O]
      split_ifs <;> simp
    · rintro (rfl | rfl)
      · exact ⟨1, by simp [O]⟩
      · exact ⟨0, by simp [O]⟩
  · rw [Code.dom_eval_projDom, Code.dom_eval_restrictId]
    ext x
    simp [PFun.Dom]

-- Ordinary `Nat.Partrec.Code` index compilers have primitive recursive implementations and exact
-- domain equations.
example :
    Primrec Nat.Partrec.Code.unionList ∧
      Primrec₂ Nat.Partrec.Code.imageDom ∧
      (Nat.Partrec.Code.rangeDom Nat.Partrec.Code.succ).eval.Dom = {y | ∃ x, x + 1 = y} := by
  refine ⟨Nat.Partrec.Code.primrec_unionList, Nat.Partrec.Code.primrec₂_imageDom, ?_⟩
  rw [Nat.Partrec.Code.dom_eval_rangeDom]
  ext y
  simp [PFun.ran, Nat.Partrec.Code.eval, eq_comm]
