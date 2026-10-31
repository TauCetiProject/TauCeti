/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.Colex
public import Mathlib.Computability.RE
public import TauCeti.Computability.Enumeration.Stage
import TauCeti.Computability.Primrec.FiniteSet

/-!
# The canonical stage enumeration of a c.e. set

For a code `c` of a partial computable function, `c.domStage s` is the finite stage `W_{c,s}`:
the inputs on which `c` halts within `s` steps of Mathlib's step-bounded evaluation
`Nat.Partrec.Code.evaln`. Step-bounded evaluation only succeeds on inputs below the step bound,
so `W_{c,s} ⊆ [0, s)`; unlike Soare's convention, neither the code nor the output is bounded.

These stages start empty, increase with `s`, and their limit is the domain `W_c` of `c`. Their
binary finite-set codes `∑ x ∈ W_{c,s}, 2 ^ x` are primitive recursive uniformly in the code and
the stage, so they form a uniformly indexed family of effective enumerations of all c.e. sets.

Conversely, the limit of finite stages with computable membership is c.e. Together these give
the stage characterization of c.e. predicates on `ℕ`: a predicate is c.e. exactly when it is the
union of an increasing sequence of finite sets, starting empty, whose binary codes are
computable.

These are raw simulation stages, not a serialized enumeration: several numbers may enter at the
same stage.

## Main definitions

* `Nat.Partrec.Code.domStage`: the stage `W_{c,s}` of the domain of a code.

## Main results

* `Nat.Partrec.Code.domStage_zero`, `Nat.Partrec.Code.monotone_domStage`: the stages start empty
  and increase.
* `Nat.Partrec.Code.stageLimit_domStage`: their limit is the domain of the code.
* `Nat.Partrec.Code.primrec₂_evaln_isSome`: halting of step-bounded evaluation is primitive
  recursive in the code, the step bound and the input.
* `Nat.Partrec.Code.primrecRel_mem_domStage`, `Nat.Partrec.Code.primrec_domStage`: membership in
  the stages and their binary codes are primitive recursive, uniformly in the code and the stage.
* `TauCeti.Enumeration.rePred_mem_stageLimit`: the limit of finite stages with computable
  membership is c.e.
* `TauCeti.Enumeration.rePred_iff_exists_stages`: a predicate on `ℕ` is c.e. if and only if it is
  the limit of increasing finite stages, starting empty, with computable binary codes.

## References

* R. I. Soare, *Recursively Enumerable Sets and Degrees*, Springer, 1987, Chapters I.3 and II.1.
-/

public section

open TauCeti.Enumeration

namespace Nat.Partrec.Code

/-- The stage `W_{c,s}` of the domain of the code `c`: the inputs on which `c` halts within `s`
steps of step-bounded evaluation. -/
def domStage (c : Code) (s : ℕ) : Finset ℕ :=
  (Finset.range s).filter fun x => (evaln s c x).isSome

variable {c : Code} {s x : ℕ}

/-- A number is in `W_{c,s}` exactly when `c` halts on it within `s` steps. -/
@[simp]
theorem mem_domStage : x ∈ c.domStage s ↔ (evaln s c x).isSome := by
  rw [domStage, Finset.mem_filter, Finset.mem_range, and_iff_right_iff_imp]
  intro h
  obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp h
  exact evaln_bound hy

/-- Every input enumerated by stage `s` is smaller than `s`. -/
theorem domStage_subset_range (c : Code) (s : ℕ) : c.domStage s ⊆ Finset.range s :=
  Finset.filter_subset _ _

/-- No computation halts within zero steps, so the stages start empty. -/
@[simp]
theorem domStage_zero (c : Code) : c.domStage 0 = ∅ := by
  simp [domStage]

/-- The stages of the domain of a code increase. -/
theorem monotone_domStage (c : Code) : Monotone c.domStage := by
  intro s t hst x
  simp only [mem_domStage, Option.isSome_iff_exists]
  exact fun ⟨y, hy⟩ => ⟨y, evaln_mono hst hy⟩

/-- The limit of the stages of the domain of a code is its domain `W_c`. -/
@[simp]
theorem stageLimit_domStage (c : Code) : stageLimit c.domStage = {x | (eval c x).Dom} := by
  ext x
  simp only [mem_stageLimit, mem_domStage, Option.isSome_iff_exists, Set.mem_ofPred_eq,
    Part.dom_iff_mem, evaln_complete]
  exact exists_comm

/-- Halting of step-bounded evaluation is primitive recursive in the code, the step bound and the
input. -/
theorem primrec₂_evaln_isSome :
    Primrec₂ fun (p : Code × ℕ) (x : ℕ) => (evaln p.2 p.1 x).isSome :=
  Primrec.option_isSome.comp (primrec_evaln.comp
    ((_root_.Primrec.pair (Primrec.snd.comp Primrec.fst) (Primrec.fst.comp Primrec.fst)).pair
      Primrec.snd))

/-- Membership in the stages of the domain of a code is primitive recursive, uniformly in the
code, the stage and the number. -/
theorem primrecRel_mem_domStage : PrimrecRel fun (p : Code × ℕ) x => x ∈ p.1.domStage p.2 :=
  (_root_.Primrec.eq.comp primrec₂_evaln_isSome (_root_.Primrec.const true)).of_eq fun p => by
    simp

/-- The binary finite-set codes `∑ x ∈ W_{c,s}, 2 ^ x` of the stages of the domain of a code are
primitive recursive, uniformly in the code and the stage. -/
theorem primrec_domStage :
    Primrec fun p : Code × ℕ => Finset.equivBitIndices.symm (p.1.domStage p.2) := by
  refine (Primrec.nat_filterBitIndices (Primrec.nat_sub.comp
    (Primrec.nat_pow.comp (_root_.Primrec.const 2) Primrec.snd) (_root_.Primrec.const 1))
    Primrec.snd primrec₂_evaln_isSome).of_eq fun p => ?_
  apply Finset.equivBitIndices.injective
  ext x
  simp [Nat.testBit_two_pow_sub_one, domStage]

end Nat.Partrec.Code

namespace TauCeti

namespace Enumeration

open Nat.Partrec

/-- The limit of finite stages is c.e. when membership in the stages is computable, uniformly in
the stage and the number. -/
theorem rePred_mem_stageLimit {A : ℕ → Finset ℕ}
    (hA : ComputablePred fun p : ℕ × ℕ => p.2 ∈ A p.1) :
    REPred fun x => x ∈ stageLimit A := by
  have hfind : Partrec fun x => Nat.rfind fun s => Part.some (decide (x ∈ A s)) :=
    Partrec.rfind (hA.decide.comp (Computable.snd.pair Computable.fst)).partrec
  refine hfind.dom_re.of_eq fun x => ?_
  refine Nat.rfind_dom.trans ?_
  simp [mem_stageLimit]

/-- A predicate on `ℕ` is c.e. if and only if it is the limit of increasing finite stages,
starting empty, whose binary finite-set codes are computable. -/
theorem rePred_iff_exists_stages {p : ℕ → Prop} :
    REPred p ↔ ∃ A : ℕ → Finset ℕ, Monotone A ∧ A 0 = ∅ ∧
      Computable (fun s => Finset.equivBitIndices.symm (A s)) ∧ stageLimit A = {x | p x} := by
  constructor
  · intro hp
    obtain ⟨c, hc⟩ := Code.exists_code.mp (Partrec.nat_iff.mp (hp.map (Computable.const 0).to₂))
    refine ⟨c.domStage, c.monotone_domStage, c.domStage_zero,
      (Code.primrec_domStage.comp ((Primrec.const c).pair Primrec.id)).to_comp, ?_⟩
    rw [Code.stageLimit_domStage, hc]
    ext x
    simp [Part.dom_iff_mem, Part.mem_assert_iff]
  · rintro ⟨A, -, -, hA, hlim⟩
    have hmem : ComputablePred fun q : ℕ × ℕ => q.2 ∈ A q.1 :=
      (Primrec.mem_equivBitIndices.comp Primrec.fst Primrec.snd).decide.to_comp.comp
        (hA.comp Computable.fst |>.pair Computable.snd) |>.computablePred.of_eq fun q => by simp
    exact (rePred_mem_stageLimit hmem).of_eq fun x => by rw [hlim, Set.mem_ofPred_eq]

end Enumeration

end TauCeti
