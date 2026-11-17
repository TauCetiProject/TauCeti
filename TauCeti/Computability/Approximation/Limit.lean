/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Computability.Approximation.Instability
public import TauCeti.Computability.Jump.Basic
import TauCeti.Computability.RecursiveIn

/-!
# Limits of uniformly computable sequences are computable in the jump

Let `f : ℕ → ℕ → ℕ` be a sequence of total functions, read as the stages `f s`, which is
computable in a set `Z` uniformly in the stage, and which converges pointwise to `g : ℕ → ℕ`.
Then `g` is computable in the jump `Z'`. This is the direction of the **Limit Lemma** used to bound
the jump of a constructed set: to show `A' ≤_T ∅'` it suffices to approximate the characteristic
function of `A'` by a computable sequence of guesses which is eventually correct at each point.

The algorithm computing `g x` relative to `Z'` searches for the least stage `s` after which the
value at `x` no longer changes, and returns `f s x`. Whether a stage is such a stage is a
question with a `Z`-c.e. negation, the existence of a later stage with a different value, so `Z'`
answers it. No modulus of convergence is needed, and none need be computable in `Z`.
If a modulus is computable in the original oracles, evaluating at that modulus already
computes the limit in those oracles, without passing to the jump.

The converse, that every function computable in `Z'` is such a limit, is proved in
`TauCeti.Computability.Approximation.Jump`.

## Main results

* `TauCeti.Approximation.IsModulus.computableIn`: a uniformly oracle-computable sequence with
  an oracle-computable modulus has an oracle-computable limit.
* `TauCeti.Approximation.Converges.computableIn_jump`: the limit of a sequence computable in `Z`
  is computable in `Z'`.
* `TauCeti.Approximation.Converges.turingReducible_jump`: the characteristic-function form, a set
  whose characteristic function is such a limit is Turing reducible to `Z'`.
* `TauCeti.Approximation.Converges.turingReducible_jump_empty`: the unrelativized form, a set
  whose characteristic function is the limit of a computable sequence is Turing reducible to
  `∅'`.

## References

* R. I. Soare, *Recursively Enumerable Sets and Degrees*, Springer, 1987, Chapter III.3, Limit
  Lemma III.3.3.
-/

public section

open Encodable

namespace TauCeti

namespace Approximation

/-- **Oracle-computable modulus, oracle-computable limit.** A uniformly oracle-computable
sequence with a modulus computable in the same oracles has a limit computable in those oracles. -/
theorem IsModulus.computableIn {α β : Type*} [Primcodable α] [Primcodable β]
    {O : Set (ℕ →. ℕ)} {f : ℕ → α → β} {g : α → β} {m : α → ℕ}
    (hm : IsModulus f g m) (hf : ComputableIn₂ O f) (hmc : ComputableIn O m) :
    ComputableIn O g :=
  RecursiveIn.of_eq (hf.comp (hmc.pair ComputableIn.id))
    fun x => congrArg Part.some (hm.apply_eq x)

variable {Z : Set ℕ} {f : ℕ → ℕ → ℕ} {g : ℕ → ℕ}

/-- **Limit Lemma, computing the limit.** If the stages `f s` are computable in `Z`, uniformly in
`s`, and converge pointwise to `g`, then `g` is computable in the jump `Z'`. -/
theorem Converges.computableIn_jump (h : Converges f g) (hf : ComputableIn₂ {Z.oracle} f) :
    ComputableIn {Z.jump.oracle} g := by
  obtain ⟨F, hF, hFdom⟩ := exists_recursiveIn_dom_iff_mem_instabilitySet hf
  have hU : TuringReducible (instabilitySet f).oracle Z.jump.oracle := by
    have hdom : {n | (F n).Dom} = instabilitySet f := Set.ext hFdom
    rw [← hdom]
    exact Z.turingReducible_jump_of_recursiveIn hF
  have hfJ : ComputableIn₂ {Z.jump.oracle} f :=
    ComputableIn₂.iff_nat.2 <| (ComputableIn₂.iff_nat.1 hf).subst
      fun _ hg => (Set.mem_singleton_iff.1 hg) ▸ RecursiveIn.iff_nat.1 Z.turingReducible_jump
  exact h.computableIn_of_instabilitySet hfJ hU

/-- **Limit Lemma for sets.** If the stages `f s` are computable in `Z`, uniformly in `s`, and
converge pointwise to the characteristic function of `A`, then `A` is Turing reducible to the
jump `Z'`. -/
theorem Converges.turingReducible_jump {A : Set ℕ} (h : Converges f (A.indicator 1))
    (hf : ComputableIn₂ {Z.oracle} f) : TuringReducible A.oracle Z.jump.oracle :=
  RecursiveIn.iff_nat.2 <| (RecursiveIn.iff_nat.1 (h.computableIn_jump hf)).of_eq fun n =>
    (Set.oracle_apply A n).symm

/-- **Limit Lemma for sets, unrelativized.** If a computable sequence `f` converges pointwise to
the characteristic function of `A`, then `A` is Turing reducible to the halting set `∅'`. -/
theorem Converges.turingReducible_jump_empty {A : Set ℕ} (h : Converges f (A.indicator 1))
    (hf : Computable₂ f) : TuringReducible A.oracle (∅ : Set ℕ).jump.oracle :=
  h.turingReducible_jump hf.computableIn

end Approximation

end TauCeti
