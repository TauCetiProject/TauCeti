/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Computability.Approximation.Modulus
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

The converse, that every function computable in `Z'` is such a limit, is not proved here.

## Main results

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

variable {Z : Set ℕ} {f : ℕ → ℕ → ℕ} {g : ℕ → ℕ}

/-- The stages `s` of a sequence `f` after which the value at `x` changes, coded as
`Nat.pair x s`, form a set c.e. in `Z` when `f` is computable in `Z`. -/
private theorem recursiveIn_unstable (hf : ComputableIn₂ {Z.oracle} f) :
    ∃ F : ℕ →. ℕ, Nat.RecursiveIn {Z.oracle} F ∧
      ∀ n, (F n).Dom ↔ ∃ t, f (n.unpair.2 + t) n.unpair.1 ≠ f n.unpair.2 n.unpair.1 := by
  -- `f` as a function on codes of pairs `Nat.pair s x`
  have hF : Nat.RecursiveIn {Z.oracle} fun n => Part.some (f n.unpair.1 n.unpair.2) :=
    ComputableIn₂.iff_nat.1 hf
  -- on `Nat.pair (Nat.pair x s) t`, the values `f (s + t) x` and `f s x`
  have h₁ := hF.comp_primrec (g := fun m =>
    Nat.pair (m.unpair.1.unpair.2 + m.unpair.2) m.unpair.1.unpair.1) <|
    Primrec.nat_iff.1 <| Primrec₂.natPair.comp
      (Primrec.nat_add.comp (Primrec.snd.comp <| Primrec.unpair.comp <|
        Primrec.fst.comp Primrec.unpair) (Primrec.snd.comp Primrec.unpair))
      (Primrec.fst.comp <| Primrec.unpair.comp <| Primrec.fst.comp Primrec.unpair)
  have h₂ := hF.comp_primrec (g := fun m => Nat.pair m.unpair.1.unpair.2 m.unpair.1.unpair.1) <|
    Primrec.nat_iff.1 <| Primrec₂.natPair.comp
      (Primrec.snd.comp <| Primrec.unpair.comp <| Primrec.fst.comp Primrec.unpair)
      (Primrec.fst.comp <| Primrec.unpair.comp <| Primrec.fst.comp Primrec.unpair)
  -- compare them: `0` when they differ, `1` when they agree
  have hq := (h₁.pair h₂).map_primrec (g := fun p => if p.unpair.1 = p.unpair.2 then 1 else 0) <|
    Primrec.nat_iff.1 <| Primrec.ite
      (Primrec.eq.comp (Primrec.fst.comp Primrec.unpair) (Primrec.snd.comp Primrec.unpair))
      (Primrec.const 1) (Primrec.const 0)
  refine ⟨_, hq.rfind, fun n => ?_⟩
  simp only [Seq.seq, Nat.unpair_pair, Part.map_some]
  refine ⟨fun hd => ?_, fun ⟨t, ht⟩ => Nat.rfind_dom.2 ⟨t, by simpa using ht, fun _ => by simp⟩⟩
  obtain ⟨t, ht, -⟩ := Nat.rfind_dom.1 hd
  exact ⟨t, by simpa using ht⟩

/-- **Limit Lemma, computing the limit.** If the stages `f s` are computable in `Z`, uniformly in
`s`, and converge pointwise to `g`, then `g` is computable in the jump `Z'`. -/
theorem Converges.computableIn_jump (h : Converges f g) (hf : ComputableIn₂ {Z.oracle} f) :
    ComputableIn {Z.jump.oracle} g := by
  classical
  obtain ⟨F, hF, hFdom⟩ := recursiveIn_unstable hf
  -- the set of codes `Nat.pair x s` of stages after which the value at `x` changes
  set U : Set ℕ := {n | (F n).Dom}
  have hU : Nat.RecursiveIn {Z.jump.oracle} U.oracle :=
    RecursiveIn.iff_nat.1 (Z.turingReducible_jump_of_recursiveIn hF)
  -- the least stage `s` with `Nat.pair x s ∉ U`
  have hS := hU.rfind
  -- `f` relative to the jump
  have hfJ : Nat.RecursiveIn {Z.jump.oracle} fun n => Part.some (f n.unpair.1 n.unpair.2) :=
    (ComputableIn₂.iff_nat.1 hf).subst
      fun _ hg => (Set.mem_singleton_iff.1 hg) ▸ RecursiveIn.iff_nat.1 Z.turingReducible_jump
  refine RecursiveIn.iff_nat.2 <| (hfJ.comp (hS.pair Nat.Primrec.id.recursiveIn)).of_eq_tot
    fun x => ?_
  -- the stages after which the value at `x` no longer changes
  have hex : ∃ s, ∀ t, f (s + t) x = f s x := by
    obtain ⟨s, hs⟩ := Approximation.converges_iff_forall_exists.1 h x
    exact ⟨s, fun t => (hs _ (Nat.le_add_right s t)).trans (hs s le_rfl).symm⟩
  have hmem : Nat.find hex ∈ Nat.rfind fun s =>
      (fun m => decide (m = 0)) <$> U.oracle (Nat.pair x s) := by
    refine Nat.mem_rfind.2 ⟨?_, fun {m} hm => ?_⟩
    · have : Nat.pair x (Nat.find hex) ∉ U := by
        simpa [U, hFdom] using Nat.find_spec hex
      simp [this]
    · have : Nat.pair x m ∈ U := by
        simpa [U, hFdom] using Nat.find_min hex hm
      simp [this]
  have hlim : f (Nat.find hex) x = g x := h.apply_eq_of_forall_le fun t ht => by
    simpa [Nat.add_sub_cancel' ht] using Nat.find_spec hex (t - Nat.find hex)
  rw [Part.eq_some_iff.2 hmem]
  simp [Seq.seq, hlim]

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
