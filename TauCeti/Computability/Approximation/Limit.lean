/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Computability.Approximation.Modulus
public import TauCeti.Computability.Jump.Basic
public import TauCeti.Computability.RecursiveIn

/-!
# Limits of uniformly computable sequences are computable in the jump

This file proves the direction of Shoenfield's Limit Lemma [Soare, III.3.3] that bounds the
complexity of a limit, relative to an arbitrary oracle set `Z`: if a sequence of total functions
`f s : ℕ → ℕ` is uniformly computable in `Z` and converges pointwise to `g`, then `g` is
computable in the jump `Z'`.

The proof finds a modulus of convergence computable in `Z'`. Whether the value at `x` changes at
some stage after `s` is a question c.e. in `Z`, so `Z'` decides it, and the least stage `s` after
which the value at `x` no longer changes can be found by a search relative to `Z'`. Evaluating the
sequence at that stage gives the limit. The second step is the relativized form of the fact that a
uniformly computable sequence with a computable modulus has a computable limit.

Taking `Z = ∅` gives the classical statement that limits of uniformly computable sequences are
computable in the halting problem `∅'`. Applied to the characteristic function of a set `B`, it
reduces `B` to `Z'` once `B` has a `Z`-computable approximation; this is how lowness of a set `A`,
the reduction `A' ≤_T ∅'`, is obtained from a computable approximation of its jump.

## Main results

* `TauCeti.Approximation.IsModulus.computableIn`: a sequence uniformly computable in `O` with a
  modulus computable in `O` has a limit computable in `O`.
* `TauCeti.Approximation.Converges.exists_isModulus_computableIn_jump`: a sequence uniformly
  computable in `Z` and converging pointwise has a modulus computable in `Z'`.
* `TauCeti.Approximation.Converges.computableIn_jump`: **Limit Lemma**, the limit of a sequence
  uniformly computable in `Z` is computable in `Z'`.
* `TauCeti.Approximation.Converges.turingReducible_jump`: a set whose characteristic function is
  the limit of a sequence uniformly computable in `Z` is Turing reducible to `Z'`.

## References

* R. I. Soare, *Recursively Enumerable Sets and Degrees*, Springer, 1987, Chapter III.3.
-/

public section

open Encodable

namespace TauCeti

namespace Approximation

section Modulus

variable {O : Set (ℕ →. ℕ)} {α β : Type*} [Primcodable α] [Primcodable β]
  {f : ℕ → α → β} {g : α → β} {m : α → ℕ}

/-- **Modulus computable in `O`, limit computable in `O`.** A sequence uniformly computable in `O`
with a modulus computable in `O` has a limit computable in `O`: evaluate the sequence at the stage
given by the modulus. This is the relative form of `TauCeti.Approximation.IsModulus.computable`. -/
theorem IsModulus.computableIn (hm : IsModulus f g m) (hf : ComputableIn₂ O f)
    (hmc : ComputableIn O m) : ComputableIn O g := by
  -- `ComputableIn` and `ComputableIn₂` are `Nat.RecursiveIn` on codes: on the code of `a`, compute
  -- `Nat.pair (m a) (encode a)`, which is the code of `(m a, a)`, and apply `f` to it
  refine (Nat.RecursiveIn.comp hf (hmc.pair Nat.Primrec.id.recursiveIn)).of_eq fun n => ?_
  cases h : decode (α := α) n <;> simp [Seq.seq, h, decode_prod_val, ← hm.apply_eq]

end Modulus

variable {Z : Set ℕ} {f : ℕ → ℕ → ℕ} {g : ℕ → ℕ}

/-- The codes `Nat.pair x s` such that the value of the sequence at `x` changes at some stage after
`s` form a set c.e. in `Z`, so its oracle is computable in `Z'`. -/
private theorem turingReducible_changes_jump (hf : ComputableIn₂ {Z.oracle} f) :
    TuringReducible {a | ∃ t, f (a.unpair.2 + t) a.unpair.1 ≠ f a.unpair.2 a.unpair.1}.oracle
      Z.jump.oracle := by
  have hF := ComputableIn₂.nat_iff.1 hf
  -- the codes of the stages `s + t` and `s` at the point `x`, read off `Nat.pair (Nat.pair x s) t`
  have h₁ : Nat.Primrec fun q : ℕ =>
      Nat.pair (q.unpair.1.unpair.2 + q.unpair.2) q.unpair.1.unpair.1 :=
    Primrec.nat_iff.1 <| Primrec₂.natPair.comp
      (Primrec.nat_add.comp (Primrec.snd.comp <| Primrec.unpair.comp <|
        Primrec.fst.comp Primrec.unpair) (Primrec.snd.comp Primrec.unpair))
      (Primrec.fst.comp <| Primrec.unpair.comp <| Primrec.fst.comp Primrec.unpair)
  have h₂ : Nat.Primrec fun q : ℕ => Nat.pair q.unpair.1.unpair.2 q.unpair.1.unpair.1 :=
    Primrec.nat_iff.1 <| Primrec₂.natPair.comp
      (Primrec.snd.comp <| Primrec.unpair.comp <| Primrec.fst.comp Primrec.unpair)
      (Primrec.fst.comp <| Primrec.unpair.comp <| Primrec.fst.comp Primrec.unpair)
  -- `1` when the two values agree and `0` when they differ
  have h₃ : Nat.Primrec fun p : ℕ => if p.unpair.1 = p.unpair.2 then 1 else 0 :=
    Primrec.nat_iff.1 <| Primrec.ite (PrimrecRel.comp Primrec.eq
      (Primrec.fst.comp Primrec.unpair) (Primrec.snd.comp Primrec.unpair))
      (Primrec.const 1) (Primrec.const 0)
  -- the search for a change halts exactly on the codes in the set
  have hs := (((hF.comp_primrec h₁).pair (hF.comp_primrec h₂)).map_primrec h₃).rfind
  refine (congrArg (fun C : Set ℕ => TuringReducible C.oracle Z.jump.oracle)
    (Set.ext fun a => ?_)).mp (Z.turingReducible_jump_of_recursiveIn hs)
  simp only [Seq.seq, Set.mem_ofPred_eq]
  exact Nat.rfind_dom.trans (by simp)

/-- A sequence of functions `ℕ → ℕ` that is uniformly computable in `Z` and converges pointwise
has a modulus of convergence computable in the jump `Z'`: the least stage after which the value no
longer changes. -/
theorem Converges.exists_isModulus_computableIn_jump (hf : ComputableIn₂ {Z.oracle} f)
    (h : Converges f g) : ∃ m, IsModulus f g m ∧ ComputableIn {Z.jump.oracle} m := by
  -- `Nat.pair x s ∈ C` when the value at `x` changes at some stage after `s`
  set C : Set ℕ := {a | ∃ t, f (a.unpair.2 + t) a.unpair.1 ≠ f a.unpair.2 a.unpair.1}
  have hC {x s : ℕ} : Nat.pair x s ∈ C ↔ ∃ t, f (s + t) x ≠ f s x := by
    simp [C]
  -- by convergence, the value at `x` eventually stops changing
  have hex (x : ℕ) : ∃ s, Nat.pair x s ∉ C := by
    obtain ⟨s, hs⟩ := converges_iff_forall_exists.1 h x
    exact ⟨s, fun hx => by
      obtain ⟨t, ht⟩ := hC.1 hx
      exact ht ((hs _ (by omega)).trans (hs _ le_rfl).symm)⟩
  classical
  refine ⟨fun x => Nat.find (hex x), isModulus_iff.2 fun x s hs => ?_, ?_⟩
  · obtain ⟨s₁, hs₁⟩ := converges_iff_forall_exists.1 h x
    have hst := not_exists_not.1 (mt hC.2 (Nat.find_spec (hex x)))
    rw [← Nat.add_sub_cancel' hs, hst, ← hst s₁, hs₁ _ (by omega)]
  · -- search the oracle of `C`, which is computable in the jump
    refine ComputableIn.nat_iff.2 <|
      ((Nat.RecursiveIn.oracle C.oracle (Set.mem_singleton _)).rfind.subst ?_).of_eq fun x => ?_
    · rintro _ rfl
      exact RecursiveIn.iff_nat.1 (turingReducible_changes_jump hf)
    · refine Part.eq_some_iff.2 (Nat.mem_rfind.2 ⟨?_, fun hlt => ?_⟩)
      · simp [Nat.find_spec (hex x)]
      · simpa using Nat.find_min (hex x) hlt

/-- **Limit Lemma.** The pointwise limit of a sequence of functions `ℕ → ℕ` that is uniformly
computable in `Z` is computable in the jump `Z'`. -/
theorem Converges.computableIn_jump (hf : ComputableIn₂ {Z.oracle} f) (h : Converges f g) :
    ComputableIn {Z.jump.oracle} g := by
  obtain ⟨m, hm, hmc⟩ := h.exists_isModulus_computableIn_jump hf
  exact hm.computableIn (RecursiveIn.subst hf fun _ h => h ▸ Z.turingReducible_jump) hmc

/-- **Limit Lemma for sets.** If the characteristic function of `B` is the pointwise limit of a
sequence uniformly computable in `Z`, then `B` is Turing reducible to the jump `Z'`. -/
theorem Converges.turingReducible_jump {B : Set ℕ} (hf : ComputableIn₂ {Z.oracle} f)
    (h : Converges f (B.indicator 1)) : TuringReducible B.oracle Z.jump.oracle :=
  (h.computableIn_jump hf).of_eq fun n => (B.oracle_apply n).symm

end Approximation

end TauCeti
