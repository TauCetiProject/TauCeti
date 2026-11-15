/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Computability.Approximation.Jump
public import TauCeti.Computability.Hierarchy.Post

/-!
# The Limit Lemma for `Δ⁰₂` sets and predicates

Combining the relativized Limit Lemma (`TauCeti.Approximation.Jump`) with the `Δ⁰₂` case of the
relativized Post theorem (`TauCeti.Computability.Hierarchy.Post`) characterizes `Δ⁰₂(Z)` sets and
predicates by pointwise eventually constant approximations computable uniformly in `Z`:

* `TauCeti.Approximation.isDelta_two_mem_iff_exists_converges`: `A ∈ Δ⁰₂(Z)` iff the characteristic
  function `A.indicator 1` is the pointwise limit of a sequence of total functions computable
  uniformly in `Z`.
* `TauCeti.Approximation.computableIn_jump_empty_iff_exists_converges`,
  `TauCeti.Approximation.turingReducible_jump_empty_iff_exists_converges`,
  `TauCeti.Approximation.isDelta_two_empty_mem_iff_exists_converges`: the unrelativized Limit Lemma
  for total functions computable in `∅'`, sets Turing reducible to `∅'`, and `Δ⁰₂` sets.
* `TauCeti.Approximation.isDelta_two_iff_exists_converges`,
  `TauCeti.Approximation.isDelta_two_empty_iff_exists_converges`: the general Boolean-approximation
  form for predicates on any primitive-codable type.

## References

* R. I. Soare, *Recursively Enumerable Sets and Degrees*, Springer, 1987, Limit Lemma III.3.3 and
  Post's Theorem IV.2.2.
-/

public section

open Encodable Filter TauCeti.ArithmeticalHierarchy

namespace TauCeti.Approximation

private theorem computableIn_oracle_empty_iff {α β : Type*} [Primcodable α] [Primcodable β]
    {f : α → β} : ComputableIn {(∅ : Set ℕ).oracle} f ↔ Computable f := by
  refine ⟨fun hf => hf.partrec_of_oracle fun g hg => ?_, Computable.computableIn⟩
  rw [Set.mem_singleton_iff.1 hg, Set.oracle_empty]
  exact Partrec.const' _

/-- **The unrelativized Limit Lemma for functions.** A total function `g : ℕ → ℕ` is computable in
the halting set `∅'` iff it is the pointwise eventually constant limit of a uniformly computable
sequence of total functions. -/
theorem computableIn_jump_empty_iff_exists_converges {g : ℕ → ℕ} :
    ComputableIn {(∅ : Set ℕ).jump.oracle} g ↔
      ∃ f : ℕ → ℕ → ℕ, Computable₂ f ∧ Converges f g := by
  rw [computableIn_jump_iff_exists_converges]
  exact exists_congr fun f => and_congr computableIn_oracle_empty_iff Iff.rfl

/-- **The unrelativized Limit Lemma for sets.** A set `A` is Turing reducible to `∅'` iff its
characteristic function is the pointwise eventually constant limit of a uniformly computable
sequence of total functions. -/
theorem turingReducible_jump_empty_iff_exists_converges {A : Set ℕ} :
    TuringReducible A.oracle (∅ : Set ℕ).jump.oracle ↔
      ∃ f : ℕ → ℕ → ℕ, Computable₂ f ∧ Converges f (A.indicator 1) := by
  rw [turingReducible_jump_iff_exists_converges]
  exact exists_congr fun f => and_congr computableIn_oracle_empty_iff Iff.rfl

/-- **The relativized `Δ⁰₂` Limit Lemma for sets.** A set `A` belongs to `Δ⁰₂(Z)` iff its
characteristic function is the pointwise eventually constant limit of a sequence of total functions
computable uniformly in `Z`. -/
theorem isDelta_two_mem_iff_exists_converges {Z A : Set ℕ} :
    IsDelta Z 2 (· ∈ A) ↔
      ∃ f : ℕ → ℕ → ℕ, ComputableIn₂ {Z.oracle} f ∧ Converges f (A.indicator 1) :=
  isDelta_two_mem_iff_turingReducible_jump.trans turingReducible_jump_iff_exists_converges

/-- **The `Δ⁰₂` Limit Lemma for sets.** A set `A` belongs to `Δ⁰₂` (relative to the empty oracle)
iff its characteristic function is the pointwise eventually constant limit of a uniformly
computable sequence of total functions. -/
theorem isDelta_two_empty_mem_iff_exists_converges {A : Set ℕ} :
    IsDelta ∅ 2 (· ∈ A) ↔
      ∃ f : ℕ → ℕ → ℕ, Computable₂ f ∧ Converges f (A.indicator 1) :=
  isDelta_two_mem_iff_turingReducible_jump.trans turingReducible_jump_empty_iff_exists_converges

/-- **The relativized `Δ⁰₂` Limit Lemma for predicates.** A predicate `p` on a primitive-codable
type belongs to `Δ⁰₂(Z)` iff it has a Boolean decision function obtained as the pointwise
eventually constant limit of a sequence of total Boolean functions computable uniformly in `Z`. -/
theorem isDelta_two_iff_exists_converges {Z : Set ℕ} {α : Type*} [Primcodable α] {p : α → Prop} :
    IsDelta Z 2 p ↔
      ∃ (f : ℕ → α → Bool) (b : α → Bool),
        ComputableIn₂ {Z.oracle} f ∧ Converges f b ∧ ∀ x, b x = true ↔ p x := by
  rw [isDelta_succ_iff_isSigma_zero_iterate_jump (Z := Z) (n := 1), Function.iterate_one,
    isSigma_zero_iff]
  have h01 : Primrec (fun c : Bool => cond c 1 0) := Primrec.dom_bool _
  constructor
  · rintro ⟨b, hb, heq⟩
    let g : ℕ → ℕ := fun n =>
      Option.casesOn (motive := fun _ => ℕ) (decode (α := α) n) 0 (fun x => cond (b x) 1 0)
    have hg : ComputableIn {Z.jump.oracle} g :=
      ComputableIn.option_casesOn Computable.decode.computableIn (ComputableIn.const 0)
        ((h01.computableIn.comp hb).comp ComputableIn.snd)
    obtain ⟨f₀, hf₀, hconv₀⟩ := computableIn_jump_iff_exists_converges.1 hg
    refine ⟨fun s x => f₀ s (encode x) == 1, b, ?_, ?_, heq⟩
    · exact (Primrec.beq.comp Primrec.id (Primrec.const 1)).computableIn.comp
        (hf₀.comp (ComputableIn.fst.pair (Primrec.encode.computableIn.comp ComputableIn.snd)))
    · refine converges_iff_eventually.2 fun x => ?_
      refine (converges_iff_eventually.1 hconv₀ (encode x)).mono fun s hs => ?_
      rw [hs]
      simp only [g, encodek]
      cases b x <;> rfl
  · rintro ⟨f, b, hf, hconv, heq⟩
    let f₀ : ℕ → ℕ → ℕ := fun s n =>
      Option.casesOn (motive := fun _ => ℕ) (decode (α := α) n) 0 (fun x => cond (f s x) 1 0)
    let g : ℕ → ℕ := fun n =>
      Option.casesOn (motive := fun _ => ℕ) (decode (α := α) n) 0 (fun x => cond (b x) 1 0)
    have hf₀ : ComputableIn₂ {Z.oracle} f₀ :=
      ComputableIn.option_casesOn (Computable.decode.computableIn.comp ComputableIn.snd)
        (ComputableIn.const 0)
        ((h01.computableIn.comp hf).comp
          ((ComputableIn.fst.comp ComputableIn.fst).pair ComputableIn.snd))
    have hconv₀ : Converges f₀ g := converges_iff_eventually.2 fun n => by
      cases hdec : decode (α := α) n with
      | none => exact Eventually.of_forall fun _ => by simp [f₀, g, hdec]
      | some x =>
        exact (converges_iff_eventually.1 hconv x).mono fun s hs => by simp [f₀, g, hdec, hs]
    have hg : ComputableIn {Z.jump.oracle} g := hconv₀.computableIn_jump hf₀
    refine ⟨b, ?_, heq⟩
    refine ((Primrec.beq.comp Primrec.id (Primrec.const 1)).computableIn.comp
      (hg.comp Primrec.encode.computableIn)).of_eq fun x => ?_
    congr 1
    simp only [g, encodek]
    cases b x <;> rfl

/-- **The `Δ⁰₂` Limit Lemma for predicates.** A predicate `p` on a primitive-codable type belongs
to `Δ⁰₂` (relative to the empty oracle) iff it has a Boolean decision function obtained as the
pointwise eventually constant limit of a uniformly computable sequence of total Boolean
functions. -/
theorem isDelta_two_empty_iff_exists_converges {α : Type*} [Primcodable α] {p : α → Prop} :
    IsDelta ∅ 2 p ↔
      ∃ (f : ℕ → α → Bool) (b : α → Bool),
        Computable₂ f ∧ Converges f b ∧ ∀ x, b x = true ↔ p x := by
  rw [isDelta_two_iff_exists_converges]
  exact exists_congr fun f => exists_congr fun _ =>
    and_congr computableIn_oracle_empty_iff Iff.rfl

end TauCeti.Approximation
