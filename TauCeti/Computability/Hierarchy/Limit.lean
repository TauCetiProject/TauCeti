/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Computability.Approximation.Jump
public import TauCeti.Computability.Hierarchy.Post

/-!
# The `Δ⁰₂` Limit Lemma

Combining relativized Post's theorem (`TauCeti.Computability.Hierarchy.Post`), which identifies
`Δ⁰₂(Z)` predicates and sets with those computable in `Z'`, and the jump Limit Lemma
(`TauCeti.Computability.Approximation.Jump`), which identifies functions computable in `Z'` with
pointwise eventually constant limits of uniformly `Z`-computable sequences, yields the
pointclass forms of the **Limit Lemma**:

* a set of natural numbers is `Δ⁰₂(Z)` (respectively `Δ⁰₂`) if and only if its characteristic
  function is the pointwise limit of a uniformly `Z`-computable (respectively computable)
  sequence;
* a predicate on any primitive-codable type is `Δ⁰₂(Z)` (respectively `Δ⁰₂`) if and only if it
  has a uniformly `Z`-computable (respectively computable) Boolean approximation converging
  pointwise to a total deciding function.

No stabilization modulus is supplied or assumed computable.

## Main results

* `TauCeti.ArithmeticalHierarchy.isDelta_two_mem_iff_exists_converges`,
  `TauCeti.ArithmeticalHierarchy.isDelta_two_empty_mem_iff_exists_converges`: `Δ⁰₂` Limit Lemma
  for sets of natural numbers.
* `TauCeti.ArithmeticalHierarchy.isDelta_two_iff_exists_converges`,
  `TauCeti.ArithmeticalHierarchy.isDelta_two_empty_iff_exists_converges`,
  `TauCeti.ArithmeticalHierarchy.isDelta_two_iff_exists_eventually`: `Δ⁰₂` Limit Lemma for
  predicates on primitive-codable types.

## References

* R. I. Soare, *Recursively Enumerable Sets and Degrees*, Springer, 1987, Limit Lemma III.3.3
  and Theorem IV.2.1.
-/

public section

open Filter TauCeti.Approximation

namespace TauCeti.ArithmeticalHierarchy

/-- **The relativized Limit Lemma, `Δ⁰₂` form for sets.** A set of natural numbers is `Δ⁰₂`
relative to `Z` if and only if its characteristic function is the pointwise limit of a sequence
of total functions computable uniformly in `Z`. -/
theorem isDelta_two_mem_iff_exists_converges {Z A : Set ℕ} :
    IsDelta Z 2 (· ∈ A) ↔
      ∃ f : ℕ → ℕ → ℕ, ComputableIn₂ {Z.oracle} f ∧ Converges f (A.indicator 1) :=
  isDelta_two_mem_iff_turingReducible_jump.trans turingReducible_jump_iff_exists_converges

/-- **The Limit Lemma, `Δ⁰₂` form for sets, unrelativized.** A set of natural numbers is `Δ⁰₂`
if and only if its characteristic function is the pointwise limit of a uniformly computable
sequence. -/
theorem isDelta_two_empty_mem_iff_exists_converges {A : Set ℕ} :
    IsDelta ∅ 2 (· ∈ A) ↔
      ∃ f : ℕ → ℕ → ℕ, Computable₂ f ∧ Converges f (A.indicator 1) :=
  isDelta_two_mem_iff_turingReducible_jump.trans turingReducible_jump_empty_iff_exists_converges

/-- **The relativized Limit Lemma, `Δ⁰₂` form.** A predicate on a primitive-codable type is
`Δ⁰₂` relative to `Z` if and only if it has a uniformly `Z`-computable Boolean approximation
converging pointwise to a total deciding function. -/
theorem isDelta_two_iff_exists_converges {Z : Set ℕ} {α : Type*} [Primcodable α] {p : α → Prop} :
    IsDelta Z 2 p ↔
      ∃ f : ℕ → α → Bool, ComputableIn₂ {Z.oracle} f ∧
        ∃ g : α → Bool, Converges f g ∧ ∀ x, g x = true ↔ p x := by
  rw [isDelta_two_iff_isSigma_zero_jump, isSigma_zero_iff]
  simp only [computableIn_jump_iff_exists_converges]
  exact ⟨fun ⟨g, ⟨f, hf, hfg⟩, hgeq⟩ => ⟨f, hf, g, hfg, hgeq⟩,
    fun ⟨f, hf, g, hfg, hgeq⟩ => ⟨g, ⟨f, hf, hfg⟩, hgeq⟩⟩

/-- **The Limit Lemma, `Δ⁰₂` form, unrelativized.** A predicate on a primitive-codable type is
`Δ⁰₂` if and only if it has a uniformly computable Boolean approximation converging pointwise to
a total deciding function. -/
theorem isDelta_two_empty_iff_exists_converges {α : Type*} [Primcodable α] {p : α → Prop} :
    IsDelta ∅ 2 p ↔
      ∃ f : ℕ → α → Bool, Computable₂ f ∧
        ∃ g : α → Bool, Converges f g ∧ ∀ x, g x = true ↔ p x := by
  simp [isDelta_two_iff_exists_converges]

/-- **The relativized Limit Lemma, `Δ⁰₂` eventual-equivalence form.** A predicate on a
primitive-codable type is `Δ⁰₂` relative to `Z` if and only if it is the eventually stable limit
of a uniformly `Z`-computable sequence of Boolean guesses. -/
theorem isDelta_two_iff_exists_eventually {Z : Set ℕ} {α : Type*} [Primcodable α] {p : α → Prop} :
    IsDelta Z 2 p ↔
      ∃ f : ℕ → α → Bool, ComputableIn₂ {Z.oracle} f ∧
        ∀ x, ∀ᶠ s in atTop, f s x = true ↔ p x := by
  classical
  rw [isDelta_two_iff_exists_converges]
  refine ⟨fun ⟨f, hf, g, hfg, hgeq⟩ => ⟨f, hf, fun x =>
      (converges_iff_eventually.1 hfg x).mono fun s hs => by simp [hs, hgeq x]⟩,
    fun ⟨f, hf, heq⟩ => ⟨f, hf, fun x => decide (p x),
      converges_iff_eventually.2 fun x => (heq x).mono fun s hs =>
        Bool.eq_iff_iff.2 (hs.trans decide_eq_true_iff.symm),
      fun _ => decide_eq_true_iff⟩⟩

end TauCeti.ArithmeticalHierarchy
