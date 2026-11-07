/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Computability.RecursiveIn
public import TauCeti.Computability.TuringDegree

/-!
# Quantifier-defined arithmetical pointclasses

`IsSigma Z n p` means that `p` belongs to the arithmetical pointclass Σ⁰ₙ relative to `Z`.
At level zero, a total Boolean procedure relative to `Z` decides the predicate. Each successor
adds an existential number quantifier in front of the complement of a predicate at the preceding
level. `IsPi` is the complementary class, and `IsDelta` is the intersection of the two classes.
These definitions do not use the Turing jump.

Parameters may range over any primitive-codable type. Adding a number variable replaces the
parameter type `α` by `α × ℕ`; successive quantifiers therefore extend it to `(α × ℕ) × ℕ`,
and so on. Mathlib's product encoding uses `Nat.pair`. This convention also makes
computable changes of parameters available at every level.

## References

* R. I. Soare, *Recursively Enumerable Sets and Degrees*, Springer, 1987, Chapter IV.1.
-/

public section

namespace TauCeti.ArithmeticalHierarchy

/-- Membership in Σ⁰ₙ relative to `Z`, defined by number quantifiers over total
oracle-computable Boolean matrices. -/
def IsSigma (Z : Set ℕ) : (n : ℕ) → {α : Type u} → [Primcodable α] → (α → Prop) → Prop
  | 0, α, _, p => ∃ b : α → Bool, ComputableIn {Z.oracle} b ∧ ∀ x, b x = true ↔ p x
  | n + 1, α, _, p => ∃ q : α × ℕ → Prop,
      IsSigma Z n (fun a => ¬q a) ∧ ∀ x, p x ↔ ∃ y, q (x, y)

/-- Membership in Π⁰ₙ relative to `Z`: the complement is in Σ⁰ₙ. -/
def IsPi (Z : Set ℕ) (n : ℕ) {α : Type*} [Primcodable α] (p : α → Prop) : Prop :=
  IsSigma Z n (fun x => ¬p x)

/-- Membership in Δ⁰ₙ relative to `Z`: both Σ⁰ₙ and Π⁰ₙ membership. -/
def IsDelta (Z : Set ℕ) (n : ℕ) {α : Type*} [Primcodable α] (p : α → Prop) : Prop :=
  IsSigma Z n p ∧ IsPi Z n p

variable {Z : Set ℕ} {n : ℕ} {α β : Type*} [Primcodable α] [Primcodable β]
  {p q : α → Prop}

/-- Δ⁰ₙ membership means simultaneous Σ⁰ₙ and Π⁰ₙ membership. -/
theorem isDelta_iff : IsDelta Z n p ↔ IsSigma Z n p ∧ IsPi Z n p := Iff.rfl

/-- The quantifier-free class consists exactly of predicates with a total Boolean decision
procedure relative to the oracle. -/
theorem isSigma_zero_iff : IsSigma Z 0 p ↔
    ∃ b : α → Bool, ComputableIn {Z.oracle} b ∧ ∀ x, b x = true ↔ p x := Iff.rfl

/-- Pointclass membership depends only on the extension of the predicate. -/
theorem IsSigma.of_eq (h : IsSigma Z n p) (hpq : ∀ x, p x ↔ q x) : IsSigma Z n q := by
  have : p = q := funext fun x => propext (hpq x)
  exact this ▸ h

/-- Π⁰ₙ membership depends only on the extension of the predicate. -/
theorem IsPi.of_eq (h : IsPi Z n p) (hpq : ∀ x, p x ↔ q x) : IsPi Z n q :=
  IsSigma.of_eq h fun x => (hpq x).not

/-- Δ⁰ₙ membership depends only on the extension of the predicate. -/
theorem IsDelta.of_eq (h : IsDelta Z n p) (hpq : ∀ x, p x ↔ q x) : IsDelta Z n q :=
  ⟨h.1.of_eq hpq, h.2.of_eq hpq⟩

/-- Complementation exchanges Π⁰ₙ and Σ⁰ₙ. -/
@[simp]
theorem isPi_not_iff : IsPi Z n (fun x => ¬p x) ↔ IsSigma Z n p := by
  simp [IsPi]

/-- Complementation exchanges Σ⁰ₙ and Π⁰ₙ. -/
@[simp]
theorem isSigma_not_iff : IsSigma Z n (fun x => ¬p x) ↔ IsPi Z n p := Iff.rfl

/-- Complementation preserves Δ⁰ₙ. -/
@[simp]
theorem isDelta_not_iff : IsDelta Z n (fun x => ¬p x) ↔ IsDelta Z n p := by
  simp [IsDelta, and_comm]

/-- A Σ⁰ₙ₊₁ predicate is an existential number projection of a Π⁰ₙ predicate. -/
theorem isSigma_succ_iff : IsSigma Z (n + 1) p ↔
    ∃ q : α × ℕ → Prop, IsPi Z n q ∧ ∀ x, p x ↔ ∃ y, q (x, y) := Iff.rfl

/-- A Π⁰ₙ₊₁ predicate is a universal number projection of a Σ⁰ₙ predicate. -/
theorem isPi_succ_iff : IsPi Z (n + 1) p ↔
    ∃ q : α × ℕ → Prop, IsSigma Z n q ∧ ∀ x, p x ↔ ∀ y, q (x, y) := by
  classical
  constructor
  · rintro ⟨q, hq, heq⟩
    exact ⟨fun a => ¬q a, hq, fun x => by simpa using (heq x).not⟩
  · rintro ⟨q, hq, heq⟩
    exact ⟨fun a => ¬q a, hq.of_eq (by simp), fun x => by simp [heq x]⟩

/-- At level zero complementation preserves computability. -/
@[simp]
theorem isPi_zero_iff : IsPi Z 0 p ↔ IsSigma Z 0 p := by
  classical
  have hnot {q : α → Prop} (h : IsSigma Z 0 q) : IsSigma Z 0 (fun x => ¬q x) := by
    obtain ⟨b, hb, heq⟩ := h
    refine ⟨fun x => !b x, Primrec.not.computableIn.comp hb, fun x => ?_⟩
    simp [← heq x]
  exact ⟨fun h => (hnot h).of_eq (by simp), hnot⟩

/-- The zero-level intersection is just the computable class. -/
@[simp]
theorem isDelta_zero_iff : IsDelta Z 0 p ↔ IsSigma Z 0 p := by
  simp [IsDelta]

/-- Σ⁰ₙ is closed under oracle-computable changes of the free parameters. -/
theorem IsSigma.preimage (h : IsSigma Z n p) {f : β → α}
    (hf : ComputableIn {Z.oracle} f) : IsSigma Z n (fun x => p (f x)) := by
  induction n generalizing α β with
  | zero =>
    obtain ⟨b, hb, heq⟩ := h
    exact ⟨fun x => b (f x), hb.comp hf, fun x => heq (f x)⟩
  | succ n ih =>
    obtain ⟨q, hq, heq⟩ := h
    refine ⟨fun a => q (f a.1, a.2), ih hq
      ((hf.comp ComputableIn.fst).pair ComputableIn.snd), fun x => heq (f x)⟩

/-- Π⁰ₙ is closed under oracle-computable changes of the free parameters. -/
theorem IsPi.preimage (h : IsPi Z n p) {f : β → α}
    (hf : ComputableIn {Z.oracle} f) : IsPi Z n (fun x => p (f x)) :=
  IsSigma.preimage h hf

/-- Δ⁰ₙ is closed under oracle-computable changes of the free parameters. -/
theorem IsDelta.preimage (h : IsDelta Z n p) {f : β → α}
    (hf : ComputableIn {Z.oracle} f) : IsDelta Z n (fun x => p (f x)) :=
  ⟨h.1.preimage hf, h.2.preimage hf⟩

/-- At level one there is a single existential number quantifier over a total
oracle-computable Boolean matrix. -/
theorem isSigma_one_iff : IsSigma Z 1 p ↔
    ∃ b : α × ℕ → Bool, ComputableIn {Z.oracle} b ∧
      ∀ x, p x ↔ ∃ y, b (x, y) = true := by
  rw [isSigma_succ_iff]
  constructor
  · rintro ⟨q, hq, heq⟩
    obtain ⟨b, hb, hdec⟩ := isPi_zero_iff.1 hq
    exact ⟨b, hb, fun x => (heq x).trans (exists_congr fun y => (hdec (x, y)).symm)⟩
  · rintro ⟨b, hb, heq⟩
    exact ⟨fun a => b a = true, isPi_zero_iff.2 ⟨b, hb, fun _ => Iff.rfl⟩, heq⟩

/-- Quantifier-free predicates are Σ⁰₁, by adding an unused number variable. -/
theorem IsSigma.one_of_zero (h : IsSigma Z 0 p) : IsSigma Z 1 p := by
  obtain ⟨b, hb, heq⟩ := h
  exact isSigma_one_iff.2 ⟨fun a => b a.1, hb.comp ComputableIn.fst, fun x => by
    simpa using (heq x).symm⟩

end TauCeti.ArithmeticalHierarchy
