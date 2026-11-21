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
computable changes of parameters and downward closure under many-one and one-one reductions
available at every level.

All three pointclass families are monotone in the oracle under Turing reducibility, invariant
under Turing equivalence, and lift unrelativized membership from the empty oracle. At levels zero
and one, **relativized Post complementation** (`isDelta_one_iff_isSigma_zero`) identifies
`Δ⁰₁(Z)` with `Σ⁰₀(Z)`, characterizing sets Turing reducible to `Z` (and `ComputablePred` at the
empty oracle) without mentioning the Turing jump.

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

/-- Σ⁰ₙ is closed downward under computable many-one reducibility. -/
theorem IsSigma.of_manyOneReducible {q : β → Prop} (hq : IsSigma Z n q)
    (hpq : ManyOneReducible p q) : IsSigma Z n p := by
  obtain ⟨f, hf, heq⟩ := hpq
  exact (hq.preimage hf.computableIn).of_eq fun x => (heq x).symm

/-- Π⁰ₙ is closed downward under computable many-one reducibility. -/
theorem IsPi.of_manyOneReducible {q : β → Prop} (hq : IsPi Z n q)
    (hpq : ManyOneReducible p q) : IsPi Z n p := by
  obtain ⟨f, hf, heq⟩ := hpq
  exact (hq.preimage hf.computableIn).of_eq fun x => (heq x).symm

/-- Δ⁰ₙ is closed downward under computable many-one reducibility. -/
theorem IsDelta.of_manyOneReducible {q : β → Prop} (hq : IsDelta Z n q)
    (hpq : ManyOneReducible p q) : IsDelta Z n p :=
  ⟨hq.1.of_manyOneReducible hpq, hq.2.of_manyOneReducible hpq⟩

/-- Σ⁰ₙ is closed downward under computable one-one reducibility. -/
theorem IsSigma.of_oneOneReducible {q : β → Prop} (hq : IsSigma Z n q)
    (hpq : OneOneReducible p q) : IsSigma Z n p :=
  hq.of_manyOneReducible hpq.to_many_one

/-- Π⁰ₙ is closed downward under computable one-one reducibility. -/
theorem IsPi.of_oneOneReducible {q : β → Prop} (hq : IsPi Z n q)
    (hpq : OneOneReducible p q) : IsPi Z n p :=
  hq.of_manyOneReducible hpq.to_many_one

/-- Δ⁰ₙ is closed downward under computable one-one reducibility. -/
theorem IsDelta.of_oneOneReducible {q : β → Prop} (hq : IsDelta Z n q)
    (hpq : OneOneReducible p q) : IsDelta Z n p :=
  hq.of_manyOneReducible hpq.to_many_one

/-- Many-one equivalent predicates belong to the same existential pointclasses. -/
theorem isSigma_congr_manyOneEquiv {q : β → Prop} (hpq : ManyOneEquiv p q) :
    IsSigma Z n p ↔ IsSigma Z n q :=
  ⟨fun h => h.of_manyOneReducible hpq.2, fun h => h.of_manyOneReducible hpq.1⟩

/-- Many-one equivalent predicates belong to the same universal pointclasses. -/
theorem isPi_congr_manyOneEquiv {q : β → Prop} (hpq : ManyOneEquiv p q) :
    IsPi Z n p ↔ IsPi Z n q :=
  ⟨fun h => h.of_manyOneReducible hpq.2, fun h => h.of_manyOneReducible hpq.1⟩

/-- Many-one equivalent predicates belong to the same intersection pointclasses. -/
theorem isDelta_congr_manyOneEquiv {q : β → Prop} (hpq : ManyOneEquiv p q) :
    IsDelta Z n p ↔ IsDelta Z n q :=
  ⟨fun h => h.of_manyOneReducible hpq.2, fun h => h.of_manyOneReducible hpq.1⟩

/-! ### Oracle monotonicity and degree invariance -/

/-- Existential pointclasses are monotone in the oracle under Turing reducibility. -/
theorem IsSigma.mono_oracle {A B : Set ℕ} (h : IsSigma A n p)
    (hAB : TuringReducible A.oracle B.oracle) : IsSigma B n p := by
  induction n generalizing α with
  | zero =>
    obtain ⟨b, hb, heq⟩ := isSigma_zero_iff.1 h
    exact isSigma_zero_iff.2 ⟨b, hb.subst (by simpa using hAB), heq⟩
  | succ n ih =>
    obtain ⟨q, hq, heq⟩ := isSigma_succ_iff.1 h
    exact isSigma_succ_iff.2 ⟨q, isSigma_not_iff.1 (ih (isSigma_not_iff.2 hq)), heq⟩

/-- Universal pointclasses are monotone in the oracle under Turing reducibility. -/
theorem IsPi.mono_oracle {A B : Set ℕ} (h : IsPi A n p)
    (hAB : TuringReducible A.oracle B.oracle) : IsPi B n p :=
  isSigma_not_iff.1 ((isSigma_not_iff.2 h).mono_oracle hAB)

/-- Intersection pointclasses are monotone in the oracle under Turing reducibility. -/
theorem IsDelta.mono_oracle {A B : Set ℕ} (h : IsDelta A n p)
    (hAB : TuringReducible A.oracle B.oracle) : IsDelta B n p := by
  obtain ⟨hS, hP⟩ := isDelta_iff.1 h
  exact isDelta_iff.2 ⟨hS.mono_oracle hAB, hP.mono_oracle hAB⟩

/-- Turing equivalent oracles define the same existential pointclasses. -/
theorem isSigma_congr_oracle {A B : Set ℕ} (hAB : TuringEquivalent A.oracle B.oracle) :
    IsSigma A n p ↔ IsSigma B n p :=
  ⟨fun h => h.mono_oracle hAB.1, fun h => h.mono_oracle hAB.2⟩

/-- Turing equivalent oracles define the same universal pointclasses. -/
theorem isPi_congr_oracle {A B : Set ℕ} (hAB : TuringEquivalent A.oracle B.oracle) :
    IsPi A n p ↔ IsPi B n p :=
  ⟨fun h => h.mono_oracle hAB.1, fun h => h.mono_oracle hAB.2⟩

/-- Turing equivalent oracles define the same intersection pointclasses. -/
theorem isDelta_congr_oracle {A B : Set ℕ} (hAB : TuringEquivalent A.oracle B.oracle) :
    IsDelta A n p ↔ IsDelta B n p :=
  ⟨fun h => h.mono_oracle hAB.1, fun h => h.mono_oracle hAB.2⟩

/-- Every unrelativized existential predicate belongs to the same level relative to any oracle. -/
theorem IsSigma.of_empty (h : IsSigma ∅ n p) : IsSigma Z n p :=
  h.mono_oracle (Set.empty_turingReducible Z.oracle)

/-- Every unrelativized universal predicate belongs to the same level relative to any oracle. -/
theorem IsPi.of_empty (h : IsPi ∅ n p) : IsPi Z n p :=
  h.mono_oracle (Set.empty_turingReducible Z.oracle)

/-- Every unrelativized intersection predicate belongs to the same level relative to any oracle. -/
theorem IsDelta.of_empty (h : IsDelta ∅ n p) : IsDelta Z n p :=
  h.mono_oracle (Set.empty_turingReducible Z.oracle)

/-! ### Level zero and relativized Post complementation -/

/-- Membership in a set of natural numbers is `Σ⁰₀(Z)` exactly when the set is Turing reducible
to `Z`. -/
theorem isSigma_zero_mem_iff_turingReducible {C : Set ℕ} :
    IsSigma Z 0 (· ∈ C) ↔ TuringReducible C.oracle Z.oracle := by
  rw [C.turingReducible_iff_computableIn_indicator, isSigma_zero_iff]
  constructor
  · rintro ⟨b, hb, heq⟩
    have h01 : Primrec fun g : Bool => cond g (1 : ℕ) 0 :=
      Primrec.cond Primrec.id (Primrec.const 1) (Primrec.const 0)
    refine RecursiveIn.of_eq (h01.computableIn.comp hb) fun x => congrArg Part.some ?_
    by_cases hx : x ∈ C
    · simp [hx, (heq x).2 hx]
    · cases hb_val : b x
      · simp [hx, hb_val]
      · exact False.elim (hx ((heq x).1 hb_val))
  · intro hχ
    refine ⟨fun x => C.indicator 1 x == 1,
      (Primrec.beq.comp Primrec.id (Primrec.const 1)).computableIn.comp hχ, fun x => ?_⟩
    by_cases hx : x ∈ C <;> simp [hx]

/-- At the empty oracle, `Σ⁰₀` agrees with Mathlib's `ComputablePred`. -/
theorem isSigma_zero_empty_iff_computablePred : IsSigma ∅ 0 p ↔ ComputablePred p := by
  rw [isSigma_zero_iff]
  constructor
  · rintro ⟨b, hb, heq⟩
    exact (by simpa using hb : Computable b).computablePred.of_eq heq
  · rintro ⟨_, hp⟩
    exact ⟨fun x => decide (p x), hp.computableIn, fun _ => decide_eq_true_iff⟩

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

/-- **Relativized Post complementation.** A predicate is `Δ⁰₁` relative to `Z` if and only if it
is `Σ⁰₀` relative to `Z`. -/
theorem isDelta_one_iff_isSigma_zero : IsDelta Z 1 p ↔ IsSigma Z 0 p := by
  refine ⟨fun h => ?_, fun h => ⟨h.one_of_zero, (isPi_zero_iff.2 h).one_of_zero⟩⟩
  obtain ⟨hp, hnp⟩ := isDelta_iff.1 h
  obtain ⟨b₁, hb₁, heq₁⟩ := isSigma_one_iff.1 hp
  obtain ⟨b₂, hb₂, heq₂⟩ := isSigma_one_iff.1 (isSigma_not_iff.2 hnp)
  let c : α → ℕ → Bool := fun x y => b₁ (x, y) || b₂ (x, y)
  have hc : ComputableIn₂ {Z.oracle} c := Primrec.or.computableIn.comp (hb₁.pair hb₂)
  have hex : ∀ x, ∃ y, c x y = true := fun x => by
    by_cases hx : p x
    · obtain ⟨y, hy⟩ := (heq₁ x).1 hx
      exact ⟨y, by simp [c, hy]⟩
    · obtain ⟨y, hy⟩ := (heq₂ x).1 hx
      exact ⟨y, by simp [c, hy]⟩
  have hfind : ComputableIn {Z.oracle} (fun x => Nat.find (hex x)) :=
    ComputableIn.find (by simpa using hc) hex
  refine isSigma_zero_iff.2 ⟨fun x => b₁ (x, Nat.find (hex x)),
    hb₁.comp (ComputableIn.id.pair hfind), fun x => ?_⟩
  constructor
  · intro hb
    exact (heq₁ x).2 ⟨Nat.find (hex x), hb⟩
  · intro hx
    have hspec : b₁ (x, Nat.find (hex x)) = true ∨ b₂ (x, Nat.find (hex x)) = true := by
      simpa [c] using Nat.find_spec (hex x)
    rcases hspec with h₁ | h₂
    · exact h₁
    · exact False.elim (((heq₂ x).2 ⟨Nat.find (hex x), h₂⟩) hx)

/-- Membership in a set of natural numbers is `Δ⁰₁(Z)` exactly when the set is Turing reducible
to `Z`. -/
theorem isDelta_one_mem_iff_turingReducible {C : Set ℕ} :
    IsDelta Z 1 (· ∈ C) ↔ TuringReducible C.oracle Z.oracle :=
  isDelta_one_iff_isSigma_zero.trans isSigma_zero_mem_iff_turingReducible

/-- At the empty oracle, `Δ⁰₁` agrees with Mathlib's `ComputablePred`. -/
theorem isDelta_one_empty_iff_computablePred : IsDelta ∅ 1 p ↔ ComputablePred p :=
  isDelta_one_iff_isSigma_zero.trans isSigma_zero_empty_iff_computablePred

end TauCeti.ArithmeticalHierarchy
