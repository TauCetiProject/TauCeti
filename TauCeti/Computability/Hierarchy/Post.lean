/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Computability.Hierarchy.One
public import TauCeti.Computability.Hierarchy.Closure
public import TauCeti.Computability.Approximation.Modulus
import TauCeti.Computability.Approximation.Jump

/-!
# Relativized Post's theorem and strictness of the arithmetical hierarchy

Post's theorem identifies the quantifier-defined arithmetical pointclasses relative to an oracle
`Z ⊆ ℕ` with computability and computable enumerability relative to finite iterates of the Turing
jump `Z⁽ⁿ⁾ = Set.jump^[n] Z`:

* `IsSigma Z (n + 1) p` holds iff `p` is c.e. in `Z⁽ⁿ⁾` (equivalently, `IsSigma Z⁽ⁿ⁾ 1 p`);
* `IsDelta Z (n + 1) p` holds iff `p` is computable in `Z⁽ⁿ⁾` (equivalently, `IsSigma Z⁽ⁿ⁾ 0 p`,
  and for sets of naturals `A`, iff `A ≤_T Z⁽ⁿ⁾`).

The core step is the single-jump shift `IsSigma Z.jump (n + 1) p ↔ IsSigma Z (n + 2) p`. In one
direction, every `Σ⁰₁(Z)` predicate reduces one-one to `Z'`, hence becomes `Σ⁰₀(Z')`, and
induction over quantifiers lowers the level by one. In the other direction, the relativized Limit
Lemma approximates every `Σ⁰₀(Z')` predicate by a uniformly `Z`-computable sequence of Boolean
guesses, placing it in `Δ⁰₂(Z)` and hence placing every `Σ⁰₁(Z')` predicate in `Σ⁰₂(Z)` by
existential quantifier contraction. Together with the fact that `Δ⁰₁(Z) = Σ⁰₀(Z)` (via
unbounded search for a witness to either `p` or `¬p`), iterating the single-jump shift yields
Post's theorem for every `n`.

From Post's theorem we deduce:

* **Completeness of iterated jumps:** `Z⁽ⁿ⁺¹⁾` is `Σ⁰_{n+1}(Z)`-complete and `(Z⁽ⁿ⁺¹⁾)ᶜ` is
  `Π⁰_{n+1}(Z)`-complete under ordinary computable one-one and many-one reductions;
* **Strictness of the arithmetical hierarchy:** `Z⁽ⁿ⁺¹⁾ ∈ Σ⁰_{n+1}(Z) \ Π⁰_{n+1}(Z)`,
  `(Z⁽ⁿ⁺¹⁾)ᶜ ∈ Π⁰_{n+1}(Z) \ Σ⁰_{n+1}(Z)`, and the parity join
  `Z⁽ⁿ⁺¹⁾ ⊕ (Z⁽ⁿ⁺¹⁾)ᶜ` lies in `Δ⁰_{n+2}(Z) \ (Σ⁰_{n+1}(Z) ∪ Π⁰_{n+1}(Z))`;
* **The `Δ⁰₂` Limit Lemma:** a predicate is `Δ⁰₂(Z)` iff it is the eventually stable limit of a
  uniformly `Z`-computable Boolean approximation, and for sets of naturals iff its characteristic
  function is the limit of a uniformly `Z`-computable approximation in the sense of
  `TauCeti.Approximation.Converges`.

## Main results

* `TauCeti.ArithmeticalHierarchy.isDelta_one_iff_isSigma_zero`: `Δ⁰₁(Z) = Σ⁰₀(Z)`.
* `TauCeti.ArithmeticalHierarchy.isSigma_succ_jump_iff`,
  `TauCeti.ArithmeticalHierarchy.isPi_succ_jump_iff`,
  `TauCeti.ArithmeticalHierarchy.isDelta_succ_jump_iff`,
  `TauCeti.ArithmeticalHierarchy.isSigma_zero_jump_iff_isDelta_two`: the single-jump shift.
* `TauCeti.ArithmeticalHierarchy.isSigma_succ_iff_isSigma_one_iterate_jump`,
  `TauCeti.ArithmeticalHierarchy.isSigma_succ_iff_exists_recursiveIn_domain`,
  `TauCeti.ArithmeticalHierarchy.isSigma_succ_iff_exists_code`,
  `TauCeti.ArithmeticalHierarchy.isDelta_succ_iff_isSigma_zero_iterate_jump`,
  `TauCeti.ArithmeticalHierarchy.isDelta_succ_iff_exists_computableIn`,
  `TauCeti.ArithmeticalHierarchy.isDelta_succ_mem_iff_turingReducible_iterate_jump`:
  relativized Post's theorem.
* `TauCeti.ArithmeticalHierarchy.isSigma_succ_iff_oneOneReducible_iterate_jump`,
  `TauCeti.ArithmeticalHierarchy.isSigma_succ_iff_manyOneReducible_iterate_jump`,
  `TauCeti.ArithmeticalHierarchy.isPi_succ_iff_oneOneReducible_compl_iterate_jump`,
  `TauCeti.ArithmeticalHierarchy.isPi_succ_iff_manyOneReducible_compl_iterate_jump`:
  completeness of `Z⁽ⁿ⁺¹⁾` and `(Z⁽ⁿ⁺¹⁾)ᶜ`.
* `TauCeti.ArithmeticalHierarchy.not_isPi_succ_iterate_jump`,
  `TauCeti.ArithmeticalHierarchy.not_isSigma_succ_compl_iterate_jump`,
  `TauCeti.ArithmeticalHierarchy.isSigma_iterate_jump_iff`,
  `TauCeti.ArithmeticalHierarchy.isPi_iterate_jump_iff`,
  `TauCeti.ArithmeticalHierarchy.isDelta_iterate_jump_iff`,
  `TauCeti.ArithmeticalHierarchy.isDelta_add_two_turingJoin_compl_iterate_jump`,
  `TauCeti.ArithmeticalHierarchy.not_isSigma_succ_turingJoin_compl_iterate_jump`,
  `TauCeti.ArithmeticalHierarchy.not_isPi_succ_turingJoin_compl_iterate_jump`:
  strictness of the arithmetical hierarchy.
* `TauCeti.ArithmeticalHierarchy.isDelta_two_iff_exists_eventually`,
  `TauCeti.ArithmeticalHierarchy.isDelta_two_empty_iff_exists_eventually`,
  `TauCeti.ArithmeticalHierarchy.isDelta_two_mem_iff_exists_converges`,
  `TauCeti.ArithmeticalHierarchy.isDelta_two_empty_mem_iff_exists_converges`:
  the `Δ⁰₂` Limit Lemma.

## References

* R. I. Soare, *Recursively Enumerable Sets and Degrees*, Springer, 1987, Chapters III.3, IV.1,
  and IV.2 (Post's Theorem IV.2.2 and the Hierarchy Theorem IV.2.3).
-/

public section

open Encodable Filter TauCeti.Oracle.Single

namespace TauCeti.ArithmeticalHierarchy

variable {Z W : Set ℕ} {n m k : ℕ} {α : Type*} [Primcodable α] {p : α → Prop}

/-! ### Level zero, oracle monotonicity, and Δ⁰₁ -/

/-- Existential pointclasses are monotone in the oracle under Turing reducibility. -/
theorem IsSigma.of_turingReducible (h : IsSigma Z n p)
    (hZW : TuringReducible Z.oracle W.oracle) : IsSigma W n p := by
  induction n generalizing α with
  | zero =>
    obtain ⟨b, hb, heq⟩ := isSigma_zero_iff.1 h
    exact isSigma_zero_iff.2
      ⟨b, hb.recursiveIn.subst fun g hg => (Set.mem_singleton_iff.1 hg) ▸ hZW, heq⟩
  | succ n ih =>
    obtain ⟨q, hq, heq⟩ := isSigma_succ_iff.1 h
    exact isSigma_succ_iff.2 ⟨q, isSigma_not_iff.1 (ih (isSigma_not_iff.2 hq)), heq⟩

/-- Universal pointclasses are monotone in the oracle under Turing reducibility. -/
theorem IsPi.of_turingReducible (h : IsPi Z n p)
    (hZW : TuringReducible Z.oracle W.oracle) : IsPi W n p :=
  isSigma_not_iff.1 ((isSigma_not_iff.2 h).of_turingReducible hZW)

/-- Intersection pointclasses are monotone in the oracle under Turing reducibility. -/
theorem IsDelta.of_turingReducible (h : IsDelta Z n p)
    (hZW : TuringReducible Z.oracle W.oracle) : IsDelta W n p := by
  obtain ⟨hS, hP⟩ := isDelta_iff.1 h
  exact isDelta_iff.2 ⟨hS.of_turingReducible hZW, hP.of_turingReducible hZW⟩

/-- Turing equivalent oracles define the same existential pointclasses. -/
theorem isSigma_congr_turingEquivalent (hZW : TuringEquivalent Z.oracle W.oracle) :
    IsSigma Z n p ↔ IsSigma W n p :=
  ⟨fun h => h.of_turingReducible hZW.1, fun h => h.of_turingReducible hZW.2⟩

/-- Turing equivalent oracles define the same universal pointclasses. -/
theorem isPi_congr_turingEquivalent (hZW : TuringEquivalent Z.oracle W.oracle) :
    IsPi Z n p ↔ IsPi W n p := by
  rw [← isSigma_not_iff, ← isSigma_not_iff]
  exact isSigma_congr_turingEquivalent hZW

/-- Turing equivalent oracles define the same intersection pointclasses. -/
theorem isDelta_congr_turingEquivalent (hZW : TuringEquivalent Z.oracle W.oracle) :
    IsDelta Z n p ↔ IsDelta W n p := by
  simp only [isDelta_iff]
  exact and_congr (isSigma_congr_turingEquivalent hZW) (isPi_congr_turingEquivalent hZW)

private theorem computableIn_empty_iff {β : Type*} [Primcodable β] {f : α → β} :
    ComputableIn {(∅ : Set ℕ).oracle} f ↔ Computable f :=
  ⟨fun hf => by rw [Set.oracle_empty] at hf; exact hf.recursiveIn.partrec_of_const,
    fun hf => hf.computableIn⟩

/-- At the empty oracle, the quantifier-free class Σ⁰₀ agrees with Mathlib's `ComputablePred`. -/
theorem isSigma_zero_empty_iff_computablePred : IsSigma ∅ 0 p ↔ ComputablePred p := by
  rw [isSigma_zero_iff, ComputablePred.computable_iff]
  constructor
  · rintro ⟨b, hb, heq⟩
    exact ⟨b, computableIn_empty_iff.1 hb, funext fun x => propext (heq x).symm⟩
  · rintro ⟨b, hb, rfl⟩
    exact ⟨b, hb.computableIn, fun _ => Iff.rfl⟩

/-- A set of naturals belongs to Σ⁰₀ relative to `Z` exactly when it is Turing reducible to `Z`. -/
theorem isSigma_zero_mem_iff_turingReducible {A : Set ℕ} :
    IsSigma Z 0 (· ∈ A) ↔ TuringReducible A.oracle Z.oracle := by
  classical
  rw [A.turingReducible_iff_computableIn_indicator, isSigma_zero_iff]
  constructor
  · rintro ⟨b, hb, heq⟩
    have hcond : ComputableIn {Z.oracle} (fun x => cond (b x) 1 0) :=
      (Primrec.cond Primrec.id (Primrec.const 1) (Primrec.const 0)).computableIn.comp hb
    refine RecursiveIn.of_eq hcond fun x => congrArg Part.some ?_
    by_cases hx : x ∈ A
    · simp [(heq x).2 hx, hx]
    · have hbf : b x = false := Bool.eq_false_iff.2 fun h => hx ((heq x).1 h)
      simp [hbf, hx]
  · intro hA
    refine ⟨fun x => A.indicator 1 x == 1,
      (Primrec.beq.comp Primrec.id (Primrec.const 1)).computableIn.comp hA, fun x => ?_⟩
    by_cases hx : x ∈ A <;> simp [hx]

/-- **Post's theorem at level one for Δ⁰₁:** a predicate is both Σ⁰₁ and Π⁰₁ relative to `Z`
exactly when it is decidable relative to `Z`. -/
@[simp]
theorem isDelta_one_iff_isSigma_zero : IsDelta Z 1 p ↔ IsSigma Z 0 p := by
  classical
  refine ⟨fun h => ?_, IsSigma.delta_succ⟩
  obtain ⟨hS, hP⟩ := isDelta_iff.1 h
  obtain ⟨b₁, hb₁, h₁⟩ := isSigma_one_iff.1 hS
  obtain ⟨b₂, hb₂, h₂⟩ := isSigma_one_iff.1 (isSigma_not_iff.2 hP)
  -- Search simultaneously for a positive witness in `b₁` or a negative witness in `b₂`.
  have hb : ComputableIn₂ {Z.oracle} (fun x y => b₁ (x, y) || b₂ (x, y)) :=
    Primrec.or.computableIn.comp (hb₁.pair hb₂)
  have hex : ∀ x, ∃ y, (b₁ (x, y) || b₂ (x, y)) = true := by
    intro x
    by_cases hx : p x
    · obtain ⟨y, hy⟩ := (h₁ x).1 hx
      exact ⟨y, by simp [hy]⟩
    · obtain ⟨y, hy⟩ := (h₂ x).1 hx
      exact ⟨y, by simp [hy]⟩
  have hw : ComputableIn {Z.oracle} (fun x => Nat.find (hex x)) := hb.find hex
  refine isSigma_zero_iff.2 ⟨fun x => b₁ (x, Nat.find (hex x)),
    hb₁.comp (ComputableIn.id.pair hw), fun x => ⟨fun hx => (h₁ x).2 ⟨_, hx⟩, fun hx => ?_⟩⟩
  rcases Bool.or_eq_true_iff.1 (Nat.find_spec (hex x)) with h1 | h2
  · exact h1
  · exact absurd hx ((h₂ x).2 ⟨_, h2⟩)

/-! ### The single-jump shift -/

private theorem isSigma_zero_jump_of_isSigma_one (h : IsSigma Z 1 p) :
    IsSigma Z.jump 0 p := by
  obtain ⟨f, hf, -, heq⟩ := h.oneOneReducible_jump
  have hmem : IsSigma Z.jump 0 (· ∈ Z.jump) :=
    isSigma_zero_mem_iff_turingReducible.2 (.refl _)
  exact (hmem.preimage hf.computableIn).of_eq fun x => (heq x).symm

private theorem isSigma_jump_of_isSigma_succ (h : IsSigma Z (n + 1) p) :
    IsSigma Z.jump n p := by
  induction n generalizing α with
  | zero => exact isSigma_zero_jump_of_isSigma_one h
  | succ n ih =>
    obtain ⟨q, hq, heq⟩ := isSigma_succ_iff.1 h
    exact isSigma_succ_iff.2 ⟨q, isSigma_not_iff.1 (ih (isSigma_not_iff.2 hq)), heq⟩

private theorem exists_computableIn₂_eventually_of_isSigma_zero_jump (h : IsSigma Z.jump 0 p) :
    ∃ f : ℕ → α → Bool, ComputableIn₂ {Z.oracle} f ∧
      ∀ x, ∀ᶠ s in atTop, f s x = true ↔ p x := by
  obtain ⟨b, hb, heq⟩ := isSigma_zero_iff.1 h
  -- Extend `b` to a total function on `ℕ` returning `0` on codes outside the image of `encode`,
  -- so the construction also works when `α` is empty.
  let g : ℕ → ℕ := fun n => ((decode (α := α) n).map fun x => encode (b x)).getD 0
  have hguard : ComputableIn {Z.jump.oracle} (fun n : ℕ => (decode (α := α) n).isSome) :=
    (Primrec.option_isSome.comp Primrec.decode).computableIn
  have hg : ComputableIn {Z.jump.oracle} g := by
    unfold ComputableIn RecursiveIn at hb
    refine RecursiveIn.iff_nat.2 <|
      (Nat.RecursiveIn.cond hguard hb (Nat.Primrec.zero.recursiveIn)).of_eq fun n => ?_
    cases e : decode (α := α) n <;> simp [g, e]
  obtain ⟨f₀, hf₀, hconv⟩ := Approximation.exists_computableIn_converges_of_computableIn_jump hg
  refine ⟨fun s x => f₀ s (encode x) == encode true, ?_, fun x => ?_⟩
  · exact Primrec.beq.computableIn.comp <|
      (hf₀.comp (ComputableIn.fst.pair
        (Primrec.encode.computableIn.comp ComputableIn.snd))).pair
        (ComputableIn.const (encode true))
  · refine (Approximation.converges_iff_eventually.1 hconv (encode x)).mono fun s hs => ?_
    simp only [hs, g, encodek, Option.map_some, Option.getD_some, beq_iff_eq, encode_inj]
    exact heq x

private theorem isSigma_two_of_eventually {f : ℕ → α → Bool} (hf : ComputableIn₂ {Z.oracle} f)
    (heq : ∀ x, ∀ᶠ s in atTop, f s x = true ↔ p x) : IsSigma Z 2 p := by
  have hmat : IsSigma Z 0 (fun b : (α × ℕ) × ℕ => f (b.1.2 + b.2) b.1.1 = true) := by
    refine isSigma_zero_iff.2 ⟨fun b => f (b.1.2 + b.2) b.1.1, ?_, fun _ => Iff.rfl⟩
    exact hf.comp <| (Primrec.nat_add.computableIn.comp
      ((ComputableIn.snd.comp ComputableIn.fst).pair ComputableIn.snd)).pair
      (ComputableIn.fst.comp ComputableIn.fst)
  have hpi : IsPi Z 1 (fun a : α × ℕ => ∀ t, f (a.2 + t) a.1 = true) :=
    isPi_succ_iff.2 ⟨_, hmat, fun _ => Iff.rfl⟩
  refine isSigma_succ_iff.2 ⟨_, hpi, fun x => ?_⟩
  obtain ⟨s₁, hs₁⟩ := eventually_atTop.1 (heq x)
  constructor
  · intro hx
    exact ⟨s₁, fun t => (hs₁ (s₁ + t) (Nat.le_add_right s₁ t)).2 hx⟩
  · rintro ⟨s₀, ht⟩
    exact (hs₁ (s₀ + s₁) (Nat.le_add_left s₁ s₀)).1 (ht s₁)

private theorem isDelta_two_of_eventually {f : ℕ → α → Bool} (hf : ComputableIn₂ {Z.oracle} f)
    (heq : ∀ x, ∀ᶠ s in atTop, f s x = true ↔ p x) : IsDelta Z 2 p := by
  have hnot : ComputableIn₂ {Z.oracle} (fun s x => !f s x) :=
    Primrec.not.computableIn.comp hf
  refine isDelta_iff.2 ⟨isSigma_two_of_eventually hf heq,
    isSigma_not_iff.1 <| isSigma_two_of_eventually hnot fun x =>
      (heq x).mono fun s hs => by simpa using hs.not⟩

private theorem isSigma_two_of_isSigma_one_jump (h : IsSigma Z.jump 1 p) : IsSigma Z 2 p := by
  obtain ⟨q, hq, heq⟩ := isSigma_succ_iff.1 h
  obtain ⟨f, hf, hfeq⟩ := exists_computableIn₂_eventually_of_isSigma_zero_jump (isPi_zero_iff.1 hq)
  exact (isSigma_two_of_eventually hf hfeq).exists_nat.of_eq fun x => (heq x).symm

private theorem isSigma_succ_succ_of_isSigma_succ_jump (h : IsSigma Z.jump (n + 1) p) :
    IsSigma Z (n + 2) p := by
  induction n generalizing α with
  | zero => exact isSigma_two_of_isSigma_one_jump h
  | succ n ih =>
    obtain ⟨q, hq, heq⟩ := isSigma_succ_iff.1 h
    exact isSigma_succ_iff.2 ⟨q, isSigma_not_iff.1 (ih (isSigma_not_iff.2 hq)), heq⟩

/-- **Single-jump shift for Σ⁰:** at positive levels, replacing `Z` by its jump `Z'` lowers the
existential level by one. -/
theorem isSigma_succ_jump_iff : IsSigma Z.jump (n + 1) p ↔ IsSigma Z (n + 2) p :=
  ⟨isSigma_succ_succ_of_isSigma_succ_jump, isSigma_jump_of_isSigma_succ⟩

/-- **Single-jump shift for Π⁰:** at positive levels, replacing `Z` by its jump `Z'` lowers the
universal level by one. -/
theorem isPi_succ_jump_iff : IsPi Z.jump (n + 1) p ↔ IsPi Z (n + 2) p := by
  rw [← isSigma_not_iff, ← isSigma_not_iff]
  exact isSigma_succ_jump_iff

/-- **Single-jump shift for Δ⁰:** at positive levels, replacing `Z` by its jump `Z'` lowers the
intersection level by one. -/
theorem isDelta_succ_jump_iff : IsDelta Z.jump (n + 1) p ↔ IsDelta Z (n + 2) p := by
  simp only [isDelta_iff]
  exact and_congr isSigma_succ_jump_iff isPi_succ_jump_iff

/-- A predicate is decidable relative to `Z'` exactly when it is Δ⁰₂ relative to `Z`. -/
theorem isSigma_zero_jump_iff_isDelta_two : IsSigma Z.jump 0 p ↔ IsDelta Z 2 p := by
  rw [← isDelta_one_iff_isSigma_zero, isDelta_succ_jump_iff]

/-! ### Relativized Post's theorem -/

/-- Shifting an existential pointclass by `k` applications of the Turing jump. -/
theorem isSigma_add_succ_iff_iterate_jump :
    IsSigma Z (n + k + 1) p ↔ IsSigma (Set.jump^[k] Z) (n + 1) p := by
  induction k generalizing Z with
  | zero => exact Iff.rfl
  | succ k ih =>
    have hidx : n + (k + 1) + 1 = n + k + 2 := by omega
    rw [Function.iterate_succ_apply, ← ih, isSigma_succ_jump_iff, hidx]

/-- Shifting a universal pointclass by `k` applications of the Turing jump. -/
theorem isPi_add_succ_iff_iterate_jump :
    IsPi Z (n + k + 1) p ↔ IsPi (Set.jump^[k] Z) (n + 1) p := by
  rw [← isSigma_not_iff, ← isSigma_not_iff]
  exact isSigma_add_succ_iff_iterate_jump

/-- Shifting an intersection pointclass by `k` applications of the Turing jump. -/
theorem isDelta_add_succ_iff_iterate_jump :
    IsDelta Z (n + k + 1) p ↔ IsDelta (Set.jump^[k] Z) (n + 1) p := by
  simp only [isDelta_iff]
  exact and_congr isSigma_add_succ_iff_iterate_jump isPi_add_succ_iff_iterate_jump

/-- **Relativized Post's theorem (Σ⁰ form):** `p` is Σ⁰_{n+1} relative to `Z` exactly when `p`
is Σ⁰₁ relative to the `n`-th jump `Z⁽ⁿ⁾`. -/
theorem isSigma_succ_iff_isSigma_one_iterate_jump :
    IsSigma Z (n + 1) p ↔ IsSigma (Set.jump^[n] Z) 1 p := by
  simpa using isSigma_add_succ_iff_iterate_jump (Z := Z) (n := 0) (k := n) (p := p)

/-- **Relativized Post's theorem (Π⁰ form):** `p` is Π⁰_{n+1} relative to `Z` exactly when `p`
is Π⁰₁ relative to the `n`-th jump `Z⁽ⁿ⁾`. -/
theorem isPi_succ_iff_isPi_one_iterate_jump :
    IsPi Z (n + 1) p ↔ IsPi (Set.jump^[n] Z) 1 p := by
  rw [← isSigma_not_iff, ← isSigma_not_iff]
  exact isSigma_succ_iff_isSigma_one_iterate_jump

/-- **Relativized Post's theorem (Δ⁰ form):** `p` is Δ⁰_{n+1} relative to `Z` exactly when `p`
is Σ⁰₀ (decidable) relative to the `n`-th jump `Z⁽ⁿ⁾`. -/
theorem isDelta_succ_iff_isSigma_zero_iterate_jump :
    IsDelta Z (n + 1) p ↔ IsSigma (Set.jump^[n] Z) 0 p := by
  rw [← isDelta_one_iff_isSigma_zero]
  simpa using isDelta_add_succ_iff_iterate_jump (Z := Z) (n := 0) (k := n) (p := p)

/-- **Relativized Post's theorem (domain form):** `p` is Σ⁰_{n+1} relative to `Z` exactly when it
is the domain of a partial function recursive in `Z⁽ⁿ⁾`. -/
theorem isSigma_succ_iff_exists_recursiveIn_domain :
    IsSigma Z (n + 1) p ↔
      ∃ f : α →. ℕ, RecursiveIn {(Set.jump^[n] Z).oracle} f ∧ ∀ x, p x ↔ (f x).Dom := by
  rw [isSigma_succ_iff_isSigma_one_iterate_jump, isSigma_one_iff_exists_recursiveIn_domain]

/-- **Relativized Post's theorem (index form):** `p` is Σ⁰_{n+1} relative to `Z` exactly when it
is the domain of an oracle program relative to `Z⁽ⁿ⁾` on encoded inputs. -/
theorem isSigma_succ_iff_exists_code :
    IsSigma Z (n + 1) p ↔
      ∃ c : Code, ∀ x, p x ↔ (Code.eval (Set.jump^[n] Z).oracle c (encode x)).Dom := by
  rw [isSigma_succ_iff_isSigma_one_iterate_jump, isSigma_one_iff_exists_code]

/-- **Relativized Post's theorem (Boolean decision form):** `p` is Δ⁰_{n+1} relative to `Z`
exactly when it has a total Boolean decision procedure computable in `Z⁽ⁿ⁾`. -/
theorem isDelta_succ_iff_exists_computableIn :
    IsDelta Z (n + 1) p ↔
      ∃ b : α → Bool, ComputableIn {(Set.jump^[n] Z).oracle} b ∧ ∀ x, b x = true ↔ p x := by
  rw [isDelta_succ_iff_isSigma_zero_iterate_jump, isSigma_zero_iff]

/-- **Relativized Post's theorem for sets (Δ⁰):** a set of naturals `A` is Δ⁰_{n+1} relative to
`Z` exactly when `A` is Turing reducible to `Z⁽ⁿ⁾`. -/
theorem isDelta_succ_mem_iff_turingReducible_iterate_jump {A : Set ℕ} :
    IsDelta Z (n + 1) (· ∈ A) ↔ TuringReducible A.oracle (Set.jump^[n] Z).oracle := by
  rw [isDelta_succ_iff_isSigma_zero_iterate_jump, isSigma_zero_mem_iff_turingReducible]

/-! ### Completeness of iterated jumps -/

/-- The `(n + 1)`-th jump `Z⁽ⁿ⁺¹⁾` is Σ⁰_{n+1} relative to `Z`. -/
theorem isSigma_succ_iterate_jump :
    IsSigma Z (n + 1) (· ∈ Set.jump^[n + 1] Z) := by
  rw [isSigma_succ_iff_isSigma_one_iterate_jump, Function.iterate_succ_apply']
  exact isSigma_one_jump

/-- Every Σ⁰_{n+1} predicate relative to `Z` reduces one-one to `Z⁽ⁿ⁺¹⁾` by an ordinary
computable function. -/
theorem IsSigma.oneOneReducible_iterate_jump (h : IsSigma Z (n + 1) p) :
    OneOneReducible p (· ∈ Set.jump^[n + 1] Z) := by
  rw [Function.iterate_succ_apply']
  exact (isSigma_succ_iff_isSigma_one_iterate_jump.1 h).oneOneReducible_jump

/-- Every Σ⁰_{n+1} predicate relative to `Z` reduces many-one to `Z⁽ⁿ⁺¹⁾` by an ordinary
computable function. -/
theorem IsSigma.manyOneReducible_iterate_jump (h : IsSigma Z (n + 1) p) :
    ManyOneReducible p (· ∈ Set.jump^[n + 1] Z) :=
  h.oneOneReducible_iterate_jump.to_many_one

/-- **Many-one completeness of `Z⁽ⁿ⁺¹⁾`:** a predicate is Σ⁰_{n+1} relative to `Z` exactly when
it many-one reduces to `Z⁽ⁿ⁺¹⁾`. -/
theorem isSigma_succ_iff_manyOneReducible_iterate_jump :
    IsSigma Z (n + 1) p ↔ ManyOneReducible p (· ∈ Set.jump^[n + 1] Z) := by
  refine ⟨IsSigma.manyOneReducible_iterate_jump, fun ⟨f, hf, heq⟩ => ?_⟩
  exact (isSigma_succ_iterate_jump.preimage hf.computableIn).of_eq fun x => (heq x).symm

/-- **One-one completeness of `Z⁽ⁿ⁺¹⁾`:** a predicate is Σ⁰_{n+1} relative to `Z` exactly when
it one-one reduces to `Z⁽ⁿ⁺¹⁾`. -/
theorem isSigma_succ_iff_oneOneReducible_iterate_jump :
    IsSigma Z (n + 1) p ↔ OneOneReducible p (· ∈ Set.jump^[n + 1] Z) :=
  ⟨IsSigma.oneOneReducible_iterate_jump,
    fun h => isSigma_succ_iff_manyOneReducible_iterate_jump.2 h.to_many_one⟩

/-- The complement `(Z⁽ⁿ⁺¹⁾)ᶜ` is Π⁰_{n+1} relative to `Z`. -/
theorem isPi_succ_compl_iterate_jump :
    IsPi Z (n + 1) (· ∈ (Set.jump^[n + 1] Z)ᶜ) :=
  isPi_not_iff.2 isSigma_succ_iterate_jump |>.of_eq fun _ => (Set.mem_compl_iff _ _).symm

/-- Every Π⁰_{n+1} predicate relative to `Z` reduces one-one to `(Z⁽ⁿ⁺¹⁾)ᶜ` by an ordinary
computable function. -/
theorem IsPi.oneOneReducible_compl_iterate_jump (h : IsPi Z (n + 1) p) :
    OneOneReducible p (· ∈ (Set.jump^[n + 1] Z)ᶜ) := by
  obtain ⟨f, hf, hinj, heq⟩ := (isSigma_not_iff.2 h).oneOneReducible_iterate_jump
  exact ⟨f, hf, hinj, fun x => by simpa [Set.mem_compl_iff] using (heq x).not⟩

/-- Every Π⁰_{n+1} predicate relative to `Z` reduces many-one to `(Z⁽ⁿ⁺¹⁾)ᶜ` by an ordinary
computable function. -/
theorem IsPi.manyOneReducible_compl_iterate_jump (h : IsPi Z (n + 1) p) :
    ManyOneReducible p (· ∈ (Set.jump^[n + 1] Z)ᶜ) :=
  h.oneOneReducible_compl_iterate_jump.to_many_one

/-- **Many-one completeness of `(Z⁽ⁿ⁺¹⁾)ᶜ`:** a predicate is Π⁰_{n+1} relative to `Z` exactly when
it many-one reduces to `(Z⁽ⁿ⁺¹⁾)ᶜ`. -/
theorem isPi_succ_iff_manyOneReducible_compl_iterate_jump :
    IsPi Z (n + 1) p ↔ ManyOneReducible p (· ∈ (Set.jump^[n + 1] Z)ᶜ) := by
  refine ⟨IsPi.manyOneReducible_compl_iterate_jump, fun ⟨f, hf, heq⟩ => ?_⟩
  exact (isPi_succ_compl_iterate_jump.preimage hf.computableIn).of_eq fun x => (heq x).symm

/-- **One-one completeness of `(Z⁽ⁿ⁺¹⁾)ᶜ`:** a predicate is Π⁰_{n+1} relative to `Z` exactly when
it one-one reduces to `(Z⁽ⁿ⁺¹⁾)ᶜ`. -/
theorem isPi_succ_iff_oneOneReducible_compl_iterate_jump :
    IsPi Z (n + 1) p ↔ OneOneReducible p (· ∈ (Set.jump^[n + 1] Z)ᶜ) :=
  ⟨IsPi.oneOneReducible_compl_iterate_jump,
    fun h => isPi_succ_iff_manyOneReducible_compl_iterate_jump.2 h.to_many_one⟩

/-! ### Strictness of the arithmetical hierarchy -/

/-- **Asymmetry of Σ⁰ and Π⁰:** `Z⁽ⁿ⁺¹⁾` is not Π⁰_{n+1} relative to `Z`. -/
theorem not_isPi_succ_iterate_jump :
    ¬IsPi Z (n + 1) (· ∈ Set.jump^[n + 1] Z) := by
  intro h
  have hred := isDelta_succ_mem_iff_turingReducible_iterate_jump.1
    (isDelta_iff.2 ⟨isSigma_succ_iterate_jump, h⟩)
  rw [Function.iterate_succ_apply'] at hred
  exact Set.not_jump_turingReducible _ hred

/-- `Z⁽ⁿ⁺¹⁾` is not Δ⁰_{n+1} relative to `Z`. -/
theorem not_isDelta_succ_iterate_jump :
    ¬IsDelta Z (n + 1) (· ∈ Set.jump^[n + 1] Z) :=
  fun h => not_isPi_succ_iterate_jump (isDelta_iff.1 h).2

/-- `(Z⁽ⁿ⁺¹⁾)ᶜ` is not Σ⁰_{n+1} relative to `Z`. -/
theorem not_isSigma_succ_compl_iterate_jump :
    ¬IsSigma Z (n + 1) (· ∈ (Set.jump^[n + 1] Z)ᶜ) :=
  fun h => not_isPi_succ_iterate_jump <|
    isSigma_not_iff.1 (h.of_eq fun _ => Set.mem_compl_iff _ _)

/-- `(Z⁽ⁿ⁺¹⁾)ᶜ` is not Δ⁰_{n+1} relative to `Z`. -/
theorem not_isDelta_succ_compl_iterate_jump :
    ¬IsDelta Z (n + 1) (· ∈ (Set.jump^[n + 1] Z)ᶜ) :=
  fun h => not_isSigma_succ_compl_iterate_jump (isDelta_iff.1 h).1

/-- Exact Σ⁰ level of the `n`-th jump: `Z⁽ⁿ⁾ ∈ Σ⁰_m(Z)` iff `n ≤ m`. -/
theorem isSigma_iterate_jump_iff :
    IsSigma Z m (· ∈ Set.jump^[n] Z) ↔ n ≤ m := by
  constructor
  · intro h
    by_contra hnm
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    exact not_isDelta_succ_iterate_jump ((h.of_le (by omega)).delta_succ)
  · intro hnm
    cases n with
    | zero => exact (isSigma_zero_mem_iff_turingReducible.2 (.refl _)).of_le hnm
    | succ k => exact isSigma_succ_iterate_jump.of_le hnm

/-- Exact Π⁰ level of a positive iterated jump: for `0 < n`, `Z⁽ⁿ⁾ ∈ Π⁰_m(Z)` iff `n < m`. -/
theorem isPi_iterate_jump_iff (hn : 0 < n) :
    IsPi Z m (· ∈ Set.jump^[n] Z) ↔ n < m := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  refine ⟨fun h => not_le.1 fun hmk => not_isPi_succ_iterate_jump (h.of_le hmk),
    fun hkm => isSigma_succ_iterate_jump.pi_succ.of_le hkm⟩

/-- Exact Δ⁰ level of a positive iterated jump: for `0 < n`, `Z⁽ⁿ⁾ ∈ Δ⁰_m(Z)` iff `n < m`. -/
theorem isDelta_iterate_jump_iff (hn : 0 < n) :
    IsDelta Z m (· ∈ Set.jump^[n] Z) ↔ n < m := by
  rw [isDelta_iff, isSigma_iterate_jump_iff, isPi_iterate_jump_iff hn]
  omega

/-- Exact Π⁰ level of the complement of the `n`-th jump: `(Z⁽ⁿ⁾)ᶜ ∈ Π⁰_m(Z)` iff `n ≤ m`. -/
theorem isPi_compl_iterate_jump_iff :
    IsPi Z m (· ∈ (Set.jump^[n] Z)ᶜ) ↔ n ≤ m := by
  rw [← isSigma_iterate_jump_iff (Z := Z) (m := m) (n := n)]
  exact ⟨fun h => isPi_not_iff.1 (h.of_eq fun _ => Set.mem_compl_iff _ _),
    fun h => (isPi_not_iff.2 h).of_eq fun _ => (Set.mem_compl_iff _ _).symm⟩

/-- Exact Σ⁰ level of the complement of a positive iterated jump: for `0 < n`,
`(Z⁽ⁿ⁾)ᶜ ∈ Σ⁰_m(Z)` iff `n < m`. -/
theorem isSigma_compl_iterate_jump_iff (hn : 0 < n) :
    IsSigma Z m (· ∈ (Set.jump^[n] Z)ᶜ) ↔ n < m := by
  rw [← isPi_iterate_jump_iff (Z := Z) (m := m) hn]
  exact ⟨fun h => isSigma_not_iff.1 (h.of_eq fun _ => Set.mem_compl_iff _ _),
    fun h => (isSigma_not_iff.2 h).of_eq fun _ => (Set.mem_compl_iff _ _).symm⟩

/-- Exact Δ⁰ level of the complement of a positive iterated jump: for `0 < n`,
`(Z⁽ⁿ⁾)ᶜ ∈ Δ⁰_m(Z)` iff `n < m`. -/
theorem isDelta_compl_iterate_jump_iff (hn : 0 < n) :
    IsDelta Z m (· ∈ (Set.jump^[n] Z)ᶜ) ↔ n < m := by
  rw [isDelta_iff, isSigma_compl_iterate_jump_iff hn, isPi_compl_iterate_jump_iff]
  omega

/-- The parity join `Z⁽ⁿ⁺¹⁾ ⊕ (Z⁽ⁿ⁺¹⁾)ᶜ` is Δ⁰_{n+2} relative to `Z`. -/
theorem isDelta_add_two_turingJoin_compl_iterate_jump :
    IsDelta Z (n + 2) (· ∈ (Set.jump^[n + 1] Z).turingJoin (Set.jump^[n + 1] Z)ᶜ) := by
  rw [isDelta_succ_mem_iff_turingReducible_iterate_jump, Set.oracle_turingJoin_turingReducible_iff]
  refine ⟨.refl _, isSigma_zero_mem_iff_turingReducible.1 ?_⟩
  exact (isSigma_not_iff.2 (isPi_zero_iff.2
    (isSigma_zero_mem_iff_turingReducible.2 (.refl _)))).of_eq
    fun _ => (Set.mem_compl_iff _ _).symm

/-- **Strict inclusion `Σ⁰_{n+1} ∪ Π⁰_{n+1} ⊊ Δ⁰_{n+2}` (Σ⁰ half):** `Z⁽ⁿ⁺¹⁾ ⊕ (Z⁽ⁿ⁺¹⁾)ᶜ` is not
Σ⁰_{n+1} relative to `Z`. -/
theorem not_isSigma_succ_turingJoin_compl_iterate_jump :
    ¬IsSigma Z (n + 1) (· ∈ (Set.jump^[n + 1] Z).turingJoin (Set.jump^[n + 1] Z)ᶜ) := by
  intro h
  exact not_isSigma_succ_compl_iterate_jump <|
    (h.preimage Primrec.nat_double_succ.computableIn).of_eq fun _ =>
      Set.two_mul_add_one_mem_turingJoin

/-- **Strict inclusion `Σ⁰_{n+1} ∪ Π⁰_{n+1} ⊊ Δ⁰_{n+2}` (Π⁰ half):** `Z⁽ⁿ⁺¹⁾ ⊕ (Z⁽ⁿ⁺¹⁾)ᶜ` is not
Π⁰_{n+1} relative to `Z`. -/
theorem not_isPi_succ_turingJoin_compl_iterate_jump :
    ¬IsPi Z (n + 1) (· ∈ (Set.jump^[n + 1] Z).turingJoin (Set.jump^[n + 1] Z)ᶜ) := by
  intro h
  exact not_isPi_succ_iterate_jump <|
    (h.preimage Primrec.nat_double.computableIn).of_eq fun _ =>
      Set.two_mul_mem_turingJoin

/-! ### The Δ⁰₂ Limit Lemma -/

/-- **Relativized Δ⁰₂ Limit Lemma for predicates:** a predicate on any primitive-codable type is
Δ⁰₂ relative to `Z` exactly when it is the eventually stable limit of a uniformly `Z`-computable
sequence of Boolean guesses. -/
theorem isDelta_two_iff_exists_eventually :
    IsDelta Z 2 p ↔
      ∃ f : ℕ → α → Bool, ComputableIn₂ {Z.oracle} f ∧
        ∀ x, ∀ᶠ s in atTop, f s x = true ↔ p x :=
  ⟨fun h => exists_computableIn₂_eventually_of_isSigma_zero_jump
      (isSigma_zero_jump_iff_isDelta_two.2 h),
    fun ⟨_, hf, heq⟩ => isDelta_two_of_eventually hf heq⟩

/-- **Unrelativized Δ⁰₂ Limit Lemma for predicates:** a predicate on any primitive-codable type is
Δ⁰₂ exactly when it is the eventually stable limit of a uniformly computable sequence of Boolean
guesses. -/
theorem isDelta_two_empty_iff_exists_eventually :
    IsDelta ∅ 2 p ↔
      ∃ f : ℕ → α → Bool, Computable₂ f ∧
        ∀ x, ∀ᶠ s in atTop, f s x = true ↔ p x := by
  rw [isDelta_two_iff_exists_eventually]
  exact exists_congr fun f => and_congr_left fun _ => computableIn_empty_iff

/-- **Relativized Δ⁰₂ Limit Lemma for sets:** a set of naturals `A` is Δ⁰₂ relative to `Z`
exactly when its characteristic function has a uniformly `Z`-computable approximation. -/
theorem isDelta_two_mem_iff_exists_converges {A : Set ℕ} :
    IsDelta Z 2 (· ∈ A) ↔
      ∃ f : ℕ → ℕ → ℕ, ComputableIn₂ {Z.oracle} f ∧
        Approximation.Converges f (A.indicator 1) := by
  rw [isDelta_succ_mem_iff_turingReducible_iterate_jump (n := 1), Function.iterate_one,
    Approximation.turingReducible_jump_iff_exists_converges]

/-- **Unrelativized Δ⁰₂ Limit Lemma for sets:** a set of naturals `A` is Δ⁰₂ exactly when its
characteristic function has a uniformly computable approximation. -/
theorem isDelta_two_empty_mem_iff_exists_converges {A : Set ℕ} :
    IsDelta ∅ 2 (· ∈ A) ↔
      ∃ f : ℕ → ℕ → ℕ, Computable₂ f ∧
        Approximation.Converges f (A.indicator 1) := by
  rw [isDelta_two_mem_iff_exists_converges]
  exact exists_congr fun f => and_congr_left fun _ => computableIn_empty_iff

end TauCeti.ArithmeticalHierarchy
