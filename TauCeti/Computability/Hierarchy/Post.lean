/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Computability.Hierarchy.Closure
public import TauCeti.Computability.Hierarchy.One
public import TauCeti.Computability.Jump.Iterate
import TauCeti.Computability.SingleOracle.Primrec

/-!
# Relativized Post's theorem and strictness of the arithmetical hierarchy

This file proves **relativized Post's theorem**, connecting the quantifier-defined arithmetical
pointclasses `IsSigma Z`, `IsPi Z`, and `IsDelta Z` to computability and enumerability in the
iterated Turing jumps `Set.jump^[n] Z`:

* **Post complementation (`isDelta_one_iff_isSigma_zero`)**: a predicate is `Δ⁰₁(Z)` if and only
  if it is decided by a total Boolean procedure computable in `Z` (`Σ⁰₀(Z)`).
* **Jump shift (`isSigma_succ_succ_iff_jump`, `isSigma_succ_iff_isSigma_one_iterate_jump`)**:
  for every `n`, a predicate is `Σ⁰_{n+2}(Z)` if and only if it is `Σ⁰₁(Z')`, and hence a
  predicate is `Σ⁰_{n+1}(Z)` if and only if it is `Σ⁰₁(Z⁽ⁿ⁾)`.
* **Domain and completeness characterizations (`isSigma_succ_iff_exists_recursiveIn_domain`,
  `isSigma_succ_iff_oneOneReducible_iterate_jump`,
  `isPi_succ_iff_oneOneReducible_compl_iterate_jump`)**: `Σ⁰_{n+1}(Z)` predicates are exactly the
  domains of partial functions recursive in `Z⁽ⁿ⁾`, and `Z⁽ⁿ⁺¹⁾` (respectively `(Z⁽ⁿ⁺¹⁾)ᶜ`) is
  one-one complete for `Σ⁰_{n+1}(Z)` (respectively `Π⁰_{n+1}(Z)`).
* **`Δ⁰_{n+1}` characterization (`isDelta_succ_iff_isSigma_zero_iterate_jump`,
  `isDelta_succ_mem_iff_turingReducible_iterate_jump`)**: a predicate is `Δ⁰_{n+1}(Z)` if and only
  if it has a total Boolean decision procedure computable in `Z⁽ⁿ⁾`; for sets of natural numbers,
  `C` is `Δ⁰_{n+1}(Z)` if and only if `C ≤_T Z⁽ⁿ⁾`.
* **Hierarchy strictness (`not_isPi_succ_iterate_jump`, `not_isDelta_succ_iterate_jump`,
  `isDelta_succ_succ_turingJoin_iterate_jump_compl`,
  `not_isSigma_succ_turingJoin_iterate_jump_compl`,
  `not_isPi_succ_turingJoin_iterate_jump_compl`)**: for every oracle `Z` and every `n`,
  `Σ⁰_{n+1}(Z) ≠ Π⁰_{n+1}(Z)`, `Δ⁰_{n+1}(Z)` is strictly contained in both `Σ⁰_{n+1}(Z)` and
  `Π⁰_{n+1}(Z)`, and `Σ⁰_{n+1}(Z) ∪ Π⁰_{n+1}(Z)` is strictly contained in `Δ⁰_{n+2}(Z)`.

The key step `isSigma_two_dom_eval_jump` expresses convergence of an oracle program against `Z'`
by existentially guessing a fuel bound and the binary code of the finite subset of `Z'` queried
below the run's stage use: positive membership queries below the use form a bounded universal
`Σ⁰₁(Z)` condition, negative queries form a bounded universal `Π⁰₁(Z)` condition, and bounded
quantifier closure places their conjunction inside `Σ⁰₂(Z)`.

## Main results

* `TauCeti.ArithmeticalHierarchy.isDelta_one_iff_isSigma_zero`: relativized Post complementation.
* `TauCeti.ArithmeticalHierarchy.isSigma_two_iff_isSigma_one_jump`,
  `TauCeti.ArithmeticalHierarchy.isSigma_succ_succ_iff_jump`: trading an alternating quantifier
  for a Turing jump of the oracle.
* `TauCeti.ArithmeticalHierarchy.isSigma_succ_iff_exists_recursiveIn_domain`: `Σ⁰_{n+1}(Z)`
  predicates are the domains of partial functions recursive in `Z⁽ⁿ⁾`.
* `TauCeti.ArithmeticalHierarchy.isSigma_succ_iff_oneOneReducible_iterate_jump`: one-one
  completeness of `Z⁽ⁿ⁺¹⁾` for `Σ⁰_{n+1}(Z)`.
* `TauCeti.ArithmeticalHierarchy.isDelta_succ_iff_isSigma_zero_iterate_jump`,
  `TauCeti.ArithmeticalHierarchy.isDelta_succ_mem_iff_turingReducible_iterate_jump`: `Δ⁰_{n+1}(Z)`
  predicates and sets are those computable in `Z⁽ⁿ⁾`.
* `TauCeti.ArithmeticalHierarchy.not_isPi_succ_iterate_jump`,
  `TauCeti.ArithmeticalHierarchy.not_isDelta_succ_iterate_jump`,
  `TauCeti.ArithmeticalHierarchy.isDelta_succ_succ_turingJoin_iterate_jump_compl`: strictness of
  every inclusion in the relativized arithmetical hierarchy.

## References

* R. I. Soare, *Recursively Enumerable Sets and Degrees*, Springer, 1987, Chapter IV.1–2,
  Theorems IV.1.13, IV.2.1, and IV.2.2.
-/

public section

open Encodable TauCeti.Oracle.Single

namespace TauCeti.ArithmeticalHierarchy

variable {Z : Set ℕ} {m n : ℕ} {α : Type*} [Primcodable α] {p : α → Prop}

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
    exact (computableIn_const_iff.1 (Set.oracle_empty ▸ hb)).computablePred.of_eq heq
  · rintro ⟨_, hp⟩
    exact ⟨fun x => decide (p x), hp.computableIn, fun _ => decide_eq_true_iff⟩

/-- **Relativized Post complementation.** A predicate is `Δ⁰₁` relative to `Z` if and only if it
is `Σ⁰₀` relative to `Z`. -/
theorem isDelta_one_iff_isSigma_zero : IsDelta Z 1 p ↔ IsSigma Z 0 p := by
  refine ⟨fun h => ?_, fun h => h.delta_succ⟩
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
    ComputableIn.find hc hex
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

/-- A predicate is `Σ⁰₁` relative to `Z` if and only if it reduces one-one to `Z'`. -/
theorem isSigma_one_iff_oneOneReducible_jump :
    IsSigma Z 1 p ↔ OneOneReducible p (· ∈ Z.jump) :=
  ⟨IsSigma.oneOneReducible_jump, fun ⟨_, hf, _, heq⟩ =>
    (isSigma_one_jump.preimage hf.computableIn).of_eq fun x => (heq x).symm⟩

/-- A predicate is `Σ⁰₁` relative to `Z` if and only if it reduces many-one to `Z'`. -/
theorem isSigma_one_iff_manyOneReducible_jump :
    IsSigma Z 1 p ↔ ManyOneReducible p (· ∈ Z.jump) :=
  ⟨fun h => h.oneOneReducible_jump.to_many_one, fun ⟨_, hf, heq⟩ =>
    (isSigma_one_jump.preimage hf.computableIn).of_eq fun x => (heq x).symm⟩

/-- The complement `(Z')ᶜ` is `Π⁰₁` relative to `Z`. -/
theorem isPi_one_compl_jump : IsPi Z 1 (· ∈ Z.jumpᶜ) :=
  (isPi_not_iff.2 isSigma_one_jump).of_eq fun _ => Iff.rfl

/-- Every `Π⁰₁(Z)` predicate reduces one-one to `(Z')ᶜ`. -/
theorem IsPi.oneOneReducible_compl_jump (h : IsPi Z 1 p) :
    OneOneReducible p (· ∈ Z.jumpᶜ) := by
  classical
  obtain ⟨f, hf, hinj, heq⟩ := (isSigma_not_iff.2 h).oneOneReducible_jump
  exact ⟨f, hf, hinj, fun x => (not_iff_comm.1 (heq x)).symm⟩

/-- A predicate is `Π⁰₁` relative to `Z` if and only if it reduces one-one to `(Z')ᶜ`. -/
theorem isPi_one_iff_oneOneReducible_compl_jump :
    IsPi Z 1 p ↔ OneOneReducible p (· ∈ Z.jumpᶜ) :=
  ⟨IsPi.oneOneReducible_compl_jump, fun ⟨_, hf, _, heq⟩ =>
    (isPi_one_compl_jump.preimage hf.computableIn).of_eq fun x => (heq x).symm⟩

/-- A predicate is `Π⁰₁` relative to `Z` if and only if it reduces many-one to `(Z')ᶜ`. -/
theorem isPi_one_iff_manyOneReducible_compl_jump :
    IsPi Z 1 p ↔ ManyOneReducible p (· ∈ Z.jumpᶜ) :=
  ⟨fun h => h.oneOneReducible_compl_jump.to_many_one, fun ⟨_, hf, heq⟩ =>
    (isPi_one_compl_jump.preimage hf.computableIn).of_eq fun x => (heq x).symm⟩

/-! ### Shifting levels across the Turing jump -/

/-- The domain of an oracle program evaluated relative to `Z'` is `Σ⁰₂` relative to `Z`. -/
theorem isSigma_two_dom_eval_jump (c : Code) :
    IsSigma Z 2 (fun x => (Code.eval Z.jump.oracle c x).Dom) := by
  classical
  have hargs : Primrec (fun p : ℕ × ℕ => (p.2.unpair.2, p.2.unpair.1, c, p.1)) :=
    (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd)).pair
      ((Primrec.fst.comp (Primrec.unpair.comp Primrec.snd)).pair
        ((Primrec.const c).pair Primrec.fst))
  have hhalt : IsSigma Z 2 (fun p : ℕ × ℕ =>
      (Code.evaln (Code.setAnswers (Finset.equivBitIndices p.2.unpair.2 : Set ℕ))
        p.2.unpair.1 c p.1).isSome = true) :=
    (isSigma_zero_iff.2 ⟨_,
      (Primrec.option_isSome.comp
        ((Code.primrec_evaln Code.primrec₂_setAnswers_equivBitIndices).comp hargs)).computableIn,
      fun _ => Iff.rfl⟩).of_le (Nat.zero_le 2)
  have huse : ComputableIn {Z.oracle} (fun p : ℕ × ℕ =>
      Code.stageUse (Code.setAnswers (Finset.equivBitIndices p.2.unpair.2 : Set ℕ))
        p.2.unpair.1 c p.1) :=
    ((Code.primrec_stageUse Code.primrec₂_setAnswers_equivBitIndices).comp hargs).computableIn
  have hbit : Primrec (fun q : (ℕ × ℕ) × ℕ => q.1.2.unpair.2.testBit q.2) :=
    Primrec.nat_testBit.comp
      (Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.fst))) Primrec.snd
  have hmemF : IsSigma Z 0 (fun q : (ℕ × ℕ) × ℕ =>
      q.2 ∈ Finset.equivBitIndices q.1.2.unpair.2) :=
    isSigma_zero_iff.2 ⟨_, hbit.computableIn, fun _ => by simp⟩
  have hpos : IsSigma Z 2 (fun p : ℕ × ℕ =>
      ∀ z < Code.stageUse (Code.setAnswers (Finset.equivBitIndices p.2.unpair.2 : Set ℕ))
          p.2.unpair.1 c p.1,
        z ∈ Finset.equivBitIndices p.2.unpair.2 → z ∈ Z.jump) := by
    have himp : IsSigma Z 1 (fun q : (ℕ × ℕ) × ℕ =>
        q.2 ∈ Finset.equivBitIndices q.1.2.unpair.2 → q.2 ∈ Z.jump) :=
      IsSigma.imp (isPi_zero_iff.2 hmemF).succ (isSigma_one_jump.preimage ComputableIn.snd)
    exact (himp.forall_lt huse).succ
  have hneg : IsSigma Z 2 (fun p : ℕ × ℕ =>
      ∀ z < Code.stageUse (Code.setAnswers (Finset.equivBitIndices p.2.unpair.2 : Set ℕ))
          p.2.unpair.1 c p.1,
        z ∉ Finset.equivBitIndices p.2.unpair.2 → z ∉ Z.jump) := by
    have himp : IsPi Z 1 (fun q : (ℕ × ℕ) × ℕ =>
        q.2 ∉ Finset.equivBitIndices q.1.2.unpair.2 → q.2 ∉ Z.jump) :=
      IsPi.imp (isSigma_not_iff.2 (isPi_zero_iff.2 hmemF)).succ
        ((isPi_not_iff.2 isSigma_one_jump).preimage ComputableIn.snd)
    exact (himp.forall_lt huse).sigma_succ
  refine ((hhalt.and (hpos.and hneg)).exists_nat).of_eq fun x => ?_
  have hanswers : ∀ z y, Code.setAnswers Z.jump z = some y ↔ y ∈ Z.jump.oracle z := by
    simp [eq_comm]
  constructor
  · rintro ⟨w, hsome, hposw, hnegw⟩
    obtain ⟨d, hd⟩ := Option.isSome_iff_exists.1 hsome
    have hduse := Code.stageUse_eq_of_evaln_eq_some hd
    refine Part.dom_iff_mem.2 ⟨d.output, Code.evaln_sound hd fun z hz y hy => ?_⟩
    have hz' : z < Code.stageUse (Code.setAnswers (Finset.equivBitIndices w.unpair.2 : Set ℕ))
        w.unpair.1 c x := hduse ▸ hz
    by_cases hzF : z ∈ Finset.equivBitIndices w.unpair.2
    · have hzj : z ∈ Z.jump := hposw z hz' hzF
      have hy1 : y = 1 := by
        simp at hzF
        simpa [hzF] using hy.symm
      simp [hy1, hzj]
    · have hzj : z ∉ Z.jump := hnegw z hz' hzF
      have hy0 : y = 0 := by
        simp at hzF
        simpa [hzF] using hy.symm
      simp [hy0, hzj]
  · intro hdom
    obtain ⟨y, hy⟩ := Part.dom_iff_mem.1 hdom
    obtain ⟨k, d, hd, -⟩ := (Code.mem_eval_iff_exists_evaln hanswers).1 hy
    let S : Finset ℕ := (Finset.range d.use).filter (· ∈ Z.jump)
    have hdS : Code.evaln (Code.setAnswers (S : Set ℕ)) k c x = some d :=
      Code.evaln_eq_some_of_eqOn hd <| Code.eqOn_setAnswers_iff.2 fun z hz => by
        simp [S, Set.mem_Iio.1 hz]
    refine ⟨Nat.pair k (Finset.equivBitIndices.symm S), ?_, ?_, ?_⟩
    · simp [hdS]
    · intro z _ hzS
      simp only [Nat.unpair_pair, Finset.equivBitIndices.apply_symm_apply] at hzS
      exact (Finset.mem_filter.1 hzS).2
    · intro z hz hzS
      simp only [Nat.unpair_pair, Finset.equivBitIndices.apply_symm_apply,
        Code.stageUse_eq_of_evaln_eq_some hdS] at hz hzS
      exact fun hzj => hzS (Finset.mem_filter.2 ⟨Finset.mem_range.2 hz, hzj⟩)

/-- A predicate is `Σ⁰₂` relative to `Z` if and only if it is `Σ⁰₁` relative to `Z'`. -/
theorem isSigma_two_iff_isSigma_one_jump : IsSigma Z 2 p ↔ IsSigma Z.jump 1 p := by
  classical
  constructor
  · intro hp
    obtain ⟨q, hq, heq⟩ := isSigma_succ_iff.1 hp
    obtain ⟨f, hf, -, hfeq⟩ := (isSigma_not_iff.2 hq).oneOneReducible_jump
    refine isSigma_one_iff.2 ⟨fun a => Z.jump.indicator 1 (f a) == 0,
      (Primrec.beq.comp Primrec.id (Primrec.const 0)).computableIn.comp
        (Z.jump.computableIn_indicator.comp hf.computableIn), fun x => ?_⟩
    refine (heq x).trans (exists_congr fun y => ?_)
    by_cases hfy : f (x, y) ∈ Z.jump
    · simp [hfy, (hfeq (x, y)).2 hfy]
    · have hqy : q (x, y) := by
        by_contra hnq
        exact hfy ((hfeq (x, y)).1 hnq)
      simp [hfy, hqy]
  · intro hp
    obtain ⟨c, hc⟩ := isSigma_one_iff_exists_code.1 hp
    exact ((isSigma_two_dom_eval_jump c).preimage Primrec.encode.computableIn).of_eq
      fun x => (hc x).symm

/-- Trading an alternating number quantifier for a Turing jump of the oracle on `Σ⁰` levels. -/
theorem isSigma_succ_succ_iff_jump : IsSigma Z (n + 2) p ↔ IsSigma Z.jump (n + 1) p := by
  induction n generalizing α with
  | zero => exact isSigma_two_iff_isSigma_one_jump
  | succ n ih =>
    rw [isSigma_succ_iff (n := n + 2), isSigma_succ_iff (n := n + 1)]
    exact exists_congr fun q => and_congr
      ((isSigma_not_iff (Z := Z)).symm.trans (ih.trans isSigma_not_iff)) Iff.rfl

/-- Trading an alternating number quantifier for a Turing jump of the oracle on `Π⁰` levels. -/
theorem isPi_succ_succ_iff_jump : IsPi Z (n + 2) p ↔ IsPi Z.jump (n + 1) p :=
  (isSigma_not_iff (Z := Z)).symm.trans (isSigma_succ_succ_iff_jump.trans isSigma_not_iff)

/-- Trading an alternating number quantifier for a Turing jump of the oracle on `Δ⁰` levels. -/
theorem isDelta_succ_succ_iff_jump : IsDelta Z (n + 2) p ↔ IsDelta Z.jump (n + 1) p :=
  isDelta_iff.trans ((and_congr isSigma_succ_succ_iff_jump isPi_succ_succ_iff_jump).trans
    isDelta_iff.symm)

/-- Shifting `k` quantifier levels into `k` iterations of the Turing jump on `Σ⁰` levels. -/
theorem isSigma_add_succ_iff_iterate_jump (k : ℕ) :
    IsSigma Z (n + 1 + k) p ↔ IsSigma (Set.jump^[k] Z) (n + 1) p := by
  induction k generalizing Z with
  | zero => rfl
  | succ k ih =>
    have hadd : n + 1 + (k + 1) = n + k + 2 := by omega
    have hadd' : n + k + 1 = n + 1 + k := by omega
    rw [hadd, isSigma_succ_succ_iff_jump, hadd', ih, Function.iterate_succ_apply]

/-- Shifting `k` quantifier levels into `k` iterations of the Turing jump on `Π⁰` levels. -/
theorem isPi_add_succ_iff_iterate_jump (k : ℕ) :
    IsPi Z (n + 1 + k) p ↔ IsPi (Set.jump^[k] Z) (n + 1) p :=
  (isSigma_not_iff (Z := Z)).symm.trans ((isSigma_add_succ_iff_iterate_jump k).trans
    isSigma_not_iff)

/-- Shifting `k` quantifier levels into `k` iterations of the Turing jump on `Δ⁰` levels. -/
theorem isDelta_add_succ_iff_iterate_jump (k : ℕ) :
    IsDelta Z (n + 1 + k) p ↔ IsDelta (Set.jump^[k] Z) (n + 1) p :=
  isDelta_iff.trans
    ((and_congr (isSigma_add_succ_iff_iterate_jump k) (isPi_add_succ_iff_iterate_jump k)).trans
      isDelta_iff.symm)

/-- A predicate is `Σ⁰_{n+1}` relative to `Z` if and only if it is `Σ⁰₁` relative to `Z⁽ⁿ⁾`. -/
theorem isSigma_succ_iff_isSigma_one_iterate_jump :
    IsSigma Z (n + 1) p ↔ IsSigma (Set.jump^[n] Z) 1 p := by
  simpa [Nat.add_comm] using isSigma_add_succ_iff_iterate_jump (Z := Z) (n := 0) (p := p) n

/-- A predicate is `Π⁰_{n+1}` relative to `Z` if and only if it is `Π⁰₁` relative to `Z⁽ⁿ⁾`. -/
theorem isPi_succ_iff_isPi_one_iterate_jump :
    IsPi Z (n + 1) p ↔ IsPi (Set.jump^[n] Z) 1 p :=
  (isSigma_not_iff (Z := Z)).symm.trans
    (isSigma_succ_iff_isSigma_one_iterate_jump.trans isSigma_not_iff)

/-- A predicate is `Δ⁰_{n+1}` relative to `Z` if and only if it is `Δ⁰₁` relative to `Z⁽ⁿ⁾`. -/
theorem isDelta_succ_iff_isDelta_one_iterate_jump :
    IsDelta Z (n + 1) p ↔ IsDelta (Set.jump^[n] Z) 1 p :=
  isDelta_iff.trans
    ((and_congr isSigma_succ_iff_isSigma_one_iterate_jump
      isPi_succ_iff_isPi_one_iterate_jump).trans isDelta_iff.symm)

/-! ### Relativized Post's theorem -/

/-- **Relativized Post's theorem, domain form.** A predicate is `Σ⁰_{n+1}` relative to `Z` if
and only if it is the domain of a partial function recursive in `Z⁽ⁿ⁾`. -/
theorem isSigma_succ_iff_exists_recursiveIn_domain :
    IsSigma Z (n + 1) p ↔
      ∃ f : α →. ℕ, RecursiveIn {(Set.jump^[n] Z).oracle} f ∧ ∀ x, p x ↔ (f x).Dom :=
  isSigma_succ_iff_isSigma_one_iterate_jump.trans isSigma_one_iff_exists_recursiveIn_domain

/-- **Relativized Post's theorem, program-domain form.** A predicate is `Σ⁰_{n+1}` relative to
`Z` if and only if it is the domain of an oracle program evaluated relative to `Z⁽ⁿ⁾` on encoded
inputs. -/
theorem isSigma_succ_iff_exists_code :
    IsSigma Z (n + 1) p ↔
      ∃ c : Code, ∀ x, p x ↔ (Code.eval (Set.jump^[n] Z).oracle c (encode x)).Dom :=
  isSigma_succ_iff_isSigma_one_iterate_jump.trans isSigma_one_iff_exists_code

/-- The `(n + 1)`-st iterated jump `Z⁽ⁿ⁺¹⁾` is `Σ⁰_{n+1}` relative to `Z`. -/
theorem isSigma_succ_iterate_jump : IsSigma Z (n + 1) (· ∈ Set.jump^[n + 1] Z) := by
  rw [isSigma_succ_iff_isSigma_one_iterate_jump, Function.iterate_succ_apply']
  exact isSigma_one_jump

/-- Every `Σ⁰_{n+1}(Z)` predicate reduces one-one to `Z⁽ⁿ⁺¹⁾`. -/
theorem IsSigma.oneOneReducible_iterate_jump (h : IsSigma Z (n + 1) p) :
    OneOneReducible p (· ∈ Set.jump^[n + 1] Z) := by
  rw [Function.iterate_succ_apply']
  exact (isSigma_succ_iff_isSigma_one_iterate_jump.1 h).oneOneReducible_jump

/-- **Relativized Post's theorem, one-one completeness of `Z⁽ⁿ⁺¹⁾`.** A predicate is `Σ⁰_{n+1}`
relative to `Z` if and only if it reduces one-one to `Z⁽ⁿ⁺¹⁾`. -/
theorem isSigma_succ_iff_oneOneReducible_iterate_jump :
    IsSigma Z (n + 1) p ↔ OneOneReducible p (· ∈ Set.jump^[n + 1] Z) :=
  ⟨IsSigma.oneOneReducible_iterate_jump, fun ⟨_, hf, _, heq⟩ =>
    (isSigma_succ_iterate_jump.preimage hf.computableIn).of_eq fun x => (heq x).symm⟩

/-- **Relativized Post's theorem, many-one completeness of `Z⁽ⁿ⁺¹⁾`.** A predicate is `Σ⁰_{n+1}`
relative to `Z` if and only if it reduces many-one to `Z⁽ⁿ⁺¹⁾`. -/
theorem isSigma_succ_iff_manyOneReducible_iterate_jump :
    IsSigma Z (n + 1) p ↔ ManyOneReducible p (· ∈ Set.jump^[n + 1] Z) :=
  ⟨fun h => h.oneOneReducible_iterate_jump.to_many_one, fun ⟨_, hf, heq⟩ =>
    (isSigma_succ_iterate_jump.preimage hf.computableIn).of_eq fun x => (heq x).symm⟩

/-- The complement `(Z⁽ⁿ⁺¹⁾)ᶜ` is `Π⁰_{n+1}` relative to `Z`. -/
theorem isPi_succ_compl_iterate_jump : IsPi Z (n + 1) (· ∈ (Set.jump^[n + 1] Z)ᶜ) :=
  (isPi_not_iff.2 isSigma_succ_iterate_jump).of_eq fun _ => Iff.rfl

/-- Every `Π⁰_{n+1}(Z)` predicate reduces one-one to `(Z⁽ⁿ⁺¹⁾)ᶜ`. -/
theorem IsPi.oneOneReducible_compl_iterate_jump (h : IsPi Z (n + 1) p) :
    OneOneReducible p (· ∈ (Set.jump^[n + 1] Z)ᶜ) := by
  classical
  obtain ⟨f, hf, hinj, heq⟩ := (isSigma_not_iff.2 h).oneOneReducible_iterate_jump
  exact ⟨f, hf, hinj, fun x => (not_iff_comm.1 (heq x)).symm⟩

/-- **Relativized Post's theorem, one-one completeness of `(Z⁽ⁿ⁺¹⁾)ᶜ`.** A predicate is
`Π⁰_{n+1}` relative to `Z` if and only if it reduces one-one to `(Z⁽ⁿ⁺¹⁾)ᶜ`. -/
theorem isPi_succ_iff_oneOneReducible_compl_iterate_jump :
    IsPi Z (n + 1) p ↔ OneOneReducible p (· ∈ (Set.jump^[n + 1] Z)ᶜ) :=
  ⟨IsPi.oneOneReducible_compl_iterate_jump, fun ⟨_, hf, _, heq⟩ =>
    (isPi_succ_compl_iterate_jump.preimage hf.computableIn).of_eq fun x => (heq x).symm⟩

/-- **Relativized Post's theorem, many-one completeness of `(Z⁽ⁿ⁺¹⁾)ᶜ`.** A predicate is
`Π⁰_{n+1}` relative to `Z` if and only if it reduces many-one to `(Z⁽ⁿ⁺¹⁾)ᶜ`. -/
theorem isPi_succ_iff_manyOneReducible_compl_iterate_jump :
    IsPi Z (n + 1) p ↔ ManyOneReducible p (· ∈ (Set.jump^[n + 1] Z)ᶜ) :=
  ⟨fun h => h.oneOneReducible_compl_iterate_jump.to_many_one, fun ⟨_, hf, heq⟩ =>
    (isPi_succ_compl_iterate_jump.preimage hf.computableIn).of_eq fun x => (heq x).symm⟩

/-- **Relativized Post's theorem for `Δ⁰_{n+1}`.** A predicate is `Δ⁰_{n+1}` relative to `Z` if
and only if it is `Σ⁰₀` relative to `Z⁽ⁿ⁾`. -/
theorem isDelta_succ_iff_isSigma_zero_iterate_jump :
    IsDelta Z (n + 1) p ↔ IsSigma (Set.jump^[n] Z) 0 p :=
  isDelta_succ_iff_isDelta_one_iterate_jump.trans isDelta_one_iff_isSigma_zero

/-- A predicate is `Δ⁰_{n+1}` relative to `Z` if and only if it has a total Boolean decision
procedure computable in `Z⁽ⁿ⁾`. -/
theorem isDelta_succ_iff_exists_computableIn :
    IsDelta Z (n + 1) p ↔
      ∃ b : α → Bool, ComputableIn {(Set.jump^[n] Z).oracle} b ∧ ∀ x, b x = true ↔ p x :=
  isDelta_succ_iff_isSigma_zero_iterate_jump.trans isSigma_zero_iff

/-- **Relativized Post's theorem for `Δ⁰_{n+1}` sets.** Membership in a set `C` of natural
numbers is `Δ⁰_{n+1}` relative to `Z` if and only if `C` is Turing reducible to `Z⁽ⁿ⁾`. -/
theorem isDelta_succ_mem_iff_turingReducible_iterate_jump {C : Set ℕ} :
    IsDelta Z (n + 1) (· ∈ C) ↔ TuringReducible C.oracle (Set.jump^[n] Z).oracle :=
  isDelta_succ_iff_isSigma_zero_iterate_jump.trans isSigma_zero_mem_iff_turingReducible

/-! ### Strictness of the relativized arithmetical hierarchy -/

/-- **Hierarchy strictness (`Σ⁰_{n+1} \ Π⁰_{n+1}`).** The iterated jump `Z⁽ⁿ⁺¹⁾` is not
`Π⁰_{n+1}` relative to `Z`. -/
theorem not_isPi_succ_iterate_jump : ¬IsPi Z (n + 1) (· ∈ Set.jump^[n + 1] Z) := fun h =>
  Z.not_iterate_jump_turingReducible_of_lt n.lt_succ_self
    (isDelta_succ_mem_iff_turingReducible_iterate_jump.1
      (isDelta_iff.2 ⟨isSigma_succ_iterate_jump, h⟩))

/-- **Hierarchy strictness (`Π⁰_{n+1} \ Σ⁰_{n+1}`).** The complement `(Z⁽ⁿ⁺¹⁾)ᶜ` is not
`Σ⁰_{n+1}` relative to `Z`. -/
theorem not_isSigma_succ_compl_iterate_jump :
    ¬IsSigma Z (n + 1) (· ∈ (Set.jump^[n + 1] Z)ᶜ) := fun h =>
  not_isPi_succ_iterate_jump (isSigma_not_iff.1 h)

/-- The iterated jump `Z⁽ⁿ⁺¹⁾` is not `Δ⁰_{n+1}` relative to `Z`. -/
theorem not_isDelta_succ_iterate_jump : ¬IsDelta Z (n + 1) (· ∈ Set.jump^[n + 1] Z) :=
  fun h => not_isPi_succ_iterate_jump (isDelta_iff.1 h).2

/-- For `m ≤ n`, the iterated jump `Z⁽ⁿ⁺¹⁾` does not belong to `Σ⁰ₘ(Z)`. -/
theorem not_isSigma_iterate_jump_of_le (hmn : m ≤ n) :
    ¬IsSigma Z m (· ∈ Set.jump^[n + 1] Z) := fun h =>
  not_isDelta_succ_iterate_jump (h.of_le hmn).delta_succ

/-- For `m ≤ n + 1`, the iterated jump `Z⁽ⁿ⁺¹⁾` does not belong to `Π⁰ₘ(Z)`. -/
theorem not_isPi_iterate_jump_of_le (hmn : m ≤ n + 1) :
    ¬IsPi Z m (· ∈ Set.jump^[n + 1] Z) := fun h =>
  not_isPi_succ_iterate_jump (h.of_le hmn)

/-- For `m ≤ n + 1`, the complement `(Z⁽ⁿ⁺¹⁾)ᶜ` does not belong to `Σ⁰ₘ(Z)`. -/
theorem not_isSigma_compl_iterate_jump_of_le (hmn : m ≤ n + 1) :
    ¬IsSigma Z m (· ∈ (Set.jump^[n + 1] Z)ᶜ) := fun h =>
  not_isSigma_succ_compl_iterate_jump (h.of_le hmn)

/-- For `m ≤ n`, the complement `(Z⁽ⁿ⁺¹⁾)ᶜ` does not belong to `Π⁰ₘ(Z)`. -/
theorem not_isPi_compl_iterate_jump_of_le (hmn : m ≤ n) :
    ¬IsPi Z m (· ∈ (Set.jump^[n + 1] Z)ᶜ) := fun h => by
  classical
  exact not_isSigma_iterate_jump_of_le hmn ((isSigma_not_iff.2 h).of_eq fun _ => not_not)

/-- For `m ≤ n + 1`, the iterated jump `Z⁽ⁿ⁺¹⁾` does not belong to `Δ⁰ₘ(Z)`. -/
theorem not_isDelta_iterate_jump_of_le (hmn : m ≤ n + 1) :
    ¬IsDelta Z m (· ∈ Set.jump^[n + 1] Z) := fun h =>
  not_isDelta_succ_iterate_jump (h.of_le hmn)

/-- **Hierarchy strictness (`Δ⁰_{n+2} \ (Σ⁰_{n+1} ∪ Π⁰_{n+1})`).** The parity join of `Z⁽ⁿ⁺¹⁾`
with its complement is `Δ⁰_{n+2}` relative to `Z`. -/
theorem isDelta_succ_succ_turingJoin_iterate_jump_compl :
    IsDelta Z (n + 2) (· ∈ (Set.jump^[n + 1] Z).turingJoin (Set.jump^[n + 1] Z)ᶜ) := by
  rw [isDelta_succ_mem_iff_turingReducible_iterate_jump, Set.oracle_turingJoin_turingReducible_iff]
  refine ⟨.rfl, isSigma_zero_mem_iff_turingReducible.1 ?_⟩
  exact isSigma_not_iff.2 (isPi_zero_iff.2 (isSigma_zero_mem_iff_turingReducible.2 .rfl))

/-- The parity join of `Z⁽ⁿ⁺¹⁾` with its complement is not `Σ⁰_{n+1}` relative to `Z`. -/
theorem not_isSigma_succ_turingJoin_iterate_jump_compl :
    ¬IsSigma Z (n + 1) (· ∈ (Set.jump^[n + 1] Z).turingJoin (Set.jump^[n + 1] Z)ᶜ) := fun h =>
  not_isSigma_succ_compl_iterate_jump <|
    (h.preimage Primrec.nat_double_succ.computableIn).of_eq fun _ =>
      Set.two_mul_add_one_mem_turingJoin

/-- The parity join of `Z⁽ⁿ⁺¹⁾` with its complement is not `Π⁰_{n+1}` relative to `Z`. -/
theorem not_isPi_succ_turingJoin_iterate_jump_compl :
    ¬IsPi Z (n + 1) (· ∈ (Set.jump^[n + 1] Z).turingJoin (Set.jump^[n + 1] Z)ᶜ) := fun h =>
  not_isPi_succ_iterate_jump <|
    (h.preimage Primrec.nat_double.computableIn).of_eq fun _ =>
      Set.two_mul_mem_turingJoin

end TauCeti.ArithmeticalHierarchy
