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

* **Jump shift (`isSigma_two_iff_isSigma_one_jump`, `isSigma_succ_succ_iff_jump`,
  `isSigma_succ_iff_isSigma_one_iterate_jump`)**: for every `n`, a predicate is `Σ⁰_{n+2}(Z)` if
  and only if it is `Σ⁰_{n+1}(Z')`, and hence a predicate is `Σ⁰_{n+1}(Z)` if and only if it is
  `Σ⁰₁(Z⁽ⁿ⁾)`.
* **Domain and completeness characterizations (`isSigma_succ_iff_exists_recursiveIn_domain`,
  `isSigma_succ_iff_oneOneReducible_iterate_jump`,
  `isPi_succ_iff_oneOneReducible_compl_iterate_jump`)**: `Σ⁰_{n+1}(Z)` predicates are exactly the
  domains of partial functions recursive in `Z⁽ⁿ⁾`, and `Z⁽ⁿ⁺¹⁾` (respectively `(Z⁽ⁿ⁺¹⁾)ᶜ`) is
  one-one complete for `Σ⁰_{n+1}(Z)` (respectively `Π⁰_{n+1}(Z)`).
* **`Δ⁰_{n+1}` characterization (`isDelta_succ_iff_isSigma_zero_iterate_jump`,
  `isDelta_succ_mem_iff_turingReducible_iterate_jump`)**: combining the jump shift with relativized
  Post complementation (`isDelta_one_iff_isSigma_zero`), a predicate is `Δ⁰_{n+1}(Z)` if and only
  if it has a total Boolean decision procedure computable in `Z⁽ⁿ⁾`; for sets of natural numbers,
  `C` is `Δ⁰_{n+1}(Z)` if and only if `C ≤_T Z⁽ⁿ⁾`.
* **Hierarchy strictness (`not_isPi_succ_iterate_jump`, `not_isDelta_succ_iterate_jump`,
  `not_isDelta_succ_compl_iterate_jump`,
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
  `TauCeti.ArithmeticalHierarchy.isDelta_succ_succ_turingJoin_iterate_jump_compl`,
  `TauCeti.ArithmeticalHierarchy.not_isSigma_succ_turingJoin_iterate_jump_compl`,
  `TauCeti.ArithmeticalHierarchy.not_isPi_succ_turingJoin_iterate_jump_compl`: strictness of
  every inclusion in the relativized arithmetical hierarchy.

## References

* R. I. Soare, *Recursively Enumerable Sets and Degrees*, Springer, 1987, Chapter IV.1–2,
  Theorems IV.1.13, IV.2.1, and IV.2.2.
-/

public section

open Encodable TauCeti.Oracle.Single

namespace TauCeti.ArithmeticalHierarchy

variable {Z : Set ℕ} {m n : ℕ} {α : Type*} [Primcodable α] {p : α → Prop}

/-! ### Shifting levels across the Turing jump -/

/-- The domain of an oracle program evaluated relative to `Z'` is `Σ⁰₂` relative to `Z`. -/
theorem isSigma_two_dom_eval_jump (c : Code) :
    IsSigma Z 2 (fun x => (Code.eval Z.jump.oracle c x).Dom) := by
  classical
  -- Unpack `(x, w)` into `(bitmask, fuel, c, x)` for the primitive-recursive stage simulation.
  have hargs : Primrec (fun p : ℕ × ℕ => (p.2.unpair.2, p.2.unpair.1, c, p.1)) :=
    (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd)).pair
      ((Primrec.fst.comp (Primrec.unpair.comp Primrec.snd)).pair
        ((Primrec.const c).pair Primrec.fst))
  have hhalt : IsSigma Z 2 (fun p : ℕ × ℕ =>
      (Code.evaln (Code.setAnswers (Finset.equivBitIndices p.2.unpair.2 : Set ℕ))
        p.2.unpair.1 c p.1).isSome) :=
    (isSigma_zero_iff.2 ⟨_,
      (Primrec.option_isSome.comp
        ((Code.primrec_evaln Code.primrec₂_setAnswers_equivBitIndices).comp hargs)).computableIn,
      fun _ => Iff.rfl⟩).of_le (Nat.zero_le 2)
  have huse : ComputableIn {Z.oracle} (fun p : ℕ × ℕ =>
      Code.stageUse (Code.setAnswers (Finset.equivBitIndices p.2.unpair.2 : Set ℕ))
        p.2.unpair.1 c p.1) :=
    ((Code.primrec_stageUse Code.primrec₂_setAnswers_equivBitIndices).comp hargs).computableIn
  have hmemF : IsSigma Z 0 (fun q : (ℕ × ℕ) × ℕ =>
      q.2 ∈ Finset.equivBitIndices q.1.2.unpair.2) :=
    (isSigma_zero_empty_iff_computablePred.2
      (Primrec.mem_equivBitIndices.comp
        (Primrec.fst.comp (hargs.comp Primrec.fst)) Primrec.snd).computablePred).of_empty
  -- Positive queries below the stage use are bounded universal `Σ⁰₁(Z)`; negative ones `Π⁰₁(Z)`.
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
  -- Pack `(fuel, finite set)` witnesses into `w : ℕ` via `Nat.pair` and `Finset.equivBitIndices`.
  refine ((hhalt.and (hpos.and hneg)).exists_nat).of_eq fun x => ?_
  rw [Code.dom_eval_oracle_iff_exists_evaln_finset]
  refine ⟨fun ⟨w, hsome, hposw, hnegw⟩ =>
      ⟨w.unpair.1, Finset.equivBitIndices w.unpair.2, hsome,
        fun z hz => ⟨hposw z hz, fun hzA => by_contra fun hzF => hnegw z hz hzF hzA⟩⟩,
    fun ⟨k, F, hsome, hagree⟩ => ⟨Nat.pair k (Finset.equivBitIndices.symm F), ?_⟩⟩
  simp only [Nat.unpair_pair, Finset.equivBitIndices.apply_symm_apply]
  exact ⟨hsome, fun z hz hzF => (hagree z hz).1 hzF,
    fun z hz hzF hzA => hzF ((hagree z hz).2 hzA)⟩

/-- A predicate is `Σ⁰₂` relative to `Z` if and only if it is `Σ⁰₁` relative to `Z'`. -/
theorem isSigma_two_iff_isSigma_one_jump : IsSigma Z 2 p ↔ IsSigma Z.jump 1 p := by
  constructor
  · intro hp
    obtain ⟨q, hq, heq⟩ := isSigma_succ_iff.1 hp
    have hcompl : IsPi Z.jump 0 (· ∈ Z.jumpᶜ) :=
      (isPi_not_iff.2 (isSigma_zero_mem_iff_turingReducible.2 .rfl)).of_eq fun _ => Iff.rfl
    exact isSigma_succ_iff.2 ⟨q, hcompl.of_oneOneReducible hq.oneOneReducible_compl_jump, heq⟩
  · intro hp
    obtain ⟨c, hc⟩ := isSigma_one_iff_exists_code.1 hp
    exact ((isSigma_two_dom_eval_jump c).preimage Primrec.encode.computableIn).of_eq
      fun x => (hc x).symm

/-- A predicate is `Π⁰₂` relative to `Z` if and only if it is `Π⁰₁` relative to `Z'`. -/
theorem isPi_two_iff_isPi_one_jump : IsPi Z 2 p ↔ IsPi Z.jump 1 p :=
  (isSigma_not_iff (Z := Z)).symm.trans (isSigma_two_iff_isSigma_one_jump.trans isSigma_not_iff)

/-- A predicate is `Δ⁰₂` relative to `Z` if and only if it is `Δ⁰₁` relative to `Z'`. -/
theorem isDelta_two_iff_isDelta_one_jump : IsDelta Z 2 p ↔ IsDelta Z.jump 1 p :=
  isDelta_iff.trans ((and_congr isSigma_two_iff_isSigma_one_jump
    isPi_two_iff_isPi_one_jump).trans isDelta_iff.symm)

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
    IsSigma Z (n + k + 1) p ↔ IsSigma (Set.jump^[k] Z) (n + 1) p := by
  induction k generalizing Z with
  | zero => simp
  | succ k ih =>
    have hidx : n + (k + 1) + 1 = n + k + 2 := by omega
    rw [hidx, isSigma_succ_succ_iff_jump, ih, Function.iterate_succ_apply]

/-- Shifting `k` quantifier levels into `k` iterations of the Turing jump on `Π⁰` levels. -/
theorem isPi_add_succ_iff_iterate_jump (k : ℕ) :
    IsPi Z (n + k + 1) p ↔ IsPi (Set.jump^[k] Z) (n + 1) p :=
  (isSigma_not_iff (Z := Z)).symm.trans ((isSigma_add_succ_iff_iterate_jump k).trans
    isSigma_not_iff)

/-- Shifting `k` quantifier levels into `k` iterations of the Turing jump on `Δ⁰` levels. -/
theorem isDelta_add_succ_iff_iterate_jump (k : ℕ) :
    IsDelta Z (n + k + 1) p ↔ IsDelta (Set.jump^[k] Z) (n + 1) p :=
  isDelta_iff.trans
    ((and_congr (isSigma_add_succ_iff_iterate_jump k) (isPi_add_succ_iff_iterate_jump k)).trans
      isDelta_iff.symm)

/-- A predicate is `Σ⁰_{n+1}` relative to `Z` if and only if it is `Σ⁰₁` relative to `Z⁽ⁿ⁾`. -/
theorem isSigma_succ_iff_isSigma_one_iterate_jump :
    IsSigma Z (n + 1) p ↔ IsSigma (Set.jump^[n] Z) 1 p := by
  simpa using isSigma_add_succ_iff_iterate_jump (Z := Z) (n := 0) (p := p) n

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
    IsSigma Z (n + 1) p ↔ OneOneReducible p (· ∈ Set.jump^[n + 1] Z) := by
  rw [isSigma_succ_iff_isSigma_one_iterate_jump, Function.iterate_succ_apply']
  exact isSigma_one_iff_oneOneReducible_jump

/-- **Relativized Post's theorem, many-one completeness of `Z⁽ⁿ⁺¹⁾`.** A predicate is `Σ⁰_{n+1}`
relative to `Z` if and only if it reduces many-one to `Z⁽ⁿ⁺¹⁾`. -/
theorem isSigma_succ_iff_manyOneReducible_iterate_jump :
    IsSigma Z (n + 1) p ↔ ManyOneReducible p (· ∈ Set.jump^[n + 1] Z) := by
  rw [isSigma_succ_iff_isSigma_one_iterate_jump, Function.iterate_succ_apply']
  exact isSigma_one_iff_manyOneReducible_jump

/-- The complement `(Z⁽ⁿ⁺¹⁾)ᶜ` is `Π⁰_{n+1}` relative to `Z`. -/
theorem isPi_succ_compl_iterate_jump : IsPi Z (n + 1) (· ∈ (Set.jump^[n + 1] Z)ᶜ) := by
  rw [isPi_succ_iff_isPi_one_iterate_jump, Function.iterate_succ_apply']
  exact isPi_one_compl_jump

/-- Every `Π⁰_{n+1}(Z)` predicate reduces one-one to `(Z⁽ⁿ⁺¹⁾)ᶜ`. -/
theorem IsPi.oneOneReducible_compl_iterate_jump (h : IsPi Z (n + 1) p) :
    OneOneReducible p (· ∈ (Set.jump^[n + 1] Z)ᶜ) := by
  rw [Function.iterate_succ_apply']
  exact (isPi_succ_iff_isPi_one_iterate_jump.1 h).oneOneReducible_compl_jump

/-- **Relativized Post's theorem, one-one completeness of `(Z⁽ⁿ⁺¹⁾)ᶜ`.** A predicate is
`Π⁰_{n+1}` relative to `Z` if and only if it reduces one-one to `(Z⁽ⁿ⁺¹⁾)ᶜ`. -/
theorem isPi_succ_iff_oneOneReducible_compl_iterate_jump :
    IsPi Z (n + 1) p ↔ OneOneReducible p (· ∈ (Set.jump^[n + 1] Z)ᶜ) := by
  rw [isPi_succ_iff_isPi_one_iterate_jump, Function.iterate_succ_apply']
  exact isPi_one_iff_oneOneReducible_compl_jump

/-- **Relativized Post's theorem, many-one completeness of `(Z⁽ⁿ⁺¹⁾)ᶜ`.** A predicate is
`Π⁰_{n+1}` relative to `Z` if and only if it reduces many-one to `(Z⁽ⁿ⁺¹⁾)ᶜ`. -/
theorem isPi_succ_iff_manyOneReducible_compl_iterate_jump :
    IsPi Z (n + 1) p ↔ ManyOneReducible p (· ∈ (Set.jump^[n + 1] Z)ᶜ) := by
  rw [isPi_succ_iff_isPi_one_iterate_jump, Function.iterate_succ_apply']
  exact isPi_one_iff_manyOneReducible_compl_jump

/-- A predicate is `Δ⁰₂` relative to `Z` if and only if it is `Σ⁰₀` relative to `Z'`. -/
theorem isDelta_two_iff_isSigma_zero_jump : IsDelta Z 2 p ↔ IsSigma Z.jump 0 p :=
  isDelta_two_iff_isDelta_one_jump.trans isDelta_one_iff_isSigma_zero

/-- Membership in a set `C` of natural numbers is `Δ⁰₂` relative to `Z` if and only if `C` is
Turing reducible to `Z'`. -/
theorem isDelta_two_mem_iff_turingReducible_jump {C : Set ℕ} :
    IsDelta Z 2 (· ∈ C) ↔ TuringReducible C.oracle Z.jump.oracle :=
  isDelta_two_iff_isSigma_zero_jump.trans isSigma_zero_mem_iff_turingReducible

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

/-- The complement `(Z⁽ⁿ⁺¹⁾)ᶜ` is not `Δ⁰_{n+1}` relative to `Z`. -/
theorem not_isDelta_succ_compl_iterate_jump :
    ¬IsDelta Z (n + 1) (· ∈ (Set.jump^[n + 1] Z)ᶜ) :=
  fun h => not_isSigma_succ_compl_iterate_jump (isDelta_iff.1 h).1

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

/-- For `m ≤ n + 1`, the complement `(Z⁽ⁿ⁺¹⁾)ᶜ` does not belong to `Δ⁰ₘ(Z)`. -/
theorem not_isDelta_compl_iterate_jump_of_le (hmn : m ≤ n + 1) :
    ¬IsDelta Z m (· ∈ (Set.jump^[n + 1] Z)ᶜ) := fun h =>
  not_isDelta_succ_compl_iterate_jump (h.of_le hmn)

/-- The parity join of `Z⁽ⁿ⁺¹⁾` with its complement is `Δ⁰_{n+2}` relative to `Z`. -/
theorem isDelta_succ_succ_turingJoin_iterate_jump_compl :
    IsDelta Z (n + 2) (· ∈ (Set.jump^[n + 1] Z).turingJoin (Set.jump^[n + 1] Z)ᶜ) := by
  rw [isDelta_succ_mem_iff_turingReducible_iterate_jump, Set.oracle_turingJoin_turingReducible_iff]
  refine ⟨.rfl, isSigma_zero_mem_iff_turingReducible.1 ?_⟩
  exact isSigma_not_iff.2 (isPi_zero_iff.2 (isSigma_zero_mem_iff_turingReducible.2 .rfl))

/-- **Hierarchy strictness (`Δ⁰_{n+2} \ Σ⁰_{n+1}`).** The parity join of `Z⁽ⁿ⁺¹⁾` with its
complement is not `Σ⁰_{n+1}` relative to `Z`. -/
theorem not_isSigma_succ_turingJoin_iterate_jump_compl :
    ¬IsSigma Z (n + 1) (· ∈ (Set.jump^[n + 1] Z).turingJoin (Set.jump^[n + 1] Z)ᶜ) := fun h =>
  not_isSigma_succ_compl_iterate_jump <|
    h.of_manyOneReducible ⟨_, Primrec.nat_double_succ.to_comp,
      fun _ => Set.two_mul_add_one_mem_turingJoin.symm⟩

/-- **Hierarchy strictness (`Δ⁰_{n+2} \ Π⁰_{n+1}`).** The parity join of `Z⁽ⁿ⁺¹⁾` with its
complement is not `Π⁰_{n+1}` relative to `Z`. -/
theorem not_isPi_succ_turingJoin_iterate_jump_compl :
    ¬IsPi Z (n + 1) (· ∈ (Set.jump^[n + 1] Z).turingJoin (Set.jump^[n + 1] Z)ᶜ) := fun h =>
  not_isPi_succ_iterate_jump <|
    h.of_manyOneReducible ⟨_, Primrec.nat_double.to_comp,
      fun _ => Set.two_mul_mem_turingJoin.symm⟩

end TauCeti.ArithmeticalHierarchy
