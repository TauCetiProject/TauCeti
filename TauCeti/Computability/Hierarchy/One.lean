/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Computability.Hierarchy.Basic
public import TauCeti.Computability.Jump.Basic
import TauCeti.Computability.SingleOracle.Relative

/-!
# The first existential level of the arithmetical hierarchy

A predicate on any primitive-codable type is Σ⁰₁ relative to `Z` exactly when it is the domain
of a partial function recursive in `Z`. The forward implication searches the total Boolean matrix;
the reverse implication uses finite successful computations of an oracle program. Totality of the
oracle is essential to computing bounded simulation.

This gives the ordinary characterization by `REPred` at the empty oracle, the index presentation
by oracle-program domains, and one-one completeness of the relative jump for Σ⁰₁ predicates.
No program index is extracted computably from a semantic pointclass-membership proof.

## References

* R. I. Soare, *Recursively Enumerable Sets and Degrees*, Springer, 1987, Chapters III.2 and IV.1.
-/

public section

open Encodable TauCeti.Oracle.Single

namespace TauCeti.ArithmeticalHierarchy

variable {Z : Set ℕ} {α : Type*} [Primcodable α] {p : α → Prop}

/-- An existential number quantifier over a total `Z`-computable matrix defines the domain
of a partial function recursive in `Z`, by least-witness search. -/
theorem IsSigma.exists_recursiveIn_domain (h : IsSigma Z 1 p) :
    ∃ f : α →. ℕ, RecursiveIn {Z.oracle} f ∧ ∀ x, p x ↔ (f x).Dom := by
  obtain ⟨b, hb, heq⟩ := isSigma_one_iff.1 h
  have hnot := Primrec.not.computableIn.comp hb
  unfold ComputableIn RecursiveIn at hnot
  refine ⟨fun x => Nat.rfind fun y => Part.some (b (x, y)), ?_, fun x => ?_⟩
  · -- Compare encodings, keeping invalid input codes undefined. Numerical search succeeds
    -- at zero, so negate the Boolean matrix to exchange its codes.
    unfold RecursiveIn
    exact hnot.rfind.of_eq fun n => by
      cases e : decode (α := α) n with
      | none =>
        simpa [e, decode_prod_val] using Nat.rfind_zero_none (fun _ => Part.none) rfl
      | some x =>
        simp only [decode_prod_val, Nat.unpair_pair, decode_nat, Option.map_some, e,
          Option.bind_some, Part.map_some, Part.map_eq_map, Part.coe_some, Part.bind_some]
        congr 1
        funext y
        cases b (x, y) <;> rfl
  · refine (heq x).trans ⟨?_, ?_⟩
    · rintro ⟨y, hy⟩
      exact Nat.rfind_dom.2 ⟨y, by simp [hy], fun _ => trivial⟩
    · intro hdom
      obtain ⟨y, hy, -⟩ := Nat.rfind_dom.1 hdom
      exact ⟨y, (Part.mem_some_iff.1 hy).symm⟩

/-- The domain of an oracle program is Σ⁰₁: a number belongs exactly when a finite successful
run is found at some fuel bound. -/
theorem isSigma_one_dom_eval (c : Code) :
    IsSigma Z 1 (fun x => (Code.eval Z.oracle c x).Dom) := by
  have hσ : ComputableIn₂ {Z.oracle} (fun (_ : ℕ) z => Z.indicator 1 z) :=
    Z.computableIn_indicator.comp ComputableIn.snd
  have hargs : ComputableIn {Z.oracle} (fun p : ℕ × ℕ => (0, p.2, c, p.1)) :=
    (ComputableIn.const 0).pair (ComputableIn.snd.pair
      ((ComputableIn.const c).pair ComputableIn.fst))
  have hrun := (Code.computableIn_evaln hσ).comp hargs
  refine isSigma_one_iff.2 ⟨fun p =>
    (Code.evaln (fun z => some (Z.indicator 1 z)) p.2 c p.1).isSome,
    Primrec.option_isSome.computableIn.comp hrun, fun x => ?_⟩
  have hanswers : ∀ z y, some (Z.indicator 1 z) = some y ↔ y ∈ Z.oracle z := by
    simp [eq_comm]
  simp only [Part.dom_iff_mem, Code.mem_eval_iff_exists_evaln hanswers,
    Option.isSome_iff_exists]
  exact ⟨fun ⟨y, k, d, hd, _⟩ => ⟨k, d, hd⟩,
    fun ⟨k, d, hd⟩ => ⟨d.output, k, d, hd, rfl⟩⟩

/-- **The first relativized Post equivalence.** Σ⁰₁ predicates relative to `Z` are exactly the
domains of partial functions recursive in `Z`. -/
theorem isSigma_one_iff_exists_recursiveIn_domain : IsSigma Z 1 p ↔
    ∃ f : α →. ℕ, RecursiveIn {Z.oracle} f ∧ ∀ x, p x ↔ (f x).Dom := by
  refine ⟨IsSigma.exists_recursiveIn_domain, fun ⟨f, hf, heq⟩ => ?_⟩
  unfold RecursiveIn at hf
  obtain ⟨c, hc⟩ := Code.exists_code.1 hf
  exact ((isSigma_one_dom_eval c).preimage Primrec.encode.computableIn).of_eq fun x => by
    simpa [hc, encodek] using (heq x).symm

/-- Σ⁰₁ predicates relative to `Z` are exactly oracle-program domains on encoded inputs. -/
theorem isSigma_one_iff_exists_code : IsSigma Z 1 p ↔
    ∃ c : Code, ∀ x, p x ↔ (Code.eval Z.oracle c (encode x)).Dom := by
  constructor
  · intro h
    obtain ⟨f, hf, heq⟩ := h.exists_recursiveIn_domain
    unfold RecursiveIn at hf
    obtain ⟨c, hc⟩ := Code.exists_code.1 hf
    exact ⟨c, fun x => by simpa [hc, encodek] using heq x⟩
  · rintro ⟨c, heq⟩
    exact ((isSigma_one_dom_eval c).preimage Primrec.encode.computableIn).of_eq
      fun x => (heq x).symm

/-- At the empty oracle, the quantifier definition of Σ⁰₁ agrees with Mathlib's c.e.
predicate `REPred`. -/
theorem isSigma_one_empty_iff_rePred : IsSigma ∅ 1 p ↔ REPred p := by
  rw [isSigma_one_iff_exists_recursiveIn_domain]
  constructor
  · rintro ⟨f, hf, heq⟩
    have hf' : Partrec f := hf.partrec_of_oracle fun g hg => by
      rw [Set.mem_singleton_iff.1 hg, Set.oracle_empty]
      exact Partrec.const' _
    exact hf'.dom_re.of_eq fun x => (heq x).symm
  · intro hp
    refine ⟨fun x => (Part.assert (p x) fun _ => Part.some ()).map fun _ => 0,
      (hp.map (Computable.const 0).to₂).recursiveIn, fun x => ?_⟩
    simp [Part.assert]

/-- The diagonal halting set relative to `Z` is Σ⁰₁ relative to `Z`. -/
theorem isSigma_one_jump : IsSigma Z 1 (· ∈ Z.jump) :=
  isSigma_one_iff_exists_recursiveIn_domain.2
    ⟨_, RecursiveIn.iff_nat.2 Z.recursiveIn_eval_diag, fun _ => Set.mem_jump⟩

/-- Every relative Σ⁰₁ set reduces one-one to the relative jump. -/
theorem IsSigma.oneOneReducible_jump (h : IsSigma Z 1 p) :
    OneOneReducible p (· ∈ Z.jump) := by
  obtain ⟨f, hf, heq⟩ := h.exists_recursiveIn_domain
  unfold RecursiveIn at hf
  have hred : OneOneReducible p
      (fun n => (Part.bind (decode (α := α) n) fun x => (f x).map encode).Dom) :=
    ⟨encode, Computable.encode, encode_injective, fun x => by simpa using heq x⟩
  exact hred.trans (Z.oneOneReducible_jump_of_recursiveIn hf)

end TauCeti.ArithmeticalHierarchy
