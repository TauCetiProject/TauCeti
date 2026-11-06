/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Computability.Hierarchy.Basic
public import TauCeti.Computability.Enumeration.Domain
public import TauCeti.Computability.Jump.Basic
import TauCeti.Computability.SingleOracle.Relative
import TauCeti.Computability.SingleOracle.Universal

/-!
# The first existential level of the arithmetical hierarchy

A predicate on the naturals is Σ⁰₁ relative to `Z` exactly when it is the domain of a partial
function recursive in `Z`. The forward implication searches the total Boolean matrix; the
reverse implication uses finite successful computations of an oracle program. Totality of the
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

variable {Z : Set ℕ} {p : ℕ → Prop}

/-- An existential number quantifier over a total `Z`-computable matrix defines the domain
of a partial function recursive in `Z`, by least-witness search. -/
theorem IsSigma.exists_recursiveIn_domain (h : IsSigma Z 1 p) :
    ∃ f : ℕ →. ℕ, Nat.RecursiveIn {Z.oracle} f ∧ ∀ x, p x ↔ (f x).Dom := by
  obtain ⟨b, hb, heq⟩ := isSigma_one_iff.1 h
  have hnot := Primrec.not.computableIn.comp hb
  unfold ComputableIn RecursiveIn at hnot
  -- Mathlib's numerical search succeeds at zero; encode the negated Boolean matrix.
  have hmatrix : Nat.RecursiveIn {Z.oracle} fun n =>
      Part.some (encode (!b (n.unpair.1, n.unpair.2))) := by
    exact hnot.of_eq fun n => by simp
  refine ⟨_, hmatrix.rfind, fun x => (heq x).trans ?_⟩
  simp only [Nat.unpair_pair]
  refine ⟨fun ⟨y, hy⟩ => Nat.rfind_dom.2 ⟨y, ?_, fun _ => by simp⟩, ?_⟩
  · simp [hy]
  · intro hdom
    obtain ⟨y, hy, -⟩ := Nat.rfind_dom.1 hdom
    exact ⟨y, by cases h : b (x, y) <;> simp_all⟩

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
    ∃ f : ℕ →. ℕ, Nat.RecursiveIn {Z.oracle} f ∧ ∀ x, p x ↔ (f x).Dom := by
  refine ⟨IsSigma.exists_recursiveIn_domain, fun ⟨f, hf, heq⟩ => ?_⟩
  obtain ⟨c, hc⟩ := Code.exists_code.1 hf
  exact (isSigma_one_dom_eval c).of_eq fun x => by rw [hc]; exact (heq x).symm

/-- Σ⁰₁ predicates relative to `Z` are exactly the domains in the adopted oracle numbering. -/
theorem isSigma_one_iff_exists_code : IsSigma Z 1 p ↔
    ∃ c : Code, ∀ x, p x ↔ (Code.eval Z.oracle c x).Dom := by
  rw [isSigma_one_iff_exists_recursiveIn_domain]
  constructor
  · rintro ⟨f, hf, heq⟩
    obtain ⟨c, hc⟩ := Code.exists_code.1 hf
    exact ⟨c, fun x => by rw [hc]; exact heq x⟩
  · rintro ⟨c, heq⟩
    exact ⟨_, Code.recursiveIn_eval Z.oracle c, heq⟩

/-- At the empty oracle, the quantifier definition of Σ⁰₁ agrees with Mathlib's c.e.
predicate `REPred`. -/
theorem isSigma_one_empty_iff_rePred : IsSigma ∅ 1 p ↔ REPred p := by
  rw [isSigma_one_iff_exists_recursiveIn_domain]
  constructor
  · rintro ⟨f, hf, heq⟩
    have hf' : Partrec f := (RecursiveIn.iff_nat.2 hf).partrec_of_oracle fun g hg => by
      rw [Set.mem_singleton_iff.1 hg, Set.oracle_empty]
      exact Partrec.const' _
    exact hf'.dom_re.of_eq fun x => (heq x).symm
  · intro hp
    obtain ⟨c, hc⟩ := Enumeration.rePred_iff_exists_code.1 hp
    exact ⟨c.eval, (Partrec.nat_iff.1 (Nat.Partrec.Code.eval_part.comp
      (Computable.const c) Computable.id)).recursiveIn, hc⟩

/-- The diagonal halting set relative to `Z` is Σ⁰₁ relative to `Z`. -/
theorem isSigma_one_jump : IsSigma Z 1 (· ∈ Z.jump) := by
  have h := (isSigma_one_dom_eval (Z := Z) Code.universal).preimage
    (Primrec₂.natPair.comp Primrec.id Primrec.id).computableIn
  have hO : Z.oracle = ((Z.indicator 1 : ℕ → ℕ) : ℕ →. ℕ) :=
    funext fun x => Set.oracle_apply Z x
  exact h.of_eq fun x => by simp [hO, Code.eval_universal, Set.mem_jump]

/-- Every relative Σ⁰₁ set reduces one-one to the relative jump. -/
theorem IsSigma.oneOneReducible_jump (h : IsSigma Z 1 p) :
    OneOneReducible p (· ∈ Z.jump) := by
  obtain ⟨f, hf, heq⟩ := h.exists_recursiveIn_domain
  have hred : OneOneReducible p (fun x => (f x).Dom) :=
    ⟨id, Computable.id, Function.injective_id, heq⟩
  exact hred.trans (Z.oneOneReducible_jump_of_recursiveIn hf)

end TauCeti.ArithmeticalHierarchy
