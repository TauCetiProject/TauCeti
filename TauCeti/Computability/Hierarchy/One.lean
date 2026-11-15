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
by oracle-program domains, one-one completeness of the relative jump for Σ⁰₁ predicates, the
identification of Δ⁰₁ relative to `Z` with Σ⁰₀ relative to `Z`, and the separation of Σ⁰₁ from
Π⁰₁ by the relative jump.
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
  refine ⟨fun x => Nat.rfind fun y => Part.some (b (x, y)),
    RecursiveIn.rfind hb.recursiveIn, fun x => (heq x).trans ⟨?_, ?_⟩⟩
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
  exact ⟨fun ⟨_, k, d, hd, _⟩ => ⟨k, d, hd⟩,
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

/-- A predicate is Σ⁰₁ relative to `Z` exactly when it reduces one-one to the jump `Z'`. -/
theorem isSigma_one_iff_oneOneReducible_jump :
    IsSigma Z 1 p ↔ OneOneReducible p (· ∈ Z.jump) :=
  ⟨IsSigma.oneOneReducible_jump, fun h => isSigma_one_jump.of_manyOneReducible h.to_many_one⟩

/-- A predicate is Σ⁰₁ relative to `Z` exactly when it reduces many-one to the jump `Z'`. -/
theorem isSigma_one_iff_manyOneReducible_jump :
    IsSigma Z 1 p ↔ ManyOneReducible p (· ∈ Z.jump) :=
  ⟨fun h => h.oneOneReducible_jump.to_many_one, isSigma_one_jump.of_manyOneReducible⟩

/-- **First-level complement theorem.** A predicate is Δ⁰₁ relative to `Z`—both Σ⁰₁ and Π⁰₁
relative to `Z`—exactly when it is Σ⁰₀ relative to `Z`. -/
@[simp]
theorem isDelta_one_iff : IsDelta Z 1 p ↔ IsSigma Z 0 p := by
  classical
  constructor
  · intro h
    obtain ⟨hp, hnp⟩ := isDelta_iff.1 h
    obtain ⟨b₁, hb₁, heq₁⟩ := isSigma_one_iff.1 hp
    obtain ⟨b₂, hb₂, heq₂⟩ := isSigma_one_iff.1 (isSigma_not_iff.2 hnp)
    have hex : ∀ x, ∃ y, (b₁ (x, y) || b₂ (x, y)) = true := fun x => by
      by_cases hx : p x
      · obtain ⟨y, hy⟩ := (heq₁ x).1 hx
        exact ⟨y, by simp [hy]⟩
      · obtain ⟨y, hy⟩ := (heq₂ x).1 hx
        exact ⟨y, by simp [hy]⟩
    have hor : ComputableIn₂ {Z.oracle} (fun x y => b₁ (x, y) || b₂ (x, y)) :=
      Primrec.or.computableIn.comp (hb₁.pair hb₂)
    have hw : ComputableIn {Z.oracle} (fun x : α => Nat.find (hex x)) :=
      (RecursiveIn.rfind hor.recursiveIn₂).of_eq_tot fun x =>
        Nat.mem_rfind.2 ⟨Part.mem_some_iff.2 (Nat.find_spec (hex x)).symm,
          fun hm => Part.mem_some_iff.2 (Bool.eq_false_iff.2 (Nat.find_min (hex x) hm)).symm⟩
    refine isSigma_zero_iff.2 ⟨fun x => b₁ (x, Nat.find (hex x)),
      hb₁.comp (ComputableIn.id.pair hw), fun x => ?_⟩
    constructor
    · intro htrue
      exact (heq₁ x).2 ⟨_, htrue⟩
    · intro hx
      rcases Bool.or_eq_true_iff.1 (Nat.find_spec (hex x)) with h₁ | h₂
      · exact h₁
      · exact False.elim (((heq₂ x).2 ⟨_, h₂⟩) hx)
  · intro h
    exact isDelta_iff.2
      ⟨h.one_of_zero, isSigma_not_iff.1 (isSigma_not_iff.2 (isPi_zero_iff.2 h)).one_of_zero⟩

/-- The diagonal halting set `Z'` is not Π⁰₁ relative to `Z`. -/
theorem not_isPi_one_jump : ¬IsPi Z 1 (· ∈ Z.jump) := fun h =>
  Z.not_jump_turingReducible <|
    isSigma_zero_mem_iff_turingReducible.1 (isDelta_one_iff.1 (isDelta_iff.2 ⟨isSigma_one_jump, h⟩))

end TauCeti.ArithmeticalHierarchy
