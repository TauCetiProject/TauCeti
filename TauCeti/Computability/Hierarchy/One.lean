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
by oracle-program domains, closure of relative `Σ⁰₁` sets under partial preimages
(`RecursiveIn.isSigma_one_mem_preimage`), and one-one and many-one completeness of the relative
jump `Z'` and its complement `(Z')ᶜ` for `Σ⁰₁` and `Π⁰₁` predicates.
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
    RecursiveIn.rfind (ComputableIn₂.recursiveIn₂ (f := fun x y => b (x, y)) hb), fun x => ?_⟩
  refine (heq x).trans ⟨?_, ?_⟩
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

/-- The domain of a partial function recursive in `Z` is Σ⁰₁ relative to `Z`. -/
theorem _root_.RecursiveIn.isSigma_one_mem_dom {β : Type*} [Primcodable β] {f : α →. β}
    (hf : RecursiveIn {Z.oracle} f) : IsSigma Z 1 (· ∈ f.Dom) := by
  obtain ⟨c, hc⟩ := RecursiveIn.exists_code.1 hf
  exact ((isSigma_one_dom_eval c).preimage Primrec.encode.computableIn).of_eq fun x => by
    simp [PFun.Dom, hc, encodek]

/-- **The first relativized Post equivalence.** Σ⁰₁ predicates relative to `Z` are exactly the
domains of partial functions recursive in `Z`. -/
theorem isSigma_one_iff_exists_recursiveIn_domain : IsSigma Z 1 p ↔
    ∃ f : α →. ℕ, RecursiveIn {Z.oracle} f ∧ ∀ x, p x ↔ (f x).Dom :=
  ⟨IsSigma.exists_recursiveIn_domain,
    fun ⟨_, hf, heq⟩ => hf.isSigma_one_mem_dom.of_eq fun x => (heq x).symm⟩

/-- Σ⁰₁ predicates relative to `Z` are exactly oracle-program domains on encoded inputs. -/
theorem isSigma_one_iff_exists_code : IsSigma Z 1 p ↔
    ∃ c : Code, ∀ x, p x ↔ (Code.eval Z.oracle c (encode x)).Dom := by
  constructor
  · intro h
    obtain ⟨f, hf, heq⟩ := h.exists_recursiveIn_domain
    obtain ⟨c, hc⟩ := RecursiveIn.exists_code.1 hf
    exact ⟨c, fun x => by simpa [hc, encodek] using heq x⟩
  · rintro ⟨c, heq⟩
    exact ((isSigma_one_dom_eval c).preimage Primrec.encode.computableIn).of_eq
      fun x => (heq x).symm

/-- The preimage of a relative Σ⁰₁ set under a partial function recursive in `Z` is Σ⁰₁ relative
to `Z`. -/
theorem _root_.RecursiveIn.isSigma_one_mem_preimage {β : Type*} [Primcodable β] {f : α →. β}
    {S : Set β} (hf : RecursiveIn {Z.oracle} f) (hS : IsSigma Z 1 (· ∈ S)) :
    IsSigma Z 1 (· ∈ f.preimage S) := by
  obtain ⟨cf, hcf⟩ := RecursiveIn.exists_code.1 hf
  obtain ⟨cS, hcS⟩ := isSigma_one_iff_exists_code.1 hS
  have heq : ∀ x : α, encode x ∈ (Code.eval Z.oracle (Code.comp cS cf)).Dom ↔
      x ∈ f.preimage S := by
    intro x
    rw [Code.dom_eval_comp, PFun.mem_preimage, PFun.mem_preimage, hcf]
    simp only [encodek, Part.coe_some, Part.bind_some, Part.mem_map_iff, PFun.Dom,
      Set.mem_ofPred_eq]
    constructor
    · rintro ⟨m, hm, y, hy, rfl⟩
      exact ⟨y, (hcS y).2 hm, hy⟩
    · rintro ⟨y, hyS, hyf⟩
      exact ⟨encode y, (hcS y).1 hyS, y, hyf, rfl⟩
  exact ((isSigma_one_dom_eval (Z := Z) (Code.comp cS cf)).preimage
    Primrec.encode.computableIn).of_eq heq

/-- At the empty oracle, the quantifier definition of Σ⁰₁ agrees with Mathlib's c.e.
predicate `REPred`. -/
theorem isSigma_one_empty_iff_rePred : IsSigma ∅ 1 p ↔ REPred p := by
  rw [isSigma_one_iff_exists_recursiveIn_domain]
  constructor
  · rintro ⟨f, hf, heq⟩
    have hf' : Partrec f := by simpa using hf
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

/-- A predicate is `Σ⁰₁` relative to `Z` if and only if it reduces one-one to `Z'`. -/
theorem isSigma_one_iff_oneOneReducible_jump :
    IsSigma Z 1 p ↔ OneOneReducible p (· ∈ Z.jump) :=
  ⟨IsSigma.oneOneReducible_jump, isSigma_one_jump.of_oneOneReducible⟩

/-- A predicate is `Σ⁰₁` relative to `Z` if and only if it reduces many-one to `Z'`. -/
theorem isSigma_one_iff_manyOneReducible_jump :
    IsSigma Z 1 p ↔ ManyOneReducible p (· ∈ Z.jump) :=
  ⟨fun h => h.oneOneReducible_jump.to_many_one, isSigma_one_jump.of_manyOneReducible⟩

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
  ⟨IsPi.oneOneReducible_compl_jump, isPi_one_compl_jump.of_oneOneReducible⟩

/-- A predicate is `Π⁰₁` relative to `Z` if and only if it reduces many-one to `(Z')ᶜ`. -/
theorem isPi_one_iff_manyOneReducible_compl_jump :
    IsPi Z 1 p ↔ ManyOneReducible p (· ∈ Z.jumpᶜ) :=
  ⟨fun h => h.oneOneReducible_compl_jump.to_many_one, isPi_one_compl_jump.of_manyOneReducible⟩

end TauCeti.ArithmeticalHierarchy
