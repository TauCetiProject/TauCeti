/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Computability.Hierarchy.Basic
public import TauCeti.Computability.Jump.Basic
import TauCeti.Computability.SingleOracle.Combinators
import TauCeti.Computability.SingleOracle.Domain
import TauCeti.Computability.SingleOracle.Relative
import TauCeti.Computability.SingleOracle.Universal

/-!
# The first existential level of the arithmetical hierarchy

A predicate on any primitive-codable type is Σ⁰₁ relative to `Z` exactly when it is the domain
of a partial function recursive in `Z`. The forward implication searches the total Boolean matrix;
the reverse implication uses finite successful computations of an oracle program. Totality of the
oracle is essential to computing bounded simulation.

This gives the ordinary characterization by `REPred` at the empty oracle, the index and
partial-range presentations (`TauCeti.ArithmeticalHierarchy.isSigma_one_iff_exists_code`,
`TauCeti.ArithmeticalHierarchy.isSigma_one_iff_exists_recursiveIn_ran`), closure of relative
`Σ⁰₁` sets under partial preimages (`RecursiveIn.isSigma_one_mem_preimage`), ranges
(`RecursiveIn.isSigma_one_mem_ran`, `ComputableIn.isSigma_one_mem_range`), and partial and total
images (`RecursiveIn.isSigma_one_mem_image`, `ComputableIn.isSigma_one_mem_image`), and one-one
and many-one completeness of the relative jump `Z'` and its complement `(Z')ᶜ` for `Σ⁰₁` and
`Π⁰₁` predicates. No program index is extracted computably from a semantic pointclass-membership
proof.

## References

* R. I. Soare, *Recursively Enumerable Sets and Degrees*, Springer, 1987, Chapters III.2 and IV.1.
-/

public section

open Encodable Denumerable TauCeti.Oracle.Single

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

/-- Halting of an oracle program with a Boolean output (`0` or `1`) is Σ⁰₁ uniformly in the
program and input. -/
theorem isSigma_one_eval_bool :
    IsSigma Z 1 (fun p : Code × ℕ =>
      ∃ b : Bool, encode b ∈ Code.eval Z.oracle p.1 p.2) := by
  obtain ⟨guard, hguard⟩ := Code.exists_boolGuardCode
  have harg : Primrec fun p : Code × ℕ =>
      Nat.pair (encode (Code.comp guard p.1)) p.2 :=
    Primrec₂.natPair.comp
      (Primrec.encode.comp (Code.primrec₂_comp.comp (Primrec.const guard) Primrec.fst))
      Primrec.snd
  have hdom := (isSigma_one_dom_eval (Z := Z) Code.universal).preimage harg.computableIn
  refine hdom.of_eq fun p => ?_
  have hZ : Z.oracle = ((Z.indicator 1 : ℕ → ℕ) : ℕ →. ℕ) := funext fun n => by simp
  rw [hZ, Code.eval_universal, ← hZ, ofNat_encode, Code.eval_comp]
  have hbind : ∀ y : ℕ,
      y ∈ (Code.eval Z.oracle p.1 p.2 >>= Code.eval Z.oracle guard) ↔
        ∃ m ∈ Code.eval Z.oracle p.1 p.2, m < 2 ∧ y = 0 := fun y => by
    refine Part.mem_bind_iff.trans ?_
    simp [hguard]
  simp only [Part.dom_iff_mem, hbind]
  constructor
  · rintro ⟨_, m, hm, hlt, _⟩
    match m, hlt with
    | 0, _ => exact ⟨false, hm⟩
    | 1, _ => exact ⟨true, hm⟩
  · rintro ⟨b, hb⟩
    exact ⟨0, encode b, hb, by cases b <;> decide, rfl⟩

/-- The domain of a partial function recursive in `Z` is Σ⁰₁ relative to `Z`. -/
theorem _root_.RecursiveIn.isSigma_one_mem_dom {β : Type*} [Primcodable β] {f : α →. β}
    (hf : RecursiveIn {Z.oracle} f) : IsSigma Z 1 (· ∈ f.Dom) := by
  unfold RecursiveIn at hf
  obtain ⟨c, hc⟩ := Code.exists_code.1 hf
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
    unfold RecursiveIn at hf
    obtain ⟨c, hc⟩ := Code.exists_code.1 hf
    exact ⟨c, fun x => by simpa [hc, encodek] using heq x⟩
  · rintro ⟨c, heq⟩
    exact ((isSigma_one_dom_eval c).preimage Primrec.encode.computableIn).of_eq
      fun x => (heq x).symm

/-- The preimage of a relative Σ⁰₁ set under a partial function recursive in `Z` is Σ⁰₁ relative
to `Z`. -/
theorem _root_.RecursiveIn.isSigma_one_mem_preimage {β : Type*} [Primcodable β] {f : α →. β}
    {S : Set β} (hf : RecursiveIn {Z.oracle} f) (hS : IsSigma Z 1 (· ∈ S)) :
    IsSigma Z 1 (· ∈ f.preimage S) := by
  unfold RecursiveIn at hf
  obtain ⟨cf, hcf⟩ := Code.exists_code.1 hf
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

/-- The range of a partial function recursive in `Z` is Σ⁰₁ relative to `Z`. -/
theorem _root_.RecursiveIn.isSigma_one_mem_ran {β : Type*} [Primcodable β] {f : α →. β}
    (hf : RecursiveIn {Z.oracle} f) : IsSigma Z 1 (· ∈ f.ran) := by
  unfold RecursiveIn at hf
  obtain ⟨c, hc⟩ := Code.exists_code.1 hf
  have heq : ∀ y : β, encode y ∈ (Code.eval Z.oracle (Code.rangeDom c)).Dom ↔ y ∈ f.ran := by
    intro y
    rw [Code.dom_eval_rangeDom_oracle, hc]
    simp only [PFun.ran, Set.mem_ofPred_eq, Part.mem_bind_iff, Part.mem_map_iff]
    constructor
    · rintro ⟨n, x, _, y', hy', heq⟩
      exact ⟨x, encode_injective heq ▸ hy'⟩
    · rintro ⟨x, hx⟩
      exact ⟨encode x, x, by simp [encodek], y, hx, rfl⟩
  exact ((isSigma_one_dom_eval (Z := Z) (Code.rangeDom c)).preimage
    Primrec.encode.computableIn).of_eq heq

/-- The image of a relative Σ⁰₁ set under a partial function recursive in `Z` is Σ⁰₁ relative to
`Z`. -/
theorem _root_.RecursiveIn.isSigma_one_mem_image {β : Type*} [Primcodable β] {f : α →. β}
    {S : Set α} (hf : RecursiveIn {Z.oracle} f) (hS : IsSigma Z 1 (· ∈ S)) :
    IsSigma Z 1 (· ∈ f.image S) := by
  unfold RecursiveIn at hf
  obtain ⟨cf, hcf⟩ := Code.exists_code.1 hf
  obtain ⟨g, hg, hSdom⟩ := hS.exists_recursiveIn_domain
  unfold RecursiveIn at hg
  obtain ⟨cg, hcg⟩ := Code.exists_code.1 hg
  have heq : ∀ y : β, encode y ∈ (Code.eval Z.oracle (Code.imageDom cf cg)).Dom ↔
      y ∈ f.image S := by
    intro y
    rw [Code.dom_eval_imageDom_oracle, PFun.mem_image, PFun.mem_image, hcf, hcg]
    constructor
    · rintro ⟨n, hnS, hnf⟩
      obtain ⟨x, hx, hy⟩ := Part.mem_bind_iff.1 hnf
      obtain ⟨y', hy', heq⟩ := (Part.mem_map_iff encode).1 hy
      have hdx : decode (α := α) n = some x := Part.mem_ofOption.1 hx
      have hxg : (g x).Dom := by simpa [PFun.Dom, hdx] using hnS
      exact ⟨x, (hSdom x).2 hxg, encode_injective heq ▸ hy'⟩
    · rintro ⟨x, hxS, hxf⟩
      refine ⟨encode x, ?_, ?_⟩
      · simpa [PFun.Dom, encodek] using (hSdom x).1 hxS
      · exact Part.mem_bind (by simp [encodek]) ((Part.mem_map_iff encode).2 ⟨y, hxf, rfl⟩)
  exact ((isSigma_one_dom_eval (Z := Z) (Code.imageDom cf cg)).preimage
    Primrec.encode.computableIn).of_eq heq

/-- The range of a total function computable in `Z` is Σ⁰₁ relative to `Z`. -/
theorem _root_.ComputableIn.isSigma_one_mem_range {β : Type*} [Primcodable β] {f : α → β}
    (hf : ComputableIn {Z.oracle} f) : IsSigma Z 1 (· ∈ Set.range f) := by
  have hf' : RecursiveIn {Z.oracle} (f : α →. β) := hf
  simpa only [PFun.ran_coe] using hf'.isSigma_one_mem_ran

/-- The image of a relative Σ⁰₁ set under a total function computable in `Z` is Σ⁰₁ relative to
`Z`. -/
theorem _root_.ComputableIn.isSigma_one_mem_image {β : Type*} [Primcodable β] {f : α → β}
    {S : Set α} (hf : ComputableIn {Z.oracle} f) (hS : IsSigma Z 1 (· ∈ S)) :
    IsSigma Z 1 (· ∈ f '' S) := by
  have hf' : RecursiveIn {Z.oracle} (f : α →. β) := hf
  exact (hf'.isSigma_one_mem_image hS).of_eq fun y => by
    simp [PFun.mem_image, PFun.coe_val, eq_comm]

/-- A set in any primitive-codable type is Σ⁰₁ relative to `Z` if and only if it is the range of a
partial function `ℕ →. α` recursive in `Z`. Unlike total range presentations, this holds for the
empty set as well. -/
theorem isSigma_one_iff_exists_recursiveIn_ran {S : Set α} :
    IsSigma Z 1 (· ∈ S) ↔ ∃ f : ℕ →. α, RecursiveIn {Z.oracle} f ∧ f.ran = S := by
  refine ⟨fun hS => ?_, fun ⟨f, hf, hran⟩ => hran ▸ hf.isSigma_one_mem_ran⟩
  obtain ⟨c, hc⟩ := isSigma_one_iff_exists_code.1 hS
  refine ⟨_, Code.recursiveIn_decode_restrict (α := α) Z.oracle c, Set.ext fun y => ?_⟩
  simp only [PFun.ran, Set.mem_ofPred_eq, Part.mem_bind_iff, Part.mem_ofOption, Part.mem_map_iff]
  constructor
  · rintro ⟨n, x, _, w, hw, rfl⟩
    exact (hc x).2 (Part.dom_iff_mem.2 ⟨w, hw⟩)
  · intro hy
    obtain ⟨w, hw⟩ := Part.dom_iff_mem.1 ((hc y).1 hy)
    exact ⟨encode y, y, encodek y, w, hw, rfl⟩

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
