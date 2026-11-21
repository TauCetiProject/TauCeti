/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Computability.Enumeration.IndexClosure
public import TauCeti.Computability.Hierarchy.One
import TauCeti.Data.PFun.Basic

/-!
# Semantic closure properties for relative Σ⁰₁ sets

Using the uniform index compilers from `TauCeti.Computability.Enumeration.IndexClosure`, this file
establishes semantic closure of relativized c.e. (`Σ⁰₁`) sets on arbitrary primitive-codable
types under ranges, partial images, total images, and partial preimages, together with the
partial-range characterization
`TauCeti.ArithmeticalHierarchy.isSigma_one_iff_exists_recursiveIn_ran`
(which requires no nonemptiness hypothesis, unlike total range presentations).

Ordinary `REPred` closure lemmas and the ordinary partial-range characterization live in
`TauCeti.Computability.RE` and `TauCeti.Computability.Enumeration.Range`.

## Main results

* `RecursiveIn.isSigma_one_mem_ran`, `RecursiveIn.isSigma_one_mem_image`,
  `RecursiveIn.isSigma_one_mem_preimage`, `ComputableIn.isSigma_one_mem_range`,
  `ComputableIn.isSigma_one_mem_image`: semantic closure of `IsSigma Z 1` under ranges, partial
  images, total images, and partial preimages.
* `TauCeti.ArithmeticalHierarchy.isSigma_one_iff_exists_recursiveIn_ran`: partial-range
  characterization of `IsSigma Z 1`.

## References

* R. I. Soare, *Recursively Enumerable Sets and Degrees*, Springer, 1987, Chapters II.1–2 and
  III.1.
-/

public section

open Encodable TauCeti.ArithmeticalHierarchy TauCeti.Oracle.Single

variable {Z : Set ℕ} {α β : Type*} [Primcodable α] [Primcodable β]

namespace RecursiveIn

/-- The range of a partial function recursive in `Z` is Σ⁰₁ relative to `Z`. -/
theorem isSigma_one_mem_ran {f : α →. β} (hf : RecursiveIn {Z.oracle} f) :
    IsSigma Z 1 (· ∈ f.ran) := by
  unfold RecursiveIn at hf
  obtain ⟨c, hc⟩ := Code.exists_code.1 hf
  have hor : Z.oracle = ((Z.indicator 1 : ℕ → ℕ) : ℕ →. ℕ) := funext Z.oracle_apply
  have heq : ∀ y : β, encode y ∈ (Code.eval Z.oracle (Code.rangeDom c)).Dom ↔ y ∈ f.ran := by
    intro y
    rw [hor, Code.dom_eval_rangeDom, ← hor, hc]
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
theorem isSigma_one_mem_image {f : α →. β} {S : Set α} (hf : RecursiveIn {Z.oracle} f)
    (hS : IsSigma Z 1 (· ∈ S)) : IsSigma Z 1 (· ∈ f.image S) := by
  unfold RecursiveIn at hf
  obtain ⟨cf, hcf⟩ := Code.exists_code.1 hf
  obtain ⟨g, hg, hSdom⟩ := hS.exists_recursiveIn_domain
  unfold RecursiveIn at hg
  obtain ⟨cg, hcg⟩ := Code.exists_code.1 hg
  have hor : Z.oracle = ((Z.indicator 1 : ℕ → ℕ) : ℕ →. ℕ) := funext Z.oracle_apply
  have heq : ∀ y : β, encode y ∈ (Code.eval Z.oracle (Code.imageDom cf cg)).Dom ↔
      y ∈ f.image S := by
    intro y
    rw [hor, Code.dom_eval_imageDom, ← hor, PFun.mem_image, PFun.mem_image, hcf, hcg]
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

/-- The preimage of a relative Σ⁰₁ set under a partial function recursive in `Z` is Σ⁰₁ relative
to `Z`. -/
theorem isSigma_one_mem_preimage {f : α →. β} {S : Set β} (hf : RecursiveIn {Z.oracle} f)
    (hS : IsSigma Z 1 (· ∈ S)) : IsSigma Z 1 (· ∈ f.preimage S) := by
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

end RecursiveIn

namespace ComputableIn

/-- The range of a total function computable in `Z` is Σ⁰₁ relative to `Z`. -/
theorem isSigma_one_mem_range {f : α → β} (hf : ComputableIn {Z.oracle} f) :
    IsSigma Z 1 (· ∈ Set.range f) :=
  (RecursiveIn.isSigma_one_mem_ran hf).of_eq fun y => by
    simp [PFun.ran, eq_comm]

/-- The image of a relative Σ⁰₁ set under a total function computable in `Z` is Σ⁰₁ relative to
`Z`. -/
theorem isSigma_one_mem_image {f : α → β} {S : Set α} (hf : ComputableIn {Z.oracle} f)
    (hS : IsSigma Z 1 (· ∈ S)) : IsSigma Z 1 (· ∈ f '' S) := by
  have hf' : RecursiveIn {Z.oracle} (f : α →. β) := hf
  exact (hf'.isSigma_one_mem_image hS).of_eq fun y => by
    simp [PFun.mem_image, PFun.coe_val, eq_comm]

end ComputableIn

namespace TauCeti.ArithmeticalHierarchy

/-- A set in any primitive-codable type is Σ⁰₁ relative to `Z` if and only if it is the range of a
partial function `ℕ →. α` recursive in `Z`. Unlike total range presentations, this holds for the
empty set as well. -/
theorem isSigma_one_iff_exists_recursiveIn_ran {S : Set α} :
    IsSigma Z 1 (· ∈ S) ↔ ∃ f : ℕ →. α, RecursiveIn {Z.oracle} f ∧ f.ran = S := by
  refine ⟨fun hS => ?_, fun ⟨f, hf, hran⟩ => hran ▸ hf.isSigma_one_mem_ran⟩
  obtain ⟨c, hc⟩ := isSigma_one_iff_exists_code.1 hS
  let f : ℕ →. α := fun n =>
    (Part.ofOption (decode (α := α) n)).bind fun x =>
      (Code.eval Z.oracle c (encode x)).map fun _ => x
  have hdec : Nat.RecursiveIn {Z.oracle} fun n =>
      Part.ofOption ((decode (α := α) n).map encode) :=
    (Partrec.nat_iff.1 (Computable.ofOption
      (Computable.decode.option_map (Computable.encode.comp Computable.snd).to₂))).recursiveIn
  have hf : RecursiveIn {Z.oracle} f := by
    unfold RecursiveIn
    refine ((Code.recursiveIn_eval Z.oracle (Code.restrictId c)).comp hdec).of_eq fun n => ?_
    refine Part.ext fun m => ?_
    simp only [f, decode_nat, Part.coe_some, Part.bind_some]
    cases hd : decode (α := α) n with
    | none =>
      simp only [Option.map_none, Part.coe_none, Part.bind_none, Part.map_none]
      exact ⟨fun h => let ⟨_, ha, _⟩ := Part.mem_bind_iff.1 h; (Part.notMem_none _ ha).elim,
        fun h => (Part.notMem_none _ h).elim⟩
    | some x =>
      simp only [Option.map_some, Part.coe_some, Part.bind_some]
      refine ⟨fun h => ?_, fun h => ?_⟩
      · obtain ⟨a, ha, hm⟩ := Part.mem_bind_iff.1 h
        rw [Part.mem_some_iff] at ha; subst ha
        obtain ⟨w, hw, rfl⟩ :=
          (Part.mem_map_iff _).1 (Code.eval_restrictId Z.oracle c (encode x) ▸ hm)
        exact (Part.mem_map_iff encode).2 ⟨x, (Part.mem_map_iff _).2 ⟨w, hw, rfl⟩, rfl⟩
      · obtain ⟨x', hx', rfl⟩ := (Part.mem_map_iff encode).1 h
        obtain ⟨w, hw, rfl⟩ := (Part.mem_map_iff _).1 hx'
        exact Part.mem_bind (Part.mem_some _)
          (Code.eval_restrictId Z.oracle c (encode x) ▸ (Part.mem_map_iff _).2 ⟨w, hw, rfl⟩)
  refine ⟨f, hf, Set.ext fun y => ?_⟩
  simp only [PFun.ran, Set.mem_ofPred_eq, f, Part.mem_bind_iff, Part.mem_ofOption,
    Part.mem_map_iff]
  constructor
  · rintro ⟨n, x, _, w, hw, rfl⟩
    exact (hc x).2 (Part.dom_iff_mem.2 ⟨w, hw⟩)
  · intro hy
    obtain ⟨w, hw⟩ := Part.dom_iff_mem.1 ((hc y).1 hy)
    exact ⟨encode y, y, encodek y, w, hw, rfl⟩

end TauCeti.ArithmeticalHierarchy
