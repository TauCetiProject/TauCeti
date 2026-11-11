/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.PushoutI

/-!
# Reduced lists of letters in an amalgamated product

Let `φ i : H →* G i` be a family of injective group homomorphisms, with amalgamated product
`Monoid.PushoutI φ`. A list of letters `⟨i, g⟩` with `g : G i` is *reduced* when consecutive
letters lie in different factors and no letter lies in the amalgamated subgroup `φ i H`. This file
states the normal form theorem for amalgamated products in terms of such lists, which is the form
in which it is applied to concrete words.

## Main results

* `Monoid.PushoutI.exists_eq_base_mul_list_prod`: every element is the product of an element of
  the amalgamated subgroup and a reduced list of letters.
* `Monoid.PushoutI.list_prod_notMem_range_base`: the product of a nonempty reduced list of letters
  is not in the amalgamated subgroup.
* `Monoid.PushoutI.list_prod_inv_mul_of_mul_list_prod_notMem_range_base`: the conjugate
  `w⁻¹ * g * w` of a letter `g` outside the amalgamated subgroup by the product `w` of a reduced
  list that does not start in the factor of `g` is not in the amalgamated subgroup.
-/

public section

namespace Monoid.PushoutI

open Function

variable {ι : Type*} {G : ι → Type*} {H : Type*} [∀ i, Group (G i)] [Group H]
  {φ : ∀ i, H →* G i}

/-- The normal form theorem for an amalgamated product of groups: every element is `h * a₁ ⋯ aᵣ`
with `h` in the amalgamated subgroup and letters `aⱼ` taken from the factors, consecutive ones
from different factors and none of them in the amalgamated subgroup. -/
theorem exists_eq_base_mul_list_prod (hφ : ∀ i, Injective (φ i)) (x : PushoutI φ) :
    ∃ (h : H) (L : List (Σ i, G i)), L.IsChain (fun l l' => l.1 ≠ l'.1) ∧
      (∀ l ∈ L, l.2 ∉ (φ l.1).range) ∧ x = base φ h * (L.map fun l => of l.1 l.2).prod := by
  classical
  obtain ⟨d⟩ := NormalWord.transversal_nonempty φ hφ
  set W := NormalWord.equiv (d := d) x
  refine ⟨W.head, W.toList, W.chain_ne, ?_, ?_⟩
  · -- A nonidentity letter of the transversal is not in the amalgamated subgroup.
    rintro ⟨i, g⟩ hl hg
    have h1 := (d.compl i).equiv_fst_eq_self_of_mem_of_one_mem (d.one_mem i) hg
    rw [(d.compl i).equiv_fst_eq_one_of_mem_of_one_mem (one_mem _) (W.normalized i g hl)] at h1
    exact W.ne_one _ hl (congrArg Subtype.val h1).symm
  · have hW : W.prod = x := NormalWord.equiv.symm_apply_apply x
    conv_lhs => rw [← hW]
    rw [NormalWord.prod, CoprodI.Word.prod, map_list_prod, List.map_map]
    simp [Function.comp_def]

/-- In an amalgamated product of groups, the product of a nonempty list of letters, consecutive
ones from different factors and none of them in the amalgamated subgroup, is not in the
amalgamated subgroup. -/
theorem list_prod_notMem_range_base (hφ : ∀ i, Injective (φ i)) {L : List (Σ i, G i)}
    (hL : L ≠ []) (hc : L.IsChain fun l l' => l.1 ≠ l'.1) (hred : ∀ l ∈ L, l.2 ∉ (φ l.1).range) :
    (L.map fun l => of l.1 l.2).prod ∉ (base φ).range := by
  intro h
  let w : CoprodI.Word G :=
    ⟨L, fun l hl h1 => hred l hl ⟨1, by rw [map_one, h1]⟩, hc⟩
  have hw : ofCoprodI w.prod = (L.map fun l => of (φ := φ) l.1 l.2).prod := by
    rw [CoprodI.Word.prod, map_list_prod, List.map_map]
    simp [Function.comp_def, w]
  exact hL (congrArg CoprodI.Word.toList
    (Reduced.eq_empty_of_mem_range hφ (w := w) hred (hw ▸ h)))

/-- In an amalgamated product of groups, let `w` be the product of a list of letters, consecutive
ones from different factors and none of them in the amalgamated subgroup, and let `g` be a letter
outside the amalgamated subgroup whose factor is not that of the first letter of the list. Then
the conjugate `w⁻¹ * g * w` is not in the amalgamated subgroup. -/
theorem list_prod_inv_mul_of_mul_list_prod_notMem_range_base (hφ : ∀ i, Injective (φ i))
    {L : List (Σ i, G i)} (hc : L.IsChain fun l l' => l.1 ≠ l'.1)
    (hred : ∀ l ∈ L, l.2 ∉ (φ l.1).range) {i : ι} {g : G i} (hg : g ∉ (φ i).range)
    (hi : ∀ l ∈ L.head?, l.1 ≠ i) :
    (L.map fun l => of l.1 l.2).prod⁻¹ * of i g * (L.map fun l => of l.1 l.2).prod ∉
      (base φ).range := by
  have hprod : (((L.map fun l => (⟨l.1, l.2⁻¹⟩ : Σ i, G i)).reverse ++ ⟨i, g⟩ :: L).map
      fun l => of (φ := φ) l.1 l.2).prod =
      (L.map fun l => of l.1 l.2).prod⁻¹ * of i g * (L.map fun l => of l.1 l.2).prod := by
    rw [List.prod_inv_reverse]
    simp [Function.comp_def, mul_assoc]
  rw [← hprod]
  refine list_prod_notMem_range_base hφ (by simp) ?_ ?_
  · refine List.isChain_append.2 ⟨?_, List.isChain_cons.2 ⟨fun l hl => (hi l hl).symm, hc⟩, ?_⟩
    · rw [List.isChain_reverse, List.isChain_map]
      exact hc.imp fun _ _ h => h.symm
    · intro l hl l' hl'
      obtain rfl : l' = ⟨i, g⟩ := by simpa using hl'.symm
      rw [List.getLast?_reverse, List.head?_map] at hl
      obtain ⟨l₀, hl₀, rfl⟩ := Option.mem_map.1 hl
      exact hi l₀ hl₀
  · intro l hl
    rcases List.mem_append.1 hl with hl | hl
    · obtain ⟨l₀, hl₀, rfl⟩ := List.mem_map.1 (List.mem_reverse.1 hl)
      exact fun h => hred l₀ hl₀ (by simpa using inv_mem h)
    · rcases List.mem_cons.1 hl with rfl | hl
      exacts [hg, hred l hl]

end Monoid.PushoutI
