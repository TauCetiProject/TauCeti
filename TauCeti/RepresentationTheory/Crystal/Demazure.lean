/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Crystal.Character
public import TauCeti.RepresentationTheory.Crystal.String

/-!
# Demazure operators on subsets of a normal crystal

Let `c` be a normal crystal over a root datum with a base and `i` a simple root. Kashiwara's
**Demazure operator on subsets** sends a finite set `s` of crystal elements to the set
`𝔇ᵢ s = {fᵢⁿ x : x ∈ s, n ≥ 0}` of all their lowerings (`TauCeti.NormalCrystal.demazureFinset`).
Starting from a highest element and applying these operators along a reduced word of a Weyl group
element `w` gives the Demazure crystal `B_w(λ)` in the crystal of an integrable highest weight
module, and in Littelmann's path model.

This file proves the combinatorial step relating these sets to the integral Demazure operators
`Dᵢ` of `RootPairing.demazureOperator`. Say that `s` has the **string property** for `i`
(`TauCeti.NormalCrystal.IsStringCompatible`) if every `i`-string meets `s` in nothing, in its
head alone, or in the whole string. Then

`char (𝔇ᵢ s) = Dᵢ (char s)`,

where `char t = ∑_{x ∈ t} e^{wt x}` is the character of a finite subset
(`TauCeti.NormalCrystal.character`). The `i`-string through an element
(`TauCeti.NormalCrystal.string`) consists of the lowerings `h, fᵢ h, …, fᵢ^φ h` of its head `h`
(`TauCeti.NormalCrystal.stringHead`),
and since `εᵢ h = 0` its length `φᵢ h` is `⟨wt h, αᵢ^∨⟩`; so its character is the root string
`Dᵢ(e^{wt h})` (`TauCeti.NormalCrystal.character_string`). A string meeting `s` in its head
contributes `Dᵢ(e^{wt h})` to both sides, and a string contained in `s` contributes `Dᵢ` of its own
character, which is again `Dᵢ(e^{wt h})` because `Dᵢ` is idempotent.

Iterating along a word gives the crystal form of the **Demazure character formula**: if each
intermediate set has the string property for the next letter, the character of
`𝔇_{i₁} ⋯ 𝔇_{iᵣ} s` is `D_{i₁} (⋯ (D_{iᵣ} (char s)))`
(`TauCeti.NormalCrystal.character_foldr_demazureFinset`). Whether the sets produced from a highest
element have the string property is a property of the particular crystal (Kashiwara proved it for
crystals of integrable highest weight modules, Littelmann for Lakshmibai–Seshadri paths); it does
not follow from the normal-crystal axioms, and it is a hypothesis here.

## Main definitions

* `TauCeti.NormalCrystal.demazureFinset`: Kashiwara's Demazure operator `𝔇ᵢ` on finite subsets.
* `TauCeti.NormalCrystal.IsStringCompatible`: Kashiwara's string property of a subset.

## Main results

* `TauCeti.NormalCrystal.character_string`: the character of an `i`-string is `Dᵢ` applied to the
  weight of its head.
* `TauCeti.NormalCrystal.isStringCompatible_iff`: the string property says that each `i`-string
  meets the set in nothing, its head, or the whole string.
* `TauCeti.NormalCrystal.character_demazureFinset`: **`char (𝔇ᵢ s) = Dᵢ (char s)` for a set `s`
  with the string property**.
* `TauCeti.NormalCrystal.character_foldr_demazureFinset`: the same along a word.

## References

* M. Kashiwara, *The crystal base and Littelmann's refined Demazure character formula*, Duke
  Math. J. 71 (1993), 839--858.
* P. Littelmann, *Paths and root operators in representation theory*, Ann. of Math. 142 (1995),
  499--525.
* D. Bump and A. Schilling, *Crystal bases: representations and combinatorics*, World Scientific
  (2017), Ch. 13 (Demazure crystals and the string property).
-/

public section

namespace TauCeti.NormalCrystal

open AddMonoidAlgebra

variable {ι X Y B : Type*} [AddCommGroup X] [AddCommGroup Y]
  {P : RootDatum ι X Y} {b : P.Base} (c : NormalCrystal P b B) (i : b.support)

/-! ### Characters of strings -/

section Character

variable {i}

/-- The character of the lowerings of `x` is the root string
`e^{wt x} + e^{wt x - αᵢ} + ⋯ + e^{wt x - φᵢ x • αᵢ}`. -/
theorem character_lowerString (x : B) :
    c.character (c.lowerString i x) =
      ∑ n ∈ Finset.range (c.φ i x + 1), single (c.wt x - n • P.root i) 1 := by
  rw [character_def]
  symm
  refine Finset.sum_bij (fun n hn ↦ (c.fIter i n x).get
      (c.isSome_fIter_iff.mpr (Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)))) ?_ ?_ ?_ ?_
  · exact fun n _ ↦ c.mem_lowerString.mpr ⟨n, (Option.some_get _).symm⟩
  · intro n _ m _ h
    exact c.eq_of_fIter_eq_some_of_fIter_eq_some (i := i) (x := x) (Option.some_get _).symm
      (h.symm ▸ (Option.some_get _).symm)
  · intro y hy
    obtain ⟨n, hn⟩ := c.mem_lowerString.mp hy
    exact ⟨n, Finset.mem_range.mpr (Nat.lt_succ_of_le (c.le_φ_of_fIter_eq_some hn)),
      Option.some_injective _ (by simp [hn])⟩
  · exact fun n _ ↦ by rw [c.wt_of_fIter_eq_some (Option.some_get _).symm]

/-- **The character of an `i`-string is `Dᵢ` applied to the weight of its head**: the string is
`h, fᵢ h, …, fᵢ^m h` with `m = ⟨wt h, αᵢ^∨⟩`, and `Dᵢ(e^{wt h})` is the matching root string. -/
theorem character_string (x : B) :
    c.character (c.string i x) = P.demazureOperator i (single (c.wt (c.stringHead i x)) 1) := by
  rw [P.demazureOperator_single_of_coroot'_eq_natCast i (c.coroot'_wt_stringHead x), string_def,
    character_lowerString]

/-- `Dᵢ` fixes the character of an `i`-string. -/
@[simp]
theorem demazureOperator_character_string (x : B) :
    P.demazureOperator i (c.character (c.string i x)) = c.character (c.string i x) := by
  rw [character_string, RootPairing.demazureOperator_demazureOperator]

end Character

/-! ### Kashiwara's Demazure operator on subsets and the string property -/

section Demazure

variable [DecidableEq B]

/-- **Kashiwara's Demazure operator** `𝔇ᵢ` on finite subsets: `𝔇ᵢ s` is the set of all
lowerings `fᵢⁿ x` of elements `x ∈ s`. -/
noncomputable def demazureFinset (s : Finset B) : Finset B :=
  s.biUnion (c.lowerString i)

variable {i} {s t : Finset B} {y : B}

@[simp]
theorem mem_demazureFinset : y ∈ c.demazureFinset i s ↔ ∃ x ∈ s, ∃ n, c.fIter i n x = some y := by
  simp [demazureFinset]

theorem subset_demazureFinset (s : Finset B) : s ⊆ c.demazureFinset i s := fun x hx ↦
  c.mem_demazureFinset.mpr ⟨x, hx, 0, c.fIter_zero x⟩

theorem demazureFinset_mono (h : s ⊆ t) : c.demazureFinset i s ⊆ c.demazureFinset i t :=
  Finset.biUnion_subset_biUnion_of_subset_left _ h

@[simp]
theorem demazureFinset_empty : c.demazureFinset i ∅ = ∅ := by
  simp [demazureFinset]

@[simp]
theorem demazureFinset_singleton (x : B) : c.demazureFinset i {x} = c.lowerString i x := by
  simp [demazureFinset]

end Demazure

section StringProperty

/-- **Kashiwara's string property** of a set `s` of crystal elements for the simple root `i`: every
element of `s` other than the head of its `i`-string has its whole `i`-string in `s`. Equivalently
(`TauCeti.NormalCrystal.isStringCompatible_iff`), every `i`-string meets `s` in nothing, in its head
alone, or in the whole string. -/
def IsStringCompatible (s : Set B) : Prop :=
  ∀ x ∈ s, c.ε i x ≠ 0 → ∀ y, c.stringHead i y = c.stringHead i x → y ∈ s

variable {c i} {s : Set B} {x : B}

/-- A set with the string property contains the head of the string through each of its
elements. -/
theorem IsStringCompatible.stringHead_mem (hs : c.IsStringCompatible i s) (hx : x ∈ s) :
    c.stringHead i x ∈ s := by
  by_cases h : c.ε i x = 0
  · rwa [c.stringHead_of_ε_eq_zero h]
  · exact hs x hx h _ (c.stringHead_stringHead x)

/-- **The string property, stringwise**: `s` has the string property for `i` exactly when every
`i`-string meets `s` in nothing, in its head alone, or in the whole string. -/
theorem isStringCompatible_iff :
    c.IsStringCompatible i s ↔ ∀ x : B,
      s ∩ c.string i x = ∅ ∨ s ∩ c.string i x = {c.stringHead i x} ∨
        s ∩ c.string i x = c.string i x := by
  simp only [Set.ext_iff, Set.mem_inter_iff, Finset.mem_coe, mem_string, Set.mem_singleton_iff,
    Set.notMem_empty, iff_false, not_and]
  refine ⟨fun hs x ↦ ?_, fun hs x hx hε y hy ↦ ?_⟩
  · by_cases hall : ∃ w ∈ s, c.stringHead i w = c.stringHead i x ∧ c.ε i w ≠ 0
    · -- Some element of `s` on the string is not its head: the whole string lies in `s`.
      obtain ⟨w, hw, hwx, hwε⟩ := hall
      exact .inr (.inr fun y ↦ ⟨fun hy ↦ hy.2, fun hy ↦ ⟨hs w hw hwε y (hy.trans hwx.symm), hy⟩⟩)
    · push Not at hall
      by_cases hne : ∃ z ∈ s, c.stringHead i z = c.stringHead i x
      · -- Every element of `s` on the string is a head, hence the head.
        obtain ⟨z, hz, hzx⟩ := hne
        refine .inr (.inl fun y ↦ ⟨fun hy ↦ ?_, ?_⟩)
        · exact (c.stringHead_of_ε_eq_zero (hall y hy.1 hy.2)).symm.trans hy.2
        · rintro rfl
          exact ⟨hzx ▸ hs.stringHead_mem hz, c.stringHead_stringHead x⟩
      · push Not at hne
        exact .inl hne
  · rcases hs x with h | h | h
    · exact absurd rfl (h x hx)
    · exact absurd (c.stringHead_eq_self_iff.mp ((h x).mp ⟨hx, rfl⟩).symm) hε
    · exact ((h y).mpr hy).1

/-- A singleton consisting of an element without raisings has the string property. -/
theorem isStringCompatible_singleton (h : c.ε i x = 0) : c.IsStringCompatible i {x} := by
  rintro y rfl hy
  exact absurd h hy

/-- A set containing the whole `i`-string through each of its elements has the string property
for `i`. -/
theorem isStringCompatible_of_forall_stringHead_eq (hs : ∀ x ∈ s, ∀ y,
    c.stringHead i y = c.stringHead i x → y ∈ s) : c.IsStringCompatible i s :=
  fun x hx _ ↦ hs x hx

theorem isStringCompatible_univ : c.IsStringCompatible i Set.univ :=
  fun _ _ _ _ _ ↦ Set.mem_univ _

variable [DecidableEq B] {t : Finset B}

/-- `𝔇ᵢ t` is the union of the `i`-strings through elements of `t`, once `t` contains the head of
the string through each of its elements. -/
theorem mem_demazureFinset_iff_of_forall_stringHead_mem
    (ht : ∀ x ∈ t, c.stringHead i x ∈ t) {y : B} :
    y ∈ c.demazureFinset i t ↔ ∃ x ∈ t, c.stringHead i y = c.stringHead i x := by
  refine ⟨fun hy ↦ ?_, fun ⟨x, hx, hyx⟩ ↦ ?_⟩
  · obtain ⟨x, hx, n, hn⟩ := c.mem_demazureFinset.mp hy
    exact ⟨x, hx, c.stringHead_of_fIter_eq_some hn⟩
  · exact c.mem_demazureFinset.mpr ⟨c.stringHead i x, ht x hx, c.ε i y,
      hyx ▸ c.fIter_ε_stringHead y⟩

/-- If `t` contains the head of the string through each of its elements, then `𝔇ᵢ t` consists of
whole `i`-strings, so it has the string property for `i`. -/
theorem isStringCompatible_demazureFinset (ht : ∀ x ∈ t, c.stringHead i x ∈ t) :
    c.IsStringCompatible i (c.demazureFinset i t) := by
  refine isStringCompatible_of_forall_stringHead_eq fun x hx y hyx ↦ ?_
  obtain ⟨z, hz, hxz⟩ := (c.mem_demazureFinset_iff_of_forall_stringHead_mem ht).mp hx
  exact (c.mem_demazureFinset_iff_of_forall_stringHead_mem ht).mpr ⟨z, hz, hyx.trans hxz⟩

/-- In `𝔇ᵢ t`, the elements with a given head `h ∈ t` form the `i`-string of `h`. -/
private theorem filter_demazureFinset_stringHead_eq (ht : ∀ x ∈ t, c.stringHead i x ∈ t)
    {h : B} (hh : h ∈ t) (hε : c.ε i h = 0) :
    (c.demazureFinset i t).filter (c.stringHead i · = h) = c.string i h := by
  ext y
  rw [Finset.mem_filter, c.mem_demazureFinset_iff_of_forall_stringHead_mem ht, c.mem_string,
    c.stringHead_of_ε_eq_zero hε]
  exact ⟨fun h ↦ h.2, fun hy ↦ ⟨⟨h, hh, hy.trans (c.stringHead_of_ε_eq_zero hε).symm⟩, hy⟩⟩

/-- A set with the string property meets the `i`-string of a head `h ∈ t` in `{h}` or in the
whole string. -/
private theorem filter_stringHead_eq (ht : c.IsStringCompatible i (t : Set B)) {h : B}
    (hh : h ∈ t) (hε : c.ε i h = 0) :
    t.filter (c.stringHead i · = h) = {h} ∨ t.filter (c.stringHead i · = h) = c.string i h := by
  have hF : (t.filter (c.stringHead i · = h) : Set B) = (t : Set B) ∩ c.string i h := by
    ext y
    simp [c.stringHead_of_ε_eq_zero hε]
  rcases isStringCompatible_iff.mp ht h with H | H | H
  · exact absurd (H ▸ Set.mem_inter hh (c.self_mem_string h)) (Set.notMem_empty h)
  · rw [c.stringHead_of_ε_eq_zero hε, ← hF, ← Finset.coe_singleton] at H
    exact .inl (Finset.coe_injective H)
  · exact .inr (Finset.coe_injective (hF.trans H))

/-- **The Demazure operator on characters**: for a finite set `t` with the string property for
`i`, the character of `𝔇ᵢ t` is `Dᵢ` applied to the character of `t`. -/
theorem character_demazureFinset (ht : c.IsStringCompatible i (t : Set B)) :
    c.character (c.demazureFinset i t) = P.demazureOperator i (c.character t) := by
  have hhead : ∀ x ∈ t, c.stringHead i x ∈ t := fun x hx ↦ ht.stringHead_mem hx
  -- Split both characters along the heads of the strings meeting `t`.
  have hD : ∀ y ∈ c.demazureFinset i t, c.stringHead i y ∈ t.image (c.stringHead i) := by
    intro y hy
    obtain ⟨x, hx, hyx⟩ := (c.mem_demazureFinset_iff_of_forall_stringHead_mem hhead).mp hy
    exact Finset.mem_image.mpr ⟨x, hx, hyx.symm⟩
  have hS : ∀ x ∈ t, c.stringHead i x ∈ t.image (c.stringHead i) :=
    fun x hx ↦ Finset.mem_image_of_mem _ hx
  rw [character_def, ← Finset.sum_fiberwise_of_maps_to hD, character_def,
    ← Finset.sum_fiberwise_of_maps_to hS, map_sum]
  refine Finset.sum_congr rfl fun h hh ↦ ?_
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hh
  have hε := c.ε_stringHead (i := i) x
  rw [← character_def, ← character_def, c.filter_demazureFinset_stringHead_eq hhead (hhead x hx) hε]
  rcases c.filter_stringHead_eq ht (hhead x hx) hε with hF | hF
  · rw [hF, character_singleton, character_string, stringHead_stringHead]
  · rw [hF, demazureOperator_character_string]

/-- **The Demazure character formula for crystals**: applying the Demazure operators on subsets
along a word `j₁ ⋯ jᵣ` turns the character into `D_{j₁} (⋯ (D_{jᵣ} (char t)))`, i.e. applies the
composite `D_{j₁} ∘ ⋯ ∘ D_{jᵣ}`, provided every intermediate set `𝔇_{j_{k+1}} ⋯ 𝔇_{jᵣ} t` has the
string property for `j_k`. -/
theorem character_foldr_demazureFinset (t : Finset B) (w : List b.support)
    (hw : ∀ u j v, w = u ++ j :: v →
      c.IsStringCompatible j ↑(v.foldr (fun k u ↦ c.demazureFinset k u) t)) :
    c.character (w.foldr (fun k u ↦ c.demazureFinset k u) t) =
      (w.map fun k : b.support ↦ P.demazureOperator k).prod (c.character t) := by
  induction w with
  | nil => simp
  | cons j w ih =>
    rw [List.foldr_cons, c.character_demazureFinset (hw [] j w rfl),
      ih fun u k v h ↦ hw (j :: u) k v (by simp [h]), List.map_cons, List.prod_cons,
      mul_apply_eq_comp]

end StringProperty

end TauCeti.NormalCrystal
