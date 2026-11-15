/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Crystal.Character
public import TauCeti.LinearAlgebra.RootSystem.Weyl.Demazure.Basic

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
`𝔇_{i₁} ⋯ 𝔇_{iᵣ} s` is `D_{i₁} ⋯ D_{iᵣ} (char s)`
(`TauCeti.NormalCrystal.character_foldr_demazureFinset`). Whether the sets produced from a highest
element have the string property is a property of the particular crystal (Kashiwara proved it for
crystals of integrable highest weight modules, Littelmann for Lakshmibai–Seshadri paths); it does
not follow from the normal-crystal axioms, and it is a hypothesis here.

## Main definitions

* `TauCeti.NormalCrystal.stringHead`: the head `eᵢ^{εᵢ x} x` of the `i`-string through `x`.
* `TauCeti.NormalCrystal.lowerString`: the lowerings `x, fᵢ x, …, fᵢ^{φᵢ x} x` of `x`.
* `TauCeti.NormalCrystal.string`: the `i`-string through `x`.
* `TauCeti.NormalCrystal.character`: the character of a finite set of crystal elements.
* `TauCeti.NormalCrystal.demazureFinset`: Kashiwara's Demazure operator `𝔇ᵢ` on finite subsets.
* `TauCeti.NormalCrystal.IsStringCompatible`: Kashiwara's string property of a subset.

## Main results

* `TauCeti.NormalCrystal.mem_string`: two elements lie on the same `i`-string exactly when they
  have the same head.
* `TauCeti.NormalCrystal.character_string`: the character of an `i`-string is `Dᵢ` applied to the
  weight of its head.
* `TauCeti.NormalCrystal.isStringCompatible_iff`: the string property says that each `i`-string
  meets the set in nothing, its head, or the whole string.
* `TauCeti.NormalCrystal.character_demazureFinset`: **`char (𝔇ᵢ s) = Dᵢ (char s)` for a set `s`
  with the string property**.
* `TauCeti.NormalCrystal.character_foldr_demazureFinset`: the same along a word.
* `TauCeti.NormalCrystal.demazureOperator_formalCharacter`: `Dᵢ` fixes the character of a finite
  normal crystal, over any root datum.

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

/-! ### Heads of strings -/

section Head

/-- The **head** `eᵢ^{εᵢ x} x` of the `i`-string through `x`: the element of the string from
which no further raising is possible. -/
noncomputable def stringHead (x : B) : B :=
  (c.eIter i (c.ε i x) x).get (c.isSome_eIter_iff.mpr le_rfl)

variable {i} {x y : B} {n : ℕ}

theorem eIter_ε_eq_some_stringHead (x : B) : c.eIter i (c.ε i x) x = some (c.stringHead i x) :=
  (Option.some_get _).symm

theorem fIter_ε_stringHead (x : B) : c.fIter i (c.ε i x) (c.stringHead i x) = some x :=
  c.fIter_eq_some_iff.mpr (c.eIter_ε_eq_some_stringHead x)

/-- The head of a string admits no raising. -/
@[simp]
theorem ε_stringHead (x : B) : c.ε i (c.stringHead i x) = 0 := by
  simpa using c.ε_of_eIter_eq_some (c.eIter_ε_eq_some_stringHead (i := i) x)

@[simp]
theorem e_stringHead (x : B) : c.e i (c.stringHead i x) = none :=
  c.ε_eq_zero_iff.mp (c.ε_stringHead x)

/-- The weight of the head of the string through `x` is `wt x + εᵢ x • αᵢ`. -/
theorem wt_stringHead (x : B) : c.wt (c.stringHead i x) = c.wt x + c.ε i x • P.root i :=
  c.wt_of_eIter_eq_some (c.eIter_ε_eq_some_stringHead x)

/-- The string through `x` has length `φᵢ x + εᵢ x`, the lowering length of its head. -/
theorem φ_stringHead (x : B) : c.φ i (c.stringHead i x) = c.φ i x + c.ε i x :=
  c.φ_of_eIter_eq_some (c.eIter_ε_eq_some_stringHead x)

/-- Since the head admits no raising, its lowering length is the pairing of its weight with the
simple coroot. -/
theorem coroot'_wt_stringHead (x : B) :
    P.coroot' i (c.wt (c.stringHead i x)) = c.φ i (c.stringHead i x) := by
  have h := c.φ_sub_ε i (c.stringHead i x)
  rw [c.ε_stringHead, Nat.cast_zero, sub_zero] at h
  simpa [RootPairing.coroot'] using h.symm

theorem stringHead_eq_self_iff : c.stringHead i x = x ↔ c.ε i x = 0 := by
  refine ⟨fun h ↦ h ▸ c.ε_stringHead x, fun h ↦ ?_⟩
  simpa [h] using (c.eIter_ε_eq_some_stringHead (i := i) x).symm

theorem stringHead_of_ε_eq_zero (h : c.ε i x = 0) : c.stringHead i x = x :=
  c.stringHead_eq_self_iff.mpr h

@[simp]
theorem stringHead_stringHead (x : B) : c.stringHead i (c.stringHead i x) = c.stringHead i x :=
  c.stringHead_of_ε_eq_zero (c.ε_stringHead x)

/-- Raising does not change the head of the string. -/
theorem stringHead_of_e_eq_some (h : c.e i x = some y) : c.stringHead i y = c.stringHead i x := by
  have hx := c.eIter_ε_eq_some_stringHead (i := i) x
  rw [← c.ε_of_e_eq_some h, eIter_succ, h, Option.bind_some] at hx
  exact Option.some_injective _ ((c.eIter_ε_eq_some_stringHead y).symm.trans hx)

/-- Iterated raising does not change the head of the string. -/
theorem stringHead_of_eIter_eq_some (h : c.eIter i n x = some y) :
    c.stringHead i y = c.stringHead i x := by
  induction n generalizing x with
  | zero => rw [Option.some_injective _ ((c.eIter_zero x).symm.trans h)]
  | succ n ih =>
    rw [eIter_succ, Option.bind_eq_some_iff] at h
    obtain ⟨z, hz, h⟩ := h
    exact (ih h).trans (c.stringHead_of_e_eq_some hz)

/-- Lowering does not change the head of the string. -/
theorem stringHead_of_f_eq_some (h : c.f i x = some y) : c.stringHead i y = c.stringHead i x :=
  (c.stringHead_of_e_eq_some (c.f_eq_some_iff.mp h)).symm

/-- Iterated lowering does not change the head of the string. -/
theorem stringHead_of_fIter_eq_some (h : c.fIter i n x = some y) :
    c.stringHead i y = c.stringHead i x :=
  (c.stringHead_of_eIter_eq_some (c.fIter_eq_some_iff.mp h)).symm

/-- The lowerings of a head are exactly the elements having it as their head. -/
theorem exists_fIter_eq_some_iff_stringHead_eq (h : c.ε i x = 0) :
    (∃ n, c.fIter i n x = some y) ↔ c.stringHead i y = x := by
  refine ⟨fun ⟨n, hn⟩ ↦ (c.stringHead_of_fIter_eq_some hn).trans (c.stringHead_of_ε_eq_zero h),
    fun hy ↦ ⟨c.ε i y, hy ▸ c.fIter_ε_stringHead y⟩⟩

/-- Distinct numbers of lowering steps from the same element give distinct results. -/
theorem eq_of_fIter_eq_some_of_fIter_eq_some {m : ℕ} (hn : c.fIter i n x = some y)
    (hm : c.fIter i m x = some y) : n = m := by
  have h₁ := c.ε_of_fIter_eq_some hn
  have h₂ := c.ε_of_fIter_eq_some hm
  omega

end Head

/-! ### Strings -/

section String

/-- The finite set `{x, fᵢ x, …, fᵢ^{φᵢ x} x}` of the lowerings of `x`. -/
noncomputable def lowerString (x : B) : Finset B :=
  (Finset.range (c.φ i x + 1)).filterMap (fun n ↦ c.fIter i n x)
    fun _ _ _ hn hm ↦ c.eq_of_fIter_eq_some_of_fIter_eq_some hn hm

/-- The **`i`-string** through `x`: the lowerings of its head. -/
noncomputable def string (x : B) : Finset B :=
  c.lowerString i (c.stringHead i x)

variable {i} {x y : B}

@[simp]
theorem mem_lowerString : y ∈ c.lowerString i x ↔ ∃ n, c.fIter i n x = some y := by
  refine ⟨fun h ↦ ?_, fun ⟨n, hn⟩ ↦ ?_⟩
  · obtain ⟨n, -, hn⟩ := (Finset.mem_filterMap _).mp h
    exact ⟨n, hn⟩
  · have hle : n ≤ c.φ i x := c.isSome_fIter_iff.mp (by simp [hn])
    exact (Finset.mem_filterMap _).mpr ⟨n, Finset.mem_range.mpr (Nat.lt_succ_of_le hle), hn⟩

theorem self_mem_lowerString (x : B) : x ∈ c.lowerString i x :=
  c.mem_lowerString.mpr ⟨0, c.fIter_zero x⟩

/-- **Two elements lie on the same `i`-string exactly when they have the same head.** -/
@[simp]
theorem mem_string : y ∈ c.string i x ↔ c.stringHead i y = c.stringHead i x := by
  rw [string, mem_lowerString, c.exists_fIter_eq_some_iff_stringHead_eq (c.ε_stringHead x)]

theorem self_mem_string (x : B) : x ∈ c.string i x :=
  c.mem_string.mpr rfl

theorem string_eq_lowerString_of_ε_eq_zero (h : c.ε i x = 0) :
    c.string i x = c.lowerString i x := by
  rw [string, c.stringHead_of_ε_eq_zero h]

theorem lowerString_subset_string (x : B) : c.lowerString i x ⊆ c.string i x := fun _ hy ↦ by
  obtain ⟨n, hn⟩ := c.mem_lowerString.mp hy
  exact c.mem_string.mpr (c.stringHead_of_fIter_eq_some hn)

end String

/-! ### Characters of finite subsets -/

section Character

/-- The **character** `∑_{x ∈ s} e^{wt x}` of a finite set of crystal elements, in the integral
group algebra of the weight lattice. -/
noncomputable def character (s : Finset B) : AddMonoidAlgebra ℤ X :=
  ∑ x ∈ s, single (c.wt x) 1

theorem character_def (s : Finset B) : c.character s = ∑ x ∈ s, single (c.wt x) 1 := (rfl)

@[simp]
theorem character_empty : c.character ∅ = 0 := by
  simp [character_def]

@[simp]
theorem character_singleton (x : B) : c.character {x} = single (c.wt x) 1 := by
  simp [character_def]

theorem character_union [DecidableEq B] {s t : Finset B} (h : Disjoint s t) :
    c.character (s ∪ t) = c.character s + c.character t :=
  Finset.sum_union h

/-- The formal character of a finite crystal is the character of the whole crystal. -/
theorem formalCharacter_eq_character_univ [Fintype B] :
    c.formalCharacter = c.character Finset.univ := by
  rw [formalCharacter_def, character_def]

variable {i}

/-- The character of the lowerings of `x` is the root string
`e^{wt x} + e^{wt x - αᵢ} + ⋯ + e^{wt x - φᵢ x • αᵢ}`. -/
theorem character_lowerString (x : B) :
    c.character (c.lowerString i x) =
      ∑ n ∈ Finset.range (c.φ i x + 1), single (c.wt x - n • P.root i) 1 := by
  symm
  refine Finset.sum_bij (fun n hn ↦ (c.fIter i n x).get
      (c.isSome_fIter_iff.mpr (Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)))) ?_ ?_ ?_ ?_
  · exact fun n _ ↦ c.mem_lowerString.mpr ⟨n, (Option.some_get _).symm⟩
  · intro n _ m _ h
    exact c.eq_of_fIter_eq_some_of_fIter_eq_some (i := i) (x := x) (Option.some_get _).symm
      (h.symm ▸ (Option.some_get _).symm)
  · intro y hy
    obtain ⟨n, hn⟩ := c.mem_lowerString.mp hy
    have hle : n ≤ c.φ i x := c.isSome_fIter_iff.mp (by simp [hn])
    exact ⟨n, Finset.mem_range.mpr (Nat.lt_succ_of_le hle), Option.some_injective _ (by simp [hn])⟩
  · exact fun n _ ↦ by rw [c.wt_of_fIter_eq_some (Option.some_get _).symm]

/-- **The character of an `i`-string is `Dᵢ` applied to the weight of its head**: the string is
`h, fᵢ h, …, fᵢ^m h` with `m = ⟨wt h, αᵢ^∨⟩`, and `Dᵢ(e^{wt h})` is the matching root string. -/
theorem character_string (x : B) :
    c.character (c.string i x) = P.demazureOperator i (single (c.wt (c.stringHead i x)) 1) := by
  rw [P.demazureOperator_single_of_coroot'_eq_natCast i (c.coroot'_wt_stringHead x), string,
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
  by_cases hall : ∃ w ∈ t, c.stringHead i w = h ∧ c.ε i w ≠ 0
  · obtain ⟨w, hw, hwh, hwε⟩ := hall
    refine .inr (Finset.ext fun y ↦ ?_)
    rw [Finset.mem_filter, c.mem_string, c.stringHead_of_ε_eq_zero hε]
    exact ⟨fun hy ↦ hy.2, fun hy ↦ ⟨ht w hw hwε y (hy.trans hwh.symm), hy⟩⟩
  · push Not at hall
    refine .inl (Finset.ext fun y ↦ ?_)
    rw [Finset.mem_filter, Finset.mem_singleton]
    refine ⟨fun hy ↦ (c.stringHead_of_ε_eq_zero (hall y hy.1 hy.2)).symm.trans hy.2, ?_⟩
    rintro rfl
    exact ⟨hh, c.stringHead_of_ε_eq_zero hε⟩

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
along a word `j₁ ⋯ jᵣ` multiplies the character by `D_{j₁} ⋯ D_{jᵣ}`, provided every intermediate
set `𝔇_{j_{k+1}} ⋯ 𝔇_{jᵣ} t` has the string property for `j_k`. -/
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

omit [DecidableEq B] in
/-- **`Dᵢ` fixes the character of a finite normal crystal**, over any root datum: the whole
crystal is a union of `i`-strings. -/
@[simp]
theorem demazureOperator_formalCharacter [Fintype B] :
    P.demazureOperator i c.formalCharacter = c.formalCharacter := by
  classical
  have hu : c.IsStringCompatible i (Finset.univ : Finset B) := by
    rw [Finset.coe_univ]
    exact isStringCompatible_univ
  rw [formalCharacter_eq_character_univ, ← c.character_demazureFinset hu,
    Finset.eq_univ_of_forall fun x ↦ c.subset_demazureFinset _ (Finset.mem_univ x)]

end StringProperty

end TauCeti.NormalCrystal
