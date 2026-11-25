/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Crystal.Basic

/-!
# Simple-root strings of a normal crystal

Let `c` be a normal crystal over a root datum with a base and `i` a simple root. The `i`-string
through an element `x` is the set of elements reachable from `x` by the root operators `eᵢ` and
`fᵢ`. In a normal crystal it has a unique **head** `eᵢ^{εᵢ x} x`, which admits no raising, and it
consists of the lowerings `h, fᵢ h, …, fᵢ^{φᵢ h} h` of its head `h`. Since `εᵢ h = 0`, the
length `φᵢ h` of the string is the pairing `⟨wt h, αᵢ^∨⟩`.

## Main definitions

* `TauCeti.NormalCrystal.stringHead`: the head `eᵢ^{εᵢ x} x` of the `i`-string through `x`.
* `TauCeti.NormalCrystal.lowerString`: the lowerings `x, fᵢ x, …, fᵢ^{φᵢ x} x` of `x`.
* `TauCeti.NormalCrystal.string`: the `i`-string through `x`.

## Main results

* `TauCeti.NormalCrystal.stringHead_of_eIter_eq_some`,
  `TauCeti.NormalCrystal.stringHead_of_fIter_eq_some`: the root operators preserve the head.
* `TauCeti.NormalCrystal.coroot'_wt_stringHead`: the lowering length of a head is the pairing of
  its weight with the simple coroot.
* `TauCeti.NormalCrystal.mem_string`: two elements lie on the same `i`-string exactly when they
  have the same head.

## References

* D. Bump and A. Schilling, *Crystal bases: representations and combinatorics*, World Scientific
  (2017), Ch. 2.
-/

public section

namespace TauCeti.NormalCrystal

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

@[simp]
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

theorem string_def (x : B) : c.string i x = c.lowerString i (c.stringHead i x) := (rfl)

@[simp]
theorem string_stringHead (x : B) : c.string i (c.stringHead i x) = c.string i x := by
  rw [string_def, string_def, stringHead_stringHead]

@[simp]
theorem mem_lowerString : y ∈ c.lowerString i x ↔ ∃ n, c.fIter i n x = some y := by
  refine ⟨fun h ↦ ?_, fun ⟨n, hn⟩ ↦ ?_⟩
  · obtain ⟨n, -, hn⟩ := (Finset.mem_filterMap _).mp h
    exact ⟨n, hn⟩
  · exact (Finset.mem_filterMap _).mpr
      ⟨n, Finset.mem_range.mpr (Nat.lt_succ_of_le (c.le_φ_of_fIter_eq_some hn)), hn⟩

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

end TauCeti.NormalCrystal
