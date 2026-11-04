/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.FreeGroup.Reduce

/-!
# Normal syllable lists for free groups

A syllable list `[(x₁, e₁), …, (x_k, e_k)]` represents the free group element
`syllableProd s = x₁ ^ e₁ ⋯ x_k ^ e_k`; it is `IsSyllableNormal` when every exponent is nonzero
and consecutive generators are distinct. `exists_isSyllableNormal` writes any free group element
as the product of a normal syllable list.
-/

public section

namespace FreeGroup

variable {X : Type*}

section Syllables

/-- The product `x₁ ^ e₁ ⋯ x_k ^ e_k` of a list of syllables. -/
def syllableProd (s : List (X × ℤ)) : FreeGroup X :=
  (s.map fun a ↦ of a.1 ^ a.2).prod

/-- The empty syllable list represents the identity. -/
@[simp]
theorem syllableProd_nil : syllableProd ([] : List (X × ℤ)) = 1 := by
  simp [syllableProd]

/-- The product of a nonempty syllable list factors at its head. -/
@[simp]
theorem syllableProd_cons (a : X × ℤ) (s : List (X × ℤ)) :
    syllableProd (a :: s) = of a.1 ^ a.2 * syllableProd s := by
  simp [syllableProd]

/-- A syllable list is normal when its exponents are nonzero and consecutive generators are
distinct. -/
def IsSyllableNormal (s : List (X × ℤ)) : Prop :=
  (∀ a ∈ s, a.2 ≠ 0) ∧ s.IsChain fun a b ↦ a.1 ≠ b.1

/-- A syllable list is normal iff its exponents are nonzero and consecutive generators are
distinct. -/
theorem isSyllableNormal_iff {s : List (X × ℤ)} :
    IsSyllableNormal s ↔ (∀ a ∈ s, a.2 ≠ 0) ∧ s.IsChain fun a b ↦ a.1 ≠ b.1 :=
  Iff.rfl

/-- Left-multiplying the product of a normal syllable list by a generator power gives the
product of another normal syllable list. -/
private theorem exists_isSyllableNormal_zpow_mul (x : X) (e : ℤ) (s : List (X × ℤ))
    (hs : IsSyllableNormal s) :
    ∃ t, IsSyllableNormal t ∧ syllableProd t = of x ^ e * syllableProd s := by
  obtain ⟨hs0, hsc⟩ := hs
  rcases eq_or_ne e 0 with rfl | he
  · exact ⟨s, ⟨hs0, hsc⟩, by simp⟩
  match s, hs0, hsc with
  | [], _, _ => exact ⟨[(x, e)], ⟨by simpa, .singleton _⟩, by simp⟩
  | (y, f) :: s', hs0, hsc =>
    by_cases hyx : y = x
    · subst hyx
      have hs' : IsSyllableNormal s' := ⟨fun a ha ↦ hs0 a (.tail _ ha), hsc.tail⟩
      by_cases hf : e + f = 0
      · exact ⟨s', hs', by simp [← mul_assoc, ← zpow_add, hf]⟩
      · refine ⟨(y, e + f) :: s', ⟨by simpa [hf] using hs'.1, ?_⟩, by simp [mul_assoc, zpow_add]⟩
        exact List.isChain_cons.2 ⟨(List.isChain_cons.1 hsc).1, hsc.tail⟩
    · exact ⟨(x, e) :: (y, f) :: s', ⟨by simpa [he] using hs0, .cons_cons (Ne.symm hyx) hsc⟩,
        by simp⟩

/-- Every element of a free group is the product of a normal syllable list. -/
theorem exists_isSyllableNormal (w : FreeGroup X) :
    ∃ s, IsSyllableNormal s ∧ syllableProd s = w := by
  suffices h : ∀ s, IsSyllableNormal s →
      ∃ t, IsSyllableNormal t ∧ syllableProd t = w * syllableProd s by
    simpa using h [] ⟨by simp, .nil⟩
  induction w with
  | one => exact fun s hs ↦ ⟨s, hs, (one_mul _).symm⟩
  | of x => simpa using exists_isSyllableNormal_zpow_mul x 1
  | inv_of x _ => simpa using exists_isSyllableNormal_zpow_mul x (-1)
  | mul u v hu hv =>
    intro s hs
    obtain ⟨t, ht, htv⟩ := hv s hs
    obtain ⟨r, hr, hru⟩ := hu t ht
    exact ⟨r, hr, by rw [hru, htv, mul_assoc]⟩

end Syllables

end FreeGroup
