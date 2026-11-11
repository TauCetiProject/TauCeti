/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.DFinsupp.Module

/-!
# Extending dependent finitely supported functions by zero

For a decidable predicate `p` on the index type, `DFinsupp.extendDomain` extends a dependent
finitely supported function on `Subtype p` by zero to all indices. It is the dependent analogue
of Mathlib's `Finsupp.extendDomain`, and a one-sided inverse of `DFinsupp.subtypeDomain`:
restricting an extension recovers the function, and extending a restriction recovers every
function that vanishes off `p`. `DFinsupp.extendDomainLinearMap` is the extension as a linear map.
-/

public section

namespace DFinsupp

variable {γ ι : Type*} {β : ι → Type*} {p : ι → Prop} [DecidablePred p]

section Zero

variable [∀ i, Zero (β i)]

/-- The extension by zero of a dependent finitely supported function on `Subtype p`. -/
def extendDomain (f : Π₀ i : Subtype p, β i) : Π₀ i, β i where
  toFun i := if h : p i then f ⟨i, h⟩ else 0
  support' := f.support'.map fun s ↦ ⟨s.1.map Subtype.val, fun i ↦ by
    by_cases h : p i
    · exact (s.2 ⟨i, h⟩).imp (Multiset.mem_map_of_mem _) (by simp [h])
    · exact Or.inr (by simp [h])⟩

/-- The extension by zero is `f` on indices satisfying `p` and zero elsewhere. -/
theorem extendDomain_apply (f : Π₀ i : Subtype p, β i) (i : ι) :
    f.extendDomain i = if h : p i then f ⟨i, h⟩ else 0 := (rfl)

/-- On indices satisfying `p`, the extension by zero agrees with the function. -/
@[simp]
theorem extendDomain_apply_subtype (f : Π₀ i : Subtype p, β i) (i : Subtype p) :
    f.extendDomain i = f i := by
  simp [extendDomain_apply, i.2]

/-- Off `p`, the extension by zero vanishes. -/
@[simp]
theorem extendDomain_apply_of_not (f : Π₀ i : Subtype p, β i) {i : ι} (hi : ¬p i) :
    f.extendDomain i = 0 := by
  simp [extendDomain_apply, hi]

/-- Restricting the extension by zero recovers the function. -/
@[simp]
theorem subtypeDomain_extendDomain (f : Π₀ i : Subtype p, β i) :
    f.extendDomain.subtypeDomain p = f := by
  ext i
  simp

/-- A function vanishing off `p` is the extension by zero of its restriction to `p`. -/
theorem extendDomain_subtypeDomain {f : Π₀ i, β i} (hf : ∀ i, ¬p i → f i = 0) :
    (f.subtypeDomain p).extendDomain = f := by
  ext i
  by_cases h : p i
  · simp [extendDomain_apply, h]
  · rw [extendDomain_apply_of_not _ h, hf i h]

/-- The extension by zero of the zero function is zero. -/
@[simp]
theorem extendDomain_zero : (0 : Π₀ i : Subtype p, β i).extendDomain = 0 := by
  ext i
  simp [extendDomain_apply]

/-- The extension by zero of a single function is a single function. -/
@[simp]
theorem extendDomain_single [DecidableEq ι] (i : Subtype p) (x : β i) :
    (single i x).extendDomain = single i.1 x := by
  ext j
  by_cases h : p j
  · rcases eq_or_ne j i.1 with rfl | hj
    · simp [extendDomain_apply, h]
    · simp only [extendDomain_apply, h, ↓reduceDIte]
      rw [single_eq_of_ne hj, single_eq_of_ne fun h' ↦ hj (congrArg Subtype.val h')]
  · rw [extendDomain_apply_of_not _ h, single_eq_of_ne fun h' ↦ h (by rw [h']; exact i.2)]

end Zero

/-- The extension by zero commutes with addition. -/
@[simp]
theorem extendDomain_add [∀ i, AddZeroClass (β i)] (f g : Π₀ i : Subtype p, β i) :
    extendDomain (β := β) (f + g) = extendDomain (β := β) f + extendDomain (β := β) g := by
  ext i
  by_cases h : p i <;> simp [extendDomain_apply, h]

/-- The extension by zero commutes with scalar multiplication. -/
@[simp]
theorem extendDomain_smul [∀ i, Zero (β i)] [∀ i, SMulZeroClass γ (β i)] (c : γ)
    (f : Π₀ i : Subtype p, β i) :
    extendDomain (β := β) (c • f) = c • extendDomain (β := β) f := by
  ext i
  by_cases h : p i <;> simp [extendDomain_apply, h]

variable (γ β p) in
/-- The extension by zero as a linear map. -/
def extendDomainLinearMap [Semiring γ] [∀ i, AddCommMonoid (β i)] [∀ i, Module γ (β i)] :
    (Π₀ i : Subtype p, β i) →ₗ[γ] Π₀ i, β i where
  toFun f := extendDomain (β := β) f
  map_add' f g := extendDomain_add f g
  map_smul' c f := extendDomain_smul (β := β) c f

/-- The linear extension by zero is `DFinsupp.extendDomain`. -/
@[simp]
theorem extendDomainLinearMap_apply [Semiring γ] [∀ i, AddCommMonoid (β i)]
    [∀ i, Module γ (β i)] (f : Π₀ i : Subtype p, β i) :
    extendDomainLinearMap γ β p f = extendDomain (β := β) f := (rfl)

end DFinsupp
