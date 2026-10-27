/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Homotopy.Equiv

/-!
# Deformation retractions

Two successive strong deformation retractions compose: first deform onto the intermediate
space, then run its deformation after the first retraction. The resulting homotopy fixes
the image of the final inclusion throughout. Inclusions are expressed as continuous maps,
so the result also applies to subspaces represented by different but homeomorphic types.

A deformation retraction in the weak sense of `B` onto `A ⊆ B` is a deformation of `B` within
itself, starting at the identity, ending inside `A`, and keeping `A` inside `A` at all times. The
inclusion of `A` is then a homotopy equivalence
(`ContinuousMap.HomotopyEquiv.ofWeakDeformationRetraction`). Unlike a strong deformation
retraction, the deformation need not fix `A`, which allows straight-line deformations that slide
points of `A` within `A`.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Chapter 0, Exercise 4
  (deformation retractions in the weak sense).
-/

public section

open Set Function

namespace ContinuousMap.HomotopicRel

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/-- Compose the relative homotopies of two strong deformation retractions. The first
retraction must be a left inverse of its inclusion; no separation or closedness is needed. -/
theorem comp_retractions {i : C(Y, X)} {j : C(Z, Y)} {r : C(X, Y)} {s : C(Y, Z)}
    (hX : (ContinuousMap.id X).HomotopicRel (i.comp r) (range i))
    (hY : (ContinuousMap.id Y).HomotopicRel (j.comp s) (range j))
    (hr : LeftInverse r i) :
    (ContinuousMap.id X).HomotopicRel ((i.comp j).comp (s.comp r)) (range (i.comp j)) := by
  obtain ⟨H⟩ := hX
  obtain ⟨G⟩ := hY
  let H' : (ContinuousMap.id X).HomotopyRel (i.comp r) (range (i.comp j)) :=
    { H with prop' := fun t x hx => H.eq_fst t (by
        obtain ⟨z, rfl⟩ := hx
        exact mem_range_self (j z)) }
  let G' : (i.comp r).HomotopyRel ((i.comp j).comp (s.comp r))
      (range (i.comp j)) :=
    { toFun := fun p => i (G (p.1, r p.2))
      continuous_toFun := i.continuous.comp
        (G.continuous.comp (continuous_fst.prodMk (r.continuous.comp continuous_snd)))
      map_zero_left := fun x => by simp
      map_one_left := fun x => by simp
      prop' := by
        rintro t x ⟨z, rfl⟩
        simpa only [ContinuousMap.coe_mk, ContinuousMap.comp_apply, hr (j z),
          ContinuousMap.id_apply] using congrArg i (G.eq_fst t (mem_range_self z)) }
  exact ⟨H'.trans G'⟩

end ContinuousMap.HomotopicRel

namespace ContinuousMap.HomotopyEquiv

open scoped unitInterval

variable {X : Type*} [TopologicalSpace X] {A B : Set X}

/-- **The inclusion of a weak deformation retract is a homotopy equivalence.** Let `A ⊆ B`, and
let `H : I × B → X` be a deformation of `B` within `B` which starts at the identity, ends inside
`A`, and keeps `A` inside `A` at all times. Then the inclusion `A → B` is a homotopy equivalence,
whose homotopy inverse is the end map of `H`. -/
def ofWeakDeformationRetraction (hAB : A ⊆ B) (H : I × B → X) (hH : Continuous H)
    (hHB : ∀ p, H p ∈ B) (h₀ : ∀ x, H (0, x) = x) (h₁ : ∀ x, H (1, x) ∈ A)
    (hHA : ∀ t (x : B), (x : X) ∈ A → H (t, x) ∈ A) : A ≃ₕ B where
  toFun := ContinuousMap.inclusion hAB
  invFun := ⟨fun x ↦ ⟨H (1, x), h₁ x⟩, by fun_prop⟩
  left_inv := ⟨ContinuousMap.Homotopy.symm
    { toFun := fun p ↦ ⟨H (p.1, ContinuousMap.inclusion hAB p.2), hHA p.1 _ p.2.2⟩
      continuous_toFun := by fun_prop
      map_zero_left := fun a ↦ Subtype.ext (h₀ _)
      map_one_left := fun _ ↦ rfl }⟩
  right_inv := ⟨ContinuousMap.Homotopy.symm
    { toFun := fun p ↦ ⟨H p, hHB p⟩
      continuous_toFun := by fun_prop
      map_zero_left := fun x ↦ Subtype.ext (h₀ x)
      map_one_left := fun _ ↦ rfl }⟩

/-- The homotopy equivalence `ContinuousMap.HomotopyEquiv.ofWeakDeformationRetraction` is the
inclusion. -/
@[simp]
theorem coe_ofWeakDeformationRetraction_apply (hAB : A ⊆ B) (H : I × B → X) (hH : Continuous H)
    (hHB : ∀ p, H p ∈ B) (h₀ : ∀ x, H (0, x) = x) (h₁ : ∀ x, H (1, x) ∈ A)
    (hHA : ∀ t (x : B), (x : X) ∈ A → H (t, x) ∈ A) (a : A) :
    (ofWeakDeformationRetraction hAB H hH hHB h₀ h₁ hHA a : X) = a :=
  (rfl)

/-- The homotopy inverse of `ContinuousMap.HomotopyEquiv.ofWeakDeformationRetraction` is the end
map of the deformation. -/
@[simp]
theorem coe_ofWeakDeformationRetraction_symm_apply (hAB : A ⊆ B) (H : I × B → X)
    (hH : Continuous H) (hHB : ∀ p, H p ∈ B) (h₀ : ∀ x, H (0, x) = x) (h₁ : ∀ x, H (1, x) ∈ A)
    (hHA : ∀ t (x : B), (x : X) ∈ A → H (t, x) ∈ A) (x : B) :
    ((ofWeakDeformationRetraction hAB H hH hHB h₀ h₁ hHA).symm x : X) = H (1, x) :=
  (rfl)

end ContinuousMap.HomotopyEquiv
