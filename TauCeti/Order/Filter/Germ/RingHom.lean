/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.Filter.Germ.Basic

/-!
# Ring homomorphisms on germs

A ring homomorphism acts on germs by postcomposition. This allows polynomial relations to
be transported between real-valued and complex-valued germs along the same filter.
-/

public section

namespace RingHom

variable {α R S : Type*} [Semiring R] [Semiring S]

/-- Postcomposition by a ring homomorphism, as a ring homomorphism on germs. -/
def mapGerm (f : R →+* S) (l : Filter α) : Filter.Germ l R →+* Filter.Germ l S where
  toFun := Filter.Germ.map f
  map_zero' := by
    simp only [← Filter.Germ.coe_zero, Filter.Germ.map_coe, Filter.Germ.coe_eq]
    exact Filter.Eventually.of_forall fun _ ↦ f.map_zero
  map_one' := by
    simp only [← Filter.Germ.coe_one, Filter.Germ.map_coe, Filter.Germ.coe_eq]
    exact Filter.Eventually.of_forall fun _ ↦ f.map_one
  map_add' a b := Filter.Germ.inductionOn₂ a b fun a b ↦ by
    simp only [← Filter.Germ.coe_add, Filter.Germ.map_coe]
    congr 1
    exact funext fun x ↦ f.map_add (a x) (b x)
  map_mul' a b := Filter.Germ.inductionOn₂ a b fun a b ↦ by
    simp only [← Filter.Germ.coe_mul, Filter.Germ.map_coe]
    congr 1
    exact funext fun x ↦ f.map_mul (a x) (b x)

/-- On representatives, the induced homomorphism is postcomposition. -/
@[simp]
theorem mapGerm_coe (f : R →+* S) (l : Filter α) (g : α → R) :
    f.mapGerm l (g : Filter.Germ l R) = (f ∘ g : α → S) := (rfl)

/-- An injective ring homomorphism induces an injective homomorphism on germs. -/
theorem mapGerm_injective (f : R →+* S) (l : Filter α) (hf : Function.Injective f) :
    Function.Injective (f.mapGerm l) := by
  intro a b
  induction a using Filter.Germ.inductionOn with | _ a =>
  induction b using Filter.Germ.inductionOn with | _ b =>
  simp only [mapGerm_coe, Filter.Germ.coe_eq]
  exact fun h ↦ h.mono fun _ hx ↦ hf hx

end RingHom
