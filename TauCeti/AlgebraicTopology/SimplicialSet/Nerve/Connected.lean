/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
public import Mathlib.AlgebraicTopology.SimplicialSet.PiZero
public import Mathlib.CategoryTheory.IsConnected

/-!
# Connectedness of nerves

Edges of the nerve are morphisms by `CategoryTheory.nerve.homEquiv`. The description
of components by `SSet.π₀.mk_eq_mk_iff` therefore gives the same connectedness condition
as Mathlib's `CategoryTheory.Zigzag`.

## References

* Kerodon, §1.2.1, Connected Components of Simplicial Sets (Tag 00G5).
-/

public section

universe u v

open SSet Simplicial

namespace CategoryTheory

/-- The nerve of a category is connected exactly when the category is connected. -/
theorem isConnected_nerve_iff (C : Type u) [Category.{v} C] :
    (nerve C).IsConnected ↔ IsConnected C := by
  constructor
  · intro h
    have : Nonempty C := h.nonempty.map nerveEquiv
    apply zigzag_isConnected
    intro x y
    have aux (a b : (nerve C) _⦋0⦌) : Zigzag (nerveEquiv a) (nerveEquiv b) := by
      have hxy := (π₀.mk_eq_mk_iff a b).mp (Subsingleton.elim _ _)
      induction hxy with
      | rel _ _ h => exact h.elim fun e ↦ Zigzag.of_hom (nerve.homEquiv e)
      | refl => exact Zigzag.refl _
      | symm _ _ _ ih => exact ih.symm
      | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂
    simpa only [Equiv.apply_symm_apply] using aux (nerveEquiv.symm x) (nerveEquiv.symm y)
  · intro h
    have : (nerve C).Nonempty := (inferInstance : Nonempty C).map nerveEquiv.symm
    rw [SSet.isConnected_iff]
    refine ⟨⟨fun a b ↦ ?_⟩, inferInstance⟩
    obtain ⟨x, rfl⟩ := π₀.mk_surjective a
    obtain ⟨y, rfl⟩ := π₀.mk_surjective b
    obtain ⟨x, rfl⟩ := nerveEquiv.symm.surjective x
    obtain ⟨y, rfl⟩ := nerveEquiv.symm.surjective y
    induction isPreconnected_zigzag x y with
    | refl => rfl
    | tail _ hz ih =>
      apply ih.trans
      rcases hz with ⟨⟨f⟩⟩ | ⟨⟨f⟩⟩
      · exact π₀.sound (nerve.edgeMk f)
      · exact (π₀.sound (nerve.edgeMk f)).symm

end CategoryTheory
