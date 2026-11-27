/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Limits.Final
public import TauCeti.AlgebraicTopology.Quasicategory.Final
public import TauCeti.AlgebraicTopology.SimplicialSet.Nerve.Comma

/-!
# Finality for maps of nerves

The undercategory comparison `CategoryTheory.nerve.cosliceIso` and Mathlib's
`CategoryTheory.nerveAdjunction` identify the fibres tested by `SSet.IsFinal` with nerves
of structured arrow categories. Weak contractibility implies connectedness. The edge
description `CategoryTheory.nerve.homEquiv` turns simplicial connectedness of those nerves
into the zigzag condition for `CategoryTheory.Functor.Final`.

## References

* J. Lurie, *Higher Topos Theory*, Theorem 4.1.3.1.
* Kerodon, §1.2.1, Connected Components of Simplicial Sets (Tag 00G5).
-/

public section

universe u

open SSet CategoryTheory Limits Simplicial

namespace CategoryTheory.Functor

open nerve

variable {C D : Type u} [Category.{u} C] [Category.{u} D]

/-- A map of nerves is final exactly when the structured arrow categories have weakly
contractible nerves, the comma-category condition of HTT Theorem 4.1.3.1. -/
theorem isFinal_nerveMap_iff (F : C ⥤ D) :
    SSet.IsFinal (nerveMap F) ↔ ∀ x : D, IsWeaklyContractible (nerve (StructuredArrow x F)) := by
  rw [SSet.isFinal_iff]
  constructor
  · intro h x
    have := h (nerveEquiv.symm x)
    exact IsWeaklyContractible.of_iso
      (F.nerveCommaIso x).symm
  · intro h y
    obtain ⟨x, rfl⟩ := nerveEquiv.symm.surjective y
    have := h x
    exact IsWeaklyContractible.of_iso (F.nerveCommaIso x)

/-- A functor whose nerve map is final is final in the ordinary sense. -/
theorem final_of_isFinal_nerveMap (F : C ⥤ D)
    (h : SSet.IsFinal (nerveMap F)) : F.Final := by
  constructor
  intro x
  have := F.isFinal_nerveMap_iff.1 h x
  have connected : (nerve (StructuredArrow x F)).IsConnected := inferInstance
  have : Nonempty (StructuredArrow x F) := connected.nonempty.map nerveEquiv
  apply zigzag_isConnected
  intro a b
  obtain ⟨a, rfl⟩ := nerveEquiv.surjective a
  obtain ⟨b, rfl⟩ := nerveEquiv.surjective b
  have hab := (π₀.mk_eq_mk_iff (X := nerve (StructuredArrow x F)) a b).mp (Subsingleton.elim _ _)
  induction hab with
  | rel _ _ h => exact h.elim fun e ↦ Zigzag.of_hom (nerve.homEquiv e)
  | refl => exact Zigzag.refl _
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

end CategoryTheory.Functor
