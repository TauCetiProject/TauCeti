/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# Residue-field extension degree under subring equality

Two equal local subrings (such as valuation subrings) below and above that carry compatible local
algebra structures induce residue-field extensions of the same degree.

## Main results

* `TauCeti.finrank_residueField_eq_of_eq`: equality of `Module.finrank` on residue fields when the
  lower and upper subrings coincide and their algebra maps agree on underlying elements.
-/

public section

namespace TauCeti

/-- If two pairs of local subrings `(A₁, B₁)` and `(A₂, B₂)` are equal and carry compatible local
algebra structures, then their residue-field extensions have the same degree. -/
theorem finrank_residueField_eq_of_eq {R S α β : Type*} [CommRing R] [CommRing S]
    [SetLike α R] [SubringClass α R] [SetLike β S] [SubringClass β S]
    {A₁ A₂ : α} {B₁ B₂ : β}
    [IsLocalRing A₁] [IsLocalRing A₂] [IsLocalRing B₁] [IsLocalRing B₂]
    [inst₁ : Algebra A₁ B₁] [IsLocalHom (algebraMap A₁ B₁)]
    [inst₂ : Algebra A₂ B₂] [IsLocalHom (algebraMap A₂ B₂)]
    (hA : A₁ = A₂) (hB : B₁ = B₂)
    (hcomp : ∀ (x : A₁) (y : A₂), (x : R) = (y : R) →
      (algebraMap A₁ B₁ x : S) = (algebraMap A₂ B₂ y : S)) :
    Module.finrank (IsLocalRing.ResidueField A₁) (IsLocalRing.ResidueField B₁) =
      Module.finrank (IsLocalRing.ResidueField A₂) (IsLocalRing.ResidueField B₂) := by
  subst hA; subst hB
  have h : inst₁ = inst₂ := Algebra.algebra_ext inst₁ inst₂ fun x ↦ Subtype.ext (hcomp x x rfl)
  subst h
  rfl

end TauCeti
