/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Formation.Basic
public import TauCeti.RepresentationTheory.Homological.TateCohomology.Character

/-!
# The connecting class of a character of a finite normal layer

Let `Γ = U ⧸ V` be the Galois group of a finite normal layer. A character `χ : Γ^ab → ℚ/ℤ` is a
homomorphism `Γ → ℚ/ℤ`, which is a class in `H¹(Γ, ℚ/ℤ)` for the trivial action. The connecting
map of the sequence `0 → ℤ → ℚ → ℚ/ℤ → 0` of trivial `Γ`-modules sends it to a class
`δχ ∈ H²(Γ, ℤ)`, which is read in the Tate group of degree `2`. This is the class through which
Artin and Tate characterize the Artin map: `χ(artinMap a)` is the invariant of the cup product of
the degree-zero class of `a` with `δχ`.

As elsewhere in this development, `ℚ/ℤ` is the rational circle `AddCircle (1 : ℚ)`.

## Main definitions

* `TauCeti.ClassFieldTheory.NormalLayer.characterConnectingClass`: the connecting class
  `δχ ∈ H²(Γ, ℤ)` of a character `χ : Γ^ab → ℚ/ℤ`, in the Tate group of degree `2`.

## Main results

* `TauCeti.ClassFieldTheory.NormalLayer.characterConnectingClass_def`: `δχ` is the connecting
  class `TauCeti.TateCohomology.characterConnectingClass` of the finite group `Γ`.
* `TauCeti.ClassFieldTheory.NormalLayer.characterConnectingClass_add`,
  `TauCeti.ClassFieldTheory.NormalLayer.characterConnectingClass_zero`,
  `TauCeti.ClassFieldTheory.NormalLayer.characterConnectingClass_neg`,
  `TauCeti.ClassFieldTheory.NormalLayer.characterConnectingClass_sub`: `δχ` is additive in `χ`.

## References

* E. Artin and J. Tate, *Class Field Theory*, Chapter XIV, §3.
* J.-P. Serre, *Local Fields*, Chapter XI, §3.
-/

public noncomputable section

open CategoryTheory

namespace TauCeti.ClassFieldTheory.NormalLayer

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G] (L : NormalLayer G)

/-- The **connecting class** `δχ ∈ H²(Γ, ℤ)` of a character `χ : Γ^ab → ℚ/ℤ` of the Galois group
`Γ` of a finite normal layer, in the Tate group of degree `2`: the image of `χ`, as a class in
`H¹(Γ, ℚ/ℤ)` for the trivial action, under the connecting map of `0 → ℤ → ℚ → ℚ/ℤ → 0`. This is
`TauCeti.TateCohomology.characterConnectingClass` for the finite group `Γ`. -/
def characterConnectingClass (χ : Additive (Abelianization L.Gal) →+ AddCircle (1 : ℚ)) :
    L.TrivialTateH 2 :=
  TateCohomology.characterConnectingClass L.Gal χ

/-- The connecting class of a character of a layer is the connecting class of the character of
its Galois group. -/
theorem characterConnectingClass_def (χ : Additive (Abelianization L.Gal) →+ AddCircle (1 : ℚ)) :
    L.characterConnectingClass χ = TateCohomology.characterConnectingClass L.Gal χ :=
  (rfl)

/-- The connecting class is additive in the character. -/
@[simp]
theorem characterConnectingClass_add
    (χ₁ χ₂ : Additive (Abelianization L.Gal) →+ AddCircle (1 : ℚ)) :
    L.characterConnectingClass (χ₁ + χ₂) =
      L.characterConnectingClass χ₁ + L.characterConnectingClass χ₂ := by
  simp only [characterConnectingClass_def, map_add]

/-- The connecting class of the trivial character vanishes. -/
@[simp]
theorem characterConnectingClass_zero : L.characterConnectingClass 0 = 0 := by
  simp only [characterConnectingClass_def, map_zero]

/-- The connecting class of the negated character is the negated class. -/
@[simp]
theorem characterConnectingClass_neg (χ : Additive (Abelianization L.Gal) →+ AddCircle (1 : ℚ)) :
    L.characterConnectingClass (-χ) = -L.characterConnectingClass χ := by
  simp only [characterConnectingClass_def, map_neg]

/-- The connecting class of a difference of characters is the difference of their classes. -/
@[simp]
theorem characterConnectingClass_sub
    (χ₁ χ₂ : Additive (Abelianization L.Gal) →+ AddCircle (1 : ℚ)) :
    L.characterConnectingClass (χ₁ - χ₂) =
      L.characterConnectingClass χ₁ - L.characterConnectingClass χ₂ := by
  simp only [characterConnectingClass_def, map_sub]

end TauCeti.ClassFieldTheory.NormalLayer
