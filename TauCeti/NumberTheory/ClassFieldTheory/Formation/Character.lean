/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude, Codex
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Formation.Basic
public import TauCeti.RepresentationTheory.Homological.TateCohomology.Character
public import TauCeti.RepresentationTheory.Homological.TateCohomology.Cup.Product

/-!
# Character classes for the Artin map of a finite normal layer

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
* `TauCeti.ClassFieldTheory.NormalLayer.artinCharacterCup`: the class `a₀ ∪ δχ` in
  `H²(Γ, A^V)` used in the character formula for the Artin map.

## Main results

* `TauCeti.ClassFieldTheory.NormalLayer.characterConnectingClass_def`: `δχ` is the connecting
  class `TauCeti.TateCohomology.characterConnectingClass` of the finite group `Γ`.
* `TauCeti.ClassFieldTheory.NormalLayer.characterConnectingClass_add`,
  `TauCeti.ClassFieldTheory.NormalLayer.characterConnectingClass_zero`,
  `TauCeti.ClassFieldTheory.NormalLayer.characterConnectingClass_neg`,
  `TauCeti.ClassFieldTheory.NormalLayer.characterConnectingClass_sub`: `δχ` is additive in `χ`.
* `TauCeti.ClassFieldTheory.NormalLayer.artinCharacterCup_apply`: the Artin character cup is the
  Tate cup product transported through the right unitor and the positive-degree comparison.
* `TauCeti.ClassFieldTheory.NormalLayer.artinCharacterCup_eq_zero_of_mem_normSubgroup`: the cup
  vanishes when its ground-level argument is a norm.

## References

* E. Artin and J. Tate, *Class Field Theory*, Chapter XIV, §3.
* J.-P. Serre, *Local Fields*, Chapter XI, §3.
-/

public noncomputable section

open CategoryTheory MonoidalCategory Rep

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

section Formation

variable (F : Formation G)

/-- The class `a₀ ∪ δχ ∈ H²(Γ, A^V)` used in the character formula for the Artin map, where `a₀`
is the degree-zero Tate class of `a` and `δχ` is the connecting class of the character `χ`.
The cup product lands in the cohomology of `A^V ⊗ ℤ`; the right unitor identifies this
coefficient representation with `A^V`, and positive Tate cohomology is then identified with
ordinary group cohomology. -/
def artinCharacterCup :
    F.level L.ground →+
      (Additive (Abelianization L.Gal) →+ AddCircle (1 : ℚ)) →+ L.H F 2 where
  toFun a :=
    { toFun := fun χ =>
        (L.tateHIsoH F 2).hom <|
          (tateCohomologyFunctor 2).map (ρ_ (L.rep F)).hom <|
            TateCohomology.cup (L.rep F) (Rep.trivial ℤ L.Gal ℤ) 0 2 2 (zero_add 2)
              (L.zeroTateClass F a) (L.characterConnectingClass χ)
      map_zero' := by simp
      map_add' := by intros; simp }
  map_zero' := by ext; simp
  map_add' := by intros; ext; simp

/-- The Artin character cup evaluates as the Tate cup product of `a₀` with `δχ`, transported
through the right unitor and the comparison between positive Tate and ordinary cohomology. -/
theorem artinCharacterCup_apply (a : F.level L.ground)
    (χ : Additive (Abelianization L.Gal) →+ AddCircle (1 : ℚ)) :
    L.artinCharacterCup F a χ =
      (L.tateHIsoH F 2).hom
        ((tateCohomologyFunctor 2).map (ρ_ (L.rep F)).hom
          (TateCohomology.cup (L.rep F) (Rep.trivial ℤ L.Gal ℤ) 0 2 2 (zero_add 2)
            (L.zeroTateClass F a) (L.characterConnectingClass χ))) :=
  by simp [artinCharacterCup]

/-- The Artin character cup vanishes on the norm subgroup. -/
theorem artinCharacterCup_eq_zero_of_mem_normSubgroup (a : F.level L.ground)
    (χ : Additive (Abelianization L.Gal) →+ AddCircle (1 : ℚ))
    (ha : a ∈ L.normSubgroup F) :
    L.artinCharacterCup F a χ = 0 := by
  rw [← L.zeroTateClass_eq_zero_iff F a] at ha
  rw [artinCharacterCup_apply, ha]
  simp

end Formation

end TauCeti.ClassFieldTheory.NormalLayer
