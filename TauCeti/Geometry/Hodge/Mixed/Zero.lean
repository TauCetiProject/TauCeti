/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
public import TauCeti.Geometry.Hodge.Mixed.Category

/-!
# The zero mixed Hodge structure

This file constructs a zero object in the category of mixed Hodge structures. Its integral,
rational, and complex carriers are the zero modules, presented as functions from `Fin 0`; its
filtrations are those of the pure zero Hodge structure, viewed as mixed in weight zero.

The zero object is a necessary finite limit and colimit. In particular, it is part of the
categorical structure needed to express kernels and cokernels of mixed-Hodge morphisms.

## Main declarations

* `TauCeti.Hodge.MixedHodgeStructureCat.zero`: the zero mixed Hodge structure.
* `TauCeti.Hodge.MixedHodgeStructureCat.isZero_of_subsingleton_ratCarrier`: a mixed Hodge
  structure with zero rational carrier is a zero object.
* `TauCeti.Hodge.MixedHodgeStructureCat.isZero_zero`: the named object is both initial and terminal.
* `HasZeroObject TauCeti.Hodge.MixedHodgeStructureCat`: the resulting categorical instance.

## References

Deligne, *Théorie de Hodge II*, §2.3; Peters--Steenbrink, *Mixed Hodge Structures*, Ch. 3.
The categorical API follows the zero-object pattern in
`TauCeti.Algebra.Coalgebra.Comodule.Zero`.
-/

public section

namespace TauCeti.Hodge.MixedHodgeStructureCat

open CategoryTheory Limits

universe u

private abbrev ZeroInt := ULift.{u} (Fin 0 → ℤ)

private abbrev ZeroRat := ULift.{u} (Fin 0 → ℚ)

private abbrev ZeroComplex := ULift.{u} (Fin 0 → ℂ)

private def zeroToRat : ZeroInt →ₗ[ℤ] ZeroRat :=
  0

private def zeroToComplex : ZeroInt →ₗ[ℤ] ZeroComplex :=
  0

private theorem zeroToRat_isBaseChange : IsBaseChange ℚ zeroToRat := by
  apply IsBaseChange.of_equiv (LinearEquiv.ofSubsingleton _ _)
  intro x
  exact Subsingleton.elim _ _

private theorem zeroToComplex_isBaseChange : IsBaseChange ℂ zeroToComplex := by
  apply IsBaseChange.of_equiv (LinearEquiv.ofSubsingleton _ _)
  intro x
  exact Subsingleton.elim _ _

private noncomputable def zeroPure :
    HodgeStructure zeroToComplex_isBaseChange 0 where
  F _ := ⊥
  F_antitone _ _ _ := le_rfl
  F_top := ⟨0, Subsingleton.elim _ _⟩
  opposed _ := ⟨by simp, by rw [codisjoint_iff]; exact Subsingleton.elim _ _⟩

/-- The zero mixed Hodge structure, with zero integral, rational, and complex carriers. -/
noncomputable def zero : MixedHodgeStructureCat.{u} :=
  .of zeroToRat_isBaseChange zeroToComplex_isBaseChange
    (MixedHodgeStructure.ofPure zeroToRat_isBaseChange zeroToComplex_isBaseChange zeroPure)

/-- A mixed Hodge structure with subsingleton rational carrier is a zero object.

Morphisms of mixed Hodge structures are determined by their rational linear maps, so the
rational carrier alone detects the zero object; no separate hypothesis on the complex carrier is
needed. -/
theorem isZero_of_subsingleton_ratCarrier (X : MixedHodgeStructureCat.{u})
    [Subsingleton X.ratCarrier] : IsZero X where
  unique_to Y :=
    ⟨{ default := 0
       uniq := fun f ↦ by
         apply hom_ext
         ext x
         rw [Subsingleton.elim x 0]
         simp }⟩
  unique_from Y :=
    ⟨{ default := 0
       uniq := fun f ↦ by
         apply hom_ext
         ext x
         exact Subsingleton.elim _ _ }⟩

/-- The rational carrier of the named zero mixed Hodge structure is subsingleton. -/
theorem subsingleton_zero_ratCarrier :
    Subsingleton (zero : MixedHodgeStructureCat.{u}).ratCarrier := by
  dsimp only [zero, of]
  infer_instance

/-- The named zero mixed Hodge structure is both initial and terminal. -/
theorem isZero_zero : IsZero (zero : MixedHodgeStructureCat.{u}) := by
  let _ : Subsingleton (zero : MixedHodgeStructureCat.{u}).ratCarrier :=
    subsingleton_zero_ratCarrier
  exact isZero_of_subsingleton_ratCarrier zero

/-- Any morphism from the named zero mixed Hodge structure is zero. -/
theorem zero_hom_eq_zero (X : MixedHodgeStructureCat.{u}) (f : zero ⟶ X) : f = 0 :=
  isZero_zero.eq_of_src f 0

/-- Any morphism to the named zero mixed Hodge structure is zero. -/
theorem hom_zero_eq_zero (X : MixedHodgeStructureCat.{u}) (f : X ⟶ zero) : f = 0 :=
  isZero_zero.eq_of_tgt f 0

/-- The canonical morphism out of the named zero mixed Hodge structure is the zero morphism. -/
@[simp]
theorem isZero_zero_to (X : MixedHodgeStructureCat.{u}) : isZero_zero.to_ X = 0 :=
  zero_hom_eq_zero X _

/-- The canonical morphism into the named zero mixed Hodge structure is the zero morphism. -/
@[simp]
theorem isZero_zero_from (X : MixedHodgeStructureCat.{u}) : isZero_zero.from_ X = 0 :=
  hom_zero_eq_zero X _

/-- Morphisms from the named zero mixed Hodge structure are unique. -/
@[ext]
theorem zero_hom_ext {X : MixedHodgeStructureCat.{u}} (f g : zero ⟶ X) : f = g :=
  isZero_zero.eq_of_src f g

/-- Morphisms to the named zero mixed Hodge structure are unique. -/
@[ext]
theorem hom_zero_ext {X : MixedHodgeStructureCat.{u}} (f g : X ⟶ zero) : f = g :=
  isZero_zero.eq_of_tgt f g

/-- The category of mixed Hodge structures has a zero object. -/
noncomputable instance hasZeroObject : HasZeroObject MixedHodgeStructureCat.{u} :=
  isZero_zero.hasZeroObject

end TauCeti.Hodge.MixedHodgeStructureCat
