/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
public import TauCeti.Geometry.Hodge.Category

/-!
# The zero polarizable Hodge structure

The zero lattice carries a unique Hodge structure of any weight, and the zero bilinear form
polarizes it: the Hodge–Riemann positivity is a condition on nonzero vectors of the Hodge
components, of which there are none. So the zero object exists in the category of polarizable
rational Hodge structures of a fixed weight, which is what makes the empty direct sum available
alongside the binary ones.

## Main declarations

* `TauCeti.Hodge.PolarizableHodgeStructureCat.zero`: the zero polarizable Hodge structure of a
  given weight.
* `TauCeti.Hodge.PolarizableHodgeStructureCat.isZero_of_subsingleton_ratCarrier`: an object with
  zero rational carrier is a zero object.
* `TauCeti.Hodge.PolarizableHodgeStructureCat.isZero_zero`: the named object is both initial and
  terminal.
* `TauCeti.Hodge.PolarizableHodgeStructureCat.subsingleton_zero_ratCarrier`: its rational carrier
  is trivial.

## References

Voisin, *Hodge Theory and Complex Algebraic Geometry I*, §7.1.2; Peters--Steenbrink, *Mixed Hodge
Structures*, §2.
-/

public section

namespace TauCeti.Hodge.PolarizableHodgeStructureCat

open CategoryTheory Limits

universe u

variable {n : ℤ}

private abbrev ZeroInt := ULift.{u} (Fin 0 → ℤ)

private abbrev ZeroRat := ULift.{u} (Fin 0 → ℚ)

private abbrev ZeroComplex := ULift.{u} (Fin 0 → ℂ)

private def zeroToRat : ZeroInt.{u} →ₗ[ℤ] ZeroRat.{u} :=
  0

private def zeroToComplex : ZeroInt.{u} →ₗ[ℤ] ZeroComplex.{u} :=
  0

private theorem zeroToRat_isBaseChange : IsBaseChange ℚ zeroToRat.{u} := by
  apply IsBaseChange.of_equiv (LinearEquiv.ofSubsingleton _ _)
  intro x
  exact Subsingleton.elim _ _

private theorem zeroToComplex_isBaseChange : IsBaseChange ℂ zeroToComplex.{u} := by
  apply IsBaseChange.of_equiv (LinearEquiv.ofSubsingleton _ _)
  intro x
  exact Subsingleton.elim _ _

private noncomputable def zeroPure (n : ℤ) :
    HodgeStructure zeroToComplex_isBaseChange.{u} n where
  F _ := ⊥
  F_antitone _ _ _ := le_rfl
  F_top := ⟨0, Subsingleton.elim _ _⟩
  opposed _ := ⟨by simp, by rw [codisjoint_iff]; exact Subsingleton.elim _ _⟩

private noncomputable def zeroPolarization (n : ℤ) :
    Polarization zeroToComplex_isBaseChange.{u} (zeroPure n) where
  Qint := 0
  isPolarization :=
    { symm_weight := by simp
      nondegenerate := ⟨fun _ _ ↦ Subsingleton.elim _ _, fun _ _ ↦ Subsingleton.elim _ _⟩
      orthogonal := by
        intro p x _ y _
        rw [Subsingleton.elim x 0, map_zero, LinearMap.zero_apply]
      positive := by
        intro p x _ hx
        exact absurd (Subsingleton.elim x 0) hx }

/-- The zero polarizable Hodge structure of weight `n`, on the zero lattice. -/
noncomputable def zero (n : ℤ) : PolarizableHodgeStructureCat.{u} n :=
  of zeroToRat_isBaseChange zeroToComplex_isBaseChange (zeroPure n)
    (zeroPolarization n).isPolarizable

/-- A polarizable Hodge structure with subsingleton rational carrier is a zero object.

Morphisms are determined by their rational linear maps, so the rational carrier alone detects the
zero object; no separate hypothesis on the complex carrier is needed. -/
theorem isZero_of_subsingleton_ratCarrier (X : PolarizableHodgeStructureCat.{u} n)
    [Subsingleton X.ratCarrier] : IsZero X where
  unique_to Y :=
    ⟨{ default := 0
       uniq := fun f ↦ by
         apply Hom.ext
         ext x
         rw [Subsingleton.elim x 0]
         simp }⟩
  unique_from Y :=
    ⟨{ default := 0
       uniq := fun f ↦ by
         apply Hom.ext
         ext x
         exact Subsingleton.elim _ _ }⟩

/-- The rational carrier of the named zero object is subsingleton. -/
theorem subsingleton_zero_ratCarrier (n : ℤ) : Subsingleton (zero.{u} n).ratCarrier := by
  dsimp only [zero, of]
  infer_instance

/-- The named zero object is both initial and terminal. -/
theorem isZero_zero (n : ℤ) : IsZero (zero.{u} n) :=
  let _ : Subsingleton (zero.{u} n).ratCarrier := subsingleton_zero_ratCarrier n
  isZero_of_subsingleton_ratCarrier _

/-- The category of polarizable Hodge structures of weight `n` has a zero object. -/
noncomputable instance hasZeroObject :
    HasZeroObject (PolarizableHodgeStructureCat.{u} n) :=
  (isZero_zero n).hasZeroObject

end TauCeti.Hodge.PolarizableHodgeStructureCat
