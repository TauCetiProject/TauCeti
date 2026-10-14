/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Orthogonal.TypeB.SpinCarrier.Generated.Basic
public import TauCeti.Algebra.Lie.Orthogonal.TypeB.SpinCarrier.Generated.Smooth
public import TauCeti.Algebra.Lie.Orthogonal.TypeB.SpinCarrier.Generated.Connected
public import TauCeti.Algebra.AlgebraicGroup.Connected.Generated
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.CommonKernel.GeometricallyReduced

/-!
# The positive subgroup of the generated type-B spin carrier

The positive numbered root subgroups and the weight torus generate a closed subgroup of the
generated type-`Bₙ₊₁` spin carrier. Its coordinate algebra is the quotient by the largest Hopf
ideal killed by those coordinate maps. Over any field this positive subgroup is smooth and
geometrically connected. The restriction from the full generated carrier is surjective, and
the positive root and torus maps factor through it.

This construction supplies the canonical positive subgroup used to build a Borel subgroup and a
pinning of the generated spin carrier.

## Main declarations

* `TauCeti.TypeBSpinCarrier.Generated.Positive.definingIdeal`: the ambient defining ideal of the
  positive subgroup.
* `TauCeti.TypeBSpinCarrier.Generated.Positive.carrierDefiningIdeal`: its defining ideal inside
  the full generated carrier.
* `TauCeti.TypeBSpinCarrier.Generated.Positive.smooth_coordinateHopfAlgebra`: smoothness over
  every field.
* `TauCeti.TypeBSpinCarrier.Generated.Positive.geometricallyConnected_coordinateHopfAlgebra`:
  geometric connectedness over every field.

## References

* J. S. Milne, *Algebraic Groups* (2017), §2.h and Chapter 17.
* J. E. Humphreys, *Linear Algebraic Groups*, §§26–28.
-/

public section

open CategoryTheory
open TauCeti.CommHopfAlgCat
  (geometricallyConnectedCommHopfAlgProperty_commonKernelQuotient_of_geometricallyConnected)

namespace TauCeti.TypeBSpinCarrier.Generated.Positive

universe u

noncomputable section

variable (n : ℕ) (A : Type u) [CommRing A]

/-- The coordinate algebras of the positive numbered roots and the weight torus. -/
abbrev generatorCodomain (j : Fin (n + 1) ⊕ Unit) : CommHopfAlgCat A :=
  TypeBSpinCarrier.generatorCoordinateAlgebra n A (match j with
    | .inl i => .inl (.inl i)
    | .inr u => .inr u)

/-- The positive numbered-root and weight-torus coordinate maps into the ambient general linear
group. -/
def generator : ∀ j, GeneralLinear.coordinateHopfAlgebra A (dimension n) ⟶
    generatorCodomain n A j
  | .inl i => TypeBSpinCarrier.generatorCoordinateMap n A (.inl (.inl i))
  | .inr u => TypeBSpinCarrier.generatorCoordinateMap n A (.inr u)

@[simp]
theorem generator_inl (i : Fin (n + 1)) :
    generator n A (.inl i) =
      TypeBSpinCarrier.generatorCoordinateMap n A (.inl (.inl i)) := by
  simp [generator]

@[simp]
theorem generator_inr :
    generator n A (.inr ()) = TypeBSpinCarrier.generatorCoordinateMap n A (.inr ()) := by
  simp [generator]

/-- The largest Hopf ideal in the ambient coordinate algebra killed by the positive numbered
root maps and the weight-torus map. -/
abbrev definingIdeal :
    HopfIdeal A (GeneralLinear.coordinateHopfAlgebra A (dimension n)) :=
  CommHopfAlgCat.commonKernelHopfIdeal (generator n A)

/-- The positive subgroup is the smallest closed subgroup containing every positive numbered
root subgroup and the weight torus, expressed contravariantly on defining ideals. -/
theorem le_definingIdeal_iff
    (I : HopfIdeal A (GeneralLinear.coordinateHopfAlgebra A (dimension n))) :
    I ≤ definingIdeal n A ↔
      (∀ i : Fin (n + 1), I.toIdeal ≤ RingHom.ker
        (TypeBSpinCarrier.generatorCoordinateMap n A (.inl (.inl i))).hom.toAlgHom.toRingHom) ∧
      I.toIdeal ≤ RingHom.ker
        (TypeBSpinCarrier.generatorCoordinateMap n A (.inr ())).hom.toAlgHom.toRingHom := by
  rw [CommHopfAlgCat.le_commonKernelHopfIdeal_iff]
  constructor
  · intro h
    exact ⟨fun i ↦ h (.inl i), h (.inr ())⟩
  · rintro ⟨hroot, htorus⟩ (i | ⟨⟩)
    · exact hroot i
    · exact htorus

/-- The generated positive subgroup lies in the full generated spin carrier. -/
theorem generatedDefiningIdeal_le :
    TypeBSpinCarrier.generatedDefiningIdeal n A ≤ definingIdeal n A := by
  rw [le_definingIdeal_iff]
  have h := (TypeBSpinCarrier.le_generatedDefiningIdeal_iff n A
    (TypeBSpinCarrier.generatedDefiningIdeal n A)).mp le_rfl
  exact ⟨fun i ↦ h (.inl (.inl i)), h (.inr ())⟩

/-- The coordinate Hopf algebra of the positive subgroup generated over the ground ring. -/
abbrev coordinateHopfAlgebra : CommHopfAlgCat A :=
  CommHopfAlgCat.quotient (GeneralLinear.coordinateHopfAlgebra A (dimension n))
    (definingIdeal n A)

/-- Restriction of the full generated carrier's coordinates to the positive subgroup. -/
def restriction : TypeBSpinCarrier.generatedCoordinateHopfAlgebra n A ⟶
    coordinateHopfAlgebra n A :=
  (eqToIso (TypeBSpinCarrier.generatedCoordinateHopfAlgebra_def n A)).hom ≫
    CommHopfAlgCat.quotientMapOfLe _ (generatedDefiningIdeal_le n A)

/-- Restricting the ambient quotient coordinates recovers the positive quotient map. -/
@[reassoc (attr := simp)]
theorem generatedCoordinateMap_comp_restriction :
    TypeBSpinCarrier.generatedCoordinateMap n A ≫ restriction n A =
      CommHopfAlgCat.mkQuotient _ (definingIdeal n A) := by
  rw [restriction, ← Category.assoc,
    TypeBSpinCarrier.generatedCoordinateMap_comp_eqToIso_hom]
  exact CommHopfAlgCat.mkQuotient_comp_quotientMapOfLe _ (generatedDefiningIdeal_le n A)

/-- Restriction to the positive subgroup is surjective, so it represents a closed immersion. -/
theorem restriction_surjective : Function.Surjective (restriction n A).hom := by
  have h := CommHopfAlgCat.mkQuotient_surjective
    (GeneralLinear.coordinateHopfAlgebra A (dimension n)) (definingIdeal n A)
  rw [← generatedCoordinateMap_comp_restriction] at h
  exact Function.Surjective.of_comp h

/-- The positive subgroup's defining ideal inside the full generated carrier. -/
def carrierDefiningIdeal :
    HopfIdeal A (TypeBSpinCarrier.generatedCoordinateHopfAlgebra n A) :=
  CommHopfAlgCat.commonKernelHopfIdeal fun j : Fin (n + 1) ⊕ Unit ↦
    TypeBSpinCarrier.generatedCoordinateLift n A (match j with
      | .inl i => .inl (.inl i)
      | .inr u => .inr u)

/-- The positive subgroup's defining ideal inside the full carrier is the kernel of the
restriction map. -/
theorem kerOfSurjective_restriction :
    HopfIdeal.kerOfSurjective (restriction n A).hom (restriction_surjective n A) =
      carrierDefiningIdeal n A :=
  CommHopfAlgCat.kerOfSurjective_eq_commonKernelHopfIdeal_of_comp
    (TypeBSpinCarrier.generatedCoordinateMap n A)
    (TypeBSpinCarrier.generatedCoordinateMap_surjective n A) (generator n A) _
    (by
      rintro (i | ⟨⟩)
      · exact TypeBSpinCarrier.generatedCoordinateMap_comp_generatedCoordinateLift n A _
      · exact TypeBSpinCarrier.generatedCoordinateMap_comp_generatedCoordinateLift n A _)
    (restriction n A) (generatedCoordinateMap_comp_restriction n A)

@[simp]
theorem mem_carrierDefiningIdeal
    (x : TypeBSpinCarrier.generatedCoordinateHopfAlgebra n A) :
    x ∈ carrierDefiningIdeal n A ↔ (restriction n A).hom x = 0 := by
  rw [← kerOfSurjective_restriction, HopfIdeal.mem_kerOfSurjective]

/-- Each positive numbered-root and weight-torus lift of the full generated carrier factors
through restriction to the positive subgroup, followed by that subgroup's generator lift. -/
@[reassoc (attr := simp)]
theorem restriction_comp_commonKernelLift (j : Fin (n + 1) ⊕ Unit) :
    restriction n A ≫ CommHopfAlgCat.commonKernelLift (generator n A) j =
      TypeBSpinCarrier.generatedCoordinateLift n A (match j with
        | .inl i => .inl (.inl i)
        | .inr u => .inr u) := by
  apply TypeBSpinCarrier.generatedCoordinateLift_unique
  rw [← Category.assoc, generatedCoordinateMap_comp_restriction,
    CommHopfAlgCat.mkQuotient_comp_commonKernelLift]
  cases j <;> rfl

/-- The positive subgroup contains every positive numbered root subgroup and the weight torus. -/
theorem carrierDefiningIdeal_toIdeal_le_ker_generatedCoordinateLift
    (j : Fin (n + 1) ⊕ Unit) :
    (carrierDefiningIdeal n A).toIdeal ≤ RingHom.ker
      (TypeBSpinCarrier.generatedCoordinateLift n A (match j with
        | .inl i => .inl (.inl i)
        | .inr u => .inr u)).hom.toAlgHom.toRingHom :=
  CommHopfAlgCat.commonKernelHopfIdeal_toIdeal_le_ker _ j

/-- A Hopf ideal of the full carrier lies below the positive subgroup's defining ideal exactly
when every positive numbered-root and weight-torus lift kills it. -/
theorem le_carrierDefiningIdeal_iff
    (I : HopfIdeal A (TypeBSpinCarrier.generatedCoordinateHopfAlgebra n A)) :
    I ≤ carrierDefiningIdeal n A ↔
      ∀ j : Fin (n + 1) ⊕ Unit, I.toIdeal ≤ RingHom.ker
        (TypeBSpinCarrier.generatedCoordinateLift n A (match j with
          | .inl i => .inl (.inl i)
          | .inr u => .inr u)).hom.toAlgHom.toRingHom :=
  CommHopfAlgCat.le_commonKernelHopfIdeal_iff _ I

variable (k : Type u) [Field k]

/-- The positive subgroup generated over any field is smooth, including over imperfect fields. -/
theorem smooth_coordinateHopfAlgebra :
    smoothCommHopfAlgProperty k (coordinateHopfAlgebra n k) := by
  let : ∀ j, Algebra.IsGeometricallyReduced k (generatorCodomain n k j) := fun j ↦
    TypeBSpinCarrier.isGeometricallyReduced_generatorCoordinateAlgebra n k (match j with
      | .inl i => .inl (.inl i)
      | .inr u => .inr u)
  exact
    CommHopfAlgCat.smoothCommHopfAlgProperty_quotient_commonKernelHopfIdeal_of_geometricallyReduced
      (generator n k)

/-- The positive subgroup generated over any field is geometrically connected. -/
theorem geometricallyConnected_coordinateHopfAlgebra :
    geometricallyConnectedCommHopfAlgProperty k (coordinateHopfAlgebra n k) := by
  exact geometricallyConnectedCommHopfAlgProperty_commonKernelQuotient_of_geometricallyConnected
    (generator n k) (fun j ↦
      TypeBSpinCarrier.geometricallyConnected_generatorCoordinateAlgebra n k (match j with
        | .inl i => .inl (.inl i)
        | .inr u => .inr u))

end

end TauCeti.TypeBSpinCarrier.Generated.Positive
