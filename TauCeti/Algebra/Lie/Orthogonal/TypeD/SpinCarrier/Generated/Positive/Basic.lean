/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Orthogonal.TypeD.SpinCarrier.Generated.Connected
public import TauCeti.Algebra.Lie.Orthogonal.TypeD.SpinCarrier.Generated.Smooth

/-!
# The positive subgroup generated over a field in the type-Dₙ spin carrier

For `4 ≤ n`, the `n` positive numbered simple-root subgroups and the rank-`n` weight torus of the
full-weight type-`Dₙ` spin carrier generate a closed subgroup of the generated spin group. Its
coordinate algebra is the quotient of the coordinate algebra of `GL_(2^n)` by the largest Hopf
ideal killed by those `n + 1` coordinate maps. Over any field this positive subgroup is smooth and
geometrically connected. Restriction of the generated spin group's coordinates to it is
surjective, and the positive root and torus maps factor through it.

This construction generates the subgroup over the chosen ground ring. It is not identified with
the specialization of an integral positive subgroup, or with a Borel subgroup of the pinned simply
connected group scheme of type `Dₙ`.

## Main declarations

* `TauCeti.TypeDSpinCarrier.Generated.Positive.definingIdeal`: the common kernel of the positive
  root and weight-torus coordinate maps in the coordinate algebra of `GL_(2^n)`.
* `TauCeti.TypeDSpinCarrier.Generated.Positive.carrierDefiningIdeal`: the same subgroup as a
  closed subgroup of the generated spin group.
* `TauCeti.TypeDSpinCarrier.Generated.Positive.smooth_coordinateHopfAlgebra` and
  `TauCeti.TypeDSpinCarrier.Generated.Positive.geometricallyConnected_coordinateHopfAlgebra`:
  smoothness and geometric connectedness over every field.

## References

* J. S. Milne, *Algebraic Groups* (2017), §2.h and Chapter 17.
* J. E. Humphreys, *Linear Algebraic Groups*, §§26–28.
* The construction follows `TauCeti.Algebra.Lie.E7.Minuscule.Generated.Positive.Basic`.
-/

public section

open CategoryTheory
open TauCeti.CommHopfAlgCat
  (geometricallyConnectedCommHopfAlgProperty_commonKernelQuotient_of_geometricallyConnected)

namespace TauCeti.TypeDSpinCarrier.Generated.Positive

universe u

noncomputable section

variable (n : ℕ) (hn : 4 ≤ n) (A : Type u) [CommRing A]

/-- The full generator index of a positive numbered root or of the weight torus. -/
abbrev generatorIndex : Fin n ⊕ Unit → (Fin n ⊕ Fin n) ⊕ Unit
  | .inl i => .inl (.inl i)
  | .inr u => .inr u

/-- The coordinate algebras of the positive numbered roots and the weight torus. -/
abbrev generatorCodomain (j : Fin n ⊕ Unit) : CommHopfAlgCat A :=
  generatorCoordinateAlgebra n A (generatorIndex n j)

/-- The positive root and weight-torus coordinate maps into `GL_(2^n)`. -/
def generator (j : Fin n ⊕ Unit) :
    GeneralLinear.coordinateHopfAlgebra A (dimension n) ⟶ generatorCodomain n A j :=
  generatorCoordinateMap n hn A (generatorIndex n j)

@[simp]
theorem generator_inl (i : Fin n) :
    generator n hn A (.inl i) = generatorCoordinateMap n hn A (.inl (.inl i)) := (rfl)

@[simp]
theorem generator_inr : generator n hn A (.inr ()) = generatorCoordinateMap n hn A (.inr ()) :=
  (rfl)

/-- The largest Hopf ideal in the `GL_(2^n)` coordinate algebra killed by the positive numbered
root coordinate maps and the weight-torus coordinate map. It defines the smallest closed subgroup
containing those roots and the torus, as characterized by `le_definingIdeal_iff`. -/
abbrev definingIdeal : HopfIdeal A (GeneralLinear.coordinateHopfAlgebra A (dimension n)) :=
  CommHopfAlgCat.commonKernelHopfIdeal (generator n hn A)

/-- The positive subgroup is the smallest closed subgroup containing the positive numbered roots
and the torus, expressed contravariantly on defining ideals. -/
theorem le_definingIdeal_iff
    (I : HopfIdeal A (GeneralLinear.coordinateHopfAlgebra A (dimension n))) :
    I ≤ definingIdeal n hn A ↔
      (∀ i : Fin n, I.toIdeal ≤ RingHom.ker
        (generatorCoordinateMap n hn A (.inl (.inl i))).hom.toAlgHom.toRingHom) ∧
      I.toIdeal ≤ RingHom.ker
        (generatorCoordinateMap n hn A (.inr ())).hom.toAlgHom.toRingHom := by
  rw [CommHopfAlgCat.le_commonKernelHopfIdeal_iff]
  constructor
  · intro h
    exact ⟨fun i ↦ h (.inl i), h (.inr ())⟩
  · rintro ⟨hroot, htorus⟩ (i | ⟨⟩)
    · exact hroot i
    · exact htorus

/-- The generated positive subgroup lies in the full generated spin group. -/
theorem generatedDefiningIdeal_le : generatedDefiningIdeal n hn A ≤ definingIdeal n hn A :=
  (le_definingIdeal_iff n hn A _).mpr
    ⟨fun i ↦ (le_generatedDefiningIdeal_iff n hn A _).mp le_rfl (.inl (.inl i)),
      (le_generatedDefiningIdeal_iff n hn A _).mp le_rfl (.inr ())⟩

/-- The coordinate Hopf algebra of the positive subgroup generated over the ground ring. It is the
quotient of the `GL_(2^n)` coordinate algebra by the common-kernel ideal `definingIdeal`. -/
abbrev coordinateHopfAlgebra : CommHopfAlgCat A :=
  CommHopfAlgCat.quotient (GeneralLinear.coordinateHopfAlgebra A (dimension n))
    (definingIdeal n hn A)

/-- Restriction of the generated spin group's coordinates to the positive subgroup. -/
def restriction : generatedCoordinateHopfAlgebra n hn A ⟶ coordinateHopfAlgebra n hn A :=
  generatedCoordinateDesc n hn A (CommHopfAlgCat.mkQuotient _ (definingIdeal n hn A)) (by
    rw [CommHopfAlgCat.mkQuotient_ker]
    exact generatedDefiningIdeal_le n hn A)

/-- Restricting the ambient quotient coordinates recovers the positive quotient map. -/
@[reassoc (attr := simp)]
theorem generatedCoordinateMap_comp_restriction :
    generatedCoordinateMap n hn A ≫ restriction n hn A =
      CommHopfAlgCat.mkQuotient _ (definingIdeal n hn A) :=
  generatedCoordinateMap_comp_generatedCoordinateDesc n hn A _ _

/-- Restriction to the positive subgroup is surjective, so it defines a closed immersion. -/
theorem restriction_surjective : Function.Surjective (restriction n hn A).hom := by
  have h := CommHopfAlgCat.mkQuotient_surjective
    (GeneralLinear.coordinateHopfAlgebra A (dimension n)) (definingIdeal n hn A)
  rw [← generatedCoordinateMap_comp_restriction] at h
  exact Function.Surjective.of_comp h

/-- The positive subgroup's defining ideal inside the generated spin group: the common kernel of
the positive numbered root and weight-torus coordinate lifts. -/
def carrierDefiningIdeal : HopfIdeal A (generatedCoordinateHopfAlgebra n hn A) :=
  CommHopfAlgCat.commonKernelHopfIdeal fun j : Fin n ⊕ Unit ↦
    generatedCoordinateLift n hn A (generatorIndex n j)

/-- The positive subgroup's defining ideal is the kernel of restriction to it. -/
theorem kerOfSurjective_restriction :
    HopfIdeal.kerOfSurjective (restriction n hn A).hom (restriction_surjective n hn A) =
      carrierDefiningIdeal n hn A :=
  CommHopfAlgCat.kerOfSurjective_eq_commonKernelHopfIdeal_of_comp
    (generatedCoordinateMap n hn A) (generatedCoordinateMap_surjective n hn A) (generator n hn A)
    _ (fun j ↦ generatedCoordinateMap_comp_generatedCoordinateLift n hn A (generatorIndex n j))
    (restriction n hn A) (generatedCoordinateMap_comp_restriction n hn A)

@[simp]
theorem mem_carrierDefiningIdeal (x : generatedCoordinateHopfAlgebra n hn A) :
    x ∈ carrierDefiningIdeal n hn A ↔ (restriction n hn A).hom x = 0 := by
  rw [← kerOfSurjective_restriction, HopfIdeal.mem_kerOfSurjective]

/-- The generated spin group's generator lifts factor through the positive subgroup. -/
@[reassoc (attr := simp)]
theorem restriction_comp_commonKernelLift (j : Fin n ⊕ Unit) :
    restriction n hn A ≫ CommHopfAlgCat.commonKernelLift (generator n hn A) j =
      generatedCoordinateLift n hn A (generatorIndex n j) := by
  apply generatedCoordinateLift_unique
  rw [← Category.assoc, generatedCoordinateMap_comp_restriction,
    CommHopfAlgCat.mkQuotient_comp_commonKernelLift]
  rfl

/-- The positive subgroup contains every positive numbered root subgroup and the weight torus. -/
theorem carrierDefiningIdeal_toIdeal_le_ker_generatedCoordinateLift (j : Fin n ⊕ Unit) :
    (carrierDefiningIdeal n hn A).toIdeal ≤ RingHom.ker
      (generatedCoordinateLift n hn A (generatorIndex n j)).hom.toAlgHom.toRingHom :=
  CommHopfAlgCat.commonKernelHopfIdeal_toIdeal_le_ker _ j

/-- A Hopf ideal of the generated spin group lies below the positive subgroup's defining ideal
exactly when the positive numbered root and weight-torus coordinate lifts kill it. -/
theorem le_carrierDefiningIdeal_iff (I : HopfIdeal A (generatedCoordinateHopfAlgebra n hn A)) :
    I ≤ carrierDefiningIdeal n hn A ↔
      ∀ j : Fin n ⊕ Unit, I.toIdeal ≤ RingHom.ker
        (generatedCoordinateLift n hn A (generatorIndex n j)).hom.toAlgHom.toRingHom :=
  CommHopfAlgCat.le_commonKernelHopfIdeal_iff _ I

variable (k : Type u) [Field k]

/-- The positive subgroup generated over any field is smooth, including over imperfect fields. -/
theorem smooth_coordinateHopfAlgebra :
    smoothCommHopfAlgProperty k (coordinateHopfAlgebra n hn k) := by
  let : ∀ j, Algebra.IsGeometricallyReduced k (generatorCodomain n k j) := fun j ↦
    isGeometricallyReduced_generatorCoordinateAlgebra n k (generatorIndex n j)
  exact
    CommHopfAlgCat.smoothCommHopfAlgProperty_quotient_commonKernelHopfIdeal_of_geometricallyReduced
      (generator n hn k)

/-- The positive subgroup generated over any field is geometrically connected. -/
theorem geometricallyConnected_coordinateHopfAlgebra :
    geometricallyConnectedCommHopfAlgProperty k (coordinateHopfAlgebra n hn k) :=
  geometricallyConnectedCommHopfAlgProperty_commonKernelQuotient_of_geometricallyConnected
    (generator n hn k)
    (fun j ↦ geometricallyConnected_generatorCoordinateAlgebra n k (generatorIndex n j))

end

end TauCeti.TypeDSpinCarrier.Generated.Positive
