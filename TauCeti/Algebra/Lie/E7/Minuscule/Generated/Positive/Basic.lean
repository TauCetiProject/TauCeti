/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.E7.Minuscule.Generated.Basic
public import TauCeti.Algebra.Lie.E7.Minuscule.Generated.Smooth
public import TauCeti.Algebra.Lie.E7.Minuscule.Generated.Connected
public import TauCeti.Algebra.AlgebraicGroup.Connected.Generated
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.CommonKernel.GeometricallyReduced
import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.SmoothConnected
import TauCeti.RingTheory.Smooth.GeometricallyReduced

/-!
# The positive subgroup generated over a field in the E₇ minuscule carrier

The seven positive numbered root subgroups and the rank-seven weight torus generate a closed
subgroup of the generated minuscule E₇ group. Its coordinate algebra is the quotient by the
largest Hopf ideal killed by those eight coordinate maps. Over any field this positive subgroup
is smooth and geometrically connected. The restriction of carrier coordinates is surjective,
and the positive root and torus maps factor through it.

This construction generates the subgroup over the chosen ground ring. It is not identified
with the specialization of the integral positive subsystem, or with a Borel of the pinned
simply connected E₇ group. These comparisons require additional results.

## References

* J. S. Milne, *Algebraic Groups* (2017), §2.h and Chapter 17.
* J. E. Humphreys, *Linear Algebraic Groups*, §§26–28.
* Related formalizations: `TauCeti.E6Minuscule.Generated.Positive` and
  `TauCeti.Algebra.Lie.G2.ShortRoot.PrimeField.Positive.Basic`.
-/

public section

open CategoryTheory
open TauCeti.CommHopfAlgCat
  (geometricallyConnectedCommHopfAlgProperty_commonKernelQuotient_of_geometricallyConnected)

namespace TauCeti.E7Minuscule.Generated.Positive

universe u

noncomputable section

variable (A : Type u) [CommRing A]

/-- The coordinate algebras of the positive numbered roots and the weight torus. -/
abbrev generatorCodomain (j : Fin 7 ⊕ Unit) : CommHopfAlgCat A :=
  generatorCoordinateAlgebra A (match j with
    | .inl i => .inl (.inl i)
    | .inr u => .inr u)

/-- The positive root and weight-torus coordinate maps into `GL₅₆`. -/
def generator : ∀ j, GeneralLinear.coordinateHopfAlgebra A 56 ⟶ generatorCodomain A j
  | .inl i => generatorCoordinateMap A (.inl (.inl i))
  | .inr u => generatorCoordinateMap A (.inr u)

@[simp]
theorem generator_inl (i : Fin 7) :
    generator A (.inl i) = generatorCoordinateMap A (.inl (.inl i)) := (rfl)

@[simp]
theorem generator_inr : generator A (.inr ()) = generatorCoordinateMap A (.inr ()) := (rfl)

/-- The largest Hopf ideal in the `GL₅₆` coordinate algebra killed by the seven positive
numbered root coordinate maps and the weight-torus coordinate map. It defines the smallest closed
subgroup containing those roots and the torus, as characterized by `le_definingIdeal_iff`. -/
abbrev definingIdeal : HopfIdeal A (GeneralLinear.coordinateHopfAlgebra A 56) :=
  CommHopfAlgCat.commonKernelHopfIdeal (generator A)

/-- The positive subgroup is the smallest closed subgroup containing the seven positive numbered
roots and the torus, expressed contravariantly on defining ideals. -/
theorem le_definingIdeal_iff (I : HopfIdeal A (GeneralLinear.coordinateHopfAlgebra A 56)) :
    I ≤ definingIdeal A ↔
      (∀ i : Fin 7, I.toIdeal ≤ RingHom.ker
        (generatorCoordinateMap A (.inl (.inl i))).hom.toAlgHom.toRingHom) ∧
      I.toIdeal ≤ RingHom.ker (generatorCoordinateMap A (.inr ())).hom.toAlgHom.toRingHom := by
  rw [CommHopfAlgCat.le_commonKernelHopfIdeal_iff]
  constructor
  · intro h
    exact ⟨fun i ↦ h (.inl i), h (.inr ())⟩
  · rintro ⟨hroot, htorus⟩ (i | ⟨⟩)
    · exact hroot i
    · exact htorus

/-- The generated positive subgroup lies in the full generated minuscule carrier. -/
theorem generatedDefiningIdeal_le : generatedDefiningIdeal A ≤ definingIdeal A := by
  rw [le_definingIdeal_iff]
  exact ⟨fun i ↦ generatedDefiningIdeal_toIdeal_le_ker A (.inl (.inl i)),
    generatedDefiningIdeal_toIdeal_le_ker A (.inr ())⟩

/-- The coordinate Hopf algebra of the positive subgroup generated over the ground ring.
It is the quotient of the `GL₅₆` coordinate algebra by the common-kernel ideal `definingIdeal`.
The positive root and weight-torus coordinate maps factor through this quotient. -/
abbrev coordinateHopfAlgebra : CommHopfAlgCat A :=
  CommHopfAlgCat.quotient (GeneralLinear.coordinateHopfAlgebra A 56) (definingIdeal A)

/-- Restriction of the full generated carrier's coordinates to the positive subgroup. -/
def restriction : generatedCoordinateHopfAlgebra A ⟶ coordinateHopfAlgebra A :=
  (eqToIso (generatedCoordinateHopfAlgebra_def A)).hom ≫
    CommHopfAlgCat.quotientMapOfLe _ (generatedDefiningIdeal_le A)

/-- Restricting the ambient quotient coordinates recovers the positive quotient map. -/
@[reassoc (attr := simp)]
theorem generatedCoordinateMap_comp_restriction :
    generatedCoordinateMap A ≫ restriction A =
      CommHopfAlgCat.mkQuotient _ (definingIdeal A) := by
  rw [restriction, ← Category.assoc, generatedCoordinateMap_comp_eqToIso_hom]
  exact CommHopfAlgCat.mkQuotient_comp_quotientMapOfLe
    (GeneralLinear.coordinateHopfAlgebra A 56) (generatedDefiningIdeal_le A)

/-- Restriction to the positive subgroup is surjective, so it defines a closed immersion. -/
theorem restriction_surjective : Function.Surjective (restriction A).hom := by
  have h := CommHopfAlgCat.mkQuotient_surjective
    (GeneralLinear.coordinateHopfAlgebra A 56) (definingIdeal A)
  rw [← generatedCoordinateMap_comp_restriction] at h
  exact Function.Surjective.of_comp h

/-- The positive subgroup's defining ideal inside the full generated carrier: the common
kernel of the positive numbered root and weight-torus coordinate lifts. -/
def carrierDefiningIdeal : HopfIdeal A (generatedCoordinateHopfAlgebra A) :=
  CommHopfAlgCat.commonKernelHopfIdeal fun j : Fin 7 ⊕ Unit ↦
    generatedCoordinateLift A (match j with
      | .inl i => .inl (.inl i)
      | .inr u => .inr u)

/-- The positive subgroup's defining ideal is the kernel of restriction to it. -/
theorem kerOfSurjective_restriction :
    HopfIdeal.kerOfSurjective (restriction A).hom (restriction_surjective A) =
      carrierDefiningIdeal A :=
  CommHopfAlgCat.kerOfSurjective_eq_commonKernelHopfIdeal_of_comp (generatedCoordinateMap A)
    (generatedCoordinateMap_surjective A) (generator A) _
    (by rintro (i | ⟨⟩) <;> exact generatedCoordinateMap_comp_generatedCoordinateLift A _)
    (restriction A) (generatedCoordinateMap_comp_restriction A)

@[simp]
theorem mem_carrierDefiningIdeal (x : generatedCoordinateHopfAlgebra A) :
    x ∈ carrierDefiningIdeal A ↔ (restriction A).hom x = 0 := by
  rw [← kerOfSurjective_restriction, HopfIdeal.mem_kerOfSurjective]

/-- The full carrier's generators restrict to the positive subgroup's generator lifts. -/
@[reassoc (attr := simp)]
theorem restriction_comp_commonKernelLift (j : Fin 7 ⊕ Unit) :
    restriction A ≫ CommHopfAlgCat.commonKernelLift (generator A) j =
      generatedCoordinateLift A (match j with
        | .inl i => .inl (.inl i)
        | .inr u => .inr u) := by
  apply generatedCoordinateLift_unique
  rw [← Category.assoc, generatedCoordinateMap_comp_restriction,
    CommHopfAlgCat.mkQuotient_comp_commonKernelLift]
  cases j <;> rfl

/-- The positive subgroup contains every positive numbered root subgroup and the weight torus. -/
theorem carrierDefiningIdeal_toIdeal_le_ker_generatedCoordinateLift (j : Fin 7 ⊕ Unit) :
    (carrierDefiningIdeal A).toIdeal ≤ RingHom.ker
      (generatedCoordinateLift A (match j with
        | .inl i => .inl (.inl i)
        | .inr u => .inr u)).hom.toAlgHom.toRingHom :=
  CommHopfAlgCat.commonKernelHopfIdeal_toIdeal_le_ker _ j

/-- A Hopf ideal of the generated carrier lies below the positive subgroup's defining ideal
exactly when the positive numbered root and weight-torus coordinate lifts kill it. -/
theorem le_carrierDefiningIdeal_iff (I : HopfIdeal A (generatedCoordinateHopfAlgebra A)) :
    I ≤ carrierDefiningIdeal A ↔
      ∀ j : Fin 7 ⊕ Unit, I.toIdeal ≤ RingHom.ker
        (generatedCoordinateLift A (match j with
          | .inl i => .inl (.inl i)
          | .inr u => .inr u)).hom.toAlgHom.toRingHom :=
  CommHopfAlgCat.le_commonKernelHopfIdeal_iff _ I

variable (k : Type u) [Field k]

/-- The positive subgroup generated over any field is smooth, including over imperfect fields. -/
theorem smooth_coordinateHopfAlgebra :
    smoothCommHopfAlgProperty k (coordinateHopfAlgebra k) := by
  let : ∀ j, Algebra.IsGeometricallyReduced k (generatorCodomain k j) := fun j ↦
    isGeometricallyReduced_generatorCoordinateAlgebra k (match j with
      | .inl i => .inl (.inl i)
      | .inr u => .inr u)
  exact
    CommHopfAlgCat.smoothCommHopfAlgProperty_quotient_commonKernelHopfIdeal_of_geometricallyReduced
      (generator k)

/-- The positive subgroup generated over any field is geometrically connected. -/
theorem geometricallyConnected_coordinateHopfAlgebra :
    geometricallyConnectedCommHopfAlgProperty k (coordinateHopfAlgebra k) := by
  exact geometricallyConnectedCommHopfAlgProperty_commonKernelQuotient_of_geometricallyConnected
    (generator k) (fun j ↦ geometricallyConnected_generatorCoordinateAlgebra k (match j with
      | .inl i => .inl (.inl i)
      | .inr u => .inr u))

end

end TauCeti.E7Minuscule.Generated.Positive
