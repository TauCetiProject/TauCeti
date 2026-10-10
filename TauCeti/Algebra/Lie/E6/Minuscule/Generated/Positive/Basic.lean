/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.E6.Minuscule.Generated.Basic
public import TauCeti.Algebra.AlgebraicGroup.Connected.Generated
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.CommonKernel.GeometricallyReduced
import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.SmoothConnected
import TauCeti.RingTheory.Smooth.GeometricallyReduced

/-!
# The positive subgroup generated over a field in the E₆ minuscule carrier

The six positive numbered root subgroups and the rank-six weight torus generate a closed
subgroup of the generated minuscule E₆ group. Its coordinate algebra is the quotient by the
largest Hopf ideal killed by those seven coordinate maps. Over any field this positive subgroup
is smooth and geometrically connected. The restriction of carrier coordinates is surjective,
and the positive root and torus maps factor through it.

This construction generates the subgroup over the chosen ground ring. It is not identified
with the specialization of the integral positive subsystem, or with a Borel of the pinned
simply connected E₆ group. These comparisons require additional results.

## References

* J. S. Milne, *Algebraic Groups* (2017), §2.h and Chapter 17.
* J. E. Humphreys, *Linear Algebraic Groups*, §§26–28.
* Related formalization: `TauCeti.Algebra.Lie.G2.ShortRoot.PrimeField.Positive.Basic`.
-/

public section

open CategoryTheory
open TauCeti.CommHopfAlgCat
  (geometricallyConnectedCommHopfAlgProperty_commonKernelQuotient_of_geometricallyConnected)

namespace TauCeti.E6Minuscule.Generated.Positive

universe u

noncomputable section

variable (A : Type u) [CommRing A]

/-- The coordinate algebras of the positive numbered roots and the weight torus. -/
abbrev generatorCodomain (j : Fin 6 ⊕ Unit) : CommHopfAlgCat A :=
  generatorCoordinateAlgebra A (match j with
    | .inl i => .inl (.inl i)
    | .inr u => .inr u)

/-- The positive root and weight-torus coordinate maps into `GL₂₇`. -/
def generator : ∀ j, GeneralLinear.coordinateHopfAlgebra A 27 ⟶ generatorCodomain A j
  | .inl i => generatorCoordinateMap A (.inl (.inl i))
  | .inr u => generatorCoordinateMap A (.inr u)

@[simp]
theorem generator_inl (i : Fin 6) :
    generator A (.inl i) = generatorCoordinateMap A (.inl (.inl i)) := (rfl)

@[simp]
theorem generator_inr : generator A (.inr ()) = generatorCoordinateMap A (.inr ()) := (rfl)

/-- The largest Hopf ideal in the `GL₂₇` coordinate algebra killed by the six positive numbered
root coordinate maps and the weight-torus coordinate map. It defines the smallest closed
subgroup containing those roots and the torus, as characterized by `le_definingIdeal_iff`. -/
abbrev definingIdeal : HopfIdeal A (GeneralLinear.coordinateHopfAlgebra A 27) :=
  CommHopfAlgCat.commonKernelHopfIdeal (generator A)

/-- The positive subgroup is the smallest closed subgroup containing the six positive numbered
roots and the torus, expressed contravariantly on defining ideals. -/
theorem le_definingIdeal_iff (I : HopfIdeal A (GeneralLinear.coordinateHopfAlgebra A 27)) :
    I ≤ definingIdeal A ↔
      (∀ i : Fin 6, I.toIdeal ≤ RingHom.ker
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
It is the quotient of the `GL₂₇` coordinate algebra by the common-kernel ideal `definingIdeal`.
The positive root and weight-torus coordinate maps factor through this quotient. -/
abbrev coordinateHopfAlgebra : CommHopfAlgCat A :=
  CommHopfAlgCat.quotient (GeneralLinear.coordinateHopfAlgebra A 27) (definingIdeal A)

/-- Restriction of the full generated carrier's coordinates to the positive subgroup. -/
def restriction : generatedCoordinateHopfAlgebra A ⟶ coordinateHopfAlgebra A :=
  generatedCoordinateDesc A (CommHopfAlgCat.mkQuotient _ (definingIdeal A)) (by
    rw [CommHopfAlgCat.mkQuotient_ker]
    exact generatedDefiningIdeal_le A)

/-- Restricting the ambient quotient coordinates recovers the positive quotient map. -/
@[reassoc (attr := simp)]
theorem generatedCoordinateMap_comp_restriction :
    generatedCoordinateMap A ≫ restriction A =
      CommHopfAlgCat.mkQuotient _ (definingIdeal A) :=
  generatedCoordinateMap_comp_generatedCoordinateDesc A _ _

/-- Restriction to the positive subgroup is surjective, so it defines a closed immersion. -/
theorem restriction_surjective : Function.Surjective (restriction A).hom := by
  have h := CommHopfAlgCat.mkQuotient_surjective
    (GeneralLinear.coordinateHopfAlgebra A 27) (definingIdeal A)
  rw [← generatedCoordinateMap_comp_restriction] at h
  exact Function.Surjective.of_comp h

/-- The positive subgroup's defining ideal inside the full generated carrier. -/
def carrierDefiningIdeal : HopfIdeal A (generatedCoordinateHopfAlgebra A) :=
  HopfIdeal.kerOfSurjective (restriction A).hom (restriction_surjective A)

@[simp]
theorem mem_carrierDefiningIdeal (x : generatedCoordinateHopfAlgebra A) :
    x ∈ carrierDefiningIdeal A ↔ (restriction A).hom x = 0 :=
  HopfIdeal.mem_kerOfSurjective _ _

/-- The full carrier's generators restrict to the positive subgroup's generator lifts. -/
@[reassoc (attr := simp)]
theorem restriction_comp_commonKernelLift (j : Fin 6 ⊕ Unit) :
    restriction A ≫ CommHopfAlgCat.commonKernelLift (generator A) j =
      generatedCoordinateLift A (match j with
        | .inl i => .inl (.inl i)
        | .inr u => .inr u) := by
  apply generatedCoordinateLift_unique
  rw [← Category.assoc, generatedCoordinateMap_comp_restriction,
    CommHopfAlgCat.mkQuotient_comp_commonKernelLift]
  cases j <;> rfl

/-- The positive subgroup contains every positive numbered root subgroup and the weight torus. -/
theorem carrierDefiningIdeal_toIdeal_le_ker_generatedCoordinateLift (j : Fin 6 ⊕ Unit) :
    (carrierDefiningIdeal A).toIdeal ≤ RingHom.ker
      (generatedCoordinateLift A (match j with
        | .inl i => .inl (.inl i)
        | .inr u => .inr u)).hom.toAlgHom.toRingHom := by
  intro x hx
  rw [HopfIdeal.mem_toIdeal, mem_carrierDefiningIdeal] at hx
  rw [RingHom.mem_ker, ← restriction_comp_commonKernelLift]
  simpa only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
    _root_.CommHopfAlgCat.hom_comp, BialgHom.coe_toAlgHom, BialgHom.coe_comp,
    Function.comp_apply, map_zero] using
    congrArg (CommHopfAlgCat.commonKernelLift (generator A) j).hom hx

variable (k : Type u) [Field k]

/-- The positive subgroup generated over any field is smooth, including over imperfect fields. -/
theorem smooth_coordinateHopfAlgebra :
    smoothCommHopfAlgProperty k (coordinateHopfAlgebra k) := by
  let : ∀ j, Algebra.IsGeometricallyReduced k (generatorCodomain k j) := by
    rintro (i | ⟨⟩)
    · exact isGeometricallyReduced_of_smooth k _
    · exact (DiagonalizableGroup.geometricallyReduced_coordinateRing k
        (SplitTorus.characterGroup (Fin 6))).isGeometricallyReduced
  exact
    CommHopfAlgCat.smoothCommHopfAlgProperty_quotient_commonKernelHopfIdeal_of_geometricallyReduced
      (generator k)

/-- The positive subgroup generated over any field is geometrically connected. -/
theorem geometricallyConnected_coordinateHopfAlgebra :
    geometricallyConnectedCommHopfAlgProperty k (coordinateHopfAlgebra k) := by
  apply geometricallyConnectedCommHopfAlgProperty_commonKernelQuotient_of_geometricallyConnected
    (generator k)
  rintro (i | ⟨⟩)
  · rw [geometricallyConnectedCommHopfAlgProperty_iff_connectedSpace_of_isAlgClosed]
    intro K _ _ _
    have := AdditiveGroup.connectedSpace_primeSpectrum_baseChange_coordinateHopfAlgebra k K
    let e := Algebra.TensorProduct.comm k (AdditiveGroup.coordinateHopfAlgebra k) K
    exact connectedSpace_primeSpectrum_of_injective e.toRingHom e.injective
  · exact DiagonalizableGroup.geometricallyConnected_coordinateRing k
      (SplitTorus.characterGroup (Fin 6))

end

end TauCeti.E6Minuscule.Generated.Positive
