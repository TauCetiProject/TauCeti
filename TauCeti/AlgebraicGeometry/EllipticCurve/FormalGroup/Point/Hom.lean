/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.AdicPoint
public import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Point.Add

/-!
# The formal parameter map is additive

For an adic ideal `I` of a complete ring `O` mapping injectively to a field `K`, the Weierstrass
formal group law makes its elements into `WeierstrassCurve.FormalGroupPoint W I`.  The usual
parametrisation sends zero to the point at infinity and, for a nonzero parameter, is given by

`t ↦ (t / w(t), -1 / w(t))`

This file proves that this map is an additive homomorphism into the points of the base-changed
curve whenever every parameter distinct from its inverse admits an auxiliary parameter distinct
from it, its inverse, and its own inverse.

## Main definitions

* `WeierstrassCurve.formalPointHom`: the additive homomorphism from formal-group parameters in an
  adic ideal to points of the curve over a field.

## Main results

* `WeierstrassCurve.formalPoint_add`: the parametrisation preserves addition when auxiliary
  parameters exist.
* `WeierstrassCurve.formalPointHom_injective`: the resulting homomorphism is injective.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], IV.1 and VII.2.

## Provenance

Adapted from Michael Stoll's elliptic-curve development
(`github.com/MichaelStollBayreuth/EllipticCurves` @ `66889eada51a`, Apache-2.0), files
`EllipticCurves/WeierstrassFormalGroup/Foundations.lean` and
`EllipticCurves/WeierstrassFormalGroup/Filtration.lean`, declarations `exists_aux_param`,
`exists_aux_point`, `formalPoint_add_self` and `formalPoint_add`.  The source works with its own
multivariable formal-group points; here the argument is rebased onto
`WeierstrassCurve.FormalGroupPoint` and the one-dimensional formal-group API already in Mathlib and
Tau Ceti.
-/

public section

namespace WeierstrassCurve

section PointMap

variable {O : Type*} [CommRing O] [UniformSpace O] [IsUniformAddGroup O] [CompleteSpace O]
  [T2Space O] [IsTopologicalRing O] [IsLinearTopology O O]
  {S : Type*} [Field S] [Algebra O S] [FaithfulSMul O S]
  (I : Ideal O) [Fact (IsAdic I)] (E : WeierstrassCurve O) [(E.baseChange S).IsElliptic]

private noncomputable def formalPointMap (P : FormalGroupPoint E I) :
    (E.baseChange S).toAffine.Point :=
  E.formalPoint (K := S) (Fact.out : IsAdic I) P.property

private theorem formalPointMap_injective :
    Function.Injective (formalPointMap (S := S) I E) := by
  intro P Q hPQ
  have hPQ' : E.formalPoint (K := S) (Fact.out : IsAdic I) P.property =
      E.formalPoint (K := S) (Fact.out : IsAdic I) Q.property := by
    simpa only [formalPointMap] using hPQ
  have hinj := E.formalPoint_injective (K := S) (Fact.out : IsAdic I)
  have heq := hinj (a₁ := (⟨P.val, P.property⟩ : I))
    (a₂ := (⟨Q.val, Q.property⟩ : I)) hPQ'
  exact FormalGroupPoint.ext (congrArg Subtype.val heq)

private theorem formalPointMap_neg (P : FormalGroupPoint E I) :
    formalPointMap (S := S) I E (-P) = -formalPointMap (S := S) I E P := by
  simp only [formalPointMap, FormalGroupPoint.coe_neg]
  exact E.formalPoint_formalInverseEval (Fact.out : IsAdic I) P.property

open Classical in
private theorem formalPointMap_add_of_ne (P Q : FormalGroupPoint E I)
    (hne : Q ≠ P) (hnneg : Q ≠ -P) :
    formalPointMap (S := S) I E (P + Q) =
      formalPointMap (S := S) I E P + formalPointMap (S := S) I E Q := by
  exact (E.add_eq_formalPoint_formalAddEval_of_ne_of_ne_formalInverseEval
    (K := S) (Fact.out : IsAdic I) P.property Q.property
    (fun _ _ h ↦ hne (FormalGroupPoint.ext h))
    (fun _ _ h ↦ hnneg (FormalGroupPoint.ext (by simpa using h)))).symm

open Classical in
private theorem formalPointMap_add_self (P : FormalGroupPoint E I) (hself : P ≠ -P)
    (haux : ∃ U : FormalGroupPoint E I, U ≠ P ∧ U ≠ -P ∧ U ≠ -U) :
    formalPointMap (S := S) I E (P + P) =
      formalPointMap (S := S) I E P + formalPointMap (S := S) I E P := by
  obtain ⟨U, hUP, hUnP, hUnegn⟩ := haux
  have hnUP : -U ≠ P := fun h ↦ hUnP (by simpa using congrArg Neg.neg h)
  have hnUnP : -U ≠ -P := fun h ↦ hUP (neg_injective h)
  have c1 := formalPointMap_add_of_ne (S := S) I E P U hUP hUnP
  have c2 := formalPointMap_add_of_ne (S := S) I E P (-U) hnUP hnUnP
  have hne : P + -U ≠ P + U := by
    intro h
    have h' := congrArg (formalPointMap (S := S) I E) h
    rw [c1, c2] at h'
    exact hUnegn (formalPointMap_injective (S := S) I E (add_left_cancel h').symm)
  have hnneg : P + -U ≠ -(P + U) := by
    intro h
    have h' := congrArg (formalPointMap (S := S) I E) h
    rw [c2, formalPointMap_neg (S := S) I E, formalPointMap_neg (S := S) I E,
      c1, neg_add] at h'
    have h'' := add_right_cancel h'
    rw [← formalPointMap_neg (S := S) I E] at h''
    exact hself (formalPointMap_injective (S := S) I E h'')
  have c3 := formalPointMap_add_of_ne (S := S) I E (P + U) (P + -U) hne hnneg
  have hkey : (P + U) + (P + -U) = P + P := by abel
  rw [← hkey, c3, c1, c2, formalPointMap_neg (S := S) I E]
  abel

open Classical in
/-- **The formal parametrisation preserves addition** whenever every parameter distinct from its
inverse has an auxiliary parameter distinct from it, its inverse, and the auxiliary parameter's
own inverse. -/
theorem formalPoint_add
    (haux : ∀ P : FormalGroupPoint E I, P ≠ -P →
      ∃ U : FormalGroupPoint E I, U ≠ P ∧ U ≠ -P ∧ U ≠ -U)
    (P Q : FormalGroupPoint E I) :
    E.formalPoint (K := S) (Fact.out : IsAdic I) (P + Q).property =
      E.formalPoint (K := S) (Fact.out : IsAdic I) P.property +
        E.formalPoint (K := S) (Fact.out : IsAdic I) Q.property := by
  suffices h : formalPointMap (S := S) I E (P + Q) =
      formalPointMap (S := S) I E P + formalPointMap (S := S) I E Q by
    simpa only [formalPointMap] using h
  rcases eq_or_ne P 0 with rfl | hP0
  · simp [formalPointMap]
  rcases eq_or_ne Q 0 with rfl | hQ0
  · simp [formalPointMap]
  rcases eq_or_ne Q (-P) with rfl | hQneg
  · rw [add_neg_cancel, formalPointMap_neg (S := S) I E]
    simp [formalPointMap]
  rcases eq_or_ne Q P with hQP | hQP
  · subst Q
    exact formalPointMap_add_self (S := S) I E P hQneg (haux P hQneg)
  · exact formalPointMap_add_of_ne (S := S) I E P Q hQP hQneg

open Classical in
/-- **The formal parameter map into the curve's points**, as an additive homomorphism whenever
the required auxiliary parameters exist. -/
noncomputable def formalPointHom
    (haux : ∀ P : FormalGroupPoint E I, P ≠ -P →
      ∃ U : FormalGroupPoint E I, U ≠ P ∧ U ≠ -P ∧ U ≠ -U) :
    FormalGroupPoint E I →+ (E.baseChange S).toAffine.Point where
  toFun := formalPointMap (S := S) I E
  map_zero' := by simp [formalPointMap]
  map_add' := formalPoint_add I E haux

open Classical in
/-- The formal point homomorphism evaluates to the usual formal parametrisation. -/
@[simp]
theorem formalPointHom_apply
    (haux : ∀ P : FormalGroupPoint E I, P ≠ -P →
      ∃ U : FormalGroupPoint E I, U ≠ P ∧ U ≠ -P ∧ U ≠ -U)
    (P : FormalGroupPoint E I) :
    E.formalPointHom I haux P =
      E.formalPoint (K := S) (Fact.out : IsAdic I) P.property :=
  (rfl)

open Classical in
/-- **The formal point homomorphism is injective.** -/
theorem formalPointHom_injective
    (haux : ∀ P : FormalGroupPoint E I, P ≠ -P →
      ∃ U : FormalGroupPoint E I, U ≠ P ∧ U ≠ -P ∧ U ≠ -U) :
    Function.Injective (E.formalPointHom (S := S) I haux) :=
  formalPointMap_injective (S := S) I E

end PointMap

end WeierstrassCurve

end
