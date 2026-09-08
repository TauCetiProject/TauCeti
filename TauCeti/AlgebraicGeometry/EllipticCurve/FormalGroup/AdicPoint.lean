/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.PairEval
-- Public: `AddGroup.ofLeftAxioms` is an `abbrev`, so the group instance's exposed body names it
-- and a private import would not make it available.
public import Mathlib.Algebra.Group.MinimalAxioms

/-!
# Points of a Weierstrass formal group in an adic ideal

Let `I` be an adic ideal of a complete linearly topologised ring `O`. The elements of `I` form an
additive commutative group under evaluation of the Weierstrass formal group law: addition is
`F(t₁, t₂)` and negation is the formal inverse `ι(t)`. This file packages that group as
`WeierstrassCurve.FormalGroupPoint W I`.

The wrapper is necessary because the subtype `I` already carries the ordinary addition inherited
from `O`, whereas the addition here is the generally different formal-group operation. The
assumption that `I` is adic is carried as `Fact (IsAdic I)`: it makes every parameter evaluable and
keeps addition and negation inside `I`.

This is only the parameter group. Mapping it into the points of the Weierstrass curve uses
`WeierstrassCurve.formalPoint`; proving that map additive requires comparing the formal law with
the geometric chord-and-tangent law.

## Main definitions

* `WeierstrassCurve.FormalGroupPoint`: a parameter in an adic ideal, equipped with the Weierstrass
  formal group law.

## Main results

* `WeierstrassCurve.FormalGroupPoint.instAddCommGroup`: the evaluated formal law makes these
  parameters an additive commutative group.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], IV.1.

## Provenance

The packaging follows Michael Stoll's elliptic-curve development
(`github.com/MichaelStollBayreuth/EllipticCurves` @ `66889eada51a`, Apache-2.0), file
`EllipticCurves/Mathlib/Chabauty/FormalGroupLaw/Points.lean`, definition
`ChabautyColeman.FormalGroupLaw.Points` and its `AddCommMonoid` instance. That source treats a
multivariable formal group law on the maximal ideal of a local ring and does not construct
inverses. Here the one-dimensional Weierstrass law is evaluated on an arbitrary adic ideal, and its
already-constructed formal inverse upgrades the result to an additive commutative group.
-/

public section

open PowerSeries

namespace WeierstrassCurve

variable {O : Type*} [CommRing O] [UniformSpace O] [IsUniformAddGroup O] [CompleteSpace O]
  [T2Space O] [IsTopologicalRing O] [IsLinearTopology O O]

/-- A point of the formal group of a Weierstrass curve, with parameter in the adic ideal `I`.

This is a newtype rather than the ideal subtype itself: `I` already uses the ordinary addition of
`O`, while `FormalGroupPoint W I` uses evaluation of `W.formalAdd`. -/
@[ext]
structure FormalGroupPoint (W : WeierstrassCurve O) (I : Ideal O) where
  /-- The parameter of a formal-group point. -/
  val : O
  /-- The parameter belongs to the ideal on which the formal law is evaluated. -/
  property : val ∈ I

namespace FormalGroupPoint

variable {W : WeierstrassCurve O} {I : Ideal O}

/-- A formal-group point coerces to its parameter in the coefficient ring. -/
instance : CoeOut (FormalGroupPoint W I) O := ⟨val⟩

omit [UniformSpace O] [IsUniformAddGroup O] [CompleteSpace O] [T2Space O]
  [IsTopologicalRing O] [IsLinearTopology O O] in
/-- The parameter of a formal-group point constructed from `t` is `t`. -/
@[simp]
theorem coe_mk (t : O) (ht : t ∈ I) : ((⟨t, ht⟩ : FormalGroupPoint W I) : O) = t := rfl

omit [UniformSpace O] [IsUniformAddGroup O] [CompleteSpace O] [T2Space O]
  [IsTopologicalRing O] [IsLinearTopology O O] in
/-- Two formal-group points are equal exactly when their parameters are equal. -/
@[simp]
theorem coe_inj {P Q : FormalGroupPoint W I} : (P : O) = Q ↔ P = Q := by
  constructor
  · exact fun h ↦ FormalGroupPoint.ext h
  · exact fun h ↦ congrArg val h

omit [IsUniformAddGroup O] [CompleteSpace O] [T2Space O] [IsTopologicalRing O]
  [IsLinearTopology O O] in
/-- A parameter in an adic ideal is an admissible evaluation point for a power series. -/
theorem hasEval [Fact (IsAdic I)] (P : FormalGroupPoint W I) : PowerSeries.HasEval (P : O) :=
  (Fact.out : IsAdic I).isTopologicallyNilpotent_of_mem P.property

/-- The zero parameter is the identity formal-group point. -/
instance : Zero (FormalGroupPoint W I) := ⟨⟨0, I.zero_mem⟩⟩

omit [UniformSpace O] [IsUniformAddGroup O] [CompleteSpace O] [T2Space O]
  [IsTopologicalRing O] [IsLinearTopology O O] in
@[simp]
theorem coe_zero : (((0 : FormalGroupPoint W I) : O)) = 0 := rfl

/-- Addition of formal-group points is evaluation of the Weierstrass formal group law. -/
noncomputable instance [Fact (IsAdic I)] : Add (FormalGroupPoint W I) :=
  ⟨fun P Q ↦ ⟨W.formalAddEval P Q, by
    simpa using W.formalAddEval_mem (I := I) (Fact.out : IsAdic I) (k := 1)
      (by simpa using P.property) (by simpa using Q.property)⟩⟩

@[simp]
theorem coe_add [Fact (IsAdic I)] (P Q : FormalGroupPoint W I) :
    ((P + Q : FormalGroupPoint W I) : O) = W.formalAddEval P Q := (rfl)

/-- Negation of a formal-group point is evaluation of the formal inverse. -/
noncomputable instance [Fact (IsAdic I)] : Neg (FormalGroupPoint W I) :=
  ⟨fun P ↦ ⟨W.formalInverseEval P, by
    simpa using W.formalInverseEval_mem (I := I) (k := 1) P.hasEval
      (by simpa using P.property)⟩⟩

@[simp]
theorem coe_neg [Fact (IsAdic I)] (P : FormalGroupPoint W I) :
    ((-P : FormalGroupPoint W I) : O) = W.formalInverseEval P := (rfl)

/-- The elements of an adic ideal form an additive commutative group under the evaluated Weierstrass
formal group law. -/
noncomputable instance instAddCommGroup [Fact (IsAdic I)] :
    AddCommGroup (FormalGroupPoint W I) :=
  { AddGroup.ofLeftAxioms (fun P Q S ↦ by
        ext
        simpa only [coe_add] using W.formalAddEval_assoc P.hasEval Q.hasEval S.hasEval)
      (fun P ↦ by
        ext
        simpa only [coe_add, coe_zero] using W.formalAddEval_zero_left P.hasEval)
      (fun P ↦ by
        ext
        simp only [coe_add, coe_neg, coe_zero]
        exact (W.formalAddEval_comm (-P).hasEval P.hasEval).trans
          (W.formalAddEval_formalInverseEval P.hasEval
            (W.hasEval_formalInverseEval (Fact.out : IsAdic I) P.property))) with
    add_comm := fun P Q ↦ by
      ext
      simpa only [coe_add] using W.formalAddEval_comm P.hasEval Q.hasEval }

end FormalGroupPoint

end WeierstrassCurve
