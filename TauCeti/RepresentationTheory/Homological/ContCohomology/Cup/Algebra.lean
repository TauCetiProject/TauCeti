/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.Action.Basic
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.Graded.Basic
public import TauCeti.RepresentationTheory.Homological.ContCohomology.SmoothDiscrete.DiscreteRing

/-!
# The multiplication pairing of a discrete `G`-algebra

When a monoid `G` acts on a discrete `R`-algebra `A` by `R`-algebra endomorphisms
(`MulSemiringAction G A` and `SMulCommClass G R A`), algebra multiplication `LinearMap.mul R A` is
jointly continuous and `G`-equivariant, hence defines a coefficient pairing `TauCeti.TopPairing` on
`TauCeti.ofDiscreteModule R G A` (`TauCeti.ofDiscreteModuleMulPairing`) and, when `R` is discrete
and the `G`-action is continuous, on `TauCeti.SmoothDiscreteTopRep.of R G A`
(`TauCeti.SmoothDiscreteTopRep.ofMulPairing`).

No commutativity of `A` is needed for the pairing itself; when `A` is commutative, the carrier
projections inherit `CommMonoid` instances as well. Over `R = ℤ`, continuity of scalar
multiplication holds automatically for every discrete `G`-ring `A`, generalizing
`TauCeti.ofDiscreteModulePairing` at `AddMonoidHom.mul` to `R`-algebras over any commutative
topological ring `R`.

## Main definitions

* `TauCeti.ofDiscreteModuleMulPairing`: algebra multiplication on a discrete `G`-algebra `A` as a
  `TauCeti.TopPairing` on `ofDiscreteModule R G A`.
* `TauCeti.SmoothDiscreteTopRep.ofMulPairing`: the same pairing on
  `(SmoothDiscreteTopRep.of R G A).obj` over a discrete commutative ring `R`.
-/

public section

universe u v w

namespace TauCeti

section GeneralRing

variable (R : Type u) [CommRing R] [TopologicalSpace R]
  (G : Type v) [Monoid G]
  (A : Type w) [Ring A] [Algebra R A] [TopologicalSpace A] [DiscreteTopology A]
  [MulSemiringAction G A] [SMulCommClass G R A] [ContinuousSMul R A]

/-- The underlying module of `ofDiscreteModule R G A` inherits the monoid structure of `A` at
instance transparency. -/
instance instMonoidOfDiscreteModuleV : Monoid (ofDiscreteModule R G A).V :=
  inferInstanceAs (Monoid A)

/-- Algebra multiplication on a discrete `G`-algebra `A` as a `TauCeti.TopPairing` on
`ofDiscreteModule R G A`. For `R = ℤ`, continuity of scalar multiplication holds automatically for
every discrete `G`-ring `A`. -/
def ofDiscreteModuleMulPairing :
    TopPairing (ofDiscreteModule R G A) (ofDiscreteModule R G A) (ofDiscreteModule R G A) where
  bil := LinearMap.mul R A
  cont := continuous_of_discreteTopology
  equivariant g (x y : A) := (smul_mul' g x y).symm

/-- The bilinear map underlying `ofDiscreteModuleMulPairing` is `LinearMap.mul R A`. -/
@[simp]
theorem ofDiscreteModuleMulPairing_bil :
    (ofDiscreteModuleMulPairing R G A).bil = LinearMap.mul R A :=
  (rfl)

/-- Evaluating `ofDiscreteModuleMulPairing` multiplies elements in `A`.

This is not a simp lemma: `ofDiscreteModuleMulPairing_bil` already simplifies its left-hand side. -/
theorem ofDiscreteModuleMulPairing_bil_apply (x y : A) :
    (ofDiscreteModuleMulPairing R G A).bil x y = x * y :=
  (rfl)

end GeneralRing

/-- When `A` is commutative, the underlying module of `ofDiscreteModule R G A` inherits the
commutative monoid structure of `A` at instance transparency. -/
instance instCommMonoidOfDiscreteModuleV
    (R : Type u) [CommRing R] [TopologicalSpace R]
    (G : Type v) [Monoid G]
    (A : Type w) [CommRing A] [Algebra R A] [TopologicalSpace A] [DiscreteTopology A]
    [MulSemiringAction G A] [SMulCommClass G R A] [ContinuousSMul R A] :
    CommMonoid (ofDiscreteModule R G A).V :=
  inferInstanceAs (CommMonoid A)

namespace SmoothDiscreteTopRep

section DiscreteRing

variable (R : Type u) [CommRing R] [TopologicalSpace R] [DiscreteTopology R]
  (G : Type v) [Monoid G] [TopologicalSpace G]
  (A : Type w) [Ring A] [Algebra R A] [TopologicalSpace A] [DiscreteTopology A]
  [MulSemiringAction G A] [SMulCommClass G R A] [ContinuousSMul G A]

/-- The underlying module of `(SmoothDiscreteTopRep.of R G A).obj` inherits the monoid structure
of `A` at instance transparency. -/
instance instMonoidOfV : Monoid (SmoothDiscreteTopRep.of R G A).obj.V :=
  inferInstanceAs (Monoid A)

/-- Algebra multiplication on a discrete `G`-algebra `A` over a discrete commutative ring `R`, as a
`TauCeti.TopPairing` on `(SmoothDiscreteTopRep.of R G A).obj`. Continuity of scalar multiplication
by `R` holds automatically because both `R` and `A` are discrete; when a `ContinuousSMul R A`
instance is already in scope (for instance at `R = ℤ`), this agrees with
`ofDiscreteModuleMulPairing R G A` by `rfl`. -/
def ofMulPairing :
    TopPairing (SmoothDiscreteTopRep.of R G A).obj (SmoothDiscreteTopRep.of R G A).obj
      (SmoothDiscreteTopRep.of R G A).obj :=
  letI : ContinuousSMul R A := ⟨continuous_of_discreteTopology⟩
  ofDiscreteModuleMulPairing R G A

/-- The bilinear map underlying `SmoothDiscreteTopRep.ofMulPairing` is `LinearMap.mul R A`. -/
@[simp]
theorem ofMulPairing_bil :
    (ofMulPairing R G A).bil = LinearMap.mul R A :=
  (rfl)

/-- Evaluating `SmoothDiscreteTopRep.ofMulPairing` multiplies elements in `A`.

This is not a simp lemma: `ofMulPairing_bil` already simplifies its left-hand side. -/
theorem ofMulPairing_bil_apply (x y : A) :
    (ofMulPairing R G A).bil x y = x * y :=
  (rfl)

end DiscreteRing

/-- When `A` is commutative, the underlying module of `(SmoothDiscreteTopRep.of R G A).obj`
inherits the commutative monoid structure of `A` at instance transparency. -/
instance instCommMonoidOfV
    (R : Type u) [CommRing R] [TopologicalSpace R] [DiscreteTopology R]
    (G : Type v) [Monoid G] [TopologicalSpace G]
    (A : Type w) [CommRing A] [Algebra R A] [TopologicalSpace A] [DiscreteTopology A]
    [MulSemiringAction G A] [SMulCommClass G R A] [ContinuousSMul G A] :
    CommMonoid (SmoothDiscreteTopRep.of R G A).obj.V :=
  inferInstanceAs (CommMonoid A)

end SmoothDiscreteTopRep

end TauCeti
