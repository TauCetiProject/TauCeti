/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.Graded.Basic
public import TauCeti.Topology.Algebra.MulAction.Discrete

/-!
# The multiplication pairing of a discrete `G`-algebra

When a monoid `G` acts on a discrete `R`-algebra `A` by `R`-algebra endomorphisms
(`MulSemiringAction G A` and `SMulCommClass G R A`), algebra multiplication `LinearMap.mul R A` is
jointly continuous and `G`-equivariant, hence defines a coefficient pairing `TauCeti.TopPairing` on
`TauCeti.ofDiscreteModule R G A` (`TauCeti.ofDiscreteModuleMulPairing`) and, when `R` is discrete
and the `G`-action is continuous, on `TauCeti.SmoothDiscreteTopRep.of R G A`
(`TauCeti.SmoothDiscreteTopRep.ofMulPairing`).

No commutativity of `A` is needed for the pairing itself; when `A` is commutative, the pairing is
symmetric (`TauCeti.ofDiscreteModuleMulPairing_flip`,
`TauCeti.SmoothDiscreteTopRep.ofMulPairing_flip`). Over `R = ℤ`, both pairings agree
(`TauCeti.ofDiscreteModuleMulPairing_int`, `TauCeti.SmoothDiscreteTopRep.ofMulPairing_int`) with
`TauCeti.ofDiscreteModulePairing` at `AddMonoidHom.mul`.

## Main definitions

* `TauCeti.ofDiscreteModuleMulPairing`: algebra multiplication on a discrete `G`-algebra `A` as a
  `TauCeti.TopPairing` on `ofDiscreteModule R G A`.
* `TauCeti.SmoothDiscreteTopRep.ofMulPairing`: the same pairing on
  `(SmoothDiscreteTopRep.of R G A).obj` over a discrete commutative ring `R`.

## Main results

* `TauCeti.SmoothDiscreteTopRep.ofMulPairing_eq_ofDiscreteModuleMulPairing`:
  `SmoothDiscreteTopRep.ofMulPairing` agrees with `ofDiscreteModuleMulPairing` under any ambient
  `ContinuousSMul R A` instance.
* `TauCeti.ofDiscreteModuleMulPairing_flip`, `TauCeti.SmoothDiscreteTopRep.ofMulPairing_flip`:
  symmetry of the multiplication pairing when `A` is commutative.
* `TauCeti.ofDiscreteModuleMulPairing_int`, `TauCeti.SmoothDiscreteTopRep.ofMulPairing_int`:
  comparison over `ℤ` with `TauCeti.ofDiscreteModulePairing` at `AddMonoidHom.mul`.
-/

public section

universe u v w

namespace TauCeti

section GeneralRing

variable (R : Type u) [CommRing R] [TopologicalSpace R]
  (G : Type v) [Monoid G]
  (A : Type w) [Ring A] [Algebra R A] [TopologicalSpace A] [DiscreteTopology A]
  [MulSemiringAction G A] [SMulCommClass G R A] [ContinuousSMul R A]

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

/-- When `A` is commutative, `ofDiscreteModuleMulPairing` is invariant under `TopPairing.flip`. -/
@[simp]
theorem ofDiscreteModuleMulPairing_flip
    (R : Type u) [CommRing R] [TopologicalSpace R]
    (G : Type v) [Monoid G]
    (A : Type w) [CommRing A] [Algebra R A] [TopologicalSpace A] [DiscreteTopology A]
    [MulSemiringAction G A] [SMulCommClass G R A] [ContinuousSMul R A] :
    (ofDiscreteModuleMulPairing R G A).flip = ofDiscreteModuleMulPairing R G A := by
  apply TopPairing.ext
  refine LinearMap.ext fun x ↦ LinearMap.ext fun y ↦ ?_
  rw [TopPairing.flip_bil]
  -- `(ofDiscreteModuleMulPairing R G A).bil` evaluates `LinearMap.mul R A` on `A`.
  exact mul_comm y x

/-- Over `ℤ`, `ofDiscreteModuleMulPairing` agrees with `ofDiscreteModulePairing` at
`AddMonoidHom.mul`. -/
theorem ofDiscreteModuleMulPairing_int
    (G : Type v) [Monoid G]
    (A : Type w) [Ring A] [TopologicalSpace A] [DiscreteTopology A] [MulSemiringAction G A] :
    ofDiscreteModuleMulPairing ℤ G A =
      ofDiscreteModulePairing AddMonoidHom.mul (fun g a b ↦ (smul_mul' g a b).symm) := by
  apply TopPairing.ext
  refine LinearMap.ext fun x ↦ LinearMap.ext fun y ↦ ?_
  -- Both `LinearMap.mul ℤ A x y` and `AddMonoidHom.mul x y` evaluate to `x * y` on `A`.
  exact (ofDiscreteModulePairing_bil_apply (AddMonoidHom.mul (R := A)) _ x y).symm

namespace SmoothDiscreteTopRep

section DiscreteRing

variable (R : Type u) [CommRing R] [TopologicalSpace R] [DiscreteTopology R]
  (G : Type v) [Monoid G] [TopologicalSpace G]
  (A : Type w) [Ring A] [Algebra R A] [TopologicalSpace A] [DiscreteTopology A]
  [MulSemiringAction G A] [SMulCommClass G R A] [ContinuousSMul G A]

/-- Algebra multiplication on a discrete `G`-algebra `A` over a discrete commutative ring `R`, as a
`TauCeti.TopPairing` on `(SmoothDiscreteTopRep.of R G A).obj`. Continuity of scalar multiplication
by `R` holds automatically via `TauCeti.continuousSMul_of_discreteTopology`; when a
`ContinuousSMul R A` instance is in scope, this agrees with `ofDiscreteModuleMulPairing R G A`
(`SmoothDiscreteTopRep.ofMulPairing_eq_ofDiscreteModuleMulPairing`). -/
def ofMulPairing :
    TopPairing (SmoothDiscreteTopRep.of R G A).obj (SmoothDiscreteTopRep.of R G A).obj
      (SmoothDiscreteTopRep.of R G A).obj :=
  ofDiscreteModuleMulPairing R G A

/-- `SmoothDiscreteTopRep.ofMulPairing` agrees with `ofDiscreteModuleMulPairing` for any ambient
`ContinuousSMul R A` instance. -/
theorem ofMulPairing_eq_ofDiscreteModuleMulPairing [ContinuousSMul R A] :
    ofMulPairing R G A = ofDiscreteModuleMulPairing R G A :=
  (rfl)

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

/-- When `A` is commutative, `SmoothDiscreteTopRep.ofMulPairing` is invariant under
`TopPairing.flip`. -/
@[simp]
theorem ofMulPairing_flip
    (R : Type u) [CommRing R] [TopologicalSpace R] [DiscreteTopology R]
    (G : Type v) [Monoid G] [TopologicalSpace G]
    (A : Type w) [CommRing A] [Algebra R A] [TopologicalSpace A] [DiscreteTopology A]
    [MulSemiringAction G A] [SMulCommClass G R A] [ContinuousSMul G A] :
    (ofMulPairing R G A).flip = ofMulPairing R G A :=
  ofDiscreteModuleMulPairing_flip R G A

/-- Over `ℤ`, `SmoothDiscreteTopRep.ofMulPairing` agrees with `ofDiscreteModulePairing` at
`AddMonoidHom.mul`. -/
theorem ofMulPairing_int
    (G : Type v) [Monoid G] [TopologicalSpace G]
    (A : Type w) [Ring A] [TopologicalSpace A] [DiscreteTopology A]
    [MulSemiringAction G A] [ContinuousSMul G A] :
    ofMulPairing ℤ G A =
      ofDiscreteModulePairing AddMonoidHom.mul (fun g a b ↦ (smul_mul' g a b).symm) :=
  (ofMulPairing_eq_ofDiscreteModuleMulPairing ℤ G A).trans (ofDiscreteModuleMulPairing_int G A)

end SmoothDiscreteTopRep

end TauCeti
