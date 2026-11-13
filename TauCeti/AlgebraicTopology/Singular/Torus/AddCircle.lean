/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import TauCeti.AlgebraicTopology.Singular.Torus.Basic
public import TauCeti.Geometry.Sphere.Circle

/-!
# The singular homology of a torus of additive circles

A torus is often modelled as a product `∀ i, AddCircle (p i)` of additive circles, as for the
smooth manifold structure used in Morse theory and de Rham cohomology. When every period `p i` is
nonzero, each factor is homeomorphic to the unit circle `TopCat.sphere 1`, through the complex unit
circle (`AddCircle.homeomorphCircle` and `EuclideanSpace.sphereHomeomorphCircle`). So the torus is
homeomorphic to the product `ι → TopCat.sphere 1` of unit circles
(`TauCeti.piAddCircleHomeomorphSphere`), whose homology is computed in
`ModuleCat.finrank_singularHomology_torus`.

Transporting along this homeomorphism, the homology of `Tⁿ = ∀ i, AddCircle (p i)` with
coefficients in a free module `M` over a commutative ring is free, and of rank
`rank Hₘ(Tⁿ; M) = (n choose m) · rank M` when `M` has finite rank and the ring is nontrivial.

## Main declarations

* `TauCeti.piAddCircleHomeomorphSphere`: the homeomorphism `(∀ i, AddCircle (p i)) ≃ₜ (ι → S¹)`.
* `ModuleCat.free_singularHomology_pi_addCircle`,
  `ModuleCat.finite_singularHomology_pi_addCircle` and
  `ModuleCat.finrank_singularHomology_pi_addCircle`: the homology of the torus is free of
  finite rank, with `rank Hₘ(Tⁿ; M) = (n choose m) · rank M`.
-/

public section

noncomputable section

open CategoryTheory AlgebraicTopology

universe w

namespace TauCeti

variable {ι : Type w} (p : ι → ℝ) [∀ i, NeZero (p i)]

/-- A torus `∀ i, AddCircle (p i)` of additive circles with nonzero periods is homeomorphic to the
product `ι → TopCat.sphere 1` of unit circles, factorwise through the complex unit circle. -/
def piAddCircleHomeomorphSphere : (∀ i, AddCircle (p i)) ≃ₜ (ι → TopCat.sphere.{w} 1) :=
  Homeomorph.piCongrRight fun i ↦ (AddCircle.homeomorphCircle (NeZero.ne (p i))).trans
    (EuclideanSpace.sphereHomeomorphCircle.symm.trans Homeomorph.ulift.symm)

/-- The homology of a torus of additive circles is that of the product of unit circles. -/
private def singularHomologyPiAddCircleLinearEquiv {k : Type w} [CommRing k]
    (M : ModuleCat.{w} k) (m : ℕ) :
    ((singularHomologyFunctor (ModuleCat.{w} k) m).obj M).obj
        (TopCat.of (∀ i, AddCircle (p i))) ≃ₗ[k]
      ((singularHomologyFunctor (ModuleCat.{w} k) m).obj M).obj
        (TopCat.of (ι → TopCat.sphere.{w} 1)) :=
  (((singularHomologyFunctor (ModuleCat.{w} k) m).obj M).mapIso
    (TopCat.isoOfHomeo (piAddCircleHomeomorphSphere p))).toLinearEquiv

end TauCeti

namespace ModuleCat

open TauCeti

variable {k : Type w} [CommRing k] (M : ModuleCat.{w} k) [Module.Free k M]
  {ι : Type w} [Finite ι] (p : ι → ℝ) [∀ i, NeZero (p i)]

/-- The singular homology of a torus of additive circles with coefficients in a free module is
free. -/
instance free_singularHomology_pi_addCircle (m : ℕ) :
    Module.Free k (((singularHomologyFunctor (ModuleCat.{w} k) m).obj M).obj
      (TopCat.of (∀ i, AddCircle (p i)))) :=
  .of_equiv (singularHomologyPiAddCircleLinearEquiv p M m).symm

variable [Module.Finite k M]

/-- The singular homology of a torus of additive circles with coefficients in a free module of
finite rank has finite rank. -/
instance finite_singularHomology_pi_addCircle (m : ℕ) :
    Module.Finite k (((singularHomologyFunctor (ModuleCat.{w} k) m).obj M).obj
      (TopCat.of (∀ i, AddCircle (p i)))) :=
  .equiv (singularHomologyPiAddCircleLinearEquiv p M m).symm

/-- **The ranks of the homology of a torus of additive circles**: over a nontrivial commutative
ring, with coefficients in a free module `M` of finite rank, the torus
`Tⁿ = ∀ i, AddCircle (p i)` of `n` circles with nonzero periods has
`rank H_m(Tⁿ; M) = (n choose m) · rank M`. -/
@[simp]
theorem finrank_singularHomology_pi_addCircle [Nontrivial k] (m : ℕ) :
    Module.finrank k (((singularHomologyFunctor (ModuleCat.{w} k) m).obj M).obj
      (TopCat.of (∀ i, AddCircle (p i)))) = (Nat.card ι).choose m * Module.finrank k M := by
  rw [(singularHomologyPiAddCircleLinearEquiv p M m).finrank_eq,
    finrank_singularHomology_torus]

end ModuleCat
