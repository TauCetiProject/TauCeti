/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Padics.Measure.CharacterIntegral
public import TauCeti.NumberTheory.Padics.Measure.JointFiniteProjection

import Mathlib.Algebra.Group.TypeTags.Finite
import Mathlib.Topology.Instances.ZMod

/-!
# Finite measure algebras

Measures on a finite discrete monoid identify with its monoid algebra: the coefficients are the
values on singleton fibres, and the inverse takes the finite linear combination of Dirac measures.
This identifies convolution with monoid-algebra multiplication. Pushing forward along a continuous
monoid homomorphism gives finite algebra coordinates, and reducing integral `p`-adic coefficients
gives finite-precision ring coordinates.

The algebra structure and the map from a monoid algebra to measures are Mathlib's
`AbstractMeasure.monoidAlgebraHom`; this file proves that map bijective in the finite discrete case.
The finite-coordinate description follows Rodrigues Jacinto and Williams, *An introduction to
p-adic L-functions*, Sections 3.2--3.3, Propositions 3.15--3.16, pp. 121--123.
-/

public noncomputable section

open ContinuousMap

namespace AbstractMeasure

variable {G A R : Type*} [TopologicalSpace G] [TopologicalSpace A]
  [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]

section Reconstruction

variable [Monoid A] [ContinuousMul A] [LocallyCompactSpace A]

/-- Mathlib's algebra homomorphism is the finite Dirac expansion of the coefficients. -/
theorem monoidAlgebraHom_eq_ofFiniteCoefficients (c : MonoidAlgebra R A) :
    monoidAlgebraHom c = ofFiniteCoefficients c.coeff := by
  have h : (monoidAlgebraHom : MonoidAlgebra R A →ₐ[R] D(A, R)).toLinearMap =
      ofFiniteCoefficients.comp (MonoidAlgebra.coeffLinearEquiv R).toLinearMap := by
    ext a
    simp
  exact LinearMap.congr_fun h c

end Reconstruction

section Finite

variable [Monoid A] [Finite A] [DiscreteTopology A]

/-- The coefficient map identifies the convolution algebra on a finite discrete monoid with its
monoid algebra. Its inverse is Mathlib's canonical monoid-algebra homomorphism. -/
def finiteProjectionAlgEquiv : D(A, R) ≃ₐ[R] MonoidAlgebra R A :=
  (AlgEquiv.ofBijective monoidAlgebraHom (by
    simpa only [Function.comp_def, MonoidAlgebra.coeffEquiv_apply,
      finiteProjectionEquiv_symm_apply,
      ← monoidAlgebraHom_eq_ofFiniteCoefficients] using
      (finiteProjectionEquiv (A := A) (R := R)).symm.bijective.comp
        (MonoidAlgebra.coeffEquiv (R := R) (M := A)).bijective)).symm

/-- The inverse finite algebra equivalence reconstructs the measure from its coefficients. -/
-- Keep the expansion named so that it does not interrupt the generic equivalence inverse laws.
theorem finiteProjectionAlgEquiv_symm_apply (c : MonoidAlgebra R A) :
    finiteProjectionAlgEquiv.symm c = ofFiniteCoefficients c.coeff := by
  simp only [finiteProjectionAlgEquiv, AlgEquiv.symm_symm, AlgEquiv.ofBijective_apply,
    monoidAlgebraHom_eq_ofFiniteCoefficients]

/-- A single coefficient reconstructs a scalar multiple of a Dirac measure. -/
@[simp]
theorem finiteProjectionAlgEquiv_symm_single (a : A) (r : R) :
    finiteProjectionAlgEquiv.symm (MonoidAlgebra.single a r) = r • dirac R a := by
  simp [finiteProjectionAlgEquiv_symm_apply]

/-- The finite algebra equivalence records the singleton fibre coefficients. -/
theorem finiteProjectionAlgEquiv_apply (μ : D(A, R)) :
    finiteProjectionAlgEquiv μ = MonoidAlgebra.ofCoeff (finiteProjection (.id A) μ) := by
  apply finiteProjectionAlgEquiv.symm.injective
  simp [finiteProjectionAlgEquiv_symm_apply]

/-- The finite algebra equivalence sends a Dirac measure to the corresponding basis element. -/
@[simp]
theorem finiteProjectionAlgEquiv_dirac (a : A) :
    finiteProjectionAlgEquiv (dirac R a) = MonoidAlgebra.single a 1 := by
  simp [finiteProjectionAlgEquiv_apply]

end Finite

end AbstractMeasure

namespace ContinuousMonoidHom

open AbstractMeasure

variable {G A R : Type*} [TopologicalSpace G] [TopologicalSpace A]
  [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]

section Projection

variable [Monoid G] [ContinuousMul G] [LocallyCompactSpace G]
  [Monoid A] [Finite A] [DiscreteTopology A]

/-- Finite algebra coordinates of a measure along a continuous monoid homomorphism. -/
def finiteProjectionAlgHom (q : G →ₜ* A) : D(G, R) →ₐ[R] MonoidAlgebra R A :=
  finiteProjectionAlgEquiv.toAlgHom.comp q.mapAlgHom

/-- The algebra projection packages the finite fibre coefficients in the monoid algebra. -/
theorem finiteProjectionAlgHom_apply (q : G →ₜ* A) (μ : D(G, R)) :
    finiteProjectionAlgHom q μ = MonoidAlgebra.ofCoeff (finiteProjection (q : C(G, A)) μ) := by
  rw [finiteProjectionAlgHom, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
    ContinuousMonoidHom.mapAlgHom_apply, finiteProjectionAlgEquiv_apply]
  congr 1
  ext a
  simp only [finiteProjection_apply, map_apply]
  congr 1
  ext g
  classical
  by_cases h : q g = a <;> simp [h]

/-- A coefficient of the algebra projection is the measure of the corresponding fibre. -/
@[simp]
theorem finiteProjectionAlgHom_coeff (q : G →ₜ* A) (μ : D(G, R)) (a : A) :
    (finiteProjectionAlgHom q μ).coeff a = finiteProjection (q : C(G, A)) μ a := by
  rw [finiteProjectionAlgHom_apply, MonoidAlgebra.coeff_ofCoeff]

/-- The algebra projection carries a Dirac measure to the basis element at its image. -/
@[simp]
theorem finiteProjectionAlgHom_dirac (q : G →ₜ* A) (g : G) :
    finiteProjectionAlgHom q (dirac R g) = MonoidAlgebra.single (q g) 1 := by
  simp [finiteProjectionAlgHom_apply]

end Projection

end ContinuousMonoidHom

namespace AbstractMeasure

variable {G A R : Type*} [TopologicalSpace G] [TopologicalSpace A]
  [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]

section Projection

variable [Monoid G] [ContinuousMul G] [LocallyCompactSpace G]
  [Monoid A] [Finite A] [DiscreteTopology A]

/-- Finite projection takes convolution to monoid-algebra multiplication. -/
theorem finiteProjection_mul (μ ν : D(G, R)) (q : G →ₜ* A) :
    MonoidAlgebra.ofCoeff (finiteProjection (q : C(G, A)) (μ * ν)) =
      MonoidAlgebra.ofCoeff (finiteProjection (q : C(G, A)) μ) *
        MonoidAlgebra.ofCoeff (finiteProjection (q : C(G, A)) ν) := by
  simpa only [ContinuousMonoidHom.finiteProjectionAlgHom_apply] using
    map_mul (ContinuousMonoidHom.finiteProjectionAlgHom q) μ ν

end Projection

end AbstractMeasure

namespace ContinuousMonoidHom

open AbstractMeasure

variable {G A : Type*} [TopologicalSpace G] [TopologicalSpace A]

section Joint

variable {p : ℕ} [Fact p.Prime]
  [Monoid G] [ContinuousMul G] [LocallyCompactSpace G]
  [Monoid A] [Finite A] [DiscreteTopology A]

/-- Finite algebra coordinates with integral coefficients reduced modulo `p ^ r`.
The precision and the finite quotient are independent; precision zero gives the zero ring. -/
def jointFiniteProjectionRingHom (r : ℕ) (q : G →ₜ* A) :
    D(G, ℤ_[p]) →+* MonoidAlgebra (ZMod (p ^ r)) A :=
  (MonoidAlgebra.mapRingHom A (PadicInt.toZModPow r)).comp
    (finiteProjectionAlgHom q).toRingHom

/-- Finite-precision algebra coordinates package the joint fibre coefficients. -/
theorem jointFiniteProjectionRingHom_apply (r : ℕ) (q : G →ₜ* A) (μ : D(G, ℤ_[p])) :
    jointFiniteProjectionRingHom r q μ =
      MonoidAlgebra.ofCoeff (jointFiniteProjection r (q : C(G, A)) μ) := by
  ext a
  simp [jointFiniteProjectionRingHom, jointFiniteProjection_apply]

/-- A finite-precision Dirac coordinate is the monoid-algebra basis element at its image. -/
-- Simplify before `p ^ r` normalizes and changes the dependent result-type presentation.
@[simp↓]
theorem jointFiniteProjectionRingHom_dirac (r : ℕ) (q : G →ₜ* A) (g : G) :
    jointFiniteProjectionRingHom (p := p) r q (dirac ℤ_[p] g) =
      MonoidAlgebra.single (q g) 1 := by
  simp [jointFiniteProjectionRingHom_apply]

/-- At precision zero, every finite-precision algebra coordinate is zero. -/
theorem jointFiniteProjectionRingHom_zero_precision (q : G →ₜ* A) (μ : D(G, ℤ_[p])) :
    jointFiniteProjectionRingHom 0 q μ = 0 := by
  rw [jointFiniteProjectionRingHom_apply, jointFiniteProjection_zero_precision,
    MonoidAlgebra.ofCoeff_zero]

end Joint

/-! Finite cyclic and finite-precision calculations, including the zero coefficient ring. -/

example :
    finiteProjectionAlgHom (R := ℤ) (ContinuousMonoidHom.id (Multiplicative (ZMod 2)))
        ((2 : ℕ) • dirac ℤ (1 : Multiplicative (ZMod 2)) +
          (3 : ℕ) • dirac ℤ (Multiplicative.ofAdd (1 : ZMod 2))) =
      MonoidAlgebra.single 1 2 + MonoidAlgebra.single (Multiplicative.ofAdd (1 : ZMod 2)) 3 := by
  ext a
  simp only [map_add, map_nsmul, finiteProjectionAlgHom_dirac]
  simp

example {G A : Type*} [TopologicalSpace G] [Monoid G] [ContinuousMul G]
    [LocallyCompactSpace G] [TopologicalSpace A] [Monoid A] [Finite A] [DiscreteTopology A]
    (q : G →ₜ* A) (x y : G) :
    finiteProjectionAlgHom q (dirac ℤ x * dirac ℤ y) =
      MonoidAlgebra.single (q x * q y) 1 := by
  simp [map_mul, dirac_mul_dirac]

example :
    finiteProjectionAlgHom (R := ℤ) (1 : Multiplicative (ZMod 2) →ₜ* PUnit)
        ((2 : ℕ) • dirac ℤ (1 : Multiplicative (ZMod 2)) +
          (3 : ℕ) • dirac ℤ (Multiplicative.ofAdd (1 : ZMod 2))) =
      MonoidAlgebra.single 1 5 := by
  simp only [map_add, map_nsmul, finiteProjectionAlgHom_dirac]
  ext
  simp

example (a b : Multiplicative (ZMod 2)) :
    finiteProjectionAlgEquiv.symm
        (MonoidAlgebra.single a (2 : ℤ) + MonoidAlgebra.single b 3) 1 = 5 := by
  simp [finiteProjectionAlgEquiv_symm_apply]

example (a b : Multiplicative (ZMod 2)) (r s : ℤ_[2]) :
    finiteProjectionAlgEquiv.symm
        (MonoidAlgebra.single a r * MonoidAlgebra.single b s) = (r * s) • dirac ℤ_[2] (a * b) := by
  rw [MonoidAlgebra.single_mul_single]
  exact finiteProjectionAlgEquiv_symm_single _ _

example :
    jointFiniteProjectionRingHom (p := 3) 1
        (ContinuousMonoidHom.id (Multiplicative (ZMod 2)))
        ((3 : ℕ) • dirac ℤ_[3] (Multiplicative.ofAdd (1 : ZMod 2))) = 0 := by
  rw [map_nsmul, jointFiniteProjectionRingHom_dirac]
  ext a
  norm_num [Finsupp.single_apply]
  intro _
  decide

example :
    jointFiniteProjectionRingHom (p := 3) 1
        (ContinuousMonoidHom.id (Multiplicative (ZMod 2)))
        (dirac ℤ_[3] (Multiplicative.ofAdd (1 : ZMod 2))) =
      MonoidAlgebra.single (Multiplicative.ofAdd (1 : ZMod 2)) 1 := by
  exact jointFiniteProjectionRingHom_dirac _ _ _

example :
    jointFiniteProjectionRingHom (p := 2) 0
        (ContinuousMonoidHom.id (Multiplicative (ZMod 2))) 1 = 0 := by
  exact jointFiniteProjectionRingHom_zero_precision _ _

example :
    jointFiniteProjectionRingHom (p := 2) 3
        (ContinuousMonoidHom.id (Multiplicative (ZMod 2)))
        (((2 : ℕ) • dirac ℤ_[2] (1 : Multiplicative (ZMod 2))) *
          ((3 : ℕ) • dirac ℤ_[2] (1 : Multiplicative (ZMod 2)))) =
      MonoidAlgebra.single 1 6 := by
  rw [map_mul, map_nsmul, map_nsmul, jointFiniteProjectionRingHom_dirac]
  ext a
  norm_num [Finsupp.single_apply]

end ContinuousMonoidHom
