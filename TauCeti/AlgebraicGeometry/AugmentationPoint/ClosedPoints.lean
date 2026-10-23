/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.AlgebraicGeometry.AugmentationPoint.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Jacobson.Ring
public import Mathlib.Topology.JacobsonSpace

/-!
# Closed points of an affine scheme over an algebraically closed field

For a finite-type algebra over an algebraically closed field, the closed points of its
spectrum are exactly the kernels of algebra homomorphisms to the base field. This affine
form of the weak Nullstellensatz connects the augmentation-point API to closed-point
arguments on schemes. It includes nonreduced algebras.

The construction uses Zariski's lemma `finite_of_finite_type_of_isJacobsonRing` and
`IsAlgClosed.algebraMap_bijective_of_isIntegral`.

## References

* D. Eisenbud, *Commutative Algebra with a View Toward Algebraic Geometry*, Chapter 4.
-/

public section

open TopologicalSpace

namespace AlgHom

variable {k A : Type*} [Field k] [CommRing A] [Algebra k A]

/-- The spectrum point defined by a base-field-valued algebra homomorphism is closed,
without a finite-type assumption. -/
@[simp]
theorem isClosed_singleton_kernelPoint (f : A →ₐ[k] k) :
    IsClosed ({TauCeti.AlgHom.kernelPoint f} :
      Set (AlgebraicGeometry.Spec (.of A))) := by
  apply (PrimeSpectrum.isClosed_singleton_iff_isMaximal
    (TauCeti.AlgHom.kernelPoint f)).mpr
  rw [TauCeti.AlgHom.kernelPoint_asIdeal]
  exact RingHom.ker_isMaximal_of_surjective _
    (fun r ↦ ⟨algebraMap k A r, f.commutes r⟩)

end AlgHom

namespace PrimeSpectrum

variable {k A : Type*} [Field k] [IsAlgClosed k] [CommRing A] [Algebra k A]
  [Algebra.FiniteType k A]

/-- Every closed point of a finite-type algebra over an algebraically closed field is the
kernel point of a base-field-valued algebra homomorphism. -/
theorem exists_kernelPoint_eq_of_isClosed (x : PrimeSpectrum A) (hx : IsClosed {x}) :
    ∃ f : A →ₐ[k] k, TauCeti.AlgHom.kernelPoint f = x := by
  let : x.asIdeal.IsMaximal := x.isClosed_singleton_iff_isMaximal.mp hx
  let : Field (A ⧸ x.asIdeal) := Ideal.Quotient.field x.asIdeal
  let : Module.Finite k (A ⧸ x.asIdeal) :=
    finite_of_finite_type_of_isJacobsonRing k (A ⧸ x.asIdeal)
  let e : k ≃ₐ[k] A ⧸ x.asIdeal := AlgEquiv.ofBijective (Algebra.ofId k _)
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  refine ⟨e.symm.toAlgHom.comp (Ideal.Quotient.mkₐ k x.asIdeal), ?_⟩
  apply PrimeSpectrum.ext
  rw [TauCeti.AlgHom.kernelPoint_asIdeal, AlgHom.comp_toRingHom,
    RingHom.ker_comp_of_injective _ e.symm.injective,
    Ideal.Quotient.mkₐ_ker]

end PrimeSpectrum

namespace TauCeti

variable {k A : Type*} [Field k] [IsAlgClosed k] [CommRing A] [Algebra k A]
  [Algebra.FiniteType k A]

/-- Rational augmentation points are exactly the closed points of a finite-type affine
scheme over an algebraically closed field. -/
theorem range_kernelPoint_eq_closedPoints :
    Set.range (AlgHom.kernelPoint (k := k) (H := A)) =
      closedPoints (AlgebraicGeometry.Spec (.of A)) := by
  ext x
  constructor
  · rintro ⟨f, rfl⟩
    exact f.isClosed_singleton_kernelPoint
  · exact PrimeSpectrum.exists_kernelPoint_eq_of_isClosed x

end TauCeti
