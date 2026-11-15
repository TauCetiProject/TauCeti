/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Representation.Fixed
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Lie.Adjoint.Differential
public import TauCeti.Algebra.AlgebraicGroup.Tangent.FiniteType

/-!
# The invariant vectors of the adjoint representation

For a connected affine group over an algebraically closed field of characteristic zero,
the invariant vectors of its rational adjoint representation are exactly the center of
its tangent Lie algebra. Thus the entire group fixes each central tangent vector after
extension to any commutative value algebra, even one with nilpotents.

This is the comparison needed to show that Lie-central tangent vectors give central
dual-number points. The action on the center as a subrepresentation is trivial.

## References

* J. S. Milne, *Algebraic Groups* (2017), Chapters 10 and 22.
* J. E. Humphreys, *Linear Algebraic Groups*, §13.
-/

public section

open TauCeti
open scoped TensorProduct

namespace TauCeti.FiniteTypeCommHopfAlgCat

universe u

variable {k : Type u} [Field k] [CharZero k] [IsAlgClosed k]
variable (H : FiniteTypeCommHopfAlgCat.{u, u} k) [ConnectedSpace (PrimeSpectrum H)]

attribute [local instance] Derivation.adjointComodule

/-- For a connected group over an algebraically closed field of characteristic zero,
a tangent vector is rationally fixed under the adjoint action exactly when it lies in the
center of the tangent Lie algebra. -/
theorem coact_adjointComodule_eq_tmul_one_iff_mem_center
    (x : Module.Dual k (Bialgebra.CotangentSpace k H)) :
    Comodule.coact (R := k) (C := H) x = x ⊗ₜ[k] (1 : H) ↔
      x ∈ LieAlgebra.center k (Module.Dual k (Bialgebra.CotangentSpace k H)) := by
  rw [Comodule.coact_eq_tmul_one_iff_forall_differential_eq_zero,
    LieModule.mem_maxTrivSubmodule]
  simp only [Derivation.differential_adjointComodule]
  constructor
  · intro hx y
    simpa only [LieEquiv.symm_apply_apply] using hx (Derivation.cotangentDualLieEquiv y)
  · intro hx d
    exact hx _

/-- Every algebra-valued point fixes the scalar extension of each central tangent vector
of a connected affine group over an algebraically closed field of characteristic zero.
The value algebra may be nonreduced. -/
theorem endOfPoint_tmul_of_mem_center
    (x : Module.Dual k (Bialgebra.CotangentSpace k H))
    (hx : x ∈ LieAlgebra.center k (Module.Dual k (Bialgebra.CotangentSpace k H)))
    {A : Type*} [CommSemiring A] [Algebra k A] (g : H →ₐ[k] A) (a : A) :
    Comodule.endOfPoint (Module.Dual k (Bialgebra.CotangentSpace k H)) g (a ⊗ₜ[k] x) =
      a ⊗ₜ[k] x :=
  Comodule.endOfPoint_tmul_of_coact_eq_tmul_one
    ((coact_adjointComodule_eq_tmul_one_iff_mem_center H x).mpr hx) g a

end TauCeti.FiniteTypeCommHopfAlgCat
