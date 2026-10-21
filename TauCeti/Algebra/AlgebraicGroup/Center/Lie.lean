/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Center.Tangent
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Lie.Adjoint.Fixed
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Central.Tangent

/-!
# The Lie algebra of the center in characteristic zero

For a connected affine group of finite type over an algebraically closed field of
characteristic zero, the Lie algebra of its scheme-theoretic center is the center of its
Lie algebra. Connectedness ensures that a Lie-central vector is fixed by the whole adjoint
representation. This identifies the kernel of the differential of the center quotient.

The two descriptions of adjoint invariants are those of `Center.Tangent` and
`Tangent.Lie.Adjoint.Fixed`.

## References

* J. S. Milne, *Algebraic Groups* (2017), Chapter 10.
* J. E. Humphreys, *Linear Algebraic Groups*, §13.
-/

public section

open _root_.CommHopfAlgCat

namespace TauCeti.FiniteTypeCommHopfAlgCat

universe u

variable {k : Type u} [Field k] [CharZero k] [IsAlgClosed k]
variable (H : FiniteTypeCommHopfAlgCat.{u, u} k) [ConnectedSpace (PrimeSpectrum H)]

attribute [local instance] Derivation.adjointComodule

/-- The Lie algebra of the scheme-theoretic center of a connected affine group over an
algebraically closed field of characteristic zero is the center of the tangent Lie algebra. -/
@[simp]
theorem lieSubalgebra_centerDefiningIdeal_eq_center :
    (CommHopfAlgCat.centerDefiningIdeal H.obj).lieSubalgebra (B := k) =
      (LieAlgebra.center k (Derivation k H (Bialgebra.CounitAlgebra k H k))).toLieSubalgebra := by
  apply le_antisymm (CommHopfAlgCat.isCentral_centerDefiningIdeal H.obj).lieSubalgebra_le_center
  intro d hd
  rw [LieIdeal.mem_toLieSubalgebra, LieModule.mem_maxTrivSubmodule] at hd
  let e : Module.Dual k (Bialgebra.CotangentSpace k H) ≃ₗ⁅k⁆
      Derivation k H (Bialgebra.CounitAlgebra k H k) := Derivation.cotangentDualLieEquiv
  have hx : e.symm d ∈ LieAlgebra.center k (Module.Dual k (Bialgebra.CotangentSpace k H)) := by
    rw [LieModule.mem_maxTrivSubmodule]
    intro x
    apply e.injective
    simp only [LieHom.map_lie, LieEquiv.coe_toLieHom, LieEquiv.apply_symm_apply, map_zero]
    exact hd (e x)
  have hfixed := (coact_adjointComodule_eq_tmul_one_iff_mem_center H (e.symm d)).mpr hx
  have hmem :=
    (coact_adjointComodule_eq_tmul_one_iff_mem_lieSubalgebra_centerDefiningIdeal
      H.obj (e.symm d)).mp hfixed
  rw [← Derivation.cotangentDualLieEquiv_apply] at hmem
  simpa only [e, LieEquiv.apply_symm_apply] using hmem

end TauCeti.FiniteTypeCommHopfAlgCat
