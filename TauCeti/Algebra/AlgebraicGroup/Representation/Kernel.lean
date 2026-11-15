/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Representation.Coordinate
public import TauCeti.Algebra.AlgebraicGroup.Representation.Differential
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Tangent
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Kernel.Tangent

/-!
# The Lie algebra of a representation kernel

For a finite free representation of an affine group, the differential of its coordinate
morphism is the differentiated comodule action. Consequently the Lie algebra of its
scheme-theoretic kernel consists exactly of the tangent vectors acting by zero.

The statements work over an arbitrary commutative base ring. A basis describes the coordinate
morphism to the general linear group; the vanishing criterion is intrinsic to the comodule.

## References

* J. S. Milne, *Algebraic Groups* (2017), Chapters 4 and 10.

The proof combines `Derivation.apply_matrixCoefficient`, the tangent-matrix equivalence for
the general linear group, and `TauCeti.CommHopfAlgCat.lieSubalgebra_kernelHopfIdeal`.
-/

public section

namespace Derivation

open TauCeti TauCeti.Comodule

universe u v w

section Matrix

variable {R : Type u} {H : Type v} {M : Type w}
variable [CommRing R] [CommRing H] [HopfAlgebra R H]
variable [AddCommGroup M] [Module R M] [Comodule R H M] {n : ℕ}

attribute [local instance 100] LieRing.ofAssociativeRing

/-- In a finite basis, differentiating the coordinate morphism of a representation gives
the matrix of the differentiated comodule action. -/
theorem tangentMatrix_comp_coordinateBialgHom
    (d : Derivation R H (Bialgebra.CounitAlgebra R H R)) (b : Module.Basis (Fin n) R M) :
    GeneralLinear.tangentMatrix n (derivationComp (coordinateBialgHom (H := H) b) d) =
      LinearMap.toMatrix b b (differential (R := R) (H := H) (M := M) d) := by
  ext i j
  rw [GeneralLinear.tangentMatrix_apply, algEquivSelf_derivationComp_apply,
    LinearMap.toMatrix_apply]
  erw [coordinateBialgHom_X, coefficientMatrix_apply]
  exact d.apply_matrixCoefficient (b.coord i) (b j)

end Matrix

section Kernel

variable {R H : Type u} {M : Type w}
variable [CommRing R] [CommRing H] [HopfAlgebra R H]
variable [AddCommGroup M] [Module R M] [Comodule R H M] {n : ℕ}

/-- A tangent vector lies in the Lie algebra of a representation's scheme-theoretic kernel
exactly when its differentiated action is zero. -/
@[simp↓]
theorem mem_lieSubalgebra_kernel_coordinateBialgHom_iff
    (d : Derivation R H (Bialgebra.CounitAlgebra R H R)) (b : Module.Basis (Fin n) R M) :
    d ∈ (CommHopfAlgCat.kernelHopfIdeal
      (CommHopfAlgCat.ofHom (coordinateBialgHom (H := H) b))).lieSubalgebra (B := R) ↔
      differential (R := R) (H := H) (M := M) d = 0 := by
  rw [CommHopfAlgCat.lieSubalgebra_kernelHopfIdeal,
    LieIdeal.mem_toLieSubalgebra, LieHom.mem_ker, derivationCompLieHom_apply]
  rw [← (GeneralLinear.tangentLinearEquivMatrix (R := R) (B := R) n).map_eq_zero_iff,
    GeneralLinear.tangentLinearEquivMatrix_apply,
    CommHopfAlgCat.hom_ofHom, tangentMatrix_comp_coordinateBialgHom]
  exact (LinearMap.toMatrix b b).map_eq_zero_iff

end Kernel

end Derivation
