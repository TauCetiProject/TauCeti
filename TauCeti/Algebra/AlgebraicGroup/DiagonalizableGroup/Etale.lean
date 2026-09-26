/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.Kernel
public import TauCeti.Algebra.MonoidAlgebra.Etale

/-!
# Étale kernels of diagonalizable-group morphisms

The kernel of `D(N) → D(M)` associated to a character homomorphism `p : M →* N`
is `D(N / range p)`. When the character cokernel is finite, this kernel is étale if
its order is invertible in the base ring; over a field the converse holds as well.
Thus the criterion detects separable versus infinitesimal kernels of isogenies,
without assuming either ambient diagonalizable group is smooth.

## References

* J. S. Milne, *Algebraic Groups* (2017), §12, diagonalizable groups.

The comparison uses `TauCeti.DiagonalizableGroup.kernelCoordinateIso`.
-/

public section

namespace TauCeti.DiagonalizableGroup

universe u v

variable (R : Type u) [CommRing R]
variable {M N : Type v} [CommGroup M] [CommGroup N] (p : M →* N)
variable [Finite (N ⧸ p.range)]

/-- A diagonalizable-group kernel is étale when the order of the character cokernel
is invertible in the base ring. -/
theorem etale_kernelCoordinate_of_isUnit_card (h : IsUnit (Nat.card (N ⧸ p.range) : R)) :
    Algebra.Etale R
      (CommHopfAlgCat.quotient (CommHopfAlgCat.of R (MonoidAlgebra R N))
        (CommHopfAlgCat.kernelHopfIdeal
          (CommHopfAlgCat.ofHom (MonoidAlgebra.mapDomainBialgHom R p)))) := by
  let _ := MonoidAlgebra.etale_of_isUnit_card R (N ⧸ p.range) h
  exact Algebra.Etale.of_equiv
    (CommHopfAlgCat.ofIso (kernelCoordinateIso R p)).toAlgEquiv.symm

/-- Over a field, a finite diagonalizable-group kernel is étale exactly when the order
of the character cokernel is invertible in the field. -/
theorem etale_kernelCoordinate_iff_isUnit_card (k : Type u) [Field k] :
    Algebra.Etale k
      (CommHopfAlgCat.quotient (CommHopfAlgCat.of k (MonoidAlgebra k N))
        (CommHopfAlgCat.kernelHopfIdeal
          (CommHopfAlgCat.ofHom (MonoidAlgebra.mapDomainBialgHom k p)))) ↔
      IsUnit (Nat.card (N ⧸ p.range) : k) := by
  refine ⟨fun h => ?_, etale_kernelCoordinate_of_isUnit_card k p⟩
  let _ := h
  apply (MonoidAlgebra.etale_iff_isUnit_card (N ⧸ p.range) k).mp
  exact Algebra.Etale.of_equiv
    (CommHopfAlgCat.ofIso (kernelCoordinateIso k p)).toAlgEquiv

end TauCeti.DiagonalizableGroup
