/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.MonoidAlgebra.Connected
public import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.Kernel
public import TauCeti.Algebra.AlgebraicGroup.Connected.CommHopfAlgCat
import Mathlib.RingTheory.TensorProduct.MonoidAlgebra

/-!
# Connected finite diagonalizable groups and kernels

Over a field of characteristic `p`, a finite diagonalizable group is geometrically
connected exactly when its character group is a `p`-group. In particular, the finite
kernel of `D(N) → D(M)` is geometrically connected exactly when the character cokernel
`N / range f` is a `p`-group. Ordinary connectedness gives the same criterion.

These statements detect infinitesimal finite kernels without assuming smoothness
of either ambient group. They complement the prime-to-characteristic criterion for
étale diagonalizable kernels.

## References

* J. S. Milne, *Algebraic Groups* (2017), §12.
* W. C. Waterhouse, *Introduction to Affine Group Schemes*, Chapter 2.

The kernel identification is `TauCeti.DiagonalizableGroup.kernelCoordinateIso`;
scalar extension uses Mathlib's `MonoidAlgebra.scalarTensorEquiv`.
-/

public section

open scoped TensorProduct

namespace TauCeti.DiagonalizableGroup

universe u v

variable (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]

/-- The diagonalizable group of an abelian `p`-group is geometrically connected
in characteristic `p`, even when the character group is infinite. -/
theorem geometricallyConnected_of_isPGroup {G : Type v} [CommGroup G]
    (hG : IsPGroup p G) :
    geometricallyConnectedCommHopfAlgProperty k (CommHopfAlgCat.of k (MonoidAlgebra k G)) := by
  rw [geometricallyConnectedCommHopfAlgProperty_iff]
  intro K _ _
  let _ : CharP K p := charP_of_injective_algebraMap (algebraMap k K).injective p
  let e := (Algebra.TensorProduct.comm k (MonoidAlgebra k G) K).toRingEquiv.trans
    (MonoidAlgebra.scalarTensorEquiv k K).toRingEquiv
  exact (PrimeSpectrum.homeomorphOfRingEquiv e).connectedSpace_iff.mpr
    (connectedSpace_primeSpectrum_monoidAlgebra_of_isPGroup K p hG)

/-- A finite diagonalizable group in characteristic `p` is geometrically connected
if and only if its character group is a `p`-group. -/
theorem geometricallyConnected_iff_isPGroup (G : Type v) [CommGroup G] [Finite G] :
    geometricallyConnectedCommHopfAlgProperty k (CommHopfAlgCat.of k (MonoidAlgebra k G)) ↔
      IsPGroup p G := by
  refine ⟨fun h => ?_, geometricallyConnected_of_isPGroup k p⟩
  exact (connectedSpace_primeSpectrum_monoidAlgebra_iff_isPGroup k G p).mp
    (h.connectedSpace k _)

variable {M N : Type v} [CommGroup M] [CommGroup N] (f : M →* N)
variable [Finite (N ⧸ f.range)]

/-- A finite diagonalizable-group kernel in characteristic `p` is connected
if and only if the character cokernel is a `p`-group. -/
theorem connectedSpace_kernelCoordinate_iff_isPGroup :
    ConnectedSpace (PrimeSpectrum
      (CommHopfAlgCat.quotient (CommHopfAlgCat.of k (MonoidAlgebra k N))
        (CommHopfAlgCat.kernelHopfIdeal
          (CommHopfAlgCat.ofHom (MonoidAlgebra.mapDomainBialgHom k f))))) ↔
      IsPGroup p (N ⧸ f.range) := by
  let e := (CommHopfAlgCat.ofIso (kernelCoordinateIso k f)).toAlgEquiv.toRingEquiv
  exact (PrimeSpectrum.homeomorphOfRingEquiv e).connectedSpace_iff.trans
    (connectedSpace_primeSpectrum_monoidAlgebra_iff_isPGroup k (N ⧸ f.range) p)

/-- A finite diagonalizable-group kernel in characteristic `p` is geometrically
connected if and only if the character cokernel is a `p`-group. -/
theorem geometricallyConnected_kernelCoordinate_iff_isPGroup :
    geometricallyConnectedCommHopfAlgProperty k
      (CommHopfAlgCat.quotient (CommHopfAlgCat.of k (MonoidAlgebra k N))
        (CommHopfAlgCat.kernelHopfIdeal
          (CommHopfAlgCat.ofHom (MonoidAlgebra.mapDomainBialgHom k f)))) ↔
      IsPGroup p (N ⧸ f.range) := by
  exact ((geometricallyConnectedCommHopfAlgProperty k).prop_iff_of_iso
    (kernelCoordinateIso k f)).trans (geometricallyConnected_iff_isPGroup k p _)

end TauCeti.DiagonalizableGroup
