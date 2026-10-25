/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Tangent.Lie.Adjoint.Centralizer
public import TauCeti.Algebra.Lie.AdjointAction.Regular

/-!
# Regular elements of the Lie algebra of an affine group

Let `G = Spec H` be a finite-type affine group over a field `k` of characteristic zero, with Lie
algebra `𝔤`. An element `x ∈ 𝔤` is regular (`LieAlgebra.IsCentralizerRegular`) when its
centralizer `ker (ad x)` in `𝔤` has minimal dimension. By Cartier's theorem the scheme-theoretic
centralizer `C_G(x)` is smooth with Lie algebra `ker (ad x)`, so `dim C_G(x) = dim ker (ad x)`
(`TauCeti.ringKrullDim_quotient_centralizerHopfIdeal`). Hence the regular elements are exactly
the elements whose group centralizer `C_G(x)` has minimal dimension
(`TauCeti.isCentralizerRegular_iff_forall_ringKrullDim_le`). Dimensions are Krull dimensions of
coordinate rings.

In positive characteristic a centralizer can be nonreduced, its Lie algebra can be larger than its
dimension, and the two notions need not agree; the comparison is stated in characteristic zero.

## Main results

* `TauCeti.isCentralizerRegular_iff_forall_ringKrullDim_le`: in characteristic zero, `x ∈ 𝔤` is
  regular exactly when `C_G(x)` has minimal dimension among the centralizers `C_G(y)`.

## References

* D. H. Collingwood and W. M. McGovern, *Nilpotent Orbits in Semisimple Lie Algebras*, Van
  Nostrand Reinhold, 1993, §1.3 and Chapter 4.
-/

public section

namespace TauCeti

universe u

variable {k : Type u} [Field k] [CharZero k] {H : Type u} [CommRing H] [HopfAlgebra k H]
  [Algebra.FiniteType k H]

/-- **Regular elements have centralizers of minimal dimension.** Over a field of characteristic
zero, an element `x` of the Lie algebra of a finite-type affine group `G` is regular, in the sense
that `ker (ad x)` has minimal dimension, exactly when its centralizer `C_G(x)` has minimal dimension
among the centralizers of elements of the Lie algebra. -/
theorem isCentralizerRegular_iff_forall_ringKrullDim_le
    (x : Module.Dual k (Bialgebra.CotangentSpace k H)) :
    LieAlgebra.IsCentralizerRegular k x ↔
      ∀ y : Module.Dual k (Bialgebra.CotangentSpace k H),
        ringKrullDim (H ⧸ (centralizerHopfIdeal H x).toIdeal) ≤
          ringKrullDim (H ⧸ (centralizerHopfIdeal H y).toIdeal) := by
  simp only [LieAlgebra.isCentralizerRegular_iff, ringKrullDim_quotient_centralizerHopfIdeal,
    Nat.cast_le]

end TauCeti
