/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Idempotents.BaseChange
public import TauCeti.RingTheory.Idempotents.Clopen.Basic
public import TauCeti.RingTheory.Spectrum.Prime.FreeLocus

import TauCeti.RingTheory.Spectrum.Prime.Topology

/-!
# Constant-rank decomposition of finitely presented flat modules

For a finitely presented flat module `M` over a commutative ring `R`, the locally constant stalk
rank `Module.rankLocallyConstant R M` attains finitely many values `Module.ranks R M`. The
idempotents attached to its clopen rank fibers form a complete orthogonal family
(`Module.completeOrthogonalIdempotents_rank`), decomposing `M` into the finite product of its base
changes to the quotient rings `R ⧸ (1 - e_k)` (`Module.equivPiRankPieces`), where the `k`-th piece
has constant stalk rank `k` (`Module.rankAtStalk_rankPiece`).

## Main declarations

* `Module.completeOrthogonalIdempotents_rank`: the rank-fiber idempotents of `M` form a complete
  orthogonal family.
* `Module.equivPiRankPieces`: the direct-sum decomposition of `M` into constant-rank pieces.
* `Module.equivPiRankPieces_apply`: the `k`-th coordinate of `m` is `1 ⊗ₜ[R] m`.
* `Module.rankAtStalk_rankPiece`: the `k`-th piece has constant stalk rank `k`.
-/

public section

open scoped TensorProduct
open PrimeSpectrum (isIdempotentElemEquivClopens)

namespace Module

variable (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M]
  [Module.FinitePresentation R M] [Module.Flat R M]

/-- The idempotents attached to the constant-rank loci of a finitely presented flat module form a
complete orthogonal family. -/
theorem completeOrthogonalIdempotents_rank :
    CompleteOrthogonalIdempotents fun k : ranks R M ↦
      (isIdempotentElemEquivClopens.symm ((rankLocallyConstant R M).fiberClopens k.val)).val :=
  PrimeSpectrum.completeOrthogonalIdempotents_fiberClopens (rankLocallyConstant R M)

/-- A finitely presented flat module splits as the product of its base changes to the quotients
cutting out its constant-rank loci. -/
noncomputable def equivPiRankPieces :
    M ≃ₗ[R] ∀ k : ranks R M,
      (R ⧸ Ideal.span
        {1 -
          (isIdempotentElemEquivClopens.symm ((rankLocallyConstant R M).fiberClopens k.val)).val})
        ⊗[R] M :=
  (completeOrthogonalIdempotents_rank R M).moduleTensorProductEquiv M

/-- Each component of the constant-rank decomposition sends `m` to `1 ⊗ₜ[R] m`. -/
@[simp]
theorem equivPiRankPieces_apply (m : M) (k : ranks R M) :
    equivPiRankPieces R M m k = 1 ⊗ₜ[R] m :=
  CompleteOrthogonalIdempotents.moduleTensorProductEquiv_apply _ m k

/-- Over the quotient ring cutting out the rank-`k` locus, the corresponding piece of `M` has
constant stalk rank `k`. -/
theorem rankAtStalk_rankPiece (k : ranks R M)
    (q : PrimeSpectrum (R ⧸ Ideal.span
      {1 -
        (isIdempotentElemEquivClopens.symm ((rankLocallyConstant R M).fiberClopens k.val)).val})) :
    rankAtStalk ((R ⧸ Ideal.span
      {1 - (isIdempotentElemEquivClopens.symm ((rankLocallyConstant R M).fiberClopens k.val)).val})
      ⊗[R] M) q = k.val := by
  let e := (isIdempotentElemEquivClopens.symm ((rankLocallyConstant R M).fiberClopens k.val)).val
  rw [rankAtStalk_baseChange]
  have hD : q.comap (algebraMap R (R ⧸ Ideal.span {1 - e})) ∈ PrimeSpectrum.basicOpen e :=
    PrimeSpectrum.comap_mem_basicOpen_quotient_one_sub e q
  rw [PrimeSpectrum.basicOpen_isIdempotentElemEquivClopens_symm] at hD
  simpa [rankLocallyConstant_apply] using LocallyConstant.mem_fiberClopens.1 hD

end Module
