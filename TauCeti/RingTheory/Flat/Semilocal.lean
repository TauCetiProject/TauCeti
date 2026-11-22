/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Spectrum.Maximal.Defs
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import TauCeti.RingTheory.Idempotents.Clopen.RankModule

import Mathlib.RingTheory.LocalRing.Module
import TauCeti.RingTheory.Idempotents.Quotient.Principal
import TauCeti.RingTheory.Spectrum.Maximal.Basic
import TauCeti.RingTheory.Spectrum.Prime.FreeLocus
import TauCeti.RingTheory.Spectrum.Prime.RankDecomposition

/-!
# Flat modules over commutative semilocal rings

Over a commutative semilocal ring (`Finite (MaximalSpectrum R)`), every constant-rank piece of a
finitely presented flat module `M` is free over its quotient ring by
`Module.nonempty_basis_of_flat_of_finrank_eq`, so `M` is linearly isomorphic to
`TauCeti.ClopenRankModule R (Module.rankLocallyConstant R M)`. When `Spec R` is preconnected,
`M` has constant stalk rank and is therefore free.

## Main results

* `TauCeti.free_of_finite_maximalSpectrum_of_preconnectedSpace`: a finitely presented flat module
  over a commutative semilocal ring with preconnected prime spectrum is free.
* `TauCeti.nonempty_linearEquiv_clopenRankModule_of_finite_maximalSpectrum`: over a commutative
  semilocal ring, every finitely presented flat module is isomorphic to the clopen-glued module of
  its rank function.

## References

* The Stacks Project, Tags 00EE and 02M9.
-/

public section

open scoped TensorProduct
open PrimeSpectrum (isIdempotentElemEquivClopens)

namespace TauCeti

/-- Over a commutative semilocal ring with preconnected prime spectrum (for instance a local ring
or a connected semilocal domain), every finitely presented flat module is free. -/
theorem free_of_finite_maximalSpectrum_of_preconnectedSpace
    {R : Type*} [CommRing R] [Finite (MaximalSpectrum R)] [PreconnectedSpace (PrimeSpectrum R)]
    (M : Type*) [AddCommGroup M] [Module R M] [Module.FinitePresentation R M] [Module.Flat R M] :
    Module.Free R M := by
  rcases subsingleton_or_nontrivial R with _ | _
  · have : Subsingleton M := Module.subsingleton R M
    exact Module.Free.of_subsingleton R M
  · obtain ⟨p₀⟩ : Nonempty (PrimeSpectrum R) := inferInstance
    refine Module.free_of_flat_of_finrank_eq R M (Module.rankAtStalk M p₀) fun P ↦ ?_
    rw [Module.finrank_quotient_tensorProduct_eq_rankAtStalk]
    exact (Module.isLocallyConstant_rankAtStalk (R := R) (M := M)).apply_eq_of_preconnectedSpace
      P.toPrimeSpectrum p₀

/-- **Semilocal module classification.** Over a commutative semilocal ring, every finitely
presented flat module `M` is linearly isomorphic to `ClopenRankModule R (rank M)`. -/
theorem nonempty_linearEquiv_clopenRankModule_of_finite_maximalSpectrum
    {R : Type*} [CommRing R] [Finite (MaximalSpectrum R)]
    (M : Type*) [AddCommGroup M] [Module R M] [Module.FinitePresentation R M] [Module.Flat R M] :
    Nonempty (M ≃ₗ[R] ClopenRankModule R (Module.rankLocallyConstant R M)) := by
  let r := Module.rankLocallyConstant R M
  have hpiece (k : Module.ranks R M) : Nonempty
      (((R ⧸ Ideal.span
          {1 - (isIdempotentElemEquivClopens.symm (r.fiberClopens k.val)).val}) ⊗[R] M)
        ≃ₗ[R] (Fin k.val →
          (Ideal.span
            {(isIdempotentElemEquivClopens.symm (r.fiberClopens k.val)).val} : Ideal R))) := by
    let e := (isIdempotentElemEquivClopens.symm (r.fiberClopens k.val)).val
    let Rk := R ⧸ Ideal.span {1 - e}
    obtain ⟨b⟩ := Module.nonempty_basis_of_flat_of_finrank_eq Rk (Rk ⊗[R] M) k.val fun P ↦ by
      rw [Module.finrank_quotient_tensorProduct_eq_rankAtStalk]
      exact Module.rankAtStalk_rankPiece R M k P.toPrimeSpectrum
    exact ⟨(b.equivFun.restrictScalars R).trans <| LinearEquiv.piCongrRight fun _ ↦
      (isIdempotentElemEquivClopens.symm _).property.spanSingletonEquivQuotientOneSub.symm⟩
  exact ⟨(Module.equivPiRankPieces R M).trans
    ((LinearEquiv.piCongrRight fun k ↦ Classical.choice (hpiece k)).trans
      (ClopenRankModule.equivPi R r).symm)⟩

end TauCeti
