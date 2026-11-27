/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.StableEquivalent
public import TauCeti.RingTheory.Spectrum.Prime.FreeLocus
import Mathlib.RingTheory.LocalRing.Module
import TauCeti.Algebra.Module.Projective.Reduction.Basic
import TauCeti.RingTheory.Ideal.Quotient.ChineseRemainder

/-!
# Finitely generated projective modules over semilocal rings

Over a commutative semilocal ring `R`, a ring with finitely many maximal ideals, a finitely
generated projective module is determined up to isomorphism by its rank function
`Module.rankAtStalk`. By Chinese remainder for modules, the reduction of `M` modulo the Jacobson
radical `J` of `R` is the product of the fibres `(R ⧸ P) ⊗[R] M` over the maximal ideals `P`, and
each fibre is a vector space over the field `R ⧸ P` whose dimension is the rank of `M` at `P`.
Equal ranks therefore give isomorphic reductions `M ⧸ J M ≃ N ⧸ J N`, and projective modules with
isomorphic radical reductions are isomorphic (`Ideal.nonempty_linearEquiv_of_quotient_smul_top`).

The Chinese remainder step uses `Ideal.quotientSMulTopEquivPiTensorProduct`.

Consequences: stably equivalent finitely generated projective modules over a semilocal ring are
isomorphic (cancellation of free summands), and if the spectrum of `R` is connected, so that the
rank is constant, every finitely generated projective module is free. The rank function need not
be constant in general: over `k × k` the module `k × 0` has rank `1` at one point and `0` at the
other.

This is the module-level input for the classification of the projective `K₀` of a commutative
semilocal ring by locally constant ranks.

## Main results

* `Module.nonempty_linearEquiv_of_finrank_quotient_tensorProduct_eq`: over a semilocal ring,
  finitely generated projective modules whose fibres at the maximal ideals have equal dimensions
  are isomorphic.
* `Module.nonempty_linearEquiv_iff_rankAtStalk_eq`: over a semilocal ring, finitely generated
  projective modules are isomorphic if and only if they have the same rank function.
* `TauCeti.StableEquivalent.nonempty_linearEquiv_of_finite_maximalSpectrum`: over a semilocal ring,
  stably equivalent finitely generated projective modules are isomorphic.
* `Module.free_of_connectedSpace_of_finite_maximalSpectrum`: over a semilocal ring with connected
  spectrum, every finitely generated projective module is free.

## References

* Charles A. Weibel, *The K-book: An Introduction to Algebraic K-theory*, Chapter II, §2,
  Exercise 2.6, p. 79.
* [The Stacks Project, Tag 02M9](https://stacks.math.columbia.edu/tag/02M9)
-/

public section

open Function TensorProduct

namespace Module

variable {R : Type*} [CommRing R] [Finite (MaximalSpectrum R)]
  {M N : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M] [Projective R M]
  [AddCommGroup N] [Module R N] [Module.Finite R N] [Projective R N]

/-- **Projective modules over a semilocal ring are determined by their fibres.** If `R` has
finitely many maximal ideals, and the fibres `(R ⧸ P) ⊗[R] M` and `(R ⧸ P) ⊗[R] N` of two
finitely generated projective modules have the same dimension over `R ⧸ P` at every maximal
ideal `P`, then `M` and `N` are isomorphic. -/
theorem nonempty_linearEquiv_of_finrank_quotient_tensorProduct_eq
    (h : ∀ P : MaximalSpectrum R, finrank (R ⧸ P.asIdeal) ((R ⧸ P.asIdeal) ⊗[R] M) =
      finrank (R ⧸ P.asIdeal) ((R ⧸ P.asIdeal) ⊗[R] N)) :
    Nonempty (M ≃ₗ[R] N) := by
  let I : MaximalSpectrum R → Ideal R := MaximalSpectrum.asIdeal
  have hI : Pairwise (IsCoprime on I) := fun P Q hPQ ↦
    Ideal.isCoprime_of_isMaximal (MaximalSpectrum.ext_iff.ne.mp hPQ)
  -- The intersection of the maximal ideals lies in the Jacobson radical.
  have hJ : ⨅ P, I P ≤ Ring.jacobson R := by
    rw [Ring.jacobson_eq_sInf_isMaximal]
    exact le_sInf fun P hP ↦ iInf_le I ⟨P, hP⟩
  refine Ideal.nonempty_linearEquiv_of_quotient_smul_top (⨅ P, I P) M N hJ ⟨?_⟩
  -- Fibres of equal dimension over the field `R ⧸ P` are isomorphic.
  have fibre (P : MaximalSpectrum R) : ((R ⧸ I P) ⊗[R] M) ≃ₗ[R] (R ⧸ I P) ⊗[R] N :=
    let _ := Ideal.Quotient.field P.asIdeal
    (LinearEquiv.ofFinrankEq _ _ (h P)).restrictScalars R
  -- By Chinese remainder, `M ⧸ (⋂ P) M` is the product of the fibres `(R ⧸ P) ⊗[R] M`.
  exact (Ideal.quotientSMulTopEquivPiTensorProduct M I hI).trans
    ((LinearEquiv.piCongrRight fibre).trans (Ideal.quotientSMulTopEquivPiTensorProduct N I hI).symm)

/-- **Projective modules over a semilocal ring are classified by rank.** If `R` has finitely many
maximal ideals, two finitely generated projective `R`-modules are isomorphic if and only if they
have the same rank at every prime. -/
theorem nonempty_linearEquiv_iff_rankAtStalk_eq :
    Nonempty (M ≃ₗ[R] N) ↔ rankAtStalk (R := R) M = rankAtStalk (R := R) N := by
  refine ⟨fun ⟨e⟩ ↦ rankAtStalk_eq_of_equiv e, fun h ↦ ?_⟩
  refine nonempty_linearEquiv_of_finrank_quotient_tensorProduct_eq fun P ↦ ?_
  rw [finrank_quotient_tensorProduct_eq_rankAtStalk, finrank_quotient_tensorProduct_eq_rankAtStalk,
    h]

/-- **Projective modules over a connected semilocal ring are free.** If `R` has finitely many
maximal ideals and its prime spectrum is connected, every finitely generated projective
`R`-module is free. -/
theorem free_of_connectedSpace_of_finite_maximalSpectrum [ConnectedSpace (PrimeSpectrum R)] :
    Free R M := by
  have := finitePresentation_of_projective R M
  obtain ⟨p⟩ := ‹ConnectedSpace (PrimeSpectrum R)›.toNonempty
  -- The rank of `M` is locally constant, hence constant on the connected spectrum.
  have hconst (q : PrimeSpectrum R) : rankAtStalk M q = rankAtStalk M p :=
    isLocallyConstant_rankAtStalk.apply_eq_of_isPreconnected isPreconnected_univ trivial trivial
  refine free_of_flat_of_finrank_eq R M (rankAtStalk M p) fun P ↦ ?_
  rw [finrank_quotient_tensorProduct_eq_rankAtStalk, hconst]

end Module

namespace TauCeti.StableEquivalent

variable {R : Type*} [CommRing R] [Finite (MaximalSpectrum R)]
  {M N : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Projective R M]
  [AddCommGroup N] [Module R N] [Module.Finite R N] [Module.Projective R N]

/-- **Cancellation over semilocal rings.** If `R` has finitely many maximal ideals, stably
equivalent finitely generated projective `R`-modules are isomorphic: `M × Rⁿ ≃ₗ[R] N × Rⁿ`
implies `M ≃ₗ[R] N`. -/
theorem nonempty_linearEquiv_of_finite_maximalSpectrum (h : StableEquivalent R M N) :
    Nonempty (M ≃ₗ[R] N) := by
  obtain ⟨n, ⟨e⟩⟩ := stableEquivalent_iff.1 h
  refine Module.nonempty_linearEquiv_iff_rankAtStalk_eq.2 ?_
  have h := Module.rankAtStalk_eq_of_equiv e
  rw [Module.rankAtStalk_prod, Module.rankAtStalk_prod] at h
  exact add_right_cancel h

end TauCeti.StableEquivalent
