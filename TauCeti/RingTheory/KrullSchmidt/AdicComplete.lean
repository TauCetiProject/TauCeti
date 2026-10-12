/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import TauCeti.RingTheory.AdicCompletion.Finite
public import TauCeti.RingTheory.Henselian.Idempotent
public import TauCeti.RingTheory.KrullSchmidt.Noetherian

/-!
# Krull-Schmidt cancellation over a complete local ring

Let `R` be a complete Noetherian local ring and `A` an `R`-algebra, for instance the group algebra
`ℤ_p[G]` of a finite group over the `p`-adic integers. For modules that are finitely generated over
`R`, the input of the Krull-Schmidt theorem is available even though such modules need not have
finite length: the endomorphism ring of an indecomposable one is local. Consequently these modules
cancel from direct sums.

Locality is proved one endomorphism at a time. An endomorphism `f` of an `A`-module `M` that is
finite over `R` is integral over `R` by Cayley-Hamilton, so the commutative subalgebra `R[f]` is a
finite `R`-module. It is therefore complete along the extension of the maximal ideal of `R`, hence
Henselian there, and its reduction is a finite-dimensional algebra over the residue field.
Idempotents of `R[f]` are idempotents of `End_A(M)`, so indecomposability of `M` leaves `R[f]` only
the trivial ones, and `R[f]` is local by
`TauCeti.HenselianRing.isLocalRing_of_forall_isIdempotentElem`. So `f` or `1 - f` is a unit.

⚠ Completeness is essential: over `ℤ` the analogous cancellation fails for integral group rings
(Swan's stably free non-free modules over generalized quaternion groups).

## Main results

* `TauCeti.isLocalRing_end_of_isIndecomposable_of_isAdicComplete`: an indecomposable `A`-module
  that is finite over a complete Noetherian local ring `R` has a local endomorphism ring.
* `TauCeti.nonempty_linearEquiv_of_prod_linearEquiv_of_isAdicComplete`: **Krull-Schmidt
  cancellation** for a summand that is finite over a complete Noetherian local ring.

## References

* C. W. Curtis, I. Reiner, *Methods of Representation Theory, Vol. I*, §6.
* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, second edition,
  Proposition (5.6.10)(i).
-/

public section

open IsLocalRing
open scoped IsMulCommutative

namespace TauCeti

variable (R : Type*) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
  [IsAdicComplete (maximalIdeal R) R] {A : Type*} [Ring A] [Algebra R A]

include R in
/-- **Indecomposable modules over a complete local ring have local endomorphism rings.** Let `R`
be a complete Noetherian local ring and `A` an `R`-algebra. The endomorphism ring of an
indecomposable `A`-module that is finitely generated over `R` is local. -/
theorem isLocalRing_end_of_isIndecomposable_of_isAdicComplete {M : Type*} [AddCommGroup M]
    [Module A M] [Module R M] [IsScalarTower R A M] [Module.Finite R M]
    (hM : IsIndecomposableModule A M) : IsLocalRing (Module.End A M) := by
  have := hM.nontrivial
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun f ↦ ?_
  -- `f` is integral over `R`, being an `R`-linear endomorphism of the finite `R`-module `M`.
  have hint : IsIntegral R f := by
    let ρ : Module.End A M →ₐ[R] Module.End R M :=
      { toFun g := g.restrictScalars R
        map_one' := rfl
        map_mul' _ _ := rfl
        map_zero' := rfl
        map_add' _ _ := rfl
        commutes' _ := rfl }
    exact (isIntegral_algHom_iff ρ fun _ _ h ↦ LinearMap.restrictScalars_injective R h).mp
      (Algebra.IsIntegral.isIntegral (ρ f))
  -- The commutative subalgebra `S = R[f]` is finite over `R`, so Henselian along `J = 𝔪 S`, with
  -- Artinian quotient `S ⧸ J`.
  let S := Algebra.adjoin R {f}
  have : Module.Finite R S := Algebra.finite_adjoin_simple_of_isIntegral hint
  let J : Ideal S := (maximalIdeal R).map (algebraMap R S)
  have : IsAdicComplete J S :=
    (IsAdicComplete.map_algebraMap_iff _ _).mpr (IsAdicComplete.of_finite _ S)
  have : IsArtinianRing (S ⧸ J) := by
    let := Ideal.Quotient.field (maximalIdeal R)
    have : Module.Finite (R ⧸ maximalIdeal R) (S ⧸ J) :=
      .of_restrictScalars_finite R _ _
    exact IsArtinianRing.of_finite (R ⧸ maximalIdeal R) (S ⧸ J)
  -- Its idempotents are idempotents of `End_A(M)`, hence trivial, so `S` is local.
  have : IsLocalRing S := HenselianRing.isLocalRing_of_forall_isIdempotentElem J fun e he ↦
    (hM.eq_zero_or_eq_one_of_isIdempotentElem (he.map S.val)).imp Subtype.ext Subtype.ext
  exact (IsLocalRing.isUnit_or_isUnit_one_sub_self
    (⟨f, Algebra.self_mem_adjoin_singleton R f⟩ : S)).imp (·.map S.val) (·.map S.val)

include R in
/-- **Krull-Schmidt cancellation over a complete local ring.** Let `R` be a complete Noetherian
local ring and `A` an `R`-algebra. If `P` is an `A`-module that is finitely generated over `R`, a
linear equivalence `M × P ≃ N × P` of `A`-modules induces a linear equivalence `M ≃ N`. No
hypothesis is placed on `M` and `N`. -/
theorem nonempty_linearEquiv_of_prod_linearEquiv_of_isAdicComplete {M N P : Type*}
    [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    [AddCommGroup P] [Module A P] [Module R P] [IsScalarTower R A P] [Module.Finite R P]
    (h : Nonempty ((M × P) ≃ₗ[A] (N × P))) : Nonempty (M ≃ₗ[A] N) := by
  have : IsNoetherian A P := isNoetherian_of_tower R inferInstance
  refine nonempty_linearEquiv_of_prod_linearEquiv_of_isNoetherian (fun Q _ _ hQ ↦ ?_) h
  have : Module.Finite R Q :=
    .of_injective (Q.subtype.restrictScalars R) Subtype.val_injective
  exact isLocalRing_end_of_isIndecomposable_of_isAdicComplete R hQ

end TauCeti
