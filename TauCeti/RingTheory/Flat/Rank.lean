/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.RingTheory.IsTensorProduct
public import Mathlib.RingTheory.LocalRing.Module
public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
public import Mathlib.RingTheory.Spectrum.Prime.Noetherian
public import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Multiplicativity of the rank of finite flat modules in towers

Let `A` be a finite flat `R`-algebra and `M` a finite flat `A`-module whose rank
`Module.rankAtStalk M` is constant, equal to `n`, on `Spec A`. Then `M` is a finite flat
`R`-module whose rank at every prime of `R` is `n` times the rank of `A`
(`TauCeti.Module.rankAtStalk_eq_mul_of_rankAtStalk_eq`). Geometrically, for finite locally free
morphisms `X ⟶ Y ⟶ S` the degree of `X ⟶ S` is the product of the degrees, provided the degree
of `X ⟶ Y` is constant; without constancy there is no such formula, since the primes of `A` over
a given prime of `R` can carry different ranks.

The rank of `M` at a prime `p` of `R` is the dimension of the fibre `κ(p) ⊗[R] M`, which is a
module over the fibre `κ(p) ⊗[R] A`, a finite `κ(p)`-algebra. The tower formula therefore reduces
to a statement over a finite algebra `A` over a field `k`. Such an `A` is Artinian, hence the
product of its finitely many localizations `A_q`, so a finite flat `A`-module `M` splits as the
product of the free `A_q`-modules `A_q ⊗[A] M`. This gives
`finrank k M = ∑ᶠ q, rankAtStalk M q * finrank k A_q`
(`TauCeti.Module.finrank_eq_finsum_rankAtStalk_mul`).

## Main results

* `TauCeti.Module.finrank_eq_finsum_rankAtStalk_mul`: over a finite algebra `A` over a field
  `k`, the `k`-dimension of a finite flat `A`-module, as a sum over the primes of `A`.
* `TauCeti.Module.finrank_eq_mul_finrank_of_rankAtStalk_eq`: if moreover the rank is constant,
  equal to `n`, then `finrank k M = n * finrank k A`.
* `TauCeti.Module.rankAtStalk_eq_mul_of_rankAtStalk_eq`: the tower formula for ranks at stalks.

## References

* [Stacks Project, Tag 00JA](https://stacks.math.columbia.edu/tag/00JA): an Artinian ring is the
  product of its localizations at its maximal ideals.
* [Stacks Project, Tag 02KA](https://stacks.math.columbia.edu/tag/02KA): the degree of a finite
  locally free morphism.
-/

public section

open Module TensorProduct

namespace TauCeti.Module

section Field

variable {k A M : Type*} [Field k] [CommRing A] [Algebra k A] [Module.Finite k A]
  [AddCommGroup M] [Module A M] [Module k M] [IsScalarTower k A M]
  [Module.Finite A M] [Module.Flat A M]

attribute [local instance] Module.free_of_flat_of_isLocalRing in
/-- Over a finite algebra `A` over a field `k`, the `k`-dimension of a finite flat `A`-module `M`
is the sum, over the finitely many primes `q` of `A`, of the rank of `M` at `q` times the
`k`-dimension of the local ring `A_q`. -/
theorem finrank_eq_finsum_rankAtStalk_mul :
    finrank k M = ∑ᶠ q : PrimeSpectrum A,
      rankAtStalk M q * finrank k (Localization.AtPrime q.asIdeal) := by
  classical
  have : IsArtinianRing A := IsArtinianRing.of_finite k A
  have := Fintype.ofFinite (PrimeSpectrum A)
  -- `A` is the product of its localizations, so `M` is the product of the `A_q ⊗[A] M`.
  let e : M ≃ₗ[A] ∀ q : PrimeSpectrum A, Localization.AtPrime q.asIdeal ⊗[A] M :=
    (TensorProduct.lid A M).symm ≪≫ₗ
      TensorProduct.congr (PrimeSpectrum.toPiLocalizationEquiv A).toLinearEquiv (.refl A M) ≪≫ₗ
      TensorProduct.piLeft (R := A) (N := M)
        (M := fun q : PrimeSpectrum A ↦ Localization.AtPrime q.asIdeal)
  have : Module.Finite k (∀ q : PrimeSpectrum A, Localization.AtPrime q.asIdeal ⊗[A] M) :=
    have : Module.Finite k M := .trans A M
    .equiv (e.restrictScalars k)
  have (q : PrimeSpectrum A) : Module.Finite k (Localization.AtPrime q.asIdeal ⊗[A] M) :=
    .of_surjective (LinearMap.proj (R := k)
      (φ := fun q : PrimeSpectrum A ↦ Localization.AtPrime q.asIdeal ⊗[A] M) q)
      (Function.surjective_eval q)
  rw [(e.restrictScalars k).finrank_eq, Module.finrank_pi_fintype, finsum_eq_sum_of_fintype]
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  -- Each factor `A_q ⊗[A] M` is free over the local ring `A_q`, of rank `rankAtStalk M q`.
  rw [← Module.finrank_mul_finrank k (Localization.AtPrime q.asIdeal), mul_comm,
    rankAtStalk_eq_finrank_tensorProduct]

/-- Over a finite algebra `A` over a field `k`, a finite flat `A`-module of constant rank `n` has
`k`-dimension `n * finrank k A`. -/
theorem finrank_eq_mul_finrank_of_rankAtStalk_eq {n : ℕ} (h : ∀ q, rankAtStalk (R := A) M q = n) :
    finrank k M = n * finrank k A := by
  rw [finrank_eq_finsum_rankAtStalk_mul (A := A) (M := M),
    finrank_eq_finsum_rankAtStalk_mul (A := A) (M := A)]
  have : IsArtinianRing A := IsArtinianRing.of_finite k A
  have := Fintype.ofFinite (PrimeSpectrum A)
  simp_rw [finsum_eq_sum_of_fintype, Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  have : Nontrivial A := q.nontrivial
  rw [h, rankAtStalk_self, Pi.one_apply, one_mul]

end Field

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
/-- **The rank is multiplicative in towers.** If `A` is a finite flat `R`-algebra and `M` is a
finite flat `A`-module of constant rank `n`, then the rank of `M` over `R` at a prime `p` is `n`
times the rank of `A` at `p`. -/
theorem rankAtStalk_eq_mul_of_rankAtStalk_eq {R A M : Type*} [CommRing R] [CommRing A]
    [Algebra R A] [Module.Finite R A] [Module.Flat R A] [AddCommGroup M] [Module A M]
    [Module R M] [IsScalarTower R A M] [Module.Finite A M] [Module.Flat A M] {n : ℕ}
    (h : ∀ q, rankAtStalk (R := A) M q = n) (p : PrimeSpectrum R) :
    rankAtStalk (R := R) M p = n * rankAtStalk (R := R) A p := by
  have : Module.Finite R M := .trans A M
  have : Module.Flat R M := .trans R A M
  -- Both ranks are dimensions of fibres over `κ(p)`, and the fibre of `M` is the base change of
  -- `M` to the fibre `κ(p) ⊗[R] A` of `A`, a finite flat module of constant rank `n`.
  let κ := p.asIdeal.ResidueField
  rw [rankAtStalk_eq, rankAtStalk_eq,
    ← (Algebra.IsPushout.cancelBaseChange R κ A (κ ⊗[R] A) M).finrank_eq]
  refine finrank_eq_mul_finrank_of_rankAtStalk_eq fun q ↦ ?_
  rw [rankAtStalk_baseChange, h]

end TauCeti.Module
