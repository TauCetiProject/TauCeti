/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Chebotarev.FrobeniusPrimeSet
public import TauCeti.NumberTheory.NumberField.Cyclotomic.Compositum

/-!
# Tagged Frobenius fibres in a cyclotomic compositum

Let `L / K` be Galois and let `M = L(μ_m)`. When `m` is coprime to the discriminant of `L`, the
joint restriction isomorphism

`Gal(M/K) ≃ Gal(L/K) × (ZMod m)ˣ`

allows a Frobenius condition over `M / K` to carry both a prescribed element `σ : Gal(L/K)` and
a cyclotomic tag `τ : (ZMod m)ˣ`. This file packages the resulting prime fibre and proves that
distinct tags give disjoint fibres, whatever the base elements.

The point is slightly stronger than injectivity of the product equivalence. Equality of Frobenius
fibres is indexed by *conjugacy classes*, so one must show that two elements whose cyclotomic
coordinates differ cannot be conjugate. Applying the cyclotomic character reduces conjugacy to
equality because `(ZMod m)ˣ` is commutative.

## Main definitions

* `NumberField.Chebotarev.taggedFrobeniusPrimeSet`: the primes whose Artin class over `M / K` is
  represented by the tag `(σ, τ)`.

## Main results

* `NumberField.Chebotarev.disjoint_taggedFrobeniusPrimeSet`: the fibres of `(σ₁, τ)` and
  `(σ₂, υ)` are disjoint whenever `τ ≠ υ`.
* `NumberField.Chebotarev.pairwise_disjoint_taggedFrobeniusPrimeSet`: the tagged fibres for a
  fixed `σ` are pairwise disjoint as `τ` varies.

## References

This implements the pairwise-disjointness target of Layer 7.5, “Why the tagged fixed fields are
cyclotomic”, of the
[Chebotarev roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/Chebotarev/README.md),
which asks to prove pairwise disjointness of the tagged Frobenius fibres for distinct `τ`.
-/

public section

open scoped NumberField

namespace NumberField.Chebotarev

variable (K L M : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Field M]
  [Algebra K L] [Algebra K M] [Algebra L M] [IsScalarTower K L M] [IsGalois K L]
  (m : ℕ) [NeZero m] [IsCyclotomicExtension {m} L M]

/-- **The Frobenius fibre carrying a fixed base element and cyclotomic tag.** Under the joint
restriction isomorphism `Gal(M/K) ≃ Gal(L/K) × (ZMod m)ˣ`, this is the prime fibre of the
conjugacy class represented by the inverse image of `(σ, τ)`.

The number-field and Galois structures on `M` are consequences of the cyclotomic tower, so they
are installed internally rather than required from callers. -/
noncomputable def taggedFrobeniusPrimeSet
    (hcop : ((NumberField.discr L).natAbs).Coprime m) {ζ : M} (hζ : IsPrimitiveRoot ζ m)
    (σ : Gal(L/K)) (τ : (ZMod m)ˣ) : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 K)) := by
  letI : FiniteDimensional L M := IsCyclotomicExtension.finiteDimensional (S := {m}) (K := L) M
  letI : NumberField M := NumberField.of_module_finite L M
  letI : IsGalois K M :=
    IsCyclotomicExtension.isGalois_of_isGalois_of_isCyclotomicExtension K L M m
  exact frobeniusPrimeSet K M
    (ConjClasses.mk ((IsCyclotomicExtension.galEquivProd K L M m hcop hζ).symm (σ, τ)))

/-- The tagged fibre is the ordinary Frobenius fibre of the conjugacy class represented by the
corresponding element of `Gal(M/K)`. This is the unfolding interface for applying results about
`frobeniusPrimeSet`; the instances on `M` are precisely those that its right-hand side requires. -/
@[simp]
theorem taggedFrobeniusPrimeSet_def [NumberField M] [IsGalois K M]
    (hcop : ((NumberField.discr L).natAbs).Coprime m) {ζ : M} (hζ : IsPrimitiveRoot ζ m)
    (σ : Gal(L/K)) (τ : (ZMod m)ˣ) :
    taggedFrobeniusPrimeSet K L M m hcop hζ σ τ =
      frobeniusPrimeSet K M
        (ConjClasses.mk ((IsCyclotomicExtension.galEquivProd K L M m hcop hζ).symm (σ, τ))) := by
  rw [taggedFrobeniusPrimeSet]

/-- **Distinct cyclotomic tags give disjoint Frobenius fibres.** The fibres indexed by
`(σ₁, τ)` and `(σ₂, υ)` are disjoint whenever `τ ≠ υ`, whatever `σ₁ σ₂ : Gal(L/K)`.

Disjointness is what allows the densities of the separate tagged fibres to be added, so this is
the form consumed by lower-bound density estimates over the compositum. -/
theorem disjoint_taggedFrobeniusPrimeSet
    (hcop : ((NumberField.discr L).natAbs).Coprime m) {ζ : M} (hζ : IsPrimitiveRoot ζ m)
    (σ₁ σ₂ : Gal(L/K)) {τ υ : (ZMod m)ˣ} (hτυ : τ ≠ υ) :
    Disjoint (taggedFrobeniusPrimeSet K L M m hcop hζ σ₁ τ)
      (taggedFrobeniusPrimeSet K L M m hcop hζ σ₂ υ) := by
  let _ : FiniteDimensional L M :=
    IsCyclotomicExtension.finiteDimensional (S := {m}) (K := L) M
  let _ : NumberField M := NumberField.of_module_finite L M
  let _ : IsGalois K M :=
    IsCyclotomicExtension.isGalois_of_isGalois_of_isCyclotomicExtension K L M m
  apply disjoint_frobeniusPrimeSet
  intro hclasses
  apply hτυ
  apply isConj_iff_eq.mp
  have hconj := (hζ.autToPow K).map_isConj
    (ConjClasses.mk_eq_mk_iff_isConj.mp hclasses)
  simpa using hconj

/-- **Tagged fibres over a fixed base element are pairwise disjoint.** For a fixed
`σ : Gal(L/K)`, the fibres indexed by `(σ, τ)` are pairwise disjoint as `τ : (ZMod m)ˣ` varies. -/
theorem pairwise_disjoint_taggedFrobeniusPrimeSet
    (hcop : ((NumberField.discr L).natAbs).Coprime m) {ζ : M} (hζ : IsPrimitiveRoot ζ m)
    (σ : Gal(L/K)) :
    Pairwise (Function.onFun Disjoint (taggedFrobeniusPrimeSet K L M m hcop hζ σ)) :=
  fun _ _ hτυ ↦ disjoint_taggedFrobeniusPrimeSet K L M m hcop hζ σ σ hτυ

end NumberField.Chebotarev
