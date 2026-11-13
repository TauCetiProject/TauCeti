/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Unramified.Locus
import Mathlib.RingTheory.Localization.Basic

/-!
# Unramifiedness at a prime transports along isomorphisms of algebras and rings

`Algebra.IsUnramifiedAt R q` says that the localization of the ambient algebra at `q` is formally
unramified over `R`. An isomorphism `ψ : A ≃ₐ[R] B` of `R`-algebras matches the prime complement
of `q` with that of `q.comap ψ`, so it induces an isomorphism of the two localizations over `R`
and unramifiedness at `q` is equivalent to unramifiedness at `q.comap ψ`.

More generally, a commuting square of ring equivalences `(e₁ : R₁ ≃+* R₂, e₂ : A₁ ≃+* A₂)`
transports formal unramifiedness (`Algebra.FormallyUnramified.of_equiv_equiv`) and hence
unramifiedness at corresponding primes (`RingEquiv.isUnramifiedAt_iff_of_eq_comap`), allowing the
base ring to vary by an isomorphism as well.

## Main results

* `AlgEquiv.isUnramifiedAt_iff_of_eq_comap`: `A` is unramified over `R` at a prime equal to
  `q.comap ψ` if and only if `B` is unramified over `R` at `q`.
* `Algebra.FormallyUnramified.of_equiv_equiv`, `Algebra.FormallyUnramified.iff_of_equiv_equiv`:
  formal unramifiedness transports across a commuting square of ring equivalences.
* `RingEquiv.isUnramifiedAt_iff_of_eq_comap`: `A₁` is unramified over `R₁` at a prime equal to
  `q.comap e₂` if and only if `A₂` is unramified over `R₂` at `q`.
-/

public section

namespace AlgEquiv

variable {R A B : Type*} [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]

/-- **Unramifiedness transports along an isomorphism of `R`-algebras.** For a prime `q` of `B`,
`A` is unramified over `R` at the corresponding prime `q.comap ψ` if and only if `B` is unramified
over `R` at `q`, stated for any prime `p` of `A` equal to `q.comap ψ`. -/
theorem isUnramifiedAt_iff_of_eq_comap (ψ : A ≃ₐ[R] B) {q : Ideal B} [q.IsPrime]
    {p : Ideal A} [p.IsPrime] (hp : p = q.comap ψ) :
    Algebra.IsUnramifiedAt R p ↔ Algebra.IsUnramifiedAt R q := by
  -- The transported prime is the parameter `p` with the equation `hp`, not the term `q.comap ψ`
  -- itself: `Algebra.IsUnramifiedAt` takes the primality of its ideal as an instance argument, so
  -- `rw` cannot turn a statement about `q.comap ψ` into one about `p`, while `subst` can.
  subst hp
  exact Algebra.FormallyUnramified.iff_of_equiv (IsLocalization.algEquivOfAlgEquiv
    (Localization.AtPrime (q.comap ψ)) (Localization.AtPrime q) ψ
      (Ideal.map_primeCompl_comap_of_surjective ψ ψ.surjective q))

end AlgEquiv

namespace Algebra.FormallyUnramified

variable {R₁ A₁ R₂ A₂ : Type*} [CommRing R₁] [CommRing A₁] [Algebra R₁ A₁]
  [CommRing R₂] [CommRing A₂] [Algebra R₂ A₂]

/-- **Formal unramifiedness transports across compatible ring equivalences.** -/
theorem of_equiv_equiv [Algebra.FormallyUnramified R₁ A₁] (e₁ : R₁ ≃+* R₂) (e₂ : A₁ ≃+* A₂)
    (he : (algebraMap R₂ A₂).comp (e₁ : R₁ →+* R₂) = (e₂ : A₁ →+* A₂).comp (algebraMap R₁ A₁)) :
    Algebra.FormallyUnramified R₂ A₂ := by
  let _ : Algebra R₁ R₂ := (e₁ : R₁ →+* R₂).toAlgebra
  let _ : Algebra R₁ A₂ := ((algebraMap R₂ A₂).comp (e₁ : R₁ →+* R₂)).toAlgebra
  have : IsScalarTower R₁ R₂ A₂ := IsScalarTower.of_algebraMap_eq' rfl
  let φ : A₁ →ₐ[R₁] A₂ :=
    { (e₂ : A₁ →+* A₂) with commutes' r := (RingHom.congr_fun he r).symm }
  have : Algebra.FormallyUnramified R₁ A₂ := .of_surjective φ e₂.surjective
  exact .of_restrictScalars R₁ R₂ A₂

/-- **Formal unramifiedness is invariant under compatible ring equivalences.** -/
theorem iff_of_equiv_equiv (e₁ : R₁ ≃+* R₂) (e₂ : A₁ ≃+* A₂)
    (he : (algebraMap R₂ A₂).comp (e₁ : R₁ →+* R₂) = (e₂ : A₁ →+* A₂).comp (algebraMap R₁ A₁)) :
    Algebra.FormallyUnramified R₁ A₁ ↔ Algebra.FormallyUnramified R₂ A₂ :=
  ⟨fun _ ↦ of_equiv_equiv e₁ e₂ he,
    fun _ ↦ of_equiv_equiv e₁.symm e₂.symm <| RingHom.ext fun x ↦
      e₂.eq_symm_apply.mpr <| by simpa using (RingHom.congr_fun he (e₁.symm x)).symm⟩

end Algebra.FormallyUnramified

namespace RingEquiv

variable {R₁ A₁ R₂ A₂ : Type*} [CommRing R₁] [CommRing A₁] [Algebra R₁ A₁]
  [CommRing R₂] [CommRing A₂] [Algebra R₂ A₂]

/-- **Unramifiedness at a prime transports across compatible ring equivalences.** -/
theorem isUnramifiedAt_iff_of_eq_comap (e₁ : R₁ ≃+* R₂) (e₂ : A₁ ≃+* A₂)
    (he : (algebraMap R₂ A₂).comp (e₁ : R₁ →+* R₂) = (e₂ : A₁ →+* A₂).comp (algebraMap R₁ A₁))
    {q : Ideal A₂} [q.IsPrime] {p : Ideal A₁} [p.IsPrime] (hp : p = q.comap e₂) :
    Algebra.IsUnramifiedAt R₁ p ↔ Algebra.IsUnramifiedAt R₂ q := by
  subst hp
  let eLoc : Localization.AtPrime (q.comap e₂) ≃+* Localization.AtPrime q :=
    IsLocalization.ringEquivOfRingEquiv (Localization.AtPrime (q.comap e₂))
      (Localization.AtPrime q) e₂ (Ideal.map_primeCompl_comap_of_surjective e₂ e₂.surjective q)
  refine Algebra.FormallyUnramified.iff_of_equiv_equiv e₁ eLoc (RingHom.ext fun r ↦ ?_)
  rw [RingHom.comp_apply, RingHom.comp_apply,
    IsScalarTower.algebraMap_apply R₁ A₁ (Localization.AtPrime (q.comap e₂)),
    IsScalarTower.algebraMap_apply R₂ A₂ (Localization.AtPrime q)]
  exact (congrArg (algebraMap A₂ (Localization.AtPrime q)) (RingHom.congr_fun he r)).trans
    (IsLocalization.ringEquivOfRingEquiv_eq _ (algebraMap R₁ A₁ r)).symm

end RingEquiv
