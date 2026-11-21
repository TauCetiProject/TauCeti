/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Unramified.Locus
import Mathlib.RingTheory.RingHom.Unramified

/-!
# Formal unramifiedness and unramifiedness at a prime along ring and algebra isomorphisms

Formal unramifiedness and unramifiedness at a prime are invariant under any commuting square of
ring isomorphisms `f : R ≃+* R'` and `g : A ≃+* B` intertwining `algebraMap R A` and
`algebraMap R' B`. For `Algebra.FormallyUnramified`, this follows from the stability of
`RingHom.FormallyUnramified` under composition and surjective ring homomorphisms. For
`Algebra.IsUnramifiedAt`, `g` induces a ring isomorphism between the localizations at `q.comap g`
and `q` intertwining the base maps through `f`.

Specialization to a fixed base ring `R` and an algebra equivalence `ψ : A ≃ₐ[R] B` yields
`AlgEquiv.isUnramifiedAt_iff_of_eq_comap`.

## Main results

* `Algebra.FormallyUnramified.of_equiv_equiv`, `Algebra.FormallyUnramified.iff_of_equiv_equiv`:
  formal unramifiedness transports along a commuting square of ring isomorphisms.
* `Algebra.isUnramifiedAt_iff_of_equiv_equiv`, `Algebra.IsUnramifiedAt.of_equiv_equiv`:
  unramifiedness at a prime transports along a commuting square of ring isomorphisms.
* `AlgEquiv.isUnramifiedAt_iff_of_eq_comap`: `A` is unramified over `R` at a prime equal to
  `q.comap ψ` if and only if `B` is unramified over `R` at `q`.
-/

public section

namespace Algebra

variable {R A R' B : Type*} [CommRing R] [CommRing A] [Algebra R A]
  [CommRing R'] [CommRing B] [Algebra R' B]

/-- **Formal unramifiedness transports along a commuting square of ring isomorphisms.** -/
theorem FormallyUnramified.of_equiv_equiv [FormallyUnramified R A]
    (f : R ≃+* R') (g : A ≃+* B)
    (hcomp : (algebraMap R' B).comp (f : R →+* R') = (g : A →+* B).comp (algebraMap R A)) :
    FormallyUnramified R' B := by
  have h : algebraMap R' B = ((g : A →+* B).comp (algebraMap R A)).comp (f.symm : R' →+* R) := by
    ext x
    simpa using RingHom.congr_fun hcomp (f.symm x)
  rw [← RingHom.formallyUnramified_algebraMap, h]
  exact .comp (.of_surjective f.symm.surjective)
    (.comp (RingHom.formallyUnramified_algebraMap.2 inferInstance) (.of_surjective g.surjective))

/-- **Formal unramifiedness is invariant under a commuting square of ring isomorphisms.** -/
theorem FormallyUnramified.iff_of_equiv_equiv
    (f : R ≃+* R') (g : A ≃+* B)
    (hcomp : (algebraMap R' B).comp (f : R →+* R') = (g : A →+* B).comp (algebraMap R A)) :
    FormallyUnramified R A ↔ FormallyUnramified R' B :=
  ⟨fun _ ↦ FormallyUnramified.of_equiv_equiv f g hcomp,
    fun _ ↦ FormallyUnramified.of_equiv_equiv f.symm g.symm <| by
      ext x
      simpa [RingEquiv.eq_symm_apply] using (RingHom.congr_fun hcomp (f.symm x)).symm⟩

/-- **Unramifiedness at a prime is invariant under a commuting square of ring isomorphisms.**
For a prime `q` of `B`, `A` is unramified over `R` at any prime `p` equal to `q.comap g` if and
only if `B` is unramified over `R'` at `q`. -/
theorem isUnramifiedAt_iff_of_equiv_equiv
    (f : R ≃+* R') (g : A ≃+* B)
    (hcomp : (algebraMap R' B).comp (f : R →+* R') = (g : A →+* B).comp (algebraMap R A))
    {q : Ideal B} [q.IsPrime] {p : Ideal A} [p.IsPrime] (hp : p = q.comap g) :
    IsUnramifiedAt R p ↔ IsUnramifiedAt R' q := by
  -- The transported prime is the parameter `p` with the equation `hp`, not the term `q.comap g`
  -- itself: `Algebra.IsUnramifiedAt` takes the primality of its ideal as an instance argument, so
  -- `rw` cannot turn a statement about `q.comap g` into one about `p`, while `subst` can.
  subst hp
  let e : Localization.AtPrime (q.comap g) ≃+* Localization.AtPrime q :=
    IsLocalization.ringEquivOfRingEquiv (Localization.AtPrime (q.comap g))
      (Localization.AtPrime q) g (g.map_primeCompl_comap_eq q)
  refine FormallyUnramified.iff_of_equiv_equiv f e ?_
  ext x
  have hx := RingHom.congr_fun hcomp x
  simp only [RingHom.coe_comp, RingEquiv.coe_toRingHom, Function.comp_apply] at hx ⊢
  rw [IsScalarTower.algebraMap_apply R' B, IsScalarTower.algebraMap_apply R A, hx]
  exact (IsLocalization.ringEquivOfRingEquiv_eq _ (algebraMap R A x)).symm

/-- **Unramifiedness at a prime transports along a commuting square of ring isomorphisms.** -/
theorem IsUnramifiedAt.of_equiv_equiv
    (f : R ≃+* R') (g : A ≃+* B)
    (hcomp : (algebraMap R' B).comp (f : R →+* R') = (g : A →+* B).comp (algebraMap R A))
    {q : Ideal B} [q.IsPrime] {p : Ideal A} [p.IsPrime] (hp : p = q.comap g)
    [IsUnramifiedAt R p] : IsUnramifiedAt R' q :=
  (isUnramifiedAt_iff_of_equiv_equiv f g hcomp hp).1 inferInstance

end Algebra

namespace AlgEquiv

variable {R A B : Type*} [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]

/-- **Unramifiedness transports along an isomorphism of `R`-algebras.** For a prime `q` of `B`,
`A` is unramified over `R` at the corresponding prime `q.comap ψ` if and only if `B` is unramified
over `R` at `q`, stated for any prime `p` of `A` equal to `q.comap ψ`. -/
theorem isUnramifiedAt_iff_of_eq_comap (ψ : A ≃ₐ[R] B) {q : Ideal B} [q.IsPrime]
    {p : Ideal A} [p.IsPrime] (hp : p = q.comap ψ) :
    Algebra.IsUnramifiedAt R p ↔ Algebra.IsUnramifiedAt R q :=
  Algebra.isUnramifiedAt_iff_of_equiv_equiv (RingEquiv.refl R) ψ.toRingEquiv
    (RingHom.ext fun x ↦ (ψ.commutes x).symm) hp

end AlgEquiv
