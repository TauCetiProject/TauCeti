/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.EssentialFiniteness
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.MvPolynomial.Basic
public import TauCeti.RingTheory.Catenary

import Mathlib.RingTheory.Localization.Submodule
import Mathlib.RingTheory.Polynomial.Basic

/-!
# Universally catenary rings

A commutative ring `R` is *universally catenary* if it is Noetherian and every `R`-algebra of
finite type is catenary (Stacks, Definition 10.105.3 (00NL)). This is the dimension-theoretic
half of excellence: an excellent ring is a quasi-excellent universally catenary ring.

The defining condition quantifies over algebras in the universe of `R`; it then holds for algebras
in every universe, and even for algebras essentially of finite type, since such an algebra is a
localization of a quotient of a polynomial ring over `R` in finitely many variables.

## Main definitions and results

* `TauCeti.Excellence.IsUniversallyCatenary R`: the ring `R` is universally catenary.
* `TauCeti.Excellence.IsUniversallyCatenary.isCatenary_of_essFiniteType`: an algebra essentially
  of finite type over a universally catenary ring, in any universe, is catenary; in particular a
  universally catenary ring is catenary.
* `TauCeti.Excellence.isUniversallyCatenary_iff_mvPolynomial`: a ring is universally catenary if
  and only if it is Noetherian and every polynomial ring over it in finitely many variables is
  catenary.
* `TauCeti.Excellence.IsUniversallyCatenary.of_essFiniteType`: an algebra essentially of finite
  type over a universally catenary ring is universally catenary; in particular so are quotients,
  localizations and polynomial rings in finitely many variables (Stacks, Lemma 10.105.4 (00NJ)
  and Lemma 10.105.7 (00NK)).
* `TauCeti.Excellence.isUniversallyCatenary_iff_forall_isMaximal`: a Noetherian ring is
  universally catenary if and only if its localizations at all maximal ideals are; equivalently,
  its localizations at all prime ideals are
  (`TauCeti.Excellence.isUniversallyCatenary_iff_forall_isPrime`).
-/

public section

universe u v

namespace TauCeti.Excellence

/-- A commutative ring `R` is *universally catenary* if it is Noetherian and every `R`-algebra of
finite type is catenary. The condition is stated for algebras in the universe of `R`; see
`IsUniversallyCatenary.isCatenary_of_finiteType` for algebras in an arbitrary universe.
Stacks, Definition 10.105.3 (00NL). -/
class IsUniversallyCatenary (R : Type u) [CommRing R] : Prop where
  /-- A universally catenary ring is Noetherian. -/
  isNoetherianRing : IsNoetherianRing R
  /-- Every finite type algebra over a universally catenary ring is catenary. -/
  forall_isCatenary : ∀ (B : Type u) [CommRing B] [Algebra R B], Algebra.FiniteType R B →
    IsCatenary B

attribute [instance] IsUniversallyCatenary.isNoetherianRing

namespace IsUniversallyCatenary

variable {R : Type u} {B : Type v} [CommRing R] [CommRing B] [Algebra R B]

/-- An algebra of finite type over a universally catenary ring is catenary. The algebra may live in
any universe: it is a quotient of a polynomial ring over `R` in finitely many variables, which lives
in the universe of `R`. -/
theorem isCatenary_of_finiteType [IsUniversallyCatenary R] [Algebra.FiniteType R B] :
    IsCatenary B := by
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.1 ‹Algebra.FiniteType R B›
  have := forall_isCatenary (R := R) (MvPolynomial (Fin n) R) inferInstance
  exact f.toRingHom.isCatenary_of_surjective hf

/-- An algebra essentially of finite type over a universally catenary ring is catenary: it is a
localization of an algebra of finite type. -/
theorem isCatenary_of_essFiniteType [IsUniversallyCatenary R] [Algebra.EssFiniteType R B] :
    IsCatenary B :=
  have : IsCatenary (Algebra.EssFiniteType.subalgebra R B) := isCatenary_of_finiteType (R := R)
  (Algebra.EssFiniteType.submonoid R B).isCatenary_of_isLocalization

/-- A universally catenary ring is catenary. -/
instance isCatenary [IsUniversallyCatenary R] : IsCatenary R :=
  isCatenary_of_finiteType (R := R)

/-- An algebra essentially of finite type over a universally catenary ring is universally
catenary: it is Noetherian, and an algebra of finite type over it is essentially of finite type
over `R`. -/
theorem of_essFiniteType [IsUniversallyCatenary R] [Algebra.EssFiniteType R B] :
    IsUniversallyCatenary B where
  isNoetherianRing := Algebra.EssFiniteType.isNoetherianRing R B
  forall_isCatenary C _ _ _ := by
    let : Algebra R C := ((algebraMap B C).comp (algebraMap R B)).toAlgebra
    have : IsScalarTower R B C := .of_algebraMap_eq fun _ => rfl
    have := Algebra.EssFiniteType.comp R B C
    exact isCatenary_of_essFiniteType (R := R)

end IsUniversallyCatenary

/-- A ring is universally catenary if and only if it is Noetherian and every polynomial ring over
it in finitely many variables is catenary. -/
theorem isUniversallyCatenary_iff_mvPolynomial {R : Type u} [CommRing R] :
    IsUniversallyCatenary R ↔
      IsNoetherianRing R ∧ ∀ n : ℕ, IsCatenary (MvPolynomial (Fin n) R) := by
  refine ⟨fun _ => ⟨inferInstance, fun n => IsUniversallyCatenary.isCatenary_of_finiteType
    (R := R)⟩, fun ⟨hR, h⟩ => ⟨hR, fun B _ _ hB => ?_⟩⟩
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.1 hB
  have := h n
  exact f.toRingHom.isCatenary_of_surjective hf

end TauCeti.Excellence

open TauCeti.Excellence

namespace RingHom

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

/-- A ring receiving a surjection from a universally catenary ring is universally catenary.
Stacks, Lemma 10.105.7 (00NK). -/
theorem isUniversallyCatenary_of_surjective [IsUniversallyCatenary R] (f : R →+* S)
    (hf : Function.Surjective f) : IsUniversallyCatenary S :=
  letI := f.toAlgebra
  have : Algebra.EssFiniteType R S :=
    .of_surjective (Algebra.ofId R S) hf
  IsUniversallyCatenary.of_essFiniteType (R := R)

end RingHom

namespace RingEquiv

/-- Universal catenarity is invariant under ring isomorphism. -/
theorem isUniversallyCatenary {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    [IsUniversallyCatenary R] (e : R ≃+* S) : IsUniversallyCatenary S :=
  e.toRingHom.isUniversallyCatenary_of_surjective e.surjective

end RingEquiv

namespace Ideal

/-- A quotient of a universally catenary ring is universally catenary.
Stacks, Lemma 10.105.7 (00NK). -/
instance isUniversallyCatenary_quotient {R : Type u} [CommRing R] [IsUniversallyCatenary R]
    (I : Ideal R) : IsUniversallyCatenary (R ⧸ I) :=
  IsUniversallyCatenary.of_essFiniteType (R := R)

end Ideal

namespace Submonoid

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

/-- A localization of a universally catenary ring is universally catenary.
Stacks, Lemma 10.105.4 (00NJ). -/
theorem isUniversallyCatenary_of_isLocalization [IsUniversallyCatenary R] (M : Submonoid R)
    [IsLocalization M S] : IsUniversallyCatenary S :=
  have : Algebra.EssFiniteType R S := .of_isLocalization S M
  IsUniversallyCatenary.of_essFiniteType (R := R)

/-- A localization of a universally catenary ring is universally catenary.
Stacks, Lemma 10.105.4 (00NJ). -/
instance isUniversallyCatenary_localization [IsUniversallyCatenary R] (M : Submonoid R) :
    IsUniversallyCatenary (Localization M) :=
  M.isUniversallyCatenary_of_isLocalization

end Submonoid

namespace MvPolynomial

/-- A polynomial ring in finitely many variables over a universally catenary ring is universally
catenary. -/
instance isUniversallyCatenary {σ : Type v} {R : Type u} [Finite σ] [CommRing R]
    [IsUniversallyCatenary R] : IsUniversallyCatenary (MvPolynomial σ R) :=
  IsUniversallyCatenary.of_essFiniteType (R := R)

end MvPolynomial

namespace Polynomial

/-- A polynomial ring in one variable over a universally catenary ring is universally catenary. -/
instance isUniversallyCatenary {R : Type u} [CommRing R] [IsUniversallyCatenary R] :
    IsUniversallyCatenary R[X] :=
  IsUniversallyCatenary.of_essFiniteType (R := R)

end Polynomial

namespace TauCeti.Excellence

/-- A Noetherian ring is universally catenary if and only if its localizations at all maximal
ideals are universally catenary. -/
theorem isUniversallyCatenary_iff_forall_isMaximal {R : Type u} [CommRing R]
    [IsNoetherianRing R] :
    IsUniversallyCatenary R ↔
      ∀ (m : Ideal R) [m.IsMaximal], IsUniversallyCatenary (Localization.AtPrime m) := by
  refine ⟨fun _ m _ => inferInstance, fun h => ⟨inferInstance, fun B _ _ _ => ?_⟩⟩
  -- For a maximal ideal `n` of a finite type `R`-algebra `B`, the prime `n ∩ R` lies in a maximal
  -- ideal `m` of `R`, and `B_n` is essentially of finite type over `R_m`.
  refine isCatenary_iff_forall_isMaximal.2 fun n _ => ?_
  obtain ⟨m, hm, hnm⟩ :=
    (n.comap (algebraMap R B)).exists_le_maximal (Ideal.IsPrime.comap _).ne_top
  -- Elements of `R` outside `m` lie outside `n ∩ R`, so they become units in `B_n`.
  let : Algebra (Localization.AtPrime m) (Localization.AtPrime n) :=
    (IsLocalization.lift (M := m.primeCompl) (g := algebraMap R (Localization.AtPrime n))
      fun y => by
        rw [IsScalarTower.algebraMap_apply R B]
        exact IsLocalization.map_units (Localization.AtPrime n)
          (⟨algebraMap R B y, fun hy => y.2 (hnm hy)⟩ : n.primeCompl)).toAlgebra
  have : IsScalarTower R (Localization.AtPrime m) (Localization.AtPrime n) :=
    .of_algebraMap_eq fun x => (IsLocalization.lift_eq _ x).symm
  have : Algebra.EssFiniteType R (Localization.AtPrime n) := .comp R B _
  have : Algebra.EssFiniteType (Localization.AtPrime m) (Localization.AtPrime n) :=
    .of_comp R _ _
  exact IsUniversallyCatenary.isCatenary_of_essFiniteType (R := Localization.AtPrime m)

/-- A Noetherian ring is universally catenary if and only if its localizations at all prime
ideals are universally catenary. -/
theorem isUniversallyCatenary_iff_forall_isPrime {R : Type u} [CommRing R] [IsNoetherianRing R] :
    IsUniversallyCatenary R ↔
      ∀ (q : Ideal R) [q.IsPrime], IsUniversallyCatenary (Localization.AtPrime q) :=
  ⟨fun _ _ _ => inferInstance,
    fun h => isUniversallyCatenary_iff_forall_isMaximal.2 fun m _ => h m⟩

end TauCeti.Excellence
