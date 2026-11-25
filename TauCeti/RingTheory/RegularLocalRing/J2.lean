/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Perfect
public import TauCeti.RingTheory.RegularLocalRing.Locus
import TauCeti.RingTheory.RegularLocalRing.Smooth

/-!
# J-2 rings

A Noetherian ring `R` is *J-2* if every `R`-algebra of finite type has open regular locus (Stacks,
Definition 15.48.1 (3)). The regular locus of a ring need not be open, and J-2 asks for openness
not only for `R` but for all algebras of finite type over it. Together with the G-ring condition
it makes up quasi-excellence, the hypothesis under which the regular and normal loci of schemes of
finite type are open and normalizations are finite.

Being J-2 passes to algebras essentially of finite type, hence to quotients, localizations and
polynomial rings in finitely many variables. A perfect field is J-2: over a perfect field the
regular locus of an algebra essentially of finite type is its smooth locus, which is open for
algebras of finite presentation. Consequently every algebra of finite type over a perfect field,
for instance `ℚ[x, y] ⧸ (y ^ 2 - x ^ 3)`, has open regular locus.

## Main definitions and results

* `TauCeti.Excellence.IsJ2 R`: `R` is Noetherian and every finite type `R`-algebra has open regular
  locus; `TauCeti.Excellence.isJ2_iff` unfolds it.
* `TauCeti.Excellence.IsJ2.isOpen_regularLocus`: a J-2 ring has open regular locus.
* `TauCeti.Excellence.IsJ2.isOpen_regularLocus_of_essFiniteType`: an algebra essentially of finite
  type over a J-2 ring, in any universe, has open regular locus.
* `TauCeti.Excellence.IsJ2.of_essFiniteType`: an algebra essentially of finite type over a J-2
  ring is J-2. Quotients, localizations and polynomial rings in finitely many variables over J-2
  rings are J-2.
* `TauCeti.Excellence.IsJ2.of_perfectField`: a perfect field is J-2.

## Implementation notes

The definition and its transfer API follow `TauCeti.RingTheory.UniversallyCatenary`: the
same-universe quantifier of `TauCeti.Excellence.IsUniversallyCatenary`, its extension to algebras
of finite type and essentially of finite type in any universe, and the surjection, ring
isomorphism, quotient, localization and polynomial ring results.

That a perfect field is J-2 rests on `TauCeti.Excellence.regularLocus_eq_smoothLocus`, whose two
inclusions come from `TauCeti.formallySmooth_of_isRegularLocalRing` and
`TauCeti.IsRegularLocalRing.of_formallySmooth`, and on Mathlib's `Algebra.isOpen_smoothLocus` for
the openness of the smooth locus of a finitely presented algebra.

## References

* The Stacks Project, Section 15.48 (*Japanese rings and J-rings*), Definition 15.48.1.
* The Stacks Project, Section 10.140 (*Smooth algebras over fields*).
-/

public section

universe u v w

namespace TauCeti.Excellence

/-- A commutative ring `R` is *J-2* if it is Noetherian and every `R`-algebra of finite type has
open regular locus. The condition is stated for algebras in the universe of `R`; see
`IsJ2.isOpen_regularLocus_of_finiteType` for algebras in an arbitrary universe.
Stacks, Definition 15.48.1 (3). -/
class IsJ2 (R : Type u) [CommRing R] : Prop where
  /-- A J-2 ring is Noetherian. -/
  isNoetherianRing : IsNoetherianRing R
  /-- Every finite type algebra over a J-2 ring has open regular locus. -/
  forall_isOpen_regularLocus : ∀ (B : Type u) [CommRing B] [Algebra R B], Algebra.FiniteType R B →
    IsOpen (regularLocus B)

attribute [instance] IsJ2.isNoetherianRing

/-- A ring is J-2 if and only if it is Noetherian and every finite type algebra over it, in its
universe, has open regular locus. -/
theorem isJ2_iff {R : Type u} [CommRing R] :
    IsJ2 R ↔ IsNoetherianRing R ∧ ∀ (B : Type u) [CommRing B] [Algebra R B],
      Algebra.FiniteType R B → IsOpen (regularLocus B) :=
  ⟨fun h ↦ ⟨h.isNoetherianRing, h.forall_isOpen_regularLocus⟩, fun ⟨h₁, h₂⟩ ↦ ⟨h₁, h₂⟩⟩

namespace IsJ2

variable {R : Type u} {B : Type v} [CommRing R] [CommRing B] [Algebra R B]

/-- An algebra of finite type over a J-2 ring has open regular locus. The algebra may live in any
universe: it is a quotient of a polynomial ring over `R` in finitely many variables, which lives in
the universe of `R`. -/
theorem isOpen_regularLocus_of_finiteType [IsJ2 R] [Algebra.FiniteType R B] :
    IsOpen (regularLocus B) := by
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.1 ‹Algebra.FiniteType R B›
  let Q := MvPolynomial (Fin n) R ⧸ RingHom.ker f
  have hQ := forall_isOpen_regularLocus (R := R) Q inferInstance
  rw [← regularLocus_ringEquiv (Ideal.quotientKerAlgEquivOfSurjective hf).toRingEquiv]
  exact hQ.preimage (PrimeSpectrum.continuous_comap _)

/-- A J-2 ring has open regular locus. -/
theorem isOpen_regularLocus [IsJ2 R] : IsOpen (regularLocus R) :=
  isOpen_regularLocus_of_finiteType (R := R)

/-- An algebra essentially of finite type over a J-2 ring has open regular locus: it is a
localization of an algebra of finite type, and its regular locus is the preimage of that of the
algebra of finite type. -/
theorem isOpen_regularLocus_of_essFiniteType [IsJ2 R] [Algebra.EssFiniteType R B] :
    IsOpen (regularLocus B) := by
  have := isOpen_regularLocus_of_finiteType (R := R) (B := Algebra.EssFiniteType.subalgebra R B)
  rw [← (Algebra.EssFiniteType.submonoid R B).preimage_comap_regularLocus]
  exact this.preimage (PrimeSpectrum.continuous_comap _)

/-- An algebra essentially of finite type over a J-2 ring is J-2: it is Noetherian, and an algebra
of finite type over it is essentially of finite type over `R`. -/
theorem of_essFiniteType [IsJ2 R] [Algebra.EssFiniteType R B] : IsJ2 B where
  isNoetherianRing := Algebra.EssFiniteType.isNoetherianRing R B
  forall_isOpen_regularLocus C _ _ _ := by
    let : Algebra R C := ((algebraMap B C).comp (algebraMap R B)).toAlgebra
    have : IsScalarTower R B C := .of_algebraMap_eq fun _ ↦ rfl
    have := Algebra.EssFiniteType.comp R B C
    exact isOpen_regularLocus_of_essFiniteType (R := R)

/-- The zero ring is J-2: every algebra over it is the zero ring, whose regular locus is empty. -/
theorem of_subsingleton [Subsingleton R] : IsJ2 R where
  isNoetherianRing := inferInstance
  forall_isOpen_regularLocus B _ _ _ := by
    have : Subsingleton B := (algebraMap R B).codomain_trivial
    rw [regularLocus_eq_empty_of_subsingleton]
    exact isOpen_empty

end IsJ2

end TauCeti.Excellence

open TauCeti.Excellence

namespace RingHom

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

/-- A ring receiving a surjection from a J-2 ring is J-2. -/
theorem isJ2_of_surjective [IsJ2 R] (f : R →+* S) (hf : Function.Surjective f) : IsJ2 S :=
  letI := f.toAlgebra
  have : Algebra.EssFiniteType R S := .of_surjective (Algebra.ofId R S) hf
  IsJ2.of_essFiniteType (R := R)

end RingHom

namespace RingEquiv

/-- Being J-2 is invariant under ring isomorphisms. -/
theorem isJ2 {R : Type u} {S : Type v} [CommRing R] [CommRing S] [IsJ2 R] (e : R ≃+* S) :
    IsJ2 S :=
  e.toRingHom.isJ2_of_surjective e.surjective

end RingEquiv

namespace Ideal

/-- A quotient of a J-2 ring is J-2. -/
instance isJ2_quotient {R : Type u} [CommRing R] [IsJ2 R] (I : Ideal R) : IsJ2 (R ⧸ I) :=
  IsJ2.of_essFiniteType (R := R)

end Ideal

namespace Submonoid

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

/-- A localization of a J-2 ring is J-2. -/
theorem isJ2_of_isLocalization [IsJ2 R] (M : Submonoid R) [IsLocalization M S] : IsJ2 S :=
  have : Algebra.EssFiniteType R S := .of_isLocalization S M
  IsJ2.of_essFiniteType (R := R)

/-- A localization of a J-2 ring is J-2. -/
instance isJ2_localization [IsJ2 R] (M : Submonoid R) : IsJ2 (Localization M) :=
  M.isJ2_of_isLocalization

end Submonoid

namespace TauCeti.Excellence

/-- A polynomial ring in finitely many variables over a J-2 ring is J-2. -/
instance IsJ2.mvPolynomial {σ : Type v} {R : Type u} [Finite σ] [CommRing R] [IsJ2 R] :
    IsJ2 (MvPolynomial σ R) :=
  IsJ2.of_essFiniteType (R := R)

/-- A polynomial ring in one variable over a J-2 ring is J-2. -/
instance IsJ2.polynomial {R : Type u} [CommRing R] [IsJ2 R] : IsJ2 (Polynomial R) :=
  IsJ2.of_essFiniteType (R := R)

/-- **A perfect field is J-2**: the regular locus of an algebra of finite type over it is its smooth
locus (`TauCeti.Excellence.regularLocus_eq_smoothLocus`), which is open since the algebra is
finitely presented (`Algebra.isOpen_smoothLocus`). -/
instance IsJ2.of_perfectField (k : Type u) [Field k] [PerfectField k] : IsJ2 k where
  isNoetherianRing := inferInstance
  forall_isOpen_regularLocus B _ _ hB := by
    have : Algebra.FinitePresentation k B := Algebra.FinitePresentation.of_finiteType.mp hB
    rw [regularLocus_eq_smoothLocus k]
    exact Algebra.isOpen_smoothLocus

/-! ### Checks -/

/-- The rationals are J-2. -/
example : IsJ2 ℚ := inferInstance

/-- Finite fields are J-2. -/
example (k : Type u) [Field k] [Finite k] : IsJ2 k := inferInstance

/-- A polynomial ring in finitely many variables over a perfect field is J-2. -/
example (k : Type u) [Field k] [PerfectField k] (n : ℕ) : IsJ2 (MvPolynomial (Fin n) k) :=
  inferInstance

/-- The cuspidal cubic `y ^ 2 = x ^ 3` over a perfect field has open regular locus. -/
example (k : Type u) [Field k] [PerfectField k] :
    IsOpen (regularLocus (MvPolynomial (Fin 2) k ⧸
      Ideal.span {(MvPolynomial.X 1 ^ 2 - MvPolynomial.X 0 ^ 3 : MvPolynomial (Fin 2) k)})) :=
  IsJ2.isOpen_regularLocus_of_finiteType (R := k)

/-- The zero ring is J-2. -/
example : IsJ2 PUnit := IsJ2.of_subsingleton

end TauCeti.Excellence
