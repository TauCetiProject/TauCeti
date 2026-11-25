/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.RingTheory.LocalProperties.IntegrallyClosed

/-!
# Integrally closed sections of affine opens

If the ring of sections over an affine open `V` is a domain, it is integrally closed exactly
when the local rings at the points of `V` are: these local rings are its localizations at primes,
and integral closedness of a domain can be checked at its maximal ideals.

## Main results

* `AlgebraicGeometry.IsAffineOpen.isDomain_and_isIntegrallyClosed_stalk_iff`: normality of a
  stalk is equivalent to normality of the corresponding localization of affine sections.
* `AlgebraicGeometry.IsAffineOpen.isIntegrallyClosed_iff_forall_stalk`: a domain of sections
  over an affine open is integrally closed iff its local rings are.
* `AlgebraicGeometry.Scheme.Hom.isDomain_stalk_of_isOpenImmersion` and
  `AlgebraicGeometry.Scheme.Hom.isDomain_and_isIntegrallyClosed_stalk_iff_of_isOpenImmersion`:
  open immersions preserve the domain and integral-closure conditions on stalks.
-/

public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- An open immersion identifies the local rings at corresponding points, preserving the
conjunction of domain and integral-closure properties. -/
theorem Scheme.Hom.isDomain_and_isIntegrallyClosed_stalk_iff_of_isOpenImmersion
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] (x : X) :
    IsDomain (Y.presheaf.stalk (f x)) ∧ IsIntegrallyClosed (Y.presheaf.stalk (f x)) ↔
      IsDomain (X.presheaf.stalk x) ∧ IsIntegrallyClosed (X.presheaf.stalk x) :=
  let e := (asIso (f.stalkMap x)).commRingCatIsoToRingEquiv
  and_congr e.toMulEquiv.isDomain_iff ⟨fun _ ↦ .of_equiv e, fun _ ↦ .of_equiv e.symm⟩

/-- The local ring of the source of an open immersion at a point is a domain when the local ring
of the target at its image is. -/
theorem Scheme.Hom.isDomain_stalk_of_isOpenImmersion {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] (u : U) [IsDomain (X.presheaf.stalk (j u))] :
    IsDomain (U.presheaf.stalk u) :=
  (asIso (j.stalkMap u)).commRingCatIsoToRingEquiv.symm.toMulEquiv.isDomain _

variable {T : Scheme.{u}}

/-- The stalk at a point of an affine open is an integrally closed domain exactly when the
localization of its ring of sections at the corresponding prime is an integrally closed domain. -/
theorem IsAffineOpen.isDomain_and_isIntegrallyClosed_stalk_iff {V : T.Opens}
    (hV : IsAffineOpen V) (x : V) :
    (IsDomain (T.presheaf.stalk x.val) ∧ IsIntegrallyClosed (T.presheaf.stalk x.val)) ↔
      (IsDomain (Localization.AtPrime (hV.primeIdealOf x).asIdeal) ∧
        IsIntegrallyClosed (Localization.AtPrime (hV.primeIdealOf x).asIdeal)) := by
  let := T.presheaf.algebra_section_stalk x
  have := hV.isLocalization_stalk x
  let e := IsLocalization.algEquiv (hV.primeIdealOf x).asIdeal.primeCompl
    (T.presheaf.stalk x.val) (Localization.AtPrime (hV.primeIdealOf x).asIdeal)
  exact and_congr e.toMulEquiv.isDomain_iff
    ⟨fun _ ↦ .of_equiv e.toRingEquiv, fun _ ↦ .of_equiv e.symm.toRingEquiv⟩

/-- The domain of sections over an affine open `V` is integrally closed exactly when the local
rings at the points of `V` are: these local rings are its localizations at primes, and its
localizations at maximal ideals are among them. -/
theorem IsAffineOpen.isIntegrallyClosed_iff_forall_stalk {V : T.Opens} [IsDomain Γ(T, V)]
    (hV : IsAffineOpen V) :
    IsIntegrallyClosed Γ(T, V) ↔ ∀ x ∈ V, IsIntegrallyClosed (T.presheaf.stalk x) := by
  refine ⟨fun _ x hx ↦ ?_, fun hT ↦ IsIntegrallyClosed.of_localization_maximal fun P _ _ ↦ ?_⟩
  · let := T.presheaf.algebra_section_stalk ⟨x, hx⟩
    have := hV.isLocalization_stalk ⟨x, hx⟩
    exact isIntegrallyClosed_of_isLocalization _ _
      (hV.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl_le_nonZeroDivisors
  let y : PrimeSpectrum Γ(T, V) := ⟨P, inferInstance⟩
  have hy : hV.fromSpec y ∈ V := hV.range_fromSpec.subset (Set.mem_range_self y)
  let := TopCat.Presheaf.algebra_section_stalk T.presheaf ⟨hV.fromSpec y, hy⟩
  have : IsLocalization P.primeCompl (T.presheaf.stalk (hV.fromSpec y)) :=
    hV.isLocalization_stalk' y hy
  exact (hT (hV.fromSpec y) hy).of_equiv (IsLocalization.algEquiv P.primeCompl
    (T.presheaf.stalk (hV.fromSpec y)) (Localization.AtPrime P)).toRingEquiv

end AlgebraicGeometry
