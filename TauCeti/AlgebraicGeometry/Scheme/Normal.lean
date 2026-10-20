/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import TauCeti.AlgebraicGeometry.Scheme.IntegrallyClosed
public import TauCeti.RingTheory.DiscreteValuationRing.IntegrallyClosed

/-!
# Normal schemes

A scheme is *normal* if every local ring is an integrally closed domain (Stacks, Definition
28.7.1 (033I)). This file defines the class `TauCeti.AlgebraicGeometry.IsNormalScheme` and
proves its basic properties: normality is local, so it can be checked on the rings of sections
over affine opens, whose localizations at primes are the local rings of the scheme (Stacks,
Lemma 28.7.2 (033J)); open subschemes of normal schemes are normal; normal schemes are reduced
(Stacks, Lemma 28.7.3 (033K)); the spectrum of a domain is normal exactly when the domain is
integrally closed; on a normal scheme the domain of sections over an affine open is
integrally closed; and on a locally Noetherian normal scheme the local ring at a point of
coheight one is a discrete valuation ring (Stacks, Lemma 10.119.7 (00PD)).

Following Stacks, Definition 10.37.11 (00GV), a ring `R` is *normal* when every localization of
`R` at a prime is an integrally closed domain; `isNormalScheme_Spec_iff_forall_localization`
says that this holds exactly when `Spec R` is a normal scheme, and the affine statements below
use `IsNormalScheme (Spec R)` for it.

## Main results

* `TauCeti.AlgebraicGeometry.IsNormalScheme`: every local ring is an integrally closed domain.
* `TauCeti.AlgebraicGeometry.isNormalScheme_Spec_iff_forall_localization`: `Spec R` is normal
  iff every localization of `R` at a prime is an integrally closed domain.
* `TauCeti.AlgebraicGeometry.isNormalScheme_iff_forall_affineOpens`: a scheme is normal iff the
  ring of sections over every affine open is normal.
* `TauCeti.AlgebraicGeometry.isNormalScheme_iff_forall_exists_affineOpens`: it suffices that
  every point has an affine open neighbourhood with normal ring of sections.
* `TauCeti.AlgebraicGeometry.isNormalScheme_iff_openCover`: normality is local on an open
  cover.
* `TauCeti.AlgebraicGeometry.IsNormalScheme.of_isOpenImmersion`: the source of an open immersion
  into a normal scheme is normal; open subschemes and the components of open covers of a normal
  scheme are normal (instances).
* `TauCeti.AlgebraicGeometry.IsNormalScheme.isReduced`: normal schemes are reduced.
* `TauCeti.AlgebraicGeometry.isNormalScheme_Spec_iff`: for a domain `R`, `Spec R` is normal iff
  `R` is integrally closed.
* `TauCeti.AlgebraicGeometry.IsNormalScheme.isIntegrallyClosed_of_isAffineOpen`: on a normal
  scheme, a domain of sections over an affine open is integrally closed.
* `TauCeti.AlgebraicGeometry.IsNormalScheme.isDiscreteValuationRing_stalk`: on a locally
  Noetherian normal scheme, the local ring at a point of coheight one is a discrete valuation
  ring, by the ring-level `IsDiscreteValuationRing.of_ringKrullDim_eq_one`.

## References

* [Stacks Project, Definition 28.7.1](https://stacks.math.columbia.edu/tag/033I),
  [Lemma 28.7.2](https://stacks.math.columbia.edu/tag/033J),
  [Lemma 28.7.3](https://stacks.math.columbia.edu/tag/033K) and
  [Lemma 10.119.7](https://stacks.math.columbia.edu/tag/00PD).
* `IsNormalScheme.isDiscreteValuationRing_stalk` is ported from T. Dupuy, T. Tucker and
  Z. Wang, [pcfawd-formalization](https://github.com/tdupu/pcfawd-formalization) at commit
  `9a20b3f351446d64e6015d704198bc71c7002008` (Apache-2.0): it is
  `Pcf.SchemeDivisorPoint.stalk_isDiscreteValuationRing` in
  `lean/Pcf/Bounding/SchemeDynamics.lean`, whose ring-level step (ported as
  `IsDiscreteValuationRing.of_ringKrullDim_eq_one`) is
  `Pcf.isDiscreteValuationRing_localizationAtPrime_of_heightOne` in
  `lean/Pcf/Bounding/Divisors.lean`. The source states it for an integral scheme with its own
  affine-sections predicate `Pcf.IsNormalScheme` (`lean/Pcf/Bounding/SchemeExtraction.lean`);
  here it is stated for the stalkwise class and needs neither integrality nor an affine chart.
-/

public section

open CategoryTheory AlgebraicGeometry Order

namespace TauCeti

namespace AlgebraicGeometry

universe u

/-- A scheme is **normal** if every local ring is a domain and integrally closed.
Stacks, Definition 28.7.1 (033I). -/
@[stacks 033I]
class IsNormalScheme (X : Scheme.{u}) : Prop where
  isDomain_stalk : ∀ x : X, IsDomain (X.presheaf.stalk x)
  isIntegrallyClosed_stalk : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)

attribute [instance] IsNormalScheme.isDomain_stalk IsNormalScheme.isIntegrallyClosed_stalk

variable {X : Scheme.{u}}

/-- A scheme is normal iff each of its local rings is an integrally closed domain; this is the
definition, as a single condition per point. -/
@[simp] theorem isNormalScheme_iff_forall_stalk :
    IsNormalScheme X ↔
      ∀ x : X, IsDomain (X.presheaf.stalk x) ∧ IsIntegrallyClosed (X.presheaf.stalk x) :=
  ⟨fun _ _ ↦ ⟨inferInstance, inferInstance⟩, fun h ↦ ⟨fun x ↦ (h x).1, fun x ↦ (h x).2⟩⟩

/-- The source of an open immersion into a normal scheme is normal. -/
theorem IsNormalScheme.of_isOpenImmersion {Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    [IsNormalScheme Y] : IsNormalScheme X :=
  isNormalScheme_iff_forall_stalk.mpr fun x ↦
    (isDomain_and_isIntegrallyClosed_stalk_iff_of_isOpenImmersion f x).mp
      (isNormalScheme_iff_forall_stalk.mp ‹_› (f x))

/-- Open subschemes of a normal scheme are normal. -/
instance IsNormalScheme.opens [IsNormalScheme X] (U : X.Opens) : IsNormalScheme U :=
  .of_isOpenImmersion U.ι

/-- A scheme is normal as soon as every point lies in the image of an open immersion from a
normal scheme. -/
theorem IsNormalScheme.of_forall_exists_isOpenImmersion
    (h : ∀ x : X, ∃ (Y : Scheme.{u}) (f : Y ⟶ X), IsOpenImmersion f ∧ IsNormalScheme Y ∧
      x ∈ Set.range f) :
    IsNormalScheme X := by
  refine isNormalScheme_iff_forall_stalk.mpr fun x ↦ ?_
  obtain ⟨Y, f, _, _, y, rfl⟩ := h x
  exact (isDomain_and_isIntegrallyClosed_stalk_iff_of_isOpenImmersion f y).mpr
    (isNormalScheme_iff_forall_stalk.mp ‹_› y)

/-- Normality is local on an open cover. Stacks, Lemma 28.7.2 (033J), in the form "normality
is local". -/
@[stacks 033J "normality is local"]
theorem isNormalScheme_iff_openCover (𝒰 : X.OpenCover) :
    IsNormalScheme X ↔ ∀ i, IsNormalScheme (𝒰.X i) :=
  ⟨fun _ i ↦ .of_isOpenImmersion (𝒰.f i), fun h ↦ .of_forall_exists_isOpenImmersion fun x ↦
    ⟨_, 𝒰.f (𝒰.idx x), inferInstance, h _, 𝒰.covers x⟩⟩

/-- The components of an open cover of a normal scheme are normal. -/
instance IsNormalScheme.openCover [IsNormalScheme X] (𝒰 : X.OpenCover) (i : 𝒰.I₀) :
    IsNormalScheme (𝒰.X i) :=
  .of_isOpenImmersion (𝒰.f i)

/-- `Spec R` is normal iff `R` is a normal ring in the sense of Stacks, Definition 10.37.11
(00GV): every localization of `R` at a prime is an integrally closed domain. The local rings of
`Spec R` are these localizations (Mathlib `AlgebraicGeometry.Spec.stalkIso`). -/
theorem isNormalScheme_Spec_iff_forall_localization (R : CommRingCat.{u}) :
    IsNormalScheme (Spec R) ↔ ∀ (p : Ideal R) [p.IsPrime],
      IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p) := by
  refine isNormalScheme_iff_forall_stalk.trans ⟨fun h p _ ↦ ?_, fun h x ↦ ?_⟩
  · let e := (Spec.stalkIso R ⟨p, inferInstance⟩).commRingCatIsoToRingEquiv
    obtain ⟨_, _⟩ := h ⟨p, inferInstance⟩
    exact ⟨e.symm.toMulEquiv.isDomain _, .of_equiv e⟩
  · have : x.asIdeal.IsPrime := x.isPrime
    let e := (Spec.stalkIso R x).commRingCatIsoToRingEquiv.symm
    obtain ⟨_, _⟩ := h x.asIdeal
    exact ⟨e.symm.toMulEquiv.isDomain _, .of_equiv e⟩

/-- A scheme is normal iff the ring of sections over every affine open is normal: `Spec Γ(X, U)`
is normal, which by `isNormalScheme_Spec_iff_forall_localization` says that every localization
of `Γ(X, U)` at a prime is an integrally closed domain. Stacks, Lemma 28.7.2 (033J). -/
@[stacks 033J]
theorem isNormalScheme_iff_forall_affineOpens :
    IsNormalScheme X ↔ ∀ U : X.affineOpens, IsNormalScheme (Spec Γ(X, U)) := by
  refine ⟨fun _ U ↦ ?_, fun h ↦ .of_forall_exists_isOpenImmersion fun x ↦ ?_⟩
  · have := U.2.isOpenImmersion_fromSpec
    exact .of_isOpenImmersion U.2.fromSpec
  · obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
    exact ⟨_, hU.fromSpec, hU.isOpenImmersion_fromSpec, h ⟨U, hU⟩, hU.range_fromSpec.ge hxU⟩

/-- A scheme is normal as soon as every point has an affine open neighbourhood whose ring of
sections is normal. Stacks, Lemma 28.7.2 (033J), the affine open covering form. -/
@[stacks 033J "affine open covering form"]
theorem isNormalScheme_iff_forall_exists_affineOpens :
    IsNormalScheme X ↔
      ∀ x : X, ∃ U : X.affineOpens, x ∈ (U : X.Opens) ∧ IsNormalScheme (Spec Γ(X, U)) := by
  refine ⟨fun h x ↦ ?_, fun h ↦ .of_forall_exists_isOpenImmersion fun x ↦ ?_⟩
  · obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
    exact ⟨⟨U, hU⟩, hxU, isNormalScheme_iff_forall_affineOpens.mp h ⟨U, hU⟩⟩
  · obtain ⟨U, hxU, hU⟩ := h x
    exact ⟨_, U.2.fromSpec, U.2.isOpenImmersion_fromSpec, hU, U.2.range_fromSpec.ge hxU⟩

/-- A normal scheme is reduced: its local rings are domains. Stacks, Lemma 28.7.3 (033K). -/
@[stacks 033K]
instance IsNormalScheme.isReduced (X : Scheme.{u}) [IsNormalScheme X] : IsReduced X :=
  isReduced_of_isReduced_stalk X

/-- The spectrum of a domain `R` is normal exactly when `R` is integrally closed. -/
theorem isNormalScheme_Spec_iff (R : CommRingCat.{u}) [IsDomain R] :
    IsNormalScheme (Spec R) ↔ IsIntegrallyClosed R := by
  rw [isNormalScheme_Spec_iff_forall_localization]
  refine ⟨fun h ↦ .of_localization_maximal fun p _ _ ↦ (h p).2, fun _ p _ ↦ ?_⟩
  exact ⟨IsLocalization.isDomain_localization p.primeCompl_le_nonZeroDivisors,
    isIntegrallyClosed_of_isLocalization _ _ p.primeCompl_le_nonZeroDivisors⟩

/-- The spectrum of an integrally closed domain is normal. -/
instance isNormalScheme_Spec (R : CommRingCat.{u}) [IsDomain R] [IsIntegrallyClosed R] :
    IsNormalScheme (Spec R) :=
  (isNormalScheme_Spec_iff R).mpr ‹_›

/-- On a normal scheme, the domain of sections over an affine open is integrally closed.
For an integral scheme, `IsIntegral.component_integral` supplies the domain instance. -/
theorem IsNormalScheme.isIntegrallyClosed_of_isAffineOpen [IsNormalScheme X]
    {U : X.Opens} [IsDomain Γ(X, U)] (hU : IsAffineOpen U) :
    IsIntegrallyClosed Γ(X, U) :=
  hU.isIntegrallyClosed fun _ _ ↦ inferInstance

/-- On a locally Noetherian normal scheme the local ring at a point of coheight one is a
discrete valuation ring. Stacks, Lemma 10.119.7 (00PD). -/
@[stacks 00PD "the codimension-one stalk"]
theorem IsNormalScheme.isDiscreteValuationRing_stalk (X : Scheme.{u}) [IsLocallyNoetherian X]
    [IsNormalScheme X] (x : X) (hx : coheight x = 1) :
    IsDiscreteValuationRing (X.presheaf.stalk x) := by
  have hdim : ringKrullDim (X.presheaf.stalk x) = 1 := by
    rw [ringKrullDim_stalk_eq_coheight]
    simp [hx]
  exact IsDiscreteValuationRing.of_ringKrullDim_eq_one hdim

end AlgebraicGeometry

end TauCeti
