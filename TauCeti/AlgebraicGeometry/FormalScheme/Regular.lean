/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.FormalScheme.Basic
public import TauCeti.AlgebraicGeometry.Scheme.CohenMacaulay
public import TauCeti.AlgebraicGeometry.Scheme.Regular.Scheme
public import TauCeti.RingTheory.CohenMacaulay.Ring

import TauCeti.AlgebraicGeometry.FormalScheme.Spf.Stalk
import TauCeti.RingTheory.RegularLocalRing.CohenMacaulay
import TauCeti.RingTheory.RegularLocalRing.Maximal

/-!
# Regular and Cohen–Macaulay formal schemes

A formal scheme is *regular* (`TauCeti.FormalScheme.IsRegular`), respectively *Cohen–Macaulay*
(`TauCeti.FormalScheme.IsCohenMacaulay`), when all of its local rings `𝒪_{X,x}` are regular local
rings, respectively noetherian Cohen–Macaulay local rings. They are the hypotheses under which
codimensions of closed formal subschemes are computed by heights of ideals, and under which
Tor sheaves of coherent modules vanish in high degrees. As for the dimension, the conditions
concern the local rings, not the underlying space: the formal spectrum of `ℤ_p⟦t⟧` is a single
point, and it is regular because `ℤ_p⟦t⟧` is a regular local ring of dimension `2`.

A regular formal scheme is Cohen–Macaulay, and both conditions pass to open formal subschemes. For
an ordinary locally noetherian scheme, regarded as a formal scheme, they are the usual regularity
and Cohen–Macaulay conditions. For a noetherian adic ring `A`, the local ring of `Spf A` at an
open prime `𝔭` shares regularity and the Cohen–Macaulay property with `A_𝔭`
(`TauCeti.FormalScheme.Spf.isRegularLocalRing_stalk_iff`,
`TauCeti.FormalScheme.Spf.isCohenMacaulay_stalk_iff`). Every maximal ideal of `A` is open, and
both properties of a noetherian ring may be tested at its maximal ideals, so `Spf A` is regular
exactly when `A` is a regular ring, and Cohen–Macaulay exactly when `A` is a Cohen–Macaulay ring.
In particular these conditions on `Spf A` also control the localizations of `A` at the primes
which are not open, although those primes are not points of `Spf A`.

## Main definitions

* `TauCeti.FormalScheme.IsRegular`: all local rings are regular local rings.
* `TauCeti.FormalScheme.IsCohenMacaulay`: all local rings are Cohen–Macaulay rings.

## Main results

* `TauCeti.FormalScheme.IsRegular.isCohenMacaulay`: regular formal schemes are Cohen–Macaulay.
* `TauCeti.FormalScheme.IsRegular.of_isOpenImmersion`,
  `TauCeti.FormalScheme.IsCohenMacaulay.of_isOpenImmersion`: both conditions pass to the source of
  an open immersion, in particular to open formal subschemes.
* `TauCeti.FormalScheme.isRegular_toFormalScheme_iff`,
  `TauCeti.FormalScheme.isCohenMacaulay_toFormalScheme_iff`: for a locally noetherian scheme, they
  are the conditions on the scheme.
* `TauCeti.FormalScheme.isRegular_ofSpf_iff`: `Spf A` is regular exactly when `A` is regular.
* `TauCeti.FormalScheme.isCohenMacaulay_ofSpf_iff`: `Spf A` is Cohen–Macaulay exactly when `A`
  is Cohen–Macaulay.

## References

* W. Zhang, *Weil representation and arithmetic fundamental lemma*, Ann. of Math. 193 (2021),
  Appendix B.1.
* [Stacks Project, Lemma 10.110.6 (Tag 0AFS)](https://stacks.math.columbia.edu/tag/0AFS), for
  testing regularity at maximal ideals.
-/

public section

universe u

open CategoryTheory AlgebraicGeometry

namespace TauCeti.FormalScheme

/-- A formal scheme is **regular** if each of its local rings `𝒪_{X,x}` is a regular local ring.
A regular local ring is in particular noetherian. -/
class IsRegular (X : FormalScheme.{u}) : Prop where
  isRegularLocalRing_stalk : ∀ x : X, IsRegularLocalRing (X.presheaf.stalk x)

attribute [instance] IsRegular.isRegularLocalRing_stalk

/-- A formal scheme is **Cohen–Macaulay** if each of its local rings `𝒪_{X,x}` is a
Cohen–Macaulay ring. Such a ring is in particular noetherian. -/
class IsCohenMacaulay (X : FormalScheme.{u}) : Prop where
  isCohenMacaulay_stalk : ∀ x : X, Ring.IsCohenMacaulay (X.presheaf.stalk x)

attribute [instance] IsCohenMacaulay.isCohenMacaulay_stalk

variable {X Y : FormalScheme.{u}}

/-- A formal scheme is Cohen–Macaulay exactly when its local rings are noetherian and
Cohen–Macaulay over themselves. -/
theorem isCohenMacaulay_iff_forall_stalk :
    X.IsCohenMacaulay ↔ ∀ x : X, IsNoetherianRing (X.presheaf.stalk x) ∧
      Module.IsCohenMacaulay (X.presheaf.stalk x) (X.presheaf.stalk x) :=
  ⟨fun _ _ ↦ ⟨inferInstance, Ring.isCohenMacaulay_iff_of_isLocalRing.mp inferInstance⟩,
    fun h ↦ ⟨fun x ↦ have := (h x).1; Ring.isCohenMacaulay_iff_of_isLocalRing.mpr (h x).2⟩⟩

/-- A regular formal scheme is Cohen–Macaulay, since regular local rings are. -/
instance (priority := 100) IsRegular.isCohenMacaulay [X.IsRegular] : X.IsCohenMacaulay :=
  isCohenMacaulay_iff_forall_stalk.mpr fun _ ↦ ⟨inferInstance, IsRegularLocalRing.isCohenMacaulay⟩

/-! ### Open immersions -/

/-- The source of an open immersion into a regular formal scheme is regular. -/
theorem IsRegular.of_isOpenImmersion (f : X ⟶ Y)
    [LocallyRingedSpace.IsOpenImmersion (forgetToLocallyRingedSpace.map f)] [Y.IsRegular] :
    X.IsRegular :=
  ⟨fun x ↦ .of_ringEquiv (stalkRingEquivOfIsOpenImmersion f x)⟩

/-- The source of an open immersion into a Cohen–Macaulay formal scheme is Cohen–Macaulay. -/
theorem IsCohenMacaulay.of_isOpenImmersion (f : X ⟶ Y)
    [LocallyRingedSpace.IsOpenImmersion (forgetToLocallyRingedSpace.map f)] [Y.IsCohenMacaulay] :
    X.IsCohenMacaulay :=
  ⟨fun x ↦ (stalkRingEquivOfIsOpenImmersion f x).isCohenMacaulay⟩

/-- Open formal subschemes of a regular formal scheme are regular. -/
instance IsRegular.restrict [X.IsRegular] (U : TopologicalSpace.Opens X) :
    (X.restrict U).IsRegular :=
  .of_isOpenImmersion (X.ofRestrict U)

/-- Open formal subschemes of a Cohen–Macaulay formal scheme are Cohen–Macaulay. -/
instance IsCohenMacaulay.restrict [X.IsCohenMacaulay] (U : TopologicalSpace.Opens X) :
    (X.restrict U).IsCohenMacaulay :=
  .of_isOpenImmersion (X.ofRestrict U)

/-! ### Ordinary schemes -/

section Scheme

variable (S : Scheme.{u})

/-- A locally noetherian scheme is regular exactly when it is regular as a formal scheme: both
conditions ask that all local rings be regular. -/
theorem isRegular_toFormalScheme_iff [IsLocallyNoetherian S] :
    S.toFormalScheme.IsRegular ↔ TauCeti.AlgebraicGeometry.IsRegular S :=
  -- the local rings of `S.toFormalScheme` are those of `S`, by
  -- `Scheme.toFormalScheme_toLocallyRingedSpace`
  ⟨fun h ↦ ⟨h.isRegularLocalRing_stalk⟩, fun h ↦ ⟨h.isRegularLocalRing_stalk⟩⟩

instance [TauCeti.AlgebraicGeometry.IsRegular S] : S.toFormalScheme.IsRegular :=
  (isRegular_toFormalScheme_iff S).mpr inferInstance

/-- A locally noetherian scheme is Cohen–Macaulay exactly when it is Cohen–Macaulay as a formal
scheme. -/
theorem isCohenMacaulay_toFormalScheme_iff [IsLocallyNoetherian S] :
    S.toFormalScheme.IsCohenMacaulay ↔ S.IsCohenMacaulay := by
  rw [isCohenMacaulay_iff_forall_stalk, Scheme.isCohenMacaulay_iff_forall_stalk,
    and_iff_right ‹_›]
  -- the local rings of `S.toFormalScheme` are those of `S`, by
  -- `Scheme.toFormalScheme_toLocallyRingedSpace`
  exact forall_congr' fun x : S ↦
    and_iff_right (inferInstance : IsNoetherianRing (S.presheaf.stalk x))

instance [S.IsCohenMacaulay] : S.toFormalScheme.IsCohenMacaulay :=
  (isCohenMacaulay_toFormalScheme_iff S).mpr inferInstance

end Scheme

/-! ### Formal spectra -/

section Spf

variable (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsAdicRing A]

/-- For a noetherian adic ring `A`, the formal spectrum `Spf A` is regular exactly when `A` is a
regular ring. Regularity of `A` may be tested at maximal ideals, which are points of `Spf A`,
where the local ring of `Spf A` is regular exactly when the localization of `A` is. -/
theorem isRegular_ofSpf_iff [IsNoetherianRing A] : (ofSpf A).IsRegular ↔ IsRegularRing A := by
  -- the local rings of `ofSpf A` are those of `Spf A`, by `ofSpf_toLocallyRingedSpace`
  refine ⟨fun h ↦ (isRegularRing_iff_localization_maximal A).mpr fun m _ ↦ ?_,
    fun _ ↦ ⟨fun p ↦ (Spf.isRegularLocalRing_stalk_iff p).mpr inferInstance⟩⟩
  exact (Spf.isRegularLocalRing_stalk_iff (Spf.pointOfIsMaximal m)).mp
    (h.isRegularLocalRing_stalk (Spf.pointOfIsMaximal m))

instance [IsRegularRing A] : (ofSpf A).IsRegular :=
  (isRegular_ofSpf_iff A).mpr inferInstance

/-- For a noetherian adic ring `A`, the formal spectrum `Spf A` is Cohen–Macaulay exactly when
`A` is a Cohen–Macaulay ring, that is, when `A_𝔪` is Cohen–Macaulay for every maximal ideal `𝔪`
(`TauCeti.Ring.isCohenMacaulay_iff_forall_isMaximal`). -/
theorem isCohenMacaulay_ofSpf_iff [IsNoetherianRing A] :
    (ofSpf A).IsCohenMacaulay ↔ Ring.IsCohenMacaulay A := by
  -- the local rings of `ofSpf A` are those of `Spf A`, by `ofSpf_toLocallyRingedSpace`
  refine isCohenMacaulay_iff_forall_stalk.trans ⟨fun h ↦
    Ring.isCohenMacaulay_iff_forall_isMaximal.mpr fun m _ ↦ ?_, fun h p ↦
    ⟨Spf.isNoetherianRing_stalk p, (Spf.isCohenMacaulay_stalk_iff p).mpr
      (h.isCohenMacaulay_localization _)⟩⟩
  exact (Spf.isCohenMacaulay_stalk_iff (Spf.pointOfIsMaximal m)).mp (h (Spf.pointOfIsMaximal m)).2

instance [Ring.IsCohenMacaulay A] : (ofSpf A).IsCohenMacaulay :=
  (isCohenMacaulay_ofSpf_iff A).mpr inferInstance

end Spf

end TauCeti.FormalScheme
