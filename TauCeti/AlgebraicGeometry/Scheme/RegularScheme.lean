/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Scheme.Normal
public import TauCeti.AlgebraicGeometry.Scheme.RegularLocalRing
public import TauCeti.RingTheory.RegularLocalRing.Normal

/-!
# Regular schemes

A scheme is regular if it is locally Noetherian and every local ring is regular. We use the
stalkwise characterization in Stacks, Lemma 28.9.2 (02IT). The spectrum of a ring is regular
exactly when the ring is regular, and regular schemes are normal. Normality follows from the
affine criterion and the ring-level theorem
`TauCeti.IsRegularRing.isIntegrallyClosed`.

## Main declarations

* `TauCeti.AlgebraicGeometry.IsRegular`: regularity of a scheme.
* `TauCeti.AlgebraicGeometry.isRegular_iff_forall_stalk`: the stalkwise characterization.
* `TauCeti.AlgebraicGeometry.isRegular_Spec_iff`: regularity of an affine scheme.
* `TauCeti.AlgebraicGeometry.IsNormalScheme.of_isRegular`: regular schemes are normal.

## References

* [Stacks Project, Lemma 28.9.2](https://stacks.math.columbia.edu/tag/02IT).
* [Stacks Project, Lemma 28.9.3](https://stacks.math.columbia.edu/tag/02IU).
* [Stacks Project, Lemma 28.9.4](https://stacks.math.columbia.edu/tag/0569).
-/

public section

open CategoryTheory AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry

universe u

/-- A regular scheme is locally Noetherian and has regular local rings.
This is condition (2) in Stacks, Lemma 28.9.2 (02IT). -/
@[stacks 02IT "condition (2)"]
class IsRegular (X : Scheme.{u}) : Prop extends IsLocallyNoetherian X where
  isRegularLocalRing_stalk : ∀ x : X, IsRegularLocalRing (X.presheaf.stalk x)

attribute [instance] IsRegular.isRegularLocalRing_stalk

variable {X : Scheme.{u}}

/-- A scheme is regular iff it is locally Noetherian and every stalk is a regular local ring. -/
@[simp] theorem isRegular_iff_forall_stalk :
    IsRegular X ↔ IsLocallyNoetherian X ∧
      ∀ x : X, IsRegularLocalRing (X.presheaf.stalk x) :=
  ⟨fun _ ↦ ⟨inferInstance, fun _ ↦ inferInstance⟩, fun ⟨_, hStalk⟩ ↦ ⟨hStalk⟩⟩

/-- The spectrum of a regular ring is regular. -/
instance isRegular_Spec (R : CommRingCat.{u}) [IsRegularRing R] : IsRegular (Spec R) where
  isRegularLocalRing_stalk _ := inferInstance

/-- The spectrum of a ring is regular exactly when the ring is regular.
This is the affine case of Stacks, Lemma 28.9.3 (02IU). -/
@[stacks 02IU "affine case"]
theorem isRegular_Spec_iff (R : CommRingCat.{u}) :
    IsRegular (Spec R) ↔ IsRegularRing R := by
  refine ⟨fun _ ↦ ?_, fun _ ↦ inferInstance⟩
  have : IsNoetherianRing R := isLocallyNoetherian_Spec.mp inferInstance
  exact (isRegularRing_iff_isRegularLocalRing_stalk_Spec R).mpr fun _ ↦ inferInstance

/-- A regular scheme is normal. Stacks, Lemma 28.9.4 (0569). -/
@[stacks 0569]
instance IsNormalScheme.of_isRegular [IsRegular X] : IsNormalScheme X := by
  refine isNormalScheme_iff_forall_affineOpens.mpr fun U ↦ ?_
  have := IsLocallyNoetherian.component_noetherian U
  have : IsRegularRing Γ(X, U) :=
    (isRegularRing_iff_isRegularLocalRing_stalk U.2).mpr fun _ _ ↦ inferInstance
  exact (isNormalScheme_Spec_iff_forall_localization Γ(X, U)).mpr fun _ _ ↦
    ⟨inferInstance, inferInstance⟩

end TauCeti.AlgebraicGeometry
