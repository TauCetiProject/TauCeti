/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Scheme.Normal
public import TauCeti.RingTheory.RegularLocalRing.Normal
public import TauCeti.AlgebraicGeometry.Morphisms.Smooth.Regular

/-!
# Regular schemes

A scheme is regular if it is locally Noetherian and every local ring is regular. We use the
stalkwise characterization in Stacks, Lemma 28.9.2 (02IT). Regularity is preserved under open
immersions and smooth morphisms and can be checked on affine neighbourhoods of each point.
It is also equivalent to regularity of every affine-open section ring. The spectrum of a
ring is regular exactly when the ring is regular, and regular schemes are normal. Normality
follows from the affine criterion and the ring-level theorem
`TauCeti.IsRegularRing.isIntegrallyClosed`.

## Main declarations

* `TauCeti.AlgebraicGeometry.IsRegular`: regularity of a scheme.
* `TauCeti.AlgebraicGeometry.isRegular_iff_forall_stalk`: the stalkwise characterization.
* `TauCeti.AlgebraicGeometry.IsRegular.of_isOpenImmersion`: open subschemes are regular.
* `TauCeti.AlgebraicGeometry.IsRegular.of_smooth`: schemes smooth over a regular scheme are regular.
* `TauCeti.AlgebraicGeometry.isRegular_iff_exists_affineOpen`: the affine-neighbourhood criterion.
* `TauCeti.AlgebraicGeometry.isRegular_iff_forall_affineOpens`: the affine-open criterion.
* `TauCeti.AlgebraicGeometry.IsRegular.component_regular`: regular affine-open section rings.
* `TauCeti.AlgebraicGeometry.isRegular_Spec_iff`: regularity of an affine scheme.
* `TauCeti.AlgebraicGeometry.IsNormalScheme.of_isRegular`: regular schemes are normal.

## References

* [Stacks Project, Lemma 28.9.2](https://stacks.math.columbia.edu/tag/02IT).
* [Stacks Project, Lemma 28.9.3](https://stacks.math.columbia.edu/tag/02IU).
* [Stacks Project, Lemma 28.9.4](https://stacks.math.columbia.edu/tag/0569).
* [Stacks Project, Definition 28.9.1](https://stacks.math.columbia.edu/tag/02IS).
* [Stacks Project, Lemma 35.18.4](https://stacks.math.columbia.edu/tag/036D).
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

/-- The source of an open immersion into a regular scheme is regular. -/
theorem IsRegular.of_isOpenImmersion {Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    [IsRegular Y] : IsRegular X := by
  have : IsLocallyNoetherian X := isLocallyNoetherian_of_isOpenImmersion f
  exact ⟨fun x ↦ (isRegularLocalRing_stalk_iff_of_isOpenImmersion f x).mp inferInstance⟩

/-- The source of a smooth morphism into a regular scheme is regular.
This is the preservation direction of Stacks, Lemma 35.18.4 (036D). -/
@[stacks 036D "preservation under smooth morphisms"]
theorem IsRegular.of_smooth {target : Scheme.{u}} (morphism : X ⟶ target) [Smooth morphism]
    [IsRegular target] : IsRegular X := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian morphism
  exact ⟨isRegularLocalRing_stalk_of_smooth morphism⟩

/-- Every open subscheme of a regular scheme is regular. -/
instance IsRegular.opens [IsRegular X] (U : X.Opens) : IsRegular U :=
  .of_isOpenImmersion U.ι

/-- The spectrum of a regular ring is regular. -/
instance isRegular_Spec (R : CommRingCat.{u}) [IsRegularRing R] : IsRegular (Spec R) where
  isRegularLocalRing_stalk _ := inferInstance

/-- A scheme is regular exactly when each point has an affine open neighbourhood with a
regular ring of sections. This is Stacks, Definition 28.9.1 (02IS). -/
@[stacks 02IS]
theorem isRegular_iff_exists_affineOpen :
    IsRegular X ↔ ∀ point : X, ∃ openSet : X.affineOpens,
      point ∈ (openSet : X.Opens) ∧ IsRegularRing Γ(X, openSet) := by
  refine ⟨fun _ point ↦ ?_, fun hRegular ↦ ?_⟩
  · obtain ⟨openSet, hAffine, hMem, -⟩ :=
      exists_isAffineOpen_mem_and_subset (TopologicalSpace.Opens.mem_top point)
    have := IsLocallyNoetherian.component_noetherian ⟨openSet, hAffine⟩
    exact ⟨⟨openSet, hAffine⟩, hMem,
      (isRegularRing_iff_isRegularLocalRing_stalk hAffine).mpr fun _ _ ↦ inferInstance⟩
  · choose openSet hMem hRing using hRegular
    have hCover : (⨆ point, (openSet point : X.Opens)) = ⊤ := by
      ext point
      exact ⟨fun _ ↦ trivial, fun _ ↦ TopologicalSpace.Opens.mem_iSup.mpr ⟨point, hMem point⟩⟩
    have hNoeth : ∀ point, IsNoetherianRing Γ(X, openSet point) := fun point ↦ by
      have : IsRegularRing Γ(X, openSet point) := hRing point
      infer_instance
    have : IsLocallyNoetherian X := isLocallyNoetherian_of_affine_cover hCover hNoeth
    refine ⟨fun point ↦ ?_⟩
    have : IsRegularRing Γ(X, openSet point) := hRing point
    exact isRegularLocalRing_stalk_of_isRegularRing (openSet point).2 (hMem point)

/-- A scheme is regular exactly when its affine-open section rings are regular. -/
@[stacks 02IU]
theorem isRegular_iff_forall_affineOpens :
    IsRegular X ↔ ∀ U : X.affineOpens, IsRegularRing Γ(X, U) := by
  refine ⟨fun _ U ↦ ?_, fun hRegular ↦ ?_⟩
  · have := IsLocallyNoetherian.component_noetherian U
    exact (isRegularRing_iff_isRegularLocalRing_stalk U.2).mpr fun _ _ ↦ inferInstance
  · apply isRegular_iff_exists_affineOpen.mpr
    intro point
    obtain ⟨openSet, hAffine, hMem, -⟩ :=
      exists_isAffineOpen_mem_and_subset (TopologicalSpace.Opens.mem_top point)
    exact ⟨⟨openSet, hAffine⟩, hMem, hRegular ⟨openSet, hAffine⟩⟩

/-- The section ring of an affine open in a regular scheme is regular. -/
instance IsRegular.component_regular [IsRegular X] (U : X.affineOpens) :
    IsRegularRing Γ(X, U) :=
  (isRegular_iff_forall_affineOpens.mp inferInstance) U

/-- The spectrum of a ring is regular exactly when the ring is regular.
This is the affine case of Stacks, Lemma 28.9.3 (02IU). -/
@[stacks 02IU "affine case"]
theorem isRegular_Spec_iff (R : CommRingCat.{u}) :
    IsRegular (Spec R) ↔ IsRegularRing R := by
  refine ⟨fun h ↦ ?_, fun _ ↦ inferInstance⟩
  have htop := (isRegular_iff_forall_affineOpens.mp h)
    ⟨⊤, isAffineOpen_top (Spec R)⟩
  let e := (Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv
  exact @IsRegularRing.of_ringEquiv Γ(Spec R, ⊤) _ R _ e htop

/-- A regular scheme is normal. Stacks, Lemma 28.9.4 (0569). -/
@[stacks 0569]
instance IsNormalScheme.of_isRegular [IsRegular X] : IsNormalScheme X := by
  refine isNormalScheme_iff_forall_affineOpens.mpr fun U ↦ ?_
  have : IsRegularRing Γ(X, U) := IsRegular.component_regular U
  exact (isNormalScheme_Spec_iff_forall_localization Γ(X, U)).mpr fun _ _ ↦
    ⟨inferInstance, inferInstance⟩

end TauCeti.AlgebraicGeometry
