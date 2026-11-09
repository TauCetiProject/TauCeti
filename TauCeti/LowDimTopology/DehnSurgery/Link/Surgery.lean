/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LowDimTopology.DehnSurgery.Link.Filling
public import TauCeti.LowDimTopology.DehnSurgery.SeifertFraming

/-!
# Surgery coefficients of rational surgery on a link

Let `Φ i : D² × S¹ → X` be pairwise disjoint solid torus neighbourhoods of the components `f i` of
a link in a Hausdorff space `X` with `H₁(X; ℤ) = H₂(X; ℤ) = 0`, such as `S³` or an integral
homology sphere (`TauCeti.IsSolidTorusLinkNeighborhood`). *Rational surgery* on the link with
coefficients `r i ∈ ℚ ∪ {∞}` is the Dehn filling of the link exterior
(`TauCeti.LinkDehnFilling`) whose `i`-th filling slope has value `r i` in the preferred framing of
the `i`-th component (Rolfsen, *Knots and Links*, 9G). That framing is the one of the component
alone (`TauCeti.IsSolidTorusNeighborhood.preferredFramedBoundaryTorus`): its longitude is
null-homologous in the complement of that component, regardless of the other components. These
slopes are `TauCeti.IsSolidTorusLinkNeighborhood.surgerySlope`, so that a rational surgery on the
link with coefficients `r`, inside a space `Y`, is a term of
`LinkDehnFilling h (h.surgerySlope h₁ h₂ r) Y`.

The boundary tori are also framed by the neighbourhoods `Φ i` themselves. In the framing of
`Φ i`, the `i`-th surgery slope has value `r i - n i`, where `n i` is the framing number of `Φ i`
(`TauCeti.IsSolidTorusLinkNeighborhood.value_surgerySlope_framedBoundaryTorus`). The coefficient
`∞` is the meridian of each component, and `∞`-surgery on every component gives back the ambient
space (`TauCeti.IsSolidTorusLinkNeighborhood.nonempty_linkDehnFilling_surgerySlope_infty`).

## Main definitions

* `TauCeti.IsSolidTorusLinkNeighborhood.surgerySlope`: the filling slopes of rational surgery on a
  link with given coefficients.

## Main results

* `TauCeti.IsSolidTorusLinkNeighborhood.surgerySlope_eq_iff`: the `i`-th surgery slope is the slope
  of value `r i` in the preferred framing of the `i`-th component.
* `TauCeti.IsSolidTorusLinkNeighborhood.value_surgerySlope_framedBoundaryTorus`: its value in the
  framing of `Φ i` is `r i` minus the framing number of `Φ i`.
* `TauCeti.IsSolidTorusLinkNeighborhood.surgerySlope_eq_meridian_iff`: the surgery slope is the
  meridian exactly for the coefficient `∞`.
* `TauCeti.IsSolidTorusLinkNeighborhood.nonempty_linkDehnFilling_surgerySlope_infty`: the ambient
  space is the `∞`-surgery on every component.

## References

* D. Rolfsen, *Knots and Links*, Publish or Perish (1976), Section 2E (the preferred framing of a
  knot in `S³`) and Chapter 9, Sections 9F and 9G (surgery on a link: the surgery coefficient of
  each component is read in its own preferred framing).
-/

public section

noncomputable section

open CategoryTheory Limits Set

open scoped OnePoint

namespace TauCeti

namespace IsSolidTorusLinkNeighborhood

variable {ι : Type*} {X : Type} [TopologicalSpace X] [T2Space X] {f : ι → Circle → X}
  {Φ : ι → SolidTorus → X}
  (h₁ : IsZero ((reducedSingularHomologyFunctor (ModuleCat.of ℤ ℤ) 1).obj (TopCat.of X)))
  (h₂ : IsZero ((reducedSingularHomologyFunctor (ModuleCat.of ℤ ℤ) 2).obj (TopCat.of X)))
  (h : IsSolidTorusLinkNeighborhood f Φ) (r : ι → OnePoint ℚ) (i : ι)

/-- The **surgery slopes** of rational surgery on a link with coefficients `r i ∈ ℚ ∪ {∞}`: on the
`i`-th boundary torus of the link exterior, the slope of value `r i` in the preferred framing of
the `i`-th component. For `r i = p / q` in lowest terms it is the class `p · μᵢ + q · λᵢ`, for the
meridian `μᵢ` and the preferred longitude `λᵢ` of the `i`-th component. -/
def surgerySlope : Slope (h.neighborhood i).framedBoundaryTorus.H :=
  ((h.neighborhood i).preferredFramedBoundaryTorus h₁ h₂).slopeEquiv.symm (r i)

/-- The `i`-th surgery slope is the slope of value `r i` in the preferred framing of the `i`-th
component. -/
theorem surgerySlope_eq_iff (s : Slope (h.neighborhood i).framedBoundaryTorus.H) :
    h.surgerySlope h₁ h₂ r i = s ↔
      ((h.neighborhood i).preferredFramedBoundaryTorus h₁ h₂).value s = r i := by
  rw [surgerySlope, Equiv.symm_apply_eq, FramedBoundaryTorus.slopeEquiv_apply, eq_comm]

/-- The `i`-th surgery slope has value `r i` in the preferred framing of the `i`-th component. -/
@[simp]
theorem value_surgerySlope :
    ((h.neighborhood i).preferredFramedBoundaryTorus h₁ h₂).value (h.surgerySlope h₁ h₂ r i) =
      r i :=
  (h.surgerySlope_eq_iff h₁ h₂ r i _).1 rfl

/-- **Surgery coefficients in the framing of a solid torus neighbourhood.** In the framing of the
boundary torus by `Φ i`, the `i`-th surgery slope has value `r i - n`, where `n` is the framing
number of `Φ i`, and value `∞` if `r i = ∞`. -/
@[simp]
theorem value_surgerySlope_framedBoundaryTorus :
    (h.neighborhood i).framedBoundaryTorus.value (h.surgerySlope h₁ h₂ r i) =
      (r i).map (· - ((h.neighborhood i).framingNumber h₁ h₂ : ℚ)) := by
  have hr := h.value_surgerySlope h₁ h₂ r i
  rw [FramedBoundaryTorus.value_shiftLongitude] at hr
  rw [← hr]
  induction (h.neighborhood i).framedBoundaryTorus.value (h.surgerySlope h₁ h₂ r i) with
  | infty => rfl
  | coe x => simp

/-- The `i`-th surgery slope is the meridian of the `i`-th component exactly when its coefficient
is `∞`. -/
theorem surgerySlope_eq_meridian_iff :
    h.surgerySlope h₁ h₂ r i = (h.neighborhood i).framedBoundaryTorus.meridian ↔ r i = ∞ := by
  rw [surgerySlope_eq_iff, FramedBoundaryTorus.value_shiftLongitude,
    FramedBoundaryTorus.value_meridian, OnePoint.map_infty, eq_comm]

/-- **`∞`-surgery on a link is the ambient space.** The ambient space is the Dehn filling of the
link exterior along the surgery slopes of coefficient `∞` on every component: gluing the solid
torus neighbourhoods back by the identity. -/
theorem nonempty_linkDehnFilling_surgerySlope_infty :
    Nonempty (LinkDehnFilling h (h.surgerySlope h₁ h₂ fun _ ↦ ∞) X) := by
  have hs : h.surgerySlope h₁ h₂ (fun _ ↦ ∞) =
      fun i ↦ (h.neighborhood i).framedBoundaryTorus.meridian :=
    funext fun i ↦ (h.surgerySlope_eq_meridian_iff h₁ h₂ _ i).2 rfl
  rw [hs]
  exact ⟨h.meridianDehnFilling⟩

end IsSolidTorusLinkNeighborhood

end TauCeti
