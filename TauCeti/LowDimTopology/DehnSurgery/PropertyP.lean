/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.UniversalCover.LensSpace.FundamentalGroup
public import TauCeti.Geometry.Manifold.SmoothEmbedding.SmoothAmbientIsotopy.Basic
public import TauCeti.KnotTheory.SmoothCircle
public import TauCeti.LowDimTopology.DehnSurgery.LensSpace

/-!
# Property P

A knot `K` has **Property P** when no nontrivial Dehn surgery on `K` gives a simply connected
manifold. Kirby's problem 1.15 asks whether every nontrivial knot in `S³` has Property P.
Kronheimer and Mrowka proved that it does: Dehn surgery on a knot in `S³` that is not the unknot,
along any slope other than the meridian, never gives a simply connected `3`-manifold.

Both exclusions are needed. Every knot has the trivial filling along its meridian, the
`∞`-surgery, which gives back the ambient space
(`TauCeti.IsSolidTorusNeighborhood.meridianDehnFilling`), and `S³` is simply connected
(`TauCeti.simplyConnectedSpace_sphere_euclideanSpace`). The unknot fails Property P
(`TauCeti.not_hasPropertyP_unknot`): its `1 / n`-surgery is the lens space `L(1; 1, 1)`, the
quotient of `S³` by the trivial group (`TauCeti.unknotLensSpaceDehnFilling`), which is simply
connected (`TauCeti.LensSpace.simplyConnectedSpace_iff`).

* **Property P** (`TauCeti.HasPropertyP f`) is stated for a loop `f : S¹ → X` in a Hausdorff
  space: for every solid torus neighbourhood `Φ` of `f` and every slope `s` on the boundary torus
  of the exterior other than the meridian, no Dehn filling of the exterior along `s`
  (`TauCeti.DehnFilling`) is simply connected. The meridian, the boundary of a disc fibre of `Φ`, is
  the same slope in every framing of the boundary torus, so no framing convention enters. The
  solid torus neighbourhood is arbitrary. Classically this is harmless, although it is not
  formalized here: replacing `Φ` by a smaller neighbourhood, such as the half-radius one whose
  boundary torus is bicollared (`TauCeti.IsSolidTorusNeighborhood.comp_halve`), adds the collar
  `T² × [1/2, 1]` swept out by `Φ` to the exterior, and the two exteriors have the same Dehn
  fillings along each slope, up to homeomorphism.
* **The Property P conjecture** (`TauCeti.PropertyPConjecture`) says that every knot
  `K : S¹ → S³` (a `TauCeti.SmoothCircleEmbedding`) which is not smoothly ambient isotopic to the
  unknot `TauCeti.unknot` has Property P. The orientation of `K` plays no role, since the unknot is
  ambient isotopic to its reverse by a rotation of `S³`.

## Main definitions

* `TauCeti.HasPropertyP f`: no Dehn surgery on `f` along a slope other than the meridian gives a
  simply connected space.
* `TauCeti.PropertyPConjecture`: every knot in `S³` that is not the unknot has Property P.

## Main results

* `TauCeti.exists_dehnFilling_unknot_simplyConnectedSpace`: the `1 / n`-surgery on the unknot is
  simply connected.
* `TauCeti.not_hasPropertyP_unknot`: the unknot does not have Property P.
* `TauCeti.PropertyPConjecture.hasPropertyP`: applying the conjecture to a nontrivial knot.

## References

* R. Kirby (ed.), *Problems in Low-Dimensional Topology*, Problem 1.15, in *Geometric Topology*,
  AMS/IP Stud. Adv. Math. 2.2 (1997).
* P. Kronheimer and T. Mrowka, *Witten's conjecture and Property P*, Geom. Topol. 8 (2004),
  295–310.
* D. Rolfsen, *Knots and Links*, Publish or Perish (1976), Chapter 9 (Dehn surgery, and
  `1 / n`-surgery on the unknot giving `S³`).
-/

public section

open Metric
open scoped Manifold

namespace TauCeti

variable {X : Type} [TopologicalSpace X] [T2Space X]

/-- A loop `f : S¹ → X` has **Property P** when no nontrivial Dehn surgery on it is simply
connected: for every solid torus neighbourhood `Φ` of `f`, every Dehn filling `Y` of the exterior
of `Φ` along a slope `s` other than the meridian of `Φ` fails to be simply connected. -/
def HasPropertyP (f : Circle → X) : Prop :=
  ∀ (Φ : SolidTorus → X) (h : IsSolidTorusNeighborhood f Φ) (s : Slope h.framedBoundaryTorus.H),
    s ≠ h.framedBoundaryTorus.meridian →
      ∀ (Y : Type) [TopologicalSpace Y], DehnFilling h s Y → ¬ SimplyConnectedSpace Y

/-- A Dehn filling of the exterior of a loop with Property P, along a slope other than the
meridian, is not simply connected. -/
theorem HasPropertyP.not_simplyConnectedSpace {f : Circle → X} (hf : HasPropertyP f)
    {Φ : SolidTorus → X} {h : IsSolidTorusNeighborhood f Φ} {s : Slope h.framedBoundaryTorus.H}
    (hs : s ≠ h.framedBoundaryTorus.meridian) {Y : Type} [TopologicalSpace Y]
    (F : DehnFilling h s Y) : ¬ SimplyConnectedSpace Y :=
  hf Φ h s hs Y F

/-- **The Property P conjecture**, Kirby's problem 1.15: every knot `K : S¹ → S³` that is not
smoothly ambient isotopic to the unknot has Property P, so no Dehn surgery on `K` along a slope
other than the meridian gives a simply connected manifold. Kronheimer and Mrowka proved it. -/
def PropertyPConjecture : Prop :=
  ∀ K : SmoothCircleEmbedding (𝓡 3) (sphere (0 : EuclideanSpace ℝ (Fin 4)) 1),
    ¬ SmoothEmbedding.SmoothAmbientIsotopic K unknot → HasPropertyP K

/-- By the Property P conjecture, a knot in `S³` that is not smoothly ambient isotopic to the
unknot has Property P. -/
theorem PropertyPConjecture.hasPropertyP (hP : PropertyPConjecture)
    {K : SmoothCircleEmbedding (𝓡 3) (sphere (0 : EuclideanSpace ℝ (Fin 4)) 1)}
    (hK : ¬ SmoothEmbedding.SmoothAmbientIsotopic K unknot) : HasPropertyP K :=
  hP K hK

/-- **`1 / n`-surgery on the unknot is simply connected.** For every integer `n`, the lens space
`L(1; 1, 1)`, the quotient of `S³` by the trivial group, is a Dehn filling of the exterior of the
unknot along the slope of value `1 / n` in the framing of `TauCeti.unknotSolidTorus`, which is the
preferred framing (`TauCeti.preferredFramedBoundaryTorus_unknotSolidTorus`). -/
theorem exists_dehnFilling_unknot_simplyConnectedSpace (n : ℤ) :
    ∃ (Y : Type) (_ : TopologicalSpace Y),
      Nonempty (DehnFilling isSolidTorusNeighborhood_unknotSolidTorus
        (isSolidTorusNeighborhood_unknotSolidTorus.framedBoundaryTorus.slopeEquiv.symm
          (slopeValue (1, n))) Y) ∧ SimplyConnectedSpace Y := by
  let ℓ : Fin 2 → (ZMod 1)ˣ := 1
  refine ⟨LensSpace 1 ℓ, inferInstance,
    ⟨unknotLensSpaceDehnFilling 1 ℓ (s := 1) (t := 0) (by simp) (Subsingleton.elim _ _)⟩,
    (LensSpace.simplyConnectedSpace_iff 1 ℓ le_rfl).2 rfl⟩

/-- **The unknot does not have Property P**: its `+1`-surgery is simply connected
(`TauCeti.exists_dehnFilling_unknot_simplyConnectedSpace`). So the hypothesis of the Property P
conjecture that the knot is not the unknot cannot be dropped. -/
theorem not_hasPropertyP_unknot : ¬ HasPropertyP (unknot : Circle → _) := by
  intro hP
  obtain ⟨Y, _, ⟨F⟩, hY⟩ := exists_dehnFilling_unknot_simplyConnectedSpace 1
  refine hP.not_simplyConnectedSpace (fun hs ↦ ?_) F hY
  have h := congrArg isSolidTorusNeighborhood_unknotSolidTorus.framedBoundaryTorus.slopeEquiv hs
  rw [Equiv.apply_symm_apply, FramedBoundaryTorus.slopeEquiv_apply,
    FramedBoundaryTorus.value_meridian, slopeValue_of_snd_ne_zero one_ne_zero] at h
  exact OnePoint.coe_ne_infty _ h

end TauCeti
