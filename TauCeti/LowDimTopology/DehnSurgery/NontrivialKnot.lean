/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Sphere
public import TauCeti.AlgebraicTopology.UniversalCover.LensSpace.FundamentalGroup
public import TauCeti.Geometry.Manifold.SmoothEmbedding.SmoothAmbientIsotopy.Basic
public import TauCeti.LowDimTopology.DehnSurgery.LensSpace
public import TauCeti.LowDimTopology.DehnSurgery.Unknot

/-!
# Surgery on nontrivial knots: Property P and Property R

Let `Φ` be a solid torus neighbourhood of a knot `f : S¹ → X`. A Dehn filling of the knot exterior
along a slope other than the meridian of `Φ` is a *nontrivial surgery* on the knot; the filling
along the meridian is `X` itself (`TauCeti.IsSolidTorusNeighborhood.meridianDehnFilling`). Two
classical properties of a knot ask that nontrivial surgeries never recover the simplest closed
`3`-manifolds:

* `f` has **Property P** (`TauCeti.HasPropertyP`) when no nontrivial surgery on `f` is simply
  connected, whatever the solid torus neighbourhood;
* `f` has **Property R** (`TauCeti.HasPropertyR`) when no `0`-surgery on `f` is homeomorphic to
  `S¹ × S²`. The slope `0` is the longitude of the preferred framing
  (`TauCeti.IsSolidTorusNeighborhood.preferredFramedBoundaryTorus`), which is defined when the
  reduced integral homology of `X` vanishes in degrees `1` and `2`.

Neither property holds for the unknot in `S³`: its `1`-surgery is the lens space `L(1; 1, 1)`,
which is simply connected (`TauCeti.not_hasPropertyP_unknot`), and its `0`-surgery is `S¹ × S²`
(`TauCeti.not_hasPropertyR_unknot`). The two theorems below say that the unknot is the only
exception among smooth knots in `S³`. They are recorded as propositions, not proved.

* **The Property P theorem** (`TauCeti.KronheimerMrowkaPropertyPTheorem`), Kirby's problem 1.15:
  every smooth knot in `S³` that is not smoothly ambient isotopic to the unknot has Property P.
  Culler, Gordon, Luecke and Shalen reduced it to the surgeries with coefficients `±1`, and
  Kronheimer and Mrowka proved it for those. Consequently no nontrivial surgery on such a knot is
  `S³` (`TauCeti.KronheimerMrowkaPropertyPTheorem.isEmpty_homeomorph_sphere`), which is the
  surgery statement behind Gordon and Luecke's theorem that knots are determined by their
  complements.
* **Gabai's Property R theorem** (`TauCeti.GabaiPropertyRTheorem`), Kirby's problem 1.82 for one
  component: every smooth knot in `S³` that is not smoothly ambient isotopic to the unknot has
  Property R.

Under either theorem the corresponding surgery detects the unknot
(`TauCeti.KronheimerMrowkaPropertyPTheorem.smoothAmbientIsotopic_unknot`,
`TauCeti.GabaiPropertyRTheorem.smoothAmbientIsotopic_unknot`).

## Main definitions

* `TauCeti.HasPropertyP`: no nontrivial Dehn surgery on the knot is simply connected.
* `TauCeti.HasPropertyR`: no `0`-surgery on the knot is homeomorphic to `S¹ × S²`.
* `TauCeti.KronheimerMrowkaPropertyPTheorem`, `TauCeti.GabaiPropertyRTheorem`: the statements
  above, as propositions.

## Main results

* `TauCeti.HasPropertyP.not_simplyConnectedSpace`, `TauCeti.HasPropertyP.isEmpty_homeomorph`,
  `TauCeti.HasPropertyR.isEmpty_homeomorph`: applying the properties.
* `TauCeti.KronheimerMrowkaPropertyPTheorem.hasPropertyP`,
  `TauCeti.GabaiPropertyRTheorem.hasPropertyR`: applying the theorems.
* `TauCeti.KronheimerMrowkaPropertyPTheorem.isEmpty_homeomorph_sphere`,
  `TauCeti.KronheimerMrowkaPropertyPTheorem.smoothAmbientIsotopic_unknot`,
  `TauCeti.GabaiPropertyRTheorem.smoothAmbientIsotopic_unknot`: under the theorems, no nontrivial
  surgery on a nontrivial knot is `S³`, and the surgeries detect the unknot.
* `TauCeti.not_hasPropertyP_unknot`, `TauCeti.not_hasPropertyR_unknot`: the unknot has neither
  property, so the nontriviality hypotheses of the two theorems cannot be dropped.

## References

* R. Kirby (ed.), *Problems in Low-Dimensional Topology*, Problems 1.15 and 1.82, in *Geometric
  Topology*, AMS/IP Stud. Adv. Math. 2.2 (1997).
* M. Culler, C. McA. Gordon, J. Luecke, P. B. Shalen, *Dehn surgery on knots*, Ann. of Math. 125
  (1987), 237–300.
* P. B. Kronheimer, T. S. Mrowka, *Witten's conjecture and Property P*, Geom. Topol. 8 (2004),
  295–310.
* D. Gabai, *Foliations and the topology of 3-manifolds. III*, J. Differential Geom. 26 (1987),
  479–536 (Property R).
* C. McA. Gordon, J. Luecke, *Knots are determined by their complements*, J. Amer. Math. Soc. 2
  (1989), 371–415.
* D. Rolfsen, *Knots and Links*, Publish or Perish (1976), Chapter 9 (surgery on the unknot).
-/

public section

open CategoryTheory Limits Metric Topology
open scoped Manifold

namespace TauCeti

variable {X : Type} [TopologicalSpace X] [T2Space X]

/-! ### Property P -/

/-- A knot `f : S¹ → X` has **Property P** when no nontrivial Dehn surgery on it is simply
connected: for every solid torus neighbourhood `Φ` of `f`, no Dehn filling of the knot exterior
along a slope other than the meridian of `Φ` is simply connected (Kirby's problem 1.15). -/
def HasPropertyP (f : Circle → X) : Prop :=
  ∀ (Φ : SolidTorus → X) (h : IsSolidTorusNeighborhood f Φ) (s : Slope h.framedBoundaryTorus.H)
    (Y : Type) [TopologicalSpace Y], DehnFilling h s Y → s ≠ h.framedBoundaryTorus.meridian →
      ¬ SimplyConnectedSpace Y

/-- Unfolding `TauCeti.HasPropertyP`. -/
theorem hasPropertyP_iff (f : Circle → X) :
    HasPropertyP f ↔
      ∀ (Φ : SolidTorus → X) (h : IsSolidTorusNeighborhood f Φ)
        (s : Slope h.framedBoundaryTorus.H) (Y : Type) [TopologicalSpace Y],
        DehnFilling h s Y → s ≠ h.framedBoundaryTorus.meridian → ¬ SimplyConnectedSpace Y :=
  Iff.rfl

variable {f : Circle → X} {Φ : SolidTorus → X} {h : IsSolidTorusNeighborhood f Φ}
  {Y : Type} [TopologicalSpace Y]

/-- A Dehn filling of the exterior of a knot with Property P along a slope other than the meridian
is not simply connected. -/
theorem HasPropertyP.not_simplyConnectedSpace (hf : HasPropertyP f)
    {s : Slope h.framedBoundaryTorus.H} (F : DehnFilling h s Y)
    (hs : s ≠ h.framedBoundaryTorus.meridian) : ¬ SimplyConnectedSpace Y :=
  hf Φ h s Y F hs

/-- A Dehn filling of the exterior of a knot with Property P along a slope other than the meridian
is not homeomorphic to any simply connected space. -/
theorem HasPropertyP.isEmpty_homeomorph (hf : HasPropertyP f)
    {s : Slope h.framedBoundaryTorus.H} (F : DehnFilling h s Y)
    (hs : s ≠ h.framedBoundaryTorus.meridian) (Z : Type*) [TopologicalSpace Z]
    [SimplyConnectedSpace Z] : IsEmpty (Y ≃ₜ Z) :=
  ⟨fun e ↦ (isEmpty_homotopyEquiv_of_not_simplyConnectedSpace
    (hf.not_simplyConnectedSpace F hs) Z).false e.toHomotopyEquiv⟩

/-! ### Property R -/

/-- A knot `f : S¹ → X` has **Property R** when no `0`-surgery on it is homeomorphic to `S¹ × S²`:
for every solid torus neighbourhood `Φ` of `f`, no Dehn filling of the knot exterior along the
longitude of the preferred framing is homeomorphic to `S¹ × S²` (Kirby's problem 1.82). The
preferred framing is defined from the proofs `h₁`, `h₂` that the reduced integral homology of `X`
vanishes in degrees `1` and `2`. -/
def HasPropertyR
    (h₁ : IsZero ((reducedSingularHomologyFunctor (ModuleCat.of ℤ ℤ) 1).obj (TopCat.of X)))
    (h₂ : IsZero ((reducedSingularHomologyFunctor (ModuleCat.of ℤ ℤ) 2).obj (TopCat.of X)))
    (f : Circle → X) : Prop :=
  ∀ (Φ : SolidTorus → X) (h : IsSolidTorusNeighborhood f Φ) (Y : Type) [TopologicalSpace Y],
    DehnFilling h (h.preferredFramedBoundaryTorus h₁ h₂).longitude Y →
      IsEmpty (Y ≃ₜ Circle × sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)

/-- Unfolding `TauCeti.HasPropertyR`. -/
theorem hasPropertyR_iff
    (h₁ : IsZero ((reducedSingularHomologyFunctor (ModuleCat.of ℤ ℤ) 1).obj (TopCat.of X)))
    (h₂ : IsZero ((reducedSingularHomologyFunctor (ModuleCat.of ℤ ℤ) 2).obj (TopCat.of X)))
    (f : Circle → X) :
    HasPropertyR h₁ h₂ f ↔
      ∀ (Φ : SolidTorus → X) (h : IsSolidTorusNeighborhood f Φ) (Y : Type) [TopologicalSpace Y],
        DehnFilling h (h.preferredFramedBoundaryTorus h₁ h₂).longitude Y →
          IsEmpty (Y ≃ₜ Circle × sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :=
  Iff.rfl

/-- A `0`-surgery on a knot with Property R is not homeomorphic to `S¹ × S²`. -/
theorem HasPropertyR.isEmpty_homeomorph
    {h₁ : IsZero ((reducedSingularHomologyFunctor (ModuleCat.of ℤ ℤ) 1).obj (TopCat.of X))}
    {h₂ : IsZero ((reducedSingularHomologyFunctor (ModuleCat.of ℤ ℤ) 2).obj (TopCat.of X))}
    (hf : HasPropertyR h₁ h₂ f)
    (F : DehnFilling h (h.preferredFramedBoundaryTorus h₁ h₂).longitude Y) :
    IsEmpty (Y ≃ₜ Circle × sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :=
  hf Φ h Y F

/-! ### The unknot -/

/-- **The unknot does not have Property P.** The `1`-surgery on the unknot is the lens space
`L(1; 1, 1)` (`TauCeti.unknotLensSpaceDehnFilling`), which is simply connected
(`TauCeti.LensSpace.simplyConnectedSpace_iff`). -/
@[simp]
theorem not_hasPropertyP_unknot : ¬ HasPropertyP unknot := by
  intro hP
  have : SimplyConnectedSpace (LensSpace 1 (1 : Fin 2 → (ZMod 1)ˣ)) :=
    (LensSpace.simplyConnectedSpace_iff 1 1 le_rfl).2 rfl
  refine hP.not_simplyConnectedSpace
    (unknotLensSpaceDehnFilling 1 1 (q := 1) (s := 1) (t := 0) (by norm_num)
      (Subsingleton.elim _ _)) ?_ this
  -- The slope has the finite value `1 / 1`, so it is not the meridian.
  rw [slopeValue_of_snd_ne_zero one_ne_zero]
  exact FramedBoundaryTorus.slopeEquiv_symm_coe_ne_meridian _ _

/-- **The unknot does not have Property R.** Its `0`-surgery is `S¹ × S²`
(`TauCeti.unknotZeroDehnFilling`), since the framing of its standard solid torus neighbourhood is
the preferred framing (`TauCeti.preferredFramedBoundaryTorus_unknotSolidTorus`). -/
@[simp]
theorem not_hasPropertyR_unknot
    (h₁ : IsZero ((reducedSingularHomologyFunctor (ModuleCat.of ℤ ℤ) 1).obj
      (TopCat.of (sphere (0 : EuclideanSpace ℝ (Fin 4)) 1))))
    (h₂ : IsZero ((reducedSingularHomologyFunctor (ModuleCat.of ℤ ℤ) 2).obj
      (TopCat.of (sphere (0 : EuclideanSpace ℝ (Fin 4)) 1)))) :
    ¬ HasPropertyR h₁ h₂ unknot := by
  intro hR
  -- The preferred framing is the framing of `TauCeti.unknotSolidTorus`, so they share the
  -- longitude.
  have hlong :
      (isSolidTorusNeighborhood_unknotSolidTorus.preferredFramedBoundaryTorus h₁ h₂).longitude =
        isSolidTorusNeighborhood_unknotSolidTorus.framedBoundaryTorus.longitude :=
    preferredFramedBoundaryTorus_unknotSolidTorus_longitude h₁ h₂
  exact (hR.isEmpty_homeomorph (hlong ▸ unknotZeroDehnFilling)).false (Homeomorph.refl _)

/-! ### Knots in `S³` -/

/-- **The Property P theorem** (Kirby's problem 1.15, proved by Kronheimer and Mrowka after the
reduction of Culler, Gordon, Luecke and Shalen to the surgery coefficients `±1`): every smooth knot
`K : S¹ → S³` that is not smoothly ambient isotopic to the unknot has Property P, so no Dehn
filling of its exterior along a slope other than the meridian is simply connected. The
nontriviality hypothesis cannot be dropped (`TauCeti.not_hasPropertyP_unknot`). The theorem is
recorded, not proved. -/
def KronheimerMrowkaPropertyPTheorem : Prop :=
  ∀ K : SmoothCircleEmbedding (𝓡 3) (sphere (0 : EuclideanSpace ℝ (Fin 4)) 1),
    ¬ SmoothEmbedding.SmoothAmbientIsotopic K unknot → HasPropertyP K

/-- **Gabai's Property R theorem** (Kirby's problem 1.82 for knots): every smooth knot
`K : S¹ → S³` that is not smoothly ambient isotopic to the unknot has Property R, so no `0`-surgery
on it is homeomorphic to `S¹ × S²`. The preferred framing is defined because the reduced integral
homology of `S³` vanishes in degrees `1` and `2`
(`TauCeti.isZero_reducedSingularHomologyFunctor_one_sphere_euclideanSpace_fin_four` and
`TauCeti.isZero_reducedSingularHomologyFunctor_two_sphere_euclideanSpace_fin_four`). The
nontriviality hypothesis cannot be dropped (`TauCeti.not_hasPropertyR_unknot`). The theorem is
recorded, not proved. -/
def GabaiPropertyRTheorem : Prop :=
  ∀ K : SmoothCircleEmbedding (𝓡 3) (sphere (0 : EuclideanSpace ℝ (Fin 4)) 1),
    ¬ SmoothEmbedding.SmoothAmbientIsotopic K unknot →
      HasPropertyR (isZero_reducedSingularHomologyFunctor_one_sphere_euclideanSpace_fin_four _)
        (isZero_reducedSingularHomologyFunctor_two_sphere_euclideanSpace_fin_four _) K

section Sphere

variable {K : SmoothCircleEmbedding (𝓡 3) (sphere (0 : EuclideanSpace ℝ (Fin 4)) 1)}
  {Φ : SolidTorus → sphere (0 : EuclideanSpace ℝ (Fin 4)) 1} {h : IsSolidTorusNeighborhood K Φ}

/-- Applying the Property P theorem: a knot in `S³` that is not smoothly ambient isotopic to the
unknot has Property P. -/
theorem KronheimerMrowkaPropertyPTheorem.hasPropertyP (hP : KronheimerMrowkaPropertyPTheorem)
    (hK : ¬ SmoothEmbedding.SmoothAmbientIsotopic K unknot) : HasPropertyP K :=
  hP K hK

/-- Applying Gabai's theorem: a knot in `S³` that is not smoothly ambient isotopic to the unknot
has Property R, for any proofs that the reduced integral homology of `S³` vanishes in degrees `1`
and `2`. -/
theorem GabaiPropertyRTheorem.hasPropertyR (hR : GabaiPropertyRTheorem)
    (hK : ¬ SmoothEmbedding.SmoothAmbientIsotopic K unknot)
    (h₁ : IsZero ((reducedSingularHomologyFunctor (ModuleCat.of ℤ ℤ) 1).obj
      (TopCat.of (sphere (0 : EuclideanSpace ℝ (Fin 4)) 1))))
    (h₂ : IsZero ((reducedSingularHomologyFunctor (ModuleCat.of ℤ ℤ) 2).obj
      (TopCat.of (sphere (0 : EuclideanSpace ℝ (Fin 4)) 1)))) :
    HasPropertyR h₁ h₂ K :=
  hR K hK

/-- **Nontrivial surgery on a nontrivial knot is not `S³`**, assuming the Property P theorem: a
Dehn filling of the exterior of a knot in `S³` that is not smoothly ambient isotopic to the unknot,
along a slope other than the meridian, is not homeomorphic to `S³`. -/
theorem KronheimerMrowkaPropertyPTheorem.isEmpty_homeomorph_sphere
    (hP : KronheimerMrowkaPropertyPTheorem)
    (hK : ¬ SmoothEmbedding.SmoothAmbientIsotopic K unknot) {s : Slope h.framedBoundaryTorus.H}
    (F : DehnFilling h s Y) (hs : s ≠ h.framedBoundaryTorus.meridian) :
    IsEmpty (Y ≃ₜ sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) :=
  have := simplyConnectedSpace_sphere_euclideanSpace (n := 3) (by norm_num)
  (hP.hasPropertyP hK).isEmpty_homeomorph F hs _

/-- **Simply connected surgeries detect the unknot**, assuming the Property P theorem: if a Dehn
filling of the exterior of a knot in `S³` along a slope other than the meridian is simply
connected, then the knot is smoothly ambient isotopic to the unknot. -/
theorem KronheimerMrowkaPropertyPTheorem.smoothAmbientIsotopic_unknot
    (hP : KronheimerMrowkaPropertyPTheorem) {s : Slope h.framedBoundaryTorus.H}
    (F : DehnFilling h s Y) (hs : s ≠ h.framedBoundaryTorus.meridian) [SimplyConnectedSpace Y] :
    SmoothEmbedding.SmoothAmbientIsotopic K unknot :=
  by_contra fun hK ↦ (hP.hasPropertyP hK).not_simplyConnectedSpace F hs inferInstance

variable
  (h₁ : IsZero ((reducedSingularHomologyFunctor (ModuleCat.of ℤ ℤ) 1).obj
    (TopCat.of (sphere (0 : EuclideanSpace ℝ (Fin 4)) 1))))
  (h₂ : IsZero ((reducedSingularHomologyFunctor (ModuleCat.of ℤ ℤ) 2).obj
    (TopCat.of (sphere (0 : EuclideanSpace ℝ (Fin 4)) 1))))

/-- Applying Gabai's theorem: a `0`-surgery on a knot in `S³` that is not smoothly ambient isotopic
to the unknot is not homeomorphic to `S¹ × S²`. The `0`-surgery is read in the preferred framing
defined from any proofs that the reduced integral homology of `S³` vanishes in degrees `1` and
`2`. -/
theorem GabaiPropertyRTheorem.isEmpty_homeomorph (hR : GabaiPropertyRTheorem)
    (hK : ¬ SmoothEmbedding.SmoothAmbientIsotopic K unknot)
    (F : DehnFilling h (h.preferredFramedBoundaryTorus h₁ h₂).longitude Y) :
    IsEmpty (Y ≃ₜ Circle × sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :=
  (hR.hasPropertyR hK h₁ h₂).isEmpty_homeomorph F

/-- **`0`-surgery detects the unknot**, assuming Gabai's theorem: if a `0`-surgery on a knot in
`S³` is homeomorphic to `S¹ × S²`, then the knot is smoothly ambient isotopic to the unknot. -/
theorem GabaiPropertyRTheorem.smoothAmbientIsotopic_unknot (hR : GabaiPropertyRTheorem)
    (F : DehnFilling h (h.preferredFramedBoundaryTorus h₁ h₂).longitude Y)
    (e : Y ≃ₜ Circle × sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    SmoothEmbedding.SmoothAmbientIsotopic K unknot :=
  by_contra fun hK ↦ (hR.isEmpty_homeomorph h₁ h₂ hK F).false e

end Sphere

end TauCeti
