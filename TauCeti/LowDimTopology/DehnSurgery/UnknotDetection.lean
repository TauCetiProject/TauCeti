/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Sphere
public import TauCeti.Geometry.Manifold.SmoothEmbedding.SmoothAmbientIsotopy.Basic
public import TauCeti.LowDimTopology.DehnSurgery.Unknot
import TauCeti.AlgebraicTopology.Sphere.SimplyConnected

/-!
# Dehn surgery detects the unknot: Property P and Property R

Two classical theorems say that Dehn surgery on a knot in `S³` recognizes the unknot.

* **Property P.** A knot `K` has Property P when no Dehn filling of its exterior along a slope
  other than the meridian is simply connected
  (`TauCeti.IsSolidTorusNeighborhood.HasPropertyP`). The Property P conjecture, Kirby's problem
  1.15, asks whether every nontrivial knot in `S³` has Property P. The first homology of the
  `p / q`-surgery is `ℤ / p`, which rules out every coefficient but `±1 / q`; earlier work reduced
  the conjecture to the coefficients `±1`, and Kronheimer and Mrowka settled that case
  (`TauCeti.KronheimerMrowkaPropertyPTheorem`).
* **Property R.** Gabai proved that the unknot is the only knot in `S³` whose `0`-surgery, the
  filling along the longitude of the preferred framing, is `S¹ × S²`
  (`TauCeti.GabaiPropertyRTheorem`). Kirby's problem 1.82, characterizing the framed links on which
  surgery gives a connected sum of copies of `S¹ × S²`, is its generalization to links.

Both are recorded as propositions about the knots of `TauCeti.SmoothCircleEmbedding` in the unit
sphere of `ℝ⁴`, a knot being trivial when it is smoothly ambient isotopic to `TauCeti.unknot`; they
are not proved. The fillings are those of `TauCeti.DehnFilling`, for every solid torus
neighbourhood of the knot, and the filled spaces range over an arbitrary universe. Both statements
are sharp on the unknot. It does not have Property P, because its `-1 / n`-surgeries are `S³`
(`TauCeti.not_hasPropertyP_unknotSolidTorus`), so the nontriviality hypothesis of
`TauCeti.KronheimerMrowkaPropertyPTheorem` cannot be dropped. Its `0`-surgery is `S¹ × S²`
(`TauCeti.nonempty_dehnFilling_preferredFramedBoundaryTorus_longitude_unknotSolidTorus`), so the
hypothesis of `TauCeti.GabaiPropertyRTheorem` is met.

## Main definitions

* `TauCeti.IsSolidTorusNeighborhood.HasPropertyP`: no nontrivial Dehn filling of the knot exterior
  is simply connected.
* `TauCeti.KronheimerMrowkaPropertyPTheorem`: every nontrivial knot in `S³` has Property P.
* `TauCeti.GabaiPropertyRTheorem`: a knot in `S³` whose `0`-surgery is `S¹ × S²` is trivial.

## Main results

* `TauCeti.not_hasPropertyP_unknotSolidTorus`: the unknot does not have Property P.
* `TauCeti.KronheimerMrowkaPropertyPTheorem.smoothAmbientIsotopic_unknot`: a knot in `S³` with a
  simply connected Dehn filling along a slope other than the meridian is trivial.
* `TauCeti.GabaiPropertyRTheorem.smoothAmbientIsotopic_unknot`: applying Property R.

## References

* R. Kirby (ed.), *Problems in Low-Dimensional Topology*, Problems 1.15 and 1.82, in *Geometric
  Topology*, AMS/IP Stud. Adv. Math. 2.2 (1997).
* P. Kronheimer, T. Mrowka, *Witten's conjecture and Property P*, Geom. Topol. 8 (2004), 295–310.
* D. Gabai, *Foliations and the topology of 3-manifolds III*, J. Differential Geom. 26 (1987),
  479–536 (Property R).
* D. Rolfsen, *Knots and Links*, Publish or Perish (1976), Section 9J (Property P).
-/

public section

open CategoryTheory Limits Metric Topology
open scoped Manifold

universe u

namespace TauCeti

/-! ### Property P -/

namespace IsSolidTorusNeighborhood

variable {X : Type} [TopologicalSpace X] [T2Space X] {f : Circle → X} {Φ : SolidTorus → X}

/-- A knot `f` with solid torus neighbourhood `Φ` has **Property P** when no Dehn filling of its
exterior along a slope other than the meridian is simply connected (Rolfsen, Definition 9J1). The
filled spaces range over `Type u`. -/
def HasPropertyP (h : IsSolidTorusNeighborhood f Φ) : Prop :=
  ∀ s : Slope h.framedBoundaryTorus.H, s ≠ h.framedBoundaryTorus.meridian →
    ∀ (Y : Type u) [TopologicalSpace Y], DehnFilling h s Y → ¬ SimplyConnectedSpace Y

/-- The defining characterization of Property P. -/
theorem hasPropertyP_iff (h : IsSolidTorusNeighborhood f Φ) :
    h.HasPropertyP.{u} ↔ ∀ s : Slope h.framedBoundaryTorus.H, s ≠ h.framedBoundaryTorus.meridian →
      ∀ (Y : Type u) [TopologicalSpace Y], DehnFilling h s Y → ¬ SimplyConnectedSpace Y :=
  Iff.rfl

/-- A Dehn filling along a slope other than the meridian of a knot with Property P is not simply
connected. -/
theorem HasPropertyP.not_simplyConnectedSpace {h : IsSolidTorusNeighborhood f Φ}
    (hP : h.HasPropertyP.{u}) {s : Slope h.framedBoundaryTorus.H}
    (hs : s ≠ h.framedBoundaryTorus.meridian) {Y : Type u} [TopologicalSpace Y]
    (F : DehnFilling h s Y) : ¬ SimplyConnectedSpace Y :=
  hP s hs Y F

end IsSolidTorusNeighborhood

/-- **The unknot does not have Property P.** The `-1`-surgery on the unknot
(`TauCeti.unknotInvIntDehnFilling`) is the simply connected `3`-sphere, and its slope, of value
`-1` in the framing of `TauCeti.unknotSolidTorus`, is not the meridian. -/
theorem not_hasPropertyP_unknotSolidTorus :
    ¬ isSolidTorusNeighborhood_unknotSolidTorus.HasPropertyP.{u} := by
  intro hP
  refine hP.not_simplyConnectedSpace (fun hs ↦ ?_)
    ((unknotInvIntDehnFilling 1).transHomeomorph Homeomorph.ulift.symm)
    ((Homeomorph.ulift.toHomotopyEquiv).simplyConnectedSpace (hY :=
      simplyConnectedSpace_sphere (by
        rw [← Module.finrank_eq_rank, finrank_euclideanSpace_fin]; norm_num) 0 zero_le_one))
  -- The meridian has value `∞`, while the slope of the `(1, -1)` curve has value `-1`.
  have hv := congrArg isSolidTorusNeighborhood_unknotSolidTorus.framedBoundaryTorus.value hs
  rw [FramedBoundaryTorus.value_mk_torusCurveClass _ isCoprime_one_left,
    FramedBoundaryTorus.value_meridian, slopeValue_of_snd_ne_zero (by decide)] at hv
  exact OnePoint.coe_ne_infty _ hv

/-- **The Property P theorem of Kronheimer and Mrowka**, Kirby's problem 1.15: every nontrivial
knot `K : S¹ → S³`, one not smoothly ambient isotopic to the unknot, has Property P for every solid
torus neighbourhood `Φ`: no Dehn filling of its exterior along a slope other than the meridian is
simply connected. The nontriviality hypothesis is needed
(`TauCeti.not_hasPropertyP_unknotSolidTorus`). -/
def KronheimerMrowkaPropertyPTheorem : Prop :=
  ∀ (K : SmoothCircleEmbedding (𝓡 3) (sphere (0 : EuclideanSpace ℝ (Fin 4)) 1))
    (Φ : SolidTorus → sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) (h : IsSolidTorusNeighborhood K Φ),
    ¬ SmoothEmbedding.SmoothAmbientIsotopic K unknot → h.HasPropertyP.{u}

/-- The defining characterization of the Property P theorem. -/
theorem kronheimerMrowkaPropertyPTheorem_iff :
    KronheimerMrowkaPropertyPTheorem.{u} ↔
      ∀ (K : SmoothCircleEmbedding (𝓡 3) (sphere (0 : EuclideanSpace ℝ (Fin 4)) 1))
        (Φ : SolidTorus → sphere (0 : EuclideanSpace ℝ (Fin 4)) 1)
        (h : IsSolidTorusNeighborhood K Φ),
        ¬ SmoothEmbedding.SmoothAmbientIsotopic K unknot → h.HasPropertyP.{u} :=
  Iff.rfl

/-- **Surgery detects the unknot**, by the Property P theorem: a knot in `S³` with a simply
connected Dehn filling along a slope other than the meridian is smoothly ambient isotopic to the
unknot. -/
theorem KronheimerMrowkaPropertyPTheorem.smoothAmbientIsotopic_unknot
    (hKM : KronheimerMrowkaPropertyPTheorem.{u})
    {K : SmoothCircleEmbedding (𝓡 3) (sphere (0 : EuclideanSpace ℝ (Fin 4)) 1)}
    {Φ : SolidTorus → sphere (0 : EuclideanSpace ℝ (Fin 4)) 1} {h : IsSolidTorusNeighborhood K Φ}
    {s : Slope h.framedBoundaryTorus.H} (hs : s ≠ h.framedBoundaryTorus.meridian)
    {Y : Type u} [TopologicalSpace Y] (F : DehnFilling h s Y) [SimplyConnectedSpace Y] :
    SmoothEmbedding.SmoothAmbientIsotopic K unknot := by
  by_contra hK
  exact (hKM K Φ h hK).not_simplyConnectedSpace hs F ‹_›

/-! ### Property R -/

/-- **Gabai's Property R theorem**: a knot `K : S¹ → S³` whose `0`-surgery is homeomorphic to
`S¹ × S²` is smoothly ambient isotopic to the unknot. The `0`-surgery is a Dehn filling of the
exterior of `K`, for any solid torus neighbourhood `Φ`, along the longitude of the preferred framing
(`TauCeti.IsSolidTorusNeighborhood.preferredFramedBoundaryTorus`), which is defined because the
reduced integral homology of `S³` vanishes in degrees `1` and `2`. The unknot meets the hypothesis
(`TauCeti.nonempty_dehnFilling_preferredFramedBoundaryTorus_longitude_unknotSolidTorus`). -/
def GabaiPropertyRTheorem : Prop :=
  ∀ (K : SmoothCircleEmbedding (𝓡 3) (sphere (0 : EuclideanSpace ℝ (Fin 4)) 1))
    (Φ : SolidTorus → sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) (h : IsSolidTorusNeighborhood K Φ)
    (Y : Type u) [TopologicalSpace Y],
    DehnFilling h
        (h.preferredFramedBoundaryTorus
          (isZero_reducedSingularHomologyFunctor_sphere_of_ne _ (n := 3) (by simp) (by norm_num))
          (isZero_reducedSingularHomologyFunctor_sphere_of_ne _ (n := 3) (by simp)
            (by norm_num))).longitude Y →
      Nonempty (Y ≃ₜ Circle × sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) →
      SmoothEmbedding.SmoothAmbientIsotopic K unknot

/-- Gabai's Property R theorem, with the `0`-surgery read in the preferred framing defined from
any proofs that the reduced integral homology of `S³` vanishes in degrees `1` and `2`. -/
theorem gabaiPropertyRTheorem_iff :
    GabaiPropertyRTheorem.{u} ↔
      ∀ (K : SmoothCircleEmbedding (𝓡 3) (sphere (0 : EuclideanSpace ℝ (Fin 4)) 1))
        (Φ : SolidTorus → sphere (0 : EuclideanSpace ℝ (Fin 4)) 1)
        (h : IsSolidTorusNeighborhood K Φ)
        (h₁ : IsZero ((reducedSingularHomologyFunctor (ModuleCat.of ℤ ℤ) 1).obj
          (TopCat.of (sphere (0 : EuclideanSpace ℝ (Fin 4)) 1))))
        (h₂ : IsZero ((reducedSingularHomologyFunctor (ModuleCat.of ℤ ℤ) 2).obj
          (TopCat.of (sphere (0 : EuclideanSpace ℝ (Fin 4)) 1))))
        (Y : Type u) [TopologicalSpace Y],
        DehnFilling h (h.preferredFramedBoundaryTorus h₁ h₂).longitude Y →
          Nonempty (Y ≃ₜ Circle × sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) →
          SmoothEmbedding.SmoothAmbientIsotopic K unknot :=
  ⟨fun hG K Φ h _ _ Y _ F e ↦ hG K Φ h Y F e, fun hG K Φ h Y _ F e ↦ hG K Φ h _ _ Y F e⟩

/-- By Gabai's Property R theorem, a knot in `S³` whose `0`-surgery is homeomorphic to `S¹ × S²` is
smoothly ambient isotopic to the unknot. -/
theorem GabaiPropertyRTheorem.smoothAmbientIsotopic_unknot (hG : GabaiPropertyRTheorem.{u})
    {K : SmoothCircleEmbedding (𝓡 3) (sphere (0 : EuclideanSpace ℝ (Fin 4)) 1)}
    {Φ : SolidTorus → sphere (0 : EuclideanSpace ℝ (Fin 4)) 1} (h : IsSolidTorusNeighborhood K Φ)
    (h₁ : IsZero ((reducedSingularHomologyFunctor (ModuleCat.of ℤ ℤ) 1).obj
      (TopCat.of (sphere (0 : EuclideanSpace ℝ (Fin 4)) 1))))
    (h₂ : IsZero ((reducedSingularHomologyFunctor (ModuleCat.of ℤ ℤ) 2).obj
      (TopCat.of (sphere (0 : EuclideanSpace ℝ (Fin 4)) 1))))
    {Y : Type u} [TopologicalSpace Y]
    (F : DehnFilling h (h.preferredFramedBoundaryTorus h₁ h₂).longitude Y)
    (e : Y ≃ₜ Circle × sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    SmoothEmbedding.SmoothAmbientIsotopic K unknot :=
  gabaiPropertyRTheorem_iff.1 hG K Φ h h₁ h₂ Y F ⟨e⟩

end TauCeti
