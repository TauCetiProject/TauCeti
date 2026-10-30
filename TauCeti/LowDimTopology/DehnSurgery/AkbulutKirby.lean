/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Sphere
public import TauCeti.Geometry.Manifold.SmoothEmbedding.Concordance
public import TauCeti.KnotTheory.SmoothCircle
public import TauCeti.LowDimTopology.DehnSurgery.Orientation
public import TauCeti.LowDimTopology.DehnSurgery.SeifertFraming

/-!
# The Akbulut–Kirby conjecture on `0`-surgery and concordance

Akbulut and Kirby conjectured that a knot in `S³` is determined up to concordance by its
`0`-surgery: if the `0`-framed surgeries on two knots give the same `3`-manifold, then the knots
are concordant (Kirby's problem 1.19). Yasui disproved it, constructing knots with the same
`0`-surgery that are not concordant for any choice of orientations.

The conjecture is recorded here as a proposition, `TauCeti.AkbulutKirbyConjecture`, about the
knots of `TauCeti.SmoothCircleEmbedding` in the unit sphere `S³` of `ℝ⁴`, and Yasui's theorem as
its negation, `TauCeti.YasuiTheorem`; neither is proved.

* **The `0`-surgery** on a knot `K` with solid torus neighbourhood `Φ` is a Dehn filling
  (`TauCeti.DehnFilling`) of the exterior of `K` along the longitude of the preferred framing
  (`TauCeti.IsSolidTorusNeighborhood.preferredFramedBoundaryTorus`), the longitude that is
  null-homologous in the knot complement.
* **"The same `3`-manifold"** means an orientation-preserving homeomorphism. The filled spaces
  are topological `3`-manifolds, oriented by homological orientations
  (`TauCeti.HomologicalOrientation`) compatible with one orientation of `S³` on the open exteriors
  (`TauCeti.DehnFilling.IsOrientationCompatible`). Orientations matter: the `0`-surgeries on a knot
  and on its mirror image are homeomorphic by an orientation-reversing map, while the
  right-handed trefoil and its mirror image are not concordant, as their signatures differ.
  The sphere `S³` is simply connected (`TauCeti.simplyConnectedSpace_sphere_euclideanSpace`), so
  it has orientations (`TauCeti.HomologicalOrientation.nonempty_of_simplyConnectedSpace`); on a
  connected filled space with nonempty open exterior (always the case for a knot in `S³`) the
  compatible orientation is unique (`TauCeti.DehnFilling.IsOrientationCompatible.unique`).
* **Concordance** is smooth concordance of the parametrized knots
  (`TauCeti.SmoothEmbedding.Concordant`), and the conclusion allows reversing the orientation of
  one knot (`TauCeti.SmoothCircleEmbedding.reverse`). The `0`-surgery does not see the orientation
  of the knot, and there are knots that are not concordant to their reverses (Livingston), so a
  conclusion about oriented concordance would fail for a knot and its reverse.

## Main definitions

* `TauCeti.AkbulutKirbyConjecture`: knots in `S³` with orientation-preservingly homeomorphic
  `0`-surgeries are smoothly concordant, up to orientation.
* `TauCeti.YasuiTheorem`: the Akbulut–Kirby conjecture is false.

## Main results

* `TauCeti.AkbulutKirbyConjecture.concordant_or_concordant_reverse`: applying the conjecture.
* `TauCeti.yasuiTheorem_iff`: Yasui's theorem spelled out, as the existence of two knots with
  orientation-preservingly homeomorphic `0`-surgeries that are not concordant for any orientations.

## References

* R. Kirby (ed.), *Problems in Low-Dimensional Topology*, Problem 1.19, in *Geometric Topology*,
  AMS/IP Stud. Adv. Math. 2.2 (1997).
* K. Yasui, *Corks, exotic 4-manifolds and knot concordance*, arXiv:1505.02551 (2015).
* C. Livingston, *Knots which are not concordant to their reverses*, Quart. J. Math. Oxford
  Ser. (2) 34 (1983), 323–328.
* D. Rolfsen, *Knots and Links*, Publish or Perish (1976), Chapter 9 (Dehn surgery and the
  `0`-framing).
-/

public section

open CategoryTheory Limits Metric Topology
open scoped Manifold

namespace TauCeti

/-- **The Akbulut–Kirby conjecture**, Kirby's problem 1.19: if the `0`-surgeries on two knots
`K K' : S¹ → S³` are homeomorphic by an orientation-preserving homeomorphism, then `K` is smoothly
concordant to `K'` or to its reverse.

The `0`-surgery on `K`, for a solid torus neighbourhood `Φ`, is a Dehn filling `F` of its exterior
along the longitude of the preferred framing
(`TauCeti.IsSolidTorusNeighborhood.preferredFramedBoundaryTorus`), defined because the reduced
integral homology of `S³` vanishes in degrees `1` and `2`
(`TauCeti.isZero_reducedSingularHomologyFunctor_one_sphere_euclideanSpace_fin_four` and
`TauCeti.isZero_reducedSingularHomologyFunctor_two_sphere_euclideanSpace_fin_four`). The filled
spaces `Y`, `Y'` are topological `3`-manifolds oriented by the orientations `oY`, `oY'` compatible
with an orientation `o` of `S³`, and the homeomorphism `e : Y ≃ₜ Y'` preserves orientation when it
pulls `oY'` back to `oY`. Yasui proved that the conjecture is false (`TauCeti.YasuiTheorem`). -/
def AkbulutKirbyConjecture : Prop :=
  ∀ (o : HomologicalOrientation (sphere (0 : EuclideanSpace ℝ (Fin 4)) 1)
      (EuclideanSpace ℝ (Fin 3)) 3)
    (K K' : SmoothCircleEmbedding (𝓡 3) (sphere (0 : EuclideanSpace ℝ (Fin 4)) 1))
    (Φ Φ' : SolidTorus → sphere (0 : EuclideanSpace ℝ (Fin 4)) 1)
    (h : IsSolidTorusNeighborhood K Φ) (h' : IsSolidTorusNeighborhood K' Φ')
    (Y Y' : Type) [TopologicalSpace Y] [T2Space Y] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) Y]
    [TopologicalSpace Y'] [T2Space Y'] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) Y']
    (F : DehnFilling h
      (h.preferredFramedBoundaryTorus
        (isZero_reducedSingularHomologyFunctor_one_sphere_euclideanSpace_fin_four _)
        (isZero_reducedSingularHomologyFunctor_two_sphere_euclideanSpace_fin_four _)).longitude Y)
    (F' : DehnFilling h'
      (h'.preferredFramedBoundaryTorus
        (isZero_reducedSingularHomologyFunctor_one_sphere_euclideanSpace_fin_four _)
        (isZero_reducedSingularHomologyFunctor_two_sphere_euclideanSpace_fin_four _)).longitude Y')
    (oY : HomologicalOrientation Y (EuclideanSpace ℝ (Fin 3)) 3)
    (oY' : HomologicalOrientation Y' (EuclideanSpace ℝ (Fin 3)) 3) (e : Y ≃ₜ Y'),
    F.IsOrientationCompatible o oY → F'.IsOrientationCompatible o oY' →
      oY'.comap e.isOpenEmbedding = oY →
      SmoothEmbedding.Concordant K K' ∨ SmoothEmbedding.Concordant K K'.reverse

/-- **Yasui's theorem**: the Akbulut–Kirby conjecture is false. There are knots in `S³` whose
`0`-surgeries are homeomorphic by an orientation-preserving homeomorphism but which are not
smoothly concordant, even after reversing the orientation of one of them
(`TauCeti.yasuiTheorem_iff`). -/
def YasuiTheorem : Prop :=
  ¬ AkbulutKirbyConjecture

/-- Applying the Akbulut–Kirby conjecture: knots in `S³` whose `0`-surgeries, oriented compatibly
with one orientation of `S³`, are homeomorphic by an orientation-preserving homeomorphism are
smoothly concordant up to orientation. The `0`-surgeries are read in the preferred framing defined
from any proofs that the reduced integral homology of `S³` vanishes in degrees `1` and `2`. -/
theorem AkbulutKirbyConjecture.concordant_or_concordant_reverse (hAK : AkbulutKirbyConjecture)
    (o : HomologicalOrientation (sphere (0 : EuclideanSpace ℝ (Fin 4)) 1)
      (EuclideanSpace ℝ (Fin 3)) 3)
    {K K' : SmoothCircleEmbedding (𝓡 3) (sphere (0 : EuclideanSpace ℝ (Fin 4)) 1)}
    {Φ Φ' : SolidTorus → sphere (0 : EuclideanSpace ℝ (Fin 4)) 1}
    (h : IsSolidTorusNeighborhood K Φ) (h' : IsSolidTorusNeighborhood K' Φ')
    (h₁ : IsZero ((reducedSingularHomologyFunctor (ModuleCat.of ℤ ℤ) 1).obj
      (TopCat.of (sphere (0 : EuclideanSpace ℝ (Fin 4)) 1))))
    (h₂ : IsZero ((reducedSingularHomologyFunctor (ModuleCat.of ℤ ℤ) 2).obj
      (TopCat.of (sphere (0 : EuclideanSpace ℝ (Fin 4)) 1))))
    {Y Y' : Type} [TopologicalSpace Y] [T2Space Y] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) Y]
    [TopologicalSpace Y'] [T2Space Y'] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) Y']
    (F : DehnFilling h (h.preferredFramedBoundaryTorus h₁ h₂).longitude Y)
    (F' : DehnFilling h' (h'.preferredFramedBoundaryTorus h₁ h₂).longitude Y')
    {oY : HomologicalOrientation Y (EuclideanSpace ℝ (Fin 3)) 3}
    {oY' : HomologicalOrientation Y' (EuclideanSpace ℝ (Fin 3)) 3}
    (hF : F.IsOrientationCompatible o oY) (hF' : F'.IsOrientationCompatible o oY')
    (e : Y ≃ₜ Y') (he : oY'.comap e.isOpenEmbedding = oY) :
    SmoothEmbedding.Concordant K K' ∨ SmoothEmbedding.Concordant K K'.reverse :=
  hAK o K K' Φ Φ' h h' Y Y' F F' oY oY' e hF hF' he

/-- **Yasui's theorem spelled out**: there are knots `K K' : S¹ → S³` with `0`-surgeries `Y`, `Y'`,
oriented compatibly with an orientation of `S³`, and an orientation-preserving homeomorphism
`Y ≃ₜ Y'`, such that `K` is smoothly concordant neither to `K'` nor to its reverse. -/
theorem yasuiTheorem_iff :
    YasuiTheorem ↔
      ∃ (o : HomologicalOrientation (sphere (0 : EuclideanSpace ℝ (Fin 4)) 1)
          (EuclideanSpace ℝ (Fin 3)) 3)
        (K K' : SmoothCircleEmbedding (𝓡 3) (sphere (0 : EuclideanSpace ℝ (Fin 4)) 1))
        (Φ Φ' : SolidTorus → sphere (0 : EuclideanSpace ℝ (Fin 4)) 1)
        (h : IsSolidTorusNeighborhood K Φ) (h' : IsSolidTorusNeighborhood K' Φ')
        (Y Y' : Type) (_ : TopologicalSpace Y) (_ : T2Space Y)
        (_ : ChartedSpace (EuclideanSpace ℝ (Fin 3)) Y)
        (_ : TopologicalSpace Y') (_ : T2Space Y')
        (_ : ChartedSpace (EuclideanSpace ℝ (Fin 3)) Y')
        (F : DehnFilling h
          (h.preferredFramedBoundaryTorus
            (isZero_reducedSingularHomologyFunctor_one_sphere_euclideanSpace_fin_four _)
            (isZero_reducedSingularHomologyFunctor_two_sphere_euclideanSpace_fin_four _)).longitude
          Y)
        (F' : DehnFilling h'
          (h'.preferredFramedBoundaryTorus
            (isZero_reducedSingularHomologyFunctor_one_sphere_euclideanSpace_fin_four _)
            (isZero_reducedSingularHomologyFunctor_two_sphere_euclideanSpace_fin_four _)).longitude
          Y')
        (oY : HomologicalOrientation Y (EuclideanSpace ℝ (Fin 3)) 3)
        (oY' : HomologicalOrientation Y' (EuclideanSpace ℝ (Fin 3)) 3) (e : Y ≃ₜ Y'),
        F.IsOrientationCompatible o oY ∧ F'.IsOrientationCompatible o oY' ∧
          oY'.comap e.isOpenEmbedding = oY ∧
          ¬ SmoothEmbedding.Concordant K K' ∧ ¬ SmoothEmbedding.Concordant K K'.reverse := by
  simp only [YasuiTheorem, AkbulutKirbyConjecture, not_forall, not_or, exists_prop]

end TauCeti
