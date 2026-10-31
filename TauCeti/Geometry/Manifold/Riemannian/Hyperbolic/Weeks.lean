/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Orientation.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Hyperbolic.Volume
public import TauCeti.LowDimTopology.DehnSurgery.Link.Weeks

/-!
# The Weeks manifold has the smallest volume

Among closed orientable hyperbolic `3`-manifolds, the **Weeks manifold**, the surgery on the
Whitehead link with coefficients `5` and `5 / 2` (`TauCeti.IsWeeksManifold`), has the smallest
volume, about `0.9427`, and it is the only one of that volume. Kirby's problem 3.60 asked for the
smallest volume; the answer is the theorem of Gabai, Meyerhoff and Milley. This file states it as
the proposition `TauCeti.GabaiMeyerhoffMilleyTheorem`, in two parts:

* the Weeks manifold is a closed hyperbolic `3`-manifold: some compact connected smooth
  `3`-manifold without boundary which is a Weeks manifold carries a hyperbolic metric
  (`TauCeti.HyperbolicMetric`);
* for every smooth Weeks manifold `W` with a hyperbolic metric `g_W`, and every closed orientable
  hyperbolic `3`-manifold `M` with a hyperbolic metric `g`, the volume of `g_W` is at most that
  of `g` (`TauCeti.hypVolumeOfMetric`), and equality forces `M` to be homeomorphic to `W`.

Volumes are those of the given metrics, so the statement does not rely on Mostow rigidity, which
is only assumed in this library (`TauCeti.IsMostowRigid`); by Mostow rigidity they are invariants
of the manifolds. Being a Weeks manifold is a topological property of `W`, and so is the
conclusion `M ≃ₜ W`; in dimension three homeomorphic smooth manifolds are diffeomorphic (Moise), so
nothing is lost by not asking for a diffeomorphism. As in the theorem of Gabai, Meyerhoff and
Milley, `M` is assumed orientable (`TauCeti.Orientable`).

The theorem is stated, not proved.

## Main definitions

* `TauCeti.GabaiMeyerhoffMilleyTheorem`: the Weeks manifold is the unique closed orientable
  hyperbolic `3`-manifold of smallest volume.

## Main results

* `TauCeti.GabaiMeyerhoffMilleyTheorem.exists_isWeeksManifold`: applying the first part, a closed
  hyperbolic Weeks manifold exists.
* `TauCeti.GabaiMeyerhoffMilleyTheorem.hypVolumeOfMetric_le`: applying the inequality.
* `TauCeti.GabaiMeyerhoffMilleyTheorem.nonempty_homeomorph_of_hypVolumeOfMetric_eq`: applying the
  uniqueness.

## References

* R. Kirby (ed.), *Problems in Low-Dimensional Topology*, Problem 3.60, in *Geometric Topology*,
  AMS/IP Stud. Adv. Math. 2.2 (1997).
* D. Gabai, R. Meyerhoff, P. Milley, *Minimum volume cusped hyperbolic three-manifolds*, J. Amer.
  Math. Soc. 22 (2009), 1157–1215.
* P. Milley, *Minimum volume hyperbolic 3-manifolds*, J. Topol. 2 (2009), 181–192.
* J. Weeks, *Hyperbolic structures on three-manifolds*, Ph.D. thesis, Princeton University
  (1985).
-/

public section

open scoped Manifold ContDiff

universe u

namespace TauCeti

/-- **The theorem of Gabai, Meyerhoff and Milley** (Kirby's problem 3.60): the Weeks manifold is
the unique closed orientable hyperbolic `3`-manifold of smallest volume.

First, some compact connected smooth `3`-manifold without boundary which is a Weeks manifold
(`TauCeti.IsWeeksManifold`) carries a hyperbolic metric. Second, for every such Weeks manifold `W`
with a hyperbolic metric `gW` and every compact connected orientable smooth `3`-manifold `M`
without boundary with a hyperbolic metric `g`, the volume of `gW` is at most the volume of `g`,
with equality only if `M` is homeomorphic to `W`. -/
def GabaiMeyerhoffMilleyTheorem : Prop :=
  (∃ (W : Type) (_ : MetricSpace W) (_ : ChartedSpace (EuclideanSpace ℝ (Fin 3)) W)
      (_ : IsManifold (𝓡 3) ∞ W) (_ : CompactSpace W) (_ : ConnectedSpace W),
      IsWeeksManifold W ∧ IsHyperbolic (I := 𝓡 3) (M := W)) ∧
    ∀ (W : Type u) [MetricSpace W] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) W]
      [IsManifold (𝓡 3) ∞ W] [CompactSpace W] [ConnectedSpace W] [MeasurableSpace W]
      [BorelSpace W]
      (M : Type u) [MetricSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [IsManifold (𝓡 3) ∞ M] [CompactSpace M] [ConnectedSpace M] [Orientable (𝓡 3) M]
      [MeasurableSpace M] [BorelSpace M],
      IsWeeksManifold W → ∀ (gW : HyperbolicMetric (I := 𝓡 3) (M := W))
        (g : HyperbolicMetric (I := 𝓡 3) (M := M)),
        hypVolumeOfMetric gW ≤ hypVolumeOfMetric g ∧
          (hypVolumeOfMetric g = hypVolumeOfMetric gW → Nonempty (M ≃ₜ W))

namespace GabaiMeyerhoffMilleyTheorem

variable (hGMM : GabaiMeyerhoffMilleyTheorem.{u})
include hGMM

/-- Applying the theorem of Gabai, Meyerhoff and Milley: some compact connected smooth
`3`-manifold without boundary which is a Weeks manifold carries a hyperbolic metric. -/
theorem exists_isWeeksManifold :
    ∃ (W : Type) (_ : MetricSpace W) (_ : ChartedSpace (EuclideanSpace ℝ (Fin 3)) W)
      (_ : IsManifold (𝓡 3) ∞ W) (_ : CompactSpace W) (_ : ConnectedSpace W),
      IsWeeksManifold W ∧ IsHyperbolic (I := 𝓡 3) (M := W) :=
  hGMM.1

variable {W : Type u} [MetricSpace W] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) W]
  [IsManifold (𝓡 3) ∞ W] [CompactSpace W] [ConnectedSpace W] [MeasurableSpace W] [BorelSpace W]
  {M : Type u} [MetricSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [CompactSpace M] [ConnectedSpace M] [Orientable (𝓡 3) M]
  [MeasurableSpace M] [BorelSpace M]

/-- Applying the theorem of Gabai, Meyerhoff and Milley: a hyperbolic metric on a Weeks manifold
has volume at most that of any hyperbolic metric on a closed orientable `3`-manifold. -/
theorem hypVolumeOfMetric_le (hW : IsWeeksManifold W) (gW : HyperbolicMetric (I := 𝓡 3) (M := W))
    (g : HyperbolicMetric (I := 𝓡 3) (M := M)) :
    hypVolumeOfMetric gW ≤ hypVolumeOfMetric g :=
  (hGMM.2 W M hW gW g).1

/-- Applying the theorem of Gabai, Meyerhoff and Milley: a closed orientable hyperbolic
`3`-manifold with the volume of a hyperbolic Weeks manifold is homeomorphic to it. -/
theorem nonempty_homeomorph_of_hypVolumeOfMetric_eq (hW : IsWeeksManifold W)
    (gW : HyperbolicMetric (I := 𝓡 3) (M := W)) (g : HyperbolicMetric (I := 𝓡 3) (M := M))
    (h : hypVolumeOfMetric g = hypVolumeOfMetric gW) : Nonempty (M ≃ₜ W) :=
  (hGMM.2 W M hW gW g).2 h

end GabaiMeyerhoffMilleyTheorem

end TauCeti
