/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Hyperbolic
public import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Volume

/-!
# Hyperbolic metrics of finite volume

A complete hyperbolic manifold need not be compact: the complement of a hyperbolic knot in `S³`,
and more generally the interior of every non-Seifert-fibred piece of the geometric (JSJ)
decomposition of a closed orientable irreducible 3-manifold, carries a complete hyperbolic metric
of *finite volume*, with cusps at its ends. This is the notion of hyperbolicity in the
geometrization theorem. This file records it, for the Riemannian volume measure
`TauCeti.riemannianVolume` of the bundled metric.

On a compact manifold the Riemannian volume is a finite measure, so there the condition is
automatic, and a compact manifold is hyperbolic of finite volume exactly when it is hyperbolic.

## Main definitions

* `TauCeti.HyperbolicMetric.HasFiniteVolume`: the Riemannian volume of a hyperbolic metric is a
  finite measure.
* `TauCeti.IsFiniteVolumeHyperbolic`: a manifold carries a hyperbolic metric of finite volume.

## Main results

* `TauCeti.isFiniteVolumeHyperbolic_iff`: the definition, for any Borel measurable structure.
* `TauCeti.HyperbolicMetric.hasFiniteVolume_of_compactSpace`: on a compact manifold every
  hyperbolic metric has finite volume.
* `TauCeti.isFiniteVolumeHyperbolic_iff_isHyperbolic`: so a compact manifold is hyperbolic of
  finite volume exactly when it is hyperbolic.

## References

* W. P. Thurston, *Three-dimensional manifolds, Kleinian groups and hyperbolic geometry*, Bull.
  Amer. Math. Soc. (N.S.) 6 (1982), 357–381.
* J. G. Ratcliffe, *Foundations of Hyperbolic Manifolds*, 3rd ed., Graduate Texts in
  Mathematics 149, Springer (2019), Chapter 10 (hyperbolic 3-manifolds).
-/

public section

open Bundle MeasureTheory
open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T3Space M] [PreconnectedSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [LindelofSpace M]

namespace HyperbolicMetric

variable [MeasurableSpace M] [BorelSpace M]

/-- A hyperbolic metric **has finite volume** when its Riemannian volume measure is finite. -/
def HasFiniteVolume (g : HyperbolicMetric (I := I) (M := M)) : Prop :=
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.metric.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
    IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle
      (IB := I) (n := ∞) (F := E) (V := fun x : M ↦ TangentSpace I x)
  IsFiniteMeasure (riemannianVolume I M)

/-- The defining property of `TauCeti.HyperbolicMetric.HasFiniteVolume`. -/
theorem hasFiniteVolume_iff (g : HyperbolicMetric (I := I) (M := M)) :
    g.HasFiniteVolume ↔
      letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.metric.toRiemannianMetric⟩
      letI : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
        IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle
          (IB := I) (n := ∞) (F := E) (V := fun x : M ↦ TangentSpace I x)
      IsFiniteMeasure (riemannianVolume I M) :=
  Iff.rfl

/-- On a compact manifold every hyperbolic metric has finite volume, since the Riemannian volume
is locally finite. -/
theorem hasFiniteVolume_of_compactSpace [CompactSpace M] (g : HyperbolicMetric (I := I) (M := M)) :
    g.HasFiniteVolume := by
  let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.metric.toRiemannianMetric⟩
  let _ : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
    IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle
      (IB := I) (n := ∞) (F := E) (V := fun x : M ↦ TangentSpace I x)
  exact (inferInstance : IsFiniteMeasure (riemannianVolume I M))

end HyperbolicMetric

variable (I M) in
/-- A manifold is **hyperbolic of finite volume** when it carries a complete smooth metric of
constant curvature `-1` whose Riemannian volume is finite. The volume is taken for the Borel
`σ`-algebra; `TauCeti.isFiniteVolumeHyperbolic_iff` restates this for any Borel measurable
structure on `M`. -/
def IsFiniteVolumeHyperbolic : Prop :=
  letI : MeasurableSpace M := borel M
  haveI : BorelSpace M := ⟨rfl⟩
  ∃ g : HyperbolicMetric (I := I) (M := M), g.HasFiniteVolume

/-- A manifold is hyperbolic of finite volume exactly when it carries a hyperbolic metric of
finite volume, computed for any Borel measurable structure. -/
theorem isFiniteVolumeHyperbolic_iff [MeasurableSpace M] [BorelSpace M] :
    IsFiniteVolumeHyperbolic I M ↔ ∃ g : HyperbolicMetric (I := I) (M := M), g.HasFiniteVolume := by
  obtain rfl := BorelSpace.measurable_eq (α := M)
  exact Iff.rfl

/-- A manifold that is hyperbolic of finite volume is hyperbolic. -/
theorem IsFiniteVolumeHyperbolic.isHyperbolic (h : IsFiniteVolumeHyperbolic I M) :
    IsHyperbolic (I := I) (M := M) :=
  let ⟨g, _⟩ := h
  isHyperbolic_iff.2 ⟨g⟩

/-- A compact manifold is hyperbolic of finite volume exactly when it is hyperbolic: on a compact
manifold every hyperbolic metric has finite volume. -/
theorem isFiniteVolumeHyperbolic_iff_isHyperbolic [CompactSpace M] :
    IsFiniteVolumeHyperbolic I M ↔ IsHyperbolic (I := I) (M := M) := by
  let _ : MeasurableSpace M := borel M
  have : BorelSpace M := ⟨rfl⟩
  rw [isFiniteVolumeHyperbolic_iff, isHyperbolic_iff]
  exact ⟨fun ⟨g, _⟩ ↦ ⟨g⟩, fun ⟨g⟩ ↦ ⟨g, g.hasFiniteVolume_of_compactSpace⟩⟩

end TauCeti
