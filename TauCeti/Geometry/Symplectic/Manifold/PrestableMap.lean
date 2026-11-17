/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.NodalGluing.Basic
public import TauCeti.Geometry.Manifold.Complex.AlmostComplexStructure
import TauCeti.Geometry.Manifold.Complex.Analytic
import TauCeti.Geometry.Manifold.ContMDiff.RestrictScalars
import TauCeti.Geometry.Manifold.ModelWithCorners.RestrictScalars.Basic

/-!
# Prestable pseudoholomorphic maps on nodal curves

Let `X` be a manifold with a smooth almost complex structure `J`, and let a nodal curve be
presented by flag-pair data `d` on normalization components `C i`, each a complex curve given by a
complex atlas. A **prestable map** from the nodal curve to `X` is a map `u : (Σ i, C i) → X` from
the normalization whose restriction to every component is smooth and pseudoholomorphic, for the
almost complex structure `SmoothAlmostComplexStructure.ofComplexManifold ℂ (C i)` of the
component, and which takes the same value at the two points of every flag pair
(`TauCeti.IsPrestableMap`). Smoothness is a separate condition, since the pseudoholomorphicity
predicate `IsPseudoholomorphic` is a derivative-level condition carrying no elliptic regularity.
No stability, taming form, compactness of `X` or genericity of `J` is part of the definition:
unmarked spheres and tori, constant or not, are allowed as components.

A prestable map descends to a continuous map on the glued curve
(`TauCeti.IsPrestableMap.continuous_lift`). Constant maps are prestable, and when `X` is a complex
manifold with its own almost complex structure, the prestable maps are exactly the maps that are
holomorphic on every component and match at the nodes
(`TauCeti.isPrestableMap_ofComplexManifold_iff`).

The automorphisms of a prestable map `u` on a curve with marking `m` are the automorphisms of the
marked nodal curve intertwining it: the isotropy group
`TauCeti.NodalGluing.AuxiliaryAut.isotropy 𝓘(ℂ) ∞ m u` of
`TauCeti.AlgebraicGeometry.Curves.NodalGluing.MapGroupoid`, whose results on components where a
map is constant apply to prestable maps. In particular, if the isotropy group of a prestable map is
finite, every component on which it is constant has finitely many biholomorphisms fixing its
special points.

## Main definitions

* `TauCeti.IsPrestableMap J d u`: `u` is a prestable map from the nodal curve presented by `d` to
  the almost complex manifold `(X, J)`.

## Main results

* `TauCeti.IsPrestableMap.continuous_lift`: a prestable map descends to a continuous map on the
  glued curve.
* `TauCeti.isPrestableMap_const`: constant maps are prestable.
* `TauCeti.isPrestableMap_ofComplexManifold_iff`: into a complex manifold, prestable maps are the
  componentwise holomorphic maps matching at the nodes.

## References

* Dusa McDuff and Dietmar Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  AMS Colloquium Publications 52 (2012), §5.1, for stable maps on nodal curves.
* John Pardon, *An algebraic approach to virtual fundamental cycles on moduli spaces of
  pseudo-holomorphic curves*, Geom. Topol. 20 (2016), 779–1034, §9.2.
-/

public section

open scoped Manifold ContDiff TauCeti.ComplexManifold

namespace TauCeti

open NodalGluing

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {X : Type*} [TopologicalSpace X] [ChartedSpace H X]
  [IsManifold I ∞ X] {J : SmoothAlmostComplexStructure I X}
  {ι Flag : Type*} {C : ι → Type*} [∀ i, TopologicalSpace (C i)] [∀ i, ChartedSpace ℂ (C i)]
  [∀ i, IsManifold 𝓘(ℂ) ∞ (C i)] {d : FlagPairData ι Flag C} {u : (Σ i, C i) → X}

variable (J d) in
/-- **A prestable map** from the nodal curve presented by the flag-pair data `d`, with
normalization components the complex curves `C i`, to a manifold `X` with a smooth almost complex
structure `J`: a map `u` from the normalization whose restriction to every component is smooth and
pseudoholomorphic, and which takes the same value at the two points of every flag pair. -/
structure IsPrestableMap (u : (Σ i, C i) → X) : Prop where
  /-- The restriction to every component is smooth. -/
  contMDiff (i : ι) : ContMDiff 𝓘(ℝ, ℂ) I ∞ fun z : C i ↦ u ⟨i, z⟩
  /-- The restriction to every component is pseudoholomorphic. -/
  isPseudoholomorphic (i : ι) :
    IsPseudoholomorphic (SmoothAlmostComplexStructure.ofComplexManifold ℂ (C i)) J
      fun z : C i ↦ u ⟨i, z⟩
  /-- The map takes the same value at the two points of every flag pair. -/
  apply_fstPoint (f : Flag) : u (fstPoint d f) = u (sndPoint d f)

namespace IsPrestableMap

/-- A prestable map is continuous on the normalization. -/
theorem continuous (hu : IsPrestableMap J d u) : Continuous u :=
  continuous_sigma fun i ↦ (hu.isPseudoholomorphic i).continuous

/-- **Descent to the glued curve.** A prestable map descends to a continuous map on the glued
curve. -/
theorem continuous_lift (hu : IsPrestableMap J d u) :
    Continuous (GluedCurve.lift d u hu.apply_fstPoint) :=
  GluedCurve.continuous_lift d u hu.apply_fstPoint hu.continuous

end IsPrestableMap

variable (J d) in
/-- **Constant maps are prestable.** -/
theorem isPrestableMap_const (x : X) : IsPrestableMap J d fun _ ↦ x where
  contMDiff _ := contMDiff_const
  isPseudoholomorphic _ := isPseudoholomorphic_const _ J x
  apply_fstPoint _ := rfl

/-- **Prestable maps into a complex manifold.** For a complex manifold `X` with its almost complex
structure, a map from the normalization of a nodal curve is prestable exactly when it is
holomorphic on every component and takes the same value at the two points of every flag pair. -/
theorem isPrestableMap_ofComplexManifold_iff {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    [CompleteSpace F] {Z : Type*} [TopologicalSpace Z] [ChartedSpace F Z]
    [IsManifold 𝓘(ℂ, F) ∞ Z] {v : (Σ i, C i) → Z} :
    IsPrestableMap (SmoothAlmostComplexStructure.ofComplexManifold F Z) d v ↔
      (∀ i, MDifferentiable 𝓘(ℂ) 𝓘(ℂ, F) fun z : C i ↦ v ⟨i, z⟩) ∧
        ∀ f, v (fstPoint d f) = v (sndPoint d f) := by
  refine ⟨fun hv ↦ ⟨fun i ↦ isPseudoholomorphic_ofComplexManifold_iff.mp (hv.isPseudoholomorphic i),
    hv.apply_fstPoint⟩, fun ⟨hv, hf⟩ ↦ ⟨fun i ↦ ?_,
      fun i ↦ isPseudoholomorphic_ofComplexManifold_iff.mpr (hv i), hf⟩⟩
  simpa only [modelWithCornersSelf_restrictScalars] using
    ((hv i).contMDiff (n := ∞)).restrictScalars ℝ

end TauCeti
