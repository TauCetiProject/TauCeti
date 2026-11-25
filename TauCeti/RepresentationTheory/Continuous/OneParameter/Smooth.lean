/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Semigroups.Group.SmoothVectors
public import TauCeti.Geometry.Manifold.Algebra.TypeTags
public import TauCeti.RepresentationTheory.Continuous.LieSmoothVector
public import TauCeti.RepresentationTheory.Continuous.OneParameter.Basic

/-!
# Smooth vectors of a representation of the real line

Let `π` be a continuous representation of the real Lie group `(ℝ, +)`, written `Multiplicative ℝ`,
on a real or complex Banach space `V`, with continuous orbits. Then `π` has two notions of smooth
vector:

* the Lie-group notion `ContRepresentation.lieSmoothVectors 𝓘(ℝ) π`, the vectors whose orbit map
  `Multiplicative ℝ → V` is smooth;
* the semigroup notion `StronglyContinuousSemigroup.smoothVectors` of the forward semigroup
  `t ≥ 0 ↦ π t` of the C₀-group `ContRepresentation.toStronglyContinuousGroup π`, the vectors in
  every iterated domain of its generator.

They coincide, after restricting the scalars of the first to `ℝ`. The charts of
`Multiplicative ℝ` are those of `ℝ`, so a Lie-smooth vector is one whose orbit `t ↦ π t v` is
smooth on `ℝ`, and
`TauCeti.Semigroups.StronglyContinuousGroup.isSmoothVector_toSemigroup_iff_contDiff` identifies
these with the smooth vectors of the forward semigroup.

## Main results

* `ContRepresentation.isLieSmoothVector_iff_contDiff`: a vector is Lie-smooth exactly when its
  orbit `t ↦ π (ofAdd t) v` is smooth on `ℝ`.
* `ContRepresentation.isLieSmoothVector_iff_isSmoothVector_toSemigroup`: Lie-smooth vectors are
  the smooth vectors of the forward semigroup.
* `ContRepresentation.restrictScalars_lieSmoothVectors_eq_smoothVectors`: the same equality of
  real submodules.

## References

* J. Bernstein and B. Krötz, *Smooth Fréchet globalizations of Harish-Chandra modules*, Israel J.
  Math. 199 (2014), §2.
* K.-J. Engel and R. Nagel, *One-Parameter Semigroups for Linear Evolution Equations*, Springer
  GTM 194 (2000), Lemma II.1.3.
-/

public section

open TauCeti.Semigroups
open scoped ContDiff Manifold

namespace ContRepresentation

/-- A vector of a continuous representation of `Multiplicative ℝ` is Lie-smooth exactly when its
orbit `t ↦ π (ofAdd t) v` is smooth on `ℝ`: the type tag keeps the charts of `ℝ`. -/
theorem isLieSmoothVector_iff_contDiff {R V : Type*} [Ring R] [NormedAddCommGroup V]
    [NormedSpace ℝ V] [Module R V] (π : ContRepresentation R (Multiplicative ℝ) V) (v : V) :
    IsLieSmoothVector 𝓘(ℝ) π v ↔ ContDiff ℝ ∞ fun t : ℝ => π (Multiplicative.ofAdd t) v :=
  (isLieSmoothVector_iff 𝓘(ℝ) π).trans contMDiff_iff_contDiff

variable {𝕜 V : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [NormedSpace 𝕜 V] [NormedSpace ℝ V]
  [IsScalarTower ℝ 𝕜 V] [CompleteSpace V]

/-- **Lie-smooth vectors of a representation of `ℝ` are the smooth vectors of its forward
semigroup.** -/
theorem isLieSmoothVector_iff_isSmoothVector_toSemigroup
    (π : ContRepresentation 𝕜 (Multiplicative ℝ) V) (hπ : ∀ v, Continuous fun g => π g v)
    (v : V) :
    IsLieSmoothVector 𝓘(ℝ) π v ↔ (π.toStronglyContinuousGroup hπ).toSemigroup.IsSmoothVector v := by
  rw [isLieSmoothVector_iff_contDiff,
    StronglyContinuousGroup.isSmoothVector_toSemigroup_iff_contDiff]
  simp only [toStronglyContinuousGroup_apply]

/-- **The smooth vectors of a representation of `ℝ`, as real submodules.** After restricting
scalars to `ℝ`, the Lie-smooth vectors are the smooth vectors of the forward semigroup
`t ≥ 0 ↦ π t`. -/
theorem restrictScalars_lieSmoothVectors_eq_smoothVectors
    (π : ContRepresentation 𝕜 (Multiplicative ℝ) V) (hπ : ∀ v, Continuous fun g => π g v) :
    (lieSmoothVectors 𝓘(ℝ) π).restrictScalars ℝ =
      (π.toStronglyContinuousGroup hπ).toSemigroup.smoothVectors :=
  Submodule.ext fun v => by
    rw [Submodule.restrictScalars_mem, mem_lieSmoothVectors,
      StronglyContinuousSemigroup.mem_smoothVectors,
      isLieSmoothVector_iff_isSmoothVector_toSemigroup π hπ]

end ContRepresentation
