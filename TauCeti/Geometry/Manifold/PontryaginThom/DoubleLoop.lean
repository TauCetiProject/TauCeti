/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Homotopy.LoopSpace.Retract
public import TauCeti.Geometry.Manifold.PontryaginThom.Degree

/-!
# Double loops of a sphere meeting a framed submanifold once

Let `τ : S × ℝᵏ → Q` be a framed tube around a compact submanifold `f : S → Q` of codimension
`k ≥ 2`, and let `σ : Sᵏ → Q` be a sphere meeting the core `f(S)` in exactly one point `x`, at
which the composite of `σ` with the Pontryagin–Thom collapse `c : Q → Sᵏ` is a local
homeomorphism (for a smooth sphere transverse to the core, by the inverse function theorem in the
normal coordinate of the tube). Then `c ∘ σ` has degree `±1`
(`TauCeti.IsFramedTube.bijective_singularHomologyMap_pontryaginThomSphereMap_comp_sphere`), so up
to rotations of the sphere `c` is a left homotopy inverse of `σ`, and the map of Moore double loop
spaces `Ω²σ : Ω²Sᵏ → Ω²Q` is injective on singular homology, in every degree, with any
coefficients and at every base point (`TauCeti.IsFramedTube.injective_singularHomologyMap_map_map`).

This is Lemma 7.6 of Barraud, Damian, Humilière and Oancea, in the proof of their Theorem G on
hypersurfaces knotted with spheres. There `σ` embeds `Sᵏ` in a closed manifold `Q`, meeting
transversely and in a single point a closed submanifold `Y` with trivial normal bundle, and the
lemma asserts that a class `j_!β = (Ω²σ)_* j_!α₀ ∈ H_*(Ω²Q; ℤ)` is not torsion whenever
`j_!α₀ ∈ H_*(Ω²Sᵏ; ℤ)` is not. With integer coefficients this follows from the injectivity proved
here, by `Function.Injective.isOfFinAddOrder_iff`.

## Main results

* `TauCeti.IsFramedTube.injective_singularHomologyMap_map_map`: the double loops of a sphere
  meeting the core of a framed tube once are injective on singular homology.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §7, Lemma 7.6.
-/

public section

open Metric Set

namespace TauCeti.IsFramedTube

variable {S Q : Type} [TopologicalSpace S] [CompactSpace S] [TopologicalSpace Q] [T2Space Q]
  {n : ℕ} {f : S → Q} {τ : S × (Fin (n + 2) → ℝ) → Q}

/-- **Lemma 7.6 of Barraud–Damian–Humilière–Oancea.** Let `σ : Sⁿ⁺² → Q` meet the core of a framed
tube with fibre `ℝⁿ⁺²` in the single point `x`, at which the composite of `σ` with the
Pontryagin–Thom collapse onto `Sⁿ⁺²` is a local homeomorphism. Then, at every base point `y` of the
sphere, the map `Ω²σ : Ω²Sⁿ⁺² → Ω²Q` of Moore double loop spaces is injective on singular homology
in every degree and with any coefficients. -/
theorem injective_singularHomologyMap_map_map (h : IsFramedTube f τ)
    (s₀ : sphere (0 : EuclideanSpace ℝ (Fin (n + 3))) 1)
    (σ : C(sphere (0 : EuclideanSpace ℝ (Fin (n + 3))) 1, Q)) {x : sphere (0 : EuclideanSpace ℝ
      (Fin (n + 3))) 1} (hx : σ ⁻¹' range f = {x})
    (hσ : IsLocalHomeomorphOn (pontryaginThomSphereMap h.isOpenEmbedding s₀ ∘ σ) {x})
    {y : sphere (0 : EuclideanSpace ℝ (Fin (n + 3))) 1} {q : Q} (hy : σ y = q)
    (R : Type) [Ring R] (m : ℕ) :
    Function.Injective (ContinuousMap.singularHomologyMap R m
      (MooreLoopSpace.map (MooreLoopSpace.map σ hy : C(MooreLoopSpace _ y, MooreLoopSpace Q q))
        (map_one (MooreLoopSpace.map σ hy)) :
        C(MooreLoopSpace (MooreLoopSpace _ y) 1, MooreLoopSpace (MooreLoopSpace Q q) 1))) :=
  MooreLoopSpace.injective_singularHomologyMap_map_map_of_surjective_singularHomologyMap hy
    (h.bijective_singularHomologyMap_pontryaginThomSphereMap_comp_sphere s₀ (by omega) σ hx hσ).2
    R m

end TauCeti.IsFramedTube
