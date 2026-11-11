/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Sphere.PointedMap
public import TauCeti.AlgebraicTopology.Singular.Homotopy.Invariance
public import TauCeti.Topology.PathSpace.Moore.Homotopy

/-!
# Double loops of a homotopy retract

If a pointed map `s : (X, x) → (Q, q)` has a pointed left homotopy inverse `r`, that is,
`r ∘ s ≃ id` relative to `x`, then the map `Ω²s` of Moore double loop spaces is injective on
singular homology in every degree and with any coefficients: by homotopy invariance of the Moore
loop functor (`TauCeti.MooreLoopSpace.homotopicRel_comp_map_id`), `Ω²r ∘ Ω²s` is homotopic to
the identity (`TauCeti.MooreLoopSpace.injective_singularHomologyMap_map_map_of_homotopicRel`).

The case of interest is a sphere. Let `s : Sⁿ⁺² → Q` be a pointed map and `c : Q → Sⁿ⁺²` a
pointed map such that `c ∘ s` has degree `±1`, that is, induces a surjection on
`Hₙ₊₂(Sⁿ⁺²; ℤ) ≅ ℤ`. By Hopf's theorem for pointed self-maps of the sphere,
`(c ∘ s) ∘ (c ∘ s) ≃ id`
(`ContinuousMap.homotopicRel_comp_self_id_of_surjective_singularHomologyMap`), so `(c ∘ s) ∘ c` is
a left homotopy inverse of `s`, and `(Ω²s)_* : H_*(Ω²Sⁿ⁺²) → H_*(Ω²Q)` is injective
(`TauCeti.MooreLoopSpace.injective_singularHomologyMap_map_map_of_surjective_singularHomologyMap`).

This is the homotopy-theoretic part of Lemma 7.6 of Barraud, Damian, Humilière and Oancea. There
`s` embeds `Sᵏ` in a closed manifold `Q`, meeting transversely and in a single point a closed
submanifold `Y` with trivial normal bundle, and `c` is the Pontryagin–Thom collapse of `Q` onto the
fibre sphere of a tubular neighbourhood `Y × Dᵏ`, so that `c ∘ s` has degree one.

## Main results

* `TauCeti.MooreLoopSpace.injective_singularHomologyMap_map_map_of_homotopicRel`: the double loops
  of a map with a pointed left homotopy inverse are injective on singular homology.
* `TauCeti.MooreLoopSpace.injective_singularHomologyMap_map_map_of_surjective_singularHomologyMap`:
  the double loops of a pointed map `s : Sⁿ⁺² → Q` are injective on singular homology when some
  pointed `c : Q → Sⁿ⁺²` makes `c ∘ s` of degree `±1`.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, Lemma 7.6.
-/

public section

open Metric

namespace TauCeti.MooreLoopSpace

universe u

/-- **Double loops of a homotopy retract.** If a pointed map `s : (X, x) → (Q, q)` has a pointed
left inverse `r` up to homotopy relative to `x`, then `Ω²s : Ω²X → Ω²Q`, on Moore double loop
spaces, is injective on singular homology in every degree and with any coefficients. -/
theorem injective_singularHomologyMap_map_map_of_homotopicRel {X Q : Type u} [TopologicalSpace X]
    [TopologicalSpace Q] {x : X} {q : Q} {s : C(X, Q)} {r : C(Q, X)} (hs : s x = q) (hr : r q = x)
    (h : (r.comp s).HomotopicRel (ContinuousMap.id X) {x}) (k : Type u) [Ring k] (m : ℕ) :
    Function.Injective (ContinuousMap.singularHomologyMap k m
      (map (map s hs : C(MooreLoopSpace X x, MooreLoopSpace Q q)) (map_one (map s hs)) :
        C(MooreLoopSpace (MooreLoopSpace X x) 1, MooreLoopSpace (MooreLoopSpace Q q) 1))) :=
  -- `Ω²r ∘ Ω²s` is homotopic to the identity, so `(Ω²s)_*` has a left inverse.
  ContinuousMap.injective_singularHomologyMap_of_homotopic_comp_id k m
    (homotopicRel_comp_map_id (homotopicRel_comp_map_id h hs hr) (map_one (map s hs))
      (map_one (map r hr))).homotopic

/-- **Double loops of a sphere mapping with degree `±1` back onto it.** Let `s : Sⁿ⁺² → Q` and
`c : Q → Sⁿ⁺²` be pointed maps such that `c ∘ s` induces a surjection on `Hₙ₊₂(Sⁿ⁺²; ℤ)`. Then
`Ω²s : Ω²Sⁿ⁺² → Ω²Q`, on Moore double loop spaces, is injective on singular homology in every
degree and with any coefficients. -/
theorem injective_singularHomologyMap_map_map_of_surjective_singularHomologyMap {Q : Type}
    [TopologicalSpace Q] {q : Q} {n : ℕ}
    {s : C(sphere (0 : EuclideanSpace ℝ (Fin (n + 3))) 1, Q)}
    {c : C(Q, sphere (0 : EuclideanSpace ℝ (Fin (n + 3))) 1)}
    (hs : s (sphereNorthPole (n + 2)) = q) (hc : c q = sphereNorthPole (n + 2))
    (h : Function.Surjective (ContinuousMap.singularHomologyMap ℤ (n + 2) (c.comp s)))
    (k : Type) [Ring k] (m : ℕ) :
    Function.Injective (ContinuousMap.singularHomologyMap k m
      (map (map s hs : C(MooreLoopSpace _ (sphereNorthPole (n + 2)), MooreLoopSpace Q q))
        (map_one (map s hs)) :
        C(MooreLoopSpace (MooreLoopSpace _ (sphereNorthPole (n + 2))) 1,
          MooreLoopSpace (MooreLoopSpace Q q) 1))) := by
  have hδ : c.comp s (sphereNorthPole (n + 2)) = sphereNorthPole (n + 2) := by
    rw [ContinuousMap.comp_apply, hs, hc]
  -- `(c ∘ s) ∘ c` is a pointed left homotopy inverse of `s`.
  refine injective_singularHomologyMap_map_map_of_homotopicRel hs
    (r := (c.comp s).comp c) (by rw [ContinuousMap.comp_apply, hc, hδ]) ?_ k m
  exact ContinuousMap.homotopicRel_comp_self_id_of_surjective_singularHomologyMap hδ h

end TauCeti.MooreLoopSpace
