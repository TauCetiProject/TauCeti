/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Sphere.PointedMap
public import TauCeti.AlgebraicTopology.Singular.Homotopy.Invariance
public import TauCeti.Topology.MappingSpace.Based
public import TauCeti.Topology.PathSpace.Moore.Homotopy

/-!
# Double loops of a homotopy retract

If a pointed map `s : (X, x) → (Q, q)` has a pointed left homotopy inverse `r`, that is,
`r ∘ s ≃ id` relative to `x`, then the map `Ω²s` of Moore double loop spaces is injective on
singular homology in every degree and with any coefficients: by homotopy invariance of the Moore
loop functor (`TauCeti.MooreLoopSpace.homotopicRel_comp_map_id`), `Ω²r ∘ Ω²s` is homotopic to
the identity (`TauCeti.MooreLoopSpace.injective_singularHomologyMap_map_map_of_homotopicRel`).

The case of interest is a sphere. Let `s : Sⁿ⁺² → Q` and `c : Q → Sⁿ⁺²` be maps such that
`c ∘ s` has degree `±1`, that is, induces a surjection on `Hₙ₊₂(Sⁿ⁺²; ℤ) ≅ ℤ`; no base point
condition is imposed on either map. A homeomorphism `a` of the sphere moving `c (s x)` to a base
point `x` (`TauCeti.Sphere.exists_homeomorph_apply_eq`) makes `δ = a ∘ c ∘ s` a self-map of
degree `±1` fixing `x`. By Hopf's theorem for pointed self-maps of the sphere, `δ ∘ δ ≃ id`
relative to `x` (`ContinuousMap.homotopicRel_comp_self_id_of_surjective_singularHomologyMap`), so
`δ ∘ a ∘ c` is a pointed left homotopy inverse of `s` at `x`
(`ContinuousMap.exists_homotopicRel_comp_id_of_surjective_singularHomologyMap`), and
`(Ω²s)_* : H_*(Ω²Sⁿ⁺²) → H_*(Ω²Q)` is injective at every base point
(`TauCeti.MooreLoopSpace.injective_singularHomologyMap_map_map_of_surjective_singularHomologyMap`).

The same holds for the based mapping spaces `Map_*(B, -)` out of a pointed space `B` with continuous
evaluation, by postcomposing with the homotopy (`TauCeti.BasedMap.homotopic_map_of_homotopicRel`):
`Map_*(B, s)` is injective on singular homology
(`TauCeti.BasedMap.injective_singularHomologyMap_map_of_homotopicRel`), in particular for the
sphere maps above
(`TauCeti.BasedMap.injective_singularHomologyMap_map_of_surjective_singularHomologyMap`). For
`B = S²` this is the double loop space in its based mapping space model, the fibre of evaluation
`Map(S², Q) → Q`.

This is the homotopy-theoretic part of Lemma 7.6 of Barraud, Damian, Humilière and Oancea. There
`s` embeds `Sᵏ` in a closed manifold `Q`, meeting transversely and in a single point a closed
submanifold `Y` with trivial normal bundle, and `c` is the Pontryagin–Thom collapse of `Q` onto the
fibre sphere of a tubular neighbourhood `Y × Dᵏ`, so that `c ∘ s` has degree one
(`TauCeti.IsFramedTube.injective_singularHomologyMap_map_map`).

## Main results

* `TauCeti.MooreLoopSpace.injective_singularHomologyMap_map_map_of_homotopicRel`: the double loops
  of a map with a pointed left homotopy inverse are injective on singular homology.
* `TauCeti.MooreLoopSpace.injective_singularHomologyMap_map_map_of_surjective_singularHomologyMap`:
  the double loops of a map `s : Sⁿ⁺² → Q` are injective on singular homology at every base point
  when some `c : Q → Sⁿ⁺²` makes `c ∘ s` of degree `±1`.
* `TauCeti.BasedMap.injective_singularHomologyMap_map_of_homotopicRel`,
  `TauCeti.BasedMap.injective_singularHomologyMap_map_of_surjective_singularHomologyMap`: the same
  statements for the based mapping spaces `Map_*(B, -)`.

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

/-- **Double loops of a sphere mapping with degree `±1` onto a sphere.** Let `s : Sⁿ⁺² → Q` and
`c : Q → Sⁿ⁺²` be maps such that `c ∘ s` induces a surjection on `Hₙ₊₂(Sⁿ⁺²; ℤ)`. Then, at every
base point `x` of the sphere, `Ω²s : Ω²Sⁿ⁺² → Ω²Q`, on Moore double loop spaces, is injective on
singular homology in every degree and with any coefficients. Neither `s` nor `c` need preserve a
chosen base point. -/
theorem injective_singularHomologyMap_map_map_of_surjective_singularHomologyMap {Q : Type}
    [TopologicalSpace Q] {n : ℕ} {x : sphere (0 : EuclideanSpace ℝ (Fin (n + 3))) 1} {q : Q}
    {s : C(sphere (0 : EuclideanSpace ℝ (Fin (n + 3))) 1, Q)}
    {c : C(Q, sphere (0 : EuclideanSpace ℝ (Fin (n + 3))) 1)} (hs : s x = q)
    (h : Function.Surjective (ContinuousMap.singularHomologyMap ℤ (n + 2) (c.comp s)))
    (k : Type) [Ring k] (m : ℕ) :
    Function.Injective (ContinuousMap.singularHomologyMap k m
      (map (map s hs : C(MooreLoopSpace _ x, MooreLoopSpace Q q)) (map_one (map s hs)) :
        C(MooreLoopSpace (MooreLoopSpace _ x) 1, MooreLoopSpace (MooreLoopSpace Q q) 1))) := by
  obtain ⟨r, hr, hrs⟩ :=
    ContinuousMap.exists_homotopicRel_comp_id_of_surjective_singularHomologyMap h x
  exact injective_singularHomologyMap_map_map_of_homotopicRel hs (by rwa [← hs]) hrs k m

end TauCeti.MooreLoopSpace

namespace TauCeti.BasedMap

universe u

/-- **Based maps into a homotopy retract.** Let `B` be a space with a base point `b₀`, such that
evaluation `Map(B, X) × B → X` is continuous (`LocallyCompactPair B X`, for instance `B` locally
compact). If a pointed map `s : (X, x) → (Q, q)` has a pointed left inverse `r` up to
homotopy relative to `x`, then postcomposition with `s`, `Map_*(B, X) → Map_*(B, Q)`, is injective
on singular homology in every degree and with any coefficients. For `B = S²` this is the double
loop space in its based mapping space model, the fibre of evaluation `Map(S², Q) → Q`. -/
theorem injective_singularHomologyMap_map_of_homotopicRel {B X Q : Type u} [TopologicalSpace B]
    [TopologicalSpace X] [LocallyCompactPair B X] [TopologicalSpace Q] {b₀ : B} {x : X} {q : Q}
    {s : C(X, Q)} {r : C(Q, X)} (hs : s x = q) (hr : r q = x)
    (h : (r.comp s).HomotopicRel (ContinuousMap.id X) {x}) (k : Type u) [Ring k] (m : ℕ) :
    Function.Injective (ContinuousMap.singularHomologyMap k m
      (⟨map s hs, continuous_map s hs⟩ : C(BasedMap B X b₀ x, BasedMap B Q b₀ q))) := by
  have hrs : r.comp s x = x := by rw [ContinuousMap.comp_apply, hs, hr]
  -- `Map_*(B, r) ∘ Map_*(B, s) = Map_*(B, r ∘ s)` is homotopic to `Map_*(B, id) = id`.
  refine ContinuousMap.injective_singularHomologyMap_of_homotopic_comp_id k m
    (r := ⟨map r hr, continuous_map r hr⟩) ?_
  convert homotopic_map_of_homotopicRel (B := B) (b₀ := b₀) hrs rfl h using 1
  · ext f : 1
    exact map_comp r hr s hs f
  · ext f : 1
    exact (map_id f).symm

/-- **Based maps into a sphere mapping with degree `±1` onto a sphere.** Let `B` be a space with a
base point `b₀`, such that evaluation `Map(B, Sⁿ⁺²) × B → Sⁿ⁺²` is continuous (for instance `B`
locally compact), and let `s : Sⁿ⁺² → Q` and `c : Q → Sⁿ⁺²` be maps such that `c ∘ s` induces a
surjection on `Hₙ₊₂(Sⁿ⁺²; ℤ)`. Then, at every point `x` of the sphere, postcomposition with `s`,
`Map_*(B, Sⁿ⁺²) → Map_*(B, Q)`, is injective on singular homology in every degree and with any
coefficients. -/
theorem injective_singularHomologyMap_map_of_surjective_singularHomologyMap {B Q : Type}
    [TopologicalSpace B] [TopologicalSpace Q] {n : ℕ}
    [LocallyCompactPair B (sphere (0 : EuclideanSpace ℝ (Fin (n + 3))) 1)] {b₀ : B}
    {x : sphere (0 : EuclideanSpace ℝ (Fin (n + 3))) 1} {q : Q}
    {s : C(sphere (0 : EuclideanSpace ℝ (Fin (n + 3))) 1, Q)}
    {c : C(Q, sphere (0 : EuclideanSpace ℝ (Fin (n + 3))) 1)} (hs : s x = q)
    (h : Function.Surjective (ContinuousMap.singularHomologyMap ℤ (n + 2) (c.comp s)))
    (k : Type) [Ring k] (m : ℕ) :
    Function.Injective (ContinuousMap.singularHomologyMap k m
      (⟨map s hs, continuous_map s hs⟩ : C(BasedMap B _ b₀ x, BasedMap B Q b₀ q))) := by
  obtain ⟨r, hr, hrs⟩ :=
    ContinuousMap.exists_homotopicRel_comp_id_of_surjective_singularHomologyMap h x
  exact injective_singularHomologyMap_map_of_homotopicRel hs (by rwa [← hs]) hrs k m

end TauCeti.BasedMap
