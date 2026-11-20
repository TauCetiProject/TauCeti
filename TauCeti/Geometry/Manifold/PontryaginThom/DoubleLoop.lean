/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Homotopy.LoopSpace.Retract
public import TauCeti.AlgebraicTopology.Singular.Fibration.Evaluation
public import TauCeti.Geometry.Manifold.PontryaginThom.Degree
public import TauCeti.Topology.MappingSpace.Fibration

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

Lemma 7.7 then carries such a class into the space `P_{Q→Y} 𝓛₀Q` of maps `S² → Q` sending a base
point into `Y`: when `Y` is `(d + 1)`-connected, the inclusion `Ω²Q → P_{Q→Y} 𝓛₀Q` of the fibre of
evaluation over a point of `Y` is an isomorphism on `H_m` for `m ≤ d`. In the based mapping space
model `Map_*(S², -)` of double loop spaces, the fibre of evaluation, the composite
`Ω²Sᵏ → Ω²Q → P_{Q→Y} 𝓛₀Q` is therefore injective on `H_m` for `m ≤ d`
(`TauCeti.IsFramedTube.injective_singularHomologyMap_inclEvalPreimage_comp_map`), so it keeps
`j_!α₀` of infinite order. In the source this composite is `j_{Y!} α = j^{(Y)}_* j_! β`, through the
shriek maps of DG Morse homology, which are not formalized here; what is proved is the statement
about the topological maps that the source's argument reduces to.

## Main results

* `TauCeti.IsFramedTube.injective_singularHomologyMap_map_map`: the double loops of a sphere
  meeting the core of a framed tube once are injective on singular homology.
* `TauCeti.IsFramedTube.injective_singularHomologyMap_inclEvalPreimage_comp_map`: followed by the
  inclusion into the maps `S² → Q` sending the base point into a `(d + 1)`-connected core, they stay
  injective on `H_m` for `m ≤ d`.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §7, Lemmas 7.6 and 7.7.
-/

public section

open Metric Set
open scoped Topology

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

/-- **The double loops of a sphere meeting a highly connected framed submanifold once, inside the
maps of `S²` sending the base point into it.** Let `σ : Sⁿ⁺² → Q` meet the core `Y = f(S)` of a
framed tube with fibre `ℝⁿ⁺²` in the single point `x`, at which the composite of `σ` with the
Pontryagin–Thom collapse onto `Sⁿ⁺²` is a local homeomorphism, and let `πⱼ(Y, σ x)` be trivial for
every `j ≤ d + 1`. Then the double loops of `σ` at `x`, followed by the inclusion of the based maps
into the maps `S² → Q` sending a base point `b₀` into `Y`,
`Ω²Sⁿ⁺² → Ω²Q → ev⁻¹(Y) = P_{Q→Y} 𝓛₀Q`, are injective on `H_m` for every `m ≤ d`, with any
coefficients. Double loops are taken in their based mapping space model `Map_*(S², -)`, the fibre
of evaluation at `b₀`. -/
theorem injective_singularHomologyMap_inclEvalPreimage_comp_map (h : IsFramedTube f τ)
    (s₀ : sphere (0 : EuclideanSpace ℝ (Fin (n + 3))) 1)
    (σ : C(sphere (0 : EuclideanSpace ℝ (Fin (n + 3))) 1, Q)) {x : sphere (0 : EuclideanSpace ℝ
      (Fin (n + 3))) 1} (hx : σ ⁻¹' range f = {x})
    (hσ : IsLocalHomeomorphOn (pontryaginThomSphereMap h.isOpenEmbedding s₀ ∘ σ) {x})
    (b₀ : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) {d : ℕ}
    (hY : ∀ j ≤ d + 1, Subsingleton (π_ j (range f) ⟨σ x, hx.ge (mem_singleton x)⟩))
    (R : Type) [Ring R] {m : ℕ} (hm : m ≤ d) :
    Function.Injective (ContinuousMap.singularHomologyMap R m
      ((BasedMap.inclEvalPreimage (b₀ := b₀) (Y := range f) (hx.ge (mem_singleton x))).comp
        (⟨BasedMap.map σ rfl, BasedMap.continuous_map σ rfl⟩ :
          C(BasedMap _ _ b₀ x, BasedMap _ Q b₀ (σ x))))) := by
  -- Over the `(d + 1)`-connected core, the based maps are a homology isomorphism below `d + 1`,
  -- and the double loops of `σ` are injective by Lemma 7.6.
  have hev : TopCat.serreFibrations (TopCat.ofHom (mappingSpaceEval (X := Q) b₀)) :=
    (isHurewiczFibration_mappingSpaceEval_sphere.{0} 2 b₀).mem_serreFibrations
  have hincl := BasedMap.bijective_singularHomologyMap_inclEvalPreimage hev
    (Y := range f) (hx.ge (mem_singleton x)) hY R (Nat.lt_succ_of_le hm)
  have hmap := BasedMap.injective_singularHomologyMap_map_of_surjective_singularHomologyMap
    (b₀ := b₀) (x := x) rfl (h.bijective_singularHomologyMap_pontryaginThomSphereMap_comp_sphere s₀
      (by omega) σ hx hσ).2 R m
  intro a b hab
  rw [ContinuousMap.singularHomologyMap_comp, ContinuousMap.singularHomologyMap_comp] at hab
  exact hmap (hincl.1 hab)

end TauCeti.IsFramedTube
