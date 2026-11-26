/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Homotopy.LoopSpace.Retract
public import TauCeti.Geometry.Manifold.PontryaginThom.Existence
public import TauCeti.Geometry.Manifold.PontryaginThom.Transverse
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Constructions

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

The paper's hypotheses are smooth, and so is the second form of the lemma. If the tube is a
smooth local diffeomorphism at the point of the core where a smooth sphere meets it, transversely,
the local homeomorphism hypothesis holds by
`TauCeti.IsFramedTube.isLocalHomeomorphOn_pontryaginThomSphereMap_comp_of_transverse`
(`TauCeti.IsFramedTube.injective_singularHomologyMap_map_map_of_transverse`). A smooth framing,
with smooth inverse, of the normal bundle of an embedded compact submanifold provides such a tube
(`TauCeti.SmoothEmbedding.exists_isFramedTube_isLocalDiffeomorph`), which gives the lemma for a
smooth sphere meeting a submanifold with trivial normal bundle transversely in one point
(`TauCeti.SmoothEmbedding.injective_singularHomologyMap_map_map_of_transverse`).

## Main results

* `TauCeti.IsFramedTube.injective_singularHomologyMap_map_map`: the double loops of a sphere
  meeting the core of a framed tube once are injective on singular homology.
* `TauCeti.IsFramedTube.injective_singularHomologyMap_map_map_of_transverse`: the same for a
  smooth sphere meeting the core of a smooth tube once, transversely.
* `TauCeti.SmoothEmbedding.injective_singularHomologyMap_map_map_of_transverse`: the same for a
  smooth sphere meeting a smoothly framed compact submanifold once, transversely.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §7, Lemma 7.6.
-/

public section

open Bundle Metric Set Topology
open scoped ContDiff Manifold

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

section Transverse

variable {ES : Type*} [NormedAddCommGroup ES] [NormedSpace ℝ ES] {HS : Type*}
  [TopologicalSpace HS] {IS : ModelWithCorners ℝ ES HS} [ChartedSpace HS S]
  {EQ : Type*} [NormedAddCommGroup EQ] [NormedSpace ℝ EQ] {HQ : Type*} [TopologicalSpace HQ]
  {IQ : ModelWithCorners ℝ EQ HQ} [ChartedSpace HQ Q] {r : WithTop ℕ∞}

/-- **Lemma 7.6 of Barraud–Damian–Humilière–Oancea for a sphere transverse to the core.** Let
`τ` be a framed tube with fibre `ℝⁿ⁺²` around `f` which is a `C^r` local diffeomorphism at
`(y, 0)`, `1 ≤ r`, and let `σ : Sⁿ⁺² → Q` meet the core in the single point `x`, with
`σ x = f y`. If `σ` is `C^r` near `x` and transverse to `f` there,
`im dσ_x + im df_y = T_{σ x} Q`, then at every base point `z` of the sphere the map
`Ω²σ : Ω²Sⁿ⁺² → Ω²Q` of Moore double loop spaces is injective on singular homology in every
degree and with any coefficients. -/
theorem injective_singularHomologyMap_map_map_of_transverse (h : IsFramedTube f τ) {y : S}
    (hτ : IsLocalDiffeomorphAt (IS.prod 𝓘(ℝ, Fin (n + 2) → ℝ)) IQ r τ (y, 0))
    (σ : C(sphere (0 : EuclideanSpace ℝ (Fin (n + 3))) 1, Q))
    {x : sphere (0 : EuclideanSpace ℝ (Fin (n + 3))) 1} (hx : σ ⁻¹' range f = {x})
    {s : Set (sphere (0 : EuclideanSpace ℝ (Fin (n + 3))) 1)} (hs : s ∈ 𝓝 x)
    (hσ : ContMDiffOn (𝓡 (n + 2)) IQ r σ s) (hr : 1 ≤ r) (hxy : f y = σ x)
    (htrans : (mfderiv (𝓡 (n + 2)) IQ σ x).range ⊔
      (((tangentSpaceCast IQ (f y) (σ x)).toContinuousLinearMap).comp
        (mfderiv IS IQ f y)).range = ⊤)
    {z : sphere (0 : EuclideanSpace ℝ (Fin (n + 3))) 1} {q : Q} (hz : σ z = q)
    (R : Type) [Ring R] (m : ℕ) :
    Function.Injective (ContinuousMap.singularHomologyMap R m
      (MooreLoopSpace.map (MooreLoopSpace.map σ hz : C(MooreLoopSpace _ z, MooreLoopSpace Q q))
        (map_one (MooreLoopSpace.map σ hz)) :
        C(MooreLoopSpace (MooreLoopSpace _ z) 1, MooreLoopSpace (MooreLoopSpace Q q) 1))) :=
  h.injective_singularHomologyMap_map_map x σ hx
    (h.isLocalHomeomorphOn_pontryaginThomSphereMap_comp_of_transverse x hτ hs hσ
      BoundarylessManifold.isInteriorPoint hr finrank_euclideanSpace_fin hxy htrans) hz R m

end Transverse

end TauCeti.IsFramedTube

namespace TauCeti.SmoothEmbedding

variable {E V H G : Type*} {S Q : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [TopologicalSpace H] [TopologicalSpace G] {I : ModelWithCorners ℝ E H}
  {J : ModelWithCorners ℝ V G} [I.Boundaryless] [J.Boundaryless]
  [TopologicalSpace S] [ChartedSpace H S] [IsManifold I ∞ S] [CompactSpace S]
  [TopologicalSpace Q] [ChartedSpace G Q] [IsManifold J ∞ Q] [T2Space Q]
  [SecondCountableTopology Q] {n : ℕ}

/-- **Lemma 7.6 of Barraud–Damian–Humilière–Oancea.** Let `f : S → Q` embed a compact manifold
with trivial normal bundle, framed by a smooth global trivialization `φ` with smooth inverse of
its normal bundle with fibre `ℝⁿ⁺²`, and let `σ : Sⁿ⁺² → Q` be a sphere meeting `f(S)` in the
single point `σ x = f y`, `C^r` near `x` for some `1 ≤ r` and transverse there:
`im dσ_x + im df_y = T_{σ x} Q`. Then at every base point `z` of the sphere the map
`Ω²σ : Ω²Sⁿ⁺² → Ω²Q` of Moore double loop spaces is injective on singular homology in every
degree and with any coefficients. -/
theorem injective_singularHomologyMap_map_map_of_transverse (f : SmoothEmbedding I J ∞ S Q)
    (hn : (∞ : ℕ∞ω) ≠ 0)
    (hdim : Module.finrank ℝ (Fin (n + 2) → ℝ) = Module.finrank ℝ V - Module.finrank ℝ E)
    (φ : Trivialization (Fin (n + 2) → ℝ)
        (π (Fin (n + 2) → ℝ) fun x ↦ f.isImmersion.NormalSpace x hn))
    [φ.IsLinear ℝ] (hφ : φ.baseSet = univ)
    (hφs : letI := f.normalSpaceFiberBundle hn hdim
      ContMDiff (I.prod 𝓘(ℝ, Fin (n + 2) → ℝ)) (I.prod 𝓘(ℝ, Fin (n + 2) → ℝ)) ∞ φ)
    (hφs' : letI := f.normalSpaceFiberBundle hn hdim
      ContMDiff (I.prod 𝓘(ℝ, Fin (n + 2) → ℝ)) (I.prod 𝓘(ℝ, Fin (n + 2) → ℝ)) ∞
        φ.toOpenPartialHomeomorph.symm)
    (σ : C(sphere (0 : EuclideanSpace ℝ (Fin (n + 3))) 1, Q))
    {x : sphere (0 : EuclideanSpace ℝ (Fin (n + 3))) 1} (hx : σ ⁻¹' range f = {x})
    {s : Set (sphere (0 : EuclideanSpace ℝ (Fin (n + 3))) 1)} (hs : s ∈ 𝓝 x)
    {r : WithTop ℕ∞} (hσ : ContMDiffOn (𝓡 (n + 2)) J r σ s) (hr : 1 ≤ r) {y : S}
    (hxy : f y = σ x)
    (htrans : (mfderiv (𝓡 (n + 2)) J σ x).range ⊔
      (((tangentSpaceCast J (f y) (σ x)).toContinuousLinearMap).comp
        (mfderiv I J f y)).range = ⊤)
    {z : sphere (0 : EuclideanSpace ℝ (Fin (n + 3))) 1} {q : Q} (hz : σ z = q)
    (R : Type) [Ring R] (m : ℕ) :
    Function.Injective (ContinuousMap.singularHomologyMap R m
      (MooreLoopSpace.map (MooreLoopSpace.map σ hz : C(MooreLoopSpace _ z, MooreLoopSpace Q q))
        (map_one (MooreLoopSpace.map σ hz)) :
        C(MooreLoopSpace (MooreLoopSpace _ z) 1, MooreLoopSpace (MooreLoopSpace Q q) 1))) := by
  obtain ⟨τ, hτ, hτd, -⟩ := f.exists_isFramedTube_isLocalDiffeomorph hn hdim φ hφ hφs hφs'
    isOpen_univ (subset_univ _)
  exact hτ.injective_singularHomologyMap_map_map_of_transverse
    ((hτd (y, 0)).of_le (min_le_right r ∞)) σ hx hs (hσ.of_le (min_le_left r ∞))
    (le_min hr (by simp)) hxy htrans hz R m

end TauCeti.SmoothEmbedding
