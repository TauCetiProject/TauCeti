/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Homotopy.LoopSpace.EvaluationPreimage
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

Lemma 7.7 then carries such a class into the space `P_{Q→Y} 𝓛₀Q` of maps `S² → Q` sending a base
point into `Y`: when `Y` is `(d + 1)`-connected, the inclusion `Ω²Q → P_{Q→Y} 𝓛₀Q` of the fibre of
evaluation over a point of `Y` is an isomorphism on `H_m` for `m ≤ d`. In the based mapping space
model `Map_*(S², -)` of double loop spaces, the fibre of evaluation, the composite
`Ω²Sᵏ → Ω²Q → P_{Q→Y} 𝓛₀Q` is therefore injective on `H_m` for `m ≤ d`
(`TauCeti.IsFramedTube.injective_singularHomologyMap_preimageInclusion_comp_map`), so it keeps
`j_!α₀` of infinite order. In the source this composite is `j_{Y!} α = j^{(Y)}_* j_! β`, through the
shriek maps of DG Morse homology, which are not formalized here; what is proved is the statement
about the topological maps that the source's argument reduces to.

## Main results

* `TauCeti.IsFramedTube.injective_singularHomologyMap_map_map`: the double loops of a sphere
  meeting the core of a framed tube once are injective on singular homology.
* `TauCeti.IsFramedTube.injective_singularHomologyMap_map_map_of_transverse`: the same for a
  smooth sphere meeting the core of a smooth tube once, transversely.
* `TauCeti.SmoothEmbedding.injective_singularHomologyMap_map_map_of_transverse`: the same for a
  smooth sphere meeting a smoothly framed compact submanifold once, transversely.
* `TauCeti.IsFramedTube.injective_singularHomologyMap_preimageInclusion_comp_map`: followed by the
  inclusion into the maps `S² → Q` sending the base point into a `(d + 1)`-connected core, the
  double loops of such a sphere stay injective on `H_m` for `m ≤ d`.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §7, Lemmas 7.6 and 7.7.
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

/-- **The double loops of a sphere meeting a highly connected framed submanifold once, inside the
maps of `S²` sending the base point into it.** Let `σ : Sⁿ⁺² → Q` meet the core `Y = f(S)` of a
framed tube with fibre `ℝⁿ⁺²` in the single point `x`, at which the composite of `σ` with the
Pontryagin–Thom collapse onto `Sⁿ⁺²` is a local homeomorphism, and let `πⱼ(Y, σ x)` be trivial for
every `j ≤ d + 1`. Then the double loops of `σ` at `x`, followed by the inclusion of the based maps
into the maps `S² → Q` sending a base point `b₀` into `Y`,
`Ω²Sⁿ⁺² → Ω²Q → ev⁻¹(Y) = P_{Q→Y} 𝓛₀Q`, are injective on `H_m` for every `m ≤ d`, with any
coefficients. Double loops are taken in their based mapping space model `Map_*(S², -)`, the fibre
of evaluation at `b₀`. -/
theorem injective_singularHomologyMap_preimageInclusion_comp_map (h : IsFramedTube f τ)
    (s₀ : sphere (0 : EuclideanSpace ℝ (Fin (n + 3))) 1)
    (σ : C(sphere (0 : EuclideanSpace ℝ (Fin (n + 3))) 1, Q)) {x : sphere (0 : EuclideanSpace ℝ
      (Fin (n + 3))) 1} (hx : σ ⁻¹' range f = {x})
    (hσ : IsLocalHomeomorphOn (pontryaginThomSphereMap h.isOpenEmbedding s₀ ∘ σ) {x})
    (b₀ : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) {d : ℕ}
    (hY : ∀ j ≤ d + 1, Subsingleton (π_ j (range f) ⟨σ x, hx.ge (mem_singleton x)⟩))
    (R : Type) [Ring R] {m : ℕ} (hm : m ≤ d) :
    Function.Injective (ContinuousMap.singularHomologyMap R m
      (((mappingSpaceEval (X := Q) b₀).preimageInclusion
          (mem_preimage.1 (hx.ge (mem_singleton x)))).hom.comp
        ((basedMapHomeomorphPreimage b₀ (σ x) :
            C(BasedMap _ Q b₀ (σ x), mappingSpaceEval (X := Q) b₀ ⁻¹' {σ x})).comp
          (BasedMap.mapContinuousMap σ rfl : C(BasedMap _ _ b₀ x, BasedMap _ Q b₀ (σ x)))))) := by
  -- Over the `(d + 1)`-connected core, the fibre of evaluation is a homology isomorphism below
  -- `d + 1`, the based maps are that fibre, and the double loops of `σ` are injective by Lemma 7.6.
  have hincl : Function.Bijective (ContinuousMap.singularHomologyMap R m
      ((mappingSpaceEval (X := Q) b₀).preimageInclusion
        (mem_preimage.1 (hx.ge (mem_singleton x)))).hom) := by
    have hiso := isIso_singularHomologyMap_preimageInclusion_mappingSpaceEval_sphere R b₀
      (mem_preimage.1 (hx.ge (mem_singleton x))) hY (Nat.lt_succ_of_le hm)
    rw [ContinuousMap.singularHomologyMap_eq_singularHomologyFunctor_map, TopCat.ofHom_hom]
    exact CategoryTheory.ConcreteCategory.bijective_of_isIso _
  have hmap := BasedMap.injective_singularHomologyMap_map_of_surjective_singularHomologyMap
    (b₀ := b₀) (x := x) rfl (h.bijective_singularHomologyMap_pontryaginThomSphereMap_comp_sphere s₀
      (by omega) σ hx hσ).2 R m
  intro a b hab
  simp only [ContinuousMap.singularHomologyMap_comp] at hab
  exact hmap (((basedMapHomeomorphPreimage b₀ (σ x)).toHomotopyEquiv.bijective_singularHomologyMap
    R m).injective (hincl.injective hab))

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
    (φ : Trivialization (Fin (n + 2) → ℝ) (π (Fin (n + 2) → ℝ) fun x ↦ f.NormalSpace x hn))
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
