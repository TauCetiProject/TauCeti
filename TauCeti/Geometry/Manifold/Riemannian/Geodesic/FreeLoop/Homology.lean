/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.CompactApproximation
public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.FreeLoop.Approximation
public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.FreeLoop.Component
public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.VertexSlide
public import TauCeti.Topology.Category.TopCat.Fiber

/-!
# The singular homology of the free loop space from broken geodesics

Let `M` be a Riemannian manifold whose distance is the Riemannian distance, and let `r` be a
radius such that the tangent ball of radius `r` at every point is a normal domain. Abouzaid's
finite-dimensional approximation of the free loop space `𝓛M` uses the distance cuts

`𝓛ⁿM = {q ∈ Mⁿ⁺¹ | d(qᵢ, qᵢ₋₁) ≤ δ n i}`

for cut-offs `δ n i < r` which grow from each stage to the next, `δ n i ≤ δ (n + 1) j` for all
`i` and `j`. They form a sequence `𝓛⁰M → 𝓛¹M → ⋯` whose maps repeat the first vertex
(`TauCeti.cyclicDistanceCutFunctor`), and the closed broken geodesics through the tuples,
`geoⁿ : 𝓛ⁿM → 𝓛M`, are compatible with these maps, so they form a cocone over the sequence
(`TauCeti.Manifold.cyclicDistanceCutCocone`).

If the first cut-off `δ 0 0` is positive, singular homology with coefficients in any module turns
this cocone into a colimit cocone:

`Hₘ(𝓛M; V) = colimₙ Hₘ(𝓛ⁿM; V)`

(`TauCeti.Manifold.isColimitMapCoconeSingularHomologyCyclicDistanceCutCocone`). This is the
compact-approximation criterion `TauCeti.isColimitMapCoconeSingularHomologyOfCompactApprox` for
the cocone of broken geodesics. Its two hypotheses are the two halves of Abouzaid's comparison of
the approximation with the free loop space.

* A compact family of free loops is sampled into a distance cut at a late enough stage, and the
  broken geodesics through the samples are homotopic to the loops themselves
  (`TauCeti.Manifold.exists_cyclicDistanceCutBrokenGeodesic_comp_homotopic`).
* Conversely, let `L` be a compact family of free loops containing the broken geodesics through a
  family `K` of tuples of `𝓛ⁿM`. Sampling `L` at a late enough stage `n + k` lands in `𝓛ⁿ⁺ᵏM`, and
  on `K` the samples of the broken geodesics are homotopic to the map of the sequence, since
  sampling a broken geodesic slides its vertices back to the subdivided tuple
  (`TauCeti.Manifold.exists_basepoint_coherent_cyclicDistanceCutSample`). Both homotopies, the arc
  straightening and the vertex slide, keep the base point, which twisted homology with
  coefficients pulled back along the evaluation at the base point needs.

No topology is put on the colimit of the spaces `𝓛ⁿM`: the statement is about their homology.

The same holds for a union `S` of path components of the free loop space, such as the
contractible loops `𝓛₀M` or the loops in one free homotopy class. Its approximations are the
parts `(geoⁿ)⁻¹(S)` of the distance cuts whose broken geodesics lie in `S`, mapped to `S` by the
restrictions of `geoⁿ` (`CategoryTheory.Limits.Cocone.restrictPreimage`), and

`Hₘ(S; V) = colimₙ Hₘ((geoⁿ)⁻¹(S); V)`

(`TauCeti.Manifold.isColimitMapCoconeSingularHomologyRestrictPreimageCyclicDistanceCutCocone`).
The two halves of the comparison hold over `S` because homotopies do not leave path components:
a compact family of loops of `S` is homotopic within `S` to the broken geodesics through its
samples (`TauCeti.Manifold.exists_restrictPreimage_cyclicDistanceCutBrokenGeodesic_comp_homotopic`),
and the vertex slide stays in `(geoⁿ⁺ᵏ)⁻¹(S)`
(`TauCeti.Manifold.exists_basepoint_coherent_restrictPreimage_cyclicDistanceCutSample`).

## Main definitions

* `TauCeti.Manifold.cyclicDistanceCutCocone`: the broken-geodesic maps `geoⁿ : 𝓛ⁿM → 𝓛M`, as a
  cocone over the sequence of distance cuts.
* `TauCeti.Manifold.isColimitMapCoconeSingularHomologyCyclicDistanceCutCocone`: the singular
  homology of the free loop space is the colimit of the singular homology of the distance cuts.
* `TauCeti.Manifold.isColimitMapCoconeSingularHomologyRestrictPreimageCyclicDistanceCutCocone`:
  the singular homology of a union of path components of the free loop space is the colimit of
  the singular homology of its parts of the distance cuts.

## Main results

* `TauCeti.Manifold.exists_cyclicDistanceCutCocone_ι_app_comp_homotopic`: a compact family of free
  loops is homotopic to broken geodesics at a late enough stage.
* `TauCeti.Manifold.exists_basepoint_coherent_cyclicDistanceCutSample`: sampling a compact family
  of free loops containing broken geodesics recovers the tuples of a later stage, up to a homotopy
  keeping the first vertex, and the broken geodesics through the samples are homotopic to the
  loops through loops keeping the base point.
* `TauCeti.Manifold.exists_comp_cyclicDistanceCutCocone_ι_app_homotopic_map`: the same, stated for
  the legs and maps of the cocone of broken geodesics.
* `TauCeti.Manifold.exists_restrictPreimage_cyclicDistanceCutCocone_ι_app_comp_homotopic`,
  `TauCeti.Manifold.exists_basepoint_coherent_restrictPreimage_cyclicDistanceCutSample`,
  `TauCeti.Manifold.exists_comp_restrictPreimage_cyclicDistanceCutCocone_ι_app_homotopic_map`: the
  same within a union of path components of the free loop space.

## References

* M. Abouzaid, *Symplectic cohomology and Viterbo's theorem*, in *Free loop spaces in geometry and
  topology*, IRMA Lect. Math. Theor. Phys. 24, Eur. Math. Soc., 2015, §11.2, Proposition 11.2.4.
* J. Milnor, *Morse theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  §16.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §4.3.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, arXiv:2308.06104, §13.2, Propositions 13.2.2 and 13.2.3.
-/

public section

open AlgebraicTopology Bundle CategoryTheory Limits Manifold Metric Set
open scoped ContDiff Manifold

noncomputable section

namespace TauCeti.Manifold

universe u

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type u} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  [IsRiemannianManifold I M] {r : ℝ} (hr : ∀ q : M, IsNormalDomain I M q (ball 0 r))
  {δ : (n : ℕ) → Fin (n + 1) → ℝ}

/-- **The broken geodesics as a cocone over the distance cuts.** For cut-offs `δ n i < r` which
grow from each stage to the next and start nonnegative, the maps `geoⁿ : 𝓛ⁿM → 𝓛M` to the closed
broken geodesics through the tuples (`TauCeti.Manifold.cyclicDistanceCutBrokenGeodesic`) form a
cocone with apex the free Moore loop space over the sequence of distance cuts
(`TauCeti.cyclicDistanceCutFunctor`): repeating the first vertex does not change the broken
geodesic. -/
@[expose, simps pt]
def cyclicDistanceCutCocone (hlt : ∀ n i, δ n i < r) (h0 : 0 ≤ δ 0 0)
    (hδ : ∀ n i j, δ n i ≤ δ (n + 1) j) : Cocone (cyclicDistanceCutFunctor M h0 hδ) where
  pt := TopCat.of (MooreFreeLoopSpace M)
  ι := NatTrans.ofSequence (fun n ↦ TopCat.ofHom (cyclicDistanceCutBrokenGeodesic hr (hlt n)))
    fun n ↦ by
      ext q : 2
      have h := cyclicDistanceCutBrokenGeodesic_cyclicDistanceCutRepeatFirst hr (hlt n)
        (hlt (n + 1)) (hδ n 0 0) (h0.trans (cutoff_le_of_forall_le_succ_of_lt hδ n.succ_pos 0 1))
        (fun _ ↦ hδ n _ _) q
      rw [← cyclicDistanceCutFunctor_map_homOfLE_succ M h0 hδ] at h
      -- Both sides are the composites of the maps in `TopCat`, applied to `q`.
      exact h

/-- The leg of the cocone of broken geodesics at the stage `n` is the broken-geodesic map
`geoⁿ : 𝓛ⁿM → 𝓛M`. -/
@[simp]
theorem cyclicDistanceCutCocone_ι_app_hom (hlt : ∀ n i, δ n i < r) (h0 : 0 ≤ δ 0 0)
    (hδ : ∀ n i j, δ n i ≤ δ (n + 1) j) (n : ℕ) :
    ((cyclicDistanceCutCocone hr hlt h0 hδ).ι.app n).hom =
      cyclicDistanceCutBrokenGeodesic hr (hlt n) :=
  (rfl)

include hr in
/-- **Sampling, straightening and sliding at a common stage, keeping the base point.** Let the
cut-offs `δ n i < r` grow from each stage to the next and start positive. Let `K` be a family of
tuples of the distance cut `𝓛ⁿM` and `L` a compact family of free loops containing the broken
geodesics through them. Then for some `k`:

* the samples at `n + k + 1` equally spaced times define a map `e : L → 𝓛ⁿ⁺ᵏM`;
* a homotopy `G` from `geoⁿ⁺ᵏ ∘ e` to the inclusion of `L` runs through loops based at the base
  point of the loop it starts from;
* a homotopy `H` on `K` from `e ∘ geoⁿ` to the map `𝓛ⁿM → 𝓛ⁿ⁺ᵏM` of the sequence of distance cuts,
  which repeats the first vertex `k` more times, keeps the first vertex of the tuple it starts
  from. -/
theorem exists_basepoint_coherent_cyclicDistanceCutSample (hpos : 0 < δ 0 0)
    (hlt : ∀ n i, δ n i < r) (hδ : ∀ n i j, δ n i ≤ δ (n + 1) j) {n : ℕ}
    {K : Set (cyclicDistanceCut (X := M) (δ n))} {L : Set (MooreFreeLoopSpace M)}
    (hL : IsCompact L) (hKL : MapsTo (cyclicDistanceCutBrokenGeodesic hr (hlt n)) K L) :
    ∃ (k : ℕ) (e : C(L, cyclicDistanceCut (X := M) (δ (n + k))))
      (G : ((cyclicDistanceCutBrokenGeodesic hr (hlt (n + k))).comp e).Homotopy
        (ContinuousMap.subtypeVal L))
      (H : (e.comp ⟨hKL.restrict, (map_continuous _).restrict hKL⟩).Homotopy
        (((cyclicDistanceCutFunctor M hpos.le hδ).map
          (homOfLE (Nat.le_add_right n k))).hom.comp (ContinuousMap.subtypeVal K))),
      (∀ γ, (e γ : Fin (n + k + 1) → M) =
        (γ : MooreFreeLoopSpace M).toMoorePath.sample (n + k + 1)) ∧
      (∀ p, (G p).basepoint = (p.2 : MooreFreeLoopSpace M).basepoint) ∧
      ∀ p, (H p : Fin (n + k + 1) → M) 0 = (p.2 : cyclicDistanceCut (X := M) (δ n)).val 0 := by
  -- At the stage `n + N + 1` every cut-off is at least `δ 0 0`: sample `L` there, and straighten
  -- the loops of `L` to the broken geodesics through their samples.
  obtain ⟨N, hN⟩ := exists_cyclicDistanceCutBrokenGeodesic_comp_homotopic hr hL hpos
  obtain ⟨e, G, he, hG⟩ := hN (n + (N + 1)) (by omega) (δ (n + (N + 1)))
    (fun i ↦ cutoff_le_of_forall_le_succ_of_lt hδ (by omega) 0 i) (hlt _)
  have hδδ' := cutoff_sub_le_of_forall_le_succ hδ n (N + 1)
  have hm := sum_cutoff_le_mul_cutoff hpos.le hδ (show n < n + (N + 1) by omega)
  -- On `K`, `e ∘ geoⁿ` samples the broken geodesics, and the map of the sequence repeats the first
  -- vertex.
  have hH : e.comp ⟨hKL.restrict, (map_continuous _).restrict hKL⟩ =
      (cyclicDistanceCutSampleBrokenGeodesic hr (hlt n) (n + (N + 1)) hm).comp
        (ContinuousMap.subtypeVal K) :=
    ContinuousMap.ext fun _ ↦ Subtype.ext <|
      (he _).trans (coe_cyclicDistanceCutSampleBrokenGeodesic_apply hr (hlt n) _ hm _).symm
  have hF : (cyclicDistanceCutRepeatFirstIterate (X := M) (N + 1) hδδ').comp
      (ContinuousMap.subtypeVal K) = ((cyclicDistanceCutFunctor M hpos.le hδ).map
        (homOfLE (Nat.le_add_right n (N + 1)))).hom.comp (ContinuousMap.subtypeVal K) := by
    rw [cyclicDistanceCutFunctor_map_homOfLE M hpos.le hδ n (N + 1) hδδ']
  refine ⟨N + 1, e, G,
    (((cyclicDistanceCutSampleBrokenGeodesicHomotopy hr (hlt n) hδδ' hm).compContinuousMap
      (ContinuousMap.subtypeVal K)).symm).cast hH.symm hF, he, hG, fun p ↦ ?_⟩
  simp

/-- **Compact families of free loops are broken geodesics up to homotopy.** Let the cut-offs
`δ n i < r` grow from each stage to the next and start positive. Every compact family `K` of free
loops maps to some distance cut `𝓛ⁿM` by a map `e` whose broken geodesics `geoⁿ ∘ e` are homotopic
to the inclusion of `K`. -/
theorem exists_cyclicDistanceCutCocone_ι_app_comp_homotopic (hpos : 0 < δ 0 0)
    (hlt : ∀ n i, δ n i < r) (hδ : ∀ n i j, δ n i ≤ δ (n + 1) j) {K : Set (MooreFreeLoopSpace M)}
    (hK : IsCompact K) :
    ∃ (n : ℕ) (e : C(K, cyclicDistanceCut (X := M) (δ n))),
      (((cyclicDistanceCutCocone hr hlt hpos.le hδ).ι.app n).hom.comp e).Homotopic
        (ContinuousMap.subtypeVal K) := by
  obtain ⟨N, hN⟩ := exists_cyclicDistanceCutBrokenGeodesic_comp_homotopic hr hK hpos
  obtain ⟨e, G, -⟩ := hN (N + 1) (by omega) (δ (N + 1))
    (fun i ↦ cutoff_le_of_forall_le_succ_of_lt hδ N.succ_pos 0 i) (hlt (N + 1))
  exact ⟨N + 1, e, by rw [cyclicDistanceCutCocone_ι_app_hom]; exact ⟨G⟩⟩

/-- **Compact families of free loops containing broken geodesics map to a later stage of the
cocone of broken geodesics.** Let the cut-offs `δ n i < r` grow from each stage to the next and
start positive. Let `K` be a family of tuples of the distance cut `𝓛ⁿM` and `L` a compact family of
free loops containing their images under the leg `geoⁿ` of the cocone. Then there are a later stage
`k`, with morphism `f : n ⟶ k`, and a map `e : L → 𝓛ᵏM` whose composite with `geoⁿ` is homotopic on
`K` to the map along `f` of the sequence of distance cuts. This is the compatibility condition of
`TauCeti.isColimitMapCoconeSingularHomologyOfCompactApprox` for this cocone. -/
theorem exists_comp_cyclicDistanceCutCocone_ι_app_homotopic_map (hpos : 0 < δ 0 0)
    (hlt : ∀ n i, δ n i < r) (hδ : ∀ n i j, δ n i ≤ δ (n + 1) j) {n : ℕ}
    {K : Set (cyclicDistanceCut (X := M) (δ n))} {L : Set (MooreFreeLoopSpace M)}
    (hL : IsCompact L) (hKL : MapsTo ((cyclicDistanceCutCocone hr hlt hpos.le hδ).ι.app n) K L) :
    ∃ (k : ℕ) (f : n ⟶ k) (e : C(L, cyclicDistanceCut (X := M) (δ k))),
      (e.comp ⟨hKL.restrict, ((cyclicDistanceCutCocone hr hlt hpos.le hδ).ι.app
        n).hom.continuous.restrict hKL⟩).Homotopic
        (((cyclicDistanceCutFunctor M hpos.le hδ).map f).hom.comp
          (ContinuousMap.subtypeVal K)) := by
  -- The leg of the cocone at `n` is `geoⁿ`.
  have hKL' : MapsTo (cyclicDistanceCutBrokenGeodesic hr (hlt n)) K L := hKL
  obtain ⟨k, e, -, H, -⟩ :=
    exists_basepoint_coherent_cyclicDistanceCutSample hr hpos hlt hδ hL hKL'
  exact ⟨n + k, homOfLE (Nat.le_add_right n k), e, ⟨H⟩⟩

/-- **The singular homology of the free loop space is the colimit of the singular homology of the
distance cuts.** For cut-offs `δ n i < r` which grow from each stage to the next,
`δ n i ≤ δ (n + 1) j`, and with `δ 0 0` positive, the broken-geodesic maps `geoⁿ : 𝓛ⁿM → 𝓛M`
induce an isomorphism `colimₙ Hₘ(𝓛ⁿM; V) ≅ Hₘ(𝓛M; V)`, with coefficients in any module `V`.
This follows the colimit over the approximations by broken geodesics of Barraud, Damian,
Humilière and Oancea, *Morse homology with differential graded coefficients*, §13.2
(Propositions 13.2.2 and 13.2.3), here in singular homology. -/
def isColimitMapCoconeSingularHomologyCyclicDistanceCutCocone {A : Type u} [Ring A]
    (V : ModuleCat.{u} A) (m : ℕ) (hpos : 0 < δ 0 0) (hlt : ∀ n i, δ n i < r)
    (hδ : ∀ n i j, δ n i ≤ δ (n + 1) j) :
    IsColimit (((singularHomologyFunctor (ModuleCat.{u} A) m).obj V).mapCocone
      (cyclicDistanceCutCocone hr hlt hpos.le hδ)) :=
  isColimitMapCoconeSingularHomologyOfCompactApprox V m _
    (fun _ hK ↦ exists_cyclicDistanceCutCocone_ι_app_comp_homotopic hr hpos hlt hδ hK)
    fun _ _ _ _ hL hKL ↦
      exists_comp_cyclicDistanceCutCocone_ι_app_homotopic_map hr hpos hlt hδ hL hKL

/-! ### Unions of components of the free loop space -/

section Component

variable {S : Set (MooreFreeLoopSpace M)}

include hr in
/-- **Sampling, straightening and sliding at a common stage over a union of components, keeping the
base point.** Let `S` be a union of path components of the free loop space and let the cut-offs
`δ n i < r` grow from each stage to the next and start positive. Let `K` be a family of tuples of
the part `(geoⁿ)⁻¹(S)` of the distance cut `𝓛ⁿM` and `L` a compact family of loops of `S`
containing the broken geodesics through them. Then for some `k`, as in
`TauCeti.Manifold.exists_basepoint_coherent_cyclicDistanceCutSample`, there are a map
`e : L → (geoⁿ⁺ᵏ)⁻¹(S)` given by the samples at `n + k + 1` equally spaced times, a homotopy `G`
within `S` from `geoⁿ⁺ᵏ ∘ e` to the inclusion of `L` through loops based at the base point of the
loop it starts from, and a homotopy `H` on `K` within `(geoⁿ⁺ᵏ)⁻¹(S)` from `e ∘ geoⁿ` to the map
of the parts over `S` of the sequence of distance cuts, keeping the first vertex of the tuple it
starts from. -/
theorem exists_basepoint_coherent_restrictPreimage_cyclicDistanceCutSample
    (hS : ∀ γ ∈ S, pathComponent γ ⊆ S) (hpos : 0 < δ 0 0) (hlt : ∀ n i, δ n i < r)
    (hδ : ∀ n i j, δ n i ≤ δ (n + 1) j) {n : ℕ}
    {K : Set (cyclicDistanceCutBrokenGeodesic hr (hlt n) ⁻¹' S)} {L : Set S} (hL : IsCompact L)
    (hKL : MapsTo ((cyclicDistanceCutBrokenGeodesic hr (hlt n)).restrictPreimage S) K L) :
    ∃ (k : ℕ) (e : C(L, cyclicDistanceCutBrokenGeodesic hr (hlt (n + k)) ⁻¹' S))
      (G : (((cyclicDistanceCutBrokenGeodesic hr (hlt (n + k))).restrictPreimage S).comp e).Homotopy
        (ContinuousMap.subtypeVal L))
      (H : (e.comp ⟨hKL.restrict, (map_continuous _).restrict hKL⟩).Homotopy
        ((((cyclicDistanceCutCocone hr hlt hpos.le hδ).preimageFunctor S).map
          (homOfLE (Nat.le_add_right n k))).hom.comp (ContinuousMap.subtypeVal K))),
      (∀ γ, ((e γ : cyclicDistanceCut (X := M) (δ (n + k))) : Fin (n + k + 1) → M) =
        (γ : MooreFreeLoopSpace M).toMoorePath.sample (n + k + 1)) ∧
      (∀ p, (G p).val.basepoint = p.2.val.val.basepoint) ∧
      -- `H.toContinuousMap`: the target of `H` is the part of the distance cut over `S` only up
      -- to unfolding `CategoryTheory.Limits.Cocone.preimageFunctor`.
      ∀ p, (H.toContinuousMap p).val.val 0 = p.2.val.val.val 0 := by
  -- Run the construction for all free loops on the images of `K` and `L`, and restrict it.
  have hKL₀ : MapsTo (cyclicDistanceCutBrokenGeodesic hr (hlt n)) (Subtype.val '' K)
      (Subtype.val '' L) := by
    rintro _ ⟨q, hq, rfl⟩
    exact ⟨_, hKL hq, rfl⟩
  obtain ⟨k, e₀, G₀, H₀, he, hG, hH⟩ := exists_basepoint_coherent_cyclicDistanceCutSample hr hpos
    hlt hδ (hL.image continuous_subtypeVal) hKL₀
  let φ : C(L, Subtype.val '' L) := ⟨(mapsTo_image _ L).restrict, continuous_subtypeVal.restrict _⟩
  let ψ : C(K, Subtype.val '' K) := ⟨(mapsTo_image _ K).restrict, continuous_subtypeVal.restrict _⟩
  -- The broken geodesics through the samples of the loops of `L` lie in `S`.
  have hmem (γ : L) : cyclicDistanceCutBrokenGeodesic hr (hlt (n + k)) (e₀ (φ γ)) ∈ S :=
    (ContinuousMap.Homotopic.symm ⟨G₀⟩).apply_mem hS γ.val.property
  refine ⟨k,
    ⟨fun γ ↦ ⟨e₀ (φ γ), hmem γ⟩, ((map_continuous e₀).comp (map_continuous φ)).subtype_mk _⟩,
    ContinuousMap.Homotopy.codRestrict hS ((G₀.compContinuousMap φ).cast
      (ContinuousMap.ext fun _ ↦ rfl) (ContinuousMap.ext fun _ ↦ rfl)),
    ContinuousMap.Homotopy.codRestrict
      (fun _ hq ↦ (map_continuous _).pathComponent_subset_preimage hS hq)
      ((H₀.compContinuousMap ψ).cast (ContinuousMap.ext fun _ ↦ rfl)
        (ContinuousMap.ext fun q ↦ (Cocone.coe_preimageFunctor_map_apply
          (cyclicDistanceCutCocone hr hlt hpos.le hδ) S _ q.val).symm)), fun γ ↦ he (φ γ),
    fun p ↦ ?_, fun p ↦ ?_⟩
  · rw [ContinuousMap.Homotopy.coe_codRestrict_apply, ContinuousMap.Homotopy.cast_apply,
      ContinuousMap.Homotopy.compContinuousMap_apply, hG]
    -- `φ` sends a loop of `L` to itself.
    rfl
  · exact (congrArg (fun q : cyclicDistanceCut (X := M) (δ (n + k)) ↦ q.val 0)
      (ContinuousMap.Homotopy.coe_codRestrict_apply _ _ p)).trans (hH (p.1, ψ p.2))

/-- **Compact families of free loops in a union of components are broken geodesics up to
homotopy within it.** Let `S` be a union of path components of the free loop space and let the
cut-offs `δ n i < r` grow from each stage to the next and start positive. Every compact family `K`
of loops of `S` maps to the part `(geoⁿ)⁻¹(S)` of some distance cut by a map whose broken geodesics
are homotopic within `S` to the inclusion of `K`. -/
theorem exists_restrictPreimage_cyclicDistanceCutCocone_ι_app_comp_homotopic
    (hS : ∀ γ ∈ S, pathComponent γ ⊆ S) (hpos : 0 < δ 0 0) (hlt : ∀ n i, δ n i < r)
    (hδ : ∀ n i j, δ n i ≤ δ (n + 1) j) {K : Set S} (hK : IsCompact K) :
    ∃ (n : ℕ) (e : C(K, cyclicDistanceCutBrokenGeodesic hr (hlt n) ⁻¹' S)),
      ((((cyclicDistanceCutCocone hr hlt hpos.le hδ).restrictPreimage S).ι.app n).hom.comp
        e).Homotopic (ContinuousMap.subtypeVal K) := by
  -- The loops of `K` are homotopic in `S` to broken geodesics through their samples.
  obtain ⟨N, hN⟩ := exists_restrictPreimage_cyclicDistanceCutBrokenGeodesic_comp_homotopic hr
    hS (hK.image continuous_subtypeVal) (Subtype.coe_image_subset S K) hpos
  obtain ⟨e, -, he⟩ := hN (N + 1) (by omega) (δ (N + 1))
    (fun i ↦ cutoff_le_of_forall_le_succ_of_lt hδ N.succ_pos 0 i) (hlt (N + 1))
  let φ : C(K, Subtype.val '' K) :=
    ⟨(mapsTo_image _ K).restrict, continuous_subtypeVal.restrict _⟩
  refine ⟨N + 1, e.comp φ, ?_⟩
  have hφ : ContinuousMap.subtypeVal K =
      (ContinuousMap.inclusion (Subtype.coe_image_subset S K)).comp φ :=
    ContinuousMap.ext fun _ ↦ rfl
  rw [hφ]
  exact he.comp (ContinuousMap.Homotopic.refl φ)

/-- **Compact families of free loops in a union of components containing broken geodesics map to a
later stage of the cocone over it.** Let `S` be a union of path components of the free loop space
and let the cut-offs `δ n i < r` grow from each stage to the next and start positive. Let `K` be a
family of tuples of the part `(geoⁿ)⁻¹(S)` of the distance cut `𝓛ⁿM` and `L` a compact family of
loops of `S` containing their images under `geoⁿ`. Then there are a later stage `k`, with morphism
`f : n ⟶ k`, and a map `e : L → (geoᵏ)⁻¹(S)` whose composite with `geoⁿ` is homotopic on `K` to the
map along `f` of the parts over `S` of the sequence of distance cuts. This is the compatibility
condition of `TauCeti.isColimitMapCoconeSingularHomologyOfCompactApprox` for this cocone. -/
theorem exists_comp_restrictPreimage_cyclicDistanceCutCocone_ι_app_homotopic_map
    (hS : ∀ γ ∈ S, pathComponent γ ⊆ S) (hpos : 0 < δ 0 0) (hlt : ∀ n i, δ n i < r)
    (hδ : ∀ n i j, δ n i ≤ δ (n + 1) j) {n : ℕ}
    {K : Set (cyclicDistanceCutBrokenGeodesic hr (hlt n) ⁻¹' S)} {L : Set S} (hL : IsCompact L)
    (hKL : MapsTo (((cyclicDistanceCutCocone hr hlt hpos.le hδ).restrictPreimage S).ι.app n) K L) :
    ∃ (k : ℕ) (f : n ⟶ k) (e : C(L, cyclicDistanceCutBrokenGeodesic hr (hlt k) ⁻¹' S)),
      (e.comp ⟨hKL.restrict, (((cyclicDistanceCutCocone hr hlt hpos.le hδ).restrictPreimage
        S).ι.app n).hom.continuous.restrict hKL⟩).Homotopic
        ((((cyclicDistanceCutCocone hr hlt hpos.le hδ).preimageFunctor S).map f).hom.comp
          (ContinuousMap.subtypeVal K)) := by
  obtain ⟨k, e, -, H, -⟩ :=
    exists_basepoint_coherent_restrictPreimage_cyclicDistanceCutSample hr hS hpos hlt hδ hL hKL
  exact ⟨n + k, homOfLE (Nat.le_add_right n k), e, ⟨H⟩⟩

/-- **The singular homology of a union of components of the free loop space is the colimit of the
singular homology of its parts of the distance cuts.** Let `S` be a union of path components of
the free loop space, such as the contractible loops `𝓛₀M` or the loops in one free homotopy class.
For cut-offs as in
`TauCeti.Manifold.isColimitMapCoconeSingularHomologyCyclicDistanceCutCocone`, the restrictions of
the broken-geodesic maps to the parts `(geoⁿ)⁻¹(S)` of the distance cuts whose broken geodesics
lie in `S` (`CategoryTheory.Limits.Cocone.restrictPreimage`) induce an isomorphism
`colimₙ Hₘ((geoⁿ)⁻¹(S); V) ≅ Hₘ(S; V)`, with coefficients in any module `V`. -/
def isColimitMapCoconeSingularHomologyRestrictPreimageCyclicDistanceCutCocone {A : Type u}
    [Ring A] (V : ModuleCat.{u} A) (m : ℕ) (hS : ∀ γ ∈ S, pathComponent γ ⊆ S)
    (hpos : 0 < δ 0 0) (hlt : ∀ n i, δ n i < r) (hδ : ∀ n i j, δ n i ≤ δ (n + 1) j) :
    IsColimit (((singularHomologyFunctor (ModuleCat.{u} A) m).obj V).mapCocone
      ((cyclicDistanceCutCocone hr hlt hpos.le hδ).restrictPreimage S)) :=
  isColimitMapCoconeSingularHomologyOfCompactApprox V m _
    (fun _ hK ↦
      exists_restrictPreimage_cyclicDistanceCutCocone_ι_app_comp_homotopic hr hS hpos hlt hδ hK)
    fun _ _ _ _ hL hKL ↦
      exists_comp_restrictPreimage_cyclicDistanceCutCocone_ι_app_homotopic_map hr hS hpos hlt hδ hL
        hKL

end Component

end TauCeti.Manifold
