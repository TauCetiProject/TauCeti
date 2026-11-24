/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.CompactApproximation
public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.FreeLoop.Approximation
public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.VertexSlide

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
  (`TauCeti.Manifold.exists_comp_homotopic_cyclicDistanceCutFunctor_map`).

No topology is put on the colimit of the spaces `𝓛ⁿM`: the statement is about their homology.

## Main definitions

* `TauCeti.Manifold.cyclicDistanceCutCocone`: the broken-geodesic maps `geoⁿ : 𝓛ⁿM → 𝓛M`, as a
  cocone over the sequence of distance cuts.
* `TauCeti.Manifold.isColimitMapCoconeSingularHomologyCyclicDistanceCutCocone`: the singular
  homology of the free loop space is the colimit of the singular homology of the distance cuts.

## Main results

* `TauCeti.Manifold.exists_comp_homotopic_cyclicDistanceCutFunctor_map`: sampling a compact family
  of free loops containing broken geodesics recovers the tuples of a later stage, up to homotopy.

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
/-- **Sampling recovers the tuples of a later stage.** Let the cut-offs `δ n i < r` grow from each
stage to the next and start positive. Let `K` be a family of tuples of the distance cut `𝓛ⁿM` and
`L` a compact family of free loops containing the broken geodesics through them. Then for some
`k` the samples at `n + k + 1` equally spaced times define a map `e : L → 𝓛ⁿ⁺ᵏM`, and on `K`
its composite with `geoⁿ` is homotopic to the map `𝓛ⁿM → 𝓛ⁿ⁺ᵏM` of the sequence of distance
cuts, which repeats the first vertex `k` more times. -/
theorem exists_comp_homotopic_cyclicDistanceCutFunctor_map (hpos : 0 < δ 0 0)
    (hlt : ∀ n i, δ n i < r) (hδ : ∀ n i j, δ n i ≤ δ (n + 1) j) {n : ℕ}
    {K : Set (cyclicDistanceCut (X := M) (δ n))} {L : Set (MooreFreeLoopSpace M)}
    (hL : IsCompact L) (hKL : MapsTo (cyclicDistanceCutBrokenGeodesic hr (hlt n)) K L) :
    ∃ (k : ℕ) (e : C(L, cyclicDistanceCut (X := M) (δ (n + k)))),
      (∀ γ, (e γ : Fin (n + k + 1) → M) = (γ : MooreFreeLoopSpace M).toMoorePath.sample
        (n + k + 1)) ∧
      (e.comp ⟨hKL.restrict, (map_continuous _).restrict hKL⟩).Homotopic
        (((cyclicDistanceCutFunctor M hpos.le hδ).map
          (homOfLE (Nat.le_add_right n k))).hom.comp (ContinuousMap.subtypeVal K)) := by
  obtain ⟨N, hN⟩ := MooreFreeLoopSpace.exists_mapsTo_sample_cyclicDistanceCut hL hpos
  -- At the stage `n + N + 1` every cut-off is at least `δ 0 0`, and the samples of `L` lie in the
  -- distance cut.
  have hmaps := hN (n + (N + 1)) (by omega) (δ (n + (N + 1)))
    fun i ↦ cutoff_le_of_forall_le_succ_of_lt hδ (by omega) 0 i
  -- Every cut-off of the stage `n` is at most every cut-off of the stage `n + N + 1`.
  have hm (j : Fin (n + (N + 1) + 1)) :
      ∑ i, δ n i ≤ ((n + (N + 1) + 1 : ℕ) : ℝ) * δ (n + (N + 1)) j :=
    sum_cutoff_le_mul_cutoff hpos.le hδ (by omega) j
  let e : C(L, cyclicDistanceCut (X := M) (δ (n + (N + 1)))) :=
    ⟨fun γ ↦ ⟨_, hmaps γ.property⟩, ((MoorePath.continuous_sample _).comp
      (MooreFreeLoopSpace.continuous_toMoorePath.comp continuous_subtypeVal)).subtype_mk _⟩
  refine ⟨N + 1, e, fun γ ↦ rfl, ?_⟩
  -- On `K`, `e ∘ geoⁿ` samples the broken geodesics, which the vertex slide joins to the map of
  -- the sequence.
  have he : e.comp ⟨hKL.restrict, (map_continuous _).restrict hKL⟩ =
      (cyclicDistanceCutSampleBrokenGeodesic hr (hlt n) (n + (N + 1)) hm).comp
        (ContinuousMap.subtypeVal K) :=
    ContinuousMap.ext fun _ ↦
      Subtype.ext (coe_cyclicDistanceCutSampleBrokenGeodesic_apply hr (hlt n) _ hm _).symm
  rw [he, cyclicDistanceCutFunctor_map_homOfLE M hpos.le hδ n (N + 1)
    (cutoff_sub_le_of_forall_le_succ hδ n (N + 1))]
  exact ((homotopic_cyclicDistanceCutRepeatFirstIterate_sampleBrokenGeodesic hr (hlt n)
    (cutoff_sub_le_of_forall_le_succ hδ n (N + 1)) hm).comp (ContinuousMap.Homotopic.refl _)).symm

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
    (fun K hK ↦ by
      -- Compact families of free loops are homotopic to broken geodesics through their samples.
      obtain ⟨N, hN⟩ := exists_cyclicDistanceCutBrokenGeodesic_comp_homotopic hr hK hpos
      obtain ⟨e, -, he⟩ := hN (N + 1) (by omega) (δ (N + 1))
        (fun i ↦ cutoff_le_of_forall_le_succ_of_lt hδ N.succ_pos 0 i) (hlt (N + 1))
      exact ⟨N + 1, e, by rwa [cyclicDistanceCutCocone_ι_app_hom]⟩)
    fun n K L _ hL hKL ↦ by
      -- The leg of the cocone at `n` is `geoⁿ`.
      have hKL' : MapsTo (cyclicDistanceCutBrokenGeodesic hr (hlt n)) K L := hKL
      obtain ⟨k, e, -, he⟩ := exists_comp_homotopic_cyclicDistanceCutFunctor_map hr hpos hlt hδ hL
        hKL'
      exact ⟨n + k, homOfLE (Nat.le_add_right n k), e, he⟩

end TauCeti.Manifold
