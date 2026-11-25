/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.BasedLoop.Approximation
public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.FreeLoop.Homology

/-!
# The singular homology of the based loop space from broken geodesics

Let `M` be a Riemannian manifold whose distance is the Riemannian distance, and let `r` be a
radius such that the tangent ball of radius `r` at every point is a normal domain. The singular
homology of the free loop space `𝓛M` is the colimit of the singular homology of the distance cuts

`𝓛ⁿM = {q ∈ Mⁿ⁺¹ | d(qᵢ, qᵢ₋₁) ≤ δ n i}`

along the closed broken geodesics `geoⁿ : 𝓛ⁿM → 𝓛M`
(`TauCeti.Manifold.isColimitMapCoconeSingularHomologyCyclicDistanceCutCocone`). This file proves
the same for the Moore loops `Ω_x M` based at a point `x`, with the based distance cuts
`𝓛ⁿ_x M = {q ∈ 𝓛ⁿM | q₀ = x}` (`TauCeti.basedCyclicDistanceCut`) in place of the distance cuts.

For cut-offs `δ n i < r` which grow from each stage to the next, `δ n i ≤ δ (n + 1) j`, the maps
of the sequence of distance cuts keep the first vertex, so the based distance cuts at `x` form a
sequence `𝓛⁰_x M → 𝓛¹_x M → ⋯` (`TauCeti.basedCyclicDistanceCutFunctor`). The closed broken
geodesic through a tuple with first vertex `x` is a loop based at `x`, so the maps
`geoⁿ : 𝓛ⁿ_x M → Ω_x M` form a cocone over it
(`TauCeti.Manifold.basedCyclicDistanceCutCocone`). If the first cut-off `δ 0 0` is positive,
singular homology with coefficients in any module turns this cocone into a colimit cocone:

`Hₘ(Ω_x M; V) = colimₙ Hₘ(𝓛ⁿ_x M; V)`

(`TauCeti.Manifold.isColimitMapCoconeSingularHomologyBasedCyclicDistanceCutCocone`). This is the
compact-approximation criterion `TauCeti.isColimitMapCoconeSingularHomologyOfCompactApprox` for
the cocone of based broken geodesics. Its two hypotheses are the based forms of the two halves of
the comparison of the approximation with the loop space: compact families of based loops are
homotopic, through based loops, to the broken geodesics through their samples
(`TauCeti.Manifold.exists_basedCyclicDistanceCutBrokenGeodesic_comp_homotopic`), and sampling a
compact family of based loops containing broken geodesics recovers the tuples of a later stage,
up to homotopy inside the based distance cut
(`TauCeti.Manifold.exists_comp_homotopic_basedCyclicDistanceCutFunctor_map`).

No topology is put on the colimit of the spaces `𝓛ⁿ_x M`: the statement is about their homology.

## Main definitions

* `TauCeti.Manifold.basedCyclicDistanceCutCocone`: the broken-geodesic maps
  `geoⁿ : 𝓛ⁿ_x M → Ω_x M`, as a cocone over the sequence of based distance cuts.
* `TauCeti.Manifold.isColimitMapCoconeSingularHomologyBasedCyclicDistanceCutCocone`: the singular
  homology of the based loop space is the colimit of the singular homology of the based distance
  cuts.

## Main results

* `TauCeti.Manifold.exists_comp_homotopic_basedCyclicDistanceCutFunctor_map`: sampling a compact
  family of based loops containing broken geodesics recovers the tuples of a later stage, up to
  homotopy.

## References

* J. Milnor, *Morse theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  §16 (the approximation of the based path space by broken geodesics).
* M. Abouzaid, *Symplectic cohomology and Viterbo's theorem*, in *Free loop spaces in geometry and
  topology*, IRMA Lect. Math. Theor. Phys. 24, Eur. Math. Soc., 2015, §11.2, Proposition 11.2.4.
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

/-- **The based broken geodesics as a cocone over the based distance cuts.** For cut-offs
`δ n i < r` which grow from each stage to the next and start nonnegative, the maps
`geoⁿ : 𝓛ⁿ_x M → Ω_x M` to the closed broken geodesics through the tuples with first vertex `x`
(`TauCeti.Manifold.basedCyclicDistanceCutBrokenGeodesic`) form a cocone with apex the Moore loop
space at `x` over the sequence of based distance cuts (`TauCeti.basedCyclicDistanceCutFunctor`):
the maps of the sequence do not change the broken geodesic. -/
@[expose, simps pt]
def basedCyclicDistanceCutCocone (hlt : ∀ n i, δ n i < r) (h0 : 0 ≤ δ 0 0)
    (hδ : ∀ n i j, δ n i ≤ δ (n + 1) j) (x : M) :
    Cocone (basedCyclicDistanceCutFunctor M h0 hδ x) where
  pt := TopCat.of (MooreLoopSpace M x)
  ι :=
    { app n := TopCat.ofHom (basedCyclicDistanceCutBrokenGeodesic hr (hlt n) x)
      naturality n m f := by
        ext q : 2
        refine MooreLoopSpace.toFreeLoop_injective ?_
        -- Read as free loops, both sides are broken geodesics of the free cocone, which is
        -- compatible with the maps of the sequence of distance cuts.
        simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id, TopCat.hom_comp,
          ConcreteCategory.hom_ofHom, ContinuousMap.comp_apply,
          toFreeLoop_basedCyclicDistanceCutBrokenGeodesic_apply hr (hlt m) x,
          toFreeLoop_basedCyclicDistanceCutBrokenGeodesic_apply hr (hlt n) x,
          coe_basedCyclicDistanceCutFunctor_map_apply]
        exact (cyclicDistanceCutCocone hr hlt h0 hδ).w_apply f q.val }

/-- The leg of the cocone of based broken geodesics at the stage `n` is the broken-geodesic map
`geoⁿ : 𝓛ⁿ_x M → Ω_x M`. -/
@[simp]
theorem basedCyclicDistanceCutCocone_ι_app_hom (hlt : ∀ n i, δ n i < r) (h0 : 0 ≤ δ 0 0)
    (hδ : ∀ n i j, δ n i ≤ δ (n + 1) j) (x : M) (n : ℕ) :
    ((basedCyclicDistanceCutCocone hr hlt h0 hδ x).ι.app n).hom =
      basedCyclicDistanceCutBrokenGeodesic hr (hlt n) x :=
  (rfl)

include hr in
/-- **Sampling based loops recovers the tuples of a later stage.** Let the cut-offs `δ n i < r`
grow from each stage to the next and start positive. Let `K` be a family of tuples of the based
distance cut `𝓛ⁿ_x M` and `L` a compact family of Moore loops based at `x` containing the broken
geodesics through them. Then for some `k` the samples at `n + k + 1` equally spaced times define a
map `e : L → 𝓛ⁿ⁺ᵏ_x M`, and on `K` its composite with `geoⁿ` is homotopic to the map
`𝓛ⁿ_x M → 𝓛ⁿ⁺ᵏ_x M` of the sequence of based distance cuts, which repeats the first vertex `k`
more times. -/
theorem exists_comp_homotopic_basedCyclicDistanceCutFunctor_map (hpos : 0 < δ 0 0)
    (hlt : ∀ n i, δ n i < r) (hδ : ∀ n i j, δ n i ≤ δ (n + 1) j) {x : M} {n : ℕ}
    {K : Set (basedCyclicDistanceCut (X := M) (δ n) x)} {L : Set (MooreLoopSpace M x)}
    (hL : IsCompact L) (hKL : MapsTo (basedCyclicDistanceCutBrokenGeodesic hr (hlt n) x) K L) :
    ∃ (k : ℕ) (e : C(L, basedCyclicDistanceCut (X := M) (δ (n + k)) x)),
      (∀ γ, (e γ : Fin (n + k + 1) → M) =
        (γ : MooreLoopSpace M x).toMoorePath.sample (n + k + 1)) ∧
      (e.comp ⟨hKL.restrict, (map_continuous _).restrict hKL⟩).Homotopic
        (((basedCyclicDistanceCutFunctor M hpos.le hδ x).map
          (homOfLE (Nat.le_add_right n k))).hom.comp (ContinuousMap.subtypeVal K)) := by
  -- At the stage `n + N + 1` every cut-off is at least `δ 0 0`, and the samples of `L` lie in the
  -- based distance cut.
  obtain ⟨N, hN⟩ := exists_basedCyclicDistanceCutBrokenGeodesic_comp_homotopic hr hL hpos
  obtain ⟨e, he, -⟩ := hN (n + (N + 1)) (by omega) (δ (n + (N + 1)))
    (fun i ↦ cutoff_le_of_forall_le_succ_of_lt hδ (by omega) 0 i) (hlt _)
  -- Every cut-off of the stage `n` is at most every cut-off of the stage `n + N + 1`.
  have hm (j : Fin (n + (N + 1) + 1)) :
      ∑ i, δ n i ≤ ((n + (N + 1) + 1 : ℕ) : ℝ) * δ (n + (N + 1)) j :=
    sum_cutoff_le_mul_cutoff hpos.le hδ (by omega) j
  refine ⟨N + 1, e, he, ?_⟩
  -- On `K`, `e ∘ geoⁿ` samples the based broken geodesics, which the vertex slide joins to the map
  -- of the sequence.
  have he' : e.comp ⟨hKL.restrict, (map_continuous _).restrict hKL⟩ =
      (basedCyclicDistanceCutSampleBrokenGeodesic hr (hlt n) (n + (N + 1)) hm x).comp
        (ContinuousMap.subtypeVal K) := by
    ext q : 3
    simp [he, coe_basedCyclicDistanceCutSampleBrokenGeodesic_apply,
      ← toFreeLoop_basedCyclicDistanceCutBrokenGeodesic_apply,
      -cyclicDistanceCutBrokenGeodesic_apply]
  rw [he', basedCyclicDistanceCutFunctor_map_homOfLE M hpos.le hδ x n (N + 1)
    (cutoff_sub_le_of_forall_le_succ hδ n (N + 1))]
  exact ((homotopic_basedCyclicDistanceCutRepeatFirstIterate_sampleBrokenGeodesic hr (hlt n)
    (cutoff_sub_le_of_forall_le_succ hδ n (N + 1)) hm x).comp
      (ContinuousMap.Homotopic.refl _)).symm

/-- **The singular homology of the based loop space is the colimit of the singular homology of the
based distance cuts.** For cut-offs `δ n i < r` which grow from each stage to the next,
`δ n i ≤ δ (n + 1) j`, and with `δ 0 0` positive, the broken-geodesic maps
`geoⁿ : 𝓛ⁿ_x M → Ω_x M` induce an isomorphism `colimₙ Hₘ(𝓛ⁿ_x M; V) ≅ Hₘ(Ω_x M; V)`, with
coefficients in any module `V`. This is the based form of the colimit over the approximations by
broken geodesics of Barraud, Damian, Humilière and Oancea, *Morse homology with differential
graded coefficients*, §13.2 (Propositions 13.2.2 and 13.2.3), here in singular homology. -/
def isColimitMapCoconeSingularHomologyBasedCyclicDistanceCutCocone {A : Type u} [Ring A]
    (V : ModuleCat.{u} A) (m : ℕ) (hpos : 0 < δ 0 0) (hlt : ∀ n i, δ n i < r)
    (hδ : ∀ n i j, δ n i ≤ δ (n + 1) j) (x : M) :
    IsColimit (((singularHomologyFunctor (ModuleCat.{u} A) m).obj V).mapCocone
      (basedCyclicDistanceCutCocone hr hlt hpos.le hδ x)) :=
  isColimitMapCoconeSingularHomologyOfCompactApprox V m _
    (fun K hK ↦ by
      -- Compact families of based loops are homotopic to broken geodesics through their samples.
      obtain ⟨N, hN⟩ := exists_basedCyclicDistanceCutBrokenGeodesic_comp_homotopic hr hK hpos
      obtain ⟨e, -, he⟩ := hN (N + 1) (by omega) (δ (N + 1))
        (fun i ↦ cutoff_le_of_forall_le_succ_of_lt hδ N.succ_pos 0 i) (hlt (N + 1))
      exact ⟨N + 1, e, by rwa [basedCyclicDistanceCutCocone_ι_app_hom]⟩)
    fun n K L _ hL hKL ↦ by
      -- The leg of the cocone at `n` is `geoⁿ`.
      have hKL' : MapsTo (basedCyclicDistanceCutBrokenGeodesic hr (hlt n) x) K L := hKL
      obtain ⟨k, e, -, he⟩ :=
        exists_comp_homotopic_basedCyclicDistanceCutFunctor_map hr hpos hlt hδ hL hKL'
      exact ⟨n + k, homOfLE (Nat.le_add_right n k), e, he⟩

end TauCeti.Manifold
