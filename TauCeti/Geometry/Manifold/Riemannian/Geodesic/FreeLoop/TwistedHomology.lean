/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Twisted.CompactApproximation
public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.FreeLoop.Homology

/-!
# The twisted homology of the free loop space from broken geodesics

Let `M` be a Riemannian manifold whose distance is the Riemannian distance, `r` a radius such that
the tangent ball of radius `r` at every point is a normal domain, and `geoⁿ : 𝓛ⁿM → 𝓛M` the
closed broken geodesics through the tuples of Abouzaid's distance cuts
`𝓛ⁿM = {q ∈ Mⁿ⁺¹ | d(qᵢ, qᵢ₋₁) ≤ δ n i}`, a cocone over the sequence of distance cuts
(`TauCeti.Manifold.cyclicDistanceCutCocone`). With constant coefficients the singular homology of
`𝓛M` is the colimit of the singular homology of the distance cuts
(`TauCeti.Manifold.isColimitMapCoconeSingularHomologyCyclicDistanceCutCocone`). This file proves
the same with coefficients in a local system pulled back from `M` along the evaluation
`ev₀ : 𝓛M → M` of a free loop at its base point:

`Hₘ(𝓛M; ev₀*L) = colimₙ Hₘ(𝓛ⁿM; (ev₀ ∘ geoⁿ)*L)`

(`TauCeti.Manifold.isColimitWhiskerOverTwistedHomologyCoconeCyclicDistanceCutCocone`), and the same
over a union `S` of path components of the free loop space, such as the contractible loops `𝓛₀M`,
with the parts `(geoⁿ)⁻¹(S)` of the distance cuts
(`isColimitWhiskerOverTwistedHomologyCoconeRestrictPreimageCyclicDistanceCutCocone`, in the
namespace `TauCeti.Manifold`).
The orientation local system of `M`, read at the base point, is an example; on a component of the
free loop space, so is any power of it whose exponent is constant on the component.

This is the compact-approximation criterion
`TauCeti.LocalCoefficientSystem.isColimitWhiskerOverTwistedHomologyCoconeOfCompactApprox`. Its new
hypothesis compared with constant coefficients is a coherence condition. A class of `𝓛ⁿM` vanishing
in `𝓛M` vanishes on a compact family `K'` of free loops containing the broken geodesics through a
compact family `K` of tuples. Sampling at `m + 1` equally spaced times maps `K'` to a later distance
cut `𝓛ᵐM`. The arc straightening `G` joins the broken geodesics through the samples to the loops of
`K'`, and the vertex slide `H` joins, inside `𝓛ᵐM`, the samples of the broken geodesics through `K`
to the tuples of `K` with the first vertex repeated. Transport in the local system along the image
under `geoᵐ` of the path traced by `H` must agree with transport along the path traced by `G`.

Both homotopies keep the base point: the straightening and the change of durations run through
loops based at the first sampled vertex
(`TauCeti.Manifold.basepoint_sampleBrokenGeodesicLoopHomotopy`), and the slide keeps the first
vertex
(`TauCeti.Manifold.coe_cyclicDistanceCutSampleBrokenGeodesicHomotopy_apply_zero`). So for a tuple
`q` both paths evaluate at the base point to the constant path at `q₀`
(`TauCeti.Manifold.exists_basepoint_coherent_cyclicDistanceCutSample`), and transport in a local
system pulled back along `ev₀` sees only these images
(`TauCeti.LocalCoefficientSystem.pullback_obj_map_mk_eq_of_forall_apply_eq`).

For a local system that is not pulled back from `M`, such as one with nontrivial monodromy along the
rotation of a loop, the two paths are not constant over `M` and the coherence condition needs a
homotopy between them in `𝓛M`; this is not treated here.

## Main results

* `TauCeti.Manifold.exists_basepoint_coherent_cyclicDistanceCutSample`: the sampling, the arc
  straightening and the vertex slide at a common later stage, with both homotopies keeping the base
  point.
* `TauCeti.Manifold.isColimitWhiskerOverTwistedHomologyCoconeCyclicDistanceCutCocone`: the twisted
  homology of the free loop space with coefficients pulled back along `ev₀` is the colimit of the
  twisted homology of the distance cuts.
* `isColimitWhiskerOverTwistedHomologyCoconeRestrictPreimageCyclicDistanceCutCocone`, in the
  namespace `TauCeti.Manifold`: the same over a union of path components of the free loop space.

## References

* M. Abouzaid, *Symplectic cohomology and Viterbo's theorem*, in *Free loop spaces in geometry and
  topology*, IRMA Lect. Math. Theor. Phys. 24, Eur. Math. Soc., 2015, §11.2, Proposition 11.2.4.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §4.3.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, arXiv:2308.06104, §13.2, Propositions 13.2.2 and 13.2.3.
* A. Hatcher, *Algebraic Topology*, Section 3.H, for homology with local coefficients.
-/

public section

open AlgebraicTopology Bundle CategoryTheory Limits Manifold Metric Set
open scoped ContDiff Manifold

noncomputable section

namespace TauCeti.Manifold

universe u w

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type u} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  [IsRiemannianManifold I M] {r : ℝ} (hr : ∀ q : M, IsNormalDomain I M q (ball 0 r))
  {δ : (n : ℕ) → Fin (n + 1) → ℝ}

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
  have hr0 : 0 < r := hpos.trans (hlt 0 0)
  obtain ⟨N, hN⟩ :=
    MooreFreeLoopSpace.exists_subset_arcsWithin_mapsTo_sample_cyclicDistanceCut hL hr0 hpos
  obtain ⟨hLA, hmaps⟩ := hN (n + (N + 1)) (by omega)
  have hεδ (i : Fin (n + (N + 1) + 1)) : δ 0 0 ≤ δ (n + (N + 1)) i :=
    cutoff_le_of_forall_le_succ_of_lt hδ (by omega) 0 i
  have hδδ' := cutoff_sub_le_of_forall_le_succ hδ n (N + 1)
  have hm := sum_cutoff_le_mul_cutoff hpos.le hδ (show n < n + (N + 1) by omega)
  -- The loops of `L` have arcs of radius less than `r`, and their samples lie in the distance cut.
  let ι : C(L, MooreFreeLoopSpace.arcsWithin {p : M × M | dist p.1 p.2 < r} (n + (N + 1) + 1)) :=
    ⟨fun γ ↦ ⟨γ, hLA γ.property⟩, continuous_subtypeVal.subtype_mk _⟩
  let e : C(L, cyclicDistanceCut (X := M) (δ (n + (N + 1)))) :=
    ⟨fun γ ↦ ⟨_, hmaps _ hεδ γ.property⟩, ((MooreFreeLoopSpace.continuous_sample _).comp
      continuous_subtypeVal).subtype_mk _⟩
  -- On `L`, `geoⁿ⁺ᵏ ∘ e` is the closed broken geodesic through the sampled vertices.
  have hG : (cyclicDistanceCutBrokenGeodesic hr (hlt (n + (N + 1)))).comp e =
      (sampleBrokenGeodesicLoop hr (n + (N + 1))).comp ι :=
    ContinuousMap.ext fun γ ↦ by
      simp only [ContinuousMap.comp_apply, cyclicDistanceCutBrokenGeodesic_apply, e, ι,
        ContinuousMap.coe_mk, sampleBrokenGeodesicLoop_apply hr (n + (N + 1)) ⟨γ, hLA γ.property⟩
          (MooreFreeLoopSpace.dist_sample_sub_one_lt_of_mem_arcsWithin (hLA γ.property))]
  -- On `K`, `e ∘ geoⁿ` samples the broken geodesics, and the map of the sequence repeats the first
  -- vertex.
  have hH : e.comp ⟨hKL.restrict, (map_continuous _).restrict hKL⟩ =
      (cyclicDistanceCutSampleBrokenGeodesic hr (hlt n) (n + (N + 1)) hm).comp
        (ContinuousMap.subtypeVal K) :=
    ContinuousMap.ext fun _ ↦
      Subtype.ext (coe_cyclicDistanceCutSampleBrokenGeodesic_apply hr (hlt n) _ hm _).symm
  have hF : (cyclicDistanceCutRepeatFirstIterate (X := M) (N + 1) hδδ').comp
      (ContinuousMap.subtypeVal K) = ((cyclicDistanceCutFunctor M hpos.le hδ).map
        (homOfLE (Nat.le_add_right n (N + 1)))).hom.comp (ContinuousMap.subtypeVal K) := by
    rw [cyclicDistanceCutFunctor_map_homOfLE M hpos.le hδ n (N + 1) hδδ']
  refine ⟨N + 1, e,
    (((sampleBrokenGeodesicLoopHomotopy hr (n + (N + 1))).compContinuousMap ι).symm).cast hG.symm
      (ContinuousMap.ext fun _ ↦ rfl),
    (((cyclicDistanceCutSampleBrokenGeodesicHomotopy hr (hlt n) hδδ' hm).compContinuousMap
      (ContinuousMap.subtypeVal K)).symm).cast hH.symm hF, fun γ ↦ rfl, fun p ↦ ?_, fun p ↦ ?_⟩
  · simp [ι]
  · simp

/-- **The twisted homology of the free loop space is the colimit of the twisted homology of the
distance cuts, for coefficients pulled back from `M`.** Let `L` be a local system on `M`, pulled
back to the free loop space along the evaluation `ev₀ : 𝓛M → M` at the base point. For cut-offs
`δ n i < r` which grow from each stage to the next, `δ n i ≤ δ (n + 1) j`, and with `δ 0 0`
positive, the broken-geodesic maps `geoⁿ : 𝓛ⁿM → 𝓛M` induce an isomorphism
`colimₙ Hₘ(𝓛ⁿM; (ev₀ ∘ geoⁿ)*L) ≅ Hₘ(𝓛M; ev₀*L)`. -/
def isColimitWhiskerOverTwistedHomologyCoconeCyclicDistanceCutCocone {R : Type*} [Ring R]
    (L : LocalCoefficientSystem.{_, u, max u w} R (TopCat.of M)) (m : ℕ) (hpos : 0 < δ 0 0)
    (hlt : ∀ n i, δ n i < r) (hδ : ∀ n i j, δ n i ≤ δ (n + 1) j) :
    IsColimit ((LocalCoefficientSystem.overTwistedHomologyCocone
      ((LocalCoefficientSystem.pullback (X := TopCat.of (MooreFreeLoopSpace M))
        (MooreFreeLoopSpace.basepointMap M)).obj L) m).whisker
      ((cyclicDistanceCutFunctor M hpos.le hδ).toOver _
        (cyclicDistanceCutCocone hr hlt hpos.le hδ).ι.app
        (cyclicDistanceCutCocone hr hlt hpos.le hδ).w)) :=
  LocalCoefficientSystem.isColimitWhiskerOverTwistedHomologyCoconeOfCompactApprox _ _
    (fun _ hK ↦ exists_cyclicDistanceCutCocone_ι_app_comp_homotopic hr hpos hlt hδ hK)
    (fun n _ _ _ hL hKL ↦ by
      obtain ⟨k, e, G, H, -, hG, hH⟩ :=
        exists_basepoint_coherent_cyclicDistanceCutSample hr hpos hlt hδ hL hKL
      refine ⟨n + k, homOfLE (Nat.le_add_right n k), e, G, H, fun x ↦ ?_⟩
      -- Both paths stay at the first vertex of `x` when evaluated at the base point.
      refine LocalCoefficientSystem.pullback_obj_map_mk_eq_of_forall_apply_eq _ _ fun t ↦ ?_
      -- At time `t` the two paths are `geoⁿ⁺ᵏ (H (t, x))` and `G (t, geoⁿ x)`: `Path.map`,
      -- `Path.cast` and `Homotopy.evalAt` evaluate by definition, and the legs of the cocone are
      -- the broken-geodesic maps.
      rw [MooreFreeLoopSpace.basepointMap_apply, MooreFreeLoopSpace.basepointMap_apply]
      change (cyclicDistanceCutBrokenGeodesic hr (hlt (n + k)) (H (t, x))).basepoint =
        (G (t, ⟨cyclicDistanceCutBrokenGeodesic hr (hlt n) x.val, hKL x.property⟩)).basepoint
      simp only [hG, hH, cyclicDistanceCutBrokenGeodesic_apply, basepoint_brokenGeodesicLoop]) m

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
`e : L → (geoⁿ⁺ᵏ)⁻¹(S)`, a homotopy `G` within `S` from `geoⁿ⁺ᵏ ∘ e` to the inclusion of `L`
through loops based at the base point of the loop it starts from, and a homotopy `H` on `K` within
`(geoⁿ⁺ᵏ)⁻¹(S)` from `e ∘ geoⁿ` to the map of the parts over `S` of the sequence of distance cuts,
keeping the first vertex of the tuple it starts from. -/
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
      (∀ p, (G p).val.basepoint = p.2.val.val.basepoint) ∧
      -- `H.toContinuousMap`: the target of `H` is the part of the distance cut over `S` only up
      -- to unfolding `CategoryTheory.Limits.Cocone.preimageFunctor`.
      ∀ p, (H.toContinuousMap p).val.val 0 = p.2.val.val.val 0 := by
  -- Run the construction for all free loops on the images of `K` and `L`, and restrict it.
  have hKL₀ : MapsTo (cyclicDistanceCutBrokenGeodesic hr (hlt n)) (Subtype.val '' K)
      (Subtype.val '' L) := by
    rintro _ ⟨q, hq, rfl⟩
    exact ⟨_, hKL hq, rfl⟩
  obtain ⟨k, e₀, G₀, H₀, -, hG, hH⟩ := exists_basepoint_coherent_cyclicDistanceCutSample hr hpos
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
          (cyclicDistanceCutCocone hr hlt hpos.le hδ) S _ q.val).symm)), fun p ↦ ?_, fun p ↦ ?_⟩
  · rw [ContinuousMap.Homotopy.coe_codRestrict_apply, ContinuousMap.Homotopy.cast_apply,
      ContinuousMap.Homotopy.compContinuousMap_apply, hG]
    -- `φ` sends a loop of `L` to itself.
    rfl
  · exact (congrArg (fun q : cyclicDistanceCut (X := M) (δ (n + k)) ↦ q.val 0)
      (ContinuousMap.Homotopy.coe_codRestrict_apply _ _ p)).trans (hH (p.1, ψ p.2))

/-- **The twisted homology of a union of components of the free loop space is the colimit of the
twisted homology of its parts of the distance cuts, for coefficients pulled back from `M`.** Let
`S` be a union of path components of the free loop space, such as the contractible loops `𝓛₀M`,
and `L` a local system on `M`, pulled back to `S` along the evaluation `ev₀` at the base point. For
cut-offs as in `TauCeti.Manifold.isColimitWhiskerOverTwistedHomologyCoconeCyclicDistanceCutCocone`,
the restrictions of the broken-geodesic maps to the parts `(geoⁿ)⁻¹(S)` of the distance cuts
(`CategoryTheory.Limits.Cocone.restrictPreimage`) induce an isomorphism
`colimₙ Hₘ((geoⁿ)⁻¹(S); (ev₀ ∘ geoⁿ)*L) ≅ Hₘ(S; ev₀*L)`. -/
def isColimitWhiskerOverTwistedHomologyCoconeRestrictPreimageCyclicDistanceCutCocone {R : Type*}
    [Ring R] (L : LocalCoefficientSystem.{_, u, max u w} R (TopCat.of M)) (m : ℕ)
    (hS : ∀ γ ∈ S, pathComponent γ ⊆ S) (hpos : 0 < δ 0 0) (hlt : ∀ n i, δ n i < r)
    (hδ : ∀ n i j, δ n i ≤ δ (n + 1) j) :
    IsColimit ((LocalCoefficientSystem.overTwistedHomologyCocone
      ((LocalCoefficientSystem.pullback (X := TopCat.of S)
        ((MooreFreeLoopSpace.basepointMap M).comp (ContinuousMap.subtypeVal S))).obj L) m).whisker
      (((cyclicDistanceCutCocone hr hlt hpos.le hδ).preimageFunctor S).toOver _
        ((cyclicDistanceCutCocone hr hlt hpos.le hδ).restrictPreimage S).ι.app
        ((cyclicDistanceCutCocone hr hlt hpos.le hδ).restrictPreimage S).w)) :=
  LocalCoefficientSystem.isColimitWhiskerOverTwistedHomologyCoconeOfCompactApprox _ _
    (fun _ hK ↦
      exists_restrictPreimage_cyclicDistanceCutCocone_ι_app_comp_homotopic hr hS hpos hlt hδ hK)
    (fun n _ _ _ hL hKL ↦ by
      obtain ⟨k, e, G, H, hG, hH⟩ :=
        exists_basepoint_coherent_restrictPreimage_cyclicDistanceCutSample hr hS hpos hlt hδ hL hKL
      refine ⟨n + k, homOfLE (Nat.le_add_right n k), e, G, H, fun x ↦ ?_⟩
      -- Both paths stay at the first vertex of `x` when evaluated at the base point.
      refine LocalCoefficientSystem.pullback_obj_map_mk_eq_of_forall_apply_eq _ _ fun t ↦ ?_
      simp only [ContinuousMap.comp_apply, MooreFreeLoopSpace.basepointMap_apply]
      -- At time `t` the two paths are `geoⁿ⁺ᵏ (H (t, x))` and `G (t, geoⁿ x)`: `Path.map`,
      -- `Path.cast`, `Homotopy.evalAt` and the legs of the restricted cocone evaluate by
      -- definition.
      change (cyclicDistanceCutBrokenGeodesic hr (hlt (n + k))
          (H.toContinuousMap (t, x)).val).basepoint =
        (G (t, ⟨_, hKL x.property⟩)).val.basepoint
      rw [hG]
      simp only [cyclicDistanceCutBrokenGeodesic_apply, basepoint_brokenGeodesicLoop]
      rw [hH]
      -- The loop `geoⁿ x`, read in `S`, is `geoⁿ x`.
      exact ((congrArg MooreFreeLoopSpace.basepoint (cyclicDistanceCutBrokenGeodesic_apply hr
        (hlt n) x.val.val)).trans (basepoint_brokenGeodesicLoop hr n _ _)).symm) m

end Component

end TauCeti.Manifold
