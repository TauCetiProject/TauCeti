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
      -- At time `t` the two paths are `geoⁿ⁺ᵏ (H (t, x))` and `G (t, geoⁿ x)`.
      have hHt : ((H.evalAt x).map (cyclicDistanceCutBrokenGeodesic hr (hlt (n + k))).continuous
          t).basepoint = x.val.val 0 := by
        rw [Path.map_coe, Function.comp_apply, ContinuousMap.Homotopy.evalAt_apply,
          cyclicDistanceCutBrokenGeodesic_apply, basepoint_brokenGeodesicLoop, hH]
      have hGt : (G.evalAt ⟨_, hKL x.property⟩ t).basepoint = x.val.val 0 := by
        simp only [ContinuousMap.Homotopy.evalAt_apply, hG, cyclicDistanceCutCocone_ι_app_hom]
        exact (congrArg MooreFreeLoopSpace.basepoint (cyclicDistanceCutBrokenGeodesic_apply hr
          (hlt n) x.val)).trans (basepoint_brokenGeodesicLoop hr n _ _)
      rw [MooreFreeLoopSpace.basepointMap_apply, MooreFreeLoopSpace.basepointMap_apply]
      -- The cast does not change the path (`Path.cast_coe`).
      exact hHt.trans hGt.symm) m

/-! ### Unions of components of the free loop space -/

section Component

variable {S : Set (MooreFreeLoopSpace M)}

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
      obtain ⟨k, e, G, H, -, hG, hH⟩ :=
        exists_basepoint_coherent_restrictPreimage_cyclicDistanceCutSample hr hS hpos hlt hδ hL hKL
      refine ⟨n + k, homOfLE (Nat.le_add_right n k), e, G, H, fun x ↦ ?_⟩
      -- Both paths stay at the first vertex of `x` when evaluated at the base point.
      refine LocalCoefficientSystem.pullback_obj_map_mk_eq_of_forall_apply_eq _ _ fun t ↦ ?_
      -- At time `t` the two paths are `geoⁿ⁺ᵏ (H (t, x))` and `G (t, geoⁿ x)`.
      have hHt : ((H.evalAt x).map ((cyclicDistanceCutBrokenGeodesic hr
          (hlt (n + k))).restrictPreimage S).continuous t).val.basepoint = x.val.val.val 0 := by
        simp only [Path.map_coe, Function.comp_apply, ContinuousMap.restrictPreimage_apply,
          Set.restrictPreimage_coe, cyclicDistanceCutBrokenGeodesic_apply,
          basepoint_brokenGeodesicLoop]
        -- `H.evalAt x` traces `H (·, x)` (`ContinuousMap.Homotopy.evalAt_apply`).
        exact hH (t, x)
      have hGt : (G.evalAt ⟨_, hKL x.property⟩ t).val.basepoint = x.val.val.val 0 := by
        simp only [ContinuousMap.Homotopy.evalAt_apply, hG]
        exact (congrArg MooreFreeLoopSpace.basepoint (cyclicDistanceCutBrokenGeodesic_apply hr
          (hlt n) x.val.val)).trans (basepoint_brokenGeodesicLoop hr n _ _)
      -- The cast does not change the path (`Path.cast_coe`).
      exact ((MooreFreeLoopSpace.basepointMap_apply _).trans hHt).trans
        (hGt.symm.trans (MooreFreeLoopSpace.basepointMap_apply _).symm)) m

end Component

end TauCeti.Manifold
