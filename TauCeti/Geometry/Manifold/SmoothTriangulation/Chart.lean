/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.SmoothTriangulation.Secant

import Mathlib.Analysis.Normed.Affine.Convex

/-!
# Immersed simplices in charts

A map of a closed simplex into the source of an extended chart is a `Cⁿ` immersion of the simplex
exactly when its chart expression, a map into the model vector space, is one. This lets the
Euclidean theory of immersed simplices (secant maps and their approximation estimates) be applied
to maps into a manifold one chart at a time.

Munkres' construction of a smooth triangulation of a manifold `M` (Theorem 10.6) starts from
embedded rectilinear complexes in coordinate charts whose images cover `M`, and then fits them
together. We supply the local input at interior points: every interior point `x` of a Hausdorff
manifold which is both `Cⁿ` and `C¹`, modelled on a finite-dimensional space `E`, lies in the
interior of the image of a closed embedding of a closed simplex of the top dimension `finrank ℝ E`
which is a `Cⁿ` immersion of the simplex. The embedded simplex can be chosen inside any prescribed
neighbourhood of `x`. Compact sets of interior points therefore admit finite covers by interiors
of such embedded simplices, subordinate to a prescribed neighbourhood at each selected point.
The simplex is the image under the inverse chart of a small simplex around the chart image of `x`,
spanned by an affine basis of `E`.

## Main results

* `TauCeti.IsSimplexImmersion.extChartAt_comp`, `TauCeti.IsSimplexImmersion.extChartAt_symm_comp`:
  extended charts and their inverses carry immersed simplices to immersed simplices.
* `TauCeti.isSimplexImmersion_extChartAt_comp_iff`: a map of a simplex into the source of an
  extended chart is an immersion exactly when its chart expression is.
* `ModelWithCorners.IsInteriorPoint.exists_isSimplexImmersion_isClosedEmbedding_range_mem_nhds`:
  every interior point of a Hausdorff manifold modelled on a finite-dimensional space is in the
  interior of the image of a `Cⁿ` closed embedding of a top-dimensional simplex which is an
  immersion of the simplex, contained in a prescribed neighbourhood.
* `IsCompact.exists_finite_isSimplexImmersion_cover`: compact sets of interior points have finite
  covers by interiors of embedded immersed simplices, subordinate to prescribed neighbourhoods.

## References

* J. Munkres, *Elementary Differential Topology*, Annals of Math. Studies 54 (1966), Chapter II,
  Theorem 10.6.
-/

public section

noncomputable section

open Set Function Filter Topology Module AbstractSimplicialComplex
open scoped Manifold ContDiff

variable {ι : Type*}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {n : WithTop ℕ∞} {σ : Finset ι}

namespace TauCeti

namespace IsSimplexImmersion

variable [IsManifold I n M] [IsManifold I 1 M] {x : M}

/-- The chart expression of an immersion of a simplex into the source of an extended chart is an
immersion of the simplex into the model vector space. -/
theorem extChartAt_comp {g : StandardSimplex σ → M} (h : IsSimplexImmersion I n g)
    (hg : range g ⊆ (extChartAt I x).source) :
    IsSimplexImmersion 𝓘(ℝ, E) n (extChartAt I x ∘ g) := by
  rw [extChartAt_source] at hg
  exact h.comp_of_contMDiffOn hg contMDiffOn_extChartAt fun y hy =>
    ⟨_, (mdifferentiableAt_extChartAt (hg hy)).hasMFDerivAt.hasMFDerivWithinAt,
      (isInvertible_mfderiv_extChartAt (by rw [extChartAt_source]; exact hg hy)).injective⟩

/-- The inverse of an extended chart carries an immersion of a simplex into its target to an
immersion of the simplex into the manifold. -/
theorem extChartAt_symm_comp {g : StandardSimplex σ → E} (h : IsSimplexImmersion 𝓘(ℝ, E) n g)
    (hg : range g ⊆ (extChartAt I x).target) :
    IsSimplexImmersion I n ((extChartAt I x).symm ∘ g) :=
  h.comp_of_contMDiffOn hg (contMDiffOn_extChartAt_symm x) fun _ hy =>
    ⟨_, (mdifferentiableWithinAt_extChartAt_symm (hg hy)).hasMFDerivWithinAt.mono
      (extChartAt_target_subset_range x),
      (isInvertible_mfderivWithin_extChartAt_symm (hg hy)).injective⟩

end IsSimplexImmersion

/-- A map of a simplex into the source of an extended chart is an immersion of the simplex exactly
when its chart expression is an immersion into the model vector space. -/
theorem isSimplexImmersion_extChartAt_comp_iff [IsManifold I n M] [IsManifold I 1 M] {x : M}
    {g : StandardSimplex σ → M} (hg : range g ⊆ (extChartAt I x).source) :
    IsSimplexImmersion 𝓘(ℝ, E) n (extChartAt I x ∘ g) ↔ IsSimplexImmersion I n g := by
  refine ⟨fun h => ?_, fun h => h.extChartAt_comp hg⟩
  have hg' : (extChartAt I x).symm ∘ (extChartAt I x ∘ g) = g :=
    funext fun y => (extChartAt I x).left_inv (hg ⟨y, rfl⟩)
  rw [← hg']
  exact h.extChartAt_symm_comp <| by
    rintro _ ⟨y, rfl⟩
    exact (extChartAt I x).map_source (hg ⟨y, rfl⟩)

end TauCeti

namespace ModelWithCorners.IsInteriorPoint

open TauCeti

/-- **Embedded simplices at interior points.** Every interior point `x` of a Hausdorff `Cⁿ`
manifold modelled on a finite-dimensional space `E` has a neighbourhood which is the image of a
closed embedding of a simplex with `finrank ℝ E + 1` vertices that is a `Cⁿ` immersion of the
simplex. It can be chosen inside any prescribed neighbourhood `s` of `x`. The simplex is the
image under the inverse chart at `x` of a small rectilinear simplex around the chart image
of `x`. -/
theorem exists_isSimplexImmersion_isClosedEmbedding_range_mem_nhds [FiniteDimensional ℝ E]
    [T2Space M] [IsManifold I n M] [IsManifold I 1 M] {x : M} (hx : I.IsInteriorPoint x)
    (hσ : σ.card = finrank ℝ E + 1) {s : Set M} (hs : s ∈ 𝓝 x) :
    ∃ g : StandardSimplex σ → M,
      IsSimplexImmersion I n g ∧ IsClosedEmbedding g ∧ range g ∈ 𝓝 x ∧ range g ⊆ s := by
  classical
  -- An affine basis of `E`, indexed by `σ`, whose closed simplex lies in the chart target and
  -- contains the chart image of `x` in its interior.
  obtain ⟨b₀, hbx, hbt⟩ := exists_mem_interior_convexHull_affineBasis
    (Filter.inter_mem
      (mem_interior_iff_mem_nhds.mp (ModelWithCorners.isInteriorPoint_iff.mp hx))
      (extChartAt_preimage_mem_nhds hs))
  let b : AffineBasis σ ℝ E := b₀.reindex (Fintype.equivOfCardEq (by simp [hσ]))
  have hb : range b = range b₀ := by
    rw [AffineBasis.coe_reindex, EquivLike.range_comp]
  rw [← hb] at hbx hbt
  -- The simplex in `E` spanned by `b`, read in barycentric coordinates.
  let L : (σ → ℝ) →ₗ[ℝ] E := Fintype.linearCombination ℝ b
  let p : StandardSimplex σ → E := fun y => L fun a => y.1 a
  have hL (v : σ → ℝ) (hv : ∑ a, v a = 0) (hv0 : L v = 0) : v = 0 := by
    refine funext fun a => (affineIndependent_iff_of_fintype ℝ ⇑b).mp b.ind v hv ?_ a
    rwa [Finset.weightedVSub_eq_linear_combination _ hv, ← Fintype.linearCombination_apply]
  have hsum (y : StandardSimplex σ) : ∑ a : σ, y.1 a = 1 := by
    simpa using (Finset.standardSimplexHomeomorph σ y).total_of_fintype
  have hp : range p = convexHull ℝ (range b) := by
    refine Subset.antisymm ?_ fun z hz => ?_
    · rintro _ ⟨y, rfl⟩
      simp only [p, L, Fintype.linearCombination_apply]
      exact (convex_convexHull ℝ _).sum_mem (fun a _ => StandardSimplex.nonneg y a) (hsum y)
        fun a _ => subset_convexHull ℝ _ (mem_range_self a)
    -- A point of the closed simplex is the image of its barycentric coordinates.
    rw [b.convexHull_eq_nonneg_coord] at hz
    let w : Convexity.StdSimplex ℝ σ :=
      ⟨Finsupp.equivFunOnFinite.symm fun a => b.coord a z, fun a => hz a, by
        rw [Finsupp.sum_fintype _ _ fun _ => rfl]
        simpa using b.sum_coord_apply_eq_one z⟩
    refine ⟨(Finset.standardSimplexHomeomorph σ).symm w, ?_⟩
    have hw : (fun a : σ => ((Finset.standardSimplexHomeomorph σ).symm w).1 a) =
        fun a => b.coord a z := by
      funext a
      rw [← Finset.standardSimplexHomeomorph_weights, Homeomorph.apply_symm_apply]
      exact Finsupp.equivFunOnFinite_symm_apply_apply _ _
    simp only [p]
    rw [hw, Fintype.linearCombination_apply, b.linear_combination_coord_eq_self]
  have hpt : range p ⊆ (extChartAt I x).target := fun z hz => (hbt (hp ▸ hz)).1
  have hpc : Continuous p := L.continuous_of_finiteDimensional.comp <|
    continuous_pi fun a => (continuous_apply (a : ι)).comp continuous_induced_dom
  have hpi : Injective p := by
    intro y y' hyy'
    have hv := hL ((fun a : σ => y.1 a) - fun a : σ => y'.1 a)
      (by simp only [Pi.sub_apply, Finset.sum_sub_distrib, hsum, sub_self])
      (by rw [map_sub]; exact sub_eq_zero.mpr hyy')
    refine (Finset.standardSimplexHomeomorph σ).injective (Convexity.StdSimplex.ext ?_)
    ext a
    simpa [sub_eq_zero] using congrFun hv a
  refine ⟨(extChartAt I x).symm ∘ p,
    (LinearMap.isSimplexImmersion L hL).extChartAt_symm_comp hpt, ?_, ?_, ?_⟩
  · refine Continuous.isClosedEmbedding
      ((continuousOn_extChartAt_symm x).comp_continuous hpc fun y => hpt (mem_range_self y))
      fun y y' hyy' => hpi ?_
    exact (extChartAt I x).symm.injOn (hpt (mem_range_self y)) (hpt (mem_range_self y')) hyy'
  · -- Every point of the chart source whose chart image lies in the simplex is in the image.
    filter_upwards [extChartAt_source_mem_nhds (I := I) x,
      (continuousAt_extChartAt (I := I) x).preimage_mem_nhds (mem_interior_iff_mem_nhds.mp hbx)]
      with y hys hyp
    obtain ⟨z, hz⟩ : extChartAt I x y ∈ range p := hp ▸ hyp
    exact ⟨z, by rw [comp_apply, hz, (extChartAt I x).left_inv hys]⟩
  · rintro _ ⟨y, rfl⟩
    exact (hbt (hp ▸ mem_range_self (f := p) y)).2

end ModelWithCorners.IsInteriorPoint

namespace IsCompact

/-- A compact set of interior points has a finite cover by interiors of closed embeddings of
top-dimensional simplices which are `Cⁿ` immersions of the simplex. The simplex at each
selected point lies in its prescribed neighbourhood. No
compatibility between different simplices is assumed or asserted. This supplies the finite
local cover used before fitting simplices together in a smooth triangulation. -/
theorem exists_finite_isSimplexImmersion_cover [FiniteDimensional ℝ E] [T2Space M]
    [IsManifold I n M] [IsManifold I 1 M] {K : Set M} (hK : IsCompact K)
    (hI : ∀ x ∈ K, I.IsInteriorPoint x) (hσ : σ.card = finrank ℝ E + 1)
    (U : M → Set M) (hU : ∀ x ∈ K, U x ∈ 𝓝 x) :
    ∃ t : Finset K, ∃ g : t → StandardSimplex σ → M,
      (∀ x, TauCeti.IsSimplexImmersion I n (g x) ∧ IsClosedEmbedding (g x) ∧
        range (g x) ∈ 𝓝 (x.1 : K).1 ∧ range (g x) ⊆ U (x.1 : K).1) ∧
      K ⊆ ⋃ x, interior (range (g x)) := by
  classical
  have hlocal (x : K) := (hI x x.2).exists_isSimplexImmersion_isClosedEmbedding_range_mem_nhds
    (n := n) hσ (hU x x.2)
  choose f hf hc hn hs using hlocal
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun x : K => interior (range (f x)))
    (fun _ => isOpen_interior) (fun x hx =>
      mem_iUnion.mpr ⟨⟨x, hx⟩, mem_interior_iff_mem_nhds.mpr (hn ⟨x, hx⟩)⟩)
  refine ⟨t, fun x => f x.1, fun x => ⟨hf _, hc _, hn _, hs _⟩, ?_⟩
  intro x hx
  obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.mp (ht hx)
  exact mem_iUnion.mpr ⟨⟨y, hy⟩, hxy⟩

end IsCompact
