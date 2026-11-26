/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.SymmetricPower.Manifold
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import TauCeti.Geometry.Manifold.ChartedSpace

/-!
# Holomorphic sheets of the incidence correspondence

Let `α` be a Hausdorff complex curve, so that its symmetric power `Sym α n` is a complex manifold
for its elementary-symmetric charts (`TauCeti.isManifold_symChartedSpace`), and let
`v : Y → Sym α n` be a map from a complex manifold, holomorphic on an open set `s`. The *incidence
correspondence* of `v`, the set of pairs `(y, z)` with `z` a point of `v y`, is the pullback of the
universal divisor of `Sym α n × α`. Over the points `y` at which `v y` has no repeated point its
projection to `Y` is an `n`-sheeted covering (`Sym.isCoveringMapOn_fst_mem`). This file shows that
its sheets are holomorphic: near such a point `y₀ ∈ s` the points of `v y` are
`σ 0 y, …, σ (n - 1) y` for holomorphic maps `σ i` into `α`, pairwise distinct at every `y`
(`TauCeti.exists_isOpen_mdifferentiableOn_ofFn_eq`). So near `y₀` the incidence correspondence is
the disjoint union of the graphs of `n` holomorphic maps.

For a holomorphic disk `v : 𝔻 → Sym^g(Σ)` in the symmetric product of a Heegaard surface, the
incidence correspondence is the surface `{(y, z) | z ∈ v y}` over `𝔻`, with its map `(y, z) ↦ z`
to `Σ`, through which Lipshitz compares holomorphic disks in `Sym^g(Σ)` with holomorphic curves in
`Σ × [0, 1] × ℝ`; the result here describes it away from the points where `v` meets the diagonal.
It is the inverse construction to taking the unordered fibres of a branched cover
(`TauCeti.RiemannSurface.FiniteHolomorphicMap.fiberSym`).

The proof reads `v` in the elementary-symmetric chart with one block per point of `v y₀`. Built from
pairwise disjoint coordinate patches `V i` around the points of `v y₀`, it reads a tuple with one
point `wᵢ` in each `V i` as the negated coordinates of the `wᵢ`
(`TauCeti.ofFn_mem_source_and_symOpenPartialHomeomorph_ofFn_eq`). This chart belongs to the maximal
analytic atlas (`TauCeti.symOpenPartialHomeomorph_mem_maximalAtlas`), so `σ i` is the composition
of `v`, this chart, a coordinate projection and the inverse of the chart of `α` at the `i`-th point.

## References

* R. Lipshitz, *A cylindrical reformulation of Heegaard Floer homology*, Geom. Topol. **10**
  (2006), 955–1097, §13.
-/

public section

open scoped Manifold ContDiff
open Set Topology

namespace TauCeti

variable {α : Type*} [TopologicalSpace α] [T2Space α] [ChartedSpace ℂ α] [IsManifold 𝓘(ℂ) 1 α]
  {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℂ E H} {Y : Type*} [TopologicalSpace Y] [ChartedSpace H Y]

/-- A coordinate of a holomorphic map into the symmetric power, read in a chart of the maximal
atlas, negated and carried back to `α` by the inverse of a chart of `α`, is holomorphic. -/
private theorem mdifferentiableOn_chartAt_symm_neg_apply {v : Y → Sym α n} {U : Set Y}
    {Φ : OpenPartialHomeomorph (Sym α n) (Fin n → ℂ)}
    (hΦ : letI := symChartedSpace (K := ℂ) (α := α) (n := n)
      Φ ∈ IsManifold.maximalAtlas 𝓘(ℂ, Fin n → ℂ) ω (Sym α n))
    (hv : letI := symChartedSpace (K := ℂ) (α := α) (n := n)
      MDifferentiableOn I 𝓘(ℂ, Fin n → ℂ) v U)
    (hvΦ : MapsTo v U Φ.source) (a : α) (i : Fin n)
    (ha : ∀ y ∈ U, -Φ (v y) i ∈ (chartAt ℂ a).target) :
    MDifferentiableOn I 𝓘(ℂ) (fun y => (chartAt ℂ a).symm (-Φ (v y) i)) U := by
  let := symChartedSpace (K := ℂ) (α := α) (n := n)
  have := isManifold_symChartedSpace (α := α) (n := n)
  have hΦd : MDifferentiableOn 𝓘(ℂ, Fin n → ℂ) 𝓘(ℂ, Fin n → ℂ) Φ Φ.source :=
    (contMDiffOn_of_mem_maximalAtlas hΦ).mdifferentiableOn (by simp)
  have hproj : MDifferentiable 𝓘(ℂ, Fin n → ℂ) 𝓘(ℂ) fun c : Fin n → ℂ => -c i :=
    mdifferentiable_iff_differentiable.2 (by fun_prop)
  exact (mdifferentiableOn_atlas_symm (chart_mem_atlas ℂ a)).comp
    (hproj.mdifferentiableOn.comp (hΦd.comp hv hvΦ) subset_preimage_univ) ha

/-- **The points of a holomorphic family of reduced tuples move holomorphically.** Let `v` be a
map from a complex manifold to the symmetric power of a Hausdorff complex curve, holomorphic on an
open set `s` for the elementary-symmetric charts. If `v y₀` has no repeated point for some
`y₀ ∈ s`, there are an open neighbourhood `U ⊆ s` of `y₀` and holomorphic maps `σ i` on `U` such
that, for every `y ∈ U`, `v y` consists of the pairwise distinct points `σ i y`. -/
theorem exists_isOpen_mdifferentiableOn_ofFn_eq {v : Y → Sym α n} {s : Set Y} (hs : IsOpen s)
    (hv : letI := symChartedSpace (K := ℂ) (α := α) (n := n)
      MDifferentiableOn I 𝓘(ℂ, Fin n → ℂ) v s)
    {y₀ : Y} (hy₀s : y₀ ∈ s) (hy₀ : (v y₀ : Multiset α).Nodup) :
    ∃ U ⊆ s, IsOpen U ∧ y₀ ∈ U ∧ ∃ σ : Fin n → Y → α,
      (∀ i, MDifferentiableOn I 𝓘(ℂ) (σ i) U) ∧
        ∀ y ∈ U, Sym.ofFn (fun i => σ i y) = v y ∧ Function.Injective fun i => σ i y := by
  let := symChartedSpace (K := ℂ) (α := α) (n := n)
  obtain ⟨p, hp⟩ := Sym.ofFn_surjective (v y₀)
  -- pairwise disjoint coordinate patches `V i` around the points `p i`
  obtain ⟨V, hVo, hVsub, hpV, hVdisj⟩ :=
    exists_pairwise_disjoint_isOpen_subset_chartAt_source (H := ℂ)
      (Sym.nodup_coe_ofFn_iff.1 (hp ▸ hy₀))
  have hm : ∑ _i : Fin n, 1 = n := by simp
  have hq : Nonempty (∀ i, Sym (V i) 1) := ⟨fun i => Sym.ofFn fun _ => ⟨p i, hpV i⟩⟩
  -- the tuples with one point in each patch form an open neighbourhood `W` of `v y₀`
  have hE : IsOpenEmbedding fun x : ∀ i, V i => Sym.ofFn fun i => (x i : α) :=
    Sym.isOpenEmbedding_ofFn_map (fun i => ((↑) : V i → α))
      (fun i => (hVo i).isOpenEmbedding_subtypeVal)
      (by simpa only [Subtype.range_coe] using hVdisj)
  set W := range fun x : ∀ i, V i => Sym.ofFn fun i => (x i : α)
  -- the elementary-symmetric chart `Φ` with one block per point reads a tuple of `W` as the
  -- negated coordinates of its points
  set Φ := symOpenPartialHomeomorph (fun i => chartAt ℂ (p i)) V (fun _ => 1) hm hVo hVsub hVdisj
    (Equiv.sigmaUnique (Fin n) fun _ => Fin 1) hq
  have hΦW (x : ∀ i, V i) : Sym.ofFn (fun i => (x i : α)) ∈ Φ.source ∧
      Φ (Sym.ofFn fun i => (x i : α)) = -fun j => chartAt ℂ (p j) (x j) :=
    ofFn_mem_source_and_symOpenPartialHomeomorph_ofFn_eq hVo hVsub hVdisj hm hq
      fun i => (x i).property
  -- on `v ⁻¹' W`, the labels `σ i` recover the points of `v y`
  have hσ {y : Y} (x : ∀ i, V i) (hx : Sym.ofFn (fun i => (x i : α)) = v y) (i : Fin n) :
      (chartAt ℂ (p i)).symm (-Φ (v y) i) = x i := by
    simp only [← hx, (hΦW x).2, Pi.neg_apply, neg_neg]
    exact (chartAt ℂ (p i)).left_inv (hVsub i (x i).property)
  refine ⟨s ∩ v ⁻¹' W, inter_subset_left, hv.continuousOn.isOpen_inter_preimage hs
      hE.isOpen_range, ⟨hy₀s, fun i => ⟨p i, hpV i⟩, hp⟩,
    fun i y => (chartAt ℂ (p i)).symm (-Φ (v y) i), fun i => ?_,
    fun y ⟨_, x, hx⟩ => ⟨?_, fun i j hij => ?_⟩⟩
  · refine mdifferentiableOn_chartAt_symm_neg_apply (Φ := Φ)
      (symOpenPartialHomeomorph_mem_maximalAtlas _ _ _ hm hVo hVsub hVdisj _ hq
        fun i => IsManifold.chart_mem_maximalAtlas _)
      (hv.mono inter_subset_left) ?_ (p i) i ?_
    · rintro y ⟨-, x, hx⟩
      rw [← hx]
      exact (hΦW x).1
    · rintro y ⟨-, x, hx⟩
      simp only [← hx, (hΦW x).2, Pi.neg_apply, neg_neg]
      exact (chartAt ℂ (p i)).map_source (hVsub i (x i).property)
  · simpa only [hσ x hx] using hx
  · refine hVdisj.eq (not_disjoint_iff.2 ⟨x i, (x i).property, ?_⟩)
    exact (hσ x hx i).symm.trans (hij.trans (hσ x hx j)) ▸ (x j).property

end TauCeti
