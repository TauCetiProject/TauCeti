/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Topology.UniformSpace.Ascoli

/-!
# The Arzelà–Ascoli theorem in `C(X, Y)`

Mathlib proves the Arzelà–Ascoli theorem for a family of functions viewed inside a space of
uniform convergence on a family of compact sets
(`ArzelaAscoli.isCompact_closure_of_isClosedEmbedding`).
This file states it directly for subsets of the space `C(X, Y)` of continuous maps with its
compact-open topology, which is the space of continuous curves when `X` is a compact interval,
and adds the two companion statements used for compactness of families of curves.

* An equicontinuous set `A ⊆ C(X, Y)` whose values at each point lie in a common compact set has
  compact closure.
* If `Y` is complete, it is enough that the values are totally bounded at the points of a dense
  set `D ⊆ X`: equicontinuity spreads total boundedness from `D` to every point, and completeness
  turns it into compactness of the closure.
* Conversely, on a compact domain and with a pseudometric target, a compact subset of `C(X, Y)` is
  equicontinuous.

The pointwise hypothesis cannot be replaced by equicontinuity and a common starting point when `Y`
is not proper. The curves `γₙ(t) = t • eₙ`, `t ∈ [0, 1]`, along the standard basis vectors of
`ℓ²` are `1`-Lipschitz and all start at `0`, but no subsequence converges uniformly, because the
endpoints `eₙ` stay at distance at least `1` from each other
(`TauCeti.exists_lipschitzWith_one_not_isCompact_closure_range`).

## Main results

* `ArzelaAscoli.isCompact_closure_of_equicontinuous`: equicontinuity and pointwise relative
  compactness give compact closure.
* `Equicontinuous.totallyBounded_image_eval`: equicontinuity spreads total boundedness of the
  values from a dense set of points to every point.
* `ArzelaAscoli.isCompact_closure_of_equicontinuous_of_totallyBounded`: for a complete target,
  total boundedness of the values at the points of a dense set suffices.
* `IsCompact.equicontinuous`: a compact set of continuous maps on a compact space is
  equicontinuous.
* `TauCeti.exists_lipschitzWith_one_not_isCompact_closure_range`: the curves `t • eₙ` in `ℓ²`.

## References

* J. R. Munkres, *Topology*, 2nd ed., Prentice Hall 2000, §47 (Ascoli's theorem).
-/

public section

open Filter Metric Set Topology Uniformity

variable {X Y : Type*} [TopologicalSpace X]

namespace ArzelaAscoli

-- `C(X, Y)` sits inside the uniform-on-compacts function space as a closed subspace: the
-- coercion is a uniform embedding, and its range is the continuous maps, which is closed when
-- the topology of `X` is coherent with its compacts. This is the shape Arzelà–Ascoli asks for.
private theorem isClosedEmbedding_ofFun_comp_coe [CompactlyCoherentSpace X] [UniformSpace Y] :
    IsClosedEmbedding (⇑(UniformOnFun.ofFun {K : Set X | IsCompact K}) ∘
      (DFunLike.coe : C(X, Y) → (X → Y))) := by
  refine ⟨ContinuousMap.isUniformEmbedding_toUniformOnFunIsCompact.isEmbedding, ?_⟩
  -- The `rfl` below is just `ContinuousMap.toUniformOnFunIsCompact` unfolded (Mathlib
  -- `Topology/UniformSpace/CompactConvergence.lean`): Arzelà–Ascoli asks for the map in the
  -- `UniformOnFun.ofFun 𝔖 ∘ F` form, while `range_toUniformOnFunIsCompact` is stated for the
  -- packaged name, so this bridges the two.
  rw [show (⇑(UniformOnFun.ofFun {K : Set X | IsCompact K}) ∘
      (DFunLike.coe : C(X, Y) → (X → Y))) = ContinuousMap.toUniformOnFunIsCompact from rfl,
    ContinuousMap.range_toUniformOnFunIsCompact]
  exact UniformOnFun.isClosed_setOfPred_continuous CompactlyCoherentSpace.isCoherentWith

/-- **The Arzelà–Ascoli theorem in `C(X, Y)`.** On a space `X` whose topology is coherent with its
compact sets (for instance a locally compact space), an equicontinuous set of continuous maps
whose values at each point lie in a common compact set has compact closure in the compact-open
topology. -/
theorem isCompact_closure_of_equicontinuous [CompactlyCoherentSpace X] [UniformSpace Y]
    [T2Space Y] {A : Set C(X, Y)} (hA : Equicontinuous fun f : A ↦ ⇑(f : C(X, Y)))
    (hApt : ∀ x, ∃ Q, IsCompact Q ∧ ∀ f ∈ A, f x ∈ Q) : IsCompact (closure A) :=
  ArzelaAscoli.isCompact_closure_of_isClosedEmbedding (fun _ hK ↦ hK)
    isClosedEmbedding_ofFun_comp_coe (fun K _ ↦ hA.equicontinuousOn K) fun _ _ x _ ↦ hApt x

end ArzelaAscoli

/-- Equicontinuity spreads total boundedness of the values from a dense set of points to every
point. -/
theorem Equicontinuous.totallyBounded_image_eval [UniformSpace Y] {A : Set C(X, Y)}
    (hA : Equicontinuous fun f : A ↦ ⇑(f : C(X, Y))) {D : Set X} (hD : Dense D)
    (hAD : ∀ x ∈ D, TotallyBounded ((fun f : C(X, Y) ↦ f x) '' A)) (x : X) :
    TotallyBounded ((fun f : C(X, Y) ↦ f x) '' A) := by
  intro U hU
  obtain ⟨V, hV, hVU⟩ := comp_mem_uniformity_sets hU
  obtain ⟨x', hx'D, hx'⟩ := hD.inter_nhds_nonempty (hA x V hV)
  obtain ⟨t, ht, hcover⟩ := hAD x' hx'D V hV
  refine ⟨t, ht, ?_⟩
  rintro _ ⟨f, hf, rfl⟩
  obtain ⟨y, hy, hfy⟩ := mem_iUnion₂.mp (hcover ⟨f, hf, rfl⟩)
  exact mem_iUnion₂.mpr ⟨y, hy, hVU ⟨f x', hx' ⟨f, hf⟩, hfy⟩⟩

namespace ArzelaAscoli

/-- **The Arzelà–Ascoli theorem in `C(X, Y)`, with a dense set of points.** For a complete
Hausdorff target `Y`, an equicontinuous set of continuous maps whose values are totally bounded at
the points of a dense set `D ⊆ X` has compact closure in the compact-open topology. -/
theorem isCompact_closure_of_equicontinuous_of_totallyBounded [CompactlyCoherentSpace X]
    [UniformSpace Y] [T2Space Y] [CompleteSpace Y] {A : Set C(X, Y)} {D : Set X} (hD : Dense D)
    (hA : Equicontinuous fun f : A ↦ ⇑(f : C(X, Y)))
    (hAD : ∀ x ∈ D, TotallyBounded ((fun f : C(X, Y) ↦ f x) '' A)) : IsCompact (closure A) :=
  isCompact_closure_of_equicontinuous hA fun x ↦
    ⟨_, ((hA.totallyBounded_image_eval hD hAD x).closure).isCompact_of_isClosed isClosed_closure,
      fun f hf ↦ subset_closure ⟨f, hf, rfl⟩⟩

end ArzelaAscoli

/-- **A compact set of continuous maps is equicontinuous.** On a compact space `X` and with a
pseudometric target, every compact subset of `C(X, Y)` is equicontinuous; this is the converse of
`ArzelaAscoli.isCompact_closure_of_equicontinuous`. -/
theorem IsCompact.equicontinuous [CompactSpace X] [PseudoMetricSpace Y] {K : Set C(X, Y)}
    (hK : IsCompact K) : Equicontinuous fun f : K ↦ ⇑(f : C(X, Y)) := by
  intro x
  rw [Metric.equicontinuousAt_iff_right]
  intro ε hε
  obtain ⟨t, ht, hcover⟩ := Metric.totallyBounded_iff.mp hK.totallyBounded (ε / 3) (by positivity)
  have hnear : ∀ᶠ x' in 𝓝 x, ∀ g ∈ t, dist (g x) (g x') < ε / 3 :=
    ht.eventually_all.mpr fun g _ ↦
      (Metric.tendsto_nhds.mp (g.continuous.tendsto x) (ε / 3) (by positivity)).mono
        fun _ h ↦ by rwa [dist_comm]
  filter_upwards [hnear] with x' hx'
  rintro ⟨f, hf⟩
  obtain ⟨g, hg, hfg⟩ := mem_iUnion₂.mp (hcover hf)
  rw [mem_ball] at hfg
  calc dist (f x) (f x') ≤ dist (f x) (g x) + dist (g x) (g x') + dist (g x') (f x') :=
        dist_triangle4 _ _ _ _
    _ < ε / 3 + ε / 3 + ε / 3 := by
        gcongr
        · exact (ContinuousMap.dist_apply_le_dist x).trans_lt hfg
        · exact hx' g hg
        · rw [dist_comm]; exact (ContinuousMap.dist_apply_le_dist x').trans_lt hfg
    _ = ε := by ring

namespace TauCeti

/-- **Equicontinuity and a common starting point do not give compactness.** The curves
`γₙ(t) = t • eₙ`, `t ∈ [0, 1]`, along the standard basis vectors `eₙ` of `ℓ²` are `1`-Lipschitz and
all start at `0`, but they form a set without compact closure in `C([0, 1], ℓ²)`, because their
endpoints are at distance at least `1` from each other. The pointwise compactness hypothesis of
`ArzelaAscoli.isCompact_closure_of_equicontinuous` therefore cannot be dropped. -/
theorem exists_lipschitzWith_one_not_isCompact_closure_range :
    ∃ γ : ℕ → C(Icc (0 : ℝ) 1, lp (fun _ : ℕ ↦ ℝ) 2),
      (∀ n, LipschitzWith 1 (γ n)) ∧ (∀ n, γ n ⟨0, left_mem_Icc.mpr zero_le_one⟩ = 0) ∧
        ¬ IsCompact (closure (range γ)) := by
  classical
  set e : ℕ → lp (fun _ : ℕ ↦ ℝ) 2 := fun n ↦ lp.single 2 n 1 with he
  have he_norm : ∀ n, ‖e n‖ = 1 := fun n ↦ by simp [he, lp.norm_single]
  -- Distinct basis vectors are at distance at least `1`: compare their `n`-th coordinates.
  have he_dist : ∀ n m, n ≠ m → 1 ≤ dist (e n) (e m) := by
    intro n m hnm
    have := lp.norm_apply_le_norm (by norm_num : (2 : ENNReal) ≠ 0) (e n - e m) n
    simpa [he, dist_eq_norm, lp.single_apply, Pi.single_apply, hnm] using this
  refine ⟨fun n ↦ ⟨fun t ↦ (t : ℝ) • e n, by fun_prop⟩, fun n ↦ ?_, fun n ↦ by simp, ?_⟩
  · refine LipschitzWith.of_dist_le_mul fun s t ↦ ?_
    simp [dist_eq_norm, ← sub_smul, norm_smul, he_norm, Subtype.dist_eq]
  · intro hc
    obtain ⟨g, -, φ, hφ, hlim⟩ := hc.tendsto_subseq fun n ↦ subset_closure ⟨n, rfl⟩
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hlim.cauchySeq 1 one_pos
    have hlt := hN N le_rfl (N + 1) N.le_succ
    have hle := ContinuousMap.dist_apply_le_dist (f := (⟨fun t ↦ (t : ℝ) • e (φ N), by fun_prop⟩ :
      C(Icc (0 : ℝ) 1, lp (fun _ : ℕ ↦ ℝ) 2)))
      (g := ⟨fun t ↦ (t : ℝ) • e (φ (N + 1)), by fun_prop⟩) ⟨1, right_mem_Icc.mpr zero_le_one⟩
    have h1 := he_dist (φ N) (φ (N + 1)) (hφ N.lt_succ_self).ne
    simp only [ContinuousMap.coe_mk, one_smul] at hle
    exact absurd (h1.trans hle) (not_le.mpr hlt)

end TauCeti
