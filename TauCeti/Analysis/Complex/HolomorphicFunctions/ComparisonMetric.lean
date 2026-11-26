/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.HolomorphicFunctions.Deriv
public import TauCeti.Topology.ContinuousMap.ExhaustionMetric
public import TauCeti.Topology.MetricSpace.ProperSpace
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Explicit comparison metric on `holomorphicFunctions U`

For an open subset `U : Opens ℂ` of the complex plane, `U.compactExhaustion 0` exhausts `U` by the
compact sets cutting out `closedBall 0 (n + 1) \ thickening (n + 1)⁻¹ Uᶜ`. Restricting
`(U.compactExhaustion 0).continuousMapDist` along the subalgebra inclusion into `C(U, ℂ)` gives an
explicit bounded metric `HolomorphicFunctions.comparisonDist U` on the closed subalgebra
`holomorphicFunctions U`:
$$
d(f, g) = \sum_{n = 0}^{\infty} 2^{-(n + 1)} \frac{s_n(f, g)}{1 + s_n(f, g)},
\qquad s_n(f, g) = \sup_{z \in K_n} |f(z) - g(z)|.
$$
Neither `C(U, ℂ)` nor `holomorphicFunctions U` is given a `MetricSpace` typeclass instance, so
their canonical compact-convergence uniformities remain the unique active uniform structures.
Instead, `uniformity_eq_iInf_comparisonDist` proves that `comparisonDist U` generates the exact
inherited uniformity on `holomorphicFunctions U` (independently of the exhaustion),
`comparisonMetricSpace U` pulls back `(U.compactExhaustion 0).continuousMapMetricSpace` along
`Subtype.val` when metric theorems are needed, `comparisonDist U` is complete on
`holomorphicFunctions U`, and both compact restriction `restrictContinuousMap hKU` and
differentiation `deriv` satisfy `ε`-`δ` uniform continuity with respect to `comparisonDist U`.

Closed-form evaluations on empty open sets (including `U = ⊥`), on domains whose initial exhaustion
stage `U.compactExhaustion 0 0` is nonempty, and on `U = ⊤` illustrate the normalization of the
bounded metric and the sharpness of the `1 / 2` comparison constant against the `min 1 s_n` series.

## References

* Armin Rainer, *Advanced Complex Analysis*, §11, equation (11.2) and Exercise 19.
* Walter Rudin, *Real and Complex Analysis*, 3rd ed., §10.28 and Theorem 13.3.
-/

public noncomputable section

open Filter Function Metric Set Topology TopologicalSpace UniformSpace
open scoped Uniformity

namespace TauCeti.HolomorphicFunctions

section ComparisonDist

variable {U : Opens ℂ}

/-- Explicit comparison distance on `holomorphicFunctions U`, obtained by restricting
`(U.compactExhaustion 0).continuousMapDist` along the subalgebra inclusion into `C(U, ℂ)`. Not
registered as a metric instance. -/
def comparisonDist (U : Opens ℂ) (f g : holomorphicFunctions U) : ℝ :=
  (U.compactExhaustion 0).continuousMapDist f.val g.val

/-- `comparisonDist U` is the restriction of `(U.compactExhaustion 0).continuousMapDist` to
`holomorphicFunctions U`. -/
theorem comparisonDist_def (U : Opens ℂ) (f g : holomorphicFunctions U) :
    comparisonDist U f g = (U.compactExhaustion 0).continuousMapDist f.val g.val := (rfl)

/-- Series expansion of `comparisonDist U f g` over the stages of `U.compactExhaustion 0`. -/
theorem comparisonDist_eq_tsum (U : Opens ℂ) (f g : holomorphicFunctions U) :
    comparisonDist U f g =
      ∑' n : ℕ, (1 / 2 : ℝ) ^ (n + 1) *
        (dist (f.val.restrict (U.compactExhaustion 0 n))
          (g.val.restrict (U.compactExhaustion 0 n)) /
          (1 + dist (f.val.restrict (U.compactExhaustion 0 n))
            (g.val.restrict (U.compactExhaustion 0 n)))) :=
  (U.compactExhaustion 0).continuousMapDist_def f.val g.val

/-- `comparisonDist U` vanishes on the diagonal. -/
@[simp]
theorem comparisonDist_self (U : Opens ℂ) (f : holomorphicFunctions U) :
    comparisonDist U f f = 0 :=
  (U.compactExhaustion 0).continuousMapDist_self f.val

/-- `comparisonDist U` is symmetric. -/
theorem comparisonDist_comm (U : Opens ℂ) (f g : holomorphicFunctions U) :
    comparisonDist U f g = comparisonDist U g f :=
  (U.compactExhaustion 0).continuousMapDist_comm f.val g.val

/-- `comparisonDist U` is nonnegative. -/
theorem comparisonDist_nonneg (U : Opens ℂ) (f g : holomorphicFunctions U) :
    0 ≤ comparisonDist U f g :=
  (U.compactExhaustion 0).continuousMapDist_nonneg f.val g.val

/-- `comparisonDist U` is strictly bounded above by `1`. -/
theorem comparisonDist_lt_one (U : Opens ℂ) (f g : holomorphicFunctions U) :
    comparisonDist U f g < 1 :=
  (U.compactExhaustion 0).continuousMapDist_lt_one f.val g.val

/-- `comparisonDist U` is bounded above by `1`. -/
theorem comparisonDist_le_one (U : Opens ℂ) (f g : holomorphicFunctions U) :
    comparisonDist U f g ≤ 1 :=
  (U.compactExhaustion 0).continuousMapDist_le_one f.val g.val

/-- Triangle inequality for `comparisonDist U`. -/
theorem comparisonDist_triangle (U : Opens ℂ) (f g h : holomorphicFunctions U) :
    comparisonDist U f h ≤ comparisonDist U f g + comparisonDist U g h :=
  (U.compactExhaustion 0).continuousMapDist_triangle f.val g.val h.val

/-- `comparisonDist U` separates distinct holomorphic functions on `U`. -/
@[simp]
theorem comparisonDist_eq_zero_iff {f g : holomorphicFunctions U} :
    comparisonDist U f g = 0 ↔ f = g :=
  (U.compactExhaustion 0).continuousMapDist_eq_zero_iff.trans Subtype.ext_iff.symm

/-- Lower comparison of `comparisonDist U` against the `min 1 s_n` series. -/
theorem half_tsum_min_one_le_comparisonDist (f g : holomorphicFunctions U) :
    (1 / 2 : ℝ) *
      (∑' n : ℕ, (1 / 2 : ℝ) ^ (n + 1) *
        min 1 (dist (f.val.restrict (U.compactExhaustion 0 n))
          (g.val.restrict (U.compactExhaustion 0 n)))) ≤
      comparisonDist U f g :=
  (U.compactExhaustion 0).half_tsum_min_one_le_continuousMapDist f.val g.val

/-- Upper comparison of `comparisonDist U` against the `min 1 s_n` series. -/
theorem comparisonDist_le_tsum_min_one (f g : holomorphicFunctions U) :
    comparisonDist U f g ≤
      ∑' n : ℕ, (1 / 2 : ℝ) ^ (n + 1) *
        min 1 (dist (f.val.restrict (U.compactExhaustion 0 n))
          (g.val.restrict (U.compactExhaustion 0 n))) :=
  (U.compactExhaustion 0).continuousMapDist_le_tsum_min_one f.val g.val

/-- Quantitative single-stage bound for `comparisonDist U`. -/
theorem dist_restrict_lt_of_comparisonDist_lt {f g : holomorphicFunctions U} {n : ℕ} {ε : ℝ}
    (hε : 0 < ε) (h : comparisonDist U f g < (1 / 2 : ℝ) ^ (n + 1) * (ε / (1 + ε))) :
    dist (f.val.restrict (U.compactExhaustion 0 n))
      (g.val.restrict (U.compactExhaustion 0 n)) < ε :=
  (U.compactExhaustion 0).dist_restrict_lt_of_continuousMapDist_lt hε h

/-- Pointwise bound on ambient zero extensions over stage `n` when
`comparisonDist U f g < (1 / 2) ^ (n + 1) * (ε / (1 + ε))`. -/
theorem norm_extend_sub_lt_of_comparisonDist_lt {f g : holomorphicFunctions U} {n : ℕ} {ε : ℝ}
    (hε : 0 < ε) (h : comparisonDist U f g < (1 / 2 : ℝ) ^ (n + 1) * (ε / (1 + ε))) {z : ℂ}
    (hz : z ∈ closedBall (0 : ℂ) (n + 1) \ thickening (n + 1 : ℝ)⁻¹ (U : Set ℂ)ᶜ) :
    ‖extend f z - extend g z‖ < ε := by
  rw [← U.image_val_compactExhaustion 0 n] at hz
  obtain ⟨w, hw, rfl⟩ := hz
  rw [extend_apply, extend_apply, ← dist_eq_norm]
  exact (U.compactExhaustion 0).dist_apply_lt_of_continuousMapDist_lt hε h hw

/-- Simplified head-plus-tail upper bound on `comparisonDist U`. -/
theorem comparisonDist_le_dist_restrict_add_half_pow_succ (f g : holomorphicFunctions U) (n : ℕ) :
    comparisonDist U f g ≤
      dist (f.val.restrict (U.compactExhaustion 0 n))
        (g.val.restrict (U.compactExhaustion 0 n)) + (1 / 2 : ℝ) ^ (n + 1) :=
  (U.compactExhaustion 0).continuousMapDist_le_dist_restrict_add_half_pow_succ f.val g.val n

/-- **Equality of uniformities on `holomorphicFunctions U` for any compact exhaustion.** For every
`K : CompactExhaustion U`, restricting `K.continuousMapDist` to `holomorphicFunctions U` generates
the exact inherited uniformity `𝓤 (holomorphicFunctions U)`. -/
theorem uniformity_eq_iInf_compactExhaustionContinuousMapDist (K : CompactExhaustion U) :
    𝓤 (holomorphicFunctions U) =
      ⨅ ε > 0, 𝓟 {fg : holomorphicFunctions U × holomorphicFunctions U |
        K.continuousMapDist fg.1.val fg.2.val < ε} := by
  rw [uniformity_subtype, K.uniformity_eq_iInf_continuousMapDist]
  simp only [Filter.comap_iInf, Filter.comap_principal]
  rfl

/-- **Equality of uniformities on `holomorphicFunctions U`.** The metric entourages of
`comparisonDist U` generate the exact inherited uniformity `𝓤 (holomorphicFunctions U)`. -/
theorem uniformity_eq_iInf_comparisonDist (U : Opens ℂ) :
    𝓤 (holomorphicFunctions U) =
      ⨅ ε > 0, 𝓟 {fg : holomorphicFunctions U × holomorphicFunctions U |
        comparisonDist U fg.1 fg.2 < ε} :=
  uniformity_eq_iInf_compactExhaustionContinuousMapDist (U.compactExhaustion 0)

/-- The `UniformSpace` constructed directly from `comparisonDist U` agrees with the inherited
subtype uniform structure on `holomorphicFunctions U`. -/
theorem uniformSpace_ofDist_comparisonDist (U : Opens ℂ) :
    UniformSpace.ofDist (comparisonDist U) (comparisonDist_self U)
      (comparisonDist_comm U) (comparisonDist_triangle U) = instUniformSpaceSubtype :=
  UniformSpace.ext (uniformity_eq_iInf_comparisonDist U).symm

/-- **Exhaustion independence on `holomorphicFunctions U`.** Any compact exhaustion `K` of `U`
induces the same uniform space on `holomorphicFunctions U` as the inherited compact-convergence
uniformity. -/
theorem uniformSpace_ofDist_compactExhaustionContinuousMapDist (K : CompactExhaustion U) :
    UniformSpace.ofDist (fun f g : holomorphicFunctions U ↦ K.continuousMapDist f.val g.val)
      (fun f ↦ K.continuousMapDist_self f.val)
      (fun f g ↦ K.continuousMapDist_comm f.val g.val)
      (fun f g h ↦ K.continuousMapDist_triangle f.val g.val h.val) =
      instUniformSpaceSubtype :=
  UniformSpace.ext (uniformity_eq_iInf_compactExhaustionContinuousMapDist K).symm

/-- Explicit `MetricSpace` packaging of `comparisonDist U` on `holomorphicFunctions U`, pulled back
from `(U.compactExhaustion 0).continuousMapMetricSpace` along `Subtype.val`, with `toUniformSpace`
definitionally equal to the inherited `instUniformSpaceSubtype`. Not registered as an instance. -/
@[expose, instance_reducible]
def comparisonMetricSpace (U : Opens ℂ) : MetricSpace (holomorphicFunctions U) :=
  let := (U.compactExhaustion 0).continuousMapMetricSpace (Y := ℂ)
  isUniformEmbedding_subtypeVal.comapMetricSpace Subtype.val

/-- Convergence in `holomorphicFunctions U` is equivalent to `comparisonDist U` tending to `0`. -/
theorem tendsto_iff_tendsto_comparisonDist {ι : Type*} {p : Filter ι}
    {F : ι → holomorphicFunctions U} {f : holomorphicFunctions U} :
    Tendsto F p (𝓝 f) ↔ Tendsto (fun i ↦ comparisonDist U (F i) f) p (𝓝 0) :=
  @tendsto_iff_dist_tendsto_zero _ _ (comparisonMetricSpace U).toPseudoMetricSpace F p f

/-- Convergence in `comparisonDist U` is locally uniform convergence of zero extensions on `U`. -/
theorem tendsto_comparisonDist_iff_tendstoLocallyUniformlyOn {ι : Type*} {p : Filter ι}
    {F : ι → holomorphicFunctions U} {f : holomorphicFunctions U} :
    Tendsto (fun i ↦ comparisonDist U (F i) f) p (𝓝 0) ↔
      TendstoLocallyUniformlyOn (fun i ↦ extend (F i)) (extend f) p U := by
  rw [← tendsto_iff_tendsto_comparisonDist, tendsto_iff_tendstoLocallyUniformlyOn]

/-- Convergence in `comparisonDist U` is uniform convergence of zero extensions on every compact
subset `K ⊆ U`. -/
theorem tendsto_comparisonDist_iff_forall_isCompact_tendstoUniformlyOn {ι : Type*} {p : Filter ι}
    {F : ι → holomorphicFunctions U} {f : holomorphicFunctions U} :
    Tendsto (fun i ↦ comparisonDist U (F i) f) p (𝓝 0) ↔
      ∀ K, IsCompact K → K ⊆ U → TendstoUniformlyOn (fun i ↦ extend (F i)) (extend f) p K := by
  rw [tendsto_comparisonDist_iff_tendstoLocallyUniformlyOn,
    tendstoLocallyUniformlyOn_iff_forall_isCompact U.isOpen]
  exact ⟨fun h K hK hKU ↦ h K hKU hK, fun h K hKU hK ↦ h K hK hKU⟩

/-- Filter-level Cauchy equivalence between `holomorphicFunctions U` and `comparisonDist U`. -/
theorem cauchy_map_iff_tendsto_comparisonDist {ι : Type*} {p : Filter ι}
    {F : ι → holomorphicFunctions U} :
    Cauchy (map F p) ↔
      p.NeBot ∧
        Tendsto (fun ij : ι × ι ↦ comparisonDist U (F ij.1) (F ij.2)) (p ×ˢ p) (𝓝 0) := by
  rw [← isUniformEmbedding_subtypeVal.isUniformInducing.cauchy_map_iff, Filter.map_map,
    (U.compactExhaustion 0).cauchy_map_iff_tendsto_continuousMapDist]
  simp only [Function.comp_apply, ← comparisonDist_def]

/-- Filter-level Cauchy equivalence on `holomorphicFunctions U` with `UniformCauchySeqOn` of the
zero extensions on every compact subset `K ⊆ U`. -/
theorem cauchy_map_iff_forall_isCompact_uniformCauchySeqOn {ι : Type*} {p : Filter ι}
    {F : ι → holomorphicFunctions U} :
    Cauchy (map F p) ↔
      p.NeBot ∧
        ∀ K, IsCompact K → K ⊆ U → UniformCauchySeqOn (fun i ↦ extend (F i)) p K := by
  rw [← isUniformEmbedding_subtypeVal.isUniformInducing.cauchy_map_iff, Filter.map_map,
    ContinuousMap.cauchy_map_iff_forall_isCompact_uniformCauchySeqOn]
  refine and_congr_right fun _ ↦ ⟨fun h K hK hKU ↦ ?_, fun h s hs ↦ ?_⟩
  · have hpre : IsCompact (((↑) : U → ℂ) ⁻¹' K) :=
      Topology.IsInducing.subtypeVal.isCompact_preimage' hK (by rwa [Subtype.range_coe])
    have hc := h _ hpre
    intro u hu
    exact (hc u hu).mono fun ij hij z hz ↦ by
      simpa only [Function.comp_apply, extend_apply _ ⟨z, hKU hz⟩] using hij ⟨z, hKU hz⟩ hz
  · have himg : IsCompact (((↑) : U → ℂ) '' s) := hs.image continuous_subtypeVal
    have hsub : ((↑) : U → ℂ) '' s ⊆ U := by rintro _ ⟨z, -, rfl⟩; exact z.property
    simpa only [Function.comp_def, extend_apply] using
      ((h _ himg hsub).comp ((↑) : U → ℂ)).mono (subset_preimage_image ((↑) : U → ℂ) s)

/-- Directed-net `CauchySeq` in `holomorphicFunctions U` is equivalent to the metric Cauchy
condition for `comparisonDist U`. -/
theorem cauchySeq_iff_comparisonDist {ι : Type*} [Nonempty ι] [SemilatticeSup ι]
    {u : ι → holomorphicFunctions U} :
    CauchySeq u ↔ ∀ ε > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N, comparisonDist U (u m) (u n) < ε :=
  @Metric.cauchySeq_iff _ _ (comparisonMetricSpace U).toPseudoMetricSpace _ _ u

/-- Directed-net `CauchySeq` in `holomorphicFunctions U` is equivalent to `UniformCauchySeqOn` of
the zero extensions on every compact subset `K ⊆ U`. -/
theorem cauchySeq_iff_forall_isCompact_uniformCauchySeqOn {ι : Type*} [Nonempty ι]
    [SemilatticeSup ι] {u : ι → holomorphicFunctions U} :
    CauchySeq u ↔
      ∀ K, IsCompact K → K ⊆ U → UniformCauchySeqOn (fun n ↦ extend (u n)) atTop K := by
  rw [CauchySeq, cauchy_map_iff_forall_isCompact_uniformCauchySeqOn,
    and_iff_right (atTop_neBot (α := ι))]

/-- **Completeness of `comparisonDist U` on `holomorphicFunctions U`.** Every directed net in
`holomorphicFunctions U` that is Cauchy with respect to `comparisonDist U` converges in
`comparisonDist U` to a holomorphic function on `U`. -/
theorem exists_tendsto_comparisonDist_of_cauchy {ι : Type*} [Nonempty ι] [SemilatticeSup ι]
    {u : ι → holomorphicFunctions U}
    (hc : ∀ ε > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N, comparisonDist U (u m) (u n) < ε) :
    ∃ f : holomorphicFunctions U, Tendsto (fun n ↦ comparisonDist U (u n) f) atTop (𝓝 0) := by
  obtain ⟨f, hf⟩ := cauchySeq_tendsto_of_complete (cauchySeq_iff_comparisonDist.mpr hc)
  exact ⟨f, tendsto_iff_tendsto_comparisonDist.mp hf⟩

end ComparisonDist

section UniformContinuity

variable {U : Opens ℂ}

/-- The `ε`-`δ` uniform-continuity condition for compact restriction
`holomorphicFunctions U → C(K, ℂ)` with respect to `comparisonDist U`. -/
theorem exists_pos_forall_norm_restrictContinuousMap_sub_lt {K : Set ℂ} [CompactSpace K]
    (hKU : K ⊆ U) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ f g : holomorphicFunctions U, comparisonDist U f g < δ →
      ‖restrictContinuousMap hKU f - restrictContinuousMap hKU g‖ < ε := by
  let := comparisonMetricSpace U
  obtain ⟨δ, hδ, h⟩ :=
    Metric.uniformContinuous_iff.mp (uniformContinuous_restrictContinuousMap hKU) ε hε
  refine ⟨δ, hδ, fun f g hfg ↦ ?_⟩
  simpa only [← dist_eq_norm] using h hfg

/-- The `ε`-`η` uniform-continuity condition for `deriv` with respect to `comparisonDist U`: for
every `ε > 0`, sufficiently `comparisonDist U`-close holomorphic functions have
`comparisonDist U`-close derivatives. -/
theorem exists_pos_forall_comparisonDist_deriv_lt {ε : ℝ} (hε : 0 < ε) :
    ∃ η > 0, ∀ f g : holomorphicFunctions U,
      comparisonDist U f g < η → comparisonDist U (deriv f) (deriv g) < ε := by
  have huc := ContinuousLinearMap.uniformContinuous (E₁ := holomorphicFunctions U)
    (E₂ := holomorphicFunctions U) deriv
  let := comparisonMetricSpace U
  obtain ⟨η, hη, h⟩ := Metric.uniformContinuous_iff.mp huc ε hε
  exact ⟨η, hη, fun f g hfg ↦ h hfg⟩

end UniformContinuity

section Checks

/-- On an empty open set `U` (in particular `U = ⊥`), the comparison distance between any two
holomorphic functions is `0`. -/
@[simp]
theorem comparisonDist_of_isEmpty {U : Opens ℂ} [IsEmpty U] (f g : holomorphicFunctions U) :
    comparisonDist U f g = 0 :=
  (U.compactExhaustion 0).continuousMapDist_of_isEmpty f.val g.val

/-- When stage `0` of `U.compactExhaustion 0` is nonempty, shifting any
`f : holomorphicFunctions U` by a constant `c : ℂ` moves it by `‖c‖ / (1 + ‖c‖)` in
`comparisonDist U`. -/
theorem comparisonDist_add_algebraMap_of_nonempty {U : Opens ℂ}
    (hU : (U.compactExhaustion 0 0).Nonempty) (f : holomorphicFunctions U) (c : ℂ) :
    comparisonDist U (f + algebraMap ℂ (holomorphicFunctions U) c) f = ‖c‖ / (1 + ‖c‖) := by
  rw [comparisonDist_def, Subalgebra.coe_add, Subalgebra.coe_algebraMap,
    ContinuousMap.algebraMap_eq_const, Algebra.algebraMap_self_apply]
  exact (U.compactExhaustion 0).continuousMapDist_add_const_of_nonempty hU f.val c

/-- When stage `0` of `U.compactExhaustion 0` is nonempty, the comparison distance between
constant holomorphic functions `a` and `b` is `dist a b / (1 + dist a b)`. -/
theorem comparisonDist_algebraMap_of_nonempty {U : Opens ℂ}
    (hU : (U.compactExhaustion 0 0).Nonempty) (a b : ℂ) :
    comparisonDist U (algebraMap ℂ (holomorphicFunctions U) a)
      (algebraMap ℂ (holomorphicFunctions U) b) = dist a b / (1 + dist a b) := by
  simp_rw [comparisonDist_def, Subalgebra.coe_algebraMap, ContinuousMap.algebraMap_eq_const,
    Algebra.algebraMap_self_apply]
  exact (U.compactExhaustion 0).continuousMapDist_const_of_nonempty hU a b

/-- When stage `0` of `U.compactExhaustion 0` is nonempty, holomorphic functions differing by `1`
have comparison distance `1 / 2`. -/
theorem comparisonDist_add_one_of_nonempty {U : Opens ℂ}
    (hU : (U.compactExhaustion 0 0).Nonempty) (f : holomorphicFunctions U) :
    comparisonDist U (f + 1) f = 1 / 2 := by
  simpa only [map_one, norm_one, show (1 : ℝ) / (1 + 1) = 1 / 2 by norm_num] using
    comparisonDist_add_algebraMap_of_nonempty hU f 1

/-- When stage `0` of `U.compactExhaustion 0` is nonempty, the constant functions `1` and `0`
have comparison distance `1 / 2`. -/
theorem comparisonDist_one_zero_of_nonempty {U : Opens ℂ}
    (hU : (U.compactExhaustion 0 0).Nonempty) :
    comparisonDist U 1 0 = 1 / 2 := by
  simpa only [zero_add] using comparisonDist_add_one_of_nonempty hU 0

/-- Sharpness of the `1 / 2` comparison constant in `half_tsum_min_one_le_comparisonDist`: when
stage `0` of `U.compactExhaustion 0` is nonempty, `1` and `0` achieve equality. -/
theorem half_tsum_min_one_eq_comparisonDist_one_zero {U : Opens ℂ}
    (hU : (U.compactExhaustion 0 0).Nonempty) :
    (1 / 2 : ℝ) *
      (∑' n : ℕ, (1 / 2 : ℝ) ^ (n + 1) *
        min 1 (dist ((1 : holomorphicFunctions U).val.restrict (U.compactExhaustion 0 n))
          ((0 : holomorphicFunctions U).val.restrict (U.compactExhaustion 0 n)))) =
      comparisonDist U 1 0 := by
  rw [comparisonDist_def, Subalgebra.coe_one, Subalgebra.coe_zero,
    ← ContinuousMap.const_one, ← ContinuousMap.const_zero]
  exact (U.compactExhaustion 0).half_tsum_min_one_eq_continuousMapDist_const hU (by simp)

/-- On the whole complex plane `⊤`, constant entire functions `a` and `b` have comparison distance
`dist a b / (1 + dist a b)`. -/
@[simp]
theorem comparisonDist_algebraMap_top (a b : ℂ) :
    comparisonDist ⊤ (algebraMap ℂ (holomorphicFunctions ⊤) a)
      (algebraMap ℂ (holomorphicFunctions ⊤) b) = dist a b / (1 + dist a b) :=
  comparisonDist_algebraMap_of_nonempty
    ((⊤ : Opens ℂ).nonempty_compactExhaustion_of_ball_subset (subset_univ _) 0) a b

/-- On `ℂ`, the constant entire function `1 / (n + 1)` has comparison distance `1 / (n + 2)` to
`0`. -/
theorem comparisonDist_algebraMap_one_div_natCast_add_one_zero_top (n : ℕ) :
    comparisonDist ⊤ (algebraMap ℂ (holomorphicFunctions ⊤) (1 / (n + 1 : ℂ))) 0 =
      1 / (n + 2 : ℝ) := by
  have hnorm : ‖((n : ℂ) + 1)‖ = (n : ℝ) + 1 := by
    simpa only [Nat.cast_add, Nat.cast_one] using Complex.norm_natCast (n + 1)
  rw [← RingHom.map_zero (algebraMap ℂ (holomorphicFunctions ⊤)), comparisonDist_algebraMap_top,
    dist_zero_right, norm_div, norm_one, hnorm]
  have : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have : (0 : ℝ) < (n : ℝ) + 2 := by positivity
  field_simp
  ring

/-- On `ℂ`, the constant entire functions `1 / (n + 1)` tend to `0` in `holomorphicFunctions ⊤`. -/
theorem tendsto_algebraMap_one_div_natCast_add_one_top :
    Tendsto (fun n : ℕ ↦ algebraMap ℂ (holomorphicFunctions ⊤) (1 / (n + 1 : ℂ))) atTop (𝓝 0) := by
  rw [tendsto_iff_tendsto_comparisonDist]
  simp_rw [comparisonDist_algebraMap_one_div_natCast_add_one_zero_top]
  simpa only [Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two] using
    (tendsto_add_atTop_iff_nat 1).mpr (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

end Checks

end TauCeti.HolomorphicFunctions
