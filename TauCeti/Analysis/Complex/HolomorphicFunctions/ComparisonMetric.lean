/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.HolomorphicFunctions.Basic
public import TauCeti.Topology.ContinuousMap.ExhaustionMetric
public import TauCeti.Topology.MetricSpace.ProperSpace
import TauCeti.Analysis.SpecificLimits.HalfPowSucc

/-!
# Explicit comparison metric on `C(U, ℂ)` and `holomorphicFunctions U`

For an open subset `U : Opens ℂ` of the complex plane, `U.compactExhaustion 0` exhausts `U` by the
compact sets cutting out `closedBall 0 (n + 1) \ thickening (n + 1)⁻¹ Uᶜ`. Specializing
`CompactExhaustion.continuousMapDist` to this canonical exhaustion gives an explicit bounded metric
`HolomorphicFunctions.continuousMapDist U` on `C(U, ℂ)` and its restriction
`HolomorphicFunctions.comparisonDist U` on the closed subalgebra `holomorphicFunctions U`:
$$
d(f, g) = \sum_{n = 0}^{\infty} 2^{-(n + 1)} \frac{s_n(f, g)}{1 + s_n(f, g)},
\qquad s_n(f, g) = \sup_{z \in K_n} |f(z) - g(z)|.
$$
Neither `C(U, ℂ)` nor `holomorphicFunctions U` is given a `MetricSpace` typeclass instance, so
their canonical compact-convergence uniformities remain the unique active uniform structures.
Instead, `uniformity_eq_iInf_comparisonDist` proves that `comparisonDist U` generates the exact
inherited uniformity on `holomorphicFunctions U` (independently of the exhaustion),
`comparisonMetricSpace U` packages the compatible `MetricSpace` structure when metric theorems are
needed, restriction `holomorphicFunctions U →ₐ[ℂ] C(K, ℂ)` to any compact `K ⊆ U` is uniformly
continuous with an explicit modulus, and `comparisonDist U` is complete on `holomorphicFunctions U`.

Closed-form evaluations on `U = ⊥`, on domains with nonempty exhaustion stages, and on `U = ⊤`
illustrate the normalization of the bounded metric and the sharpness of the `1 / 2` comparison
constant against the `min 1 s_n` series.

## References

* Armin Rainer, *Advanced Complex Analysis*, §11, equation (11.2) and Exercise 19.
* Walter Rudin, *Real and Complex Analysis*, 3rd ed., §10.28 and Theorem 13.3.
-/

public noncomputable section

open Filter Function Metric Set Topology TopologicalSpace UniformSpace
open scoped Uniformity

namespace TauCeti.HolomorphicFunctions

section ContinuousMapDist

/-- Explicit comparison distance on `C(U, ℂ)` built from the canonical exhaustion
`U.compactExhaustion 0` whose stage `n` cuts out
`closedBall 0 (n + 1) \ thickening (n + 1)⁻¹ Uᶜ`. Not registered as a metric instance. -/
def continuousMapDist (U : Opens ℂ) (f g : C(U, ℂ)) : ℝ :=
  (U.compactExhaustion 0).continuousMapDist f g

/-- `continuousMapDist U` is `CompactExhaustion.continuousMapDist` at `U.compactExhaustion 0`. -/
theorem continuousMapDist_def (U : Opens ℂ) (f g : C(U, ℂ)) :
    continuousMapDist U f g = (U.compactExhaustion 0).continuousMapDist f g := (rfl)

/-- Series expansion of `continuousMapDist U f g` over the stages of `U.compactExhaustion 0`. -/
theorem continuousMapDist_eq_tsum (U : Opens ℂ) (f g : C(U, ℂ)) :
    continuousMapDist U f g =
      ∑' n : ℕ, (1 / 2 : ℝ) ^ (n + 1) *
        (dist (f.restrict (U.compactExhaustion 0 n)) (g.restrict (U.compactExhaustion 0 n)) /
          (1 + dist (f.restrict (U.compactExhaustion 0 n))
            (g.restrict (U.compactExhaustion 0 n)))) :=
  (U.compactExhaustion 0).continuousMapDist_def f g

/-- `continuousMapDist U` vanishes on the diagonal. -/
@[simp]
theorem continuousMapDist_self (U : Opens ℂ) (f : C(U, ℂ)) : continuousMapDist U f f = 0 :=
  (U.compactExhaustion 0).continuousMapDist_self f

/-- `continuousMapDist U` is symmetric. -/
theorem continuousMapDist_comm (U : Opens ℂ) (f g : C(U, ℂ)) :
    continuousMapDist U f g = continuousMapDist U g f :=
  (U.compactExhaustion 0).continuousMapDist_comm f g

/-- `continuousMapDist U` is nonnegative. -/
theorem continuousMapDist_nonneg (U : Opens ℂ) (f g : C(U, ℂ)) : 0 ≤ continuousMapDist U f g :=
  (U.compactExhaustion 0).continuousMapDist_nonneg f g

/-- `continuousMapDist U` is strictly bounded above by `1`. -/
theorem continuousMapDist_lt_one (U : Opens ℂ) (f g : C(U, ℂ)) : continuousMapDist U f g < 1 :=
  (U.compactExhaustion 0).continuousMapDist_lt_one f g

/-- `continuousMapDist U` is bounded above by `1`. -/
theorem continuousMapDist_le_one (U : Opens ℂ) (f g : C(U, ℂ)) : continuousMapDist U f g ≤ 1 :=
  (U.compactExhaustion 0).continuousMapDist_le_one f g

/-- Triangle inequality for `continuousMapDist U`. -/
theorem continuousMapDist_triangle (U : Opens ℂ) (f g h : C(U, ℂ)) :
    continuousMapDist U f h ≤ continuousMapDist U f g + continuousMapDist U g h :=
  (U.compactExhaustion 0).continuousMapDist_triangle f g h

/-- `continuousMapDist U` separates distinct continuous maps on `U`. -/
@[simp]
theorem continuousMapDist_eq_zero_iff {U : Opens ℂ} {f g : C(U, ℂ)} :
    continuousMapDist U f g = 0 ↔ f = g :=
  (U.compactExhaustion 0).continuousMapDist_eq_zero_iff

/-- **Equality of uniformities on `C(U, ℂ)`.** The comparison distance `continuousMapDist U`
induces the exact compact-convergence uniformity on `C(U, ℂ)`. -/
theorem uniformity_continuousMap_eq_iInf_continuousMapDist (U : Opens ℂ) :
    𝓤 C(U, ℂ) = ⨅ ε > 0, 𝓟 {fg : C(U, ℂ) × C(U, ℂ) | continuousMapDist U fg.1 fg.2 < ε} :=
  (U.compactExhaustion 0).uniformity_eq_iInf_continuousMapDist

/-- Compatible `MetricSpace` packaging on `C(U, ℂ)` with `toUniformSpace` definitionally equal to
`ContinuousMap.compactConvergenceUniformSpace`. Not registered as an instance. -/
@[instance_reducible]
def continuousMapMetricSpace (U : Opens ℂ) : MetricSpace C(U, ℂ) :=
  (U.compactExhaustion 0).continuousMapMetricSpace

end ContinuousMapDist

section ComparisonDist

variable {U : Opens ℂ}

/-- Explicit comparison distance on `holomorphicFunctions U`, obtained by restricting
`continuousMapDist U` along the subalgebra inclusion into `C(U, ℂ)`. Not registered as a metric
instance. -/
def comparisonDist (U : Opens ℂ) (f g : holomorphicFunctions U) : ℝ :=
  continuousMapDist U f.val g.val

/-- `comparisonDist U` is the restriction of `continuousMapDist U` to `holomorphicFunctions U`. -/
theorem comparisonDist_def (U : Opens ℂ) (f g : holomorphicFunctions U) :
    comparisonDist U f g = continuousMapDist U f.val g.val := (rfl)

/-- Series expansion of `comparisonDist U f g` over the stages of `U.compactExhaustion 0`. -/
theorem comparisonDist_eq_tsum (U : Opens ℂ) (f g : holomorphicFunctions U) :
    comparisonDist U f g =
      ∑' n : ℕ, (1 / 2 : ℝ) ^ (n + 1) *
        (dist (f.val.restrict (U.compactExhaustion 0 n))
          (g.val.restrict (U.compactExhaustion 0 n)) /
          (1 + dist (f.val.restrict (U.compactExhaustion 0 n))
            (g.val.restrict (U.compactExhaustion 0 n)))) :=
  continuousMapDist_eq_tsum U f.val g.val

/-- `comparisonDist U` vanishes on the diagonal. -/
@[simp]
theorem comparisonDist_self (U : Opens ℂ) (f : holomorphicFunctions U) :
    comparisonDist U f f = 0 :=
  continuousMapDist_self U f.val

/-- `comparisonDist U` is symmetric. -/
theorem comparisonDist_comm (U : Opens ℂ) (f g : holomorphicFunctions U) :
    comparisonDist U f g = comparisonDist U g f :=
  continuousMapDist_comm U f.val g.val

/-- `comparisonDist U` is nonnegative. -/
theorem comparisonDist_nonneg (U : Opens ℂ) (f g : holomorphicFunctions U) :
    0 ≤ comparisonDist U f g :=
  continuousMapDist_nonneg U f.val g.val

/-- `comparisonDist U` is strictly bounded above by `1`. -/
theorem comparisonDist_lt_one (U : Opens ℂ) (f g : holomorphicFunctions U) :
    comparisonDist U f g < 1 :=
  continuousMapDist_lt_one U f.val g.val

/-- `comparisonDist U` is bounded above by `1`. -/
theorem comparisonDist_le_one (U : Opens ℂ) (f g : holomorphicFunctions U) :
    comparisonDist U f g ≤ 1 :=
  continuousMapDist_le_one U f.val g.val

/-- Triangle inequality for `comparisonDist U`. -/
theorem comparisonDist_triangle (U : Opens ℂ) (f g h : holomorphicFunctions U) :
    comparisonDist U f h ≤ comparisonDist U f g + comparisonDist U g h :=
  continuousMapDist_triangle U f.val g.val h.val

/-- `comparisonDist U` separates distinct holomorphic functions on `U`. -/
@[simp]
theorem comparisonDist_eq_zero_iff {f g : holomorphicFunctions U} :
    comparisonDist U f g = 0 ↔ f = g :=
  continuousMapDist_eq_zero_iff.trans Subtype.ext_iff.symm

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
theorem comparisonDist_le_dist_restrict_add_pow_half (f g : holomorphicFunctions U) (n : ℕ) :
    comparisonDist U f g ≤
      dist (f.val.restrict (U.compactExhaustion 0 n))
        (g.val.restrict (U.compactExhaustion 0 n)) + (1 / 2 : ℝ) ^ (n + 1) :=
  (U.compactExhaustion 0).continuousMapDist_le_dist_restrict_add_pow_half f.val g.val n

/-- **Equality of uniformities on `holomorphicFunctions U` for any compact exhaustion.** For every
`K : CompactExhaustion U`, restricting `K.continuousMapDist` to `holomorphicFunctions U` generates
the exact inherited uniformity `𝓤 (holomorphicFunctions U)`. -/
theorem uniformity_eq_iInf_exhaustion_continuousMapDist (K : CompactExhaustion U) :
    𝓤 (holomorphicFunctions U) =
      ⨅ ε > 0, 𝓟 {fg : holomorphicFunctions U × holomorphicFunctions U |
        K.continuousMapDist fg.1.val fg.2.val < ε} := by
  change Filter.comap (Prod.map Subtype.val Subtype.val) (𝓤 C(U, ℂ)) = _
  rw [K.uniformity_eq_iInf_continuousMapDist]
  simp only [Filter.comap_iInf, Filter.comap_principal]
  rfl

/-- **Equality of uniformities on `holomorphicFunctions U`.** The metric entourages of
`comparisonDist U` generate the exact inherited uniformity `𝓤 (holomorphicFunctions U)`. -/
theorem uniformity_eq_iInf_comparisonDist (U : Opens ℂ) :
    𝓤 (holomorphicFunctions U) =
      ⨅ ε > 0, 𝓟 {fg : holomorphicFunctions U × holomorphicFunctions U |
        comparisonDist U fg.1 fg.2 < ε} :=
  uniformity_eq_iInf_exhaustion_continuousMapDist (U.compactExhaustion 0)

/-- The `UniformSpace` constructed directly from `comparisonDist U` agrees with the inherited
subtype uniform structure on `holomorphicFunctions U`. -/
theorem uniformSpace_ofDist_comparisonDist (U : Opens ℂ) :
    UniformSpace.ofDist (comparisonDist U) (comparisonDist_self U)
      (comparisonDist_comm U) (comparisonDist_triangle U) = instUniformSpaceSubtype :=
  UniformSpace.ext (uniformity_eq_iInf_comparisonDist U).symm

/-- **Exhaustion independence on `holomorphicFunctions U`.** Any compact exhaustion `K` of `U`
induces the same uniform space on `holomorphicFunctions U` as `comparisonDist U`. -/
theorem uniformSpace_ofDist_exhaustion_eq (K : CompactExhaustion U) :
    UniformSpace.ofDist (fun f g : holomorphicFunctions U ↦ K.continuousMapDist f.val g.val)
      (fun f ↦ K.continuousMapDist_self f.val)
      (fun f g ↦ K.continuousMapDist_comm f.val g.val)
      (fun f g h ↦ K.continuousMapDist_triangle f.val g.val h.val) =
      instUniformSpaceSubtype :=
  UniformSpace.ext (uniformity_eq_iInf_exhaustion_continuousMapDist K).symm

/-- Explicit `MetricSpace` packaging of `comparisonDist U` on `holomorphicFunctions U`, with
`toUniformSpace` definitionally equal to the inherited `instUniformSpaceSubtype`. Not registered as
an instance. -/
@[instance_reducible]
def comparisonMetricSpace (U : Opens ℂ) : MetricSpace (holomorphicFunctions U) where
  dist := comparisonDist U
  dist_self := comparisonDist_self U
  dist_comm := comparisonDist_comm U
  dist_triangle := comparisonDist_triangle U
  eq_of_dist_eq_zero := comparisonDist_eq_zero_iff.mp
  toUniformSpace := instUniformSpaceSubtype
  uniformity_dist := uniformity_eq_iInf_comparisonDist U

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
  have hind : CauchySeq u ↔ CauchySeq (fun n ↦ (u n).val) :=
    cauchySeq_iff_comparisonDist.trans
      (U.compactExhaustion 0).cauchySeq_iff_continuousMapDist.symm
  rw [hind, ContinuousMap.cauchySeq_iff_forall_isCompact_uniformCauchySeqOn]
  constructor
  · intro h K hK hKU
    have hpre : IsCompact (((↑) : U → ℂ) ⁻¹' K) :=
      Topology.IsInducing.subtypeVal.isCompact_preimage' hK (by rwa [Subtype.range_coe])
    have hc := h _ hpre
    rw [Metric.uniformCauchySeqOn_iff] at hc ⊢
    intro ε hε
    obtain ⟨N, hN⟩ := hc ε hε
    refine ⟨N, fun m hm n hn z hz ↦ ?_⟩
    simpa only [extend_apply _ ⟨z, hKU hz⟩] using hN m hm n hn ⟨z, hKU hz⟩ hz
  · intro h s hs
    have himg : IsCompact (((↑) : U → ℂ) '' s) := hs.image continuous_subtype_val
    have hsub : ((↑) : U → ℂ) '' s ⊆ U := by rintro _ ⟨z, -, rfl⟩; exact z.2
    have hc := h _ himg hsub
    rw [Metric.uniformCauchySeqOn_iff] at hc ⊢
    intro ε hε
    obtain ⟨N, hN⟩ := hc ε hε
    refine ⟨N, fun m hm n hn z hz ↦ ?_⟩
    simpa only [extend_apply _ z] using hN m hm n hn z.1 (mem_image_of_mem _ hz)

/-- **Completeness of `comparisonDist U` on `holomorphicFunctions U`.** Every sequence in
`holomorphicFunctions U` that is Cauchy with respect to `comparisonDist U` converges in
`comparisonDist U` to a holomorphic function on `U`. -/
theorem exists_tendsto_comparisonDist_of_cauchy {u : ℕ → holomorphicFunctions U}
    (hc : ∀ ε > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N, comparisonDist U (u m) (u n) < ε) :
    ∃ f : holomorphicFunctions U, Tendsto (fun n ↦ comparisonDist U (u n) f) atTop (𝓝 0) := by
  obtain ⟨f, hf⟩ := cauchySeq_tendsto_of_complete (cauchySeq_iff_comparisonDist.mpr hc)
  exact ⟨f, tendsto_iff_tendsto_comparisonDist.mp hf⟩

end ComparisonDist

section CompactRestriction

variable {U : Opens ℂ}

/-- Restriction of holomorphic functions on `U` to continuous functions `C(K, ℂ)` on any subset
`K ⊆ U`, as a complex algebra homomorphism. -/
def restrictContinuousMap {K : Set ℂ} (hKU : K ⊆ U) : holomorphicFunctions U →ₐ[ℂ] C(K, ℂ) :=
  (ContinuousMap.compRightAlgHom ℂ ℂ ⟨Set.inclusion hKU, continuous_inclusion hKU⟩).comp
    (holomorphicFunctions U).val

/-- Evaluating `restrictContinuousMap hKU f` at `z : K` gives `f.val (Set.inclusion hKU z)`. -/
@[simp]
theorem restrictContinuousMap_apply {K : Set ℂ} (hKU : K ⊆ U) (f : holomorphicFunctions U)
    (z : K) : restrictContinuousMap hKU f z = f.val (Set.inclusion hKU z) := (rfl)

/-- Evaluating `restrictContinuousMap hKU f` at `z : K` agrees with `extend f z`. -/
theorem restrictContinuousMap_apply_eq_extend {K : Set ℂ} (hKU : K ⊆ U)
    (f : holomorphicFunctions U) (z : K) : restrictContinuousMap hKU f z = extend f z :=
  (extend_apply f ⟨z.1, hKU z.2⟩).symm

/-- Restriction to any subset `K ⊆ U` is uniformly continuous into `C(K, ℂ)` (in particular for
the supremum norm when `K` is compact). -/
theorem uniformContinuous_restrictContinuousMap {K : Set ℂ} (hKU : K ⊆ U) :
    UniformContinuous (restrictContinuousMap hKU) :=
  (ContinuousMap.uniformContinuous_comp_left
    (⟨Set.inclusion hKU, continuous_inclusion hKU⟩ : C(K, U))).comp uniformContinuous_subtype_val

/-- Quantitative modulus of uniform continuity for compact restriction
`holomorphicFunctions U → C(K, ℂ)` with respect to `comparisonDist U`. -/
theorem exists_pos_forall_norm_restrictContinuousMap_sub_lt {K : Set ℂ} [CompactSpace K]
    (hKU : K ⊆ U) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ f g : holomorphicFunctions U, comparisonDist U f g < δ →
      ‖restrictContinuousMap hKU f - restrictContinuousMap hKU g‖ < ε := by
  have hK : IsCompact K := isCompact_iff_compactSpace.mpr ‹_›
  have hpre : IsCompact (((↑) : U → ℂ) ⁻¹' K) :=
    Topology.IsInducing.subtypeVal.isCompact_preimage' hK (by rwa [Subtype.range_coe])
  obtain ⟨n, hn⟩ := (U.compactExhaustion 0).exists_superset_of_isCompact hpre
  refine ⟨(1 / 2 : ℝ) ^ (n + 1) * (ε / (1 + ε)), by positivity, fun f g hfg ↦ ?_⟩
  rw [ContinuousMap.norm_lt_iff _ hε]
  intro z
  have hmem : (⟨z.1, hKU z.2⟩ : U) ∈ U.compactExhaustion 0 n := hn z.2
  simpa only [ContinuousMap.sub_apply, restrictContinuousMap_apply, ← dist_eq_norm] using
    (U.compactExhaustion 0).dist_apply_lt_of_continuousMapDist_lt hε hfg hmem

end CompactRestriction

section Checks

/-- On any empty open set `U`, `holomorphicFunctions U` has a unique element (`0`). -/
instance instUniqueOfIsEmpty {U : Opens ℂ} [IsEmpty U] : Unique (holomorphicFunctions U) :=
  uniqueOfSubsingleton 0

/-- On `⊥`, `holomorphicFunctions ⊥` has a unique element (`0`). -/
instance instUniqueBot : Unique (holomorphicFunctions ⊥) :=
  have : IsEmpty (⊥ : Opens ℂ) := ⟨fun x ↦ x.2⟩
  inferInstance

/-- On an empty open set `U`, the comparison distance between any two holomorphic functions is
`0`. -/
@[simp]
theorem comparisonDist_of_isEmpty {U : Opens ℂ} [IsEmpty U] (f g : holomorphicFunctions U) :
    comparisonDist U f g = 0 :=
  (U.compactExhaustion 0).continuousMapDist_of_isEmpty f.val g.val

/-- On `⊥`, the comparison distance between any two holomorphic functions is `0`. -/
@[simp]
theorem comparisonDist_bot (f g : holomorphicFunctions ⊥) : comparisonDist ⊥ f g = 0 := by
  have : IsEmpty (⊥ : Opens ℂ) := ⟨fun x ↦ x.2⟩
  exact comparisonDist_of_isEmpty f g

/-- When every stage of `U.compactExhaustion 0` is nonempty, shifting any
`f : holomorphicFunctions U` by a constant `c : ℂ` moves it by `‖c‖ / (1 + ‖c‖)` in
`comparisonDist U`. -/
theorem comparisonDist_add_algebraMap_of_forall_nonempty {U : Opens ℂ}
    (hU : ∀ n, (U.compactExhaustion 0 n).Nonempty) (f : holomorphicFunctions U) (c : ℂ) :
    comparisonDist U (f + algebraMap ℂ (holomorphicFunctions U) c) f = ‖c‖ / (1 + ‖c‖) := by
  refine (U.compactExhaustion 0).continuousMapDist_eq_of_forall_dist_restrict_eq fun n ↦ ?_
  have : Nonempty (U.compactExhaustion 0 n) := (hU n).to_subtype
  have hconst : ∀ z : U.compactExhaustion 0 n,
      dist (((f + algebraMap ℂ (holomorphicFunctions U) c).val.restrict
        (U.compactExhaustion 0 n)) z) ((f.val.restrict (U.compactExhaustion 0 n)) z) = ‖c‖ := by
    intro z
    change dist (f.val z.1 + c) (f.val z.1) = ‖c‖
    simp [dist_eq_norm]
  rw [ContinuousMap.dist_eq_iSup]
  simp_rw [hconst, ciSup_const]

/-- When every stage of `U.compactExhaustion 0` is nonempty, the comparison distance between
constant holomorphic functions `a` and `b` is `dist a b / (1 + dist a b)`. -/
theorem comparisonDist_algebraMap_of_forall_nonempty {U : Opens ℂ}
    (hU : ∀ n, (U.compactExhaustion 0 n).Nonempty) (a b : ℂ) :
    comparisonDist U (algebraMap ℂ (holomorphicFunctions U) a)
      (algebraMap ℂ (holomorphicFunctions U) b) = dist a b / (1 + dist a b) := by
  have heq : algebraMap ℂ (holomorphicFunctions U) a =
      algebraMap ℂ (holomorphicFunctions U) b + algebraMap ℂ (holomorphicFunctions U) (a - b) := by
    rw [← RingHom.map_add, add_sub_cancel]
  rw [heq, comparisonDist_add_algebraMap_of_forall_nonempty hU, dist_eq_norm]

/-- When every stage of `U.compactExhaustion 0` is nonempty, holomorphic functions differing by `1`
have comparison distance `1 / 2`. -/
theorem comparisonDist_add_one_of_forall_nonempty {U : Opens ℂ}
    (hU : ∀ n, (U.compactExhaustion 0 n).Nonempty) (f : holomorphicFunctions U) :
    comparisonDist U (f + 1) f = 1 / 2 := by
  simpa only [map_one, norm_one, show (1 : ℝ) / (1 + 1) = 1 / 2 by norm_num] using
    comparisonDist_add_algebraMap_of_forall_nonempty hU f 1

/-- When every stage of `U.compactExhaustion 0` is nonempty, the constant functions `1` and `0`
have comparison distance `1 / 2`. -/
theorem comparisonDist_one_zero_of_forall_nonempty {U : Opens ℂ}
    (hU : ∀ n, (U.compactExhaustion 0 n).Nonempty) :
    comparisonDist U 1 0 = 1 / 2 := by
  simpa only [zero_add] using comparisonDist_add_one_of_forall_nonempty hU 0

/-- Sharpness of the `1 / 2` comparison constant in `half_tsum_min_one_le_comparisonDist`: when
every stage is nonempty, `1` and `0` have `min 1 s_n` series equal to `1` while
`comparisonDist U 1 0 = 1 / 2`. -/
theorem half_tsum_min_one_eq_comparisonDist_one_zero {U : Opens ℂ}
    (hU : ∀ n, (U.compactExhaustion 0 n).Nonempty) :
    (1 / 2 : ℝ) *
      (∑' n : ℕ, (1 / 2 : ℝ) ^ (n + 1) *
        min 1 (dist ((1 : holomorphicFunctions U).val.restrict (U.compactExhaustion 0 n))
          ((0 : holomorphicFunctions U).val.restrict (U.compactExhaustion 0 n)))) =
      comparisonDist U 1 0 := by
  have hd : ∀ n, dist ((1 : holomorphicFunctions U).val.restrict (U.compactExhaustion 0 n))
      ((0 : holomorphicFunctions U).val.restrict (U.compactExhaustion 0 n)) = 1 := by
    intro n
    have : Nonempty (U.compactExhaustion 0 n) := (hU n).to_subtype
    rw [ContinuousMap.dist_eq_iSup]
    simp [ciSup_const]
  rw [comparisonDist_one_zero_of_forall_nonempty hU]
  simp_rw [hd, min_self, mul_one, TauCeti.tsum_half_pow_succ, mul_one]

/-- On the whole complex plane `⊤`, constant entire functions `a` and `b` have comparison distance
`dist a b / (1 + dist a b)`. -/
@[simp]
theorem comparisonDist_algebraMap_top (a b : ℂ) :
    comparisonDist ⊤ (algebraMap ℂ (holomorphicFunctions ⊤) a)
      (algebraMap ℂ (holomorphicFunctions ⊤) b) = dist a b / (1 + dist a b) :=
  comparisonDist_algebraMap_of_forall_nonempty
    ((⊤ : Opens ℂ).nonempty_compactExhaustion_of_ball_subset (subset_univ _)) a b

/-- On `ℂ`, the constant entire function `1 / (n + 1)` has comparison distance `1 / (n + 2)` to
`0`. -/
theorem comparisonDist_inv_nat_add_one_zero_top (n : ℕ) :
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
theorem tendsto_algebraMap_inv_nat_add_one_top :
    Tendsto (fun n : ℕ ↦ algebraMap ℂ (holomorphicFunctions ⊤) (1 / (n + 1 : ℂ))) atTop (𝓝 0) := by
  rw [tendsto_iff_tendsto_comparisonDist]
  simp_rw [comparisonDist_inv_nat_add_one_zero_top]
  refine ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp
    (tendsto_add_atTop_nat 1)).congr fun n ↦ ?_
  simp only [Function.comp_apply, Nat.cast_add, Nat.cast_one]
  ring

end Checks

end TauCeti.HolomorphicFunctions
