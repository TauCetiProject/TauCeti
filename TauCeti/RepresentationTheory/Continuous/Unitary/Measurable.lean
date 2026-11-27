/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Group.Measure
public import TauCeti.RepresentationTheory.Continuous.Unitary.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Group.Action
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.Topology.UniformSpace.UniformApproximation

/-!
# Unitary representations with measurable matrix coefficients are strongly continuous

Let `G` be a locally compact group with a left Haar measure `ν`, and let `π` be a unitary
representation of `G` on a separable Hilbert space `V`. If every matrix coefficient
`g ↦ ⟪π g v, w⟫` is locally integrable for `ν` (for instance, almost everywhere strongly
measurable on compact sets, since it is bounded), then every orbit `g ↦ π g v` is continuous
(`ContRepresentation.IsUnitary.continuous_apply_of_locallyIntegrable_inner`).

No continuity of the action and no countability of `G` is assumed. Separability of `V` cannot be
dropped: the representation of `ℝ` on `ℓ²(ℝ)` by translation of the index has matrix coefficients
supported on countable sets, hence zero almost everywhere, but `‖π(t) δ₀ - δ₀‖ = √2` for `t ≠ 0`.

The proof follows the convolution argument. For `v ∈ V` and a compact set `K`, the Riesz
representation theorem gives a vector `u` with `⟪u, w⟫ = ∫ g in K, ⟪π g v, w⟫ ∂ν` for every `w`
(the weak integral of the orbit over `K`). Left invariance of `ν` gives
`⟪π k u, w⟫ = ∫ g in k • K, ⟪π g v, w⟫ ∂ν`, so
`‖π k u - u‖ ≤ (ν (k • K \ K) + ν (k⁻¹ • K \ K)) ‖v‖`, which tends to `0` as `k → 1`
(Mathlib's `tendsto_measure_smul_sdiff_isCompact_isClosed`): these averaged vectors have
continuous orbits. The vectors with continuous orbits form a closed subspace. A vector `w`
orthogonal to it has `∫ g in K, ⟪π g v, w⟫ ∂ν = 0` for every compact `K`, so the coefficient
`g ↦ ⟪π g v, w⟫` vanishes almost everywhere on a compact neighbourhood of `1`, for each `v` in a
countable dense set; at a common point `g`, `⟪π g v, w⟫ = 0` for every `v`, and `v = π g⁻¹ w`
gives `w = 0`.

## Main results

* `ContRepresentation.IsUnitary.continuous_apply_of_continuousAt_one`: an orbit of a unitary
  representation is continuous when it is continuous at `1`.
* `ContRepresentation.IsUnitary.isClosed_setOf_continuous_apply`: the vectors with continuous
  orbits form a closed set.
* `ContRepresentation.IsUnitary.continuous_apply_of_locallyIntegrable_inner`: measurable
  (locally integrable) matrix coefficients imply strong continuity on separable Hilbert spaces.
-/

public section

open MeasureTheory Topology Filter Set
open scoped InnerProductSpace ENNReal Pointwise

namespace ContRepresentation.IsUnitary

variable {𝕜 G V : Type*} [RCLike 𝕜] [Group G] [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
  {π : ContRepresentation 𝕜 G V}

section Topology

variable [TopologicalSpace G]

/-- An orbit of a unitary representation of a group is continuous as soon as it is continuous at
the identity. -/
theorem continuous_apply_of_continuousAt_one (hπ : π.IsUnitary) {v : V}
    (hv : ContinuousAt (fun g ↦ π g v) 1) [ContinuousMul G] : Continuous fun g ↦ π g v := by
  rw [continuous_iff_continuousAt]
  intro g₀
  have h₁ : Tendsto (fun g ↦ g₀⁻¹ * g) (𝓝 g₀) (𝓝 1) := by
    simpa using ((continuous_const_mul g₀⁻¹).tendsto g₀)
  have h₂ := (hv.tendsto.comp h₁).sub_const v
  rw [map_one, one_apply_eq_self, sub_self] at h₂
  have h₃ : Tendsto (fun g ↦ ‖π (g₀⁻¹ * g) v - v‖) (𝓝 g₀) (𝓝 0) := by
    simpa using h₂.norm
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  refine h₃.congr fun g ↦ ?_
  rw [← hπ.norm_map g₀, map_sub, ← mul_apply_eq_comp, ← map_mul, mul_inv_cancel_left]

/-- The vectors of a unitary representation whose orbits are continuous form a closed set. -/
theorem isClosed_setOf_continuous_apply (hπ : π.IsUnitary) :
    IsClosed {v : V | Continuous fun g ↦ π g v} := by
  refine isClosed_iff_clusterPt.2 fun v hv ↦ ?_
  have : (𝓝 v ⊓ 𝓟 {v : V | Continuous fun g ↦ π g v}).NeBot := hv
  refine TendstoUniformly.continuous (F := fun (u : V) (g : G) ↦ π g u)
    (p := 𝓝 v ⊓ 𝓟 {v : V | Continuous fun g ↦ π g v}) ?_ ?_
  · rw [Metric.tendstoUniformly_iff]
    intro ε hε
    have : ∀ᶠ u in 𝓝 v, dist u v < ε := Metric.ball_mem_nhds v hε
    filter_upwards [inf_le_left (b := 𝓟 _) this] with u hu g
    rw [dist_comm, dist_eq_norm, ← map_sub, hπ.norm_map, ← dist_eq_norm]
    exact hu
  · exact (eventually_inf_principal.2 (Eventually.of_forall fun u hu ↦ hu)).frequently

end Topology

section Measure

variable [TopologicalSpace G] [MeasurableSpace G] (ν : Measure G)

omit [TopologicalSpace G] in
/-- The weak integral of an orbit over a set on which all its coefficients are integrable: a
vector `u` with `⟪u, w⟫ = ∫ g in A, ⟪π g v, w⟫ ∂ν` for every `w`. -/
private theorem exists_inner_eq_setIntegral [CompleteSpace V] (hπ : π.IsUnitary) (v : V)
    {A : Set G} (hA : ν A < ∞) (hint : ∀ w, IntegrableOn (fun g ↦ ⟪π g v, w⟫_𝕜) A ν) :
    ∃ u : V, ∀ w, ⟪u, w⟫_𝕜 = ∫ g in A, ⟪π g v, w⟫_𝕜 ∂ν := by
  let ℓ : V →ₗ[𝕜] 𝕜 :=
    { toFun w := ∫ g in A, ⟪π g v, w⟫_𝕜 ∂ν
      map_add' w₁ w₂ := by
        simp only [inner_add_right]
        exact integral_add (hint w₁) (hint w₂)
      map_smul' c w := by
        simp only [inner_smul_right, RingHom.id_apply, smul_eq_mul]
        exact integral_const_mul c _ }
  have hbound : ∀ w, ‖ℓ w‖ ≤ ν.real A * ‖v‖ * ‖w‖ := fun w ↦ by
    refine (norm_setIntegral_le_of_norm_le_const (C := ‖v‖ * ‖w‖) hA fun g _ ↦ ?_).trans_eq
      (by ring)
    exact (norm_inner_le_norm _ _).trans_eq (by rw [hπ.norm_map])
  refine ⟨(InnerProductSpace.toDual 𝕜 V).symm (ℓ.mkContinuous _ hbound), fun w ↦ ?_⟩
  rw [InnerProductSpace.toDual_symm_apply, LinearMap.mkContinuous_apply]
  rfl

variable [IsTopologicalGroup G] [BorelSpace G] [ν.IsMulLeftInvariant]

/-- Change of variables under a left translation for a matrix coefficient of a unitary
representation: `∫ g in K, ⟪π g v, π k⁻¹ w⟫ ∂ν = ∫ g in k • K, ⟪π g v, w⟫ ∂ν`. -/
private theorem setIntegral_inner_inv_apply (hπ : π.IsUnitary) (v w : V) (k : G) (K : Set G) :
    ∫ g in K, ⟪π g v, π k⁻¹ w⟫_𝕜 ∂ν = ∫ g in k • K, ⟪π g v, w⟫_𝕜 ∂ν := by
  have hcoef (g : G) : ⟪π g v, π k⁻¹ w⟫_𝕜 = ⟪π (k * g) v, w⟫_𝕜 := by
    rw [← hπ.inner_map_map k, ← mul_apply_eq_comp, ← map_mul,
      ← mul_apply_eq_comp (π k), ← map_mul, mul_inv_cancel, map_one,
      one_apply_eq_self]
  simp_rw [hcoef]
  have hemb : MeasurableEmbedding (fun g : G ↦ k * g) :=
    (Homeomorph.mulLeft k).measurableEmbedding
  have hK : (fun g : G ↦ k * g) ⁻¹' (k • K) = K := by
    ext g
    simp [Set.mem_smul_set_iff_inv_smul_mem]
  calc ∫ g in K, ⟪π (k * g) v, w⟫_𝕜 ∂ν
      = ∫ g in (fun g : G ↦ k * g) ⁻¹' (k • K), ⟪π (k * g) v, w⟫_𝕜 ∂ν := by rw [hK]
    _ = ∫ g in k • K, ⟪π g v, w⟫_𝕜 ∂ν := by
      exact (measurePreserving_mul_left ν k).setIntegral_preimage_emb hemb
        (fun g ↦ ⟪π g v, w⟫_𝕜) (k • K)

/-- The bound `‖π k u - u‖ ≤ (ν (k • K \ K) + ν (k⁻¹ • K \ K)) ‖v‖` for the weak integral `u` of
the orbit of `v` over a closed compact set `K`. -/
private theorem norm_apply_sub_le_of_inner_eq_setIntegral [IsFiniteMeasureOnCompacts ν]
    (hπ : π.IsUnitary) {v u : V} (hint : ∀ w, LocallyIntegrable (fun g ↦ ⟪π g v, w⟫_𝕜) ν)
    {K : Set G} (hK : IsCompact K) (hKc : IsClosed K)
    (hu : ∀ w, ⟪u, w⟫_𝕜 = ∫ g in K, ⟪π g v, w⟫_𝕜 ∂ν) (k : G) :
    ‖π k u - u‖ ≤ (ν.real (k • K \ K) + ν.real (k⁻¹ • K \ K)) * ‖v‖ := by
  set C := (ν.real (k • K \ K) + ν.real (k⁻¹ • K \ K)) * ‖v‖
  have hC : 0 ≤ C := by positivity
  have hinner (w : V) : ‖⟪π k u - u, w⟫_𝕜‖ ≤ C * ‖w‖ := by
    have h₁ : ⟪π k u, w⟫_𝕜 = ∫ g in k • K, ⟪π g v, w⟫_𝕜 ∂ν := by
      rw [← setIntegral_inner_inv_apply ν hπ v w k K, ← hu]
      have hkw : π k (π k⁻¹ w) = w := by
        rw [← mul_apply_eq_comp, ← map_mul, mul_inv_cancel, map_one, one_apply_eq_self]
      conv_lhs => rw [← hkw]
      exact hπ.inner_map_map k u _
    have hKk : IsCompact (k • K) := hK.smul k
    have h₂ := integral_inter_add_sdiff (μ := ν) (f := fun g ↦ ⟪π g v, w⟫_𝕜)
      hKc.measurableSet ((hint w).integrableOn_isCompact hKk)
    have h₃ := integral_inter_add_sdiff (μ := ν) (f := fun g ↦ ⟪π g v, w⟫_𝕜)
      (hKc.smul k).measurableSet ((hint w).integrableOn_isCompact hK)
    have hdiff : ⟪π k u - u, w⟫_𝕜 =
        (∫ g in k • K \ K, ⟪π g v, w⟫_𝕜 ∂ν) - ∫ g in K \ k • K, ⟪π g v, w⟫_𝕜 ∂ν := by
      rw [inner_sub_left, h₁, hu, ← h₂, ← h₃, Set.inter_comm]
      ring
    have hmeas : ν (K \ k • K) = ν (k⁻¹ • K \ K) := by
      rw [← measure_smul ν k⁻¹, Set.smul_set_sdiff, inv_smul_smul]
    have hbd (A : Set G) (hA : ν A < ∞) :
        ‖∫ g in A, ⟪π g v, w⟫_𝕜 ∂ν‖ ≤ ‖v‖ * ‖w‖ * ν.real A :=
      norm_setIntegral_le_of_norm_le_const hA fun g _ ↦
        (norm_inner_le_norm _ _).trans_eq (by rw [hπ.norm_map])
    have hA₁ : ν (k • K \ K) < ∞ := (measure_mono Set.sdiff_subset).trans_lt hKk.measure_lt_top
    have hA₂ : ν (K \ k • K) < ∞ := (measure_mono Set.sdiff_subset).trans_lt hK.measure_lt_top
    have hreal : ν.real (K \ k • K) = ν.real (k⁻¹ • K \ K) := by
      simp only [measureReal_def, hmeas]
    rw [hdiff]
    refine (norm_sub_le _ _).trans ?_
    refine (add_le_add (hbd _ hA₁) (hbd _ hA₂)).trans_eq ?_
    rw [hreal]
    ring
  have hx := hinner (π k u - u)
  rw [inner_self_eq_norm_sq_to_K, norm_pow, RCLike.norm_ofReal, abs_norm] at hx
  nlinarith [norm_nonneg (π k u - u)]

variable [LocallyCompactSpace G] [IsFiniteMeasureOnCompacts ν] [ν.IsOpenPosMeasure]
  [ν.InnerRegularCompactLTTop]

omit [ν.IsOpenPosMeasure] in
/-- The weak integral of an orbit over a closed compact set has a continuous orbit. -/
private theorem continuous_apply_of_inner_eq_setIntegral (hπ : π.IsUnitary)
    {v u : V} (hint : ∀ w, LocallyIntegrable (fun g ↦ ⟪π g v, w⟫_𝕜) ν) {K : Set G}
    (hK : IsCompact K) (hKc : IsClosed K) (hu : ∀ w, ⟪u, w⟫_𝕜 = ∫ g in K, ⟪π g v, w⟫_𝕜 ∂ν) :
    Continuous fun g ↦ π g u := by
  refine hπ.continuous_apply_of_continuousAt_one ?_
  have hlim : Tendsto (fun k : G ↦ (ν.real (k • K \ K) + ν.real (k⁻¹ • K \ K)) * ‖v‖)
      (𝓝 1) (𝓝 0) := by
    have hm := tendsto_measure_smul_sdiff_isCompact_isClosed (μ := ν) hK hKc
    have h₁ : Tendsto (fun k : G ↦ ν.real (k • K \ K)) (𝓝 1) (𝓝 0) := by
      simpa [measureReal_def, Function.comp_def] using
        (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hm
    have hinv : Tendsto (fun k : G ↦ k⁻¹) (𝓝 1) (𝓝 1) := by
      simpa using (continuous_inv.tendsto (1 : G))
    have h₂ := h₁.comp hinv
    simpa using (h₁.add h₂).mul_const ‖v‖
  rw [ContinuousAt, map_one, one_apply_eq_self, tendsto_iff_norm_sub_tendsto_zero]
  exact squeeze_zero (fun _ ↦ norm_nonneg _)
    (norm_apply_sub_le_of_inner_eq_setIntegral ν hπ hint hK hKc hu) hlim

omit [ν.IsMulLeftInvariant] [IsFiniteMeasureOnCompacts ν] [ν.InnerRegularCompactLTTop] in
/-- On a separable space, a vector `w` such that every coefficient `g ↦ ⟪π g u, w⟫` integrates
to `0` over every closed compact set is `0`. -/
private theorem eq_zero_of_forall_setIntegral_inner_eq_zero [TopologicalSpace.SeparableSpace V]
    (hint : ∀ v w, LocallyIntegrable (fun g ↦ ⟪π g v, w⟫_𝕜) ν) {w : V}
    (hzero : ∀ u K, IsCompact K → IsClosed K → ∫ g in K, ⟪π g u, w⟫_𝕜 ∂ν = 0) : w = 0 := by
  obtain ⟨K₀, hK₀, hK₀1⟩ := exists_compact_mem_nhds (1 : G)
  have hK₀c : IsCompact (closure K₀) := hK₀.closure
  have hK₀1' : closure K₀ ∈ 𝓝 (1 : G) := Filter.mem_of_superset hK₀1 subset_closure
  have hcoef (u : V) : (fun g ↦ ⟪π g u, w⟫_𝕜) =ᵐ[ν.restrict (closure K₀)] 0 := by
    refine ae_eq_zero_of_forall_setIntegral_isClosed_eq_zero
      ((hint u w).integrableOn_isCompact hK₀c) fun s hs ↦ ?_
    rw [Measure.restrict_restrict hs.measurableSet]
    exact hzero u _ (hK₀c.inter_left hs) (hs.inter isClosed_closure)
  obtain ⟨d, hd⟩ := TopologicalSpace.exists_dense_seq V
  have hae : ∀ᵐ g ∂ν.restrict (closure K₀), ∀ n, ⟪π g (d n), w⟫_𝕜 = 0 :=
    ae_all_iff.2 fun n ↦ hcoef (d n)
  have hne : ν.restrict (closure K₀) ≠ 0 := by
    rw [Ne, Measure.restrict_eq_zero]
    exact (Measure.measure_pos_of_mem_nhds ν hK₀1').ne'
  have : (ae (ν.restrict (closure K₀))).NeBot := ae_neBot.2 hne
  obtain ⟨g, hg⟩ := hae.exists
  have hall (u : V) : ⟪π g u, w⟫_𝕜 = 0 :=
    hd.induction_on (p := fun u ↦ ⟪π g u, w⟫_𝕜 = 0) u
      (isClosed_eq ((π g).continuous.inner continuous_const) continuous_const) hg
  have := hall (π g⁻¹ w)
  have hgw : π g (π g⁻¹ w) = w := by
    rw [← mul_apply_eq_comp, ← map_mul, mul_inv_cancel, map_one, one_apply_eq_self]
  rwa [hgw, inner_self_eq_zero] at this

/-- **Measurable unitary representations are strongly continuous.** Let `π` be a unitary
representation of a locally compact group `G` with a left Haar measure `ν` on a separable Hilbert
space `V`. If every matrix coefficient `g ↦ ⟪π g v, w⟫` is locally integrable for `ν`, then every
orbit `g ↦ π g v` is continuous. -/
theorem continuous_apply_of_locallyIntegrable_inner [CompleteSpace V]
    [TopologicalSpace.SeparableSpace V] (hπ : π.IsUnitary)
    (hint : ∀ v w, LocallyIntegrable (fun g ↦ ⟪π g v, w⟫_𝕜) ν) (v : V) :
    Continuous fun g ↦ π g v := by
  let S : Submodule 𝕜 V :=
    { carrier := {u | Continuous fun g ↦ π g u}
      add_mem' := fun {a b} (ha : Continuous _) (hb : Continuous _) ↦ by
        change Continuous fun g ↦ π g (a + b)
        simp_rw [map_add]
        exact ha.add hb
      zero_mem' := by
        change Continuous fun g ↦ π g 0
        simp_rw [map_zero]
        exact continuous_const
      smul_mem' := fun c a (ha : Continuous _) ↦ by
        change Continuous fun g ↦ π g (c • a)
        simp_rw [map_smul]
        exact ha.const_smul c }
  have hS : IsClosed (S : Set V) := hπ.isClosed_setOf_continuous_apply
  have : CompleteSpace S := hS.completeSpace_coe
  suffices hS' : S = ⊤ from (hS' ▸ Submodule.mem_top : v ∈ S)
  rw [← Submodule.orthogonal_eq_bot_iff, Submodule.eq_bot_iff]
  intro w hw
  refine eq_zero_of_forall_setIntegral_inner_eq_zero ν hint fun u K hK hKc ↦ ?_
  obtain ⟨a, ha⟩ := exists_inner_eq_setIntegral ν hπ u hK.measure_lt_top
    fun w' ↦ (hint u w').integrableOn_isCompact hK
  rw [← ha]
  exact Submodule.inner_right_of_mem_orthogonal
    (continuous_apply_of_inner_eq_setIntegral ν hπ (hint u) hK hKc ha) hw

end Measure

end ContRepresentation.IsUnitary
