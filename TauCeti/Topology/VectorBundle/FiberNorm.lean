/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Seminorm.Norm
public import Mathlib.Topology.VectorBundle.Riemannian
public import TauCeti.Analysis.Normed.Module.Seminorm.Comparison
public import TauCeti.Topology.VectorBundle.Trivialization

/-!
# Continuous fibre norms on a vector bundle

A family of seminorms `ν b` on the fibres `E b` of a real topological vector bundle with model
fibre `F` is a *continuous fibre norm* (`TauCeti.IsContinuousFiberNorm F E ν`) when

* each `ν b`, read in the trivialization at `b`, is bounded above and below by positive multiples
  of the norm of `F`, so that it is a norm inducing the topology of `E b`; and
* the norms vary continuously, uniformly on the unit ball of the model fibre: at every `b₀` and
  for every `ε > 0`, the norms read in the trivialization at `b₀` satisfy
  `|ν b (e.symm b v) - ν b₀ (e.symm b₀ v)| ≤ ε * ‖v‖` for all `v : F` and `b` near `b₀`.

These are continuous Finsler data on a vector bundle whose model fibre may be an
infinite-dimensional Banach space; no smoothness and no inner product is required.

## Main results

* `TauCeti.IsContinuousFiberNorm.exists_bounds_of_mem` and
  `TauCeti.IsContinuousFiberNorm.eventually_abs_sub_le_of_mem`: both conditions hold in every
  trivialization of the atlas, not only in the trivializations `trivializationAt F E b`.
* `TauCeti.IsContinuousFiberNorm.eventually_bounds`: local two-sided comparison with the norm of
  the model fibre, and its uniform version
  `TauCeti.IsContinuousFiberNorm.exists_bounds_of_isCompact` on a compact set of base points,
  through finitely many trivializations.
* `TauCeti.IsContinuousFiberNorm.continuous_totalSpace`: evaluation of the norm is continuous on
  the total space; in particular each `ν b` is continuous (`continuous_fiber`) and definite
  (`eq_zero_of_apply_eq_zero`).
* `TauCeti.isContinuousFiberNorm_trivial`: the norm of `F` on the trivial bundle.
* `TauCeti.isContinuousFiberNorm_norm`: the norms of a continuous Riemannian bundle
  (`IsContinuousRiemannianBundle`).
-/

@[expose] public section

open Bundle Filter Topology

namespace TauCeti

section General

variable {B : Type*} [TopologicalSpace B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type*} [TopologicalSpace (TotalSpace F E)]
  [∀ b, TopologicalSpace (E b)] [∀ b, AddCommGroup (E b)] [∀ b, Module ℝ (E b)]
  [FiberBundle F E] [VectorBundle ℝ F E]

variable (F E) in
/-- A family of seminorms `ν b` on the fibres of a real topological vector bundle with model
fibre `F` is a *continuous fibre norm* if each `ν b`, read in the trivialization at `b`, is
bounded above and below by positive multiples of the norm of `F`, and if at every `b₀` the
norms read in the trivialization at `b₀` are uniformly close to `ν b₀` on the unit ball of `F`
for `b` near `b₀`. By `IsContinuousFiberNorm.exists_bounds_of_mem` and
`IsContinuousFiberNorm.eventually_abs_sub_le_of_mem`, any trivialization of the atlas may be used
in place of `trivializationAt F E b`. -/
structure IsContinuousFiberNorm (ν : ∀ b, Seminorm ℝ (E b)) : Prop where
  /-- In the trivialization at `b`, the norm `ν b` is comparable with the model norm. -/
  exists_bounds (b : B) : ∃ c > 0, ∃ C, ∀ v : F,
    c * ‖v‖ ≤ ν b ((trivializationAt F E b).symmL ℝ b v) ∧
      ν b ((trivializationAt F E b).symmL ℝ b v) ≤ C * ‖v‖
  /-- In the trivialization at `b₀`, the norms near `b₀` are uniformly close to `ν b₀` on the
  unit ball of the model fibre. -/
  eventually_abs_sub_le (b₀ : B) {ε : ℝ} (hε : 0 < ε) : ∀ᶠ b in 𝓝 b₀, ∀ v : F,
    |ν b ((trivializationAt F E b₀).symmL ℝ b v) -
      ν b₀ ((trivializationAt F E b₀).symmL ℝ b₀ v)| ≤ ε * ‖v‖

namespace IsContinuousFiberNorm

variable {ν : ∀ b, Seminorm ℝ (E b)} (hν : IsContinuousFiberNorm F E ν)
include hν

/-- The comparison of a continuous fibre norm with the model norm holds in every trivialization
of the atlas. -/
theorem exists_bounds_of_mem (e : Trivialization F (π F E)) [MemTrivializationAtlas e] {b : B}
    (hb : b ∈ e.baseSet) :
    ∃ c > 0, ∃ C, ∀ v : F, c * ‖v‖ ≤ ν b (e.symmL ℝ b v) ∧ ν b (e.symmL ℝ b v) ≤ C * ‖v‖ := by
  obtain ⟨c, hc, C, hN⟩ := hν.exists_bounds b
  have hb' : b ∈ e.baseSet ∩ (trivializationAt F E b).baseSet :=
    ⟨hb, FiberBundle.mem_baseSet_trivializationAt' b⟩
  obtain ⟨c', hc', C', h⟩ :=
    exists_bounds_comp_continuousLinearEquiv hc hN (e.coordChangeL ℝ (trivializationAt F E b) b)
  refine ⟨c', hc', C', fun v ↦ ?_⟩
  rw [← (trivializationAt F E b).symmL_coordChangeL ℝ e hb']
  exact h v

/-- The continuity of a continuous fibre norm holds in every trivialization of the atlas. -/
theorem eventually_abs_sub_le_of_mem (e : Trivialization F (π F E)) [MemTrivializationAtlas e]
    {b₀ : B} (hb₀ : b₀ ∈ e.baseSet) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ b in 𝓝 b₀, ∀ v : F, |ν b (e.symmL ℝ b v) - ν b₀ (e.symmL ℝ b₀ v)| ≤ ε * ‖v‖ := by
  set e₀ := trivializationAt F E b₀
  have hmem : b₀ ∈ e.baseSet ∩ e₀.baseSet :=
    ⟨hb₀, FiberBundle.mem_baseSet_trivializationAt' b₀⟩
  have hopen : e.baseSet ∩ e₀.baseSet ∈ 𝓝 b₀ :=
    (e.open_baseSet.inter e₀.open_baseSet).mem_nhds hmem
  obtain ⟨c, -, C, hC⟩ := hν.exists_bounds b₀
  have key := eventually_abs_sub_le_comp_continuousLinearMap
    (N := fun b ↦ (ν b).comp (e₀.symmL ℝ b).toLinearMap) (C := C)
    (fun w ↦ by simpa using (hC w).2) (fun δ hδ ↦ by simpa using hν.eventually_abs_sub_le b₀ hδ)
    ((continuousOn_coordChange ℝ e e₀).continuousAt hopen) hε
  filter_upwards [key, hopen] with b hb hbmem v
  have := hb v
  simp only [Seminorm.comp_apply, ContinuousLinearMap.coe_coe, ContinuousLinearEquiv.coe_coe,
    e₀.symmL_coordChangeL ℝ e hbmem, e₀.symmL_coordChangeL ℝ e hmem] at this
  exact this

/-- Local two-sided comparison of a continuous fibre norm with the model norm, in any
trivialization of the atlas. -/
theorem eventually_bounds (e : Trivialization F (π F E)) [MemTrivializationAtlas e] {b₀ : B}
    (hb₀ : b₀ ∈ e.baseSet) :
    ∃ c > 0, ∃ C, ∀ᶠ b in 𝓝 b₀, ∀ v : F,
      c * ‖v‖ ≤ ν b (e.symmL ℝ b v) ∧ ν b (e.symmL ℝ b v) ≤ C * ‖v‖ := by
  obtain ⟨c, hc, C, h⟩ := hν.exists_bounds_of_mem e hb₀
  refine ⟨c / 2, by positivity, C + c / 2, ?_⟩
  filter_upwards [hν.eventually_abs_sub_le_of_mem e hb₀ (half_pos hc)] with b hb v
  have := abs_le.1 (hb v)
  have := h v
  constructor <;> linarith

/-- On a compact set of base points, a continuous fibre norm is comparable with the model norm,
uniformly, through the trivializations at finitely many points. -/
theorem exists_bounds_of_isCompact {K : Set B} (hK : IsCompact K) :
    ∃ t : Finset B, ∃ c > 0, ∃ C, ∀ b ∈ K, ∃ x ∈ t, b ∈ (trivializationAt F E x).baseSet ∧
      ∀ v : F, c * ‖v‖ ≤ ν b ((trivializationAt F E x).symmL ℝ b v) ∧
        ν b ((trivializationAt F E x).symmL ℝ b v) ≤ C * ‖v‖ := by
  choose c hc C hC using fun x ↦
    hν.eventually_bounds (trivializationAt F E x) (FiberBundle.mem_baseSet_trivializationAt' x)
  obtain ⟨t, -, hcover⟩ := hK.elim_nhds_subcover
    (fun x ↦ {b | b ∈ (trivializationAt F E x).baseSet ∧ ∀ v : F,
      c x * ‖v‖ ≤ ν b ((trivializationAt F E x).symmL ℝ b v) ∧
        ν b ((trivializationAt F E x).symmL ℝ b v) ≤ C x * ‖v‖})
    fun x _ ↦ Filter.inter_mem ((trivializationAt F E x).open_baseSet.mem_nhds
      (FiberBundle.mem_baseSet_trivializationAt' x)) (hC x)
  have hsum0 : 0 ≤ ∑ x ∈ t, (c x)⁻¹ := Finset.sum_nonneg fun y _ ↦ (inv_pos.2 (hc y)).le
  refine ⟨t, (∑ x ∈ t, (c x)⁻¹ + 1)⁻¹, inv_pos.2 (by linarith), ∑ x ∈ t, |C x|,
    fun b hb ↦ ?_⟩
  obtain ⟨x, hxt, hbx, hv⟩ := Set.mem_iUnion₂.1 (hcover hb)
  refine ⟨x, hxt, hbx, fun v ↦ ⟨?_, ?_⟩⟩
  · refine le_trans ?_ (hv v).1
    gcongr
    have hsum : (c x)⁻¹ ≤ ∑ x ∈ t, (c x)⁻¹ + 1 :=
      (Finset.single_le_sum (fun y _ ↦ (inv_pos.2 (hc y)).le) hxt).trans (le_add_of_nonneg_right
        zero_le_one)
    simpa using inv_anti₀ (inv_pos.2 (hc x)) hsum
  · refine (hv v).2.trans ?_
    gcongr
    exact (le_abs_self _).trans (Finset.single_le_sum (fun y _ ↦ abs_nonneg (C y)) hxt)

/-- Evaluation of a continuous fibre norm is continuous on the total space. -/
theorem continuous_totalSpace : Continuous fun p : TotalSpace F E ↦ ν p.proj p.snd := by
  rw [continuous_iff_continuousAt]
  intro p₀
  set e := trivializationAt F E p₀.proj
  have hp₀ : p₀.proj ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' _
  have hrep (q : TotalSpace F E) (hq : q.proj ∈ e.baseSet) :
      ν q.proj q.snd = ν q.proj (e.symmL ℝ q.proj (e q).2) := by
    rw [e.symmL_apply hq]
    exact congrArg _ (e.symm_apply_apply_mk hq q.snd).symm
  obtain ⟨c, -, C, hC⟩ := hν.exists_bounds p₀.proj
  have hw : ContinuousAt (fun p ↦ (e p).2) p₀ :=
    (e.continuousOn.continuousAt (e.open_source.mem_nhds (e.mem_source.2 hp₀))).snd
  rw [Metric.continuousAt_iff']
  intro ε hε
  set W := ‖(e p₀).2‖ + 1
  set C' := max C 0 + 1
  have hW : 0 < W := by positivity
  have hC' : 0 < C' := by positivity
  have h1 : ∀ᶠ p in 𝓝 p₀, ‖(e p).2 - (e p₀).2‖ < min 1 (ε / (2 * C')) :=
    ((Metric.continuousAt_iff'.1 hw) (min 1 (ε / (2 * C'))) (by positivity)).mono
      fun p hp ↦ by rwa [← dist_eq_norm]
  have h2 := ((FiberBundle.continuous_proj F E).tendsto p₀).eventually
    (hν.eventually_abs_sub_le p₀.proj (ε := ε / (2 * W)) (by positivity))
  have h3 : ∀ᶠ p in 𝓝 p₀, p.proj ∈ e.baseSet :=
    (FiberBundle.continuous_proj F E).continuousAt.preimage_mem_nhds (e.open_baseSet.mem_nhds hp₀)
  filter_upwards [h1, h2, h3] with p hp1 hp2 hp3
  rw [Real.dist_eq, hrep p hp3, hrep p₀ hp₀]
  set w := (e p).2
  set w₀ := (e p₀).2
  have hw1 : ‖w - w₀‖ ≤ 1 := hp1.le.trans (min_le_left _ _)
  have hw2 : ‖w - w₀‖ < ε / (2 * C') := hp1.trans_le (min_le_right _ _)
  have hwW : ‖w‖ ≤ W := by
    have := norm_le_insert' w w₀
    simp only [W]
    linarith
  have hCw : ν p₀.proj (e.symmL ℝ p₀.proj (w - w₀)) ≤ C' * ‖w - w₀‖ := (hC _).2.trans (by
    gcongr; exact (le_max_left _ _).trans (le_add_of_nonneg_right zero_le_one))
  calc |ν p.proj (e.symmL ℝ p.proj w) - ν p₀.proj (e.symmL ℝ p₀.proj w₀)|
      ≤ |ν p.proj (e.symmL ℝ p.proj w) - ν p₀.proj (e.symmL ℝ p₀.proj w)| +
          |ν p₀.proj (e.symmL ℝ p₀.proj w) - ν p₀.proj (e.symmL ℝ p₀.proj w₀)| :=
        abs_sub_le _ _ _
    _ ≤ ε / (2 * W) * ‖w‖ + C' * ‖w - w₀‖ := by
        gcongr
        · exact hp2 w
        · refine (abs_sub_map_le_sub _ _ _).trans ?_
          rw [← map_sub]
          exact hCw
    _ < ε / (2 * W) * W + C' * (ε / (2 * C')) :=
        add_lt_add_of_le_of_lt (by gcongr) (by gcongr)
    _ = ε := by field_simp; ring

/-- Each norm of a continuous fibre norm is continuous on its fibre. -/
theorem continuous_fiber (b : B) : Continuous (ν b) :=
  hν.continuous_totalSpace.comp (FiberBundle.totalSpaceMk_isInducing F E b).continuous

/-- Each norm of a continuous fibre norm is definite. -/
theorem eq_zero_of_apply_eq_zero {b : B} {v : E b} (h : ν b v = 0) : v = 0 := by
  set e := trivializationAt F E b
  have hb : b ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' b
  obtain ⟨c, hc, C, hC⟩ := hν.exists_bounds b
  have hle := (hC (e.continuousLinearMapAt ℝ b v)).1
  rw [e.symmL_continuousLinearMapAt (R := ℝ) hb, h] at hle
  have hw : e.continuousLinearMapAt ℝ b v = 0 :=
    norm_le_zero_iff.1 (le_of_mul_le_mul_left (by rwa [mul_zero]) hc)
  rw [← e.symmL_continuousLinearMapAt (R := ℝ) hb v, hw, map_zero]

end IsContinuousFiberNorm

end General

section Trivial

variable (B : Type*) [TopologicalSpace B] (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The norm of the model fibre is a continuous fibre norm on the trivial bundle. -/
theorem isContinuousFiberNorm_trivial :
    IsContinuousFiberNorm F (Bundle.Trivial B F) fun _ ↦ normSeminorm ℝ F where
  exists_bounds _ := ⟨1, one_pos, 1, fun v ↦ by simp⟩
  eventually_abs_sub_le _ _ hε := Eventually.of_forall fun _ v ↦ by
    simp only [Trivial.fiberBundle_trivializationAt', Trivial.symmL_trivialization,
      ContinuousLinearMap.id_apply, sub_self, abs_zero]
    positivity

end Trivial

section Riemannian

variable {B : Type*} [TopologicalSpace B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type*} [TopologicalSpace (TotalSpace F E)] [∀ b, NormedAddCommGroup (E b)]
  [∀ b, InnerProductSpace ℝ (E b)] [FiberBundle F E] [VectorBundle ℝ F E]
  [IsContinuousRiemannianBundle F E]

variable (F E) in
/-- The norms of a continuous Riemannian bundle form a continuous fibre norm. -/
theorem isContinuousFiberNorm_norm :
    IsContinuousFiberNorm F E fun b ↦ normSeminorm ℝ (E b) where
  exists_bounds b := by
    set e := trivializationAt F E b
    have hb : b ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' b
    refine ⟨(‖e.continuousLinearMapAt ℝ b‖ + 1)⁻¹, by positivity, ‖e.symmL ℝ b‖,
      fun v ↦ ⟨?_, ?_⟩⟩
    · simp only [coe_normSeminorm]
      have h1 : ‖v‖ ≤ ‖e.continuousLinearMapAt ℝ b‖ * ‖e.symmL ℝ b v‖ := by
        simpa [e.continuousLinearMapAt_symmL hb] using
          (e.continuousLinearMapAt ℝ b).le_opNorm (e.symmL ℝ b v)
      rw [inv_mul_le_iff₀ (by positivity)]
      nlinarith [norm_nonneg (e.symmL ℝ b v)]
    · exact (e.symmL ℝ b).le_opNorm v
  eventually_abs_sub_le b₀ ε hε := by
    set e := trivializationAt F E b₀
    have hb₀ : b₀ ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' b₀
    set S := ‖e.symmL ℝ b₀‖
    set η := min 1 (ε / (2 * (S + 1)))
    have hη : 0 < η := by positivity
    have hη1 : η ≤ 1 := min_le_left _ _
    have hηS : 2 * η * S ≤ ε := by
      have : η * (2 * (S + 1)) ≤ ε :=
        (le_div_iff₀ (by positivity)).1 (min_le_right _ _)
      nlinarith [norm_nonneg (e.symmL ℝ b₀)]
    filter_upwards [eventually_norm_symmL_trivializationAt_comp_self_lt F E b₀
        (r := 1 + η) (by linarith),
      eventually_norm_symmL_trivializationAt_self_comp_lt F E b₀ (r := 1 + η) (by linarith),
      e.open_baseSet.mem_nhds hb₀] with b h1 h2 hb v
    simp only [coe_normSeminorm]
    have ha : ‖e.symmL ℝ b v‖ ≤ (1 + η) * ‖e.symmL ℝ b₀ v‖ := by
      have : e.symmL ℝ b v = (e.symmL ℝ b ∘L e.continuousLinearMapAt ℝ b₀) (e.symmL ℝ b₀ v) := by
        simp [e.continuousLinearMapAt_symmL hb₀]
      rw [this]
      exact ((e.symmL ℝ b ∘L e.continuousLinearMapAt ℝ b₀).le_opNorm _).trans (by gcongr)
    have ha₀ : ‖e.symmL ℝ b₀ v‖ ≤ (1 + η) * ‖e.symmL ℝ b v‖ := by
      have : e.symmL ℝ b₀ v = (e.symmL ℝ b₀ ∘L e.continuousLinearMapAt ℝ b) (e.symmL ℝ b v) := by
        simp [e.continuousLinearMapAt_symmL hb]
      rw [this]
      exact ((e.symmL ℝ b₀ ∘L e.continuousLinearMapAt ℝ b).le_opNorm _).trans (by gcongr)
    have hS : ‖e.symmL ℝ b₀ v‖ ≤ S * ‖v‖ := (e.symmL ℝ b₀).le_opNorm v
    have hη2 : η * ‖e.symmL ℝ b v‖ ≤ 2 * η * ‖e.symmL ℝ b₀ v‖ := by
      nlinarith [norm_nonneg (e.symmL ℝ b₀ v)]
    have hfin : 2 * η * ‖e.symmL ℝ b₀ v‖ ≤ ε * ‖v‖ :=
      calc 2 * η * ‖e.symmL ℝ b₀ v‖ ≤ 2 * η * (S * ‖v‖) := by gcongr
        _ = 2 * η * S * ‖v‖ := by ring
        _ ≤ ε * ‖v‖ := by gcongr
    rw [abs_le]
    constructor <;> nlinarith [norm_nonneg (e.symmL ℝ b₀ v), norm_nonneg (e.symmL ℝ b v)]

end Riemannian

end TauCeti
