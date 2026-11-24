/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
public import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
public import TauCeti.Geometry.Manifold.ContMDiffMap.Chart.Seminorm
public import TauCeti.Geometry.Manifold.ContMDiffMap.CLMApply
public import TauCeti.Geometry.Manifold.VectorBundle.Trivialization
import TauCeti.Analysis.Calculus.ContDiff.Bounds
import TauCeti.Geometry.Manifold.ContMDiffMap.Chart.Restriction
import TauCeti.Geometry.Manifold.ExtChartAt

/-!
# Compact chart seminorms for bundle sections

A smooth bundle trivialization sends sections to vector-valued maps on its base set.
Composing this linear coordinate map with `ContMDiffMap.chartDerivativeSeminorm` and
`ContMDiffMap.chartCkSeminorm` gives the compact chart/frame seminorms of sections
(`Bundle.Trivialization.chartDerivativeSeminorm`, `Bundle.Trivialization.chartCkSeminorm`),
with each derivative seminorm of order `m ≤ k` bounded by the `C^k` seminorm
(`Bundle.Trivialization.chartDerivativeSeminorm_le_chartCkSeminorm`).
These measure the actual coordinate derivatives, including order zero, without requiring
an ambient norm on the fibres or choosing a connection. They supply the local controls
used in smooth-section and compactly supported test-section topologies. On a compact overlap
of two smooth trivializations and inherited charts, the combined Leibniz and Faà di Bruno
estimate bounds the `C^k` seminorm in one frame and chart by a constant multiple of the `C^k`
seminorm in the other (`Bundle.Trivialization.exists_chartCkSeminorm_le_coordChange`).
The chart jet of the coefficients at a single coordinate point is the linear map
`Bundle.Trivialization.frameJetAt`.
At the centre of a chart on an open subset, an interior point, these chart jets are the
ordinary derivatives of the coefficients read in the ambient chart
(`Bundle.Trivialization.chartIteratedFDeriv_frameCoordinates_self`).

The construction allows finite and infinite regularity, manifolds with corners, and
arbitrary normed model fibres. No topology on the section space is installed here.
-/

public section

noncomputable section

open Set TopologicalSpace Bundle Filter Topology
open scoped Manifold ContDiff

namespace Bundle.Trivialization

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {V : M → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle 𝕜 F V]
  {n : ℕ∞ω} [ContMDiffVectorBundle n F V I]
  (e : Trivialization F (π F V)) [MemTrivializationAtlas e]
  {U : Opens M} (hU : (U : Set M) ⊆ e.baseSet)

/-- The coefficients of a section in a smooth bundle trivialization, on an open subset of
its base set, as a linear map to native vector-valued smooth maps. -/
def frameCoordinates : Cₛ^n⟮I; F, V⟯ →ₗ[𝕜] C^n⟮I, U; 𝓘(𝕜, F), F⟯ where
  toFun s := ⟨fun x => (e ⟨(x : M), s x⟩).2, fun x =>
    (contMDiffAt_subtype_iff (f := fun y => (e ⟨y, s y⟩).2)).mpr
      ((e.contMDiffAt_section_iff (hU x.property)).mp (s.contMDiff x))⟩
  map_add' s t := by
    ext x
    -- Unpack the bundled maps before applying fibrewise linearity.
    change (e ⟨(x : M), s x + t x⟩).2 = (e ⟨(x : M), s x⟩).2 +
      (e ⟨(x : M), t x⟩).2
    simp only [← e.continuousLinearMapAt_apply_of_mem 𝕜 (hU x.property), map_add]
  map_smul' c s := by
    ext x
    -- Unpack the bundled maps before applying fibrewise linearity.
    change (e ⟨(x : M), c • s x⟩).2 = c • (e ⟨(x : M), s x⟩).2
    simp only [← e.continuousLinearMapAt_apply_of_mem 𝕜 (hU x.property), map_smul]

/-- Frame coordinates are the fibre component of the given trivialization. -/
@[simp]
theorem frameCoordinates_apply (s : Cₛ^n⟮I; F, V⟯) (x : U) :
    frameCoordinates e hU s x = (e ⟨(x : M), s x⟩).2 :=
  (rfl)

/-- Equality of frame coordinates at a point is equality of section values there. -/
theorem frameCoordinates_eq_iff (s t : Cₛ^n⟮I; F, V⟯) (x : U) :
    frameCoordinates e hU s x = frameCoordinates e hU t x ↔ s x = t x := by
  constructor
  · intro h
    rw [frameCoordinates_apply, frameCoordinates_apply] at h
    simpa only [e.symm_apply_apply_mk (hU x.property)] using congrArg (e.symm x) h
  · intro h
    simp only [frameCoordinates_apply, h]

/-- Coordinates in two smooth trivializations are related by their native transition map. -/
theorem frameCoordinates_coordChange (e' : Trivialization F (π F V))
    [MemTrivializationAtlas e'] (hU' : (U : Set M) ⊆ e'.baseSet)
    (s : Cₛ^n⟮I; F, V⟯) (x : U) :
    e.coordChangeL 𝕜 e' x (frameCoordinates e hU s x) = frameCoordinates e' hU' s x := by
  simp only [frameCoordinates_apply, e.coordChangeL_apply e' ⟨hU x.property, hU' x.property⟩,
    e.symm_apply_apply_mk (hU x.property)]

/-- Coefficients in a second frame are obtained by the smooth transition multiplier. -/
theorem frameCoordinates_eq_clmApply (e' : Trivialization F (π F V))
    [MemTrivializationAtlas e'] (hU' : (U : Set M) ⊆ e'.baseSet)
    (s : Cₛ^n⟮I; F, V⟯) :
    e'.frameCoordinates hU' s = ContMDiffMap.clmApplyLinearMap
      (frameTransitionMap (I := I) (n := n) e e' hU hU') (e.frameCoordinates hU s) := by
  ext x
  simp only [ContMDiffMap.clmApplyLinearMap_apply, frameTransitionMap_apply]
  exact (e.frameCoordinates_coordChange hU e' hU' s x).symm


variable [IsManifold I n M]

/-- The chart derivative of order `m` of the frame coefficients of a section, in the chart of `U`
at `x`, evaluated at the coordinate point `z`. -/
def frameJetAt (x : U) (m : ℕ) (hm : m ≤ n) (z : (extChartAt I x).target) :
    Cₛ^n⟮I; F, V⟯ →ₗ[𝕜] E [×m]→L[𝕜] F :=
  (ContinuousMap.evalCLM 𝕜 z).toLinearMap ∘ₗ
    ContMDiffMap.chartIteratedFDerivLinearMap x m hm ∘ₗ frameCoordinates e hU

/-- The pointwise frame jet is the chart derivative of the frame coefficients at that point. -/
@[simp]
theorem frameJetAt_apply (x : U) (m : ℕ) (hm : m ≤ n) (z : (extChartAt I x).target)
    (s : Cₛ^n⟮I; F, V⟯) :
    frameJetAt e hU x m hm z s =
      ContMDiffMap.chartIteratedFDeriv (frameCoordinates e hU s) x m hm z := by
  simp only [frameJetAt, LinearMap.comp_apply, ContinuousLinearMap.coe_coe,
    ContinuousMap.evalCLM_apply]
  exact congrArg (· z) (ContMDiffMap.chartIteratedFDerivLinearMap_apply (I := I) x m hm
    (frameCoordinates e hU s))

/-- At the centre of a chart of an open subset `U` of the base set of a trivialization `e`, if the
centre is an interior point, the chart derivatives of the frame coefficients of a section are the
ordinary derivatives of the frame coefficients read in the ambient chart. -/
theorem chartIteratedFDeriv_frameCoordinates_self (s : Cₛ^n⟮I; F, V⟯) (x : U) (k : ℕ)
    (hk : k ≤ n) (hx : I.IsInteriorPoint (x : M)) :
    ContMDiffMap.chartIteratedFDeriv (frameCoordinates e hU s) x k hk
        ⟨extChartAt I x x, mem_extChartAt_target x⟩ =
      iteratedFDeriv 𝕜 k ((fun y ↦ (e ⟨y, s y⟩).2) ∘ (extChartAt I (x : M)).symm)
        (extChartAt I (x : M) x) := by
  -- The chart of `U` at `x` is the subtype restriction of the ambient chart at `x`, so both send
  -- `x` to the same coordinates by definition.
  have hpt : (extChartAt I x x : E) = extChartAt I (x : M) x := rfl
  have hf : ⇑(frameCoordinates e hU s) = (fun y ↦ (e ⟨y, s y⟩).2) ∘ Subtype.val :=
    funext (frameCoordinates_apply e hU s)
  have h := congrFun (ContMDiffMap.ftaylorSeriesWithin_restrict_extChartAt (I := I)
    (fun y ↦ (e ⟨y, s y⟩).2) U x (mem_extChartAt_target x)) k
  simp only [ftaylorSeriesWithin] at h
  rw [ContMDiffMap.chartIteratedFDeriv_self_target_apply, hf, h, hpt,
    iteratedFDerivWithin_congr_set (Filter.eventuallyEqSet_univ.2
      (mem_interior_iff_mem_nhds.mp (I.isInteriorPoint_iff.mp hx))),
    iteratedFDerivWithin_univ]

/-- The supremum seminorm of the derivative of order `m` in a source chart and bundle frame,
restricted to a compact coordinate set. -/
def chartDerivativeSeminorm (x : U) (K : Compacts (extChartAt I x).target)
    (m : ℕ) (hm : m ≤ n) : Seminorm 𝕜 Cₛ^n⟮I; F, V⟯ :=
  (ContMDiffMap.chartDerivativeSeminorm x K m hm).comp (frameCoordinates e hU)

/-- The section seminorm is the norm of its actual frame-coordinate jet on the compact set. -/
theorem chartDerivativeSeminorm_apply (x : U) (K : Compacts (extChartAt I x).target)
    (m : ℕ) (hm : m ≤ n) (s : Cₛ^n⟮I; F, V⟯) :
    chartDerivativeSeminorm e hU x K m hm s =
      ‖(ContMDiffMap.chartIteratedFDeriv (frameCoordinates e hU s) x m hm).restrict K‖ := by
  rw [chartDerivativeSeminorm, Seminorm.comp_apply, ContMDiffMap.chartDerivativeSeminorm_apply]

/-- A nonnegative seminorm bound is exactly a bound for every coordinate derivative on `K`. -/
theorem chartDerivativeSeminorm_le_iff (x : U) (K : Compacts (extChartAt I x).target)
    (m : ℕ) (hm : m ≤ n) (s : Cₛ^n⟮I; F, V⟯) {r : ℝ} (hr : 0 ≤ r) :
    chartDerivativeSeminorm e hU x K m hm s ≤ r ↔ ∀ z ∈ K,
      ‖ContMDiffMap.chartIteratedFDeriv (frameCoordinates e hU s) x m hm z‖ ≤ r := by
  exact ContMDiffMap.chartDerivativeSeminorm_le_iff x K m hm _ hr

/-- Pointwise strict bounds are uniform on a compact coordinate set. -/
theorem chartDerivativeSeminorm_lt_iff (x : U) (K : Compacts (extChartAt I x).target)
    (m : ℕ) (hm : m ≤ n) (s : Cₛ^n⟮I; F, V⟯) {r : ℝ} (hr : 0 < r) :
    chartDerivativeSeminorm e hU x K m hm s < r ↔ ∀ z ∈ K,
      ‖ContMDiffMap.chartIteratedFDeriv (frameCoordinates e hU s) x m hm z‖ < r := by
  exact ContMDiffMap.chartDerivativeSeminorm_lt_iff x K m hm _ hr

/-- Increasing the compact set increases the section derivative seminorm. -/
theorem chartDerivativeSeminorm_mono (x : U) {K L : Compacts (extChartAt I x).target}
    (hKL : K ≤ L) (m : ℕ) (hm : m ≤ n) :
    chartDerivativeSeminorm (I := I) e hU x K m hm ≤
      chartDerivativeSeminorm e hU x L m hm :=
  Seminorm.comp_mono _ (ContMDiffMap.chartDerivativeSeminorm_mono x hKL m hm)

/-- The seminorm on the empty compact set is zero. -/
@[simp]
theorem chartDerivativeSeminorm_bot (x : U) (m : ℕ) (hm : m ≤ n) :
    chartDerivativeSeminorm (I := I) e hU x ⊥ m hm = 0 := by
  rw [chartDerivativeSeminorm, ContMDiffMap.chartDerivativeSeminorm_bot, Seminorm.zero_comp]

/-- **Locality.** A frame derivative seminorm vanishes on a section which is zero near the points
of the base represented by the compact coordinate set. -/
theorem chartDerivativeSeminorm_eq_zero_of_eventuallyEq_zero (x : U)
    (K : Compacts (extChartAt I x).target) (m : ℕ) (hm : m ≤ n) {s : Cₛ^n⟮I; F, V⟯}
    (hs : ∀ᶠ y in 𝓝ˢ (Subtype.val '' ((extChartAt I x).symm ''
      (Subtype.val '' (K : Set (extChartAt I x).target)))), s y = 0) :
    chartDerivativeSeminorm e hU x K m hm s = 0 := by
  have hCk : ContMDiffMap.chartCkSeminorm x K m hm (frameCoordinates e hU s) = 0 := by
    refine ContMDiffMap.chartCkSeminorm_eq_zero_of_eventuallyEq_zero x K m hm fun z hz ↦ ?_
    have hz' : (((extChartAt I x).symm z : U) : M) ∈ Subtype.val '' ((extChartAt I x).symm ''
        (Subtype.val '' (K : Set (extChartAt I x).target))) :=
      ⟨_, ⟨z, ⟨z, hz, rfl⟩, rfl⟩, rfl⟩
    have hnhds := (continuous_subtypeVal.continuousAt
      (x := (extChartAt I x).symm z)).eventually (hs.filter_mono (nhds_le_nhdsSet hz'))
    filter_upwards [hnhds] with y hy
    exact (frameCoordinates_eq_iff e hU s 0 y).mpr (by simpa using hy) |>.trans (by simp)
  refine le_antisymm ?_ (apply_nonneg _ _)
  refine (chartDerivativeSeminorm_le_iff e hU x K m hm s le_rfl).mpr fun z hz ↦ ?_
  exact (ContMDiffMap.chartCkSeminorm_le_iff x K m hm _ le_rfl).mp hCk.le m le_rfl z hz

/-- The compact chart/frame `C^k` seminorm of a section, including order zero. -/
def chartCkSeminorm (x : U) (K : Compacts (extChartAt I x).target) (k : ℕ) (hk : k ≤ n) :
    Seminorm 𝕜 Cₛ^n⟮I; F, V⟯ :=
  (ContMDiffMap.chartCkSeminorm x K k hk).comp (frameCoordinates e hU)

/-- A compact frame seminorm is the compact chart seminorm of its coefficient function. -/
@[simp]
theorem chartCkSeminorm_apply (x : U) (K : Compacts (extChartAt I x).target)
    (k : ℕ) (hk : k ≤ n) (s : Cₛ^n⟮I; F, V⟯) :
    chartCkSeminorm e hU x K k hk s =
      ContMDiffMap.chartCkSeminorm x K k hk (frameCoordinates e hU s) := by
  rfl

/-- A `C^k` bound is simultaneous control of every frame-coordinate derivative through order `k`. -/
theorem chartCkSeminorm_le_iff (x : U) (K : Compacts (extChartAt I x).target)
    (k : ℕ) (hk : k ≤ n) (s : Cₛ^n⟮I; F, V⟯) {r : ℝ} (hr : 0 ≤ r) :
    chartCkSeminorm e hU x K k hk s ≤ r ↔ ∀ (m : ℕ) (hm : m ≤ k), ∀ z ∈ K,
      ‖ContMDiffMap.chartIteratedFDeriv (frameCoordinates e hU s) x m
        ((Nat.cast_le.mpr hm).trans hk) z‖ ≤ r :=
  ContMDiffMap.chartCkSeminorm_le_iff x K k hk _ hr

/-- Strict `C^k` control is simultaneous strict control of all the coordinate derivatives. -/
theorem chartCkSeminorm_lt_iff (x : U) (K : Compacts (extChartAt I x).target)
    (k : ℕ) (hk : k ≤ n) (s : Cₛ^n⟮I; F, V⟯) {r : ℝ} (hr : 0 < r) :
    chartCkSeminorm e hU x K k hk s < r ↔ ∀ (m : ℕ) (hm : m ≤ k), ∀ z ∈ K,
      ‖ContMDiffMap.chartIteratedFDeriv (frameCoordinates e hU s) x m
        ((Nat.cast_le.mpr hm).trans hk) z‖ < r :=
  ContMDiffMap.chartCkSeminorm_lt_iff x K k hk _ hr

/-- Raising the order increases the compact chart/frame `C^k` seminorm. -/
theorem chartCkSeminorm_le_of_le (x : U) (K : Compacts (extChartAt I x).target)
    {k l : ℕ} (hkl : k ≤ l) (hl : l ≤ n) :
    chartCkSeminorm (I := I) e hU x K k ((Nat.cast_le.mpr hkl).trans hl) ≤
      chartCkSeminorm e hU x K l hl :=
  Seminorm.comp_mono _ (ContMDiffMap.chartCkSeminorm_le_of_le x K hkl hl)

/-- Each compact chart/frame derivative seminorm of order `m ≤ k` is bounded by the compact
chart/frame `C^k` seminorm. -/
theorem chartDerivativeSeminorm_le_chartCkSeminorm (x : U) (K : Compacts (extChartAt I x).target)
    {m k : ℕ} (hmk : m ≤ k) (hk : k ≤ n) :
    chartDerivativeSeminorm (I := I) e hU x K m ((Nat.cast_le.mpr hmk).trans hk) ≤
      chartCkSeminorm e hU x K k hk :=
  Seminorm.comp_mono _ (ContMDiffMap.chartDerivativeSeminorm_le_chartCkSeminorm x K _ hk hmk)

/-- The `C^k` seminorm on the empty compact set is zero. -/
@[simp]
theorem chartCkSeminorm_bot (x : U) (k : ℕ) (hk : k ≤ n) :
    chartCkSeminorm (I := I) e hU x ⊥ k hk = 0 := by
  rw [chartCkSeminorm, ContMDiffMap.chartCkSeminorm_bot, Seminorm.zero_comp]

/-- A compact chart/frame `C^k` ball controls differences of the actual coordinate jets. -/
theorem mem_ball_chartCkSeminorm_iff (x : U) (K : Compacts (extChartAt I x).target)
    (k : ℕ) (hk : k ≤ n) (s t : Cₛ^n⟮I; F, V⟯) {r : ℝ} (hr : 0 < r) :
    t ∈ (chartCkSeminorm e hU x K k hk).ball s r ↔
      ∀ (m : ℕ) (hm : m ≤ k), ∀ z ∈ K,
        ‖ContMDiffMap.chartIteratedFDeriv (frameCoordinates e hU t) x m
            ((Nat.cast_le.mpr hm).trans hk) z -
          ContMDiffMap.chartIteratedFDeriv (frameCoordinates e hU s) x m
            ((Nat.cast_le.mpr hm).trans hk) z‖ < r := by
  rw [Seminorm.mem_ball, chartCkSeminorm, Seminorm.comp_apply, map_sub]
  exact ContMDiffMap.mem_ball_chartCkSeminorm_iff x K k hk _ _ hr

/-- Vanishing of the order-zero seminorm is exactly vanishing of the section at all points
represented by the compact coordinate set. In particular the seminorms detect section values. -/
theorem chartDerivativeSeminorm_zero_eq_zero_iff (x : U) (K : Compacts (extChartAt I x).target)
    (s : Cₛ^n⟮I; F, V⟯) :
    chartDerivativeSeminorm e hU x K 0 (by simp) s = 0 ↔
      ∀ z ∈ K, s ((extChartAt I x).symm z : U) = 0 := by
  have heq : chartDerivativeSeminorm e hU x K 0 (by simp) s = 0 ↔
      chartDerivativeSeminorm e hU x K 0 (by simp) s ≤ 0 :=
    ⟨le_of_eq, fun h => le_antisymm h (apply_nonneg _ _)⟩
  rw [heq, chartDerivativeSeminorm_le_iff e hU x K 0 (by simp) s le_rfl]
  constructor
  · intro h z hz
    have hjet := norm_eq_zero.mp (le_antisymm (h z hz) (norm_nonneg _))
    have hval := congrArg (fun L : E [×0]→L[𝕜] F => L (fun i => i.elim0)) hjet
    have hc : frameCoordinates e hU s ((extChartAt I x).symm z) = 0 := by
      exact (ContMDiffMap.chartIteratedFDeriv_zero_apply
        (frameCoordinates e hU s) x z (fun i => i.elim0)).symm.trans (by
          -- Normalize the chart-target subtype in the continuous-map coercion.
          convert! hval using 1)
    apply (frameCoordinates_eq_iff e hU s 0 ((extChartAt I x).symm z)).mp
    simpa using hc
  · intro h z hz
    have hc := (frameCoordinates_eq_iff e hU s 0 ((extChartAt I x).symm z)).mpr (h z hz)
    have hjet : ContMDiffMap.chartIteratedFDeriv (frameCoordinates e hU s) x 0 (by simp) z = 0 := by
      ext v
      exact (ContMDiffMap.chartIteratedFDeriv_zero_apply
        (frameCoordinates e hU s) x z v).trans (by simpa using hc)
    exact le_of_eq ((congrArg norm hjet).trans (norm_zero))

/-- The compact order-zero chart seminorms detect the restriction of a section to the frame
domain. This is the separation property needed for the smooth-section seminorm topology. -/
theorem forall_chartDerivativeSeminorm_zero_eq_zero_iff (s : Cₛ^n⟮I; F, V⟯) :
    (∀ (x : U) (K : Compacts (extChartAt I x).target),
      chartDerivativeSeminorm e hU x K 0 (by simp) s = 0) ↔ ∀ x : U, s x = 0 := by
  constructor
  · intro h x
    let z : (extChartAt I x).target := ⟨extChartAt I x x, mem_extChartAt_target x⟩
    let K : Compacts (extChartAt I x).target := ⟨{z}, isCompact_singleton⟩
    have hz := (chartDerivativeSeminorm_zero_eq_zero_iff e hU x K s).mp (h x K) z
      (mem_singleton z)
    -- Rewrite the point before the dependent fibre and its zero are elaborated.
    have hpoint : (extChartAt I x).symm z = x := extChartAt_to_inv x
    rw [hpoint] at hz
    exact hz
  · intro h x K
    exact (chartDerivativeSeminorm_zero_eq_zero_iff e hU x K s).mpr fun z _ => h _

omit [IsManifold I n M] in
private theorem eqOn_frameCoordinates_comp_symm
    (e₁ e₂ : Trivialization F (π F V)) [MemTrivializationAtlas e₁] [MemTrivializationAtlas e₂]
    {U₁ U₂ : Opens M} (hU₁ : (U₁ : Set M) ⊆ e₁.baseSet) (hU₂ : (U₂ : Set M) ⊆ e₂.baseSet)
    (x₁ : U₁) (x₂ : U₂) {S : Set E} (hS₁ : S ⊆ (extChartAt I x₁).target)
    (hmemS : ∀ z ∈ S,
      (extChartAt I (x₁ : M)).symm z ∈ (U₂ : Set M) ∩ (extChartAt I (x₂ : M)).source)
    (hST : MapsTo (I.extendCoordChange (chartAt H (x₁ : M)) (chartAt H (x₂ : M)))
      S (extChartAt I x₂).target)
    (s : Cₛ^n⟮I; F, V⟯) :
    EqOn ((e₁.frameCoordinates hU₁ s) ∘ (extChartAt I x₁).symm)
      (fun y ↦ (e₂.coordChangeL 𝕜 e₁ ((extChartAt I (x₁ : M)).symm y) : F →L[𝕜] F)
        (((e₂.frameCoordinates hU₂ s) ∘ (extChartAt I x₂).symm)
          (I.extendCoordChange (chartAt H (x₁ : M)) (chartAt H (x₂ : M)) y))) S := fun w hw ↦ by
  have hcoe₁ := U₁.coe_extChartAt_symm_apply x₁ (hS₁ hw)
  have hcoe₂ := U₂.coe_extChartAt_symm_apply x₂ (hST hw)
  have hpt : ((extChartAt I x₂).symm
      (I.extendCoordChange (chartAt H (x₁ : M)) (chartAt H (x₂ : M)) w) : M) =
      ((extChartAt I x₁).symm w : M) := by
    rw [hcoe₂, hcoe₁, I.extendCoordChange_chartAt_apply]
    exact (extChartAt I (x₂ : M)).left_inv (hmemS w hw).2
  simp only [Function.comp_apply, frameCoordinates_apply, ContinuousLinearEquiv.coe_coe]
  rw [hpt, ← hcoe₁]
  exact ((e₂.coordChangeL_apply e₁ ⟨hU₂ (by rw [hcoe₁]; exact (hmemS w hw).1),
    hU₁ ((extChartAt I x₁).symm w).property⟩ _).trans
    (congrArg (fun v ↦ (e₁ ⟨((extChartAt I x₁).symm w : M), v⟩).2)
      (e₂.symm_apply_apply_mk (hU₂ (by rw [hcoe₁]; exact (hmemS w hw).1)) _))).symm

/-- On a compact overlap of two bundle trivializations and inherited charts (boundary and corner
charts included), the `C^k` seminorm in the first trivialization and chart is bounded by a positive
multiple of the `C^k` seminorm in the second on any compact piece containing the transformed
coordinates. -/
theorem exists_chartCkSeminorm_le_coordChange
    (e₁ e₂ : Trivialization F (π F V)) [MemTrivializationAtlas e₁] [MemTrivializationAtlas e₂]
    {U₁ U₂ : Opens M} (hU₁ : (U₁ : Set M) ⊆ e₁.baseSet) (hU₂ : (U₂ : Set M) ⊆ e₂.baseSet)
    (x₁ : U₁) (x₂ : U₂)
    (P : Compacts (extChartAt I x₁).target) (Q : Compacts (extChartAt I x₂).target)
    (hoverlap : ∀ z ∈ P, ∃ hy₂ : ((extChartAt I x₁).symm z : M) ∈ U₂,
      ∃ hy : (⟨((extChartAt I x₁).symm z : M), hy₂⟩ : U₂) ∈ (extChartAt I x₂).source,
        (⟨extChartAt I x₂ ⟨((extChartAt I x₁).symm z : M), hy₂⟩,
          (extChartAt I x₂).map_source hy⟩ : (extChartAt I x₂).target) ∈ Q)
    (k : ℕ) (hk : k ≤ n) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : Cₛ^n⟮I; F, V⟯,
      e₁.chartCkSeminorm hU₁ x₁ P k hk s ≤ C * e₂.chartCkSeminorm hU₂ x₂ Q k hk s := by
  obtain ⟨W, hW, hPS, hmemS, hSτ, hST⟩ := TauCeti.exists_open_extChartAt_overlap x₁ x₂
    (P := (P : Set (extChartAt I x₁).target))
    fun z hz ↦ let ⟨hy₂, hy, _⟩ := hoverlap z hz; ⟨hy₂, hy⟩
  set S : Set E := (extChartAt I x₁).target ∩ W
  set τ := I.extendCoordChange (chartAt H (x₁ : M)) (chartAt H (x₂ : M))
  have hL : ContDiffOn 𝕜 k
      (fun z ↦ (e₂.coordChangeL 𝕜 e₁ ((extChartAt I (x₁ : M)).symm z) : F →L[𝕜] F)) S :=
    (e₂.contDiffOn_coordChangeL_comp_symm e₁ (x₁ : M)
      (inter_subset_left.trans (U₁.extChartAt_target_subset x₁)) fun z hz ↦
        ⟨hU₂ (hmemS z hz).1, hU₁ (by
          rw [← U₁.coe_extChartAt_symm_apply x₁ hz.1]
          exact ((extChartAt I x₁).symm z).property)⟩).of_le hk
  have hτ : ContDiffOn 𝕜 k τ S :=
    ((I.contDiffOn_extendCoordChange (StructureGroupoid.chart_mem_maximalAtlas _ (x₁ : M))
      (StructureGroupoid.chart_mem_maximalAtlas _ (x₂ : M))).mono hSτ).of_le hk
  choose C hC using fun i : Fin (k + 1) ↦
    ContDiffOn.exists_norm_iteratedFDerivWithin_clm_apply_comp_le (n := i)
      (hL.of_le (Nat.cast_le.mpr (Nat.le_of_lt_succ i.isLt)))
      (hτ.of_le (Nat.cast_le.mpr (Nat.le_of_lt_succ i.isLt)))
      ((uniqueDiffOn_extChartAt_target x₁).inter hW) (uniqueDiffOn_extChartAt_target x₂) hST
      (P.isCompact.image continuous_subtypeVal) hPS
  refine ⟨∑ i, |C i| + 1, by positivity, fun s ↦ ?_⟩
  set φ := (e₂.frameCoordinates hU₂ s) ∘ (extChartAt I x₂).symm
  have hφ : ContDiffOn 𝕜 k φ (extChartAt I x₂).target :=
    (((e₂.frameCoordinates hU₂ s).contMDiff.comp_contMDiffOn
      (contMDiffOn_extChartAt_symm x₂)).contDiffOn).of_le hk
  have hδ := apply_nonneg (e₂.chartCkSeminorm hU₂ x₂ Q k hk) s
  refine (e₁.chartCkSeminorm_le_iff hU₁ x₁ P k hk s (by positivity)).mpr fun m hm z hzP ↦ ?_
  have hzS : (z : E) ∈ S := hPS ⟨z, hzP, rfl⟩
  rw [ContMDiffMap.chartIteratedFDeriv_self_target_apply,
    ← iteratedFDerivWithin_inter (hW.mem_nhds hzS.2),
    iteratedFDerivWithin_congr (eqOn_frameCoordinates_comp_symm e₁ e₂ hU₁ hU₂ x₁ x₂
      inter_subset_left hmemS hST s) hzS]
  let m' : Fin (k + 1) := ⟨m, Nat.lt_succ_of_le hm⟩
  refine (hC m' φ (hφ.of_le (Nat.cast_le.mpr hm)) (e₂.chartCkSeminorm hU₂ x₂ Q k hk s)
    (fun j hj _ hw ↦ ?_) z ⟨z, hzP, rfl⟩).trans ?_
  · obtain ⟨w, hwP, rfl⟩ := hw
    obtain ⟨hy₂, hy, hQ⟩ := hoverlap w hwP
    have hτeq : (⟨extChartAt I x₂ ⟨((extChartAt I x₁).symm w : M), hy₂⟩,
        (extChartAt I x₂).map_source hy⟩ : (extChartAt I x₂).target) =
        ⟨τ w, hST (hPS ⟨w, hwP, rfl⟩)⟩ :=
      Subtype.ext (Opens.extendCoordChange_chartAt_coe_apply x₁ x₂ w.property).symm
    have hQj := (e₂.chartCkSeminorm_le_iff hU₂ x₂ Q k hk s hδ).mp le_rfl j (hj.trans hm) _ hQ
    rwa [hτeq, ContMDiffMap.chartIteratedFDeriv_self_target_apply] at hQj
  · exact mul_le_mul_of_nonneg_right ((le_abs_self _).trans <|
      (Finset.single_le_sum (fun i _ ↦ abs_nonneg (C i)) (Finset.mem_univ m')).trans
        (le_add_of_nonneg_right zero_le_one)) hδ

end Bundle.Trivialization
