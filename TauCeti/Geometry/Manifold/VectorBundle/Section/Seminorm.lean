/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
public import TauCeti.Geometry.Manifold.ContMDiffMap.Chart.Seminorm

/-!
# Compact chart seminorms for bundle sections

A smooth bundle trivialization sends sections to vector-valued maps on its base set.
Composing this linear coordinate map with `ContMDiffMap.chartDerivativeSeminorm` and
`ContMDiffMap.chartCkSeminorm` gives the compact chart/frame seminorms of sections.
These measure the actual coordinate derivatives, including order zero, without requiring
an ambient norm on the fibres or choosing a connection. They supply the local controls
used in smooth-section and compactly supported test-section topologies.

The construction allows finite and infinite regularity, manifolds with corners, and
arbitrary normed model fibres. No topology on the section space is installed here.
-/

public section

noncomputable section

open Set TopologicalSpace Bundle
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
      ((e.contMDiffAt_section_iff (hU x.2)).mp (s.contMDiff x))⟩
  map_add' s t := by
    ext x
    -- Unpack the bundled maps before applying fibrewise linearity.
    change (e ⟨(x : M), s x + t x⟩).2 = (e ⟨(x : M), s x⟩).2 +
      (e ⟨(x : M), t x⟩).2
    simp only [← e.continuousLinearMapAt_apply_of_mem 𝕜 (hU x.2), map_add]
  map_smul' c s := by
    ext x
    -- Unpack the bundled maps before applying fibrewise linearity.
    change (e ⟨(x : M), c • s x⟩).2 = c • (e ⟨(x : M), s x⟩).2
    simp only [← e.continuousLinearMapAt_apply_of_mem 𝕜 (hU x.2), map_smul]

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
    simpa only [e.symm_apply_apply_mk (hU x.2)] using congrArg (e.symm x) h
  · intro h
    simp only [frameCoordinates_apply, h]

/-- Coordinates in two smooth trivializations are related by their native transition map. -/
theorem frameCoordinates_coordChange (e' : Trivialization F (π F V))
    [MemTrivializationAtlas e'] (hU' : (U : Set M) ⊆ e'.baseSet)
    (s : Cₛ^n⟮I; F, V⟯) (x : U) :
    e.coordChangeL 𝕜 e' x (frameCoordinates e hU s x) = frameCoordinates e' hU' s x := by
  simp only [frameCoordinates_apply, e.coordChangeL_apply e' ⟨hU x.2, hU' x.2⟩,
    e.symm_apply_apply_mk (hU x.2)]

variable [IsManifold I n M]

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

/-- The compact chart/frame `C^k` seminorm of a section, including order zero. -/
def chartCkSeminorm (x : U) (K : Compacts (extChartAt I x).target) (k : ℕ) (hk : k ≤ n) :
    Seminorm 𝕜 Cₛ^n⟮I; F, V⟯ :=
  (ContMDiffMap.chartCkSeminorm x K k hk).comp (frameCoordinates e hU)

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

end Bundle.Trivialization
