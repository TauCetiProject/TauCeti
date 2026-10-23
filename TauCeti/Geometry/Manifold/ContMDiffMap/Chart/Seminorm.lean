/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.ContMDiffMap.Chart.Topology
public import Mathlib.Analysis.Normed.Module.Seminorm.Norm
public import Mathlib.Topology.ContinuousMap.Compact

/-!
# Compact chart seminorms

For vector-valued maps on a manifold, the supremum norm of a coordinate derivative on a
fixed compact coordinate set is a seminorm. Taking the maximum through order `k` gives the
compact chart `C^k` seminorm. Its balls are exactly the simultaneous strict bounds on all
coordinate derivatives through that order, and are neighborhoods in the weak Whitney topology.
Finite intersections therefore express compact chart control of perturbations, including the
`C²` control used to preserve nondegenerate critical points.

The compact sets live in the target of an extended source chart. Derivatives are taken within
that target, so the construction also applies to manifolds with boundary and corners. Empty
compact sets give the zero seminorm. No finite-dimensionality or local compactness is required.

The construction uses `ContMDiffMap.chartIteratedFDeriv` and Mathlib's supremum norm on
continuous maps on a compact space, rather than choosing extrema of the derivative norms.

## References

* M. Hirsch, *Differential Topology*, GTM 33, Chapter 2, §1.
-/

public section

open Set Topology
open scoped Manifold TauCeti.ManifoldWeakWhitney

namespace ContMDiffMap

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {n : WithTop ℕ∞} [IsManifold I n M]

/-- The supremum norm of the `m`th coordinate derivative on a compact coordinate set. -/
noncomputable def chartDerivativeSeminorm (x : M)
    (K : TopologicalSpace.Compacts (extChartAt I x).target) (m : ℕ) (hm : m ≤ n) :
    Seminorm 𝕜 C^n⟮I, M; 𝓘(𝕜, F), F⟯ :=
  (normSeminorm 𝕜 C(K, E [×m]→L[𝕜] F)).comp
    ({ toFun := fun f ↦ (chartIteratedFDerivLinearMap x m hm f).restrict K
       map_add' := fun f g ↦ by rw [map_add]; rfl
       map_smul' := fun c f ↦ by rw [map_smul]; rfl } :
      C^n⟮I, M; 𝓘(𝕜, F), F⟯ →ₗ[𝕜] C(K, E [×m]→L[𝕜] F))

/-- The derivative seminorm is the supremum norm of the restricted chart jet. -/
theorem chartDerivativeSeminorm_apply (x : M)
    (K : TopologicalSpace.Compacts (extChartAt I x).target) (m : ℕ) (hm : m ≤ n)
    (f : C^n⟮I, M; 𝓘(𝕜, F), F⟯) :
    chartDerivativeSeminorm x K m hm f = ‖(chartIteratedFDeriv f x m hm).restrict K‖ := by
  rw [chartDerivativeSeminorm, Seminorm.comp_apply]
  simp only [coe_normSeminorm, LinearMap.coe_mk, AddHom.coe_mk]
  exact congrArg (fun j : C((extChartAt I x).target, E [×m]→L[𝕜] F) ↦ ‖j.restrict K‖)
    (chartIteratedFDerivLinearMap_apply x m hm f)

/-- A nonnegative bound on the derivative seminorm is a pointwise bound on the compact set. -/
theorem chartDerivativeSeminorm_le_iff (x : M)
    (K : TopologicalSpace.Compacts (extChartAt I x).target) (m : ℕ) (hm : m ≤ n)
    (f : C^n⟮I, M; 𝓘(𝕜, F), F⟯) {r : ℝ} (hr : 0 ≤ r) :
    chartDerivativeSeminorm x K m hm f ≤ r ↔
      ∀ z ∈ K, ‖chartIteratedFDeriv f x m hm z‖ ≤ r := by
  rw [chartDerivativeSeminorm_apply, ContinuousMap.norm_le _ hr]
  exact Subtype.forall

/-- A positive strict bound on the derivative seminorm is a pointwise strict bound on the
compact set. Compactness makes the pointwise strict bounds uniform. -/
theorem chartDerivativeSeminorm_lt_iff (x : M)
    (K : TopologicalSpace.Compacts (extChartAt I x).target) (m : ℕ) (hm : m ≤ n)
    (f : C^n⟮I, M; 𝓘(𝕜, F), F⟯) {r : ℝ} (hr : 0 < r) :
    chartDerivativeSeminorm x K m hm f < r ↔
      ∀ z ∈ K, ‖chartIteratedFDeriv f x m hm z‖ < r := by
  rw [chartDerivativeSeminorm_apply, ContinuousMap.norm_lt_iff _ hr]
  exact Subtype.forall

/-- Enlarging the compact coordinate set can only increase its derivative seminorm. -/
theorem chartDerivativeSeminorm_mono (x : M)
    {K L : TopologicalSpace.Compacts (extChartAt I x).target} (hKL : K ≤ L)
    (m : ℕ) (hm : m ≤ n) :
    chartDerivativeSeminorm (F := F) x K m hm ≤ chartDerivativeSeminorm x L m hm := by
  intro f
  rw [chartDerivativeSeminorm_apply, chartDerivativeSeminorm_apply]
  exact ContinuousMap.norm_restrict_mono_set _ hKL

/-- The derivative seminorm on the empty coordinate set is zero. -/
@[simp]
theorem chartDerivativeSeminorm_bot (x : M) (m : ℕ) (hm : m ≤ n) :
    chartDerivativeSeminorm (I := I) (F := F) x ⊥ m hm = 0 := by
  ext f
  apply le_antisymm
  · exact (chartDerivativeSeminorm_le_iff x ⊥ m hm f le_rfl).mpr
      (by intro z hz; exact False.elim hz)
  · exact apply_nonneg _ _

/-- A compact coordinate derivative seminorm is continuous in the weak Whitney topology. -/
theorem continuous_chartDerivativeSeminorm (x : M)
    (K : TopologicalSpace.Compacts (extChartAt I x).target) (m : ℕ) (hm : m ≤ n) :
    Continuous (chartDerivativeSeminorm (F := F) x K m hm) := by
  have hjet : Continuous (fun f : C^n⟮I, M; 𝓘(𝕜, F), F⟯ ↦
      (chartIteratedFDeriv f x m hm).restrict (K : Set _)) :=
    (ContinuousMap.continuous_restrict (K : Set (extChartAt I x).target)).comp
      (continuous_chartIteratedFDeriv (I := I) (F := F) x m hm)
  exact ((continuous_norm (E := C(K, E [×m]→L[𝕜] F))).comp hjet).congr
    (fun f ↦ (chartDerivativeSeminorm_apply x K m hm f).symm)

/-- The compact chart `C^k` seminorm: the maximum of the coordinate derivative seminorms
through order `k`, including order zero. -/
noncomputable def chartCkSeminorm (x : M)
    (K : TopologicalSpace.Compacts (extChartAt I x).target) (k : ℕ) (hk : k ≤ n) :
    Seminorm 𝕜 C^n⟮I, M; 𝓘(𝕜, F), F⟯ :=
  Finset.univ.sup fun m : Fin (k + 1) ↦
    chartDerivativeSeminorm x K m ((Nat.cast_le.mpr (Nat.le_of_lt_succ m.isLt)).trans hk)

/-- A bound on the compact `C^k` seminorm is exactly the bounds on every derivative through
order `k`. -/
theorem chartCkSeminorm_le_iff (x : M)
    (K : TopologicalSpace.Compacts (extChartAt I x).target) (k : ℕ) (hk : k ≤ n)
    (f : C^n⟮I, M; 𝓘(𝕜, F), F⟯) {r : ℝ} (hr : 0 ≤ r) :
    chartCkSeminorm x K k hk f ≤ r ↔
      ∀ (m : ℕ) (hm : m ≤ k), ∀ z ∈ K,
        ‖chartIteratedFDeriv f x m ((Nat.cast_le.mpr hm).trans hk) z‖ ≤ r := by
  constructor
  · intro h m hm
    exact (chartDerivativeSeminorm_le_iff x K m _ f hr).mp
      ((Seminorm.le_finset_sup_apply (Finset.mem_univ (⟨m, by omega⟩ : Fin (k + 1)))).trans h)
  · intro h
    exact Seminorm.finset_sup_apply_le hr fun m _ ↦
      (chartDerivativeSeminorm_le_iff x K m _ f hr).mpr (h m (by omega))

/-- The compact chart `C^k` seminorm on the empty coordinate set is zero. -/
@[simp]
theorem chartCkSeminorm_bot (x : M) (k : ℕ) (hk : k ≤ n) :
    chartCkSeminorm (I := I) (F := F) x ⊥ k hk = 0 := by
  ext f
  apply le_antisymm
  · exact (chartCkSeminorm_le_iff x ⊥ k hk f le_rfl).mpr
      (by intro m hm z hz; exact False.elim hz)
  · exact apply_nonneg _ _

/-- Positive strict `C^k` control is equivalent to pointwise strict control of every coordinate
derivative through order `k`. -/
theorem chartCkSeminorm_lt_iff (x : M)
    (K : TopologicalSpace.Compacts (extChartAt I x).target) (k : ℕ) (hk : k ≤ n)
    (f : C^n⟮I, M; 𝓘(𝕜, F), F⟯) {r : ℝ} (hr : 0 < r) :
    chartCkSeminorm x K k hk f < r ↔
      ∀ (m : ℕ) (hm : m ≤ k), ∀ z ∈ K,
        ‖chartIteratedFDeriv f x m ((Nat.cast_le.mpr hm).trans hk) z‖ < r := by
  constructor
  · intro h m hm
    exact (chartDerivativeSeminorm_lt_iff x K m _ f hr).mp
      ((Seminorm.le_finset_sup_apply (Finset.mem_univ (⟨m, by omega⟩ : Fin (k + 1)))).trans_lt h)
  · intro h
    exact Seminorm.finset_sup_apply_lt hr fun m _ ↦
      (chartDerivativeSeminorm_lt_iff x K m _ f hr).mpr (h m (by omega))

/-- A positive compact `C^k` ball bounds the difference of the coordinate derivatives of
its two maps, simultaneously through order `k`. -/
theorem mem_ball_chartCkSeminorm_iff (x : M)
    (K : TopologicalSpace.Compacts (extChartAt I x).target) (k : ℕ) (hk : k ≤ n)
    (f g : C^n⟮I, M; 𝓘(𝕜, F), F⟯) {r : ℝ} (hr : 0 < r) :
    g ∈ (chartCkSeminorm x K k hk).ball f r ↔
      ∀ (m : ℕ) (hm : m ≤ k), ∀ z ∈ K,
        ‖chartIteratedFDeriv g x m ((Nat.cast_le.mpr hm).trans hk) z -
          chartIteratedFDeriv f x m ((Nat.cast_le.mpr hm).trans hk) z‖ < r := by
  rw [Seminorm.mem_ball, chartCkSeminorm_lt_iff x K k hk (g - f) hr]
  simp only [chartIteratedFDeriv_sub, ContinuousMap.sub_apply]

/-- A ball of a compact coordinate derivative seminorm is weak Whitney open. -/
theorem isOpen_ball_chartDerivativeSeminorm (x : M)
    (K : TopologicalSpace.Compacts (extChartAt I x).target) (m : ℕ) (hm : m ≤ n)
    (f : C^n⟮I, M; 𝓘(𝕜, F), F⟯) (r : ℝ) :
    IsOpen ((chartDerivativeSeminorm x K m hm).ball f r) := by
  exact isOpen_lt
    ((continuous_chartDerivativeSeminorm x K m hm).comp
      (continuous_sub_manifoldWeakWhitney.comp (continuous_id.prodMk continuous_const)))
    continuous_const

/-- A compact chart `C^k` ball about a map is open in the weak Whitney topology. -/
theorem isOpen_ball_chartCkSeminorm (x : M)
    (K : TopologicalSpace.Compacts (extChartAt I x).target) (k : ℕ) (hk : k ≤ n)
    (f : C^n⟮I, M; 𝓘(𝕜, F), F⟯) (r : ℝ) :
    IsOpen ((chartCkSeminorm x K k hk).ball f r) := by
  by_cases hr : 0 < r
  · rw [chartCkSeminorm, Seminorm.ball_finset_sup_eq_iInter _ _ _ hr]
    exact isOpen_iInter_of_finite fun _ ↦ isOpen_iInter_of_finite fun _ ↦
      isOpen_ball_chartDerivativeSeminorm x K _ _ f r
  · rw [Seminorm.ball_eq_emptyset _ (le_of_not_gt hr)]
    exact isOpen_empty

/-- Every positive compact chart `C^k` tolerance gives a weak Whitney neighborhood. -/
theorem ball_chartCkSeminorm_mem_nhds (x : M)
    (K : TopologicalSpace.Compacts (extChartAt I x).target) (k : ℕ) (hk : k ≤ n)
    (f : C^n⟮I, M; 𝓘(𝕜, F), F⟯) {r : ℝ} (hr : 0 < r) :
    (chartCkSeminorm x K k hk).ball f r ∈ 𝓝 f :=
  (isOpen_ball_chartCkSeminorm x K k hk f r).mem_nhds (by simpa using hr)

end ContMDiffMap
