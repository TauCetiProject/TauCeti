/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.UniformLimitsDeriv
public import Mathlib.Topology.MetricSpace.Equicontinuity
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.Sequences
import TauCeti.Topology.ContinuousMap.Ascoli
import TauCeti.Topology.Algebra.Module.FiniteDimension

/-!
# Equicontinuity from bounds on derivatives

A family of differentiable maps on an open subset of a proper real normed space is
equicontinuous if its derivatives are uniformly bounded on each compact subset. The
mean-value inequality supplies a common Lipschitz bound on a small ball around each point.
This criterion is useful when applying Arzelà–Ascoli to families controlled by interior
estimates, without requiring a global bound on the derivatives.

Applied to the derivatives themselves, Arzelà–Ascoli gives convergence in `C¹`
(`TauCeti.exists_strictMono_tendstoLocallyUniformlyOn_fderiv`): if `uₙ → v` pointwise on an open
subset of a finite-dimensional space, with values in a finite-dimensional space, and the
derivatives `Duₙ` are equicontinuous and bounded at each point, then along a subsequence
`Duₙ → Dv` locally uniformly, and `v` is `C¹`. Equicontinuity of the derivatives is what interior
estimates for second derivatives provide.

Iterating the `C¹` statement gives **Arzelà–Ascoli in `Cᵏ`**
(`TauCeti.exists_strictMono_tendstoLocallyUniformlyOn_iteratedFDeriv`): if the derivatives of
order at most `k + 1` of the `uₙ` are bounded on each compact subset of `Ω`, uniformly in `n`,
then along a subsequence the `uₙ` converge to a `Cᵏ` map together with their derivatives of order
at most `k`, locally uniformly on `Ω`.
-/

public section

open Filter Metric Set Topology
open scoped NNReal

namespace TauCeti

variable {E F ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {Ω : Set E} {u : ι → E → F}

/-- Uniform bounds on derivatives on compact subsets of an open set imply equicontinuity
there. No compactness or completeness assumption on the target is needed. -/
theorem equicontinuousOn_of_forall_isCompact_norm_fderiv_le
    (hΩ : IsOpen Ω) (hu : ∀ i, DifferentiableOn ℝ (u i) Ω)
    (hb : ∀ C, IsCompact C → C ⊆ Ω → ∃ M, ∀ i, ∀ x ∈ C, ‖fderiv ℝ (u i) x‖ ≤ M) :
    EquicontinuousOn u Ω := by
  rw [← equicontinuous_restrict_iff]
  intro x
  obtain ⟨r, hr, hrΩ⟩ := Metric.isOpen_iff.mp hΩ x x.2
  have hball : closedBall (x : E) (r / 2) ⊆ Ω :=
    (closedBall_subset_ball (by linarith : r / 2 < r)).trans hrΩ
  obtain ⟨M, hM⟩ := hb _ (isCompact_closedBall (x : E) (r / 2)) hball
  let L : ℝ≥0 := ⟨max M 0, le_max_right _ _⟩
  have hLip : ∀ i, LipschitzOnWith L (u i) (closedBall (x : E) (r / 2)) := by
    intro i
    apply (convex_closedBall (x : E) (r / 2)).lipschitzOnWith_of_nnNorm_fderiv_le (𝕜 := ℝ)
    · intro y hy
      exact (hu i y (hball hy)).differentiableAt (hΩ.mem_nhds (hball hy))
    · intro y hy
      exact_mod_cast (hM i y hy).trans (le_max_left M 0)
  have hmod : Continuous (fun y : Ω ↦ (L : ℝ) * dist (x : E) (y : E)) :=
    continuous_const.mul (continuous_const.dist continuous_subtype_val)
  apply Metric.equicontinuousAt_of_continuity_modulus
    (fun y : Ω ↦ (L : ℝ) * dist (x : E) (y : E))
    (by simpa using (hmod.continuousAt (x := x)).tendsto) _
  have hnear : ∀ᶠ y : Ω in 𝓝 x, (y : E) ∈ ball (x : E) (r / 2) :=
    continuous_subtype_val.continuousAt (ball_mem_nhds (x : E) (by positivity))
  filter_upwards [hnear] with y hy i
  exact (hLip i).dist_le_mul _ (mem_closedBall_self (by positivity)) _
    (ball_subset_closedBall hy)

/-- **Arzelà–Ascoli in `C¹`.** Let `uₙ` be differentiable on an open subset `Ω` of a
finite-dimensional space, with values in a finite-dimensional space, and converge pointwise on
`Ω` to `v`. If the derivatives `Duₙ` are equicontinuous on `Ω` and bounded at each point, then
`v` is `C¹` on `Ω` and, along a subsequence, `Duₙ → Dv` locally uniformly on `Ω`. -/
theorem exists_strictMono_tendstoLocallyUniformlyOn_fderiv [FiniteDimensional ℝ E]
    [FiniteDimensional ℝ F] {u : ℕ → E → F} {v : E → F} (hΩ : IsOpen Ω)
    (hu : ∀ n, DifferentiableOn ℝ (u n) Ω) (hequi : EquicontinuousOn (fun n ↦ fderiv ℝ (u n)) Ω)
    (hbd : ∀ x ∈ Ω, ∃ M, ∀ n, ‖fderiv ℝ (u n) x‖ ≤ M)
    (hlim : ∀ x ∈ Ω, Tendsto (fun n ↦ u n x) atTop (𝓝 (v x))) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ContDiffOn ℝ 1 v Ω ∧
      TendstoLocallyUniformlyOn (fun n ↦ fderiv ℝ (u (φ n))) (fderiv ℝ v) atTop Ω := by
  classical
  let : LocallyCompactSpace Ω := hΩ.locallyCompactSpace
  let U : ℕ → C(Ω, E →L[ℝ] F) := fun n ↦
    ⟨Ω.domRestrict (fderiv ℝ (u n)), (hequi.continuousOn n).domRestrict⟩
  have hcompact : IsCompact (closure (range U)) :=
    ArzelaAscoli.isCompact_closure_range_of_equicontinuous
      ((equicontinuous_restrict_iff _).mpr hequi) fun x ↦
        ⟨closedBall 0 (hbd x x.2).choose, isCompact_closedBall _ _,
          fun n ↦ mem_closedBall_zero_iff.2 ((hbd x x.2).choose_spec n)⟩
  obtain ⟨a, -, φ, hφ, hlimU⟩ := hcompact.tendsto_subseq (x := U)
    (fun n ↦ subset_closure (mem_range_self n))
  -- Extend the limit of the derivatives by zero off `Ω`.
  let G : E → E →L[ℝ] F := fun z ↦ if hz : z ∈ Ω then a ⟨z, hz⟩ else 0
  have hG : G ∘ (Subtype.val : Ω → E) = fun x : Ω ↦ a x := by
    funext x
    simp [G, x.2]
  have hconv : TendstoLocallyUniformlyOn (fun n ↦ fderiv ℝ (u (φ n))) G atTop Ω := by
    rw [tendstoLocallyUniformlyOn_iff_tendstoLocallyUniformly_comp_coe, hG]
    exact ContinuousMap.tendsto_iff_tendstoLocallyUniformly.mp hlimU
  -- The limit of the derivatives is the derivative of the limit.
  have hderiv : ∀ x ∈ Ω, HasFDerivAt v (G x) x := fun x hx ↦
    hasFDerivAt_of_tendstoLocallyUniformlyOn hΩ hconv
      (fun n y hy ↦ ((hu (φ n)) y hy).differentiableAt (hΩ.mem_nhds hy) |>.hasFDerivAt)
      (fun y hy ↦ (hlim y hy).comp hφ.tendsto_atTop) hx
  have hfd : EqOn (fderiv ℝ v) G Ω := fun x hx ↦ (hderiv x hx).fderiv
  have hGc : ContinuousOn G Ω := hconv.continuousOn (Eventually.of_forall fun n ↦
    (hequi.comp φ).continuousOn n).frequently
  refine ⟨φ, hφ, ?_, hconv.congr_right fun x hx ↦ (hfd hx).symm⟩
  exact (contDiffOn_succ_iff_fderiv_of_isOpen (n := 0) hΩ).2
    ⟨fun x hx ↦ (hderiv x hx).differentiableAt.differentiableWithinAt, by simp,
      contDiffOn_zero.2 (hGc.congr hfd)⟩

omit [ProperSpace E] in
/-- A map `C^(k+1)` on an open set has differentiable derivatives of order at most `k` there. -/
private theorem differentiableOn_iteratedFDeriv_of_contDiffOn (hΩ : IsOpen Ω) {f : E → F}
    {k m : ℕ} (hf : ContDiffOn ℝ (k + 1) f Ω) (hm : m ≤ k) :
    DifferentiableOn ℝ (iteratedFDeriv ℝ m f) Ω :=
  (hf.differentiableOn_iteratedFDerivWithin (by exact_mod_cast Nat.lt_succ_of_le hm)
    hΩ.uniqueDiffOn).congr fun _ hx ↦ (iteratedFDerivWithin_of_isOpen m hΩ hx).symm

/-- The case `k = 0` of `TauCeti.exists_strictMono_tendstoLocallyUniformlyOn_iteratedFDeriv`. -/
private theorem exists_strictMono_tendstoLocallyUniformlyOn_iteratedFDeriv_zero
    [FiniteDimensional ℝ F] {u : ℕ → E → F} (hΩ : IsOpen Ω)
    (hu : ∀ n, ContDiffOn ℝ 1 (u n) Ω)
    (hbd : ∀ K, IsCompact K → K ⊆ Ω → ∃ M, ∀ n, ∀ j ≤ 1, ∀ x ∈ K,
      ‖iteratedFDeriv ℝ j (u n) x‖ ≤ M) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ v : E → F, ContinuousOn v Ω ∧
      TendstoLocallyUniformlyOn (fun n ↦ iteratedFDeriv ℝ 0 (u (φ n))) (iteratedFDeriv ℝ 0 v)
        atTop Ω := by
  -- Arzelà–Ascoli for the maps themselves, which are equicontinuous by the mean value bound.
  have hequi : EquicontinuousOn u Ω :=
    equicontinuousOn_of_forall_isCompact_norm_fderiv_le hΩ
      (fun n ↦ (hu n).differentiableOn (by simp)) fun K hK hKΩ ↦
        let ⟨M, hM⟩ := hbd K hK hKΩ
        ⟨M, fun n x hx ↦ by simpa [norm_iteratedFDeriv_one] using hM n 1 le_rfl x hx⟩
  have hbd₀ (x : Ω) : ∃ M, ∀ n, ‖u n x‖ ≤ M :=
    let ⟨M, hM⟩ := hbd {(x : E)} isCompact_singleton (singleton_subset_iff.2 x.2)
    ⟨M, fun n ↦ by simpa [norm_iteratedFDeriv_zero] using hM n 0 (Nat.zero_le _) x rfl⟩
  classical
  let : LocallyCompactSpace Ω := hΩ.locallyCompactSpace
  let U : ℕ → C(Ω, F) := fun n ↦ ⟨Ω.domRestrict (u n), (hequi.continuousOn n).domRestrict⟩
  have hcompact : IsCompact (closure (range U)) :=
    ArzelaAscoli.isCompact_closure_range_of_equicontinuous
      ((equicontinuous_restrict_iff _).mpr hequi) fun x ↦
        ⟨closedBall 0 (hbd₀ x).choose, isCompact_closedBall _ _,
          fun n ↦ mem_closedBall_zero_iff.2 ((hbd₀ x).choose_spec n)⟩
  obtain ⟨a, -, φ, hφ, hlimU⟩ := hcompact.tendsto_subseq (x := U)
    (fun n ↦ subset_closure (mem_range_self n))
  -- Extend the limit by zero off `Ω`.
  let v : E → F := fun z ↦ if hz : z ∈ Ω then a ⟨z, hz⟩ else 0
  have hv : Ω.domRestrict v = a := by
    funext x
    simp [v, Set.domRestrict, x.2]
  have hconv : TendstoLocallyUniformlyOn (fun n ↦ u (φ n)) v atTop Ω := by
    rw [tendstoLocallyUniformlyOn_iff_tendstoLocallyUniformly_comp_coe]
    exact (ContinuousMap.tendsto_iff_tendstoLocallyUniformly.mp hlimU).congr_right
      (fun x ↦ congrFun hv.symm x)
  refine ⟨φ, hφ, v, by rw [continuousOn_iff_continuous_domRestrict, hv]; exact a.continuous, ?_⟩
  simp only [iteratedFDeriv_zero_eq_comp]
  exact (continuousMultilinearCurryFin0 ℝ E F).symm.isometry.uniformContinuous
    |>.comp_tendstoLocallyUniformlyOn hconv

/-- The inductive step of `TauCeti.exists_strictMono_tendstoLocallyUniformlyOn_iteratedFDeriv`:
if the derivatives of order `k` of the `uₙ` converge to those of a `Cᵏ` map `v`, and the
derivatives of order `k + 1` and `k + 2` are bounded on compact sets, then along a further
subsequence the derivatives of order `k + 1` converge to those of `v`, which is `C^(k+1)`. -/
private theorem exists_strictMono_tendstoLocallyUniformlyOn_iteratedFDeriv_succ
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] {u : ℕ → E → F} {v : E → F} (hΩ : IsOpen Ω)
    {k : ℕ} (hu : ∀ n, ContDiffOn ℝ (k + 2) (u n) Ω)
    (hbd : ∀ K, IsCompact K → K ⊆ Ω → ∃ M, ∀ n, ∀ j ≤ k + 2, ∀ x ∈ K,
      ‖iteratedFDeriv ℝ j (u n) x‖ ≤ M)
    (hv : ContDiffOn ℝ k v Ω)
    (hconv : TendstoLocallyUniformlyOn (fun n ↦ iteratedFDeriv ℝ k (u n)) (iteratedFDeriv ℝ k v)
      atTop Ω) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ContDiffOn ℝ (k + 1 : ℕ) v Ω ∧
      TendstoLocallyUniformlyOn (fun n ↦ iteratedFDeriv ℝ (k + 1) (u (ψ n)))
        (iteratedFDeriv ℝ (k + 1) v) atTop Ω := by
  -- The derivative of the `k`-th derivative is the `(k + 1)`-th derivative, up to currying.
  let e := continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k + 1) ↦ E) F
  have hfd (f : E → F) : fderiv ℝ (iteratedFDeriv ℝ k f) = e ∘ iteratedFDeriv ℝ (k + 1) f := by
    rw [iteratedFDeriv_succ_eq_comp_left]
    funext x
    exact (e.apply_symm_apply _).symm
  -- The `(k + 1)`-th derivatives are equicontinuous, by the bound on the next derivative.
  have hequi : EquicontinuousOn (fun n ↦ fderiv ℝ (iteratedFDeriv ℝ k (u n))) Ω := by
    simp only [hfd]
    refine e.isometry.isUniformInducing.equicontinuousOn_iff.1 ?_
    refine equicontinuousOn_of_forall_isCompact_norm_fderiv_le hΩ
      (fun n ↦ differentiableOn_iteratedFDeriv_of_contDiffOn hΩ (hu n) le_rfl) fun K hK hKΩ ↦ ?_
    obtain ⟨M, hM⟩ := hbd K hK hKΩ
    exact ⟨M, fun n x hx ↦ by rw [norm_fderiv_iteratedFDeriv]; exact hM n (k + 2) le_rfl x hx⟩
  obtain ⟨ψ, hψ, hvk, hconvk⟩ := exists_strictMono_tendstoLocallyUniformlyOn_fderiv hΩ
    (fun n ↦ differentiableOn_iteratedFDeriv_of_contDiffOn hΩ (hu n) (by omega)) hequi
    (fun x hx ↦
      let ⟨M, hM⟩ := hbd {x} isCompact_singleton (singleton_subset_iff.2 hx)
      ⟨M, fun n ↦ by rw [norm_fderiv_iteratedFDeriv]; exact hM n (k + 1) (by omega) x rfl⟩)
    fun x hx ↦ hconv.tendsto_at hx
  refine ⟨ψ, hψ, ?_, ?_⟩
  · -- `v` is `Cᵏ` and its `k`-th derivative is `C¹`, so `v` is `C^(k+1)`.
    have hEq (m : ℕ) : EqOn (iteratedFDerivWithin ℝ m v Ω) (iteratedFDeriv ℝ m v) Ω :=
      fun _ hx ↦ iteratedFDerivWithin_of_isOpen m hΩ hx
    refine contDiffOn_of_continuousOn_differentiableOn (fun m hm ↦ ?_) fun m hm ↦ ?_
    · rcases (show m ≤ k ∨ m = k + 1 by norm_cast at hm; omega) with hm | rfl
      · exact hv.continuousOn_iteratedFDerivWithin (by exact_mod_cast hm) hΩ.uniqueDiffOn
      · refine ContinuousOn.congr ?_ (hEq (k + 1))
        rw [iteratedFDeriv_succ_eq_comp_left]
        exact e.symm.continuous.comp_continuousOn (hvk.continuousOn_fderiv_of_isOpen hΩ le_rfl)
    · rcases (show m < k ∨ m = k by norm_cast at hm; omega) with hm | rfl
      · exact hv.differentiableOn_iteratedFDerivWithin (by exact_mod_cast hm) hΩ.uniqueDiffOn
      · exact (hvk.differentiableOn one_ne_zero).congr (hEq m)
  · simp only [iteratedFDeriv_succ_eq_comp_left]
    exact e.symm.isometry.uniformContinuous.comp_tendstoLocallyUniformlyOn hconvk

/-- **Arzelà–Ascoli in `Cᵏ`.** Let `uₙ` be `C^(k+1)` on an open subset `Ω` of a
finite-dimensional space, with values in a finite-dimensional space, and suppose that on each
compact subset of `Ω` their derivatives of order at most `k + 1` are bounded uniformly in `n`.
Then along a subsequence the `uₙ` converge to a map `v` that is `Cᵏ` on `Ω`, together with their
derivatives of order at most `k`, locally uniformly on `Ω`. -/
theorem exists_strictMono_tendstoLocallyUniformlyOn_iteratedFDeriv [FiniteDimensional ℝ E]
    [FiniteDimensional ℝ F] {u : ℕ → E → F} (hΩ : IsOpen Ω) (k : ℕ)
    (hu : ∀ n, ContDiffOn ℝ (k + 1) (u n) Ω)
    (hbd : ∀ K, IsCompact K → K ⊆ Ω → ∃ M, ∀ n, ∀ j ≤ k + 1, ∀ x ∈ K,
      ‖iteratedFDeriv ℝ j (u n) x‖ ≤ M) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ v : E → F, ContDiffOn ℝ k v Ω ∧
      ∀ j ≤ k, TendstoLocallyUniformlyOn (fun n ↦ iteratedFDeriv ℝ j (u (φ n)))
        (iteratedFDeriv ℝ j v) atTop Ω := by
  induction k with
  | zero =>
    obtain ⟨φ, hφ, v, hv, hconv⟩ :=
      exists_strictMono_tendstoLocallyUniformlyOn_iteratedFDeriv_zero hΩ hu hbd
    exact ⟨φ, hφ, v, contDiffOn_zero.2 hv, fun j hj ↦ Nat.le_zero.1 hj ▸ hconv⟩
  | succ k ih =>
    -- Extract a subsequence along which the derivatives of order at most `k` converge, then a
    -- further one for the derivatives of order `k + 1`.
    obtain ⟨φ, hφ, v, hv, hconv⟩ := ih (fun n ↦ (hu n).of_le (by norm_cast; omega))
      fun K hK hKΩ ↦
        let ⟨M, hM⟩ := hbd K hK hKΩ
        ⟨M, fun n j hj ↦ hM n j (by omega)⟩
    obtain ⟨ψ, hψ, hv', hlast⟩ := exists_strictMono_tendstoLocallyUniformlyOn_iteratedFDeriv_succ
      hΩ (fun n ↦ hu (φ n)) (fun K hK hKΩ ↦
        let ⟨M, hM⟩ := hbd K hK hKΩ
        ⟨M, fun n ↦ hM (φ n)⟩) hv (hconv k le_rfl)
    refine ⟨φ ∘ ψ, hφ.comp hψ, v, hv', fun j hj ↦ ?_⟩
    rcases (show j ≤ k ∨ j = k + 1 by omega) with hj | rfl
    · exact fun U hU x hx ↦
        let ⟨t, ht, H⟩ := hconv j hj U hU x hx
        ⟨t, ht, hψ.tendsto_atTop.eventually H⟩
    · exact hlast

end TauCeti
