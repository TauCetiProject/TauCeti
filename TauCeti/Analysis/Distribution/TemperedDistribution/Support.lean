/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.Support
public import Mathlib.Analysis.Distribution.TemperedDistribution
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Distribution.SchwartzSpace.CompactSupport
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Multilinear.Basis
import TauCeti.Analysis.Calculus.IteratedFDeriv.Cutoff
import TauCeti.Analysis.Normed.Module.Ball
import TauCeti.Analysis.Distribution.Support
import TauCeti.Analysis.Distribution.TemperedDistribution.Deriv
import TauCeti.Analysis.Distribution.TestFunction.Schwartz

/-!
# Support of tempered distributions and distributions supported at a point

Mathlib's support `dsupport T` of a tempered distribution `T` is the complement of the union of
the open sets on which `T` vanishes. On a finite-dimensional real space `T` vanishes on that union
(`TemperedDistribution.isVanishingOn_compl_dsupport`, the localization principle). A Schwartz
function whose closed support avoids `dsupport T` is the limit of its products with dilated
compactly supported cutoffs, whose supports also avoid `dsupport T`, and on compactly supported
functions the localization principle for test functions applies. In particular `T` is zero
exactly when its support is empty.

The main results describe the tempered distributions supported at a point `x`.

* Such a `T` with values in a normed space has finite order at `x`: there is an `N` such that
  `T f = 0` for every Schwartz function `f` whose derivatives of order at most `N` vanish at `x`.
  Indeed `T` is bounded by finitely many Schwartz seminorms, of derivative order at most `N`. The
  value `T f` does not change when `f` is multiplied by a cutoff `φ (t • (· - x))` equal to one
  near `x`, and the seminorms of order at most `N` of these products tend to zero as `t → ∞`,
  since their derivatives of order at most `N` are `O(t⁻¹)`
  (`TauCeti.exists_norm_iteratedFDeriv_smul_le_mul`).
* Consequently a scalar tempered distribution is supported in `{x}` exactly when it is a finite
  linear combination of derivatives `∂^m δ_x` of the Dirac distribution. In coordinates on `ℝⁿ`
  these are the combinations `∑_{|α| ≤ N} c_α ∂^α δ_x`.

A normed target is needed for the finite order: on `ℝ`, the tempered distribution with values in
`ℂ^ℕ` whose `n`-th coordinate is `f ↦ f⁽ⁿ⁾(0)` is supported at `0` but sees every derivative
there.

This description of point-supported distributions is the input for classifying the distributions
on `ℝ` and `ℂ` that are supported at the origin and transform by a character under dilations, as
in Tate's local theory at the archimedean places.

## Main results

* `TemperedDistribution.isVanishingOn_compl_dsupport`: the localization principle.
* `TemperedDistribution.isVanishingOn_iff_disjoint_dsupport`,
  `TemperedDistribution.dsupport_eq_empty_iff`: its consequences for open sets and for the zero
  distribution.
* `TemperedDistribution.exists_apply_eq_zero_of_dsupport_subset_singleton`: a tempered
  distribution supported at `x` vanishes on the Schwartz functions whose derivatives of order at
  most some `N` vanish at `x`.
* `TemperedDistribution.dsupport_subset_singleton_iff_mem_span`: a scalar tempered distribution
  is supported in `{x}` if and only if it lies in the span of the derivatives `∂^m δ_x`.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, Theorem 2.3.4
  (distributions supported at a point).
* W. Rudin, *Functional Analysis*, 2nd ed., Theorem 6.25.
* S. S. Kudla, *Tate's thesis*, in *An Introduction to the Langlands Program*, §3.
-/

public section

open Filter Set Function TopologicalSpace Distribution
open scoped Topology ContDiff SchwartzMap Distributions LineDeriv

namespace TemperedDistribution

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Multiplying a Schwartz function by the shifted and dilated cutoff `φ (t • (· - x))`, for a
smooth compactly supported `φ` and `t ≠ 0`, is pointwise multiplication. -/
private theorem smulLeftCLM_comp_smul_sub_apply {φ : E → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hφc : HasCompactSupport φ) {t : ℝ} (ht : t ≠ 0) (x : E) (f : 𝓢(E, ℂ)) :
    SchwartzMap.smulLeftCLM ℂ (fun y ↦ φ (t • (y - x))) f = fun y ↦ φ (t • (y - x)) • f y :=
  SchwartzMap.smulLeftCLM_apply ((hφc.comp_homeomorph
    ((Homeomorph.subRight x).trans (Homeomorph.smulOfNeZero t ht))).hasTemperateGrowth
    (hφ.comp ((contDiff_const_smul t).comp (contDiff_id.sub contDiff_const)))) f

variable [FiniteDimensional ℝ E]

section Localization

variable [AddCommGroup F] [Module ℂ F] [TopologicalSpace F]

/-- **Localization principle.** A tempered distribution on a finite-dimensional space vanishes on
every Schwartz function whose closed support avoids the support of the distribution. -/
theorem isVanishingOn_compl_dsupport [T2Space F] (T : 𝓢'(E, F)) :
    IsVanishingOn T (dsupport T)ᶜ := by
  -- On compactly supported tests this is the localization principle for test functions.
  have hc : ∀ g : 𝓢(E, ℂ), HasCompactSupport g → tsupport g ⊆ (dsupport T)ᶜ → T g = 0 := by
    intro g hg hgs
    let S : 𝓓((⊤ : Opens E), ℂ) →ₗ[ℂ] F :=
      { toFun φ := T (TestFunction.toSchwartzMapCLM ℂ φ)
        map_add' := by simp
        map_smul' := by simp }
    have hS : dsupport S ⊆ dsupport T := fun y hy ↦ by_contra fun hyT ↦ by
      obtain ⟨s, hs, hso, hys⟩ := (notMem_dsupport_iff y).1 hyT
      exact (notMem_dsupport_iff y).2 ⟨s, fun φ hφ ↦ hs _ (by simpa [S] using hφ), hso, hys⟩ hy
    have := Distribution.isVanishingOn_compl_dsupport S (g.toTestFunction hg (subset_univ _))
      (by simpa using hgs.trans (compl_subset_compl.2 hS))
    simpa [S] using this
  -- A general test is the limit of its products with dilated cutoffs.
  intro f hf
  set b : ContDiffBump (0 : E) := ⟨1, 2, one_pos, one_lt_two⟩
  have ht := SchwartzMap.tendsto_smulLeftCLM_comp_smul b.contDiff b.hasCompactSupport
    b.eventuallyEq_one f
  have hT := ((T : 𝓢(E, ℂ) →L[ℂ] F).continuous.tendsto f).comp
    (ht.mono_left (nhdsWithin_le_nhds (s := {0}ᶜ)))
  refine tendsto_nhds_unique hT (tendsto_const_nhds.congr' ?_)
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hcs : HasCompactSupport (fun x ↦ b (ε • x)) := b.hasCompactSupport.comp_smul hε
  have hg := hcs.hasTemperateGrowth (b.contDiff.comp (contDiff_const_smul _))
  refine (hc _ ?_ ?_).symm
  · rw [SchwartzMap.smulLeftCLM_apply hg]
    exact hcs.smul_right
  · rw [SchwartzMap.smulLeftCLM_apply hg]
    exact (tsupport_smul_subset_right _ _).trans hf

/-- A tempered distribution vanishes on an open set exactly when that set is disjoint from its
support. -/
theorem isVanishingOn_iff_disjoint_dsupport [T2Space F] (T : 𝓢'(E, F)) {s : Set E}
    (hs : IsOpen s) : IsVanishingOn T s ↔ Disjoint s (dsupport T) :=
  ⟨fun h ↦ h.disjoint_dsupport hs,
    fun h ↦ (isVanishingOn_compl_dsupport T).mono h.subset_compl_right⟩

/-- A tempered distribution is zero exactly when its support is empty. -/
theorem dsupport_eq_empty_iff [T2Space F] [IsTopologicalAddGroup F] {T : 𝓢'(E, F)} :
    dsupport T = ∅ ↔ T = 0 := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · ext f
    simpa using isVanishingOn_compl_dsupport T f (by simp [h])
  · rintro rfl
    exact univ_disjoint.1 ((isVanishingOn_iff_disjoint_dsupport _ isOpen_univ).1 fun _ _ ↦ rfl)

end Localization

section PointSupport

variable [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- If the derivatives of `f` of order at most `N` vanish at `x`, the Schwartz seminorms of order
`n ≤ N` of the products of `f` with the shrinking cutoffs `φ (t • (· - x))` tend to zero as
`t → ∞`: by `TauCeti.exists_norm_iteratedFDeriv_smul_le_mul` their derivatives of order at most `N`
are `O(t⁻¹)`, and they are supported in `closedBall x t⁻¹`. -/
private theorem tendsto_seminorm_smulLeftCLM_comp_smul_sub {φ : E → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hφs : tsupport φ ⊆ Metric.closedBall 0 1) (f : 𝓢(E, ℂ)) {x : E} {N : ℕ}
    (hf : ∀ i ≤ N, iteratedFDeriv ℝ i f x = 0) (k : ℕ) {n : ℕ} (hn : n ≤ N) :
    Tendsto (fun t : ℝ ↦ (SchwartzMap.smulLeftCLM ℂ (fun y ↦ φ (t • (y - x))) f).seminorm ℝ k n)
      atTop (𝓝 0) := by
  have hφc : HasCompactSupport φ :=
    (isCompact_closedBall 0 1).of_isClosed_subset (isClosed_tsupport φ) hφs
  obtain ⟨C, hC⟩ := TauCeti.exists_norm_iteratedFDeriv_smul_le_mul (r := N)
    (hφ.of_le (mod_cast le_top)) hφs (f.smooth _) hf
  have hC0 : 0 ≤ C := by simpa using (norm_nonneg _).trans (hC 1 one_pos le_rfl 0 (Nat.zero_le _) x)
  refine squeeze_zero' (g := fun t : ℝ ↦ (‖x‖ + 1) ^ k * C * t⁻¹)
    (.of_forall fun _ ↦ apply_nonneg _ _) ?_
    (by simpa using tendsto_inv_atTop_zero.const_mul ((‖x‖ + 1) ^ k * C))
  filter_upwards [eventually_ge_atTop 1] with t ht
  have ht0 : 0 < t := one_pos.trans_le ht
  have ht1 : t⁻¹ ≤ 1 := inv_le_one_of_one_le₀ ht
  refine SchwartzMap.seminorm_le_bound ℝ k n _ (by positivity) fun y ↦ ?_
  have hy := hC t⁻¹ (inv_pos.2 ht0) ht1 n hn y
  have hsupp := TauCeti.tsupport_comp_inv_smul_sub_subset_closedBall hφs (inv_pos.2 ht0) x
  simp only [inv_inv] at hy hsupp
  rw [smulLeftCLM_comp_smul_sub_apply hφ hφc ht0.ne']
  by_cases hyx : y ∈ Metric.closedBall x t⁻¹
  · have hy1 : ‖y‖ ≤ ‖x‖ + 1 := by
      calc ‖y‖ = ‖x + (y - x)‖ := by simp
        _ ≤ ‖x‖ + ‖y - x‖ := norm_add_le _ _
        _ ≤ ‖x‖ + 1 := by gcongr; exact (mem_closedBall_iff_norm.1 hyx).trans ht1
    calc ‖y‖ ^ k * ‖iteratedFDeriv ℝ n (fun y ↦ φ (t • (y - x)) • f y) y‖
        ≤ (‖x‖ + 1) ^ k * (C * t⁻¹) := by gcongr
      _ = (‖x‖ + 1) ^ k * C * t⁻¹ := by ring
  · -- Away from `closedBall x t⁻¹` the product vanishes near `y`.
    have hy0 : y ∉ tsupport fun y ↦ φ (t • (y - x)) • f y :=
      fun h ↦ hyx (hsupp (tsupport_smul_subset_left _ _ h))
    rw [Function.notMem_support.mp fun h ↦ hy0 (support_iteratedFDeriv_subset n h), norm_zero,
      mul_zero]
    positivity

/-- **A tempered distribution supported at a point has finite order there.** If a tempered
distribution `T` with values in a normed space is supported in `{x}`, there is an `N` such that
`T f = 0` for every Schwartz function `f` whose iterated derivatives of order at most `N` vanish
at `x`. -/
theorem exists_apply_eq_zero_of_dsupport_subset_singleton {T : 𝓢'(E, F)} {x : E}
    (hT : dsupport T ⊆ {x}) :
    ∃ N : ℕ, ∀ f : 𝓢(E, ℂ), (∀ i ≤ N, iteratedFDeriv ℝ i f x = 0) → T f = 0 := by
  -- `T` is bounded by finitely many Schwartz seminorms; `N` is the largest order among them.
  have hq : Continuous ((normSeminorm ℂ F).comp (T : 𝓢(E, ℂ) →L[ℂ] F).toLinearMap) :=
    continuous_norm.comp (T : 𝓢(E, ℂ) →L[ℂ] F).continuous
  obtain ⟨S, c, -, hc⟩ := Seminorm.bound_sum_of_continuous (schwartz_withSeminorms ℂ E ℂ) _ hq
  have hc' (φ : 𝓢(E, ℂ)) : ‖T φ‖ ≤ c * ∑ i ∈ S, SchwartzMap.seminorm ℂ i.1 i.2 φ :=
    (hc φ).trans_eq (by simp [schwartzSeminormFamily, NNReal.smul_def])
  refine ⟨S.sup Prod.snd, fun f hf ↦ ?_⟩
  have hvan : IsVanishingOn T {x}ᶜ :=
    (isVanishingOn_compl_dsupport T).mono (compl_subset_compl.2 hT)
  set b : ContDiffBump (0 : E) := ⟨1 / 2, 1, by norm_num, by norm_num⟩
  set g : ℝ → 𝓢(E, ℂ) := fun t ↦ SchwartzMap.smulLeftCLM ℂ (fun y ↦ b (t • (y - x))) f
  -- Cutting `f` off near `x` does not change the value of `T`.
  have heq : ∀ t : ℝ, 0 < t → T f = T (g t) := by
    intro t ht
    rw [← sub_eq_zero, ← map_sub]
    refine hvan _ (subset_compl_singleton_iff.2 (notMem_tsupport_iff_eventuallyEq.2 ?_))
    have hopen : IsOpen {y : E | t • (y - x) ∈ Metric.ball (0 : E) (1 / 2)} :=
      Metric.isOpen_ball.preimage (by fun_prop)
    filter_upwards [hopen.mem_nhds (by simp)] with y hy
    have hb : b (t • (y - x)) = 1 := b.one_of_mem_closedBall (Metric.ball_subset_closedBall hy)
    simp [g, smulLeftCLM_comp_smul_sub_apply b.contDiff b.hasCompactSupport ht.ne', hb]
  have hlim : Tendsto (fun t ↦ c * ∑ i ∈ S, SchwartzMap.seminorm ℂ i.1 i.2 (g t)) atTop
      (𝓝 0) := by
    -- The Schwartz seminorms do not depend on the scalar field.
    simpa [SchwartzMap.seminorm_apply] using (tendsto_finsetSum S fun i hi ↦
      tendsto_seminorm_smulLeftCLM_comp_smul_sub b.contDiff b.tsupport_eq.subset f hf i.1
        (Finset.le_sup (f := Prod.snd) hi)).const_mul (c : ℝ)
  refine norm_le_zero_iff.1 (ge_of_tendsto hlim ?_)
  filter_upwards [eventually_gt_atTop 0] with t ht
  rw [heq t ht]
  exact hc' _

end PointSupport

/-- **Tempered distributions supported at a point.** A scalar tempered distribution on a
finite-dimensional space is supported in `{x}` if and only if it is a finite linear combination of
iterated directional derivatives `∂^m δ_x` of the Dirac distribution at `x`. -/
theorem dsupport_subset_singleton_iff_mem_span {T : 𝓢'(E, ℂ)} {x : E} :
    dsupport T ⊆ {x} ↔
      T ∈ Submodule.span ℂ (⋃ n : ℕ, range fun m : Fin n → E ↦ ∂^{m} (delta x)) := by
  constructor
  · intro hT
    obtain ⟨N, hN⟩ := exists_apply_eq_zero_of_dsupport_subset_singleton hT
    -- Derivatives of `δ_x` along tuples of basis vectors, of order at most `N`.
    let b := Module.finBasis ℝ E
    let D : (Σ n : Fin (N + 1), Fin n → Fin (Module.finrank ℝ E)) → 𝓢'(E, ℂ) :=
      fun i ↦ ∂^{b ∘ i.2} (delta x)
    -- Tempered distributions as linear functionals.
    let toLin := PointwiseConvergenceCLM.coeLM ℂ 𝓢(E, ℂ) ℂ
    have hker : ⨅ i, LinearMap.ker (toLin (D i)) ≤ LinearMap.ker (toLin T) := by
      intro f hf
      simp only [Submodule.mem_iInf, LinearMap.mem_ker] at hf
      refine hN f fun n hn ↦ ContinuousMultilinearMap.toMultilinearMap_injective
        (Module.Basis.ext_multilinear (fun _ ↦ b) fun v ↦ ?_)
      have := hf ⟨⟨n, Nat.lt_succ_of_le hn⟩, v ∘ Fin.rev⟩
      change (∂^{b ∘ (v ∘ Fin.rev)} (delta x)) f = 0 at this
      rw [iteratedLineDerivOp_delta_apply, mul_eq_zero] at this
      simpa only [ContinuousMultilinearMap.coe_coe, ContinuousMultilinearMap.toMultilinearMap_zero,
        zero_apply, Function.comp_def, Fin.rev_rev] using
        this.resolve_left (pow_ne_zero _ (by norm_num))
    obtain ⟨c, hc⟩ :=
      (Submodule.mem_span_range_iff_exists_fun ℂ).1 (mem_span_of_iInf_ker_le_ker hker)
    have hT : T = ∑ i, c i • D i := by
      simp only [← map_smul, ← map_sum] at hc
      ext f
      exact (LinearMap.congr_fun hc f).symm
    rw [hT]
    refine Submodule.sum_mem _ fun i _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span ?_)
    exact mem_iUnion.2 ⟨i.1, b ∘ i.2, rfl⟩
  · intro hT
    have hvan : IsVanishingOn T {x}ᶜ := by
      induction hT using Submodule.span_induction with
      | mem S hS =>
        obtain ⟨n, m, rfl⟩ := mem_iUnion.1 hS
        exact Distribution.TemperedDistribution.IsVanishingOn.iteratedLineDerivOp
          (isVanishingOn_delta x) m
      | zero => intro f _; simp
      | add S S' _ _ hS hS' => intro f hf; simp [hS f hf, hS' f hf]
      | smul a S _ hS => intro f hf; simp [hS f hf]
    exact disjoint_compl_left_iff_subset.1 (hvan.disjoint_dsupport isOpen_compl_singleton)

end TemperedDistribution
