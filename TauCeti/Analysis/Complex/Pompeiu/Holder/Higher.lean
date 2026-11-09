/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Pompeiu.Holder.Operator
public import TauCeti.Analysis.Holder.Iterated
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import TauCeti.Topology.MetricSpace.Holder

/-!
# The Cauchy transform on `C^{k,α}` data

For every `k : ℕ` the normalized Cauchy transform
`TauCeti.cauchyTransform f w = π⁻¹ ∫ (w - z)⁻¹ • f z` maps `C^{k,α}` data supported in a fixed
disc `closedBall c r` to functions that are `C^{k+1}` near each fixed output disc
`closedBall c R`, with all derivatives through order `k + 1` bounded there and the derivative of
order `k + 1` `α`-Hölder, for `0 < α < 1`. The constant depends only on the target, `k`, `α`, `c`,
`r` and `R`.

The proof differentiates under the kernel: on compactly supported `C¹` data the derivative of
the transform is the transform of the derivative. So `D^{j+1} (T f)` is `D^j (T (D f))` up to a
currying isometry, and induction on `k` reduces everything to the case `k = 0`, which is the
one-derivative Hölder gain of
`TauCeti.exists_contDiffOn_holderOnWith_fderiv_pi_inv_smul_integral_sub_inv_smul`.

## Main results

* `HasCompactSupport.fderiv_cauchyTransform`: `D (T f) = T (D f)` for compactly supported `C¹`
  data, and `HasCompactSupport.fderiv_cauchyTransform_apply`, its directional form.
* `TauCeti.exists_contDiffOn_holderOnWith_iteratedFDeriv_cauchyTransform`: the `C^{k+1,α}`
  estimate on an output disc, for `C^{k,α}` data on an input disc.
* `TauCeti.contDiff_cauchyTransform_of_holderWith_iteratedFDeriv`: the transform of such data is
  globally `C^{k+1}`.
* `TauCeti.cauchyTransformCkCLM`: the transform as a bounded real-linear operator from
  `C^{k,α}` data supported in `closedBall c r` to the derivative fields of orders through
  `k + 1` on `closedBall c R` with the supremum norm, together with the `α`-Hölder field of
  order `k + 1`. For `k = 0` it carries the same data as `TauCeti.cauchyTransformCLM`.
* `TauCeti.contDiffOn_holderOnWith_fderiv_cauchyTransform_norm_rpow_mul`: the check that the
  `C^{0,α}` source `‖z‖ ^ α χ(z)` has a `C^{1,α}` transform near `0`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, Appendix B.
* D. Gilbarg and N. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Lemma 4.4.
-/

public noncomputable section

open Complex Metric MeasureTheory Set
open scoped NNReal ContDiff BoundedContinuousFunction

section Commutation

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- On compactly supported `C¹` data the real derivative of the Cauchy transform is the Cauchy
transform of the real derivative. -/
theorem HasCompactSupport.fderiv_cauchyTransform {f : ℂ → F} (hc : HasCompactSupport f)
    (hf : ContDiff ℝ 1 f) :
    fderiv ℝ (TauCeti.cauchyTransform f) = TauCeti.cauchyTransform (fderiv ℝ f) :=
  funext fun w ↦ by
    rw [(hc.hasFDerivAt_cauchyTransform hf w).fderiv, TauCeti.cauchyTransform_apply]

/-- The directional derivative of the Cauchy transform of compactly supported `C¹` data in the
direction `v` is the Cauchy transform of the directional derivative of the data. -/
theorem HasCompactSupport.fderiv_cauchyTransform_apply {f : ℂ → F} (hc : HasCompactSupport f)
    (hf : ContDiff ℝ 1 f) (w v : ℂ) :
    fderiv ℝ (TauCeti.cauchyTransform f) w v =
      TauCeti.cauchyTransform (fun z ↦ fderiv ℝ f z v) w := by
  have hi : Integrable fun z ↦ (w - z)⁻¹ • fderiv ℝ f z :=
    (Complex.locallyIntegrable_sub_inv w).integrable_smul_right_of_hasCompactSupport
      (hf.continuous_fderiv one_ne_zero) (hc.fderiv ℝ)
  rw [hc.fderiv_cauchyTransform hf, TauCeti.cauchyTransform_apply,
    TauCeti.cauchyTransform_apply, smul_apply,
    ContinuousLinearMap.integral_apply hi]
  rfl

end Commutation

namespace TauCeti

section Estimate

/-- The derivative fields of a function with values in a finite-dimensional complex space form
a finite-dimensional complex space. -/
private theorem finiteDimensional_continuousLinearMap {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℂ F] [NormedSpace ℝ F] [IsScalarTower ℝ ℂ F] [FiniteDimensional ℂ F] :
    FiniteDimensional ℂ (ℂ →L[ℝ] F) := by
  have : FiniteDimensional ℝ F := Module.Finite.trans ℂ F
  exact Module.Finite.of_restrictScalars_finite ℝ ℂ (ℂ →L[ℝ] F)

/-- Composing with a linear isometry equivalence on the left preserves Hölder bounds. -/
private theorem holderOnWith_linearIsometryEquiv_comp {G G' : Type*}
    [SeminormedAddCommGroup G] [Module ℝ G] [SeminormedAddCommGroup G'] [Module ℝ G']
    (e : G ≃ₗᵢ[ℝ] G') {u : ℂ → G} {C α : ℝ≥0} {s : Set ℂ} (h : HolderOnWith C α u s) :
    HolderOnWith C α (fun x ↦ e (u x)) s := fun x hx y hy ↦ by
  simpa only [LinearIsometryEquiv.edist_map] using h x hx y hy

/-- The one-derivative gain, in the form used as the base of the induction on `k`. -/
private theorem exists_gain_zero {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    [NormedSpace ℝ F] [IsScalarTower ℝ ℂ F] [FiniteDimensional ℂ F]
    {α : ℝ≥0} (hα : 0 < α) (hα1 : α < 1) (c : ℂ) {r R : ℝ} (hr : 0 ≤ r) (hR : 0 ≤ R) :
    ∃ C : ℝ≥0, ∀ {f : ℂ → F} {H M : ℝ≥0},
      Function.support f ⊆ closedBall c r →
      HolderWith H α (iteratedFDeriv ℝ 0 f) →
      (∀ i ≤ 0, ∀ x, ‖iteratedFDeriv ℝ i f x‖ ≤ M) →
      ContDiffOn ℝ (0 + 1 : ℕ) (cauchyTransform f) (ball c (R + 1)) ∧
      HolderOnWith (C * (H + M)) α (iteratedFDeriv ℝ (0 + 1) (cauchyTransform f))
        (closedBall c R) ∧
      ∀ i ≤ 0 + 1, ∀ x ∈ closedBall c R,
        ‖iteratedFDeriv ℝ i (cauchyTransform f) x‖ ≤ C * (H + M) := by
  -- The real action is uniquely determined by the compatible complex action.
  cases NormedSpace.restrictScalars_eq (𝕜 := ℝ) (𝕜' := ℂ) (E := F)
  obtain ⟨C, hC⟩ :=
    exists_contDiffOn_holderOnWith_fderiv_pi_inv_smul_integral_sub_inv_smul
      (F := F) hα hα1 c hr hR
  refine ⟨C + (2 * (r + R)).toNNReal, fun {f H M} hs hH hM ↦ ?_⟩
  have hf : HolderWith H α f := by
    have h := holderOnWith_linearIsometryEquiv_comp (continuousMultilinearCurryFin0 ℝ ℂ F)
      (holderOnWith_univ.mpr hH)
    simpa only [iteratedFDeriv_zero_eq_comp, Function.comp_apply,
      LinearIsometryEquiv.apply_symm_apply, holderOnWith_univ] using h
  have hM0 (x : ℂ) : ‖f x‖ ≤ M := by
    simpa only [norm_iteratedFDeriv_zero] using hM 0 le_rfl x
  have hT : cauchyTransform f = fun w ↦ (Real.pi : ℂ)⁻¹ • ∫ z, (w - z)⁻¹ • f z :=
    funext (cauchyTransform_apply f)
  obtain ⟨hcd, hD, hN, -⟩ := hC hs hf hM0
  rw [← hT] at hcd hD hN
  have hle : (C * (H + M) : ℝ≥0) ≤ (C + (2 * (r + R)).toNNReal) * (H + M) := by
    gcongr
    exact le_self_add
  refine ⟨by simpa using hcd, ?_, fun i hi x hx ↦ ?_⟩
  · have h1 : iteratedFDeriv ℝ (0 + 1) (cauchyTransform f) = fun x ↦
        (continuousMultilinearCurryRightEquiv' ℝ 0 ℂ F).symm
          ((continuousMultilinearCurryFin0 ℝ ℂ (ℂ →L[ℝ] F)).symm
            (fderiv ℝ (cauchyTransform f) x)) := by
      funext x
      rw [iteratedFDeriv_succ_eq_comp_right, Function.comp_apply, iteratedFDeriv_zero_eq_comp,
        Function.comp_apply]
    rw [h1]
    exact holderOnWith_linearIsometryEquiv_comp _
      (holderOnWith_linearIsometryEquiv_comp _ (hD.mono_const hle))
  · interval_cases i
    · rw [norm_iteratedFDeriv_zero, hT]
      calc
        _ ≤ 2 * (r + R) * M := norm_pi_inv_smul_integral_sub_inv_smul_le hr hR hs hM0 hx
        _ ≤ ((2 * (r + R)).toNNReal : ℝ) * (H + M) := by
          rw [Real.coe_toNNReal _ (by positivity)]
          gcongr
          exact le_add_of_nonneg_left H.coe_nonneg
        _ ≤ _ := by
          push_cast
          gcongr
          exact le_add_of_nonneg_left C.coe_nonneg
    · rw [norm_iteratedFDeriv_one]
      exact (hN x hx).trans (by exact_mod_cast hle)

/-- **Higher Hölder gain for the Cauchy transform.** For `0 < α < 1`, `C^{k,α}` data `f` supported
in `closedBall c r`, with `[D^k f]_α ≤ H` and `‖D^i f‖_∞ ≤ M` for `i ≤ k`, has a Cauchy transform
that is `C^{k+1}` on `ball c (R + 1)`; on `closedBall c R` its derivatives through order `k + 1`
are bounded by `C (H + M)` and its derivative of order `k + 1` is `α`-Hölder with constant
`C (H + M)`. The constant `C` depends only on the target, `k`, `α`, `c`, `r` and `R`. The
compatible real scalar action remains a parameter because it determines the derivative
carriers. -/
theorem exists_contDiffOn_holderOnWith_iteratedFDeriv_cauchyTransform
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedSpace ℝ F]
    [IsScalarTower ℝ ℂ F] [FiniteDimensional ℂ F] (k : ℕ)
    {α : ℝ≥0} (hα : 0 < α) (hα1 : α < 1) (c : ℂ) {r R : ℝ} (hr : 0 ≤ r) (hR : 0 ≤ R) :
    ∃ C : ℝ≥0, ∀ {f : ℂ → F} {H M : ℝ≥0},
      ContDiff ℝ k f → Function.support f ⊆ closedBall c r →
      HolderWith H α (iteratedFDeriv ℝ k f) →
      (∀ i ≤ k, ∀ x, ‖iteratedFDeriv ℝ i f x‖ ≤ M) →
      ContDiffOn ℝ (k + 1 : ℕ) (cauchyTransform f) (ball c (R + 1)) ∧
      HolderOnWith (C * (H + M)) α (iteratedFDeriv ℝ (k + 1) (cauchyTransform f))
        (closedBall c R) ∧
      ∀ i ≤ k + 1, ∀ x ∈ closedBall c R,
        ‖iteratedFDeriv ℝ i (cauchyTransform f) x‖ ≤ C * (H + M) := by
  induction k generalizing F with
  | zero =>
    obtain ⟨C, hC⟩ := exists_gain_zero (F := F) hα hα1 c hr hR
    exact ⟨C, fun _ hs hH hM ↦ hC hs hH hM⟩
  | succ k ih =>
    -- The real action is uniquely determined by the compatible complex action.
    cases NormedSpace.restrictScalars_eq (𝕜 := ℝ) (𝕜' := ℂ) (E := F)
    have := finiteDimensional_continuousLinearMap (F := F)
    obtain ⟨C, hC⟩ := ih (F := ℂ →L[ℝ] F)
    refine ⟨C + (2 * (r + R)).toNNReal, fun {f H M} hf hs hH hM ↦ ?_⟩
    have hc : HasCompactSupport f :=
      HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall c r) hs
    have hf1 : ContDiff ℝ 1 f := hf.of_le (by exact_mod_cast Nat.le_add_left 1 k)
    have hDT := hc.fderiv_cauchyTransform hf1
    -- The derivative of the data satisfies the hypotheses one order lower.
    have hg : ContDiff ℝ k (fderiv ℝ f) := hf.fderiv_right (by push_cast; exact le_rfl)
    have hgs : Function.support (fderiv ℝ f) ⊆ closedBall c r :=
      (support_fderiv_subset ℝ).trans (closure_minimal hs isClosed_closedBall)
    have hgH : HolderWith H α (iteratedFDeriv ℝ k (fderiv ℝ f)) := by
      have h := holderOnWith_linearIsometryEquiv_comp
        (continuousMultilinearCurryRightEquiv' ℝ k ℂ F) (holderOnWith_univ.mpr hH)
      simpa only [iteratedFDeriv_succ_eq_comp_right, Function.comp_apply,
        LinearIsometryEquiv.apply_symm_apply, holderOnWith_univ] using h
    have hgM : ∀ i ≤ k, ∀ x, ‖iteratedFDeriv ℝ i (fderiv ℝ f) x‖ ≤ M := fun i hi x ↦ by
      rw [norm_iteratedFDeriv_fderiv]
      exact hM (i + 1) (by omega) x
    obtain ⟨hcd, hD, hN⟩ := hC hg hgs hgH hgM
    rw [← hDT] at hcd hD hN
    have hle : (C * (H + M) : ℝ≥0) ≤ (C + (2 * (r + R)).toNNReal) * (H + M) := by
      gcongr
      exact le_self_add
    refine ⟨?_, ?_, fun i hi x hx ↦ ?_⟩
    · have hn : ((k + 1 + 1 : ℕ) : WithTop ℕ∞) = ((k + 1 : ℕ) : WithTop ℕ∞) + 1 := by
        push_cast
        rfl
      rw [hn, contDiffOn_succ_iff_fderiv_of_isOpen isOpen_ball]
      refine ⟨fun x _ ↦ (hc.hasFDerivAt_cauchyTransform hf1 x).differentiableAt
        |>.differentiableWithinAt, by simp, hcd⟩
    · have he : iteratedFDeriv ℝ (k + 1 + 1) (cauchyTransform f) = fun x ↦
          (continuousMultilinearCurryRightEquiv' ℝ (k + 1) ℂ F).symm
            (iteratedFDeriv ℝ (k + 1) (fderiv ℝ (cauchyTransform f)) x) :=
        funext fun x ↦ iteratedFDeriv_succ_eq_comp_right
      rw [he]
      exact holderOnWith_linearIsometryEquiv_comp _ (hD.mono_const hle)
    · rcases i with _ | i
      · have hM0 (x : ℂ) : ‖f x‖ ≤ M := by
          simpa only [norm_iteratedFDeriv_zero] using hM 0 (Nat.zero_le _) x
        rw [norm_iteratedFDeriv_zero, cauchyTransform_apply]
        calc
          _ ≤ 2 * (r + R) * M := norm_pi_inv_smul_integral_sub_inv_smul_le hr hR hs hM0 hx
          _ ≤ ((2 * (r + R)).toNNReal : ℝ) * (H + M) := by
            rw [Real.coe_toNNReal _ (by positivity)]
            gcongr
            exact le_add_of_nonneg_left H.coe_nonneg
          _ ≤ _ := by
            push_cast
            gcongr
            exact le_add_of_nonneg_left C.coe_nonneg
      · rw [← norm_iteratedFDeriv_fderiv]
        exact (hN i (by omega) x hx).trans (by exact_mod_cast hle)

/-- The Cauchy transform of `C^{k,α}` data supported in a closed disc is globally `C^{k+1}`. -/
theorem contDiff_cauchyTransform_of_holderWith_iteratedFDeriv
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedSpace ℝ F]
    [IsScalarTower ℝ ℂ F] [FiniteDimensional ℂ F] {k : ℕ}
    {α : ℝ≥0} (hα : 0 < α) (hα1 : α < 1) {c : ℂ} {r : ℝ} (hr : 0 ≤ r) {f : ℂ → F} {H : ℝ≥0}
    (hf : ContDiff ℝ k f) (hs : Function.support f ⊆ closedBall c r)
    (hH : HolderWith H α (iteratedFDeriv ℝ k f)) :
    ContDiff ℝ (k + 1 : ℕ) (cauchyTransform f) := by
  have hc : HasCompactSupport f :=
    HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall c r) hs
  -- Each derivative of order at most `k` is continuous with compact support, hence bounded.
  have hb (i : ℕ) (hi : i ≤ k) : ∃ M : ℝ, ∀ x, ‖iteratedFDeriv ℝ i f x‖ ≤ M :=
    ((hf.continuous_iteratedFDeriv (by exact_mod_cast hi)).norm.bddAbove_range_of_hasCompactSupport
      (hc.iteratedFDeriv i).norm).imp fun _ h x ↦ h ⟨x, rfl⟩
  choose M hM using hb
  let M' : ℝ≥0 := ∑ i ∈ Finset.range (k + 1), (if h : i ≤ k then M i h else 0).toNNReal
  have hM' : ∀ i ≤ k, ∀ x, ‖iteratedFDeriv ℝ i f x‖ ≤ M' := fun i hi x ↦ by
    calc
      _ ≤ ((if h : i ≤ k then M i h else 0).toNNReal : ℝ) := by
        simp only [hi, ↓reduceDIte]
        exact (hM i hi x).trans (Real.le_coe_toNNReal _)
      _ ≤ M' := by
        exact_mod_cast Finset.single_le_sum (f := fun i ↦ (if h : i ≤ k then M i h else 0).toNNReal)
          (fun _ _ ↦ by positivity) (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))
  rw [contDiff_iff_contDiffAt]
  intro x
  obtain ⟨C, hC⟩ := exists_contDiffOn_holderOnWith_iteratedFDeriv_cauchyTransform (F := F) k
    hα hα1 c hr (dist_nonneg (x := x) (y := c))
  exact (hC hf hs hH hM').1.contDiffAt
    (isOpen_ball.mem_nhds (mem_ball.mpr (lt_add_one (dist x c))))

end Estimate

section Operator

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedSpace ℝ F]
  [IsScalarTower ℝ ℂ F] [FiniteDimensional ℂ F] {k : ℕ} {α : ℝ≥0} {c : ℂ} {r R : ℝ}

/-- The Cauchy transform of an element of the supported `C^{k,α}` source space. -/
private def cauchyCk (f : supportedCkHolderSubmodule (E := ℂ) (F := F) k α (closedBall c r)) :
    ℂ → F :=
  cauchyTransform (f : CkHolderSpace k α ℂ F)

omit [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F] [FiniteDimensional ℂ F] in
private theorem support_source
    (f : supportedCkHolderSubmodule (E := ℂ) (F := F) k α (closedBall c r)) :
    Function.support (f : CkHolderSpace k α ℂ F) ⊆ closedBall c r :=
  support_subset_of_mem_supportedCkHolderSubmodule f.property

omit [IsScalarTower ℝ ℂ F] [FiniteDimensional ℂ F] in
private theorem integrable_source
    (f : supportedCkHolderSubmodule (E := ℂ) (F := F) k α (closedBall c r)) (w : ℂ) :
    Integrable (fun z ↦ (w - z)⁻¹ • (f : CkHolderSpace k α ℂ F) z) :=
  (Complex.locallyIntegrable_sub_inv w).integrable_smul_right_of_hasCompactSupport
    (f : CkHolderSpace k α ℂ F).contDiff.continuous
    (HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall c r) (support_source f))

omit [FiniteDimensional ℂ F] in
private theorem cauchyCk_add
    (f g : supportedCkHolderSubmodule (E := ℂ) (F := F) k α (closedBall c r)) :
    cauchyCk (f + g) = cauchyCk f + cauchyCk g := by
  -- The integral in the transform uses the real action induced by the complex one.
  cases NormedSpace.restrictScalars_eq (𝕜 := ℝ) (𝕜' := ℂ) (E := F)
  funext w
  simp only [cauchyCk, cauchyTransform_apply, Submodule.coe_add, CkHolderSpace.coe_add,
    Pi.add_apply, smul_add]
  rw [integral_add (integrable_source f w) (integrable_source g w), smul_add]

omit [FiniteDimensional ℂ F] in
private theorem cauchyCk_smul (a : ℝ)
    (f : supportedCkHolderSubmodule (E := ℂ) (F := F) k α (closedBall c r)) :
    cauchyCk (a • f) = a • cauchyCk f := by
  -- The integral in the transform uses the real action induced by the complex one.
  cases NormedSpace.restrictScalars_eq (𝕜 := ℝ) (𝕜' := ℂ) (E := F)
  funext w
  simp only [cauchyCk, cauchyTransform_apply, Submodule.coe_smul, CkHolderSpace.coe_smul,
    Pi.smul_apply]
  simp_rw [smul_comm (w - _)⁻¹ a]
  rw [integral_smul, smul_comm]

private theorem contDiff_cauchyCk (hα : 0 < α) (hα1 : α < 1) (hr : 0 ≤ r)
    (f : supportedCkHolderSubmodule (E := ℂ) (F := F) k α (closedBall c r)) :
    ContDiff ℝ (k + 1 : ℕ) (cauchyCk f) :=
  contDiff_cauchyTransform_of_holderWith_iteratedFDeriv hα hα1 hr
    (f : CkHolderSpace k α ℂ F).contDiff (support_source f)
    (f : CkHolderSpace k α ℂ F).memHolder_iteratedFDeriv.holderWith

/-- The constant of the higher Hölder gain, for fixed target, order, exponent and discs. -/
private def gainConst (k : ℕ) (hα : 0 < α) (hα1 : α < 1) (c : ℂ) (hr : 0 ≤ r) (hR : 0 ≤ R) :
    ℝ≥0 :=
  Classical.choose
    (exists_contDiffOn_holderOnWith_iteratedFDeriv_cauchyTransform (F := F) k hα hα1 c hr hR)

/-- The higher Hölder gain for an element of the supported source space, with the source norm. -/
private theorem gain_source (hα : 0 < α) (hα1 : α < 1) (hr : 0 ≤ r) (hR : 0 ≤ R)
    (f : supportedCkHolderSubmodule (E := ℂ) (F := F) k α (closedBall c r)) :
    HolderOnWith (2 * gainConst (F := F) k hα hα1 c hr hR * ‖f‖₊) α
      (iteratedFDeriv ℝ (k + 1) (cauchyCk f)) (closedBall c R) ∧
    ∀ i ≤ k + 1, ∀ x ∈ closedBall c R,
      ‖iteratedFDeriv ℝ i (cauchyCk f) x‖ ≤ 2 * gainConst (F := F) k hα hα1 c hr hR * ‖f‖ := by
  let u : CkHolderSpace k α ℂ F := f
  have hM : ∀ i ≤ k, ∀ x, ‖iteratedFDeriv ℝ i u x‖ ≤ (‖f‖₊ : ℝ) := fun i hi x ↦ by
    rw [coe_nnnorm, ← Submodule.norm_coe]
    exact u.norm_iteratedFDeriv_apply_le hi x
  obtain ⟨-, hH, hN⟩ := Classical.choose_spec
    (exists_contDiffOn_holderOnWith_iteratedFDeriv_cauchyTransform (F := F) k hα hα1 c hr hR)
    u.contDiff (support_source f) u.memHolder_iteratedFDeriv.holderWith hM
  have hHle : nnHolderNorm α (iteratedFDeriv ℝ k u) ≤ ‖f‖₊ := by
    rw [← NNReal.coe_le_coe, coe_nnnorm, ← Submodule.norm_coe]
    exact u.nnHolderNorm_iteratedFDeriv_le
  have hle : gainConst (F := F) k hα hα1 c hr hR * (nnHolderNorm α (iteratedFDeriv ℝ k u) + ‖f‖₊)
      ≤ 2 * gainConst (F := F) k hα hα1 c hr hR * ‖f‖₊ := by
    calc
      _ ≤ gainConst (F := F) k hα hα1 c hr hR * (‖f‖₊ + ‖f‖₊) := by gcongr
      _ = _ := by ring
  have hleR : (gainConst (F := F) k hα hα1 c hr hR : ℝ) *
      ((nnHolderNorm α (iteratedFDeriv ℝ k u) : ℝ) + (‖f‖₊ : ℝ)) ≤
        2 * gainConst (F := F) k hα hα1 c hr hR * ‖f‖ := by
    simpa only [NNReal.coe_mul, NNReal.coe_add, NNReal.coe_ofNat, coe_nnnorm] using
      NNReal.coe_le_coe.mpr hle
  exact ⟨hH.mono_const hle, fun i hi x hx ↦ (hN i hi x hx).trans hleR⟩

section Fields

/-- Shortcut instance for bounded continuous fields of `n`-multilinear maps on `ℂ`. Without it,
instance search for the norm of these fields fails inside `LinearMap.mkContinuous`. It is local,
and no public statement mentions it: only the private field operators below use it. -/
private local instance instNormedAddCommGroupBoundedContinuousFunction {X : Type*}
    [TopologicalSpace X] (n : ℕ) : NormedAddCommGroup (X →ᵇ (ℂ [×n]→L[ℝ] F)) :=
  inferInstance

/-- Shortcut instance for bounded continuous fields of `n`-multilinear maps on `ℂ`, needed for
the operator norm bounds of the private field operators below. It is local for the same reason. -/
private local instance instNormedSpaceBoundedContinuousFunction {X : Type*} [TopologicalSpace X]
    (n : ℕ) : NormedSpace ℝ (X →ᵇ (ℂ [×n]→L[ℝ] F)) :=
  inferInstance

/-- The derivative field of order `j ≤ k + 1` of the transform, restricted to the output disc. -/
private def cauchyField (hα : 0 < α) (hα1 : α < 1) (hr : 0 ≤ r) (j : ℕ) (hj : j ≤ k + 1)
    (f : supportedCkHolderSubmodule (E := ℂ) (F := F) k α (closedBall c r)) :
    closedBall c R →ᵇ (ℂ [×j]→L[ℝ] F) :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun x ↦ iteratedFDeriv ℝ j (cauchyCk f) x,
      ((contDiff_cauchyCk hα hα1 hr f).continuous_iteratedFDeriv
        (by exact_mod_cast hj)).comp continuous_subtype_val⟩

private theorem cauchyField_apply (hα : 0 < α) (hα1 : α < 1) (hr : 0 ≤ r) (j : ℕ)
    (hj : j ≤ k + 1) (f : supportedCkHolderSubmodule (E := ℂ) (F := F) k α (closedBall c r))
    (x : closedBall c R) :
    cauchyField hα hα1 hr j hj f x = iteratedFDeriv ℝ j (cauchyCk f) x :=
  rfl

private def cauchyFieldLinearMap (hα : 0 < α) (hα1 : α < 1) (hr : 0 ≤ r) (j : ℕ)
    (hj : j ≤ k + 1) :
    supportedCkHolderSubmodule (E := ℂ) (F := F) k α (closedBall c r) →ₗ[ℝ]
      (closedBall c R →ᵇ (ℂ [×j]→L[ℝ] F)) where
  toFun := cauchyField hα hα1 hr j hj
  map_add' f g := by
    ext1 x
    have hj' : (j : WithTop ℕ∞) ≤ (k + 1 : ℕ) := by exact_mod_cast hj
    simp only [cauchyField_apply, FunLike.coe_add, Pi.add_apply,
      cauchyCk_add]
    exact iteratedFDeriv_add_apply ((contDiff_cauchyCk hα hα1 hr f).contDiffAt.of_le hj')
      ((contDiff_cauchyCk hα hα1 hr g).contDiffAt.of_le hj')
  map_smul' a f := by
    ext1 x
    have hj' : (j : WithTop ℕ∞) ≤ (k + 1 : ℕ) := by exact_mod_cast hj
    simp only [cauchyField_apply, FunLike.coe_smul, Pi.smul_apply,
      cauchyCk_smul, RingHom.id_apply]
    exact iteratedFDeriv_const_smul_apply ((contDiff_cauchyCk hα hα1 hr f).contDiffAt.of_le hj')

private theorem norm_cauchyField_le (hα : 0 < α) (hα1 : α < 1) (hr : 0 ≤ r) (hR : 0 ≤ R)
    (j : ℕ) (hj : j ≤ k + 1)
    (f : supportedCkHolderSubmodule (E := ℂ) (F := F) k α (closedBall c r)) :
    ‖cauchyField (R := R) hα hα1 hr j hj f‖ ≤ 2 * gainConst (F := F) k hα hα1 c hr hR * ‖f‖ :=
  (BoundedContinuousFunction.norm_le (by positivity)).mpr fun x ↦
    (gain_source hα hα1 hr hR f).2 j hj x x.property

/-- The derivative field of order `j ≤ k + 1` of the Cauchy transform on the output disc, as a
bounded operator on the supported `C^{k,α}` source space. -/
private def cauchyFieldCLM (hα : 0 < α) (hα1 : α < 1) (hr : 0 ≤ r) (hR : 0 ≤ R) (j : ℕ)
    (hj : j ≤ k + 1) :
    supportedCkHolderSubmodule (E := ℂ) (F := F) k α (closedBall c r) →L[ℝ]
      (closedBall c R →ᵇ (ℂ [×j]→L[ℝ] F)) :=
  (cauchyFieldLinearMap hα hα1 hr j hj).mkContinuous (2 * gainConst (F := F) k hα hα1 c hr hR)
    (norm_cauchyField_le hα hα1 hr hR j hj)

/-- The top derivative field of the transform on the output disc, as a Hölder field. -/
private def cauchyTop (hα : 0 < α) (hα1 : α < 1) (hr : 0 ≤ r) (hR : 0 ≤ R)
    (f : supportedCkHolderSubmodule (E := ℂ) (F := F) k α (closedBall c r)) :
    HolderSpace α (closedBall c R) (ℂ [×k + 1]→L[ℝ] F) :=
  HolderSpace.ofBoundedContinuousFunction (cauchyField hα hα1 hr (k + 1) le_rfl f)
    (HolderWith.memHolder (C := 2 * gainConst (F := F) k hα hα1 c hr hR * ‖f‖₊)
      fun x y ↦ (gain_source hα hα1 hr hR f).1 x x.property y y.property)

private theorem cauchyTop_apply (hα : 0 < α) (hα1 : α < 1) (hr : 0 ≤ r) (hR : 0 ≤ R)
    (f : supportedCkHolderSubmodule (E := ℂ) (F := F) k α (closedBall c r))
    (x : closedBall c R) :
    cauchyTop hα hα1 hr hR f x = iteratedFDeriv ℝ (k + 1) (cauchyCk f) x := by
  rw [cauchyTop, HolderSpace.ofBoundedContinuousFunction_apply, cauchyField_apply]

private def cauchyTopLinearMap (hα : 0 < α) (hα1 : α < 1) (hr : 0 ≤ r) (hR : 0 ≤ R) :
    supportedCkHolderSubmodule (E := ℂ) (F := F) k α (closedBall c r) →ₗ[ℝ]
      HolderSpace α (closedBall c R) (ℂ [×k + 1]→L[ℝ] F) where
  toFun := cauchyTop hα hα1 hr hR
  map_add' f g := by
    apply HolderSpace.ext
    intro x
    rw [HolderSpace.add_apply, cauchyTop_apply, cauchyTop_apply, cauchyTop_apply]
    exact congrArg (· x) ((cauchyFieldLinearMap hα hα1 hr (R := R) (k + 1) le_rfl).map_add f g)
  map_smul' a f := by
    apply HolderSpace.ext
    intro x
    rw [HolderSpace.smul_apply, cauchyTop_apply, cauchyTop_apply]
    exact congrArg (· x) ((cauchyFieldLinearMap hα hα1 hr (R := R) (k + 1) le_rfl).map_smul a f)

private theorem norm_cauchyTop_le (hα : 0 < α) (hα1 : α < 1) (hr : 0 ≤ r) (hR : 0 ≤ R)
    (f : supportedCkHolderSubmodule (E := ℂ) (F := F) k α (closedBall c r)) :
    ‖cauchyTop hα hα1 hr hR f‖ ≤ (2 * (2 * gainConst (F := F) k hα hα1 c hr hR)) * ‖f‖ := by
  set B := 2 * gainConst (F := F) k hα hα1 c hr hR
  have hval (x : closedBall c R) : (cauchyTop hα hα1 hr hR f).toBoundedContinuousFunction x =
      iteratedFDeriv ℝ (k + 1) (cauchyCk f) x := by
    rw [HolderSpace.toBoundedContinuousFunction_apply, cauchyTop_apply]
  have hH : HolderWith (B * ‖f‖₊) α
      ((cauchyTop hα hα1 hr hR f).toBoundedContinuousFunction :
        closedBall c R → (ℂ [×k + 1]→L[ℝ] F)) := fun x y ↦ by
    rw [hval, hval]
    exact (gain_source hα hα1 hr hR f).1 x x.property y y.property
  have hHN : (nnHolderNorm α ((cauchyTop hα hα1 hr hR f).toBoundedContinuousFunction :
      closedBall c R → (ℂ [×k + 1]→L[ℝ] F)) : ℝ) ≤ B * ‖f‖ := by
    have h := ENNReal.coe_le_coe.mp (coe_nnHolderNorm_le_eHolderNorm.trans hH.eHolderNorm_le)
    simpa only [NNReal.coe_mul, coe_nnnorm] using NNReal.coe_le_coe.mpr h
  have hN : ‖(cauchyTop hα hα1 hr hR f).toBoundedContinuousFunction‖ ≤ B * ‖f‖ :=
    (BoundedContinuousFunction.norm_le (by positivity)).mpr fun x ↦ by
      rw [hval]
      exact (gain_source hα hα1 hr hR f).2 (k + 1) le_rfl x x.property
  rw [HolderSpace.norm_def]
  calc
    _ ≤ (B : ℝ) * ‖f‖ + B * ‖f‖ := add_le_add hN hHN
    _ = _ := by
      simp only [B]
      push_cast
      ring

end Fields

/-- **The Cauchy transform as a bounded operator `C^{k,α}(D_r) → C^{k+1,α}(D_R)`.** For
`0 < α < 1`, it sends `C^{k,α}` data supported in `closedBall c r` to the derivative fields
`x ↦ D^i (T f) x` of orders `i ≤ k + 1` on `closedBall c R`, each with the supremum norm, together
with the `α`-Hölder field `D^{k+1} (T f)` on `closedBall c R`. It is real linear and bounded, so
continuous source families give continuous families of derivative fields in these norms. For
`k = 0` it carries the same data as `TauCeti.cauchyTransformCLM`. -/
def cauchyTransformCkCLM (k : ℕ) (hα : 0 < α) (hα1 : α < 1) (hr : 0 ≤ r) (hR : 0 ≤ R) :
    supportedCkHolderSubmodule (E := ℂ) (F := F) k α (closedBall c r) →L[ℝ]
      ((i : Fin (k + 2)) → closedBall c R →ᵇ (ℂ [×i]→L[ℝ] F)) ×
        HolderSpace α (closedBall c R) (ℂ [×k + 1]→L[ℝ] F) :=
  (ContinuousLinearMap.pi fun i : Fin (k + 2) ↦
      cauchyFieldCLM hα hα1 hr hR i (Nat.lt_succ_iff.mp i.isLt)).prod
    ((cauchyTopLinearMap hα hα1 hr hR).mkContinuous
      (2 * (2 * gainConst (F := F) k hα hα1 c hr hR)) (norm_cauchyTop_le hα hα1 hr hR))

/-- The derivative-field component of `TauCeti.cauchyTransformCkCLM` is the iterated derivative
of the actual Cauchy transform. -/
@[simp]
theorem cauchyTransformCkCLM_apply_fst (k : ℕ) (hα : 0 < α) (hα1 : α < 1) (hr : 0 ≤ r)
    (hR : 0 ≤ R) (f : supportedCkHolderSubmodule (E := ℂ) (F := F) k α (closedBall c r))
    (i : Fin (k + 2)) (x : closedBall c R) :
    (cauchyTransformCkCLM k hα hα1 hr hR f).1 i x =
      iteratedFDeriv ℝ i (cauchyTransform (f : CkHolderSpace k α ℂ F)) x :=
  cauchyField_apply hα hα1 hr i (Nat.lt_succ_iff.mp i.isLt) f x

/-- The Hölder component of `TauCeti.cauchyTransformCkCLM` is the derivative of order `k + 1` of
the actual Cauchy transform. -/
@[simp]
theorem cauchyTransformCkCLM_apply_snd (k : ℕ) (hα : 0 < α) (hα1 : α < 1) (hr : 0 ≤ r)
    (hR : 0 ≤ R) (f : supportedCkHolderSubmodule (E := ℂ) (F := F) k α (closedBall c r))
    (x : closedBall c R) :
    (cauchyTransformCkCLM k hα hα1 hr hR f).2 x =
      iteratedFDeriv ℝ (k + 1) (cauchyTransform (f : CkHolderSpace k α ℂ F)) x :=
  cauchyTop_apply hα hα1 hr hR f x

end Operator

section ConePoint

/-- On `[0, ∞)` the power `t ↦ t ^ p` is `p`-Hölder with constant one, for `0 ≤ p ≤ 1`. -/
private theorem abs_rpow_sub_rpow_le {a b p : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hp : 0 ≤ p)
    (hp1 : p ≤ 1) : |a ^ p - b ^ p| ≤ |a - b| ^ p := by
  wlog hab : b ≤ a generalizing a b
  · rw [abs_sub_comm, abs_sub_comm a]
    exact this hb ha (le_of_not_ge hab)
  have h := Real.rpow_add_le_add_rpow (sub_nonneg.mpr hab) hb hp hp1
  rw [sub_add_cancel] at h
  rw [abs_of_nonneg (sub_nonneg.mpr (Real.rpow_le_rpow hb hab hp)),
    abs_of_nonneg (sub_nonneg.mpr hab)]
  linarith

/-- The source `‖z‖ ^ α χ(z)` of the cone-point check is globally `α`-Hölder for a compactly
supported `C¹` cutoff `χ`. -/
private theorem exists_holderWith_norm_rpow_mul {α : ℝ≥0} (hα1 : α ≤ 1) {χ : ℂ → ℝ}
    (hχ : ContDiff ℝ 1 χ) (hc : HasCompactSupport χ) :
    ∃ H : ℝ≥0, HolderWith H α (fun z : ℂ ↦ ((‖z‖ ^ (α : ℝ) * χ z : ℝ) : ℂ)) := by
  obtain ⟨ρ, -, hsub⟩ := hc.isCompact.isBounded.subset_closedBall_lt 0 (0 : ℂ)
  obtain ⟨A, hA⟩ := hχ.continuous.bounded_above_of_compact_support hc
  obtain ⟨L, hL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hc hχ one_ne_zero
  have hχH := (hL.lipschitzOnWith (s := univ)).holderOnWith_of_norm_le (M := A.toNNReal)
    (fun x _ ↦ (hA x).trans (Real.le_coe_toNNReal A)) hα1
  let K : ℝ≥0 := A.toNNReal + (ρ ^ (α : ℝ)).toNNReal * (L + 2 * A.toNNReal)
  -- The bound when `y` is the point closer to the origin, so that `‖y‖ ≤ ρ` unless both
  -- values of `χ` vanish.
  have key (x y : ℂ) (hxy : ‖y‖ ≤ ‖x‖) :
      |‖x‖ ^ (α : ℝ) * χ x - ‖y‖ ^ (α : ℝ) * χ y| ≤ K * dist x y ^ (α : ℝ) := by
    by_cases h0 : χ x = 0 ∧ χ y = 0
    · rw [h0.1, h0.2, mul_zero, mul_zero, sub_zero, abs_zero]
      positivity
    have hy : ‖y‖ ≤ ρ := by
      rcases not_and_or.mp h0 with h | h
      · exact hxy.trans (by simpa using hsub (subset_tsupport _ h))
      · simpa using hsub (subset_tsupport _ h)
    have hρ : 0 ≤ ρ := (norm_nonneg y).trans hy
    have h1 : |‖x‖ ^ (α : ℝ) - ‖y‖ ^ (α : ℝ)| ≤ dist x y ^ (α : ℝ) :=
      (abs_rpow_sub_rpow_le (norm_nonneg _) (norm_nonneg _) α.coe_nonneg hα1).trans
        (Real.rpow_le_rpow (abs_nonneg _) (by rw [dist_eq_norm]; exact abs_norm_sub_norm_le x y)
          α.coe_nonneg)
    have h2 : |χ x - χ y| ≤ (L + 2 * A.toNNReal : ℝ≥0) * dist x y ^ (α : ℝ) := by
      rw [← Real.dist_eq]
      exact hχH.dist_le (mem_univ _) (mem_univ _)
    have h3 : |χ x| ≤ A.toNNReal := (hA x).trans (Real.le_coe_toNNReal A)
    have h4 : ‖y‖ ^ (α : ℝ) ≤ ρ ^ (α : ℝ) := Real.rpow_le_rpow (norm_nonneg _) hy α.coe_nonneg
    have e : ‖x‖ ^ (α : ℝ) * χ x - ‖y‖ ^ (α : ℝ) * χ y =
        (‖x‖ ^ (α : ℝ) - ‖y‖ ^ (α : ℝ)) * χ x + ‖y‖ ^ (α : ℝ) * (χ x - χ y) := by ring
    have hyα : 0 ≤ ‖y‖ ^ (α : ℝ) := by positivity
    rw [e]
    calc
      _ ≤ |‖x‖ ^ (α : ℝ) - ‖y‖ ^ (α : ℝ)| * |χ x| + ‖y‖ ^ (α : ℝ) * |χ x - χ y| := by
        refine (abs_add_le _ _).trans_eq ?_
        rw [abs_mul, abs_mul, abs_of_nonneg hyα]
      _ ≤ dist x y ^ (α : ℝ) * A.toNNReal +
          ρ ^ (α : ℝ) * ((L + 2 * A.toNNReal : ℝ≥0) * dist x y ^ (α : ℝ)) := by
        gcongr
      _ = _ := by
        simp only [K]
        push_cast
        rw [Real.coe_toNNReal _ (Real.rpow_nonneg hρ _)]
        ring
  refine ⟨K, holderOnWith_univ.mp (HolderOnWith.of_dist_le fun x _ y _ ↦ ?_)⟩
  rw [dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  rcases le_total ‖y‖ ‖x‖ with h | h
  · exact key x y h
  · rw [abs_sub_comm, dist_comm]
    exact key y x h

/-- **The cone-point check for the Hölder gain.** For `0 < α < 1` and a compactly supported `C¹`
cutoff `χ`, the source `‖z‖ ^ α χ(z)` is `α`-Hölder, and its Cauchy transform is `C¹` near every
closed disc about `0`, with `α`-Hölder derivative there: one derivative better. -/
theorem contDiffOn_holderOnWith_fderiv_cauchyTransform_norm_rpow_mul {α : ℝ≥0} (hα : 0 < α)
    (hα1 : α < 1) {χ : ℂ → ℝ} (hχ : ContDiff ℝ 1 χ) (hc : HasCompactSupport χ) {R : ℝ}
    (hR : 0 ≤ R) :
    ContDiffOn ℝ 1 (cauchyTransform fun z : ℂ ↦ ((‖z‖ ^ (α : ℝ) * χ z : ℝ) : ℂ))
        (ball 0 (R + 1)) ∧
      ∃ C : ℝ≥0, HolderOnWith C α
        (fderiv ℝ (cauchyTransform fun z : ℂ ↦ ((‖z‖ ^ (α : ℝ) * χ z : ℝ) : ℂ)))
        (closedBall 0 R) := by
  obtain ⟨H, hH⟩ := exists_holderWith_norm_rpow_mul hα1.le hχ hc
  obtain ⟨ρ, hρ, hsub⟩ := hc.isCompact.isBounded.subset_closedBall_lt 0 (0 : ℂ)
  obtain ⟨A, hA⟩ := hχ.continuous.bounded_above_of_compact_support hc
  obtain ⟨C, hC⟩ :=
    exists_contDiffOn_holderOnWith_fderiv_pi_inv_smul_integral_sub_inv_smul
      (F := ℂ) hα hα1 0 hρ.le hR
  have hs : Function.support (fun z : ℂ ↦ ((‖z‖ ^ (α : ℝ) * χ z : ℝ) : ℂ)) ⊆
      closedBall 0 ρ := fun z hz ↦ by
    refine hsub (subset_tsupport _ fun h ↦ hz ?_)
    simp only [h, mul_zero, Complex.ofReal_zero]
  have hM (z : ℂ) : ‖((‖z‖ ^ (α : ℝ) * χ z : ℝ) : ℂ)‖ ≤ (ρ ^ (α : ℝ) * A).toNNReal := by
    refine le_trans ?_ (Real.le_coe_toNNReal _)
    by_cases h : χ z = 0
    · simp only [h, mul_zero, Complex.ofReal_zero, norm_zero]
      exact mul_nonneg (by positivity) ((norm_nonneg _).trans (hA z))
    have hz : ‖z‖ ≤ ρ := by simpa using hsub (subset_tsupport _ h)
    rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity)]
    exact mul_le_mul (Real.rpow_le_rpow (norm_nonneg _) hz α.coe_nonneg) (hA z) (abs_nonneg _)
      (by positivity)
  obtain ⟨hcd, hD, -, -⟩ := hC hs hH hM
  rw [funext (cauchyTransform_apply _)]
  exact ⟨hcd, _, hD⟩

end ConePoint

end TauCeti
