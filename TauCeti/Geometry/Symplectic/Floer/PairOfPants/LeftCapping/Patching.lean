/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.LeftCapping
public import TauCeti.Geometry.Symplectic.Floer.Linearization.Pullback
public import TauCeti.Geometry.Symplectic.Floer.SemiFredholm.Adjoint
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import TauCeti.Analysis.Calculus.ContDiff.Bounds
import TauCeti.Analysis.Complex.Basic
import TauCeti.Analysis.Complex.RealChart
import TauCeti.Analysis.SpecialFunctions.SmoothTransition
import TauCeti.Geometry.Symplectic.Floer.SemiFredholm.Patching
import TauCeti.Topology.ContinuousOn.CompactDomination

/-!
# Patching the semi-Fredholm estimate of the formal adjoint on the pair of pants capped at `0`

The left unit of the pair-of-pants product is compared with continuation maps along the
input-exchange family capped at `0`, whose domain is the capped surface `ℂ ∖ {1}`: the input end
at `1` is read in the positive end chart `φ'_1` of the pair of pants, the output end in the chart
`c + φ'_∞` recentred at a point `c ∈ [0, 1]`, and the capped puncture `0` is an interior point.
The cokernel of the linearized Floer operator `D_u` is the kernel of its formal adjoint `D_u^*`
(`TauCeti.SymplecticForm.floerLinearizationAdjoint`), and its finiteness rests on a semi-Fredholm
estimate of `D_u^*`. This file patches that estimate together from estimates of `D_u^*` on the two
ends, for any Floer data regular and compatible along `u` on `ℂ ∖ {1}` and any weight `w`
continuous and positive there, in the namespace `TauCeti.SymplecticForm`:
`exists_forall_sum_setIntegral_add_setIntegral_le_mul_integral_floerLinearizationAdjoint_of_capped`.

A covector field `η` is read on an end as the `(0, 1)`-form `η' = η (ψ ·) ∘ (a + b J)`
(`TauCeti.Floer.covectorPullback`), and the core is the annulus
`Σ_T = {exp (-2πT) / 2 ≤ |w - 1|, |w - c| ≤ 2 exp (2πT)}`, which contains the capped puncture `0`
and is bounded by the circles `s = T` of the two ends. The estimate is

`∑_{e} ∫_{(T, ∞) × [0, 1]} (‖∂s η'_e‖² + ‖∂t η'_e‖² + ‖η'_e‖²)`
`  + ∫_{Σ_T} (‖∂s η‖² + ‖∂t η‖² + ‖η‖²) ≤ C (∫ w ‖D_u^* η‖² + ∫_{Σ_{T + 1}} ‖η‖²)`.

A covector field is cut into end pieces `β_e η`, with `β_e = ψ(2 (s_e - R₀) - 1)` for the smooth
transition function `ψ` and the longitudinal coordinate `s_e` of the end `e`, and the core piece
`(1 - ∑_e β_e) η`, supported in `Σ_{R₀ + 1}`. The end pieces are controlled by the end estimates,
and the core piece by the interior estimate of the adjoint
(`exists_forall_setIntegral_sobolevDensity_le_mul_setIntegral_floerLinearizationAdjoint_add`);
the capped puncture is an interior point of the core, so no estimate is needed there. Beyond the
height `0` the two ends are disjoint, so at most one end cutoff is nonzero at each point. The
steps that do not depend on the domain are shared with the pair of pants through
`TauCeti.Geometry.Symplectic.Floer.SemiFredholm.Patching`.

The end estimates along the input-exchange family capped at `0` are supplied in
`TauCeti.Geometry.Symplectic.Floer.PairOfPants.LeftCapping.Adjoint`.

## References

* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, 2nd ed., Section 3.1
  and Appendices B and C.1, on the formal adjoint and the semi-Fredholm estimate on punctured
  Riemann surfaces with cylindrical ends.
-/

public section

open Filter Function Set MeasureTheory TauCeti.ThricePuncturedSphere
  TauCeti.ThricePuncturedSphere.Puncture
open scoped Topology NNReal Manifold Real

namespace TauCeti.SymplecticForm

open Floer

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] {c : ℝ}

/-! ### The ends of the capped surface -/

/-- The capped surface `ℂ ∖ {1}`, in real coordinates. -/
private def cappedDomain : Set (ℝ × ℝ) := {z | Complex.equivRealProdCLM.symm z ≠ 1}

private theorem mem_cappedDomain {z : ℝ × ℝ} :
    z ∈ cappedDomain ↔ Complex.equivRealProdCLM.symm z ≠ 1 :=
  Iff.rfl

private theorem isOpen_cappedDomain : IsOpen cappedDomain :=
  isOpen_ne_fun Complex.equivRealProdCLM.symm.continuous continuous_const

/-- The longitudinal coordinate of the end `e` of the capped surface: on the input end at `1`
(`true`) the first positive end coordinate of the pair of pants, on the output end (`false`) the
first positive end coordinate of the output end recentred at `c`. -/
private noncomputable def cappedEndCoord (c : ℝ) : Bool → ℝ × ℝ → ℝ
  | true, z => (positiveEndCoord one z).1
  | false, z => (positiveEndCoord inf (z - (c, 0))).1

/-- The chart of the end `e` of the capped surface: the positive end chart `φ'_1` on the input
end, and `c + φ'_∞` on the output end. -/
private noncomputable def cappedEndChart (c : ℝ) : Bool → ℝ × ℝ → ℝ × ℝ
  | true => positiveEndChart one
  | false => fun ζ ↦ positiveEndChart inf ζ + (c, 0)

/-- The longitudinal coordinate recovers the first coordinate of a point of the end chart. -/
private theorem cappedEndCoord_cappedEndChart (e : Bool) (ζ : ℝ × ℝ) :
    cappedEndCoord c e (cappedEndChart c e ζ) = ζ.1 := by
  cases e <;> simp [cappedEndCoord, cappedEndChart]

private theorem contDiff_cappedEndChart (e : Bool) {n : WithTop ℕ∞} :
    ContDiff ℝ n (cappedEndChart c e) := by
  cases e
  · exact (contDiff_positiveEndChart inf n).add contDiff_const
  · exact contDiff_positiveEndChart one n

/-- Away from `c`, the coordinate of the output end exceeds `r` exactly off the closed disc
`‖w - c‖ ≤ 2 exp (2πr)`. -/
private theorem lt_cappedEndCoord_false_iff {r : ℝ} {z : ℝ × ℝ}
    (hz : Complex.equivRealProdCLM.symm z ≠ c) :
    r < cappedEndCoord c false z ↔
      2 * Real.exp (2 * π * r) < ‖Complex.equivRealProdCLM.symm z - c‖ := by
  rw [cappedEndCoord, lt_fst_positiveEndCoord_inf_iff,
    TauCeti.Complex.equivRealProdCLM_symm_sub_prodMk_zero]
  rw [TauCeti.Complex.equivRealProdCLM_symm_sub_prodMk_zero]
  exact sub_ne_zero.2 hz

/-- On the closed disc `‖w - c‖ ≤ 2 exp (2πr)` with `r ≥ 0`, the coordinate of the output end is at
most `r`. -/
private theorem cappedEndCoord_false_le {r : ℝ} (hr : 0 ≤ r) {z : ℝ × ℝ}
    (hz : ‖Complex.equivRealProdCLM.symm z - c‖ ≤ 2 * Real.exp (2 * π * r)) :
    cappedEndCoord c false z ≤ r := by
  rw [cappedEndCoord, fst_positiveEndCoord, endSign_inf, neg_one_mul]
  refine neg_re_endCoord_inf_le hr ?_
  rwa [TauCeti.Complex.equivRealProdCLM_symm_sub_prodMk_zero]

/-- Away from `1`, the coordinate of the input end is at most `r` exactly off the open disc
`‖w - 1‖ < exp (-2πr) / 2`. -/
private theorem cappedEndCoord_true_le_iff {r : ℝ} {z : ℝ × ℝ} (hz : z ∈ cappedDomain) :
    cappedEndCoord c true z ≤ r ↔
      Real.exp (-(2 * π * r)) / 2 ≤ ‖Complex.equivRealProdCLM.symm z - 1‖ := by
  rw [cappedEndCoord, fst_positiveEndCoord, endSign_one, one_mul,
    re_endCoord_le_iff (by decide) (by rw [endCenter_one]; exact hz), endCenter_one]

/-- A point lies beyond the height `0` on at most one end of the capped surface. -/
private theorem cappedEndCoord_nonpos_of_ne (hc₀ : 0 ≤ c) (hc₁ : c ≤ 1) {e e' : Bool}
    (hee' : e ≠ e') {z : ℝ × ℝ} (h : 0 < cappedEndCoord c e z) : cappedEndCoord c e' z ≤ 0 := by
  have h₂ := Complex.norm_sub_ofReal_le_norm_sub_one_add_one hc₀ (by linarith)
    (Complex.equivRealProdCLM.symm z)
  cases e <;> cases e' <;> simp only [ne_eq, not_true_eq_false] at hee'
  · -- Beyond `0` on the output end, `‖w - c‖ > 2`, so `‖w - 1‖ > 1`.
    have h₁ := two_lt_norm_sub_of_pos_fst_positiveEndCoord_inf_sub h
    rw [cappedEndCoord, fst_positiveEndCoord, endSign_one, one_mul]
    exact re_endCoord_nonpos_of_le_norm_sub_endCenter (by decide) (by rw [endCenter_one]; linarith)
  · -- Beyond `0` on the input end, `‖w - 1‖ < 1/2`, so `‖w - c‖ < 3/2`.
    have h₁ := norm_sub_one_lt_of_pos_fst_positiveEndCoord_one h
    refine cappedEndCoord_false_le le_rfl ?_
    simp only [mul_zero, Real.exp_zero, mul_one]
    linarith

/-- The coordinate of the input end is smooth on the capped surface. -/
private theorem contDiffAt_cappedEndCoord_true {z : ℝ × ℝ} (hz : z ∈ cappedDomain)
    {n : WithTop ℕ∞} : ContDiffAt ℝ n (cappedEndCoord c true) z :=
  contDiffAt_fst_positiveEndCoord one (by rw [endCenter_one]; exact hz)

/-- The coordinate of the output end is smooth away from `c`. -/
private theorem contDiffAt_cappedEndCoord_false {z : ℝ × ℝ}
    (hz : Complex.equivRealProdCLM.symm z ≠ c) {n : WithTop ℕ∞} :
    ContDiffAt ℝ n (cappedEndCoord c false) z := by
  have h : Complex.equivRealProdCLM.symm (z - (c, 0)) ≠ inf.endCenter := by
    rw [TauCeti.Complex.equivRealProdCLM_symm_sub_prodMk_zero, endCenter_inf]
    exact sub_ne_zero.2 hz
  exact (contDiffAt_fst_positiveEndCoord inf h).comp z (contDiffAt_id.sub contDiffAt_const)

/-! ### The core of the capped surface -/

/-- The core `Σ_T` of the capped surface: the annulus `exp (-2πT) / 2 ≤ |w - 1|`,
`|w - c| ≤ 2 exp (2πT)` bounded by the circles `s = T` of the two ends. -/
private def cappedCore (c T : ℝ) : Set (ℝ × ℝ) :=
  {z | Real.exp (-(2 * π * T)) / 2 ≤ ‖Complex.equivRealProdCLM.symm z - 1‖ ∧
    ‖Complex.equivRealProdCLM.symm z - c‖ ≤ 2 * Real.exp (2 * π * T)}

private theorem isCompact_cappedCore (c T : ℝ) : IsCompact (cappedCore c T) := by
  have hball : IsCompact (Complex.equivRealProdCLM.symm ⁻¹'
      Metric.closedBall (c : ℂ) (2 * Real.exp (2 * π * T))) :=
    Complex.equivRealProdCLM.symm.toHomeomorph.isCompact_preimage.2
      (isCompact_closedBall _ _)
  refine hball.of_isClosed_subset ?_ fun z hz ↦ ?_
  · exact (isClosed_le continuous_const (continuous_norm.comp
      (Complex.equivRealProdCLM.symm.continuous.sub continuous_const))).inter
      (isClosed_le (continuous_norm.comp
        (Complex.equivRealProdCLM.symm.continuous.sub continuous_const)) continuous_const)
  · simpa [dist_eq_norm] using hz.2

private theorem cappedCore_mono (c : ℝ) : Monotone (cappedCore c) := fun T T' h z hz ↦
  ⟨le_trans (by gcongr) hz.1, hz.2.trans (by gcongr)⟩

private theorem cappedCore_subset (c T : ℝ) : cappedCore c T ⊆ cappedDomain := fun z hz h1 ↦ by
  have := hz.1
  rw [h1, sub_self, norm_zero] at this
  linarith [Real.exp_pos (-(2 * π * T))]

/-- For `T ≥ 0`, a point lies in the core `Σ_T` exactly when it lies in the capped surface and its
coordinate on each end is at most `T`. -/
private theorem mem_cappedCore_iff {T : ℝ} (hT : 0 ≤ T) {z : ℝ × ℝ} :
    z ∈ cappedCore c T ↔ z ∈ cappedDomain ∧ ∀ e, cappedEndCoord c e z ≤ T := by
  constructor
  · intro hz
    refine ⟨cappedCore_subset c T hz, fun e ↦ ?_⟩
    cases e
    · exact cappedEndCoord_false_le hT hz.2
    · exact (cappedEndCoord_true_le_iff (cappedCore_subset c T hz)).2 hz.1
  rintro ⟨hzU, hle⟩
  refine ⟨(cappedEndCoord_true_le_iff hzU).1 (hle true), ?_⟩
  · rcases eq_or_ne (Complex.equivRealProdCLM.symm z) c with hzc | hzc
    · rw [hzc, sub_self, norm_zero]
      positivity
    · exact not_lt.1 fun h ↦ (not_le.2 ((lt_cappedEndCoord_false_iff hzc).2 h)) (hle false)

/-! ### Cutoffs on the capped surface -/

/-- The cutoff `β_e = ψ(2 (s_e - R₀) - 1)` of the end `e`, for the smooth transition function `ψ`.
It vanishes to first order where `s_e ≤ R₀`, and it is `1` where `s_e ≥ R₀ + 1`. -/
private noncomputable def cappedEndCutoff (c R₀ : ℝ) (e : Bool) (z : ℝ × ℝ) : ℝ :=
  Real.smoothTransition (2 * (cappedEndCoord c e z - R₀) - 1)

private theorem cappedEndCutoff_eq_zero {R₀ : ℝ} {e : Bool} {z : ℝ × ℝ}
    (h : cappedEndCoord c e z ≤ R₀) : cappedEndCutoff c R₀ e z = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

private theorem cappedEndCutoff_eq_one {R₀ : ℝ} {e : Bool} {z : ℝ × ℝ}
    (h : R₀ + 1 ≤ cappedEndCoord c e z) : cappedEndCutoff c R₀ e z = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

private theorem cappedEndCutoff_nonneg (R₀ : ℝ) (e : Bool) (z : ℝ × ℝ) :
    0 ≤ cappedEndCutoff c R₀ e z :=
  Real.smoothTransition.nonneg _

private theorem cappedEndCutoff_le_one (R₀ : ℝ) (e : Bool) (z : ℝ × ℝ) :
    cappedEndCutoff c R₀ e z ≤ 1 :=
  Real.smoothTransition.le_one _

/-- For `R₀ ≥ 0`, at a point of the capped surface either the cutoff of the end `e` vanishes
nearby, or the coordinate of the end is smooth there. Near `c`, where the coordinate of the output
end is not smooth, the cutoff of the output end vanishes. -/
private theorem cappedEndCutoff_eventuallyEq_zero_or_contDiffAt {R₀ : ℝ} (hR₀ : 0 ≤ R₀)
    (e : Bool) {z : ℝ × ℝ} (hz : z ∈ cappedDomain) :
    cappedEndCutoff c R₀ e =ᶠ[𝓝 z] 0 ∨ ∀ n : WithTop ℕ∞, ContDiffAt ℝ n (cappedEndCoord c e) z := by
  cases e
  · rcases eq_or_ne (Complex.equivRealProdCLM.symm z) c with hzc | hzc
    · refine .inl ?_
      have hopen : IsOpen {w : ℝ × ℝ | ‖Complex.equivRealProdCLM.symm w - c‖ < 2} :=
        isOpen_lt (by fun_prop) continuous_const
      filter_upwards [hopen.mem_nhds (by simp [hzc])] with w hw
      refine cappedEndCutoff_eq_zero ((cappedEndCoord_false_le le_rfl ?_).trans hR₀)
      simp only [mul_zero, Real.exp_zero, mul_one]
      exact hw.le
    · exact .inr fun n ↦ contDiffAt_cappedEndCoord_false hzc
  · exact .inr fun n ↦ contDiffAt_cappedEndCoord_true hz

/-- The derivative of the cutoff of the end `e` where the coordinate of the end is smooth. -/
private theorem hasFDerivAt_cappedEndCutoff (R₀ : ℝ) {e : Bool} {z : ℝ × ℝ}
    (hs : ContDiffAt ℝ 1 (cappedEndCoord c e) z) :
    HasFDerivAt (cappedEndCutoff c R₀ e)
      (deriv Real.smoothTransition (2 * (cappedEndCoord c e z - R₀) - 1) •
        (2 : ℝ) • fderiv ℝ (cappedEndCoord c e) z) z :=
  (((hs.differentiableAt one_ne_zero).hasFDerivAt.sub_const R₀).const_mul 2 |>.sub_const
    1).smoothTransition

/-- The cutoff of an end is smooth on the capped surface, for `R₀ ≥ 0`. -/
private theorem contDiffAt_cappedEndCutoff {R₀ : ℝ} (hR₀ : 0 ≤ R₀) (e : Bool) {z : ℝ × ℝ}
    (hz : z ∈ cappedDomain) {n : ℕ∞} : ContDiffAt ℝ n (cappedEndCutoff c R₀ e) z := by
  rcases cappedEndCutoff_eventuallyEq_zero_or_contDiffAt hR₀ e hz with h | h
  · exact contDiffAt_const (c := (0 : ℝ)).congr_of_eventuallyEq h
  · exact Real.smoothTransition.contDiff.contDiffAt.comp z
      ((contDiffAt_const.mul ((h n).sub contDiffAt_const)).sub contDiffAt_const)

/-- Off the collar `R₀ ≤ s_e ≤ R₀ + 1`, the derivative of the cutoff of the end `e` vanishes. -/
private theorem mem_Icc_of_fderiv_cappedEndCutoff_ne_zero {R₀ : ℝ} (hR₀ : 0 ≤ R₀) {e : Bool}
    {z : ℝ × ℝ} (hz : z ∈ cappedDomain) (h : fderiv ℝ (cappedEndCutoff c R₀ e) z ≠ 0) :
    cappedEndCoord c e z ∈ Icc R₀ (R₀ + 1) := by
  rcases cappedEndCutoff_eventuallyEq_zero_or_contDiffAt hR₀ e hz with h₀ | h₀
  · exact absurd ((hasFDerivAt_const (0 : ℝ) z).congr_of_eventuallyEq h₀).fderiv h
  rw [(hasFDerivAt_cappedEndCutoff R₀ (h₀ 1)).fderiv] at h
  refine ⟨?_, ?_⟩ <;> by_contra! h'
  · exact h (by rw [Real.smoothTransition.deriv_of_nonpos (by linarith), zero_smul])
  · exact h (by rw [Real.smoothTransition.deriv_of_one_le (by linarith), zero_smul])

/-- Where the coordinate of the end is at most `R₀`, the cutoff of the end has derivative zero. -/
private theorem fderiv_cappedEndCutoff_eq_zero {R₀ : ℝ} (hR₀ : 0 ≤ R₀) {e : Bool} {z : ℝ × ℝ}
    (hz : z ∈ cappedDomain) (h : cappedEndCoord c e z ≤ R₀) :
    fderiv ℝ (cappedEndCutoff c R₀ e) z = 0 := by
  by_contra h'
  have := (mem_Icc_of_fderiv_cappedEndCutoff_ne_zero hR₀ hz h').1
  -- At `s_e = R₀` the cutoff has derivative `ψ'(-1) = 0`.
  have hs : cappedEndCoord c e z = R₀ := le_antisymm h this
  rcases cappedEndCutoff_eventuallyEq_zero_or_contDiffAt hR₀ e hz with h₀ | h₀
  · exact h' ((hasFDerivAt_const (0 : ℝ) z).congr_of_eventuallyEq h₀).fderiv
  · exact h' (by rw [(hasFDerivAt_cappedEndCutoff R₀ (h₀ 1)).fderiv, hs,
      Real.smoothTransition.deriv_of_nonpos (by linarith), zero_smul])

/-- The cutoff `1 - ∑_e β_e` of the core of the capped surface. -/
private noncomputable def cappedCoreCutoff (c R₀ : ℝ) (z : ℝ × ℝ) : ℝ :=
  1 - ∑ e, cappedEndCutoff c R₀ e z

private theorem contDiffAt_cappedCoreCutoff {R₀ : ℝ} (hR₀ : 0 ≤ R₀) {z : ℝ × ℝ}
    (hz : z ∈ cappedDomain) {n : ℕ∞} : ContDiffAt ℝ n (cappedCoreCutoff c R₀) z :=
  contDiffAt_const.sub (ContDiffAt.sum fun e _ ↦ contDiffAt_cappedEndCutoff hR₀ e hz)

private theorem fderiv_cappedCoreCutoff {R₀ : ℝ} (hR₀ : 0 ≤ R₀) {z : ℝ × ℝ}
    (hz : z ∈ cappedDomain) :
    fderiv ℝ (cappedCoreCutoff c R₀) z = -∑ e, fderiv ℝ (cappedEndCutoff c R₀ e) z := by
  have hd (e : Bool) : DifferentiableAt ℝ (cappedEndCutoff c R₀ e) z :=
    (contDiffAt_cappedEndCutoff hR₀ e hz (n := 1)).differentiableAt one_ne_zero
  unfold cappedCoreCutoff
  rw [fderiv_const_sub, fderiv_fun_sum fun e _ ↦ hd e]

section Geometry

variable (hc₀ : 0 ≤ c) (hc₁ : c ≤ 1)
include hc₀ hc₁

/-- At a point beyond `R₀ ≥ 0` on the end `e`, the cutoff of the other end vanishes. -/
private theorem cappedEndCutoff_eq_zero_of_ne {R₀ : ℝ} (hR₀ : 0 ≤ R₀) {e e' : Bool}
    (hee' : e ≠ e') {z : ℝ × ℝ} (h : R₀ < cappedEndCoord c e z) :
    cappedEndCutoff c R₀ e' z = 0 :=
  cappedEndCutoff_eq_zero ((cappedEndCoord_nonpos_of_ne hc₀ hc₁ hee' (by linarith)).trans hR₀)

/-- At most one end cutoff is nonzero, so the core cutoff lies in `[0, 1]`. -/
private theorem cappedCoreCutoff_mem_Icc {R₀ : ℝ} (hR₀ : 0 ≤ R₀) (z : ℝ × ℝ) :
    cappedCoreCutoff c R₀ z ∈ Icc 0 1 := by
  by_cases h : ∃ e, R₀ < cappedEndCoord c e z
  · obtain ⟨e, he⟩ := h
    rw [cappedCoreCutoff, Finset.sum_eq_single e (fun e' _ he' ↦
      cappedEndCutoff_eq_zero_of_ne hc₀ hc₁ hR₀ (Ne.symm he') he) (by simp)]
    exact ⟨by linarith [cappedEndCutoff_le_one (c := c) R₀ e z],
      by linarith [cappedEndCutoff_nonneg (c := c) R₀ e z]⟩
  · push Not at h
    simp [cappedCoreCutoff, cappedEndCutoff_eq_zero (h _)]

private theorem abs_cappedCoreCutoff_le_one {R₀ : ℝ} (hR₀ : 0 ≤ R₀) (z : ℝ × ℝ) :
    |cappedCoreCutoff c R₀ z| ≤ 1 :=
  abs_le.2 ⟨by linarith [(cappedCoreCutoff_mem_Icc hc₀ hc₁ hR₀ z).1],
    (cappedCoreCutoff_mem_Icc hc₀ hc₁ hR₀ z).2⟩

private theorem cappedCoreCutoff_eq_zero {R₀ : ℝ} (hR₀ : 0 ≤ R₀) {e : Bool} {z : ℝ × ℝ}
    (h : R₀ + 1 ≤ cappedEndCoord c e z) : cappedCoreCutoff c R₀ z = 0 := by
  rw [cappedCoreCutoff, Finset.sum_eq_single e (fun e' _ he' ↦
    cappedEndCutoff_eq_zero_of_ne hc₀ hc₁ hR₀ (Ne.symm he') (by linarith)) (by simp),
    cappedEndCutoff_eq_one h, sub_self]

/-- Where the derivative of an end cutoff is nonzero, the point lies in `Σ_{R₀ + 1}`. -/
private theorem mem_cappedCore_of_fderiv_cappedEndCutoff_ne_zero {R₀ : ℝ} (hR₀ : 0 < R₀)
    {e : Bool} {z : ℝ × ℝ} (hz : z ∈ cappedDomain)
    (h : fderiv ℝ (cappedEndCutoff c R₀ e) z ≠ 0) : z ∈ cappedCore c (R₀ + 1) := by
  obtain ⟨h₁, h₂⟩ := mem_Icc_of_fderiv_cappedEndCutoff_ne_zero hR₀.le hz h
  refine (mem_cappedCore_iff (by linarith)).2 ⟨hz, fun e' ↦ ?_⟩
  rcases eq_or_ne e e' with rfl | hee'
  · exact h₂
  · have := cappedEndCoord_nonpos_of_ne hc₀ hc₁ hee' (z := z) (by linarith)
    linarith

/-- Where the derivative of the core cutoff is nonzero, the point lies in `Σ_{R₀ + 1}`. -/
private theorem mem_cappedCore_of_fderiv_cappedCoreCutoff_ne_zero {R₀ : ℝ} (hR₀ : 0 < R₀)
    {z : ℝ × ℝ} (hz : z ∈ cappedDomain) (h : fderiv ℝ (cappedCoreCutoff c R₀) z ≠ 0) :
    z ∈ cappedCore c (R₀ + 1) := by
  rw [fderiv_cappedCoreCutoff hR₀.le hz, neg_ne_zero] at h
  obtain ⟨e, -, he⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  exact mem_cappedCore_of_fderiv_cappedEndCutoff_ne_zero hc₀ hc₁ hR₀ hz he

omit hc₀ hc₁ in
/-- On `Σ_{R₀}` the core cutoff is `1` to first order. -/
private theorem cappedCoreCutoff_eq_one_and_fderiv_eq_zero {R₀ : ℝ} (hR₀ : 0 ≤ R₀) {z : ℝ × ℝ}
    (hz : z ∈ cappedCore c R₀) :
    cappedCoreCutoff c R₀ z = 1 ∧ fderiv ℝ (cappedCoreCutoff c R₀) z = 0 := by
  obtain ⟨hzU, hle⟩ := (mem_cappedCore_iff hR₀).1 hz
  refine ⟨by simp [cappedCoreCutoff, cappedEndCutoff_eq_zero (hle _)], ?_⟩
  rw [fderiv_cappedCoreCutoff hR₀ hzU, neg_eq_zero]
  exact Finset.sum_eq_zero fun e _ ↦ fderiv_cappedEndCutoff_eq_zero hR₀ hzU (hle e)

omit [FiniteDimensional ℝ V] hc₀ hc₁ in
/-- The cut-off field `β_e η` of the end `e` is supported where `s_e ≥ R₀`. -/
private theorem tsupport_cappedEndCutoff_smul_subset {R₀ : ℝ} (hR₀ : 0 ≤ R₀) {e : Bool}
    {η : ℝ × ℝ → V →L[ℝ] ℝ}
    (hηU : tsupport η ⊆ cappedDomain) :
    tsupport (fun z ↦ cappedEndCutoff c R₀ e z • η z) ⊆
      {z | z ∈ cappedDomain ∧ R₀ ≤ cappedEndCoord c e z} := by
  intro z hz
  have hzU : z ∈ cappedDomain := hηU (tsupport_smul_subset_right _ _ hz)
  refine ⟨hzU, le_of_not_gt fun h ↦ notMem_tsupport_iff_eventuallyEq.2 ?_ hz⟩
  rcases cappedEndCutoff_eventuallyEq_zero_or_contDiffAt hR₀ e hzU (c := c) with h₀ | h₀
  · filter_upwards [h₀] with w hw
    simp [hw]
  · filter_upwards [(h₀ 0).continuousAt.eventually (Iio_mem_nhds h)] with w hw
    simp [cappedEndCutoff_eq_zero (le_of_lt hw)]

omit [FiniteDimensional ℝ V] in
/-- The cut-off field `(1 - ∑_e β_e) η` of the core is supported in `Σ_{R₀ + 1}`. -/
private theorem tsupport_cappedCoreCutoff_smul_subset {R₀ : ℝ} (hR₀ : 0 ≤ R₀)
    {η : ℝ × ℝ → V →L[ℝ] ℝ}
    (hηU : tsupport η ⊆ cappedDomain) :
    tsupport (fun z ↦ cappedCoreCutoff c R₀ z • η z) ⊆ cappedCore c (R₀ + 1) := by
  intro z hz
  have hzU : z ∈ cappedDomain := hηU (tsupport_smul_subset_right _ _ hz)
  refine (mem_cappedCore_iff (by linarith)).2 ⟨hzU, fun e ↦ le_of_not_gt fun h ↦
    notMem_tsupport_iff_eventuallyEq.2 ?_ hz⟩
  have hs : ContDiffAt ℝ 0 (cappedEndCoord c e) z := by
    rcases cappedEndCutoff_eventuallyEq_zero_or_contDiffAt hR₀ e hzU (c := c) with h₀ | h₀
    · -- The cutoff of the end `e` is `1` at `z`, so it does not vanish near `z`.
      exact absurd (h₀.eq_of_nhds) (by rw [cappedEndCutoff_eq_one (by linarith)]; norm_num)
    · exact h₀ 0
  filter_upwards [hs.continuousAt.eventually (Ioi_mem_nhds h)] with w hw
  simp [cappedCoreCutoff_eq_zero hc₀ hc₁ hR₀ (le_of_lt hw)]

end Geometry

/-! ### Covector fields read on the ends -/

omit [FiniteDimensional ℝ V] in
/-- If `J` is `C¹` along `u` and `u` is `C¹` on the capped surface, the `W^{1,2}` density of the
pulled-back form, in the chart of an end, of a `C¹` covector field supported in the capped surface
is continuous: near a point whose image lies off the support of the field, the form vanishes. -/
private theorem continuous_sobolevDensity_covectorPullback_cappedEndChart
    {J : ℝ × ℝ → V → V →L[ℝ] V} {u : ℝ × ℝ → V}
    (hJ : ∀ z ∈ cappedDomain, ContDiffAt ℝ 1 (Function.uncurry J) (z, u z))
    (hu : ∀ z ∈ cappedDomain, ContDiffAt ℝ 1 u z) {η : ℝ × ℝ → V →L[ℝ] ℝ}
    (hη : ContDiff ℝ 1 η) (hηU : tsupport η ⊆ cappedDomain) (e : Bool) :
    Continuous (sobolevDensity (covectorPullback (cappedEndChart c e) J u η)) := by
  refine continuous_sobolevDensity (contDiff_iff_contDiffAt.2 fun ζ ↦ ?_)
  have hφ : ContDiffAt ℝ 1 (cappedEndChart c e) ζ := (contDiff_cappedEndChart e).contDiffAt
  by_cases hζ : cappedEndChart c e ζ ∈ tsupport η
  · have hS := hηU hζ
    have hdφ : ContDiffAt ℝ 1 (fun w ↦ fderiv ℝ (cappedEndChart c e) w stdComplexLineReal) ζ :=
      (((contDiff_cappedEndChart (c := c) e (n := 2)).fderiv_right (m := 1)
        (by norm_num)).clm_apply contDiff_const).contDiffAt
    have hJu : ContDiffAt ℝ 1
        (fun w ↦ J (cappedEndChart c e w) (u (cappedEndChart c e w))) ζ :=
      (hJ _ hS).comp (f := fun w ↦ (cappedEndChart c e w, u (cappedEndChart c e w))) ζ
        (hφ.prodMk ((hu _ hS).comp ζ hφ))
    rw [show covectorPullback (cappedEndChart c e) J u η = _ from
      funext (covectorPullback_apply (cappedEndChart c e) J u η)]
    exact (hη.contDiffAt.comp ζ hφ).clm_comp (((contDiffAt_fst.comp ζ hdφ).smul
      (contDiffAt_const (c := (1 : V →L[ℝ] V)))).add ((contDiffAt_snd.comp ζ hdφ).smul hJu))
  · refine contDiffAt_const (c := (0 : V →L[ℝ] ℝ)).congr_of_eventuallyEq ?_
    filter_upwards [((isClosed_tsupport η).isOpen_compl.preimage
      (contDiff_cappedEndChart (c := c) e (n := 1)).continuous).mem_nhds hζ] with ζ' hζ'
    have h₀ : η (cappedEndChart c e ζ') = 0 := image_eq_zero_of_notMem_tsupport hζ'
    simp [covectorPullback_apply, h₀]

/-- The coordinate of each end is bounded above on a compact subset of the capped surface. -/
private theorem exists_forall_cappedEndCoord_le {K : Set (ℝ × ℝ)} (hK : IsCompact K)
    (hKU : K ⊆ cappedDomain) (e : Bool) : ∃ N, ∀ z ∈ K, cappedEndCoord c e z ≤ N := by
  cases e
  · simpa only [cappedEndCoord] using exists_forall_fst_positiveEndCoord_inf_sub_le hK
  · obtain ⟨N, hN⟩ := hK.exists_bound_of_continuousOn (f := cappedEndCoord c true)
      fun z hz ↦ (contDiffAt_cappedEndCoord_true (hKU hz) (n := 0)).continuousAt.continuousWithinAt
    exact ⟨N, fun z hz ↦ (Real.le_norm_self _).trans (hN z hz)⟩

omit [FiniteDimensional ℝ V] in
/-- If `J` is `C¹` along `u` and `u` is `C¹` on the capped surface, a `C¹` covector field with
compact support in the capped surface has integrable `W^{1,2}` energy density in the chart of each
end, read as the pulled-back form, over every half-cylinder `(a, ∞) × [0, 1]`: it vanishes far out
on the end. -/
private theorem integrableOn_sobolevDensity_covectorPullback_cappedEndChart
    {J : ℝ × ℝ → V → V →L[ℝ] V} {u : ℝ × ℝ → V}
    (hJ : ∀ z ∈ cappedDomain, ContDiffAt ℝ 1 (Function.uncurry J) (z, u z))
    (hu : ∀ z ∈ cappedDomain, ContDiffAt ℝ 1 u z) {η : ℝ × ℝ → V →L[ℝ] ℝ}
    (hη : ContDiff ℝ 1 η) (hηc : HasCompactSupport η) (hηU : tsupport η ⊆ cappedDomain)
    (e : Bool) (a : ℝ) :
    IntegrableOn (sobolevDensity (covectorPullback (cappedEndChart c e) J u η))
      (Ioi a ×ˢ Icc 0 1) := by
  obtain ⟨N, hN⟩ := exists_forall_cappedEndCoord_le (c := c) hηc.isCompact hηU e
  refine integrableOn_sobolevDensity_of_eventuallyEq_zero
    (continuous_sobolevDensity_covectorPullback_cappedEndChart hJ hu hη hηU e) (N := N)
    (fun ζ hζN ↦ ?_) a
  filter_upwards [(isOpen_lt continuous_const continuous_fst).mem_nhds hζN] with ζ' hζ'
  have h₀ : η (cappedEndChart c e ζ') = 0 := by
    refine image_eq_zero_of_notMem_tsupport fun h ↦ ?_
    have := hN _ h
    rw [cappedEndCoord_cappedEndChart] at this
    linarith
  simp [covectorPullback_apply, h₀]

/-! ### The formal adjoint on cut-off covector fields -/

/-- **The end estimate of the adjoint on a cut-off covector field.** If `D^*` controls the energy
of the pulled-back form, in the chart of the end `e`, of covector fields supported beyond the
height `R_e` of that end, against a weight `w`, then for `R_e < R₀` the energy of a covector field
beyond `R₀ + 1` on that end is controlled by the `w`-weighted norm of `D^* (β_e η)`. -/
private theorem setIntegral_sobolevDensity_covectorPullback_le_of_cappedEndCutoff
    (ω : SymplecticForm V) (hc₀ : 0 ≤ c) (hc₁ : c ≤ 1) {J : ℝ × ℝ → V → V →L[ℝ] V}
    {Ks Kt : ℝ × ℝ → V → ℝ} {u : ℝ × ℝ → V}
    (hJ : ∀ z ∈ cappedDomain, ContDiffAt ℝ 1 (Function.uncurry J) (z, u z))
    (hKs : ∀ z ∈ cappedDomain, ContDiffAt ℝ 2 (Function.uncurry Ks) (z, u z))
    (hKt : ∀ z ∈ cappedDomain, ContDiffAt ℝ 2 (Function.uncurry Kt) (z, u z))
    (hu : ∀ z ∈ cappedDomain, ContDiffAt ℝ 1 u z) {w : ℝ × ℝ → ℝ} (hw : ∀ z, 0 ≤ w z)
    (hwc : ContinuousOn w cappedDomain) {R₀ : ℝ} (hR₀ : 1 ≤ R₀) (e : Bool) {Ce Re : ℝ}
    (hRe : Re < R₀)
    (hend : ∀ ⦃η : ℝ × ℝ → V →L[ℝ] ℝ⦄, ContDiff ℝ 2 η → HasCompactSupport η →
      tsupport η ⊆ {z | z ∈ cappedDomain ∧ Re < cappedEndCoord c e z} →
      ∫ ζ in Ioi 2 ×ˢ Icc (0 : ℝ) 1,
          sobolevDensity (covectorPullback (cappedEndChart c e) J u η) ζ ≤
        Ce * ∫ z, w z * ‖ω.floerLinearizationAdjoint J Ks Kt u η z‖ ^ 2)
    {M B Λ : ℝ}
    (hM : ∀ z ∈ cappedCore c (R₀ + 1), ‖fderiv ℝ (cappedEndCutoff c R₀ e) z‖ ≤ M)
    (hB : ∀ z ∈ cappedCore c (R₀ + 1), ‖J z (u z)‖ ≤ B) (hΛ₀ : 0 ≤ Λ)
    (hΛ : ∀ z ∈ cappedCore c (R₀ + 1), w z ≤ Λ) {η : ℝ × ℝ → V →L[ℝ] ℝ}
    (hη : ContDiff ℝ 2 η) (hηc : HasCompactSupport η) (hηU : tsupport η ⊆ cappedDomain) :
    ∫ ζ in Ioi (R₀ + 1) ×ˢ Icc (0 : ℝ) 1,
        sobolevDensity (covectorPullback (cappedEndChart c e) J u η) ζ ≤
      max Ce 0 * (2 * (∫ z, w z * ‖ω.floerLinearizationAdjoint J Ks Kt u η z‖ ^ 2) +
        2 * (M * (1 + B)) ^ 2 * Λ * ∫ z in cappedCore c (R₀ + 1), ‖η z‖ ^ 2) := by
  have hβη : ContDiff ℝ 2 fun z ↦ cappedEndCutoff c R₀ e z • η z :=
    (ContinuousLinearMap.lsmul ℝ ℝ).contDiff_of_tsupport_subset_right
      (fun z hz ↦ (contDiffAt_cappedEndCutoff (by linarith) e hz).contDiffWithinAt)
      hη.contDiffOn isOpen_cappedDomain hηU
  have hD₀ : 0 ≤ ∫ z, w z * ‖ω.floerLinearizationAdjoint J Ks Kt u
      (fun z ↦ cappedEndCutoff c R₀ e z • η z) z‖ ^ 2 :=
    integral_nonneg fun z ↦ by have := hw z; positivity
  calc _ = ∫ ζ in Ioi (R₀ + 1) ×ˢ Icc (0 : ℝ) 1, sobolevDensity (covectorPullback
        (cappedEndChart c e) J u fun z ↦ cappedEndCutoff c R₀ e z • η z) ζ := by
        refine setIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Icc) fun ζ hζ ↦ ?_
        refine (sobolevDensity_congr_of_eventuallyEq ?_).symm
        filter_upwards [(isOpen_lt continuous_const continuous_fst).mem_nhds hζ.1] with ζ' hζ'
        rw [covectorPullback_fun_smul, cappedEndCutoff_eq_one
          (by rw [cappedEndCoord_cappedEndChart]; exact le_of_lt hζ'), one_smul]
    _ ≤ ∫ ζ in Ioi 2 ×ˢ Icc (0 : ℝ) 1, sobolevDensity (covectorPullback
        (cappedEndChart c e) J u fun z ↦ cappedEndCutoff c R₀ e z • η z) ζ :=
        setIntegral_mono_set (integrableOn_sobolevDensity_covectorPullback_cappedEndChart hJ hu
          (hβη.of_le one_le_two) (hηc.mono (support_smul_subset_right (cappedEndCutoff c R₀ e) η))
          ((tsupport_smul_subset_right _ _).trans hηU) e 2)
          (ae_of_all _ fun ζ ↦ sobolevDensity_nonneg _ ζ)
          (.of_forall fun _ hζ ↦ prod_mono (Ioi_subset_Ioi (by linarith)) subset_rfl hζ)
    _ ≤ Ce * ∫ z, w z * ‖ω.floerLinearizationAdjoint J Ks Kt u
          (fun z ↦ cappedEndCutoff c R₀ e z • η z) z‖ ^ 2 :=
        hend hβη (hηc.mono (support_smul_subset_right (cappedEndCutoff c R₀ e) η)) fun z hz ↦ by
          obtain ⟨hzU, hzR⟩ := tsupport_cappedEndCutoff_smul_subset (by linarith) hηU hz
          exact ⟨hzU, hRe.trans_le hzR⟩
    _ ≤ _ := (mul_le_mul_of_nonneg_right (le_max_left _ _) hD₀).trans
        (mul_le_mul_of_nonneg_left
          (ω.integral_mul_norm_floerLinearizationAdjoint_fun_smul_sq_le
          isOpen_cappedDomain hJ hKs hKt hu (isCompact_cappedCore c (R₀ + 1))
          (fun z hz ↦ contDiffAt_cappedEndCutoff (by linarith) e hz)
          (fun z _ ↦ abs_le.2 ⟨by linarith [cappedEndCutoff_nonneg (c := c) R₀ e z],
            cappedEndCutoff_le_one R₀ e z⟩)
          (fun z hz ↦ mem_cappedCore_of_fderiv_cappedEndCutoff_ne_zero hc₀ hc₁ (by linarith) hz)
          hM hB hw hwc hΛ₀ hΛ (hη.of_le one_le_two) hηc hηU) (le_max_right _ _))

/-- **The core estimate of the adjoint.** If `D^*` satisfies the `L²` estimate `hint` on covector
fields supported in `K = Σ_{R₀ + 1}`, and the weight `w`, positive on the capped surface,
satisfies `w⁻¹ ≤ Λ` on `K`, the energy of a covector field on `Σ_{R₀}` is controlled by the
`w`-weighted `L²` norm of `D^*` on the cut-off field `(1 - ∑_e β_e) η` and by the `L²` norm of
`η` on `K`. -/
private theorem setIntegral_sobolevDensity_le_of_cappedCoreCutoff (ω : SymplecticForm V)
    (hc₀ : 0 ≤ c) (hc₁ : c ≤ 1) {J : ℝ × ℝ → V → V →L[ℝ] V} {Ks Kt : ℝ × ℝ → V → ℝ}
    {u : ℝ × ℝ → V}
    (hJ : ∀ z ∈ cappedDomain, ContDiffAt ℝ 1 (Function.uncurry J) (z, u z))
    (hKs : ∀ z ∈ cappedDomain, ContDiffAt ℝ 2 (Function.uncurry Ks) (z, u z))
    (hKt : ∀ z ∈ cappedDomain, ContDiffAt ℝ 2 (Function.uncurry Kt) (z, u z))
    (hu : ∀ z ∈ cappedDomain, ContDiffAt ℝ 1 u z) {R₀ : ℝ} (hR₀ : 1 ≤ R₀) {C₀ : ℝ}
    (hC₀ : 0 ≤ C₀)
    (hint : ∀ ⦃η : ℝ × ℝ → V →L[ℝ] ℝ⦄, ContDiff ℝ 2 η → tsupport η ⊆ cappedCore c (R₀ + 1) →
      ∫ z in cappedCore c (R₀ + 1), sobolevDensity η z ≤
        C₀ * ∫ z in cappedCore c (R₀ + 1),
          (‖ω.floerLinearizationAdjoint J Ks Kt u η z‖ ^ 2 + ‖η z‖ ^ 2))
    {w : ℝ × ℝ → ℝ} (hw : ∀ z, 0 ≤ w z) (hwc : ContinuousOn w cappedDomain)
    (hwS : ∀ z ∈ cappedDomain, 0 < w z) {Λ : ℝ} (hΛ₀ : 0 ≤ Λ)
    (hΛ : ∀ z ∈ cappedCore c (R₀ + 1), (w z)⁻¹ ≤ Λ)
    {η : ℝ × ℝ → V →L[ℝ] ℝ} (hη : ContDiff ℝ 2 η) (hηU : tsupport η ⊆ cappedDomain) :
    ∫ z in cappedCore c R₀, sobolevDensity η z ≤
      C₀ * (Λ * (∫ z, w z * ‖ω.floerLinearizationAdjoint J Ks Kt u
          (fun w ↦ cappedCoreCutoff c R₀ w • η w) z‖ ^ 2) +
        ∫ z in cappedCore c (R₀ + 1), ‖η z‖ ^ 2) := by
  have hK : IsCompact (cappedCore c (R₀ + 1)) := isCompact_cappedCore c _
  have hKU : cappedCore c (R₀ + 1) ⊆ cappedDomain := cappedCore_subset c _
  have hηc' : ContDiff ℝ 2 fun w ↦ cappedCoreCutoff c R₀ w • η w :=
    (ContinuousLinearMap.lsmul ℝ ℝ).contDiff_of_tsupport_subset_right
      (fun z hz ↦ (contDiffAt_cappedCoreCutoff (by linarith) hz).contDiffWithinAt)
      hη.contDiffOn isOpen_cappedDomain hηU
  have hηcY : ∫ z in cappedCore c (R₀ + 1), ‖cappedCoreCutoff c R₀ z • η z‖ ^ 2 ≤
      ∫ z in cappedCore c (R₀ + 1), ‖η z‖ ^ 2 := by
    refine setIntegral_mono_on ((hηc'.continuous.norm.pow 2).continuousOn.integrableOn_compact hK)
      ((hη.continuous.norm.pow 2).continuousOn.integrableOn_compact hK) hK.measurableSet
      fun z _ ↦ ?_
    simp only [norm_smul, Real.norm_eq_abs]
    gcongr
    exact mul_le_of_le_one_left (norm_nonneg _)
      (abs_cappedCoreCutoff_le_one hc₀ hc₁ (by linarith) z)
  -- On `Σ_{R₀ + 1}`, where `w⁻¹ ≤ Λ`, we have `1 ≤ Λ w`.
  have hΛK (z : ℝ × ℝ) (hz : z ∈ cappedCore c (R₀ + 1)) : 1 ≤ Λ * w z := by
    have hρ := hwS z (hKU hz)
    rw [← inv_mul_cancel₀ hρ.ne']
    exact mul_le_mul_of_nonneg_right (hΛ z hz) hρ.le
  calc _ ≤ ∫ z in cappedCore c (R₀ + 1),
        sobolevDensity (fun w ↦ cappedCoreCutoff c R₀ w • η w) z :=
        setIntegral_sobolevDensity_le_setIntegral_sobolevDensity_smul
          (isCompact_cappedCore c R₀).measurableSet hK
          (cappedCore_mono c (by linarith : R₀ ≤ R₀ + 1))
          (fun z hz ↦ (contDiffAt_cappedCoreCutoff (by linarith) (cappedCore_subset c R₀ hz)
            (n := 1)).differentiableAt one_ne_zero)
          (fun z hz ↦ cappedCoreCutoff_eq_one_and_fderiv_eq_zero (by linarith) hz)
          (hη.differentiable two_ne_zero) (hηc'.of_le one_le_two)
    _ ≤ C₀ * (Λ * (∫ z, w z * ‖ω.floerLinearizationAdjoint J Ks Kt u
          (fun w ↦ cappedCoreCutoff c R₀ w • η w) z‖ ^ 2) +
          ∫ z in cappedCore c (R₀ + 1), ‖cappedCoreCutoff c R₀ z • η z‖ ^ 2) :=
        setIntegral_sobolevDensity_le_mul_integral_mul_norm_floerLinearizationAdjoint_add
          (θ := fun w ↦ cappedCoreCutoff c R₀ w • η w) (K := cappedCore c (R₀ + 1))
          (S := cappedDomain) ω isOpen_cappedDomain hJ hKs hKt hu hw hwc hK hΛ₀ hΛK hC₀ hint
          hηc' ((tsupport_smul_subset_right _ _).trans hηU)
          (tsupport_cappedCoreCutoff_smul_subset (R₀ := R₀) hc₀ hc₁ (by linarith) hηU)
    _ ≤ _ := by gcongr

/-! ### Patching -/

/-- **Patching at one height.** Under the hypotheses of
`exists_forall_sum_setIntegral_add_setIntegral_le_mul_integral_floerLinearizationAdjoint_of_capped`,
for every height `R₀ ≥ 1` above the heights `R e` of the end estimates, the energy of a covector
field beyond `R₀ + 1` on the ends and on the core `Σ_{R₀}` is controlled by the `w`-weighted norm
of `D_u^* η` and by `η` on `Σ_{R₀ + 1}`. -/
private theorem exists_forall_sum_setIntegral_add_setIntegral_le_of_capped_aux
    (ω : SymplecticForm V) (hc₀ : 0 ≤ c) (hc₁ : c ≤ 1)
    {J : ℝ × ℝ → V → AlmostComplexStructure V} {Ks Kt : ℝ × ℝ → V → ℝ} {u : ℝ × ℝ → V}
    (hJ : ∀ z ∈ cappedDomain, ContDiffAt ℝ 1
      (fun p : (ℝ × ℝ) × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap) (z, u z))
    (hKs : ∀ z ∈ cappedDomain, ContDiffAt ℝ 2 (uncurry Ks) (z, u z))
    (hKt : ∀ z ∈ cappedDomain, ContDiffAt ℝ 2 (uncurry Kt) (z, u z))
    (hu : ∀ z ∈ cappedDomain, ContDiffAt ℝ 1 u z)
    (hc : ∀ z ∈ cappedDomain, ω.Compatible (J z (u z))) {w : ℝ × ℝ → ℝ}
    (hw : ∀ z, 0 ≤ w z) (hwc : ContinuousOn w cappedDomain)
    (hwS : ∀ z ∈ cappedDomain, 0 < w z) {C R : Bool → ℝ}
    (hend : ∀ e ⦃η : ℝ × ℝ → V →L[ℝ] ℝ⦄, ContDiff ℝ 2 η → HasCompactSupport η →
      tsupport η ⊆ {z | z ∈ cappedDomain ∧ R e < cappedEndCoord c e z} →
      ∫ ζ in Ioi 2 ×ˢ Icc (0 : ℝ) 1, sobolevDensity (covectorPullback (cappedEndChart c e)
          (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) u η) ζ ≤
        C e * ∫ z, w z * ‖ω.floerLinearizationAdjoint
          (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) Ks Kt u η z‖ ^ 2)
    {R₀ : ℝ} (hR₀ : 1 ≤ R₀) (hR : ∀ e, R e < R₀) :
    ∃ C', 0 ≤ C' ∧ ∀ ⦃η : ℝ × ℝ → V →L[ℝ] ℝ⦄, ContDiff ℝ 2 η → HasCompactSupport η →
      tsupport η ⊆ cappedDomain →
      (∑ e, ∫ ζ in Ioi (R₀ + 1) ×ˢ Icc (0 : ℝ) 1, sobolevDensity (covectorPullback
          (cappedEndChart c e) (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) u η) ζ) +
          ∫ z in cappedCore c R₀, sobolevDensity η z ≤
        C' * ((∫ z, w z * ‖ω.floerLinearizationAdjoint
          (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) Ks Kt u η z‖ ^ 2) +
          ∫ z in cappedCore c (R₀ + 1), ‖η z‖ ^ 2) := by
  have hK : IsCompact (cappedCore c (R₀ + 1)) := isCompact_cappedCore c _
  have hKU : cappedCore c (R₀ + 1) ⊆ cappedDomain := cappedCore_subset c _
  set J' : ℝ × ℝ → V → V →L[ℝ] V := fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap
  -- Bounds on the core for `J` along `u`, for the derivatives of the cutoffs, and for `w`, `w⁻¹`.
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn (f := fun z ↦ J' z (u z))
    fun z hz ↦ ((hJ z (hKU hz)).continuousAt.comp₂ continuousAt_id
      (hu z (hKU hz)).continuousAt).continuousWithinAt
  obtain ⟨M, hMe, hMc⟩ := hK.exists_forall_norm_fderiv_le
    (fun e z hz ↦ contDiffAt_cappedEndCutoff (by linarith) e (hKU hz))
    fun z hz ↦ fderiv_cappedCoreCutoff (by linarith) (hKU hz)
  obtain ⟨Λ, hΛ₀, hΛ⟩ := hK.exists_forall_le_and_inv_le (hwc.mono hKU) fun z hz ↦ hwS z (hKU hz)
  -- The estimate on the compact core.
  obtain ⟨C₀, hC₀, hint⟩ :=
    ω.exists_forall_setIntegral_sobolevDensity_le_mul_setIntegral_floerLinearizationAdjoint_add hK
      (fun z hz ↦ hJ z (hKU hz)) (fun z hz ↦ hKs z (hKU hz)) (fun z hz ↦ hKt z (hKU hz))
      (fun z hz ↦ hu z (hKU hz)) (fun z hz ↦ hc z (hKU hz))
  set c' := M * (1 + B)
  set Cs := ∑ e, max (C e) 0
  refine ⟨Cs * (2 + 2 * c' ^ 2 * Λ) + C₀ * Λ * (2 + 2 * c' ^ 2 * Λ) + C₀, by positivity,
    fun η hη hηc hηU ↦ ?_⟩
  set X := ∫ z, w z * ‖ω.floerLinearizationAdjoint J' Ks Kt u η z‖ ^ 2
  set Y := ∫ z in cappedCore c (R₀ + 1), ‖η z‖ ^ 2
  have hX : 0 ≤ X := integral_nonneg fun z ↦ by have := hw z; positivity
  have hY : 0 ≤ Y := setIntegral_nonneg hK.measurableSet fun _ _ ↦ sq_nonneg _
  have hE : 2 * X + 2 * c' ^ 2 * Λ * Y ≤ (2 + 2 * c' ^ 2 * Λ) * (X + Y) := by
    nlinarith [mul_nonneg (mul_nonneg (sq_nonneg c') hΛ₀) hX]
  -- The ends and the core, through their cutoffs.
  have hends (e : Bool) := ω.setIntegral_sobolevDensity_covectorPullback_le_of_cappedEndCutoff
    hc₀ hc₁ (J := J') hJ hKs hKt hu hw hwc hR₀ e (hR e) (hend e) (hMe e) hB hΛ₀
    (fun z hz ↦ (hΛ z hz).1) hη hηc hηU
  have hcore : ∫ z in cappedCore c R₀, sobolevDensity η z ≤
      C₀ * (Λ * (2 * X + 2 * c' ^ 2 * Λ * Y) + Y) :=
    (ω.setIntegral_sobolevDensity_le_of_cappedCoreCutoff hc₀ hc₁ (J := J') hJ hKs hKt hu hR₀ hC₀
      hint hw hwc hwS hΛ₀ (fun z hz ↦ (hΛ z hz).2) hη hηU).trans (by
      gcongr
      exact ω.integral_mul_norm_floerLinearizationAdjoint_fun_smul_sq_le
        (J := J') isOpen_cappedDomain hJ hKs hKt hu hK
        (fun z hz ↦ contDiffAt_cappedCoreCutoff (by linarith) hz)
        (fun z _ ↦ abs_cappedCoreCutoff_le_one hc₀ hc₁ (by linarith) z)
        (fun z hz ↦ mem_cappedCore_of_fderiv_cappedCoreCutoff_ne_zero hc₀ hc₁ (by linarith) hz)
        hMc hB hw hwc hΛ₀ (fun z hz ↦ (hΛ z hz).1) (hη.of_le one_le_two) hηc hηU)
  -- Summing the pieces.
  refine (add_le_add (Finset.sum_le_sum fun e (_ : e ∈ Finset.univ) ↦ hends e) hcore).trans ?_
  rw [← Finset.sum_mul]
  have h₁ := mul_le_mul_of_nonneg_left hE (by positivity : 0 ≤ Cs)
  have h₂ := mul_le_mul_of_nonneg_left hE (mul_nonneg hC₀ hΛ₀)
  nlinarith [mul_nonneg hC₀ hX]

/-- **Patching end estimates into the semi-Fredholm estimate of the formal adjoint on the pair of
pants capped at `0`.** Let `0 ≤ c ≤ 1`. Let `J(z)` be compatible along `u` on the capped surface
`ℂ ∖ {1}`, with `J` `C¹` and `K_s`, `K_t` `C²` at the points `(z, u z)`, and `u` `C¹` there, and let
`w ≥ 0` be a weight that is continuous and positive on `ℂ ∖ {1}`. Suppose that on the two ends
the formal adjoint `D_u^*` of the linearized Floer operator controls the energy of covector fields
in the chart of the end: on the input end at `1`, read in the positive end chart `φ'_1`, every
`C²` covector field `η` with compact support in the part `s > R_in` of the end satisfies
`∫_{(2, ∞) × [0, 1]} (‖∂s η'‖² + ‖∂t η'‖² + ‖η'‖²) ≤ C_in ∫ w ‖D_u^* η‖²`, where
`η' = η (φ'_1 ·) ∘ (a + b J)` is `η` read in the chart (`TauCeti.Floer.covectorPullback`), and
likewise on the output end in the chart `c + φ'_∞` beyond `R_out`, with the constant `C_out`.
Then there are `C ≥ 0` and `T ≥ 1` such that every `C²` covector field `η` with compact support in
`ℂ ∖ {1}` satisfies

`∑_{e} ∫_{(T, ∞) × [0, 1]} (‖∂s η'_e‖² + ‖∂t η'_e‖² + ‖η'_e‖²)`
`  + ∫_{Σ_T} (‖∂s η‖² + ‖∂t η‖² + ‖η‖²) ≤ C (∫ w ‖D_u^* η‖² + ∫_{Σ_{T + 1}} ‖η‖²)`,

where `η'_e` is `η` read in the chart of the end `e` and `Σ_T` is the annulus
`exp (-2πT) / 2 ≤ |w - 1|`, `|w - c| ≤ 2 exp (2πT)` bounded by the circles `s = T` of the two
ends. -/
theorem
  exists_forall_sum_setIntegral_add_setIntegral_le_mul_integral_floerLinearizationAdjoint_of_capped
    (ω : SymplecticForm V) (hc₀ : 0 ≤ c) (hc₁ : c ≤ 1)
    {J : ℝ × ℝ → V → AlmostComplexStructure V} {Ks Kt : ℝ × ℝ → V → ℝ} {u : ℝ × ℝ → V}
    (hJ : ∀ z, Complex.equivRealProdCLM.symm z ≠ 1 → ContDiffAt ℝ 1
      (fun p : (ℝ × ℝ) × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap) (z, u z))
    (hKs : ∀ z, Complex.equivRealProdCLM.symm z ≠ 1 → ContDiffAt ℝ 2 (uncurry Ks) (z, u z))
    (hKt : ∀ z, Complex.equivRealProdCLM.symm z ≠ 1 → ContDiffAt ℝ 2 (uncurry Kt) (z, u z))
    (hu : ∀ z, Complex.equivRealProdCLM.symm z ≠ 1 → ContDiffAt ℝ 1 u z)
    (hc : ∀ z, Complex.equivRealProdCLM.symm z ≠ 1 → ω.Compatible (J z (u z)))
    {w : ℝ × ℝ → ℝ} (hw : ∀ z, 0 ≤ w z)
    (hwc : ContinuousOn w {z | Complex.equivRealProdCLM.symm z ≠ 1})
    (hwS : ∀ z, Complex.equivRealProdCLM.symm z ≠ 1 → 0 < w z) {Cin Rin Cout Rout : ℝ}
    (hendIn : ∀ ⦃η : ℝ × ℝ → V →L[ℝ] ℝ⦄, ContDiff ℝ 2 η → HasCompactSupport η →
      tsupport η ⊆
        {z | Complex.equivRealProdCLM.symm z ≠ 1 ∧ Rin < (positiveEndCoord one z).1} →
      ∫ ζ in Ioi 2 ×ˢ Icc (0 : ℝ) 1, sobolevDensity (covectorPullback (positiveEndChart one)
          (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) u η) ζ ≤
        Cin * ∫ z, w z * ‖ω.floerLinearizationAdjoint
          (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) Ks Kt u η z‖ ^ 2)
    (hendOut : ∀ ⦃η : ℝ × ℝ → V →L[ℝ] ℝ⦄, ContDiff ℝ 2 η → HasCompactSupport η →
      tsupport η ⊆ {z | Complex.equivRealProdCLM.symm z ≠ 1 ∧
        Rout < (positiveEndCoord inf (z - (c, 0))).1} →
      ∫ ζ in Ioi 2 ×ˢ Icc (0 : ℝ) 1, sobolevDensity
          (covectorPullback (fun ζ ↦ positiveEndChart inf ζ + (c, 0))
            (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) u η) ζ ≤
        Cout * ∫ z, w z * ‖ω.floerLinearizationAdjoint
          (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) Ks Kt u η z‖ ^ 2) :
    ∃ C, 0 ≤ C ∧ ∃ T, 1 ≤ T ∧ ∀ ⦃η : ℝ × ℝ → V →L[ℝ] ℝ⦄, ContDiff ℝ 2 η →
      HasCompactSupport η → tsupport η ⊆ {z | Complex.equivRealProdCLM.symm z ≠ 1} →
      (∫ ζ in Ioi T ×ˢ Icc (0 : ℝ) 1, sobolevDensity (covectorPullback (positiveEndChart one)
          (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) u η) ζ) +
        (∫ ζ in Ioi T ×ˢ Icc (0 : ℝ) 1, sobolevDensity
          (covectorPullback (fun ζ ↦ positiveEndChart inf ζ + (c, 0))
            (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) u η) ζ) +
        ∫ z in {z | Real.exp (-(2 * π * T)) / 2 ≤ ‖Complex.equivRealProdCLM.symm z - 1‖ ∧
          ‖Complex.equivRealProdCLM.symm z - c‖ ≤ 2 * Real.exp (2 * π * T)},
          sobolevDensity η z ≤
        C * ((∫ z, w z * ‖ω.floerLinearizationAdjoint
          (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) Ks Kt u η z‖ ^ 2) +
          ∫ z in {z | Real.exp (-(2 * π * (T + 1))) / 2 ≤ ‖Complex.equivRealProdCLM.symm z - 1‖ ∧
            ‖Complex.equivRealProdCLM.symm z - c‖ ≤ 2 * Real.exp (2 * π * (T + 1))},
            ‖η z‖ ^ 2) := by
  -- Index the ends by `Bool`, with `true` the input end at `1`. Membership in `cappedDomain` is
  -- by definition `Complex.equivRealProdCLM.symm z ≠ 1` (`mem_cappedDomain`), so the hypotheses
  -- on the capped surface apply as stated.
  let Ce : Bool → ℝ := fun e ↦ if e then Cin else Cout
  let Re : Bool → ℝ := fun e ↦ if e then Rin else Rout
  have hend (e : Bool) ⦃η : ℝ × ℝ → V →L[ℝ] ℝ⦄ (hη : ContDiff ℝ 2 η)
      (hηc : HasCompactSupport η)
      (hηR : tsupport η ⊆ {z | z ∈ cappedDomain ∧ Re e < cappedEndCoord c e z}) :
      ∫ ζ in Ioi 2 ×ˢ Icc (0 : ℝ) 1, sobolevDensity (covectorPullback (cappedEndChart c e)
          (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) u η) ζ ≤
        Ce e * ∫ z, w z * ‖ω.floerLinearizationAdjoint
          (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) Ks Kt u η z‖ ^ 2 := by
    cases e
    · simpa only [Ce, cappedEndChart, Bool.false_eq_true, ↓reduceIte] using hendOut hη hηc
        (by simpa only [Re, mem_cappedDomain, cappedEndCoord, Bool.false_eq_true, ↓reduceIte]
          using hηR)
    · simpa only [Ce, cappedEndChart, ↓reduceIte] using hendIn hη hηc
        (by simpa only [Re, mem_cappedDomain, cappedEndCoord, ↓reduceIte] using hηR)
  obtain ⟨C', hC', T, hT, hest⟩ := exists_forall_sum_setIntegral_add_setIntegral_le_of_forall_le
    (K := cappedCore c) (isCompact_cappedCore c) (cappedCore_mono c) (r := 1)
    (S := cappedDomain) (R := Re)
    (G := fun e η ↦ covectorPullback (cappedEndChart c e)
      (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) u η) fun _ hR₀ hR ↦
      ω.exists_forall_sum_setIntegral_add_setIntegral_le_of_capped_aux hc₀ hc₁ hJ hKs hKt hu hc
        hw hwc hwS hend hR₀ hR
  refine ⟨C', hC', T, hT, fun η hη hηc hηU ↦ ?_⟩
  simpa only [Fintype.sum_bool, cappedEndChart, cappedCore] using hest hη hηc hηU

end TauCeti.SymplecticForm
