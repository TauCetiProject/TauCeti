/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.Compact.Estimate
public import TauCeti.Analysis.Sobolev.Cylinder
public import TauCeti.Geometry.Symplectic.Floer.SemiFredholm
import TauCeti.Topology.Instances.Real.TSupport

/-!
# The Sobolev realization of the linearized Floer operator on a cylinder

Let `(V, ω)` be a finite-dimensional symplectic vector space and `D_u` the linearized Floer operator
(`TauCeti.SymplecticForm.floerLinearization`) along a map `u : ℝ × ℝ → V` of period one in `t`.
This file realizes `D_u` as a bounded operator `W^{1,2}(ℝ × S¹, V) → L²(ℝ × S¹, V)` between the
Sobolev spaces of the cylinder of `TauCeti.Analysis.Sobolev.Cylinder`, and proves that along a
Floer trajectory between nondegenerate orbits it is semi-Fredholm: its kernel is finite
dimensional and its range is closed. This is the functional-analytic form of the semi-Fredholm
estimate of `TauCeti.Geometry.Symplectic.Floer.SemiFredholm`, and the starting point of the
Fredholm theory of Floer cylinders.

* `TauCeti.SymplecticForm.floerLinearizationLp`: `D_u` on the test sections of the cylinder, with
  values in `L²` of the fundamental domain `ℝ × [0, 1]`. On a test section it is square integrable
  as soon as `u` is `C¹` and the data are regular along `u`
  (`TauCeti.SymplecticForm.memLp_floerLinearization`).
* `TauCeti.SymplecticForm.norm_floerLinearizationLp_le`: if `J(z, u z)` and the zeroth-order
  coefficient of `D_u` are bounded by `M` on `ℝ × [0, 1]`, then
  `‖D_u ξ‖_{L²} ≤ (1 + 2 M) ‖ξ‖_{W^{1,2}}`.
* `TauCeti.SymplecticForm.floerSobolevOperator`: the continuous extension of `D_u` to
  `W^{1,2}`, which is `D_u` on test sections when `D_u` is bounded
  (`TauCeti.SymplecticForm.floerSobolevOperator_toW12`).
* `finiteDimensional_ker_and_isClosed_range_floerSobolevOperator_of_estimate` (in the namespace
  `TauCeti.SymplecticForm`): if `D_u` is bounded and satisfies the semi-Fredholm estimate
  `‖ξ‖²_{W^{1,2}} ≤ C (‖D_u ξ‖²_{L²} + ‖ξ‖²_{L²([-T, T] × S¹)})` on test sections, then its Sobolev
  realization has finite dimensional kernel and closed range. The estimate extends from the dense
  test sections to `W^{1,2}`, and restriction to `[-T, T] × S¹` is compact
  (`TauCeti.CylinderSobolev.isCompactOperator_restrictValue`), so Peetre's compact-error argument
  (`ContinuousLinearMap.finiteDimensional_ker_of_compact_estimate`,
  `ContinuousLinearMap.isClosed_range_of_compact_estimate`) applies.
* `TauCeti.SymplecticForm.finiteDimensional_ker_and_isClosed_range_floerSobolevOperator`: along
  a Floer trajectory `u` from a nondegenerate orbit `xm` to a nondegenerate orbit `xp`, for the
  datum `K = H_t dt` and `J_t` compatible along `u`, the Sobolev realization of `D_u` has finite
  dimensional kernel and closed range. The loops of `u` and its slice defect `∂t u - X_{H_t}(u)`
  converge uniformly at both ends, so `u` and the slice defect are bounded on `ℝ × [0, 1]`, which
  bounds the coefficients of `D_u` there; the semi-Fredholm estimate is
  `TauCeti.SymplecticForm.exists_forall_setIntegral_le_mul_setIntegral_floerLinearization_add`.

The cokernel, and hence the Fredholm property and the index of `D_u`, are not treated here: they
need the corresponding estimate for the formal adjoint of `D_u`.

## References

* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 2, on the Fredholm property of `∂s + J ∂t + S(s, t)` along a Floer
  trajectory.
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, 2nd ed., Section 3.1
  and Appendix A.1, on semi-Fredholm estimates with a compact error.
-/

public section

noncomputable section

open Filter Set Function MeasureTheory Topology ContinuousLinearMap
open TauCeti.CylinderSobolev
open scoped NNReal ENNReal Manifold

namespace TauCeti.SymplecticForm

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- The linearized Floer operator along `u` vanishes near every point with `s ∉ [a, b]` on a map
which vanishes for `s ∉ (a, b)`. -/
private theorem floerLinearization_eq_zero_of_fst_notMem_Icc (ω : SymplecticForm V)
    (J : ℝ × ℝ → V → V →L[ℝ] V) (Ks Kt : ℝ × ℝ → V → ℝ) (u : ℝ × ℝ → V) {ξ : ℝ × ℝ → V}
    {a b : ℝ} (hξ : ∀ s t, s ∉ Ioo a b → ξ (s, t) = 0) {z : ℝ × ℝ} (hz : z.1 ∉ Icc a b) :
    ω.floerLinearization J Ks Kt u ξ z = 0 := by
  rw [ω.floerLinearization_congr_of_eventuallyEq J Ks Kt u
    (eventuallyEq_zero_of_forall_notMem_Ioo_of_fst_notMem_Icc hξ hz), floerLinearization_zero]

/-- On test sections, the linearized Floer operator is square integrable over the fundamental
domain `ℝ × [0, 1]` when `u` is `C¹` and the data are regular along `u`. -/
theorem memLp_floerLinearization (ω : SymplecticForm V)
    {J : ℝ × ℝ → V → V →L[ℝ] V} {Ks Kt : ℝ × ℝ → V → ℝ} {u : ℝ × ℝ → V}
    (hJ : ∀ z, ContDiffAt ℝ 1 (Function.uncurry J) (z, u z))
    (hKs : ∀ z, ContDiffAt ℝ 2 (Function.uncurry Ks) (z, u z))
    (hKt : ∀ z, ContDiffAt ℝ 2 (Function.uncurry Kt) (z, u z)) (hu : ContDiff ℝ 1 u)
    {ξ : ℝ × ℝ → V} (hξ : ξ ∈ testSections V) :
    MemLp (ω.floerLinearization J Ks Kt u ξ) 2 (stripMeasure) := by
  obtain ⟨a, b, hab⟩ := exists_forall_notMem_Ioo_of_mem_testSections hξ
  refine memLp_stripMeasure (ω.continuous_floerLinearization hJ hKs hKt hu
    ((contDiff_of_mem_testSections hξ).of_le (by norm_num))) (a := a - 1) (b := b + 1)
    (fun s t hs ↦ ω.floerLinearization_eq_zero_of_fst_notMem_Icc J Ks Kt u hab fun h ↦
      hs ⟨by linarith [h.1], by linarith [h.2]⟩) 2

/-- **The linearized Floer operator on test sections**, as a linear map into `L²` of the
fundamental domain `ℝ × [0, 1]`. The hypothesis `hD` is supplied by
`TauCeti.SymplecticForm.memLp_floerLinearization`. -/
def floerLinearizationLp (ω : SymplecticForm V) (J : ℝ × ℝ → V → V →L[ℝ] V)
    (Ks Kt : ℝ × ℝ → V → ℝ) (u : ℝ × ℝ → V)
    (hD : ∀ ξ ∈ testSections V, MemLp (ω.floerLinearization J Ks Kt u ξ) 2 (stripMeasure)) :
    testSections V →ₗ[ℝ] Lp V 2 (stripMeasure) where
  toFun ξ := (hD ξ ξ.2).toLp _
  map_add' ξ η := by
    have hξ := (contDiff_of_mem_testSections ξ.2).differentiable two_ne_zero
    have hη := (contDiff_of_mem_testSections η.2).differentiable two_ne_zero
    rw [← MemLp.toLp_add]
    exact MemLp.toLp_congr _ _ (Eventually.of_forall fun z ↦
      ω.floerLinearization_add J Ks Kt u _ _ z (hξ z) (hη z))
  map_smul' c ξ := by
    rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
    exact MemLp.toLp_congr _ _ (Eventually.of_forall fun z ↦
      ω.floerLinearization_smul J Ks Kt u _ z c)

theorem floerLinearizationLp_apply (ω : SymplecticForm V) (J : ℝ × ℝ → V → V →L[ℝ] V)
    (Ks Kt : ℝ × ℝ → V → ℝ) (u : ℝ × ℝ → V)
    (hD : ∀ ξ ∈ testSections V, MemLp (ω.floerLinearization J Ks Kt u ξ) 2 (stripMeasure))
    (ξ : testSections V) :
    ω.floerLinearizationLp J Ks Kt u hD ξ = (hD ξ ξ.2).toLp _ :=
  (rfl)

/-- **The `L²` norm of the linearized Floer operator on a test section.** -/
theorem norm_floerLinearizationLp_sq (ω : SymplecticForm V) (J : ℝ × ℝ → V → V →L[ℝ] V)
    (Ks Kt : ℝ × ℝ → V → ℝ) (u : ℝ × ℝ → V)
    (hD : ∀ ξ ∈ testSections V, MemLp (ω.floerLinearization J Ks Kt u ξ) 2 (stripMeasure))
    (ξ : testSections V) :
    ‖ω.floerLinearizationLp J Ks Kt u hD ξ‖ ^ 2 =
      ∫ z in univ ×ˢ Icc (0 : ℝ) 1, ‖ω.floerLinearization J Ks Kt u ξ z‖ ^ 2 := by
  rw [floerLinearizationLp_apply, MemLp.norm_toLp_sq]

/-- **The `L²` bound of the linearized Floer operator by the `W^{1,2}` norm.** If `J(z, u z)` and
the zeroth-order coefficient of `D_u` (`TauCeti.SymplecticForm.floerLinearizationCoeff`) are
bounded by `M` on `ℝ × [0, 1]`, then `‖D_u ξ‖_{L²} ≤ (1 + 2 M) ‖ξ‖_{W^{1,2}}` for every test
section `ξ`. -/
theorem norm_floerLinearizationLp_le (ω : SymplecticForm V) (J : ℝ × ℝ → V → V →L[ℝ] V)
    (Ks Kt : ℝ × ℝ → V → ℝ) (u : ℝ × ℝ → V)
    (hD : ∀ ξ ∈ testSections V, MemLp (ω.floerLinearization J Ks Kt u ξ) 2 (stripMeasure))
    {M : ℝ} (hJM : ∀ z ∈ univ ×ˢ Icc (0 : ℝ) 1, ‖J z (u z)‖ ≤ M)
    (hAM : ∀ z ∈ univ ×ˢ Icc (0 : ℝ) 1, ‖ω.floerLinearizationCoeff J Ks Kt u z‖ ≤ M)
    (ξ : testSections V) :
    ‖ω.floerLinearizationLp J Ks Kt u hD ξ‖ ≤ (1 + 2 * M) * ‖toW12 V ξ‖ := by
  rw [← Submodule.norm_coe, coe_toW12]
  refine Lp.norm_le_mul_norm_of_ae_le_mul ?_
  filter_upwards [(hD ξ ξ.2).coeFn_toLp, coeFn_jetLp ξ,
    ae_restrict_mem (MeasurableSet.univ.prod measurableSet_Icc)] with z hz hz' hzS
  rw [floerLinearizationLp_apply, hz, hz', ω.floerLinearization_eq_add]
  set j := ‖jet (ξ : ℝ × ℝ → V) z‖
  have h₁ : ‖fderiv ℝ (ξ : ℝ × ℝ → V) z stdComplexLineReal‖ ≤ j :=
    norm_fderiv_apply_one_zero_le_norm_jet (ξ : ℝ × ℝ → V) z
  have h₂ : ‖fderiv ℝ (ξ : ℝ × ℝ → V) z stdComplexLineImag‖ ≤ j :=
    norm_fderiv_apply_zero_one_le_norm_jet (ξ : ℝ × ℝ → V) z
  have h₀ : ‖(ξ : ℝ × ℝ → V) z‖ ≤ j := norm_le_norm_jet (ξ : ℝ × ℝ → V) z
  have hM : 0 ≤ M := (norm_nonneg _).trans (hJM z hzS)
  calc ‖fderiv ℝ (ξ : ℝ × ℝ → V) z stdComplexLineReal +
        J z (u z) (fderiv ℝ (ξ : ℝ × ℝ → V) z stdComplexLineImag) +
        ω.floerLinearizationCoeff J Ks Kt u z ((ξ : ℝ × ℝ → V) z)‖
      ≤ ‖fderiv ℝ (ξ : ℝ × ℝ → V) z stdComplexLineReal‖ +
          ‖J z (u z)‖ * ‖fderiv ℝ (ξ : ℝ × ℝ → V) z stdComplexLineImag‖ +
          ‖ω.floerLinearizationCoeff J Ks Kt u z‖ * ‖(ξ : ℝ × ℝ → V) z‖ :=
        (norm_add₃_le).trans (by gcongr <;> exact le_opNorm _ _)
    _ ≤ j + M * j + M * j := by
        gcongr
        exacts [hJM z hzS, hAM z hzS]
    _ = (1 + 2 * M) * j := by ring


/-- **The Sobolev realization of the linearized Floer operator** `D_u : W^{1,2} → L²` on the
cylinder: the continuous extension of `D_u` from the test sections to
`TauCeti.CylinderSobolev.W12 V`. When `D_u` is bounded in the `W^{1,2}` norm on test sections, it
agrees with `D_u` there (`TauCeti.SymplecticForm.floerSobolevOperator_toW12`). -/
def floerSobolevOperator (ω : SymplecticForm V) (J : ℝ × ℝ → V → V →L[ℝ] V)
    (Ks Kt : ℝ × ℝ → V → ℝ) (u : ℝ × ℝ → V)
    (hD : ∀ ξ ∈ testSections V, MemLp (ω.floerLinearization J Ks Kt u ξ) 2 (stripMeasure)) :
    W12 V →L[ℝ] Lp V 2 (stripMeasure) :=
  (ω.floerLinearizationLp J Ks Kt u hD).extendOfNorm (toW12 V)

/-- On a test section, the Sobolev realization of `D_u` is `D_u`, provided `D_u` is bounded in the
`W^{1,2}` norm (as given by `TauCeti.SymplecticForm.norm_floerLinearizationLp_le`). -/
theorem floerSobolevOperator_toW12 (ω : SymplecticForm V) (J : ℝ × ℝ → V → V →L[ℝ] V)
    (Ks Kt : ℝ × ℝ → V → ℝ) (u : ℝ × ℝ → V)
    (hD : ∀ ξ ∈ testSections V, MemLp (ω.floerLinearization J Ks Kt u ξ) 2 (stripMeasure))
    {M : ℝ} (hM : ∀ ξ, ‖ω.floerLinearizationLp J Ks Kt u hD ξ‖ ≤ M * ‖toW12 V ξ‖)
    (ξ : testSections V) :
    ω.floerSobolevOperator J Ks Kt u hD (toW12 V ξ) = ω.floerLinearizationLp J Ks Kt u hD ξ :=
  LinearMap.extendOfNorm_eq denseRange_toW12 ⟨M, hM⟩ ξ

/-- **The Sobolev realization of `D_u` is semi-Fredholm under the semi-Fredholm estimate.** If
`D_u` is bounded in the `W^{1,2}` norm on test sections, and satisfies the estimate

`‖ξ‖²_{W^{1,2}} ≤ C (‖D_u ξ‖²_{L²} + ‖ξ‖²_{L²([-T, T] × [0, 1])})`

on test sections, then its Sobolev realization has finite dimensional kernel and closed range.
The restriction to `[-T, T] × [0, 1]` is compact
(`TauCeti.CylinderSobolev.isCompactOperator_restrictValue`), so this is Peetre's compact-error
argument (`ContinuousLinearMap.finiteDimensional_ker_of_compact_estimate`,
`ContinuousLinearMap.isClosed_range_of_compact_estimate`). -/
theorem finiteDimensional_ker_and_isClosed_range_floerSobolevOperator_of_estimate
    (ω : SymplecticForm V) (J : ℝ × ℝ → V → V →L[ℝ] V) (Ks Kt : ℝ × ℝ → V → ℝ) (u : ℝ × ℝ → V)
    (hD : ∀ ξ ∈ testSections V, MemLp (ω.floerLinearization J Ks Kt u ξ) 2 (stripMeasure))
    {M : ℝ} (hM : ∀ ξ, ‖ω.floerLinearizationLp J Ks Kt u hD ξ‖ ≤ M * ‖toW12 V ξ‖) {C T : ℝ}
    (hest : ∀ ξ : testSections V, ‖toW12 V ξ‖ ^ 2 ≤
      C * (‖ω.floerLinearizationLp J Ks Kt u hD ξ‖ ^ 2 + ‖restrictValue V T (toW12 V ξ)‖ ^ 2)) :
    FiniteDimensional ℝ (ω.floerSobolevOperator J Ks Kt u hD).ker ∧
      IsClosed ((ω.floerSobolevOperator J Ks Kt u hD).range : Set (Lp V 2 (stripMeasure))) := by
  set D := ω.floerSobolevOperator J Ks Kt u hD
  set c := √(max C 0)
  have hc : c ^ 2 = max C 0 := Real.sq_sqrt (le_max_right _ _)
  -- The estimate on the dense subspace of test sections, and then on all of `W^{1,2}`.
  have hbound (x : W12 V) : ‖x‖ ≤ c * ‖D x‖ + ‖(c • restrictValue V T) x‖ := by
    refine denseRange_toW12.induction_on x (isClosed_le (by fun_prop) (by fun_prop)) fun ξ ↦ ?_
    rw [ω.floerSobolevOperator_toW12 J Ks Kt u hD hM, smul_apply, norm_smul,
      Real.norm_of_nonneg (Real.sqrt_nonneg _), ← mul_add]
    set a := ‖ω.floerLinearizationLp J Ks Kt u hD ξ‖
    set b := ‖restrictValue V T (toW12 V ξ)‖
    have ha : 0 ≤ a := norm_nonneg _
    have hb : 0 ≤ b := norm_nonneg _
    have hsq : ‖toW12 V ξ‖ ^ 2 ≤ (c * (a + b)) ^ 2 := by
      rw [mul_pow, hc]
      calc ‖toW12 V ξ‖ ^ 2 ≤ C * (a ^ 2 + b ^ 2) := hest ξ
        _ ≤ max C 0 * (a ^ 2 + b ^ 2) := by gcongr; exact le_max_left _ _
        _ ≤ max C 0 * (a + b) ^ 2 := by gcongr; nlinarith
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 hsq
  have hK : IsCompactOperator (c • restrictValue V T) :=
    (isCompactOperator_restrictValue T).smul c
  exact ⟨D.finiteDimensional_ker_of_compact_estimate hK hbound,
    D.isClosed_range_of_compact_estimate hK hbound⟩


/-- A continuous map on the strip `ℝ × [0, 1]` whose slices converge uniformly at both ends to
maps bounded on `[0, 1]` is bounded on the strip. -/
private theorem exists_forall_norm_le_of_tendstoUniformlyOn {E : Type*} [NormedAddCommGroup E]
    {f : ℝ × ℝ → E} (hf : Continuous f) {gm gp : ℝ → E} {Bm Bp : ℝ}
    (hgm : ∀ t ∈ Icc (0 : ℝ) 1, ‖gm t‖ ≤ Bm) (hgp : ∀ t ∈ Icc (0 : ℝ) 1, ‖gp t‖ ≤ Bp)
    (hm : TendstoUniformlyOn (fun s t ↦ f (s, t)) gm atBot (Icc 0 1))
    (hp : TendstoUniformlyOn (fun s t ↦ f (s, t)) gp atTop (Icc 0 1)) :
    ∃ B, ∀ z ∈ univ ×ˢ Icc (0 : ℝ) 1, ‖f z‖ ≤ B := by
  obtain ⟨Rp, hRp⟩ := eventually_atTop.1 (Metric.tendstoUniformlyOn_iff.1 hp 1 one_pos)
  obtain ⟨Rm, hRm⟩ := eventually_atBot.1 (Metric.tendstoUniformlyOn_iff.1 hm 1 one_pos)
  have hK : IsCompact (Icc Rm Rp ×ˢ Icc (0 : ℝ) 1) := isCompact_Icc.prod isCompact_Icc
  obtain ⟨B₀, hB₀⟩ := hK.exists_bound_of_continuousOn hf.continuousOn
  refine ⟨max (max (Bm + 1) (Bp + 1)) B₀, ?_⟩
  rintro ⟨s, t⟩ ⟨-, ht⟩
  by_cases hs₁ : Rp ≤ s
  · have h := hRp s hs₁ t ht
    rw [dist_eq_norm'] at h
    calc ‖f (s, t)‖ ≤ ‖gp t‖ + ‖f (s, t) - gp t‖ := norm_le_insert' _ _
      _ ≤ Bp + 1 := add_le_add (hgp t ht) h.le
      _ ≤ _ := (le_max_right _ _).trans (le_max_left _ _)
  by_cases hs₂ : s ≤ Rm
  · have h := hRm s hs₂ t ht
    rw [dist_eq_norm'] at h
    calc ‖f (s, t)‖ ≤ ‖gm t‖ + ‖f (s, t) - gm t‖ := norm_le_insert' _ _
      _ ≤ Bm + 1 := add_le_add (hgm t ht) h.le
      _ ≤ _ := (le_max_left _ _).trans (le_max_left _ _)
  · exact (hB₀ (s, t) ⟨⟨(not_le.1 hs₂).le, (not_le.1 hs₁).le⟩, ht⟩).trans (le_max_right _ _)

/-- A continuous loop is bounded on `[0, 1]`. -/
private theorem exists_forall_norm_le_of_continuous {E : Type*} [NormedAddCommGroup E] {x : ℝ → E}
    (hx : Continuous x) : ∃ B, ∀ t ∈ Icc (0 : ℝ) 1, ‖x t‖ ≤ B :=
  isCompact_Icc.exists_bound_of_continuousOn hx.continuousOn

/-- The zeroth-order coefficient of `D_u` for the datum `K = H_t dt` at `z` is bounded by
`‖∂_y J‖ ‖∂t u - X_{H_t}(u)‖ + ‖J‖ ‖∂_y X_{H_t}‖` at `(t, u z)`. -/
private theorem norm_floerLinearizationCoeff_le (ω : SymplecticForm V)
    {H : ℝ → V → ℝ} {J : ℝ → V → AlmostComplexStructure V} {u : ℝ × ℝ → V} {z : ℝ × ℝ}
    {B₁ B₂ B₃ Bδ : ℝ}
    (e₁ : ‖(J z.2 (u z)).toLinearMap.toContinuousLinearMap‖ ≤ B₁)
    (e₂ : ‖fderiv ℝ (fun y ↦ (J z.2 y).toLinearMap.toContinuousLinearMap) (u z)‖ ≤ B₂)
    (e₃ : ‖fderiv ℝ (ω.hamiltonianVectorField (H z.2)) (u z)‖ ≤ B₃)
    (eδ : ‖sliceDefect (fun t ↦ ω.hamiltonianVectorField (H t)) u z‖ ≤ Bδ) :
    ‖ω.floerLinearizationCoeff (fun w y ↦ (J w.2 y).toLinearMap.toContinuousLinearMap)
      (fun _ _ ↦ 0) (fun w ↦ H w.2) u z‖ ≤ B₂ * Bδ + B₁ * B₃ := by
  set J' : ℝ × ℝ → V → V →L[ℝ] V := fun w y ↦ (J w.2 y).toLinearMap.toContinuousLinearMap
  have hB₁0 : 0 ≤ B₁ := (norm_nonneg (J' z (u z))).trans e₁
  have hB₂0 : 0 ≤ B₂ := (norm_nonneg (fderiv ℝ (J' z) (u z))).trans e₂
  have hB₃0 : 0 ≤ B₃ := (norm_nonneg (fderiv ℝ (ω.hamiltonianVectorField (H z.2)) (u z))).trans e₃
  have hBδ0 : 0 ≤ Bδ := (norm_nonneg _).trans eδ
  refine opNorm_le_bound _ (by positivity) fun v ↦ ?_
  rw [floerLinearizationCoeff_apply, hamiltonianVectorField_const, fderiv_zero, Pi.zero_apply,
    zero_apply, sub_zero]
  have hδz : fderiv ℝ u z stdComplexLineImag - ω.hamiltonianVectorField (H z.2) (u z) =
      sliceDefect (fun t ↦ ω.hamiltonianVectorField (H t)) u z := by
    rw [sliceDefect_def, stdComplexLineImag_eq]
  rw [hδz]
  calc ‖fderiv ℝ (J' z) (u z) v (sliceDefect (fun t ↦ ω.hamiltonianVectorField (H t)) u z) -
        J' z (u z) (fderiv ℝ (ω.hamiltonianVectorField (H z.2)) (u z) v)‖
      ≤ ‖fderiv ℝ (J' z) (u z)‖ * ‖v‖ *
          ‖sliceDefect (fun t ↦ ω.hamiltonianVectorField (H t)) u z‖ +
        ‖J' z (u z)‖ * (‖fderiv ℝ (ω.hamiltonianVectorField (H z.2)) (u z)‖ * ‖v‖) :=
      (norm_sub_le _ _).trans (add_le_add (le_opNorm₂ _ _ _)
        ((le_opNorm _ _).trans (mul_le_mul_of_nonneg_left (le_opNorm _ _) (norm_nonneg _))))
    _ ≤ B₂ * ‖v‖ * Bδ + B₁ * (B₃ * ‖v‖) := by
        have hv := norm_nonneg v
        have h₁ := mul_le_mul (mul_le_mul_of_nonneg_right e₂ hv) eδ (norm_nonneg _)
          (by positivity)
        have h₂ := mul_le_mul e₁ (mul_le_mul_of_nonneg_right e₃ hv) (by positivity) hB₁0
        linarith
    _ = (B₂ * Bδ + B₁ * B₃) * ‖v‖ := by ring

/-- **Bounds of the coefficients of `D_u` for the datum `K = H_t dt`.** If `u` and its slice
defect `∂t u - X_{H_t}(u)` are bounded on `ℝ × [0, 1]`, then so are `J_t(u)` and the zeroth-order
coefficient of the linearized Floer operator. -/
private theorem exists_forall_norm_le_floerLinearizationCoeff (ω : SymplecticForm V)
    {H : ℝ → V → ℝ} (hH : ContDiff ℝ 2 (Function.uncurry H)) {J : ℝ → V → AlmostComplexStructure V}
    (hJ : ContDiff ℝ 1 fun p : ℝ × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap)
    {u : ℝ × ℝ → V} {B Bδ : ℝ} (hB : ∀ z ∈ univ ×ˢ Icc (0 : ℝ) 1, ‖u z‖ ≤ B)
    (hBδ : ∀ z ∈ univ ×ˢ Icc (0 : ℝ) 1,
      ‖sliceDefect (fun t ↦ ω.hamiltonianVectorField (H t)) u z‖ ≤ Bδ) :
    ∃ M, (∀ z ∈ univ ×ˢ Icc (0 : ℝ) 1,
        ‖(J z.2 (u z)).toLinearMap.toContinuousLinearMap‖ ≤ M) ∧
      ∀ z ∈ univ ×ˢ Icc (0 : ℝ) 1, ‖ω.floerLinearizationCoeff
        (fun w y ↦ (J w.2 y).toLinearMap.toContinuousLinearMap) (fun _ _ ↦ 0) (fun w ↦ H w.2) u
          z‖ ≤ M := by
  set Jc : ℝ × V → V →L[ℝ] V := fun p ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap
  set X : ℝ × V → V := fun p ↦ ω.hamiltonianVectorField (H p.1) p.2
  have hXc : ContDiff ℝ 1 X := ω.contDiff_hamiltonianVectorField_uncurry (n := 1) hH
  -- Bounds of `J`, `∂_y J` and `∂_y X_H` on the compact set of the points `(t, y)` with
  -- `t ∈ [0, 1]` and `‖y‖ ≤ B`.
  have hcpt : IsCompact (Icc (0 : ℝ) 1 ×ˢ Metric.closedBall (0 : V) B) :=
    isCompact_Icc.prod (isCompact_closedBall _ _)
  have hdJ : Continuous fun p : ℝ × V ↦ fderiv ℝ (fun y ↦ Jc (p.1, y)) p.2 :=
    (ContDiff.fderiv (f := fun (p : ℝ × V) (y : V) ↦ Jc (p.1, y)) (g := Prod.snd)
      (hJ.comp (contDiff_fst.fst.prodMk contDiff_snd)) (contDiff_snd (n := 0))
        (by norm_num)).continuous
  have hdX : Continuous fun p : ℝ × V ↦ fderiv ℝ (fun y ↦ X (p.1, y)) p.2 :=
    (ContDiff.fderiv (f := fun (p : ℝ × V) (y : V) ↦ X (p.1, y)) (g := Prod.snd)
      (hXc.comp (contDiff_fst.fst.prodMk contDiff_snd)) (contDiff_snd (n := 0))
        (by norm_num)).continuous
  obtain ⟨B₁, hB₁⟩ := hcpt.exists_bound_of_continuousOn hJ.continuous.continuousOn
  obtain ⟨B₂, hB₂⟩ := hcpt.exists_bound_of_continuousOn
    (f := fun p : ℝ × V ↦ fderiv ℝ (fun y ↦ Jc (p.1, y)) p.2) hdJ.continuousOn
  obtain ⟨B₃, hB₃⟩ := hcpt.exists_bound_of_continuousOn
    (f := fun p : ℝ × V ↦ fderiv ℝ (fun y ↦ X (p.1, y)) p.2) hdX.continuousOn
  have hmem {z : ℝ × ℝ} (hz : z ∈ univ ×ˢ Icc (0 : ℝ) 1) :
      (z.2, u z) ∈ Icc (0 : ℝ) 1 ×ˢ Metric.closedBall (0 : V) B :=
    ⟨hz.2, mem_closedBall_zero_iff.2 (hB z hz)⟩
  refine ⟨max B₁ (B₂ * Bδ + B₁ * B₃), fun z hz ↦ (hB₁ _ (hmem hz)).trans (le_max_left _ _),
    fun z hz ↦ le_trans ?_ (le_max_right _ _)⟩
  exact ω.norm_floerLinearizationCoeff_le (hB₁ (z.2, u z) (hmem hz))
    (hB₂ (z.2, u z) (hmem hz)) (hB₃ (z.2, u z) (hmem hz)) (hBδ z hz)

/-- **The semi-Fredholm estimate in the norms of the Sobolev spaces.** The estimate of
`TauCeti.Geometry.Symplectic.Floer.SemiFredholm`, stated with integrals over `[a, b] × [0, 1]` for
sections vanishing for `s ∉ (a, b)`, gives the estimate of
`finiteDimensional_ker_and_isClosed_range_floerSobolevOperator_of_estimate` on test sections. -/
private theorem norm_toW12_sq_le_of_setIntegral_le (ω : SymplecticForm V)
    (J : ℝ × ℝ → V → V →L[ℝ] V) (Ks Kt : ℝ × ℝ → V → ℝ) (u : ℝ × ℝ → V)
    (hD : ∀ ξ ∈ testSections V, MemLp (ω.floerLinearization J Ks Kt u ξ) 2 (stripMeasure))
    {C T : ℝ} (hest : ∀ ⦃ξ : ℝ × ℝ → V⦄, ContDiff ℝ 2 ξ → (∀ s t, ξ (s, t + 1) = ξ (s, t)) →
      ∀ ⦃a b : ℝ⦄, a ≤ b → (∀ s t, s ∉ Ioo a b → ξ (s, t) = 0) →
        ∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1, (‖fderiv ℝ ξ z stdComplexLineReal‖ ^ 2 +
            ‖fderiv ℝ ξ z stdComplexLineImag‖ ^ 2 + ‖ξ z‖ ^ 2) ≤
          C * ((∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1, ‖ω.floerLinearization J Ks Kt u ξ z‖ ^ 2) +
            ∫ z in Icc (-T) T ×ˢ Icc (0 : ℝ) 1, ‖ξ z‖ ^ 2))
    (ξ : testSections V) :
    ‖toW12 V ξ‖ ^ 2 ≤
      C * (‖ω.floerLinearizationLp J Ks Kt u hD ξ‖ ^ 2 + ‖restrictValue V T (toW12 V ξ)‖ ^ 2) := by
  obtain ⟨a, b, hab⟩ := exists_forall_notMem_Ioo_of_mem_testSections ξ.2
  have hab' : ∀ s t, s ∉ Ioo a (max a b) → (ξ : ℝ × ℝ → V) (s, t) = 0 := fun s t hs ↦
    hab s t fun h ↦ hs ⟨h.1, h.2.trans_le (le_max_right _ _)⟩
  have hsub : Icc a (max a b) ×ˢ Icc (0 : ℝ) 1 ⊆ univ ×ˢ Icc (0 : ℝ) 1 :=
    prod_mono (subset_univ _) subset_rfl
  have hzero {z : ℝ × ℝ} (hz : z ∈ univ ×ˢ Icc (0 : ℝ) 1 \ Icc a (max a b) ×ˢ Icc (0 : ℝ) 1) :
      z.1 ∉ Icc a (max a b) := fun h ↦ hz.2 ⟨h, hz.1.2⟩
  have hW : ‖toW12 V ξ‖ ^ 2 = ∫ z in Icc a (max a b) ×ˢ Icc (0 : ℝ) 1,
      (‖fderiv ℝ (ξ : ℝ × ℝ → V) z stdComplexLineReal‖ ^ 2 +
        ‖fderiv ℝ (ξ : ℝ × ℝ → V) z stdComplexLineImag‖ ^ 2 + ‖(ξ : ℝ × ℝ → V) z‖ ^ 2) := by
    rw [norm_toW12_sq, stdComplexLineReal_eq, stdComplexLineImag_eq]
    refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
      (MeasurableSet.univ.prod measurableSet_Icc) hsub fun z hz ↦ ?_
    have h := eventuallyEq_zero_of_forall_notMem_Ioo_of_fst_notMem_Icc hab' (hzero hz)
    simp [h.fderiv_eq, h.eq_of_nhds]
  have hDξ : ‖ω.floerLinearizationLp J Ks Kt u hD ξ‖ ^ 2 =
      ∫ z in Icc a (max a b) ×ˢ Icc (0 : ℝ) 1, ‖ω.floerLinearization J Ks Kt u ξ z‖ ^ 2 := by
    rw [norm_floerLinearizationLp_sq]
    refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
      (MeasurableSet.univ.prod measurableSet_Icc) hsub fun z hz ↦ ?_
    rw [ω.floerLinearization_eq_zero_of_fst_notMem_Icc _ _ _ _ hab' (hzero hz), norm_zero,
      zero_pow two_ne_zero]
  rw [hW, hDξ, norm_restrictValue_toW12_sq]
  exact hest (contDiff_of_mem_testSections ξ.2) (periodic_of_mem_testSections ξ.2)
    (le_max_left _ _) hab'

/-- **The Sobolev realization of the linearized Floer operator along a Floer trajectory is
semi-Fredholm.** Let `H` be a jointly `C²` Hamiltonian whose suspended vector field is globally
Lipschitz, let `J_t(y)` be a `C¹` family of almost complex structures, and let `u` be a `C¹` map
along which `J_t` is `ω`-compatible, whose loops converge uniformly to orbits `xm` at `-∞` and
`xp` at `+∞` starting at nondegenerate fixed points of the time-one map, with `J_t` compatible
along them, while its slice defect `∂t u - X_{H_t}(u)` tends uniformly to zero at both ends, as
for a Floer trajectory from `xm` to `xp`. Then the Sobolev realization
`D_u : W^{1,2}(ℝ × S¹, V) → L²` of the linearized Floer operator of the datum `K = H_t dt` has
finite dimensional kernel and closed range.

Here `hD` is any proof that `D_u` is square integrable on test sections, as supplied by
`TauCeti.SymplecticForm.memLp_floerLinearization`; the operator does not depend on it. -/
theorem finiteDimensional_ker_and_isClosed_range_floerSobolevOperator
    (ω : SymplecticForm V) {H : ℝ → V → ℝ} {K : ℝ≥0}
    (hX : LipschitzWith K (ω.timeDependentHamiltonianSuspension H))
    (hH : ContDiff ℝ 2 (Function.uncurry H)) {xm xp : ℝ → V}
    (hxm : ∀ t, HasDerivAt xm (ω.hamiltonianVectorField (H t) (xm t)) t)
    (hndm : IsNondegenerateFixedPt 𝓘(ℝ, V) (ω.timeDependentHamiltonianFlow H hX 0 1) (xm 0))
    (hxp : ∀ t, HasDerivAt xp (ω.hamiltonianVectorField (H t) (xp t)) t)
    (hndp : IsNondegenerateFixedPt 𝓘(ℝ, V) (ω.timeDependentHamiltonianFlow H hX 0 1) (xp 0))
    {J : ℝ → V → AlmostComplexStructure V}
    (hJ : ContDiff ℝ 1 fun p : ℝ × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hJxm : ∀ t, ω.Compatible (J t (xm t))) (hJxp : ∀ t, ω.Compatible (J t (xp t)))
    {u : ℝ × ℝ → V} (hu : ContDiff ℝ 1 u) (hJu : ∀ z, ω.Compatible (J z.2 (u z)))
    (huxm : TendstoUniformlyOn (fun s t ↦ u (s, t)) xm atBot (Icc 0 1))
    (huxp : TendstoUniformlyOn (fun s t ↦ u (s, t)) xp atTop (Icc 0 1))
    (hδm : TendstoUniformlyOn
      (fun s t ↦ sliceDefect (fun t ↦ ω.hamiltonianVectorField (H t)) u (s, t)) 0 atBot (Icc 0 1))
    (hδp : TendstoUniformlyOn
      (fun s t ↦ sliceDefect (fun t ↦ ω.hamiltonianVectorField (H t)) u (s, t)) 0 atTop
        (Icc 0 1))
    (hD : ∀ ξ ∈ testSections V, MemLp (ω.floerLinearization
      (fun w y ↦ (J w.2 y).toLinearMap.toContinuousLinearMap) (fun _ _ ↦ 0) (fun w ↦ H w.2) u ξ)
        2 (stripMeasure)) :
    FiniteDimensional ℝ (ω.floerSobolevOperator
        (fun w y ↦ (J w.2 y).toLinearMap.toContinuousLinearMap) (fun _ _ ↦ 0)
        (fun w ↦ H w.2) u hD).ker ∧
      IsClosed ((ω.floerSobolevOperator (fun w y ↦ (J w.2 y).toLinearMap.toContinuousLinearMap)
        (fun _ _ ↦ 0) (fun w ↦ H w.2) u hD).range : Set (Lp V 2 (stripMeasure))) := by
  -- `u` and its slice defect converge uniformly at both ends, so they are bounded on the strip.
  have hxmc : Continuous xm := continuous_iff_continuousAt.2 fun t ↦ (hxm t).continuousAt
  have hxpc : Continuous xp := continuous_iff_continuousAt.2 fun t ↦ (hxp t).continuousAt
  obtain ⟨Bm, hBm⟩ := exists_forall_norm_le_of_continuous hxmc
  obtain ⟨Bp, hBp⟩ := exists_forall_norm_le_of_continuous hxpc
  obtain ⟨B, hB⟩ := exists_forall_norm_le_of_tendstoUniformlyOn hu.continuous hBm hBp huxm huxp
  have hδc : Continuous (sliceDefect (fun t ↦ ω.hamiltonianVectorField (H t)) u) := by
    have h₁ : Continuous fun z ↦ fderiv ℝ u z (0, 1) :=
      (hu.continuous_fderiv one_ne_zero).clm_apply continuous_const
    have h₂ : Continuous fun z : ℝ × ℝ ↦ ω.hamiltonianVectorField (H z.2) (u z) :=
      (ω.contDiff_hamiltonianVectorField_uncurry (n := 1) hH).continuous.comp
        (continuous_snd.prodMk hu.continuous)
    rw [show sliceDefect (fun t ↦ ω.hamiltonianVectorField (H t)) u =
      fun z ↦ fderiv ℝ u z (0, 1) - ω.hamiltonianVectorField (H z.2) (u z) from
        funext (sliceDefect_def _ _)]
    exact h₁.sub h₂
  obtain ⟨Bδ, hBδ⟩ := exists_forall_norm_le_of_tendstoUniformlyOn hδc
    (fun _ _ ↦ (norm_zero (E := V)).le) (fun _ _ ↦ (norm_zero (E := V)).le) hδm hδp
  -- Hence `D_u` is bounded in `W^{1,2}`, and the semi-Fredholm estimate gives the conclusion.
  obtain ⟨M, hJM, hAM⟩ := ω.exists_forall_norm_le_floerLinearizationCoeff hH hJ hB hBδ
  obtain ⟨C, -, T, hest⟩ := ω.exists_forall_setIntegral_le_mul_setIntegral_floerLinearization_add
    hX hH hxm hndm hxp hndp hJ hJxm hJxp hu hJu huxm huxp hδm hδp
  exact ω.finiteDimensional_ker_and_isClosed_range_floerSobolevOperator_of_estimate _ _ _ u hD
    (ω.norm_floerLinearizationLp_le _ _ _ u hD hJM hAM)
    (ω.norm_toW12_sq_le_of_setIntegral_le _ _ _ u hD hest)

end TauCeti.SymplecticForm
