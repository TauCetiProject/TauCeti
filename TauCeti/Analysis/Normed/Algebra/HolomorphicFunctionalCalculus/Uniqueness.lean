/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.HolomorphicFunctions.CauchyRiemannSum
public import TauCeti.Analysis.Normed.Algebra.HolomorphicFunctionalCalculus.Basic

/-!
# Uniqueness, commutativity, and explicit evaluations of the holomorphic calculus

For an element `a` of a complex Banach algebra `A`, `holomorphicCalculus a` is the unique unital
complex-algebra homomorphism `holomorphicGerms (spectrum ℂ a) →ₐ[ℂ] A` sending the coordinate germ
to `a` whose compositions with `HolomorphicFunctions.toGerm` are continuous on every open
neighbourhood of `spectrum ℂ a` for the compact-open topology.

Along the way we record:
* commutativity of `holomorphicCalculusOn a U ha f` and `holomorphicCalculus a g` with every
  element commuting with `a`;
* agreement of the calculus with resolvents on Cauchy kernels `z ↦ (w - z)⁻¹`, with rational
  expressions `p(a) q(a)⁻¹` whenever `q` has no zeros on `spectrum ℂ a`, and with norm-convergent
  power series `∑' n, c n • (a - z₀) ^ n` whenever `spectrum ℂ a` lies in the open disk of
  convergence.

No normalization of `‖(1 : A)‖` or nontriviality of `A` is assumed.

## References

* H. G. Dales, *Banach Algebras and Automatic Continuity*, Theorem 2.4.9.
* J. B. Conway, *A Course in Functional Analysis*, second edition, VII.4.
-/

public noncomputable section

open Complex Filter Metric Set TopologicalSpace Topology
open scoped NNReal ENNReal Ring

section Commute

open TauCeti TauCeti.Contour TauCeti.HolomorphicFunctions

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

/-- Every element commuting with `a` commutes with `holomorphicCalculusOn a U ha f`. -/
theorem Commute.holomorphicCalculusOn_right {a b : A} (hb : Commute b a) (U : Opens ℂ)
    (ha : spectrum ℂ a ⊆ U) (f : holomorphicFunctions U) :
    Commute b (holomorphicCalculusOn a U ha f) := by
  obtain ⟨Γ, hΓ, hn, hw⟩ := (spectrum.isCompact a).exists_cycle_windingNumber_eq_one U.isOpen ha
  rw [holomorphicCalculusOn_eq_integral a U ha f Γ hΓ hn hw]
  have hfΓ : ContinuousOn (extend f) (Cycle.trace Γ) :=
    (differentiableOn_extend f).continuousOn.mono fun _ hz ↦ (Cycle.isIn_iff.mp hΓ hz).1
  have hΓ_res : Γ.IsIn (resolventSet ℂ a) :=
    Cycle.isIn_iff.mpr fun _ hz ↦ spectrum.notMem_iff.mp (Cycle.isIn_iff.mp hΓ hz).2
  exact (hb.integral_smul_resolvent_right hfΓ hΓ_res).smul_right _

/-- `holomorphicCalculusOn a U ha f` commutes with every element commuting with `a`. -/
theorem Commute.holomorphicCalculusOn_left {a b : A} (hb : Commute a b) (U : Opens ℂ)
    (ha : spectrum ℂ a ⊆ U) (f : holomorphicFunctions U) :
    Commute (holomorphicCalculusOn a U ha f) b :=
  (hb.symm.holomorphicCalculusOn_right U ha f).symm

/-- Every element commuting with `a` commutes with `holomorphicCalculus a g`. -/
theorem Commute.holomorphicCalculus_right {a b : A} (hb : Commute b a)
    (g : holomorphicGerms (spectrum ℂ a)) :
    Commute b (holomorphicCalculus a g) := by
  obtain ⟨U, ha, f, rfl⟩ := holomorphicGerms.exists_toGerm_eq g
  rw [holomorphicCalculus_toGerm]
  exact hb.holomorphicCalculusOn_right U ha f

/-- `holomorphicCalculus a g` commutes with every element commuting with `a`. -/
theorem Commute.holomorphicCalculus_left {a b : A} (hb : Commute a b)
    (g : holomorphicGerms (spectrum ℂ a)) :
    Commute (holomorphicCalculus a g) b :=
  (hb.symm.holomorphicCalculus_right g).symm

end Commute

namespace TauCeti

open Contour HolomorphicFunctions

/-- Fix the inherited additive group before forming linear spans of `holomorphicFunctions`. -/
local instance instAddCommGroupHolomorphicCalculusUniqueness (U : Opens ℂ) :
    AddCommGroup (holomorphicFunctions U) := inferInstance

/-- Linear maps and spans use the additive monoid projection of the inherited additive group. -/
local instance instAddCommMonoidHolomorphicCalculusUniqueness (U : Opens ℂ) :
    AddCommMonoid (holomorphicFunctions U) :=
  (inferInstance : AddCommGroup (holomorphicFunctions U)).toAddCommMonoid

section Algebraic

/-- Any unital `ℂ`-algebra homomorphism on `holomorphicFunctions V` sending the coordinate
function to `b` sends each Cauchy kernel `z ↦ (w - z)⁻¹` (`w ∉ V`) to `resolvent b w`. -/
theorem algHom_cauchyKernel_eq_resolvent {B : Type*} [Ring B] [Algebra ℂ B]
    {V : Opens ℂ} {b : B} (Φ : holomorphicFunctions V →ₐ[ℂ] B)
    (hΦ : Φ (of V id differentiableOn_id) = b) {w : ℂ} (hw : w ∉ (V : Set ℂ)) :
    Φ (cauchyKernel hw) = resolvent b w := by
  have hleft : (algebraMap ℂ B w - b) * Φ (cauchyKernel hw) = 1 := by
    rw [← Φ.commutes w, ← hΦ, ← map_sub, ← map_mul, sub_id_mul_cauchyKernel, map_one]
  have hright : Φ (cauchyKernel hw) * (algebraMap ℂ B w - b) = 1 := by
    rw [← Φ.commutes w, ← hΦ, ← map_sub, ← map_mul, cauchyKernel_mul_sub_id, map_one]
  let u : Bˣ :=
    { val := algebraMap ℂ B w - b
      inv := Φ (cauchyKernel hw)
      val_inv := hleft
      inv_val := hright }
  have hu : algebraMap ℂ B w - b = u := rfl
  rw [resolvent, hu, Ring.inverse_unit]
  rfl

end Algebraic

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

/-- On an open neighbourhood `U` of `spectrum ℂ a`, the holomorphic calculus sends the Cauchy
kernel at `w ∉ U` to `resolvent a w`. -/
@[simp]
theorem holomorphicCalculusOn_cauchyKernel (a : A) (U : Opens ℂ) (ha : spectrum ℂ a ⊆ U)
    {w : ℂ} (hw : w ∉ (U : Set ℂ)) :
    holomorphicCalculusOn a U ha (cauchyKernel hw) = resolvent a w :=
  algHom_cauchyKernel_eq_resolvent (holomorphicCalculusOn a U ha)
    (holomorphicCalculusOn_id a U ha) hw

/-- At a point `w` in the resolvent set of `a`, the holomorphic germ calculus sends
`z ↦ (w - z)⁻¹` to `resolvent a w`. -/
theorem holomorphicCalculus_inv_sub (a : A) {w : ℂ} (hw : w ∈ resolventSet ℂ a)
    (hf : AnalyticOnNhd ℂ (fun z ↦ (w - z)⁻¹) (spectrum ℂ a) :=
      (analyticOnNhd_const.sub analyticOnNhd_id).inv fun _ hz ↦
        sub_ne_zero.mpr (ne_of_mem_of_not_mem hz (spectrum.notMem_iff.mpr hw)).symm) :
    holomorphicCalculus a (holomorphicGerms.ofFun (fun z ↦ (w - z)⁻¹) hf) = resolvent a w := by
  let U : Opens ℂ := ⟨{w}ᶜ, isClosed_singleton.isOpen_compl⟩
  have ha : spectrum ℂ a ⊆ U := fun z hz hzw ↦
    spectrum.notMem_iff.mpr hw (mem_singleton_iff.mp hzw ▸ hz)
  have hwU : w ∉ (U : Set ℂ) := fun h ↦ h (mem_singleton w)
  have hgerm : holomorphicGerms.ofFun (fun z ↦ (w - z)⁻¹) hf = toGerm ha (cauchyKernel hwU) :=
    (toGerm_eq_ofFun ha (cauchyKernel hwU) _ hf fun z ↦ cauchyKernel_apply hwU z).symm
  rw [hgerm, holomorphicCalculus_toGerm, holomorphicCalculusOn_cauchyKernel]

/-- **Rational functional calculus compatibility.** For polynomials `p` and `q` such that `q` has
no zeros on `spectrum ℂ a`, the holomorphic germ calculus sends `z ↦ p.eval z / q.eval z` to
`p(a) * q(a)⁻¹`. -/
theorem holomorphicCalculus_div_polynomial (a : A) (p q : Polynomial ℂ)
    (hq : ∀ z ∈ spectrum ℂ a, q.eval z ≠ 0)
    (hf : AnalyticOnNhd ℂ (fun z ↦ p.eval z / q.eval z) (spectrum ℂ a) :=
      ((AnalyticOnNhd.eval_polynomial p).mono (subset_univ _)).div
        ((AnalyticOnNhd.eval_polynomial q).mono (subset_univ _)) hq) :
    holomorphicCalculus a (holomorphicGerms.ofFun (fun z ↦ p.eval z / q.eval z) hf) =
      Polynomial.aeval a p * (Polynomial.aeval a q)⁻¹ʳ := by
  have hqunit : IsUnit (Polynomial.aeval a q) := by
    rw [← spectrum.zero_notMem_iff (R := ℂ), spectrum.map_polynomial_aeval]
    rintro ⟨z, hz, hz0⟩
    exact hq z hz hz0
  have hmul :
      holomorphicGerms.ofFun (fun z ↦ p.eval z / q.eval z) hf *
        holomorphicGerms.ofFun (fun z ↦ q.eval z)
          ((AnalyticOnNhd.eval_polynomial q).mono (subset_univ _)) =
        holomorphicGerms.ofFun (fun z ↦ p.eval z)
          ((AnalyticOnNhd.eval_polynomial p).mono (subset_univ _)) := by
    rw [← holomorphicGerms.ofFun_mul, holomorphicGerms.ofFun_eq_iff]
    have hopen : IsOpen {z : ℂ | q.eval z ≠ 0} :=
      isOpen_compl_singleton.preimage q.continuous
    filter_upwards [hopen.mem_nhdsSet.mpr hq] with z hz
    exact div_mul_cancel₀ (p.eval z) hz
  have hcalc := congrArg (holomorphicCalculus a) hmul
  rw [map_mul, holomorphicCalculus_polynomial, holomorphicCalculus_polynomial] at hcalc
  calc holomorphicCalculus a (holomorphicGerms.ofFun (fun z ↦ p.eval z / q.eval z) hf)
      = holomorphicCalculus a (holomorphicGerms.ofFun (fun z ↦ p.eval z / q.eval z) hf) *
          (Polynomial.aeval a q * (Polynomial.aeval a q)⁻¹ʳ) := by
          rw [Ring.mul_inverse_cancel _ hqunit, mul_one]
    _ = (holomorphicCalculus a (holomorphicGerms.ofFun (fun z ↦ p.eval z / q.eval z) hf) *
          Polynomial.aeval a q) * (Polynomial.aeval a q)⁻¹ʳ := (mul_assoc _ _ _).symm
    _ = Polynomial.aeval a p * (Polynomial.aeval a q)⁻¹ʳ := by rw [hcalc]

/-- **Power-series evaluation of the holomorphic calculus.** If `f` has the scalar power-series
expansion `∑ c n (z - z₀) ^ n` on the open ball `Metric.eball z₀ R` containing `spectrum ℂ a`,
then `∑ c n • (a - z₀) ^ n` converges unconditionally in norm to `holomorphicCalculus a f`. -/
theorem _root_.HasFPowerSeriesOnBall.hasSum_holomorphicCalculus
    {f : ℂ → ℂ} {c : ℕ → ℂ} {z₀ : ℂ} {R : ℝ≥0∞}
    (hf : HasFPowerSeriesOnBall f (FormalMultilinearSeries.ofScalars ℂ c) z₀ R)
    (a : A) (ha : spectrum ℂ a ⊆ Metric.eball z₀ R)
    (hf_an : AnalyticOnNhd ℂ f (spectrum ℂ a) := hf.analyticOnNhd.mono ha) :
    HasSum (fun n ↦ c n • (a - algebraMap ℂ A z₀) ^ n)
      (holomorphicCalculus a (holomorphicGerms.ofFun f hf_an)) := by
  rcases subsingleton_or_nontrivial A with hsub | hnt
  · rw [Subsingleton.elim (holomorphicCalculus a (holomorphicGerms.ofFun f hf_an)) 0]
    exact hasSum_zero.congr_fun fun _ ↦ Subsingleton.elim _ _
  let b : A := a - algebraMap ℂ A z₀
  -- Step 1: Establish absolute norm summability from Gelfand's spectral radius formula.
  have hspec_lt : spectralRadius ℂ b < R := by
    obtain ⟨w, hw, hw_eq⟩ := spectrum.exists_nnNorm_eq_spectralRadius b
    rw [← hw_eq]
    have hw' : w + z₀ ∈ spectrum ℂ a := by
      rw [spectrum.mem_iff] at hw ⊢
      convert hw using 2
      dsimp only [b]
      rw [map_add]
      abel
    simpa only [Metric.mem_eball, eDist_eq_eNorm_sub, add_sub_cancel_right, eNorm_eq_nnNorm]
      using ha hw'
  obtain ⟨r, hrb, hrR⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hspec_lt
  have hgelf : gelfandRadius b < (r : ℝ) := by
    have h1 : ENNReal.ofReal (gelfandRadius b) < (r : ℝ≥0∞) :=
      spectrum.spectralRadius_eq_gelfandRadius b ▸ hrb
    exact (ENNReal.ofReal_lt_coe_iff (gelfandRadius_nonneg b)).mp h1
  obtain ⟨C, -, hpow⟩ := norm_pow_le_mul_pow_of_gelfandRadius_lt b hgelf
  have hsum_scalar : Summable (fun n ↦ ‖c n‖ * (r : ℝ) ^ n) := by
    simpa only [FormalMultilinearSeries.ofScalars_norm] using
      (FormalMultilinearSeries.ofScalars ℂ c).summable_norm_mul_pow (hrR.trans_le hf.r_le)
  have hsum_norm : Summable (fun n ↦ ‖c n • b ^ n‖) :=
    Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _)
      (fun n ↦ by
        rw [norm_smul]
        calc ‖c n‖ * ‖b ^ n‖ ≤ ‖c n‖ * (C * (r : ℝ) ^ n) :=
              mul_le_mul_of_nonneg_left (hpow n) (norm_nonneg _)
          _ = C * (‖c n‖ * (r : ℝ) ^ n) := by ring)
      (hsum_scalar.mul_left C)
  have hsum : Summable (fun n ↦ c n • b ^ n) := hsum_norm.of_norm
  -- Step 2: Identify the partial-sum limit on `U = Metric.eball z₀ R` by continuity.
  let U : Opens ℂ := ⟨Metric.eball z₀ R, Metric.isOpen_eball⟩
  have haU : spectrum ℂ a ⊆ U := ha
  let zU : holomorphicFunctions U :=
    of U id differentiableOn_id - algebraMap ℂ (holomorphicFunctions U) z₀
  let F : ℕ → holomorphicFunctions U := fun n ↦ ∑ k ∈ Finset.range n, c k • zU ^ k
  have hF_tendsto : Tendsto F atTop (𝓝 (of U f hf.differentiableOn)) := by
    rw [tendsto_iff_tendstoLocallyUniformlyOn]
    refine (hf.tendstoLocallyUniformlyOn'.congr ?_).congr_right fun z hz ↦
      ((extend_apply (of U f hf.differentiableOn) ⟨z, hz⟩).trans (of_apply _ _ ⟨z, hz⟩)).symm
    intro n z hz
    rw [extend_apply (F n) ⟨z, hz⟩]
    simp [F, zU, FormalMultilinearSeries.partialSum, mul_comm]
  have hcalc_tendsto :
      Tendsto (fun n ↦ holomorphicCalculusOn a U haU (F n)) atTop
        (𝓝 (holomorphicCalculusOn a U haU (of U f hf.differentiableOn))) :=
    (continuous_holomorphicCalculusOn a U haU).tendsto _ |>.comp hF_tendsto
  have hcalc_F (n : ℕ) :
      holomorphicCalculusOn a U haU (F n) = ∑ k ∈ Finset.range n, c k • b ^ k := by
    simp [F, zU, b, map_sum, map_smul, map_pow, map_sub]
  simp only [hcalc_F] at hcalc_tendsto
  have hgerm_eq :
      holomorphicCalculusOn a U haU (of U f hf.differentiableOn) =
        holomorphicCalculus a (holomorphicGerms.ofFun f hf_an) := by
    rw [← holomorphicCalculus_toGerm a U haU (of U f hf.differentiableOn), toGerm_of]
  rw [hgerm_eq] at hcalc_tendsto
  exact tendsto_nhds_unique hsum.hasSum.tendsto_sum_nat hcalc_tendsto ▸ hsum.hasSum

/-- Specialization of `HasFPowerSeriesOnBall.hasSum_holomorphicCalculus` centered at `0`. -/
theorem _root_.HasFPowerSeriesOnBall.hasSum_holomorphicCalculus_zero
    {f : ℂ → ℂ} {c : ℕ → ℂ} {R : ℝ≥0∞}
    (hf : HasFPowerSeriesOnBall f (FormalMultilinearSeries.ofScalars ℂ c) 0 R)
    (a : A) (ha : spectrum ℂ a ⊆ Metric.eball 0 R)
    (hf_an : AnalyticOnNhd ℂ f (spectrum ℂ a) := hf.analyticOnNhd.mono ha) :
    HasSum (fun n ↦ c n • a ^ n)
      (holomorphicCalculus a (holomorphicGerms.ofFun f hf_an)) := by
  simpa only [map_zero, sub_zero] using hf.hasSum_holomorphicCalculus a ha hf_an

/-- **Uniqueness of the holomorphic functional calculus.** Any unital complex-algebra homomorphism
on `holomorphicGerms (spectrum ℂ a)` sending the coordinate germ to `a` whose restriction to every
open neighbourhood of `spectrum ℂ a` is continuous for the compact-open topology coincides with
`holomorphicCalculus a`. -/
theorem holomorphicCalculus_unique (a : A) (Φ : holomorphicGerms (spectrum ℂ a) →ₐ[ℂ] A)
    (hΦ_id : Φ (holomorphicGerms.ofFun id analyticOnNhd_id) = a)
    (hΦ_cont : ∀ (U : Opens ℂ) (ha : spectrum ℂ a ⊆ U),
      Continuous (Φ.comp (toGerm ha))) :
    Φ = holomorphicCalculus a := by
  apply holomorphicGerms.algHom_ext
  intro U ha f
  obtain ⟨Γ, hΓ, hn, hw⟩ := (spectrum.isCompact a).exists_cycle_windingNumber_eq_one U.isOpen ha
  -- Carve out the open winding-one region `V ≤ U` avoiding `Cycle.trace Γ`.
  have hW_open : IsOpen {z : ℂ | z ∉ Cycle.trace Γ ∧ Cycle.windingNumber z Γ = 1} := by
    have heq : {z : ℂ | z ∉ Cycle.trace Γ ∧ Cycle.windingNumber z Γ = 1} =
        Subtype.val ''
          ((fun z : ((Cycle.trace Γ : Set ℂ)ᶜ : Set ℂ) ↦ Cycle.windingNumber z.val Γ) ⁻¹' {1}) := by
      ext z
      simp [and_comm]
    rw [heq]
    exact (Cycle.isCompact_trace Γ).isClosed.isOpen_compl.isOpenMap_subtype_val _
      ((Cycle.isLocallyConstant_windingNumber Γ).isOpen_fiber 1)
  let V : Opens ℂ := ⟨(U : Set ℂ) ∩ {z | z ∉ Cycle.trace Γ ∧ Cycle.windingNumber z Γ = 1},
    U.isOpen.inter hW_open⟩
  have hVU : V ≤ U := inter_subset_left
  have haV : spectrum ℂ a ⊆ V := fun z hz ↦
    ⟨ha hz, fun hzΓ ↦ (Cycle.isIn_iff.mp hΓ hzΓ).2 hz, hw z hz⟩
  have hVΓ : Disjoint (V : Set ℂ) (Cycle.trace Γ) :=
    disjoint_left.mpr fun _ hzV hzΓ ↦ hzV.2.1 hzΓ
  have hwV : ∀ z ∈ (V : Set ℂ), Cycle.windingNumber z Γ = 1 := fun _ hzV ↦ hzV.2.2
  have hΓU : Γ.IsIn U := Cycle.isIn_iff.mpr fun _ hz ↦ (Cycle.isIn_iff.mp hΓ hz).1
  -- Both `Φ ∘ toGerm haV` and `holomorphicCalculusOn a V haV` send Cauchy kernels to resolvents.
  let ΦV : holomorphicFunctions V →ₐ[ℂ] A := Φ.comp (toGerm haV)
  have hΦV_id : ΦV (of V id differentiableOn_id) = a := by
    simpa only [ΦV, AlgHom.comp_apply, toGerm_of] using hΦ_id
  let S : Set (holomorphicFunctions V) :=
    {cauchyKernel (V := V) (hVΓ.notMem_of_mem_right hm) | (w : ℂ) (hm : w ∈ Cycle.trace Γ)}
  have hS : Set.EqOn ΦV.toLinearMap (holomorphicCalculusOn a V haV).toLinearMap S := by
    rintro _ ⟨w, hm, rfl⟩
    simp only [AlgHom.toLinearMap_apply]
    rw [algHom_cauchyKernel_eq_resolvent ΦV hΦV_id, holomorphicCalculusOn_cauchyKernel]
  have hmem := restrict_mem_closure_span_cauchyKernel hVU f Γ hΓU hn hVΓ hwV
  have heqV : ΦV (restrict hVU f) = holomorphicCalculusOn a V haV (restrict hVU f) :=
    (LinearMap.eqOn_span' hS).closure (hΦ_cont V haV) (continuous_holomorphicCalculusOn a V haV)
      hmem
  simpa only [ΦV, AlgHom.comp_apply, toGerm_restrict, holomorphicCalculusOn_restrict,
    holomorphicCalculus_toGerm] using heqV

/-- Characterization of `holomorphicCalculus a` by the coordinate condition and open-domain
continuity. -/
theorem eq_holomorphicCalculus_iff (a : A) (Φ : holomorphicGerms (spectrum ℂ a) →ₐ[ℂ] A) :
    Φ = holomorphicCalculus a ↔
      Φ (holomorphicGerms.ofFun id analyticOnNhd_id) = a ∧
        ∀ (U : Opens ℂ) (ha : spectrum ℂ a ⊆ U), Continuous (Φ.comp (toGerm ha)) := by
  refine ⟨?_, fun ⟨hid, hcont⟩ ↦ holomorphicCalculus_unique a Φ hid hcont⟩
  rintro rfl
  refine ⟨holomorphicCalculus_id a, fun U ha ↦ ?_⟩
  have hcomp : (holomorphicCalculus a).comp (toGerm ha) = holomorphicCalculusOn a U ha := by
    ext f
    exact holomorphicCalculus_toGerm a U ha f
  rw [hcomp]
  exact continuous_holomorphicCalculusOn a U ha

end TauCeti
