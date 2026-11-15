/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.ChangeOrigin
public import Mathlib.Analysis.Analytic.OfScalars
public import TauCeti.Analysis.Complex.HolomorphicFunctions.CauchyKernel
public import TauCeti.Analysis.Normed.Algebra.HolomorphicFunctionalCalculus.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandFormula

/-!
# Uniqueness, rational functions, and power series in the holomorphic functional calculus

Any unital `ℂ`-algebra homomorphism out of `holomorphicFunctions V` sending `id` to `a` must send
every Cauchy kernel `(w - ·)⁻¹` with `w ∉ V` to `resolvent a w`, and must agree with rational
evaluation `p(a) q(a)⁻¹` on quotients of polynomials whose denominator does not vanish on `V`.

Combining this algebraic determination on Cauchy kernels with Riemann-sum approximation of
Cauchy's integral formula (`HolomorphicFunctions.tendsto_cauchyIntegralRiemannSum`) proves that
`holomorphicCalculus a` is the **unique** unital `ℂ`-algebra homomorphism from
`holomorphicGerms (spectrum ℂ a)` to `A` sending the coordinate germ to `a` whose restriction to
every open neighbourhood of `spectrum ℂ a` is continuous for the compact-open topology.

Furthermore, if `f` has a scalar power-series expansion `∑ c_n (z - z₀)^n` on an open extended ball
`Metric.eball z₀ r` containing `spectrum ℂ a`, Gelfand's spectral radius formula ensures absolute
convergence of `∑ c_n • (a - z₀)^n` in `A`, and continuity of `holomorphicCalculusOn` identifies
`holomorphicCalculus a` of `f` with that unconditional sum.

## Main results

* `TauCeti.algHom_cauchyKernel_eq_resolvent`, `TauCeti.holomorphicCalculusOn_cauchyKernel`,
  `TauCeti.holomorphicCalculus_sub_inv`, `TauCeti.holomorphicCalculus_inv_sub`: evaluation on
  Cauchy kernels.
* `TauCeti.holomorphicCalculusOn_div_polynomial`, `TauCeti.holomorphicCalculus_div_polynomial`:
  compatibility with rational functions `p / q` regular on the spectrum.
* `TauCeti.summable_norm_smul_sub_pow_of_le_radius`,
  `HasFPowerSeriesOnBall.hasSum_holomorphicCalculus`,
  `HasFPowerSeriesOnBall.holomorphicCalculus_eq_tsum`: unconditional norm-convergent power-series
  evaluation when `spectrum ℂ a ⊆ Metric.eball z₀ r`.
* `TauCeti.holomorphicCalculus_unique`, `TauCeti.existsUnique_holomorphicCalculus`: uniqueness of
  the holomorphic germ functional calculus from continuity on open neighbourhoods.

## References

* H. G. Dales, *Banach Algebras and Automatic Continuity*, Theorem 2.4.9.
* J. B. Conway, *A Course in Functional Analysis*, second edition, Theorem VII.4.10.
* W. Rudin, *Functional Analysis*, second edition, Theorem 10.27.
-/

public noncomputable section

open Complex Filter Set TopologicalSpace Topology
open scoped ENNReal NNReal Real

namespace TauCeti

open Contour HolomorphicFunctions

section Algebraic

variable {B : Type*} [Ring B] [Algebra ℂ B]

private theorem algHom_map_sub {V : Opens ℂ} (Φ : holomorphicFunctions V →ₐ[ℂ] B)
    (x y : holomorphicFunctions V) : Φ (x - y) = Φ x - Φ y := by
  have h : x - y + y = x := by
    apply Subtype.ext
    ext z
    simp
  exact eq_sub_of_add_eq (by rw [← map_add, h])

/-- Any unital `ℂ`-algebra homomorphism out of `holomorphicFunctions V` sending `id` to `b`
forces every point `w ∉ V` into `resolventSet ℂ b`. -/
theorem algHom_mem_resolventSet_of_notMem {V : Opens ℂ} (Φ : holomorphicFunctions V →ₐ[ℂ] B)
    {b : B} (hid : Φ (of V id differentiableOn_id) = b) {w : ℂ} (hw : w ∉ (V : Set ℂ)) :
    w ∈ resolventSet ℂ b := by
  have hunit : IsUnit (Φ (algebraMap ℂ (holomorphicFunctions V) w -
      of V id differentiableOn_id)) :=
    (isUnit_sub_id_of_notMem V hw).map Φ
  rwa [algHom_map_sub, AlgHom.commutes, hid] at hunit

/-- Any unital `ℂ`-algebra homomorphism out of `holomorphicFunctions V` sending `id` to `b`
sends `cauchyKernel V w hw` to `resolvent b w`. -/
theorem algHom_cauchyKernel_eq_resolvent {V : Opens ℂ} (Φ : holomorphicFunctions V →ₐ[ℂ] B)
    {b : B} (hid : Φ (of V id differentiableOn_id) = b) {w : ℂ} (hw : w ∉ (V : Set ℂ)) :
    Φ (cauchyKernel V w hw) = resolvent b w := by
  have h₁ := congrArg Φ (sub_id_mul_cauchyKernel V w hw)
  have h₂ := congrArg Φ (cauchyKernel_mul_sub_id V w hw)
  rw [map_mul, map_one, algHom_map_sub, AlgHom.commutes, hid] at h₁ h₂
  let u : Bˣ :=
    { val := algebraMap ℂ B w - b
      inv := Φ (cauchyKernel V w hw)
      val_inv := h₁
      inv_val := h₂ }
  exact (Ring.inverse_unit u).symm

end Algebraic

section BanachAlgebra

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

/-- On an open neighbourhood `U` of the spectrum, the holomorphic calculus sends the Cauchy kernel
`(w - ·)⁻¹` with `w ∉ U` to `resolvent a w`. -/
@[simp]
theorem holomorphicCalculusOn_cauchyKernel (a : A) (U : Opens ℂ) (ha : spectrum ℂ a ⊆ U)
    (w : ℂ) (hw : w ∉ (U : Set ℂ)) :
    holomorphicCalculusOn a U ha (cauchyKernel U w hw) = resolvent a w :=
  algHom_cauchyKernel_eq_resolvent (holomorphicCalculusOn a U ha)
    (holomorphicCalculusOn_id a U ha) hw

/-- The germ calculus sends `(w - ·)⁻¹` to `resolvent a w` for every `w ∈ resolventSet ℂ a`. -/
@[simp]
theorem holomorphicCalculus_sub_inv (a : A) {w : ℂ} (hw : w ∈ resolventSet ℂ a) :
    holomorphicCalculus a
      (holomorphicGerms.ofFun (fun z => (w - z)⁻¹)
        ((((differentiableOn_const w).sub differentiableOn_id).inv fun _ hz =>
          sub_ne_zero.mpr (Ne.symm (mem_compl_singleton_iff.mp hz))).analyticOnNhd
            isOpen_compl_singleton |>.mono
              fun _ hz hzw => spectrum.notMem_iff.mpr hw
                ((mem_singleton_iff.mp hzw) ▸ hz))) =
      resolvent a w := by
  let U : Opens ℂ := ⟨{w}ᶜ, isOpen_compl_singleton⟩
  have haU : spectrum ℂ a ⊆ U := fun z hz hzw =>
    spectrum.notMem_iff.mpr hw ((mem_singleton_iff.mp hzw) ▸ hz)
  have hwU : w ∉ (U : Set ℂ) := not_not_intro (mem_singleton w)
  have hgerm : toGerm haU (cauchyKernel U w hwU) =
      holomorphicGerms.ofFun (fun z => (w - z)⁻¹)
        ((((differentiableOn_const w).sub differentiableOn_id).inv fun _ hz =>
          sub_ne_zero.mpr (Ne.symm (mem_compl_singleton_iff.mp hz))).analyticOnNhd
            isOpen_compl_singleton |>.mono
              fun _ hz hzw => spectrum.notMem_iff.mpr hw
                ((mem_singleton_iff.mp hzw) ▸ hz)) :=
    toGerm_eq_ofFun haU (cauchyKernel U w hwU) _ _ fun z => cauchyKernel_apply U w hwU z
  rw [← hgerm, holomorphicCalculus_toGerm, holomorphicCalculusOn_cauchyKernel]

/-- The germ calculus sends `(· - w)⁻¹` to `-resolvent a w` for every `w ∈ resolventSet ℂ a`. -/
@[simp]
theorem holomorphicCalculus_inv_sub (a : A) {w : ℂ} (hw : w ∈ resolventSet ℂ a) :
    holomorphicCalculus a
      (holomorphicGerms.ofFun (fun z => (z - w)⁻¹)
        (((differentiableOn_id.sub (differentiableOn_const w)).inv fun _ hz =>
          sub_ne_zero.mpr (mem_compl_singleton_iff.mp hz)).analyticOnNhd
            isOpen_compl_singleton |>.mono
              fun _ hz hzw => spectrum.notMem_iff.mpr hw
                ((mem_singleton_iff.mp hzw) ▸ hz))) =
      -resolvent a w := by
  let U : Opens ℂ := ⟨{w}ᶜ, isOpen_compl_singleton⟩
  have haU : spectrum ℂ a ⊆ U := fun z hz hzw =>
    spectrum.notMem_iff.mpr hw ((mem_singleton_iff.mp hzw) ▸ hz)
  have hwU : w ∉ (U : Set ℂ) := not_not_intro (mem_singleton w)
  have hgerm : toGerm haU ((-1 : ℂ) • cauchyKernel U w hwU) =
      holomorphicGerms.ofFun (fun z => (z - w)⁻¹)
        (((differentiableOn_id.sub (differentiableOn_const w)).inv fun _ hz =>
          sub_ne_zero.mpr (mem_compl_singleton_iff.mp hz)).analyticOnNhd
            isOpen_compl_singleton |>.mono
              fun _ hz hzw => spectrum.notMem_iff.mpr hw
                ((mem_singleton_iff.mp hzw) ▸ hz)) :=
    toGerm_eq_ofFun haU ((-1 : ℂ) • cauchyKernel U w hwU) _ _ fun z => by
      rw [← (holomorphicFunctions U).val_apply, map_smul, ContinuousMap.smul_apply,
        (holomorphicFunctions U).val_apply, cauchyKernel_apply, neg_one_smul, ← inv_neg, neg_sub]
  rw [← hgerm, map_smul, map_smul, neg_one_smul, holomorphicCalculus_toGerm,
    holomorphicCalculusOn_cauchyKernel]

/-- On an open neighbourhood `U` of `spectrum ℂ a` where a polynomial `q` does not vanish,
`holomorphicCalculusOn` evaluates `p / q` as `p(a) * Ring.inverse (q(a))` and `q(a)` is a unit. -/
theorem holomorphicCalculusOn_div_polynomial (a : A) (U : Opens ℂ) (ha : spectrum ℂ a ⊆ U)
    (p q : Polynomial ℂ) (hq : ∀ z ∈ (U : Set ℂ), q.eval z ≠ 0) :
    IsUnit (Polynomial.aeval a q) ∧
      holomorphicCalculusOn a U ha
        (of U (fun z => p.eval z / q.eval z)
          (p.differentiable.differentiableOn.div q.differentiable.differentiableOn hq)) =
        Polynomial.aeval a p * Ring.inverse (Polynomial.aeval a q) := by
  let qU := of U (fun z => q.eval z) q.differentiable.differentiableOn
  let qInv := of U (fun z => (q.eval z)⁻¹) (q.differentiable.differentiableOn.inv hq)
  have hmul₁ : qU * qInv = 1 := by
    apply Subtype.ext
    ext z
    simpa [qU, qInv] using mul_inv_cancel₀ (hq z z.property)
  have hmul₂ : qInv * qU = 1 := by rw [mul_comm, hmul₁]
  let u : Aˣ :=
    { val := Polynomial.aeval a q
      inv := holomorphicCalculusOn a U ha qInv
      val_inv := by
        rw [← holomorphicCalculusOn_polynomial a U ha q, ← map_mul, hmul₁, map_one]
      inv_val := by
        rw [← holomorphicCalculusOn_polynomial a U ha q, ← map_mul, hmul₂, map_one] }
  have hdiv : of U (fun z => p.eval z / q.eval z)
      (p.differentiable.differentiableOn.div q.differentiable.differentiableOn hq) =
      of U (fun z => p.eval z) p.differentiable.differentiableOn * qInv := by
    apply Subtype.ext
    ext z
    simp [qInv, div_eq_mul_inv]
  refine ⟨⟨u, rfl⟩, ?_⟩
  rw [hdiv, map_mul, holomorphicCalculusOn_polynomial]
  congr 1
  exact (Ring.inverse_unit u).symm

/-- For polynomials `p, q` with `q` nonvanishing on `spectrum ℂ a`, `q(a)` is a unit and the germ
calculus evaluates `p / q` as `p(a) * Ring.inverse (q(a))`. -/
theorem holomorphicCalculus_div_polynomial (a : A) (p q : Polynomial ℂ)
    (hq : ∀ z ∈ spectrum ℂ a, q.eval z ≠ 0) :
    IsUnit (Polynomial.aeval a q) ∧
      holomorphicCalculus a
        (holomorphicGerms.ofFun (fun z => p.eval z / q.eval z)
          (((p.differentiable.differentiableOn.div q.differentiable.differentiableOn
            fun _ hz => mem_ofPred.mp hz).analyticOnNhd
              (isOpen_compl_singleton.preimage q.continuous)).mono hq)) =
        Polynomial.aeval a p * Ring.inverse (Polynomial.aeval a q) := by
  let U : Opens ℂ := ⟨{z | q.eval z ≠ 0}, isOpen_compl_singleton.preimage q.continuous⟩
  have haU : spectrum ℂ a ⊆ U := fun z hz => mem_ofPred.mpr (hq z hz)
  have hqU : ∀ z ∈ (U : Set ℂ), q.eval z ≠ 0 := fun _ hz => mem_ofPred.mp hz
  obtain ⟨hu, hval⟩ := holomorphicCalculusOn_div_polynomial a U haU p q hqU
  refine ⟨hu, ?_⟩
  have hgerm : toGerm haU (of U (fun z => p.eval z / q.eval z)
      (p.differentiable.differentiableOn.div q.differentiable.differentiableOn hqU)) =
      holomorphicGerms.ofFun (fun z => p.eval z / q.eval z)
        (((p.differentiable.differentiableOn.div q.differentiable.differentiableOn
          fun _ hz => mem_ofPred.mp hz).analyticOnNhd
            (isOpen_compl_singleton.preimage q.continuous)).mono hq) :=
    toGerm_eq_ofFun haU _ _ _ fun z => of_apply _ _ z
  rw [← hgerm, holomorphicCalculus_toGerm, hval]

/-! ### Power-series evaluation -/

/-- If `spectrum ℂ a` lies in the open extended ball `Metric.eball z₀ r` and `r` does not exceed
the convergence radius of the scalar power series `∑ c_n w^n`, then `∑ ‖c_n • (a - z₀)^n‖`
converges. -/
theorem summable_norm_smul_sub_pow_of_le_radius (a : A) {c : ℕ → ℂ} {z₀ : ℂ} {r : ℝ≥0∞}
    (ha : spectrum ℂ a ⊆ Metric.eball z₀ r)
    (hr : r ≤ (FormalMultilinearSeries.ofScalars ℂ c).radius) :
    Summable fun n => ‖c n • (a - algebraMap ℂ A z₀) ^ n‖ := by
  let b := a - algebraMap ℂ A z₀
  rcases subsingleton_or_nontrivial A with hsub | hnt
  · convert summable_zero with n
    rw [Subsingleton.elim (c n • b ^ n) 0, norm_zero]
  · obtain ⟨w, hw, hw_eq⟩ := spectrum.exists_nnNorm_eq_spectralRadius b
    have hzw : z₀ + w ∈ spectrum ℂ a := by
      rw [spectrum.mem_iff] at hw ⊢
      have heq : algebraMap ℂ A (z₀ + w) - a = algebraMap ℂ A w - b := by
        dsimp [b]
        rw [map_add]
        abel
      rwa [heq]
    have hw_lt : (‖w‖₊ : ℝ≥0∞) < r := by
      have hmem := ha hzw
      rwa [Metric.mem_eball, edist_nndist, nnDist_eq_nnNorm, add_sub_cancel_left] at hmem
    have hspec : spectralRadius ℂ b < r := hw_eq ▸ hw_lt
    obtain ⟨ρ, hρ_gt, hρ_lt⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hspec
    have hgelf := (spectrum.pow_nnNorm_pow_one_div_tendsto_nhds_spectralRadius b).eventually
      (Iio_mem_nhds hρ_gt)
    obtain ⟨N, hN⟩ := eventually_atTop.mp hgelf
    have hcsum : Summable fun n => ‖c n‖ * (ρ : ℝ) ^ n := by
      simpa only [FormalMultilinearSeries.ofScalars_norm] using
        (FormalMultilinearSeries.ofScalars ℂ c).summable_norm_mul_pow (hρ_lt.trans_le hr)
    refine Summable.of_norm_bounded_eventually_nat hcsum ?_
    filter_upwards [eventually_ge_atTop (max N 1)] with n hn
    have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_of_ne_zero (by omega)).ne'
    have hbn_lt : (‖b ^ n‖₊ : ℝ≥0∞) ^ (1 / n : ℝ) ≤ ρ := (hN n (le_of_max_le_left hn)).le
    have hbn : ‖b ^ n‖ ≤ (ρ : ℝ) ^ n := by
      have hrpow := ENNReal.rpow_le_rpow hbn_lt (Nat.cast_nonneg n)
      rw [← ENNReal.rpow_mul, one_div_mul_cancel hn0, ENNReal.rpow_one,
        ENNReal.rpow_natCast, ← ENNReal.coe_pow, ENNReal.coe_le_coe] at hrpow
      exact_mod_cast hrpow
    rw [Real.norm_of_nonneg (norm_nonneg _), norm_smul]
    exact mul_le_mul_of_nonneg_left hbn (norm_nonneg _)

/-- **Power-series evaluation for the holomorphic functional calculus.** If `f` has scalar power
series `∑ c_n (z - z₀)^n` on `Metric.eball z₀ r` and `spectrum ℂ a ⊆ Metric.eball z₀ r`, then the
series `∑ c_n • (a - z₀)^n` is unconditionally summable to `holomorphicCalculus a` of `f`. -/
theorem _root_.HasFPowerSeriesOnBall.hasSum_holomorphicCalculus {f : ℂ → ℂ} {c : ℕ → ℂ}
    {z₀ : ℂ} {r : ℝ≥0∞} (hf : HasFPowerSeriesOnBall f (FormalMultilinearSeries.ofScalars ℂ c) z₀ r)
    (a : A) (ha : spectrum ℂ a ⊆ Metric.eball z₀ r) :
    HasSum (fun n => c n • (a - algebraMap ℂ A z₀) ^ n)
      (holomorphicCalculus a (holomorphicGerms.ofFun f (hf.analyticOnNhd.mono ha))) := by
  let B : Opens ℂ := ⟨Metric.eball z₀ r, Metric.isOpen_eball⟩
  let S : ℕ → holomorphicFunctions B := fun n =>
    ∑ k ∈ Finset.range n, c k • (of B id differentiableOn_id - algebraMap ℂ _ z₀) ^ k
  have hS_tendsto : Tendsto S atTop (𝓝 (of B f hf.differentiableOn)) := by
    rw [tendsto_iff_tendstoLocallyUniformlyOn]
    refine (hf.tendstoLocallyUniformlyOn'.congr fun n z hz => ?_).congr_right fun z hz => ?_
    · have hzB : z ∈ B := hz
      rw [extend_apply (S n) ⟨z, hzB⟩, ← (holomorphicFunctions B).val_apply]
      simp only [S, map_sum, map_smul, map_pow, algHom_map_sub, AlgHom.commutes,
        ContinuousMap.sum_apply, ContinuousMap.smul_apply, ContinuousMap.pow_apply,
        ContinuousMap.sub_apply, smul_eq_mul,
        FormalMultilinearSeries.partialSum, FormalMultilinearSeries.ofScalars_apply_eq]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [(holomorphicFunctions B).val_apply, of_apply]
      simp
    · have hzB : z ∈ B := hz
      rw [extend_apply _ ⟨z, hzB⟩, of_apply]
  have hcalc_tendsto :
      Tendsto (fun n => ∑ k ∈ Finset.range n, c k • (a - algebraMap ℂ A z₀) ^ k) atTop
        (𝓝 (holomorphicCalculus a (holomorphicGerms.ofFun f (hf.analyticOnNhd.mono ha)))) := by
    have hmap := ((continuous_holomorphicCalculusOn a B ha).tendsto _).comp hS_tendsto
    rw [← holomorphicCalculus_toGerm a B ha, toGerm_of] at hmap
    refine hmap.congr fun n => ?_
    simp only [Function.comp_apply, S, map_sum, map_smul, map_pow, algHom_map_sub, AlgHom.commutes,
      holomorphicCalculusOn_id]
  have hsum : Summable fun n => c n • (a - algebraMap ℂ A z₀) ^ n :=
    (summable_norm_smul_sub_pow_of_le_radius a ha hf.r_le).of_norm
  exact (tendsto_nhds_unique hsum.hasSum.tendsto_sum_nat hcalc_tendsto) ▸ hsum.hasSum

/-- Under the hypotheses of `HasFPowerSeriesOnBall.hasSum_holomorphicCalculus`, the holomorphic
calculus of `f` equals `∑' n, c n • (a - algebraMap ℂ A z₀) ^ n`. -/
theorem _root_.HasFPowerSeriesOnBall.holomorphicCalculus_eq_tsum {f : ℂ → ℂ} {c : ℕ → ℂ}
    {z₀ : ℂ} {r : ℝ≥0∞} (hf : HasFPowerSeriesOnBall f (FormalMultilinearSeries.ofScalars ℂ c) z₀ r)
    (a : A) (ha : spectrum ℂ a ⊆ Metric.eball z₀ r) :
    holomorphicCalculus a (holomorphicGerms.ofFun f (hf.analyticOnNhd.mono ha)) =
      ∑' n, c n • (a - algebraMap ℂ A z₀) ^ n :=
  (hf.hasSum_holomorphicCalculus a ha).tsum_eq.symm

/-- Centered-at-zero specialization of `HasFPowerSeriesOnBall.hasSum_holomorphicCalculus`. -/
theorem _root_.HasFPowerSeriesOnBall.hasSum_holomorphicCalculus_zero {f : ℂ → ℂ} {c : ℕ → ℂ}
    {r : ℝ≥0∞} (hf : HasFPowerSeriesOnBall f (FormalMultilinearSeries.ofScalars ℂ c) 0 r)
    (a : A) (ha : spectrum ℂ a ⊆ Metric.eball 0 r) :
    HasSum (fun n => c n • a ^ n)
      (holomorphicCalculus a (holomorphicGerms.ofFun f (hf.analyticOnNhd.mono ha))) := by
  simpa only [map_zero, sub_zero] using hf.hasSum_holomorphicCalculus a ha

/-! ### Uniqueness of the holomorphic germ functional calculus -/

namespace Contour.Cycle

/-- The open set of points off the trace of a cycle `Γ` around which `Γ` has winding number `1`. -/
def windingOneOpen (Γ : Cycle) : Opens ℂ where
  carrier := Subtype.val '' {z : {z : ℂ // z ∉ Cycle.trace Γ} | Cycle.windingNumber z Γ = 1}
  is_open' := (Cycle.isCompact_trace Γ).isClosed.isOpen_compl.isOpenMap_subtype_val _
    ((Cycle.isLocallyConstant_windingNumber Γ).isOpen_fiber 1)

/-- Membership in `windingOneOpen Γ` means avoiding `trace Γ` with winding number `1`. -/
@[simp]
theorem mem_windingOneOpen {Γ : Cycle} {z : ℂ} :
    z ∈ windingOneOpen Γ ↔ z ∉ Cycle.trace Γ ∧ Cycle.windingNumber z Γ = 1 := by
  constructor
  · rintro ⟨⟨z, hz⟩, hw, rfl⟩
    exact ⟨hz, hw⟩
  · rintro ⟨hz, hw⟩
    exact ⟨⟨z, hz⟩, hw, rfl⟩

end Contour.Cycle

/-- If a continuous `ℂ`-algebra homomorphism `Φ : holomorphicFunctions V →ₐ[ℂ] A` sends `id` to
`a`, and `V ≤ U` lies inside a null-homologous cycle `Γ` in `U` avoiding `V` with winding number
`1` on `V`, then `Φ ∘ restrict hVU = holomorphicCalculusOn a U _`. -/
theorem algHom_eq_holomorphicCalculusOn_of_cycle {a : A} {U V : Opens ℂ}
    (ha : spectrum ℂ a ⊆ V) (hVU : V ≤ U) {Γ : Cycle} (hΓ : Γ.IsIn U)
    (hn : Γ.IsNullHomologous U) (hdisj : Disjoint (V : Set ℂ) (Cycle.trace Γ))
    (hw : ∀ z ∈ (V : Set ℂ), Cycle.windingNumber z Γ = 1)
    (Φ : holomorphicFunctions V →ₐ[ℂ] A) (hΦ : Continuous Φ)
    (hid : Φ (of V id differentiableOn_id) = a) (f : holomorphicFunctions U) :
    Φ (restrict hVU f) = holomorphicCalculusOn a U (ha.trans hVU) f := by
  have hker : ∀ (w : ℂ) (hwΓ : w ∈ Cycle.trace Γ),
      Φ (cauchyKernel V w (disjoint_right.mp hdisj hwΓ)) =
        holomorphicCalculusOn a V ha (cauchyKernel V w (disjoint_right.mp hdisj hwΓ)) := by
    intro w hwΓ
    rw [algHom_cauchyKernel_eq_resolvent Φ hid, holomorphicCalculusOn_cauchyKernel]
  have hriem := tendsto_cauchyIntegralRiemannSum f hVU hΓ hn hdisj hw
  have h₁ := (hΦ.tendsto (restrict hVU f)).comp hriem
  have h₂ := ((continuous_holomorphicCalculusOn a V ha).tendsto (restrict hVU f)).comp hriem
  have heq : Φ ∘ cauchyIntegralRiemannSum f Γ V hdisj =
      holomorphicCalculusOn a V ha ∘ cauchyIntegralRiemannSum f Γ V hdisj :=
    funext fun n => algHom_cauchyIntegralRiemannSum_eq Φ (holomorphicCalculusOn a V ha)
      f Γ hdisj hker n
  rw [heq] at h₁
  exact (tendsto_nhds_unique h₁ h₂).trans (holomorphicCalculusOn_restrict a ha hVU f)

/-- **Uniqueness of the holomorphic functional calculus.** Any unital `ℂ`-algebra homomorphism from
`holomorphicGerms (spectrum ℂ a)` to `A` sending the coordinate germ to `a` whose pullback to every
open neighbourhood of `spectrum ℂ a` is continuous equals `holomorphicCalculus a`. -/
theorem holomorphicCalculus_unique (a : A) (Ψ : holomorphicGerms (spectrum ℂ a) →ₐ[ℂ] A)
    (hid : Ψ (holomorphicGerms.ofFun id analyticOnNhd_id) = a)
    (hcont : ∀ (U : Opens ℂ) (ha : spectrum ℂ a ⊆ U), Continuous (Ψ.comp (toGerm ha))) :
    Ψ = holomorphicCalculus a := by
  ext U ha f
  obtain ⟨Γ, hΓ, hn, hw⟩ := (spectrum.isCompact a).exists_cycle_windingNumber_eq_one U.isOpen ha
  let V : Opens ℂ := U ⊓ Cycle.windingOneOpen Γ
  have hVU : V ≤ U := inf_le_left
  have haV : spectrum ℂ a ⊆ V := fun z hz =>
    ⟨ha hz, Cycle.mem_windingOneOpen.mpr ⟨fun ht => (Cycle.isIn_iff.mp hΓ ht).2 hz, hw z hz⟩⟩
  have hΓU : Γ.IsIn U := Cycle.isIn_iff.mpr fun z hz => (Cycle.isIn_iff.mp hΓ hz).1
  have hdisj : Disjoint (V : Set ℂ) (Cycle.trace Γ) :=
    disjoint_left.mpr fun z hz => (Cycle.mem_windingOneOpen.mp hz.2).1
  have hwV : ∀ z ∈ (V : Set ℂ), Cycle.windingNumber z Γ = 1 :=
    fun z hz => (Cycle.mem_windingOneOpen.mp hz.2).2
  have hidV : (Ψ.comp (toGerm haV)) (of V id differentiableOn_id) = a := by
    simpa only [AlgHom.comp_apply, toGerm_of] using hid
  have key := algHom_eq_holomorphicCalculusOn_of_cycle haV hVU hΓU hn hdisj hwV
    (Ψ.comp (toGerm haV)) (hcont V haV) hidV f
  simpa only [AlgHom.comp_apply, toGerm_restrict, holomorphicCalculus_toGerm] using key

/-- Existence and uniqueness of the continuous holomorphic germ functional calculus at `a`. -/
theorem existsUnique_holomorphicCalculus (a : A) :
    ∃! Ψ : holomorphicGerms (spectrum ℂ a) →ₐ[ℂ] A,
      Ψ (holomorphicGerms.ofFun id analyticOnNhd_id) = a ∧
        ∀ (U : Opens ℂ) (ha : spectrum ℂ a ⊆ U), Continuous (Ψ.comp (toGerm ha)) := by
  refine ⟨holomorphicCalculus a, ⟨holomorphicCalculus_id a, fun U ha => ?_⟩, fun Ψ hΨ =>
    holomorphicCalculus_unique a Ψ hΨ.1 hΨ.2⟩
  have hcomp : (holomorphicCalculus a).comp (toGerm ha) = holomorphicCalculusOn a U ha := by
    ext f
    exact holomorphicCalculus_toGerm a U ha f
  rw [hcomp]
  exact continuous_holomorphicCalculusOn a U ha

end BanachAlgebra

end TauCeti
