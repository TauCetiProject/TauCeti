/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.ChangeOrigin
public import TauCeti.Analysis.Complex.HolomorphicFunctions.CauchyKernel
public import TauCeti.Analysis.Normed.Algebra.HolomorphicFunctionalCalculus.Basic
import TauCeti.Analysis.Contour.Cycle.Winding
import TauCeti.Analysis.Normed.Algebra.GelfandRadius

/-!
# Uniqueness, rational functions, and power series in the holomorphic functional calculus

Let `A` be a complex Banach algebra and `a : A`. By the algebraic evaluation lemmas in
`TauCeti.Analysis.Complex.HolomorphicFunctions.CauchyKernel`, any unital `ℂ`-algebra homomorphism
out of `holomorphicFunctions V` sending `id` to `a` sends every Cauchy kernel `(w - ·)⁻¹` with
`w ∉ V` to `resolvent a w` and evaluates rational functions `p / q` (with `q` nonvanishing on `V`)
as `Polynomial.aeval a p * Ring.inverse (Polynomial.aeval a q)`. In particular, this applies to
`holomorphicCalculusOn a` and `holomorphicCalculus a`.

Combining Cauchy-kernel evaluation with Riemann-sum approximation of Cauchy's integral formula
(`HolomorphicFunctions.tendsto_cauchyIntegralRiemannSum`) proves that `holomorphicCalculus a` is
the **unique** unital `ℂ`-algebra homomorphism from `holomorphicGerms (spectrum ℂ a)` to `A`
sending the coordinate germ to `a` whose restriction to every open neighbourhood of `spectrum ℂ a`
is continuous for the compact-open topology.

Furthermore, if `f` has a formal power series `p : FormalMultilinearSeries ℂ ℂ ℂ` on an open
extended ball `Metric.eball z₀ r` containing `spectrum ℂ a`,
`TauCeti.summable_norm_smul_sub_pow_of_le_radius` ensures absolute convergence of
`∑ p.coeff n • (a - z₀)^n` in `A`, and continuity of `holomorphicCalculusOn` identifies
`holomorphicCalculus a` of `f` with that unconditional sum.

## Main results

* `TauCeti.holomorphicCalculusOn_cauchyKernel`, `TauCeti.holomorphicCalculus_inv_const_sub_id`,
  `TauCeti.holomorphicCalculus_inv_id_sub_const`: evaluation on Cauchy kernels.
* `TauCeti.isUnit_aeval_of_forall_eval_ne_zero`, `TauCeti.holomorphicCalculusOn_div_polynomial`,
  `TauCeti.holomorphicCalculus_div_polynomial`: invertibility of polynomial denominators
  nonvanishing on the spectrum and compatibility with rational functions `p / q`.
* `HasFPowerSeriesOnBall.hasSum_holomorphicCalculus`,
  `HasFPowerSeriesOnBall.holomorphicCalculus_eq_tsum`,
  `HasFPowerSeriesOnBall.hasSum_holomorphicCalculus_zero`: unconditional norm-convergent
  power-series evaluation when `spectrum ℂ a ⊆ Metric.eball z₀ r`.
* `TauCeti.algHom_restrict_eq_holomorphicCalculusOn_of_cycle`, `TauCeti.holomorphicCalculus_unique`,
  `TauCeti.existsUnique_holomorphicCalculus`: uniqueness of the holomorphic germ functional
  calculus from continuity on open neighbourhoods.

## References

* H. G. Dales, *Banach Algebras and Automatic Continuity*, Theorem 2.4.9.
* J. B. Conway, *A Course in Functional Analysis*, second edition, Theorem VII.4.10.
* W. Rudin, *Functional Analysis*, second edition, Theorem 10.27.
-/

public noncomputable section

open Complex Filter Set TopologicalSpace Topology
open scoped ENNReal Real

namespace TauCeti

open Contour HolomorphicFunctions

section BanachAlgebra

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

/-- On an open neighbourhood `U` of the spectrum, the holomorphic calculus sends the Cauchy kernel
`(w - ·)⁻¹` with `w ∉ U` to `resolvent a w`. -/
@[simp]
theorem holomorphicCalculusOn_cauchyKernel (a : A) (U : Opens ℂ) (ha : spectrum ℂ a ⊆ U)
    (w : ℂ) (hw : w ∉ (U : Set ℂ)) :
    holomorphicCalculusOn a U ha (cauchyKernel U w hw) = resolvent a w :=
  map_cauchyKernel_eq_resolvent (holomorphicCalculusOn a U ha)
    (holomorphicCalculusOn_id a U ha) hw

/-- The germ calculus sends `(w - ·)⁻¹` to `resolvent a w` whenever `(w - ·)⁻¹` is analytic on
`spectrum ℂ a`. -/
@[simp]
theorem holomorphicCalculus_inv_const_sub_id (a : A) {w : ℂ}
    (hf : AnalyticOnNhd ℂ (fun z => (w - z)⁻¹) (spectrum ℂ a)) :
    holomorphicCalculus a (holomorphicGerms.ofFun (fun z => (w - z)⁻¹) hf) = resolvent a w := by
  let U : Opens ℂ := ⟨{w}ᶜ, isOpen_compl_singleton⟩
  have haU : spectrum ℂ a ⊆ U := fun z hz hzw => by
    have hzw' : z = w := mem_singleton_iff.mp hzw
    subst hzw'
    have hinv : ContinuousAt (Inv.inv : ℂ → ℂ) 0 := by
      have hcomp := (hf z hz).continuousAt.comp_of_eq
        (continuousAt_const.sub continuousAt_id : ContinuousAt (fun t : ℂ => z - t) 0)
        (sub_zero z)
      simpa only [Function.comp_def, Pi.sub_apply, sub_sub_cancel] using hcomp
    exact NormedField.continuousAt_inv.mp hinv rfl
  have hwU : w ∉ (U : Set ℂ) := not_not_intro (mem_singleton w)
  rw [← toGerm_eq_ofFun haU (cauchyKernel U w hwU) _ hf (cauchyKernel_apply U w hwU),
    holomorphicCalculus_toGerm, holomorphicCalculusOn_cauchyKernel]

/-- The germ calculus sends `(· - w)⁻¹` to `-resolvent a w` whenever `(· - w)⁻¹` is analytic on
`spectrum ℂ a`. -/
@[simp]
theorem holomorphicCalculus_inv_id_sub_const (a : A) {w : ℂ}
    (hf : AnalyticOnNhd ℂ (fun z => (z - w)⁻¹) (spectrum ℂ a)) :
    holomorphicCalculus a (holomorphicGerms.ofFun (fun z => (z - w)⁻¹) hf) = -resolvent a w := by
  have heq : (fun z => (z - w)⁻¹) = -fun z => (w - z)⁻¹ := by
    ext z
    simp [← inv_neg, neg_sub]
  have hf' : AnalyticOnNhd ℂ (fun z => (w - z)⁻¹) (spectrum ℂ a) := by
    simpa [heq] using hf.neg
  have hneg : holomorphicGerms.ofFun (fun z => (z - w)⁻¹) hf =
      -holomorphicGerms.ofFun (fun z => (w - z)⁻¹) hf' := by
    apply Subtype.ext
    simp [heq, Germ.coe_neg]
  rw [hneg, map_neg, holomorphicCalculus_inv_const_sub_id a hf']

/-- If a polynomial `q` does not vanish on `spectrum ℂ a`, then `Polynomial.aeval a q` is a unit
in `A`. -/
theorem isUnit_aeval_of_forall_eval_ne_zero (a : A) (q : Polynomial ℂ)
    (hq : ∀ z ∈ spectrum ℂ a, q.eval z ≠ 0) :
    IsUnit (Polynomial.aeval a q) := by
  let U : Opens ℂ := ⟨{z | q.eval z ≠ 0}, isOpen_compl_singleton.preimage q.continuous⟩
  exact isUnit_aeval_of_map_id (holomorphicCalculusOn a U hq)
    (holomorphicCalculusOn_id a U hq) q fun _ hz => hz

/-- On an open neighbourhood `U` of `spectrum ℂ a` where a polynomial `q` does not vanish,
`holomorphicCalculusOn` evaluates `p / q` as
`Polynomial.aeval a p * Ring.inverse (Polynomial.aeval a q)`. -/
theorem holomorphicCalculusOn_div_polynomial (a : A) (U : Opens ℂ) (ha : spectrum ℂ a ⊆ U)
    (p q : Polynomial ℂ) (hq : ∀ z ∈ (U : Set ℂ), q.eval z ≠ 0) :
    holomorphicCalculusOn a U ha
        (of U (fun z => p.eval z / q.eval z)
          (p.differentiable.differentiableOn.div q.differentiable.differentiableOn hq)) =
      Polynomial.aeval a p * Ring.inverse (Polynomial.aeval a q) :=
  map_of_div_polynomial (holomorphicCalculusOn a U ha) (holomorphicCalculusOn_id a U ha) p q hq

/-- For polynomials `p, q` with `q` nonvanishing on `spectrum ℂ a`, the germ calculus evaluates
`p / q` as `Polynomial.aeval a p * Ring.inverse (Polynomial.aeval a q)`. -/
theorem holomorphicCalculus_div_polynomial (a : A) (p q : Polynomial ℂ)
    (hq : ∀ z ∈ spectrum ℂ a, q.eval z ≠ 0) :
    holomorphicCalculus a
        (holomorphicGerms.ofFun (fun z => p.eval z / q.eval z)
          (((AnalyticOnNhd.eval_polynomial p).mono (subset_univ _)).div
            ((AnalyticOnNhd.eval_polynomial q).mono (subset_univ _)) hq)) =
      Polynomial.aeval a p * Ring.inverse (Polynomial.aeval a q) := by
  let U : Opens ℂ := ⟨{z | q.eval z ≠ 0}, isOpen_compl_singleton.preimage q.continuous⟩
  have haU : spectrum ℂ a ⊆ U := hq
  have hqU : ∀ z ∈ (U : Set ℂ), q.eval z ≠ 0 := fun _ hz => hz
  rw [← toGerm_eq_ofFun haU
      (of U (fun z => p.eval z / q.eval z)
        (p.differentiable.differentiableOn.div q.differentiable.differentiableOn hqU))
      _ _ (of_apply _ _),
    holomorphicCalculus_toGerm, holomorphicCalculusOn_div_polynomial a U haU p q hqU]

/-! ### Power-series evaluation -/

/-- **Power-series evaluation for the holomorphic functional calculus.** If `f` has formal power
series `p` on `Metric.eball z₀ r` and `spectrum ℂ a ⊆ Metric.eball z₀ r`, then the series
`∑ p.coeff n • (a - z₀)^n` is unconditionally summable to `holomorphicCalculus a` of `f`. -/
theorem _root_.HasFPowerSeriesOnBall.hasSum_holomorphicCalculus {f : ℂ → ℂ}
    {p : FormalMultilinearSeries ℂ ℂ ℂ} {z₀ : ℂ} {r : ℝ≥0∞}
    (hf : HasFPowerSeriesOnBall f p z₀ r) (a : A) (ha : spectrum ℂ a ⊆ Metric.eball z₀ r) :
    HasSum (fun n => p.coeff n • (a - algebraMap ℂ A z₀) ^ n)
      (holomorphicCalculus a (holomorphicGerms.ofFun f (hf.analyticOnNhd.mono ha))) := by
  let B : Opens ℂ := ⟨Metric.eball z₀ r, Metric.isOpen_eball⟩
  let S : ℕ → holomorphicFunctions B := fun n =>
    ∑ k ∈ Finset.range n, p.coeff k • (of B id differentiableOn_id - algebraMap ℂ _ z₀) ^ k
  have hS_tendsto : Tendsto S atTop (𝓝 (of B f hf.differentiableOn)) := by
    rw [tendsto_iff_tendstoLocallyUniformlyOn]
    refine (hf.tendstoLocallyUniformlyOn'.congr fun n z hz => ?_).congr_right fun z hz => ?_
    · have hzB : z ∈ B := hz
      rw [extend_apply (S n) ⟨z, hzB⟩, ← (holomorphicFunctions B).val_apply]
      simp only [S, map_sum, map_smul, map_pow, map_sub (holomorphicFunctions B).val,
        AlgHom.commutes, ContinuousMap.sum_apply, ContinuousMap.smul_apply,
        ContinuousMap.pow_apply, ContinuousMap.sub_apply, smul_eq_mul,
        FormalMultilinearSeries.partialSum, FormalMultilinearSeries.apply_eq_pow_smul_coeff]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [(holomorphicFunctions B).val_apply, of_apply]
      simp [mul_comm]
    · have hzB : z ∈ B := hz
      exact (extend_of hf.differentiableOn hzB).symm
  have hcalc_tendsto :
      Tendsto (fun n => ∑ k ∈ Finset.range n, p.coeff k • (a - algebraMap ℂ A z₀) ^ k) atTop
        (𝓝 (holomorphicCalculus a (holomorphicGerms.ofFun f (hf.analyticOnNhd.mono ha)))) := by
    have hmap := ((continuous_holomorphicCalculusOn a B ha).tendsto _).comp hS_tendsto
    rw [← holomorphicCalculus_toGerm a B ha, toGerm_of] at hmap
    refine hmap.congr fun n => ?_
    simp only [Function.comp_apply, S, map_sum, map_smul, map_pow,
      map_sub (holomorphicCalculusOn a B ha), AlgHom.commutes, holomorphicCalculusOn_id]
  have hsum : Summable fun n => p.coeff n • (a - algebraMap ℂ A z₀) ^ n :=
    (summable_norm_smul_sub_pow_of_le_radius a ha hf.r_le).of_norm
  exact (tendsto_nhds_unique hsum.hasSum.tendsto_sum_nat hcalc_tendsto) ▸ hsum.hasSum

/-- Under the hypotheses of `HasFPowerSeriesOnBall.hasSum_holomorphicCalculus`, the holomorphic
calculus of `f` equals `∑' n, p.coeff n • (a - algebraMap ℂ A z₀) ^ n`. -/
theorem _root_.HasFPowerSeriesOnBall.holomorphicCalculus_eq_tsum {f : ℂ → ℂ}
    {p : FormalMultilinearSeries ℂ ℂ ℂ} {z₀ : ℂ} {r : ℝ≥0∞}
    (hf : HasFPowerSeriesOnBall f p z₀ r) (a : A) (ha : spectrum ℂ a ⊆ Metric.eball z₀ r) :
    holomorphicCalculus a (holomorphicGerms.ofFun f (hf.analyticOnNhd.mono ha)) =
      ∑' n, p.coeff n • (a - algebraMap ℂ A z₀) ^ n :=
  (hf.hasSum_holomorphicCalculus a ha).tsum_eq.symm

/-- Centered-at-zero specialization of `HasFPowerSeriesOnBall.hasSum_holomorphicCalculus`. -/
theorem _root_.HasFPowerSeriesOnBall.hasSum_holomorphicCalculus_zero {f : ℂ → ℂ}
    {p : FormalMultilinearSeries ℂ ℂ ℂ} {r : ℝ≥0∞}
    (hf : HasFPowerSeriesOnBall f p 0 r) (a : A) (ha : spectrum ℂ a ⊆ Metric.eball 0 r) :
    HasSum (fun n => p.coeff n • a ^ n)
      (holomorphicCalculus a (holomorphicGerms.ofFun f (hf.analyticOnNhd.mono ha))) := by
  simpa only [map_zero, sub_zero] using hf.hasSum_holomorphicCalculus a ha

/-! ### Uniqueness of the holomorphic germ functional calculus -/

/-- If a continuous unital `ℂ`-algebra homomorphism `Φ` out of `holomorphicFunctions V` into `A`
sends `id` to `a`, and `V ≤ U` lies inside a null-homologous cycle `Γ` in `U` avoiding `V` with
winding number `1` on `V`, then `Φ (restrict hVU f)` agrees with
`holomorphicCalculusOn a U _ f`. -/
theorem algHom_restrict_eq_holomorphicCalculusOn_of_cycle {a : A} {U V : Opens ℂ} {F : Type*}
    [FunLike F (holomorphicFunctions V) A] [AlgHomClass F ℂ (holomorphicFunctions V) A]
    (hVU : V ≤ U) {Γ : Cycle} (hΓ : Γ.IsIn U)
    (hn : Γ.IsNullHomologous U) (hdisj : Disjoint (V : Set ℂ) (Cycle.trace Γ))
    (hw : ∀ z ∈ (V : Set ℂ), Cycle.windingNumber z Γ = 1)
    (Φ : F) (hΦ : Continuous Φ)
    (hid : Φ (of V id differentiableOn_id) = a) (f : holomorphicFunctions U) :
    Φ (restrict hVU f) =
      holomorphicCalculusOn a U ((spectrum_subset_of_map_id Φ hid).trans hVU) f := by
  have ha : spectrum ℂ a ⊆ V := spectrum_subset_of_map_id Φ hid
  have hker : ∀ (w : ℂ) (hwΓ : w ∈ Cycle.trace Γ),
      Φ (cauchyKernel V w (disjoint_right.mp hdisj hwΓ)) =
        holomorphicCalculusOn a V ha (cauchyKernel V w (disjoint_right.mp hdisj hwΓ)) := by
    intro w hwΓ
    rw [map_cauchyKernel_eq_resolvent Φ hid, holomorphicCalculusOn_cauchyKernel]
  have hriem := tendsto_cauchyIntegralRiemannSum f hVU hΓ hn hdisj hw
  have h₁ := (hΦ.tendsto (restrict hVU f)).comp hriem
  have h₂ := ((continuous_holomorphicCalculusOn a V ha).tendsto (restrict hVU f)).comp hriem
  have heq : Φ ∘ cauchyIntegralRiemannSum f Γ V hdisj =
      holomorphicCalculusOn a V ha ∘ cauchyIntegralRiemannSum f Γ V hdisj :=
    funext fun n => map_cauchyIntegralRiemannSum_eq Φ (holomorphicCalculusOn a V ha)
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
  have key := algHom_restrict_eq_holomorphicCalculusOn_of_cycle hVU hΓU hn hdisj hwV
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
