/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.ChangeOrigin
public import Mathlib.Analysis.Calculus.DSlope
public import Mathlib.Analysis.Calculus.FDeriv.Analytic
public import Mathlib.Analysis.Normed.Algebra.GelfandFormula
public import Mathlib.Analysis.Normed.Group.InfiniteSum
public import TauCeti.Analysis.Normed.Algebra.HolomorphicFunctionalCalculus.Basic
public import TauCeti.Analysis.Normed.Algebra.Unitization.Basic

/-!
# Spectral mapping, series, and naturality for the holomorphic functional calculus

Let `a` be an element of a complex Banach algebra `A`. Building on `TauCeti.holomorphicCalculus`,
this file establishes the algebraic, analytic, functorial, and spectral properties of `f(a)`:

* **Commutation**: every element commuting with `a` commutes with `f(a)`, and values of the
  calculus at commuting elements commute with one another.
* **Resolvent kernels and rational functions**: any unital complex-algebra homomorphism on
  `holomorphicGerms (spectrum ℂ a)` sending the coordinate germ to `a` maps `(w - ·)⁻¹` to
  `resolvent a w` for `w ∈ resolventSet ℂ a`; in particular `holomorphicCalculus a` agrees with
  rational evaluation `p(a) q(a)⁻¹` whenever `q` has no zeros on `spectrum ℂ a`.
* **Convergent power series**: if `f` has power series `p` on an open extended ball around `z₀`
  containing `spectrum ℂ a`, then `∑ p.coeff k • (a - z₀ 1) ^ k` converges unconditionally in norm
  to `f(a)`.
* **Naturality and nonunital algebras**: continuous unital algebra homomorphisms commute with
  `holomorphicCalculus` (restricting germs along spectral inclusion). On `ℂ`, the calculus is
  point evaluation; applying naturality to the scalar augmentation of the `ℓ¹` unitization of a
  nonunital Banach algebra shows that the unitized calculus of `a` at `f` lies in `A` if and only
  if `f(0) = 0`.
* **Spectral mapping theorem**: `spectrum ℂ (holomorphicCalculus a g) = spectrum ℂ g`, so for any
  representative `f` analytic near `spectrum ℂ a`, `σ(f(a)) = f(σ(a))` (including the zero
  algebra, where both sides are empty).

## References

* H. G. Dales, *Banach Algebras and Automatic Continuity*, §2.4, Theorem 2.4.4 and Corollary 2.4.5.
* J. B. Conway, *A Course in Functional Analysis*, second edition, VII.4, Theorems 4.7 and 4.10.
-/

public noncomputable section

open Complex Filter Set TopologicalSpace Topology
open scoped ENNReal NNReal Real

section Commute

open TauCeti TauCeti.Contour TauCeti.HolomorphicFunctions

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

/-- Every element commuting with `a` commutes with `holomorphicCalculusOn a U ha f`. -/
theorem Commute.holomorphicCalculusOn_right {a b : A} (hb : Commute b a) (U : Opens ℂ)
    (ha : spectrum ℂ a ⊆ U) (f : holomorphicFunctions U) :
    Commute b (holomorphicCalculusOn a U ha f) := by
  obtain ⟨Γ, hΓ, hn, hw⟩ := (spectrum.isCompact a).exists_cycle_windingNumber_eq_one U.isOpen ha
  rw [holomorphicCalculusOn_eq_integral a U ha f Γ hΓ hn hw]
  exact (hb.integral_smul_resolvent_right
    ((differentiableOn_extend f).continuousOn.mono fun _ hz ↦ (Cycle.isIn_iff.mp hΓ hz).1)
    (Cycle.isIn_iff.mpr fun _ hz ↦ spectrum.notMem_iff.mp (Cycle.isIn_iff.mp hΓ hz).2)).smul_right _

/-- Every element commuting with `a` commutes with `holomorphicCalculus a g`. -/
theorem Commute.holomorphicCalculus_right {a b : A} (hb : Commute b a)
    (g : holomorphicGerms (spectrum ℂ a)) :
    Commute b (holomorphicCalculus a g) := by
  obtain ⟨U, ha, f, rfl⟩ := holomorphicGerms.exists_toGerm_eq g
  rw [holomorphicCalculus_toGerm]
  exact hb.holomorphicCalculusOn_right U ha f

/-- Functions of commuting Banach-algebra elements under the holomorphic calculus commute. -/
theorem Commute.holomorphicCalculus {a b : A} (hab : Commute a b)
    (f : holomorphicGerms (spectrum ℂ a)) (g : holomorphicGerms (spectrum ℂ b)) :
    Commute (holomorphicCalculus a f) (holomorphicCalculus b g) :=
  ((hab.holomorphicCalculus_right g).symm.holomorphicCalculus_right f).symm

end Commute

namespace AlgHom

open TauCeti TauCeti.Contour TauCeti.HolomorphicFunctions

/-- Continuous unital complex-algebra homomorphisms preserve `holomorphicCalculusOn`. -/
theorem map_holomorphicCalculusOn {F A B : Type*} [NormedRing A] [NormedAlgebra ℂ A]
    [CompleteSpace A] [NormedRing B] [NormedAlgebra ℂ B] [CompleteSpace B]
    [FunLike F A B] [AlgHomClass F ℂ A B] (φ : F) (hφ : Continuous φ) (a : A)
    (U : Opens ℂ) (ha : spectrum ℂ a ⊆ U) (f : holomorphicFunctions U) :
    φ (holomorphicCalculusOn a U ha f) =
      holomorphicCalculusOn (φ a) U ((AlgHom.spectrum_apply_subset φ a).trans ha) f := by
  let L : A →L[ℂ] B := { (AlgHom.ofClass φ).toLinearMap with cont := hφ }
  have hL : ∀ x, L x = φ x := fun _ ↦ rfl
  have hsub : spectrum ℂ (φ a) ⊆ spectrum ℂ a := AlgHom.spectrum_apply_subset φ a
  obtain ⟨Γ, hΓ, hn, hw⟩ := (spectrum.isCompact a).exists_cycle_windingNumber_eq_one U.isOpen ha
  have hΓB : Γ.IsIn (U \ spectrum ℂ (φ a)) := Cycle.isIn_iff.mpr fun z hz ↦
    ⟨(Cycle.isIn_iff.mp hΓ hz).1, fun hzB ↦ (Cycle.isIn_iff.mp hΓ hz).2 (hsub hzB)⟩
  have hR : Γ.IsIn (resolventSet ℂ a) :=
    Cycle.isIn_iff.mpr fun _ hz ↦ spectrum.notMem_iff.mp (Cycle.isIn_iff.mp hΓ hz).2
  have hcont : ContinuousOn (fun z ↦ extend f z • resolvent a z) (Cycle.trace Γ) :=
    ((differentiableOn_extend f).continuousOn.mono
      fun _ hz ↦ (Cycle.isIn_iff.mp hΓ hz).1).smul (Cycle.continuousOn_resolvent hR)
  have hcomm := Cycle.integral_comp_comm (f := fun z ↦ extend f z • resolvent a z)
    (fun _ ↦ Cycle.intervalIntegrable_of_mem_support hcont) L
  rw [holomorphicCalculusOn_eq_integral a U ha f Γ hΓ hn hw,
    holomorphicCalculusOn_eq_integral (φ a) U (hsub.trans ha) f Γ hΓB hn
      (fun z hz ↦ hw z (hsub hz)),
    ← hL, L.map_smul, ← hcomm]
  congr 1
  refine Cycle.integral_congr fun z hz ↦ ?_
  rw [hL, map_smul, AlgHom.map_resolvent φ (Cycle.isIn_iff.mp hR hz)]

/-- Continuous unital complex-algebra homomorphisms preserve `holomorphicCalculus`, restricting the
germ from `spectrum ℂ a` to `spectrum ℂ (φ a)`. -/
theorem map_holomorphicCalculus {F A B : Type*} [NormedRing A] [NormedAlgebra ℂ A]
    [CompleteSpace A] [NormedRing B] [NormedAlgebra ℂ B] [CompleteSpace B]
    [FunLike F A B] [AlgHomClass F ℂ A B] (φ : F) (hφ : Continuous φ) (a : A)
    (g : holomorphicGerms (spectrum ℂ a)) :
    φ (holomorphicCalculus a g) =
      holomorphicCalculus (φ a)
        (holomorphicGerms.restrict (AlgHom.spectrum_apply_subset φ a) g) := by
  obtain ⟨U, ha, f, rfl⟩ := holomorphicGerms.exists_toGerm_eq g
  rw [holomorphicCalculus_toGerm, restrict_toGerm, holomorphicCalculus_toGerm]
  exact AlgHom.map_holomorphicCalculusOn φ hφ a U ha f

end AlgHom

namespace ContinuousAlgHom

open TauCeti TauCeti.HolomorphicFunctions

variable {A B : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]
  [NormedRing B] [NormedAlgebra ℂ B] [CompleteSpace B]

/-- Continuous unital algebra homomorphisms commute with `holomorphicCalculusOn`. -/
@[simp]
theorem map_holomorphicCalculusOn (φ : A →A[ℂ] B) (a : A) (U : Opens ℂ)
    (ha : spectrum ℂ a ⊆ U) (f : holomorphicFunctions U) :
    φ (holomorphicCalculusOn a U ha f) =
      holomorphicCalculusOn (φ a) U ((AlgHom.spectrum_apply_subset φ a).trans ha) f :=
  AlgHom.map_holomorphicCalculusOn φ φ.continuous a U ha f

/-- Continuous unital algebra homomorphisms commute with `holomorphicCalculus`. -/
@[simp]
theorem map_holomorphicCalculus (φ : A →A[ℂ] B) (a : A)
    (g : holomorphicGerms (spectrum ℂ a)) :
    φ (holomorphicCalculus a g) =
      holomorphicCalculus (φ a)
        (holomorphicGerms.restrict (AlgHom.spectrum_apply_subset φ a) g) :=
  AlgHom.map_holomorphicCalculus φ φ.continuous a g

end ContinuousAlgHom

namespace TauCeti

open Contour HolomorphicFunctions

section ResolventKernel

/-- For `w` in the resolvent set of `a`, the Cauchy kernel `z ↦ (w - z)⁻¹` is analytic on a
neighbourhood of `spectrum ℂ a`. -/
theorem analyticOnNhd_sub_inv {A : Type*} [Ring A] [Algebra ℂ A] {a : A} {w : ℂ}
    (hw : w ∈ resolventSet ℂ a) :
    AnalyticOnNhd ℂ (fun z ↦ (w - z)⁻¹) (spectrum ℂ a) := fun z hz ↦
  (analyticAt_const.sub analyticAt_id).inv <| sub_ne_zero.mpr fun (h : w = z) ↦
    spectrum.mem_iff.mp (h ▸ hz) (spectrum.mem_resolventSet_iff.mp hw)

/-- Any unital complex-algebra homomorphism on `holomorphicGerms (spectrum ℂ a)` sending the
coordinate germ to `a` maps the Cauchy kernel `(w - ·)⁻¹` to `resolvent a w` for every
`w ∈ resolventSet ℂ a`. -/
theorem algHom_ofFun_sub_inv_eq_resolvent {A : Type*} [Ring A] [Algebra ℂ A] {a : A}
    (Φ : holomorphicGerms (spectrum ℂ a) →ₐ[ℂ] A)
    (hid : Φ (holomorphicGerms.ofFun id analyticOnNhd_id) = a)
    {w : ℂ} (hw : w ∈ resolventSet ℂ a) :
    Φ (holomorphicGerms.ofFun (fun z ↦ (w - z)⁻¹) (analyticOnNhd_sub_inv hw)) =
      resolvent a w := by
  let k := holomorphicGerms.ofFun (fun z ↦ (w - z)⁻¹) (analyticOnNhd_sub_inv hw)
  have hmul : (algebraMap ℂ (holomorphicGerms (spectrum ℂ a)) w -
      holomorphicGerms.ofFun id analyticOnNhd_id) * k = 1 := by
    apply Subtype.ext
    rw [Subalgebra.coe_mul, Subalgebra.coe_sub, Subalgebra.coe_one, Subalgebra.coe_algebraMap,
      Germ.algebraMap_eq, holomorphicGerms.coe_ofFun, holomorphicGerms.coe_ofFun, ← Germ.coe_sub,
      ← Germ.coe_mul, ← Germ.coe_one]
    apply Germ.coe_eq.mpr
    apply eventually_nhdsSet_iff_forall.mpr fun z hz ↦ ?_
    have hne : w - z ≠ 0 := sub_ne_zero.mpr fun (h : w = z) ↦
      spectrum.mem_iff.mp (h ▸ hz) (spectrum.mem_resolventSet_iff.mp hw)
    filter_upwards [(continuousAt_const.sub continuousAt_id).eventually_ne hne] with u hu
    exact mul_inv_cancel₀ hu
  have hΦ := congrArg Φ hmul
  rw [map_mul, map_sub, AlgHom.commutes, hid, map_one] at hΦ
  calc Φ k = 1 * Φ k := (one_mul _).symm
    _ = (resolvent a w * (algebraMap ℂ A w - a)) * Φ k := by
        rw [resolvent, Ring.inverse_mul_cancel _ (spectrum.mem_resolventSet_iff.mp hw)]
    _ = resolvent a w * ((algebraMap ℂ A w - a) * Φ k) := mul_assoc _ _ _
    _ = resolvent a w := by rw [hΦ, mul_one]

end ResolventKernel

section CalculusProperties

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

/-- The holomorphic germ calculus maps `(w - ·)⁻¹` to `resolvent a w` on the resolvent set. -/
@[simp]
theorem holomorphicCalculus_sub_inv (a : A) {w : ℂ} (hw : w ∈ resolventSet ℂ a) :
    holomorphicCalculus a
      (holomorphicGerms.ofFun (fun z ↦ (w - z)⁻¹) (analyticOnNhd_sub_inv hw)) =
      resolvent a w :=
  algHom_ofFun_sub_inv_eq_resolvent (holomorphicCalculus a) (holomorphicCalculus_id a) hw

/-- On an open neighbourhood `U` of `spectrum ℂ a` avoiding `w`, the calculus maps `(w - ·)⁻¹` to
`resolvent a w`. -/
@[simp]
theorem holomorphicCalculusOn_sub_inv (a : A) (U : Opens ℂ) (ha : spectrum ℂ a ⊆ U)
    {w : ℂ} (hwU : w ∉ (U : Set ℂ)) :
    holomorphicCalculusOn a U ha
      (of U (fun z ↦ (w - z)⁻¹)
        ((differentiableOn_const w).sub differentiableOn_id |>.inv
          fun _ hz ↦ sub_ne_zero.mpr fun (h : w = _) ↦ hwU (h ▸ hz))) = resolvent a w := by
  have hw : w ∈ resolventSet ℂ a :=
    spectrum.notMem_iff.mp fun hwσ ↦ hwU (ha hwσ)
  rw [← holomorphicCalculus_toGerm, toGerm_of]
  exact holomorphicCalculus_sub_inv a hw

/-- **Rational functions in the holomorphic calculus.** If `p, q : Polynomial ℂ` and `q` has no
zeros on `spectrum ℂ a`, then `Polynomial.aeval a q` is a unit and the holomorphic calculus sends
`z ↦ p(z) / q(z)` to `p(a) q(a)⁻¹`. -/
theorem holomorphicCalculus_div_polynomial (a : A) (p q : Polynomial ℂ)
    (hq : ∀ z ∈ spectrum ℂ a, q.eval z ≠ 0) :
    IsUnit (Polynomial.aeval a q) ∧
      holomorphicCalculus a
        (holomorphicGerms.ofFun (fun z ↦ p.eval z / q.eval z)
          (((AnalyticOnNhd.eval_polynomial p).mono (subset_univ _)).div
            ((AnalyticOnNhd.eval_polynomial q).mono (subset_univ _)) hq)) =
        Polynomial.aeval a p * Ring.inverse (Polynomial.aeval a q) := by
  have hunit : IsUnit (Polynomial.aeval a q) := by
    rw [← spectrum.zero_notMem_iff (R := ℂ), spectrum.map_polynomial_aeval]
    rintro ⟨z, hz, h0⟩
    exact hq z hz h0
  have hp_ana : AnalyticOnNhd ℂ (fun z ↦ p.eval z) (spectrum ℂ a) :=
    (AnalyticOnNhd.eval_polynomial p).mono (subset_univ _)
  have hq_ana : AnalyticOnNhd ℂ (fun z ↦ q.eval z) (spectrum ℂ a) :=
    (AnalyticOnNhd.eval_polynomial q).mono (subset_univ _)
  refine ⟨hunit, ?_⟩
  have hmul : holomorphicGerms.ofFun (fun z ↦ p.eval z / q.eval z) (hp_ana.div hq_ana hq) *
      holomorphicGerms.ofFun (fun z ↦ q.eval z) hq_ana =
      holomorphicGerms.ofFun (fun z ↦ p.eval z) hp_ana := by
    apply Subtype.ext
    rw [Subalgebra.coe_mul, holomorphicGerms.coe_ofFun, holomorphicGerms.coe_ofFun,
      holomorphicGerms.coe_ofFun, ← Germ.coe_mul]
    apply Germ.coe_eq.mpr
    apply eventually_nhdsSet_iff_forall.mpr fun z hz ↦ ?_
    filter_upwards [q.continuous.continuousAt.eventually_ne (hq z hz)] with u hu
    exact div_mul_cancel₀ _ hu
  have hcalc := congrArg (holomorphicCalculus a) hmul
  rw [map_mul, holomorphicCalculus_polynomial, holomorphicCalculus_polynomial] at hcalc
  calc holomorphicCalculus a
        (holomorphicGerms.ofFun (fun z ↦ p.eval z / q.eval z) (hp_ana.div hq_ana hq))
      = holomorphicCalculus a
          (holomorphicGerms.ofFun (fun z ↦ p.eval z / q.eval z) (hp_ana.div hq_ana hq)) *
          (Polynomial.aeval a q * Ring.inverse (Polynomial.aeval a q)) := by
          rw [Ring.mul_inverse_cancel _ hunit, mul_one]
    _ = Polynomial.aeval a p * Ring.inverse (Polynomial.aeval a q) := by
          rw [← mul_assoc, hcalc]

/-- On an open neighbourhood `U` of `spectrum ℂ a` where `q` does not vanish, the calculus sends
`z ↦ p(z) / q(z)` to `p(a) q(a)⁻¹`. -/
theorem holomorphicCalculusOn_div_polynomial (a : A) (U : Opens ℂ) (ha : spectrum ℂ a ⊆ U)
    (p q : Polynomial ℂ) (hq : ∀ z ∈ U, q.eval z ≠ 0) :
    holomorphicCalculusOn a U ha
      (of U (fun z ↦ p.eval z / q.eval z)
        (p.differentiable.differentiableOn.div q.differentiable.differentiableOn hq)) =
      Polynomial.aeval a p * Ring.inverse (Polynomial.aeval a q) := by
  rw [← holomorphicCalculus_toGerm, toGerm_of]
  exact (holomorphicCalculus_div_polynomial a p q fun z hz ↦ hq z (ha hz)).2

private theorem summable_norm_coeff_smul_pow (a : A) {p : FormalMultilinearSeries ℂ ℂ ℂ}
    {z₀ : ℂ} {r : ℝ≥0∞} (hr : r ≤ p.radius) (ha : spectrum ℂ a ⊆ Metric.eball z₀ r) :
    Summable fun k : ℕ ↦ ‖p.coeff k • (a - algebraMap ℂ A z₀) ^ k‖ := by
  rcases subsingleton_or_nontrivial A with hsub | hnt
  · convert summable_zero with k
    rw [Subsingleton.elim (p.coeff k • (a - algebraMap ℂ A z₀) ^ k) 0, norm_zero]
  set b := a - algebraMap ℂ A z₀
  obtain ⟨w, hw, hsr⟩ := spectrum.exists_nnNorm_eq_spectralRadius b
  have hw_mem : z₀ + w ∈ spectrum ℂ a := by
    rw [spectrum.mem_iff] at hw ⊢
    convert hw using 2
    dsimp only [b]
    rw [map_add]
    abel
  have hlt : spectralRadius ℂ b < r := by
    have hed : edist (z₀ + w) z₀ < r := Metric.mem_eball.mp (ha hw_mem)
    simpa only [← hsr, eDist_eq_eNorm_sub, add_sub_cancel_left, eNorm_eq_nnNorm] using hed
  obtain ⟨ρ, hsr_lt, hρ_lt⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hlt
  have hev := (spectrum.pow_nnNorm_pow_one_div_tendsto_nhds_spectralRadius b).eventually
    (gt_mem_nhds hsr_lt)
  refine Summable.of_norm_bounded_eventually_nat (g := fun k ↦ ‖p k‖ * (ρ : ℝ) ^ k)
    (p.summable_norm_mul_pow (hρ_lt.trans_le hr)) ?_
  filter_upwards [hev, eventually_ge_atTop 1] with k hk hk1
  have hkpos : (0 : ℝ) < k := Nat.cast_pos.mpr hk1
  have hpow := ENNReal.rpow_lt_rpow hk hkpos
  rw [← ENNReal.rpow_mul, one_div_mul_cancel hkpos.ne', ENNReal.rpow_one,
    ENNReal.rpow_natCast, ← ENNReal.coe_pow, ENNReal.coe_lt_coe] at hpow
  have hle : ‖b ^ k‖ ≤ (ρ : ℝ) ^ k := le_of_lt (by exact_mod_cast hpow)
  rw [Real.norm_of_nonneg (norm_nonneg _), norm_smul, ← p.norm_apply_eq_norm_coef]
  exact mul_le_mul_of_nonneg_left hle (norm_nonneg _)

private theorem tendsto_holomorphicCalculusOn_partialSum (a : A) {f : ℂ → ℂ}
    {p : FormalMultilinearSeries ℂ ℂ ℂ} {z₀ : ℂ} {r : ℝ≥0∞}
    (hf : HasFPowerSeriesOnBall f p z₀ r) (ha : spectrum ℂ a ⊆ Metric.eball z₀ r) :
    Tendsto (fun n : ℕ ↦ ∑ k ∈ Finset.range n, p.coeff k • (a - algebraMap ℂ A z₀) ^ k) atTop
      (𝓝 (holomorphicCalculusOn a ⟨Metric.eball z₀ r, Metric.isOpen_eball⟩ ha
        (of ⟨Metric.eball z₀ r, Metric.isOpen_eball⟩ f hf.differentiableOn))) := by
  let U : Opens ℂ := ⟨Metric.eball z₀ r, Metric.isOpen_eball⟩
  let P : ℕ → Polynomial ℂ := fun n ↦
    ∑ k ∈ Finset.range n, Polynomial.C (p.coeff k) * (Polynomial.X - Polynomial.C z₀) ^ k
  let S : ℕ → holomorphicFunctions U := fun n ↦
    of U (fun z ↦ (P n).eval z) (P n).differentiable.differentiableOn
  have hconv : Tendsto S atTop (𝓝 (of U f hf.differentiableOn)) := by
    rw [tendsto_iff_tendstoLocallyUniformlyOn,
      tendstoLocallyUniformlyOn_iff_tendstoLocallyUniformly_comp_coe]
    convert tendstoLocallyUniformlyOn_iff_tendstoLocallyUniformly_comp_coe.mp
      hf.tendstoLocallyUniformlyOn' using 1
    · ext n ⟨z, hz⟩
      rw [extend_apply (S n) ⟨z, hz⟩, of_apply, ← Polynomial.coe_evalRingHom]
      dsimp only [P]
      rw [map_sum]
      simp [Polynomial.coe_evalRingHom, FormalMultilinearSeries.partialSum, mul_comm]
    · ext ⟨z, hz⟩
      simp [extend_apply _ ⟨z, hz⟩]
  have hmap := ((continuous_holomorphicCalculusOn a U ha).tendsto _).comp hconv
  refine hmap.congr fun n ↦ ?_
  simp [S, P, Function.comp_apply, Algebra.smul_def]

/-- **Power series expansion in the holomorphic calculus (open ball form).** If `f` has power
series `p` on `Metric.eball z₀ r` and `spectrum ℂ a ⊆ Metric.eball z₀ r`, then the series
`∑ p.coeff k • (a - z₀ 1) ^ k` converges unconditionally in norm to the calculus value of `f` on
`Metric.eball z₀ r`. -/
theorem hasSum_holomorphicCalculusOn_of_hasFPowerSeriesOnBall (a : A) {f : ℂ → ℂ}
    {p : FormalMultilinearSeries ℂ ℂ ℂ} {z₀ : ℂ} {r : ℝ≥0∞}
    (hf : HasFPowerSeriesOnBall f p z₀ r) (ha : spectrum ℂ a ⊆ Metric.eball z₀ r) :
    HasSum (fun k : ℕ ↦ p.coeff k • (a - algebraMap ℂ A z₀) ^ k)
      (holomorphicCalculusOn a ⟨Metric.eball z₀ r, Metric.isOpen_eball⟩ ha
        (of ⟨Metric.eball z₀ r, Metric.isOpen_eball⟩ f hf.differentiableOn)) :=
  (hasSum_iff_tendsto_nat_of_summable_norm (summable_norm_coeff_smul_pow a hf.r_le ha)).mpr
    (tendsto_holomorphicCalculusOn_partialSum a hf ha)

/-- **Power series expansion in the holomorphic germ calculus.** If `f` has power series `p` on
`Metric.eball z₀ r` and `spectrum ℂ a ⊆ Metric.eball z₀ r`, then `∑ p.coeff k • (a - z₀ 1) ^ k`
converges unconditionally in norm to `holomorphicCalculus a` at the germ of `f`. -/
theorem hasSum_holomorphicCalculus_of_hasFPowerSeriesOnBall (a : A) {f : ℂ → ℂ}
    {p : FormalMultilinearSeries ℂ ℂ ℂ} {z₀ : ℂ} {r : ℝ≥0∞}
    (hf : HasFPowerSeriesOnBall f p z₀ r) (ha : spectrum ℂ a ⊆ Metric.eball z₀ r) :
    HasSum (fun k : ℕ ↦ p.coeff k • (a - algebraMap ℂ A z₀) ^ k)
      (holomorphicCalculus a (holomorphicGerms.ofFun f (hf.analyticOnNhd.mono ha))) := by
  have h := hasSum_holomorphicCalculusOn_of_hasFPowerSeriesOnBall a hf ha
  rwa [← holomorphicCalculus_toGerm, toGerm_of] at h

/-- Value of `holomorphicCalculus a` on a convergent power series as a `tsum`. -/
theorem holomorphicCalculus_eq_tsum_of_hasFPowerSeriesOnBall (a : A) {f : ℂ → ℂ}
    {p : FormalMultilinearSeries ℂ ℂ ℂ} {z₀ : ℂ} {r : ℝ≥0∞}
    (hf : HasFPowerSeriesOnBall f p z₀ r) (ha : spectrum ℂ a ⊆ Metric.eball z₀ r) :
    holomorphicCalculus a (holomorphicGerms.ofFun f (hf.analyticOnNhd.mono ha)) =
      ∑' k : ℕ, p.coeff k • (a - algebraMap ℂ A z₀) ^ k :=
  (hasSum_holomorphicCalculus_of_hasFPowerSeriesOnBall a hf ha).tsum_eq.symm

end CalculusProperties

section ScalarAndUnitization

/-- On `ℂ`, `holomorphicCalculusOn c` is point evaluation at `c`. -/
@[simp]
theorem holomorphicCalculusOn_complex (c : ℂ) (U : Opens ℂ) (hc : spectrum ℂ c ⊆ U)
    (f : holomorphicFunctions U) :
    holomorphicCalculusOn c U hc f = f.val ⟨c, hc (by simp [spectrum.mem_iff])⟩ := by
  have hc_mem : c ∈ spectrum ℂ c := by simp [spectrum.mem_iff]
  obtain ⟨Γ, hΓ, hn, hw⟩ := (spectrum.isCompact c).exists_cycle_windingNumber_eq_one U.isOpen hc
  have hΓU : Γ.IsIn U := Cycle.isIn_iff.mpr fun _ hz ↦ (Cycle.isIn_iff.mp hΓ hz).1
  have hoff : c ∉ Cycle.trace Γ := fun hcΓ ↦ (Cycle.isIn_iff.mp hΓ hcΓ).2 hc_mem
  rw [holomorphicCalculusOn_eq_integral c U hc f Γ hΓ hn hw,
    Cycle.integral_congr (g := fun z ↦ extend f z / (z - c)) fun z _ ↦ by
      rw [smul_eq_mul, resolvent, Algebra.algebraMap_self, RingHom.id_apply, Ring.inverse_eq_inv,
        ← div_eq_mul_inv],
    Cycle.cauchyIntegralFormula_nullHomologous U.isOpen (differentiableOn_extend f) hΓU hn hoff,
    hw c hc_mem, mul_one, extend_apply f ⟨c, hc hc_mem⟩, smul_eq_mul,
    inv_mul_cancel_left₀ two_pi_I_ne_zero]

/-- On `ℂ`, `holomorphicCalculus c` evaluates germs at `c`. -/
@[simp]
theorem holomorphicCalculus_complex (c : ℂ) (g : holomorphicGerms (spectrum ℂ c)) :
    holomorphicCalculus c g = holomorphicGerms.eval c (by simp [spectrum.mem_iff]) g := by
  obtain ⟨U, hc, f, rfl⟩ := holomorphicGerms.exists_toGerm_eq g
  rw [holomorphicCalculus_toGerm, holomorphicCalculusOn_complex, eval_toGerm]

section NonUnital

variable {A : Type*} [NonUnitalNormedRing A] [NormedSpace ℂ A]
  [IsScalarTower ℂ A A] [SMulCommClass ℂ A A] [CompleteSpace A]

/-- The scalar coordinate of the unitized holomorphic calculus of `a : A` at `g` is `g(0)`. -/
theorem unitizationFstA_holomorphicCalculus_unitizationInrL (a : A)
    (g : holomorphicGerms (spectrum ℂ (WithLp.unitizationInrL ℂ A a))) :
    WithLp.unitizationFstA ℂ A (holomorphicCalculus (WithLp.unitizationInrL ℂ A a) g) =
      holomorphicGerms.eval 0 (WithLp.zero_mem_spectrum_unitizationInrL a) g := by
  rw [ContinuousAlgHom.map_holomorphicCalculus, holomorphicCalculus_complex]
  obtain ⟨U, haU, f, rfl⟩ := holomorphicGerms.exists_toGerm_eq g
  simp

/-- **Nonunital holomorphic calculus criterion (germ form).** For `a` in a nonunital complex Banach
algebra `A`, the holomorphic calculus of `WithLp.unitizationInrL ℂ A a` in the `ℓ¹` unitization
lies in the image of `A` if and only if the germ vanishes at `0`. -/
theorem holomorphicCalculus_unitizationInrL_mem_range_iff (a : A)
    (g : holomorphicGerms (spectrum ℂ (WithLp.unitizationInrL ℂ A a))) :
    holomorphicCalculus (WithLp.unitizationInrL ℂ A a) g ∈
      Set.range (WithLp.unitizationInrL ℂ A) ↔
      holomorphicGerms.eval 0 (WithLp.zero_mem_spectrum_unitizationInrL a) g = 0 := by
  rw [WithLp.mem_range_unitizationInrL_iff, unitizationFstA_holomorphicCalculus_unitizationInrL]

/-- **Nonunital holomorphic calculus criterion (open-domain form).** The unitized calculus of
`a : A` at `f : holomorphicFunctions U` lies in the image of `A` if and only if `f(0) = 0`. -/
theorem holomorphicCalculusOn_unitizationInrL_mem_range_iff (a : A) (U : Opens ℂ)
    (ha : spectrum ℂ (WithLp.unitizationInrL ℂ A a) ⊆ U) (f : holomorphicFunctions U) :
    holomorphicCalculusOn (WithLp.unitizationInrL ℂ A a) U ha f ∈
      Set.range (WithLp.unitizationInrL ℂ A) ↔
      f.val ⟨0, ha (WithLp.zero_mem_spectrum_unitizationInrL a)⟩ = 0 := by
  rw [← holomorphicCalculus_toGerm, holomorphicCalculus_unitizationInrL_mem_range_iff, eval_toGerm]

end NonUnital

end ScalarAndUnitization

section SpectralMapping

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

/-- **Spectral mapping theorem for the holomorphic germ calculus.** For every Banach-algebra
element `a` and every holomorphic germ `g` near `spectrum ℂ a`,
`spectrum ℂ (holomorphicCalculus a g) = spectrum ℂ g` (including in the zero algebra). -/
@[simp]
theorem spectrum_holomorphicCalculus (a : A) (g : holomorphicGerms (spectrum ℂ a)) :
    spectrum ℂ (holomorphicCalculus a g) = spectrum ℂ g := by
  refine Subset.antisymm (AlgHom.spectrum_apply_subset (holomorphicCalculus a) g) ?_
  obtain ⟨f, hf, rfl⟩ := holomorphicGerms.exists_ofFun_eq g
  rw [holomorphicGerms.spectrum_ofFun]
  rintro _ ⟨z₀, hz₀, rfl⟩
  let u := algebraMap ℂ (holomorphicGerms (spectrum ℂ a)) z₀ -
    holomorphicGerms.ofFun id analyticOnNhd_id
  let q := holomorphicGerms.ofFun (dslope f z₀) (hf.dslope z₀)
  have hfac : u * q =
      algebraMap ℂ (holomorphicGerms (spectrum ℂ a)) (f z₀) - holomorphicGerms.ofFun f hf := by
    apply Subtype.ext
    simp only [u, q, Subalgebra.coe_mul, Subalgebra.coe_sub,
      Subalgebra.coe_algebraMap, Germ.algebraMap_eq, holomorphicGerms.coe_ofFun,
      ← Germ.coe_sub, ← Germ.coe_mul]
    apply Germ.coe_eq.mpr
    refine Eventually.of_forall fun z ↦ ?_
    have hd := sub_smul_dslope f z₀ z
    simp only [Pi.mul_apply, Pi.sub_apply, id_eq, Algebra.algebraMap_self, RingHom.id_apply]
    rw [smul_eq_mul] at hd
    linear_combination -hd
  have hcomm : Commute (holomorphicCalculus a u) (holomorphicCalculus a q) :=
    (Commute.all u q).map (holomorphicCalculus a)
  have hu : holomorphicCalculus a u = algebraMap ℂ A z₀ - a := by
    simp [u]
  have hmap : holomorphicCalculus a u * holomorphicCalculus a q =
      algebraMap ℂ A (f z₀) - holomorphicCalculus a (holomorphicGerms.ofFun f hf) := by
    rw [← map_mul, hfac, map_sub, AlgHom.commutes]
  rw [spectrum.mem_iff, ← hmap]
  intro hunit
  exact spectrum.mem_iff.mp hz₀ (hu ▸ (hcomm.isUnit_mul_iff.mp hunit).1)

/-- **Spectral mapping theorem (represented germ form).** If `f` is analytic on a neighbourhood of
`spectrum ℂ a`, then `spectrum ℂ (f(a)) = f '' spectrum ℂ a`. -/
theorem spectrum_holomorphicCalculus_ofFun (a : A) (f : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f (spectrum ℂ a)) :
    spectrum ℂ (holomorphicCalculus a (holomorphicGerms.ofFun f hf)) = f '' spectrum ℂ a := by
  rw [spectrum_holomorphicCalculus, holomorphicGerms.spectrum_ofFun]

/-- **Spectral mapping theorem (open-domain form).** For `f : holomorphicFunctions U` with
`spectrum ℂ a ⊆ U`, `spectrum ℂ (holomorphicCalculusOn a U ha f) = extend f '' spectrum ℂ a`. -/
theorem spectrum_holomorphicCalculusOn (a : A) (U : Opens ℂ) (ha : spectrum ℂ a ⊆ U)
    (f : holomorphicFunctions U) :
    spectrum ℂ (holomorphicCalculusOn a U ha f) = extend f '' spectrum ℂ a := by
  rw [← holomorphicCalculus_toGerm, spectrum_holomorphicCalculus, toGerm_apply,
    holomorphicGerms.spectrum_ofFun]

/-- **Spectral mapping theorem (ambient differentiable representative).** For `f` differentiable on
an open neighbourhood `U` of `spectrum ℂ a`,
`spectrum ℂ (holomorphicCalculusOn a U ha (of U f hf)) = f '' spectrum ℂ a`. -/
theorem spectrum_holomorphicCalculusOn_of (a : A) (U : Opens ℂ) (ha : spectrum ℂ a ⊆ U)
    (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f U) :
    spectrum ℂ (holomorphicCalculusOn a U ha (of U f hf)) = f '' spectrum ℂ a := by
  rw [← holomorphicCalculus_toGerm, toGerm_of, spectrum_holomorphicCalculus_ofFun]

end SpectralMapping

end TauCeti
