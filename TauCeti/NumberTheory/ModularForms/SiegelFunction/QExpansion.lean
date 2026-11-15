/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.QExpansion.Laurent
public import TauCeti.NumberTheory.ModularForms.SiegelFunction.Congruence
public import TauCeti.RingTheory.HahnSeries.Map
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import Mathlib.RingTheory.RootsOfUnity.Complex
import TauCeti.NumberTheory.ModularForms.QExpansion.BigO

/-!
# Laurent `q_N`-expansions and cusp orders of Siegel functions

For a positive level `N` and an integral row vector `a = (a₀, a₁)`, the `(12 N)`-th power
`g_{a/N}(τ)^{12 N}` of the Siegel function depends only on `a mod N` and expands in the local
cusp parameter `q_N = e^{2π i τ / N}` at `i∞` as `q_N^{m(a)} ψ(q_N)`, where
`m(a) = 6 N² B₂({a₀ / N}) = 6 r₀² - 6 N r₀ + N²` for the canonical residue `0 ≤ r₀ < N` of `a₀`
modulo `N`, and `ψ` is a holomorphic unit power series (with nonzero constant term whenever
`a ∉ N ℤ²`). Every coefficient of this Laurent `q_N`-expansion is a polynomial over `ℤ` in the
primitive `N`-th root of unity `ζ_N = e^{2π i / N}`, and substituting `ζ_N ↦ ζ_N^d` transforms the
expansion into that of `g_{(a₀, d a₁)/N}^{12 N}` — the diagonal right action of `diag(1, d)` on the
row index.

Reading `g_{a/N}(γ • τ)` in the coordinate of an arbitrary cusp `γ • ∞` (`γ ∈ SL₂(ℤ)`) replaces `a`
by `a γ`. Together with `Gamma(N)`-normality, this implies that every `Γ(N)`-invariant Kubert–Lang
product `∏ᵢ g_{aᵢ/N}^{mᵢ}` is meromorphic at every cusp, and for non-integral parameters has exact
`q_N`-order `(1 / (12 N)) ∑ᵢ mᵢ · 6 N² B₂({(aᵢ γ)₀ / N})`.

## Main definitions and results

* `TauCeti.ModularForm.siegelCuspOrder`: the integer `6 r₀² - 6 N r₀ + N²` with `r₀ = (v 0).val`,
  equal to `6 N² B₂({a₀ / N})` (`siegelCuspOrder_eq_bernoulliFun`).
* `TauCeti.ModularForm.siegelFunction_div_pow_twelve_mul_congr`,
  `TauCeti.ModularForm.siegelFunction_div_pow_twelve_mul_eq_zmod`: `g_{a/N}^{12N}` depends only on
  `a mod N`.
* `TauCeti.ModularForm.meromorphicAt_cuspFunction_siegelFunction_div_pow_twelve_mul`,
  `TauCeti.ModularForm.meromorphicOrderAt_cuspFunction_siegelFunction_div_pow_twelve_mul`: cusp
  meromorphy and exact `q_N`-order at `γ • ∞` of `g_{a/N}^{12N}`.
* `TauCeti.ModularForm.laurentQExpansion_siegelFunction_div_pow_twelve_mul_coeff_siegelCuspOrder`:
  the exact leading Laurent `q_N`-coefficient of `g_{v/N}^{12N}`.
* `TauCeti.ModularForm.siegelPowerLaurentPoly`,
  `TauCeti.ModularForm.map_aeval_siegelPowerLaurentPoly`,
  `TauCeti.ModularForm.laurentQExpansion_siegelFunction_div_pow_twelve_mul_coeff_mem_adjoin`:
  the universal `HahnSeries ℤ ℤ[X]` lift of the Laurent `q_N`-expansion of `g_{v/N}^{12N}`, its
  equivariance under `ζ_N ↦ ζ_N^d` via `(v₀, v₁) ↦ (v₀, d v₁)`, and `ℤ[ζ_N]`-integrality of all
  Laurent `q_N`-coefficients.
* `TauCeti.ModularForm.meromorphicAt_cuspFunction_prod_siegelFunction_div_zpow`,
  `TauCeti.ModularForm.meromorphicOrderAt_cuspFunction_prod_siegelFunction_div_zpow`: cusp
  meromorphy and exact cusp order at every cusp for `Γ(N)`-invariant Kubert–Lang products.

## References

* D. S. Kubert, S. Lang, *Modular Units*, Grundlehren der mathematischen Wissenschaften 244,
  Chapter 2, §1 and §2, and Chapter 3, §5.
* D. H. Shin, *Generation of class fields by Siegel–Ramachandra invariants*, §2.
-/

public noncomputable section

open Complex Filter Topology
open UpperHalfPlane hiding I
open scoped Real Matrix MatrixGroups Manifold Polynomial

namespace TauCeti.ModularForm

local notation "𝕢" => Function.Periodic.qParam

/-! ### Shifted `q`-Pochhammer power series -/

section QPochhammer

/-- Formal power series `∏_{n ≥ 0} (1 - x X^{N n + c})`, whose `m`-th coefficient for `N, c > 0`
stabilizes at the partial product over `n < m`. -/
private def qPochhammerSeries {R : Type*} [CommRing R] (N c : ℕ) (x : R) : PowerSeries R :=
  PowerSeries.mk fun m ↦ PowerSeries.coeff m
    (∏ n ∈ Finset.range m, (1 - PowerSeries.C x * PowerSeries.X ^ (N * n + c)))

private theorem map_qPochhammerSeries {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (N c : ℕ) (x : R) :
    (qPochhammerSeries N c x).map f = qPochhammerSeries N c (f x) := by
  ext m
  rw [qPochhammerSeries, PowerSeries.coeff_map, PowerSeries.coeff_mk, qPochhammerSeries,
    PowerSeries.coeff_mk, ← PowerSeries.coeff_map]
  simp

private theorem coeff_zero_qPochhammerSeries {R : Type*} [CommRing R] (N c : ℕ) (x : R) :
    (qPochhammerSeries N c x).coeff 0 = 1 := by
  simp [qPochhammerSeries]

/-- Analytic infinite product `∏_{n ≥ 0} (1 - w z^{N n + c})` on the open unit disc. -/
private def qPochhammerFun (N c : ℕ) (w z : ℂ) : ℂ :=
  ∏' n : ℕ, (1 - w * z ^ (N * n + c))

private theorem qPochhammerFun_eq_one_sub_mul_tprod {N : ℕ} (hN : 0 < N) (c : ℕ) (w : ℂ)
    {z : ℂ} (hz : ‖z‖ < 1) :
    qPochhammerFun N c w z =
      (1 - w * z ^ c) * ∏' k : ℕ, (1 - (z ^ N) ^ (k + 1) * (w * z ^ c)) := by
  have hm : Multipliable fun k : ℕ ↦ 1 - w * z ^ (N * (k + 1) + c) :=
    (multipliable_one_sub_pow_mul (norm_pow_lt_one hz hN.ne') (w * z ^ c)).congr fun k ↦ by
      congr 1; rw [← pow_mul, mul_left_comm, ← pow_add]
  rw [qPochhammerFun, tprod_eq_zero_mul' hm]
  simp only [mul_zero, zero_add]
  refine congrArg _ (tprod_congr fun k ↦ ?_)
  congr 1
  rw [← pow_mul, mul_left_comm, ← pow_add]

private theorem qPochhammerFun_eq_mul {N : ℕ} (hN : 0 < N) (c : ℕ) (w : ℂ) {z : ℂ}
    (hz : ‖z‖ < 1) :
    qPochhammerFun N c w z = (1 - w * z ^ c) * qPochhammerFun N (N + c) w z := by
  have hm : Multipliable fun k : ℕ ↦ 1 - w * z ^ (N * (k + 1) + c) :=
    (multipliable_one_sub_pow_mul (norm_pow_lt_one hz hN.ne') (w * z ^ c)).congr fun k ↦ by
      congr 1; rw [← pow_mul, mul_left_comm, ← pow_add]
  rw [qPochhammerFun, tprod_eq_zero_mul' hm, qPochhammerFun]
  simp only [mul_zero, zero_add]
  refine congrArg _ (tprod_congr fun k ↦ ?_)
  congr 2
  ring

private theorem analyticAt_qPochhammerFun {N : ℕ} (hN : 0 < N) (c : ℕ) (w : ℂ) :
    AnalyticAt ℂ (qPochhammerFun N c w) 0 := by
  have hd : DifferentiableOn ℂ (qPochhammerFun N c w) (Metric.ball 0 1) := by
    refine DifferentiableOn.congr ?_ fun z hz ↦
      qPochhammerFun_eq_one_sub_mul_tprod hN c w (mem_ball_zero_iff.mp hz)
    exact (DifferentiableOn.sub (differentiableOn_const 1) (by fun_prop)).mul
      (differentiableOn_tprod_one_sub_pow_mul Metric.isOpen_ball (by fun_prop)
        (fun z hz ↦ norm_pow_lt_one (mem_ball_zero_iff.mp hz) hN.ne') (by fun_prop))
  exact hd.analyticOnNhd Metric.isOpen_ball 0 (Metric.mem_ball_self zero_lt_one)

private theorem cuspFunction_qPochhammer_eventuallyEq {h : ℝ} (hh : 0 < h) {N : ℕ} (hN : 0 < N)
    (c : ℕ) (w : ℂ) :
    cuspFunction h (fun τ : ℍ ↦ qPochhammerFun N c w (𝕢 h τ)) =ᶠ[𝓝 0] qPochhammerFun N c w := by
  refine UpperHalfPlane.cuspFunction_eventuallyEq_nhds_of_continuousAt ?_
    (analyticAt_qPochhammerFun hN c w).continuousAt
  filter_upwards [self_mem_nhdsWithin,
    nhdsWithin_le_nhds (Metric.ball_mem_nhds (0 : ℂ) zero_lt_one)] with q hq hqn
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hq
  rw [UpperHalfPlane.cuspFunction_of_ne_zero hq,
    ofComplex_apply_of_im_pos (Function.Periodic.im_invQParam_pos_of_norm_lt_one hh
      (mem_ball_zero_iff.mp hqn) hq),
    Function.Periodic.qParam_right_inv hh.ne' hq]

private theorem analyticAt_cuspFunction_qPochhammer {h : ℝ} (hh : 0 < h) {N : ℕ} (hN : 0 < N)
    (c : ℕ) (w : ℂ) :
    AnalyticAt ℂ (cuspFunction h fun τ : ℍ ↦ qPochhammerFun N c w (𝕢 h τ)) 0 :=
  (analyticAt_qPochhammerFun hN c w).congr (cuspFunction_qPochhammer_eventuallyEq hh hN c w).symm

private theorem isBigO_qPochhammerFun_sub_one {N c : ℕ} (hN : 0 < N) (hc : 0 < c) (w : ℂ) :
    (fun z : ℂ ↦ qPochhammerFun N c w z - 1) =O[𝓝 0] fun z : ℂ ↦ ‖z‖ ^ c := by
  set y : ℂ → ℝ := fun z ↦ ‖w‖ * ‖z‖ ^ c / (1 - ‖z‖ ^ N)
  have hy0 : Tendsto y (𝓝 0) (𝓝 0) := by
    have hnum : Tendsto (fun z : ℂ ↦ ‖w‖ * ‖z‖ ^ c) (𝓝 0) (𝓝 0) := by
      simpa [zero_pow hc.ne'] using
        (((continuous_norm (E := ℂ)).pow c).tendsto (0 : ℂ)).const_mul ‖w‖
    have hden : Tendsto (fun z : ℂ ↦ 1 - ‖z‖ ^ N) (𝓝 0) (𝓝 1) := by
      simpa [zero_pow hN.ne'] using
        tendsto_const_nhds.sub (((continuous_norm (E := ℂ)).pow N).tendsto (0 : ℂ))
    have hdiv := hnum.div hden one_ne_zero
    rwa [zero_div] at hdiv
  have hexp : (fun z : ℂ ↦ Real.exp (y z) - 1) =O[𝓝 0] y := by
    simpa [Function.comp_def, Real.exp_zero] using
      (Real.differentiableAt_exp (x := 0)).isBigO_sub.comp_tendsto hy0
  have hyO : y =O[𝓝 0] fun z : ℂ ↦ ‖z‖ ^ c := by
    have hcts : ContinuousAt (fun z : ℂ ↦ ‖w‖ / (1 - ‖z‖ ^ N)) 0 :=
      continuousAt_const.div
        (continuousAt_const.sub ((continuous_norm (E := ℂ)).pow N).continuousAt)
        (by simp [zero_pow hN.ne'])
    exact ((hcts.norm.isBoundedUnder_le.isBigO_one ℝ).mul
      (Asymptotics.isBigO_refl (fun z : ℂ ↦ ‖z‖ ^ c) _)).congr'
      (Eventually.of_forall fun z ↦ by dsimp only [y, Pi.mul_apply]; ring)
      (Eventually.of_forall fun z ↦ by simp)
  refine Asymptotics.IsBigO.trans (Asymptotics.isBigO_iff.mpr ⟨1, ?_⟩) (hexp.trans hyO)
  filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (by positivity : (0 : ℝ) < 1 / 2)] with z hz
  have hz1 : ‖z‖ < 1 := (mem_ball_zero_iff.mp hz).trans (by norm_num)
  have hsum : HasSum (fun n : ℕ ↦ ‖-(w * z ^ (N * n + c))‖) (y z) := by
    have hg := hasSum_geometric_of_lt_one (pow_nonneg (norm_nonneg z) N)
      (by simpa [norm_pow] using norm_pow_lt_one hz1 hN.ne')
    simpa [y, norm_mul, norm_pow, pow_add, pow_mul, ← mul_assoc, mul_comm, mul_left_comm,
      div_eq_mul_inv] using hg.mul_left (‖w‖ * ‖z‖ ^ c)
  have hle := norm_tprod_one_add_sub_one_le hsum.summable
  simp only [← sub_eq_add_neg, hsum.tsum_eq] at hle
  have hy_nonneg : 0 ≤ Real.exp (y z) - 1 :=
    sub_nonneg.mpr (Real.one_le_exp (div_nonneg (by positivity)
      (sub_nonneg.mpr (pow_le_one₀ (norm_nonneg z) hz1.le))))
  simpa [qPochhammerFun, Real.norm_of_nonneg hy_nonneg] using hle

private theorem analyticAt_and_qExpansion_one_sub_mul_qParam_pow {h : ℝ} (hh : 0 < h)
    (c : ℕ) (w : ℂ) :
    AnalyticAt ℂ (cuspFunction h fun τ : ℍ ↦ 1 - w * 𝕢 h τ ^ c) 0 ∧
      qExpansion h (fun τ : ℍ ↦ 1 - w * 𝕢 h τ ^ c) =
        1 - PowerSeries.C w * PowerSeries.X ^ c := by
  have han1 : AnalyticAt ℂ (cuspFunction h (1 : ℍ → ℂ)) 0 := by
    rw [UpperHalfPlane.cuspFunction_one]
    exact analyticAt_const
  have hanq := UpperHalfPlane.analyticAt_cuspFunction_qParam_pow h c
  have hans : AnalyticAt ℂ (cuspFunction h (w • fun τ : ℍ ↦ 𝕢 h τ ^ c)) 0 := by
    rw [UpperHalfPlane.cuspFunction_smul hanq.continuousAt w]
    exact hanq.const_smul
  have hfun : (fun τ : ℍ ↦ 1 - w * 𝕢 h τ ^ c) = (1 : ℍ → ℂ) - w • fun τ : ℍ ↦ 𝕢 h τ ^ c := by
    funext τ; simp
  refine ⟨?_, ?_⟩
  · rw [hfun, UpperHalfPlane.cuspFunction_sub han1.continuousAt hans.continuousAt]
    exact han1.sub hans
  · rw [hfun, UpperHalfPlane.qExpansion_sub han1 hans, UpperHalfPlane.qExpansion_one,
      UpperHalfPlane.qExpansion_smul hanq w, UpperHalfPlane.qExpansion_qParam_pow hh,
      Algebra.smul_def]
    rfl

private theorem qExpansion_qPochhammer_mul_range {h : ℝ} (hh : 0 < h) {N : ℕ} (hN : 0 < N)
    (c m : ℕ) (w : ℂ) :
    qExpansion h (fun τ : ℍ ↦ qPochhammerFun N c w (𝕢 h τ)) =
      (∏ n ∈ Finset.range m, (1 - PowerSeries.C w * PowerSeries.X ^ (N * n + c))) *
        qExpansion h (fun τ : ℍ ↦ qPochhammerFun N (N * m + c) w (𝕢 h τ)) := by
  induction m generalizing c with
  | zero => simp
  | succ m ih =>
    have hfun : (fun τ : ℍ ↦ qPochhammerFun N c w (𝕢 h τ)) =
        (fun τ : ℍ ↦ 1 - w * 𝕢 h τ ^ c) * fun τ : ℍ ↦ qPochhammerFun N (N + c) w (𝕢 h τ) :=
      funext fun τ ↦ qPochhammerFun_eq_mul hN c w
        (Function.Periodic.norm_qParam_lt_one hh τ.im_pos)
    obtain ⟨han₁, hq₁⟩ := analyticAt_and_qExpansion_one_sub_mul_qParam_pow hh c w
    have hexp₁ (n : ℕ) : N * n + (N + c) = N * (n + 1) + c := by ring
    rw [hfun, UpperHalfPlane.qExpansion_mul han₁ (analyticAt_cuspFunction_qPochhammer hh hN _ w),
      hq₁, ih (N + c)]
    simp only [hexp₁, Finset.prod_range_succ', mul_zero, zero_add]
    ring

private theorem qExpansion_qPochhammer {h : ℝ} (hh : 0 < h) {N c : ℕ} (hN : 0 < N)
    (hc : 0 < c) (w : ℂ) :
    qExpansion h (fun τ : ℍ ↦ qPochhammerFun N c w (𝕢 h τ)) = qPochhammerSeries N c w := by
  ext m
  set c' := N * m + c
  have hc' : m < c' := by
    have : 1 * m ≤ N * m := Nat.mul_le_mul_right m hN
    omega
  have han1 : AnalyticAt ℂ (cuspFunction h (1 : ℍ → ℂ)) 0 := by
    rw [UpperHalfPlane.cuspFunction_one]; exact analyticAt_const
  have hanP := analyticAt_cuspFunction_qPochhammer hh hN c' w
  have han : AnalyticAt ℂ (cuspFunction h fun τ : ℍ ↦ qPochhammerFun N c' w (𝕢 h τ) - 1) 0 := by
    change AnalyticAt ℂ (cuspFunction h ((fun τ : ℍ ↦ qPochhammerFun N c' w (𝕢 h τ)) - 1)) 0
    rw [UpperHalfPlane.cuspFunction_sub hanP.continuousAt han1.continuousAt]
    exact hanP.sub han1
  have hzero : ∀ k < c',
      (qExpansion h fun τ : ℍ ↦ qPochhammerFun N c' w (𝕢 h τ) - 1).coeff k = 0 := by
    refine (UpperHalfPlane.cuspFunction_isBigO_pow_iff_qExpansion_coeff_eq_zero han).mp ?_
    refine (isBigO_qPochhammerFun_sub_one hN (by omega) w).congr' ?_ EventuallyEq.rfl
    have hsub := UpperHalfPlane.cuspFunction_sub (h := h) hanP.continuousAt han1.continuousAt
    filter_upwards [cuspFunction_qPochhammer_eventuallyEq hh hN c' w] with z hz₁
    change (qPochhammerFun N c' w z - 1) =
      cuspFunction h ((fun τ : ℍ ↦ qPochhammerFun N c' w (𝕢 h τ)) - 1) z
    rw [hsub, Pi.sub_apply, UpperHalfPlane.cuspFunction_one, Pi.one_apply, hz₁]
  have hsplit : qExpansion h (fun τ : ℍ ↦ qPochhammerFun N c' w (𝕢 h τ)) =
      1 + qExpansion h (fun τ : ℍ ↦ qPochhammerFun N c' w (𝕢 h τ) - 1) := by
    rw [← UpperHalfPlane.qExpansion_one (h := h), ← UpperHalfPlane.qExpansion_add han1 han]
    exact congrArg (qExpansion h) (funext fun τ ↦ by simp)
  rw [qExpansion_qPochhammer_mul_range hh hN c m w, hsplit, mul_add, mul_one, map_add,
    qPochhammerSeries, PowerSeries.coeff_mk, PowerSeries.coeff_mul]
  refine add_eq_left.mpr (Finset.sum_eq_zero fun p hp ↦ ?_)
  have hp2 : p.2 ≤ m := by
    have := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
    omega
  rw [hzero p.2 (hp2.trans_lt hc'), mul_zero]

end QPochhammer

/-! ### Congruence of `g_{a/N}^{12N}` modulo `N` and `q_N`-factorization -/

/-- **Congruence modulo `N` of `(12 N)`-th powers.** If `a ≡ b [ZMOD N]` coordinatewise, then
`g_{a/N}(τ)^{12 N} = g_{b/N}(τ)^{12 N}` on the upper half-plane. -/
theorem siegelFunction_div_pow_twelve_mul_congr (N : ℕ) {a b : Fin 2 → ℤ}
    (hab : ∀ i, a i ≡ b i [ZMOD N]) {τ : ℂ} (hτ : 0 < τ.im) :
    siegelFunction (fun i ↦ (a i : ℝ) / N) τ ^ (12 * N) =
      siegelFunction (fun i ↦ (b i : ℝ) / N) τ ^ (12 * N) := by
  rcases eq_or_ne N 0 with rfl | hN
  · simp
  have hdvd (i : Fin 2) : (N : ℤ) ∣ a i - b i := Int.modEq_iff_dvd.mp (hab i).symm
  choose s hs using hdvd
  have hadd : (fun i ↦ (a i : ℝ) / N) = (fun i ↦ (b i : ℝ) / N) + fun i ↦ (s i : ℝ) := by
    ext i
    have hi : (a i : ℝ) - b i = N * s i := by exact_mod_cast hs i
    have hN' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN
    simp only [Pi.add_apply]
    field_simp
    linarith
  rw [hadd]
  refine siegelFunction_add_intCast_pow_twelve_mul _ s N (fun i ↦ ⟨6 * b i, ?_⟩) hτ
  have hN' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  push_cast
  field_simp

/-- On the upper half-plane, `g_{a/N}(τ)^{12 N}` agrees with `g_{((a mod N)/N)}(τ)^{12 N}`. -/
theorem siegelFunction_div_pow_twelve_mul_eq_zmod {N : ℕ} (a : Fin 2 → ℤ)
    {τ : ℂ} (hτ : 0 < τ.im) :
    siegelFunction (fun i ↦ (a i : ℝ) / N) τ ^ (12 * N) =
      siegelFunction (fun i ↦ ((a i : ZMod N).val : ℝ) / N) τ ^ (12 * N) := by
  rcases eq_or_ne N 0 with rfl | hN
  · simp
  have : NeZero N := ⟨hN⟩
  refine siegelFunction_div_pow_twelve_mul_congr N (b := fun i ↦ ((a i : ZMod N).val : ℤ))
    (fun i ↦ ?_) hτ
  rw [ZMod.val_intCast]
  exact (Int.mod_modEq (a i) N).symm

/-- For `[NeZero N]`, the rational vector `a / N` is non-integral (`a / N ∉ ℤ²`) if and only if its
reduction `(a 0, a 1) : Fin 2 → ZMod N` is nonzero. -/
theorem forall_div_ne_intCast_iff_zmod_ne_zero {N : ℕ} [NeZero N] (a : Fin 2 → ℤ) :
    (∀ s : Fin 2 → ℤ, (fun i ↦ (a i : ℝ) / N) ≠ fun i ↦ (s i : ℝ)) ↔
      (fun i ↦ (a i : ZMod N)) ≠ 0 := by
  have hN : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  refine not_iff_not.mp ?_
  push Not
  refine ⟨fun ⟨s, hs⟩ ↦ funext fun i ↦ ?_, fun h0 ↦ ?_⟩
  · have hi := congrFun hs i
    rw [div_eq_iff hN] at hi
    have hZ : a i = s i * N := by exact_mod_cast hi
    rw [Pi.zero_apply, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact ⟨s i, by linarith⟩
  · have hdvd (i : Fin 2) : (N : ℤ) ∣ a i :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd (a i) N).mp (congrFun h0 i)
    choose s hs using hdvd
    refine ⟨s, funext fun i ↦ ?_⟩
    rw [div_eq_iff hN]
    exact_mod_cast (hs i).trans (mul_comm _ _)

/-- **The cusp-order integer of a level-`N` Siegel `(12 N)`-th power**:
`6 r₀² - 6 N r₀ + N²` where `r₀ = (v 0).val`, equal to `6 N² B₂({a₀ / N})`. -/
def siegelCuspOrder (N : ℕ) (v : Fin 2 → ZMod N) : ℤ :=
  6 * ((v 0).val : ℤ) ^ 2 - 6 * (N : ℤ) * (v 0).val + (N : ℤ) ^ 2

/-- Defining formula for `siegelCuspOrder`. -/
theorem siegelCuspOrder_def (N : ℕ) (v : Fin 2 → ZMod N) :
    siegelCuspOrder N v = 6 * ((v 0).val : ℤ) ^ 2 - 6 * (N : ℤ) * (v 0).val + (N : ℤ) ^ 2 :=
  (rfl)

@[simp]
theorem siegelCuspOrder_of_apply_zero {N : ℕ} {v : Fin 2 → ZMod N} (hv : (v 0).val = 0) :
    siegelCuspOrder N v = (N : ℤ) ^ 2 := by
  simp [siegelCuspOrder, hv]

/-- `siegelCuspOrder N (a mod N)` equals `6 N² B₂({a₀ / N})`, where `{x} = Int.fract x` is the
fractional part and `B₂` is the second Bernoulli polynomial. -/
theorem siegelCuspOrder_eq_bernoulliFun {N : ℕ} [NeZero N] (a : Fin 2 → ℤ) :
    (siegelCuspOrder N (fun i ↦ (a i : ZMod N)) : ℝ) =
      6 * (N : ℝ) ^ 2 * bernoulliFun 2 (Int.fract ((a 0 : ℝ) / N)) := by
  have hN : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have hval : (((a 0 : ZMod N).val : ℤ) : ℝ) = ((a 0 % (N : ℤ) : ℤ) : ℝ) := by
    rw [ZMod.val_intCast]
  rw [siegelCuspOrder, Int.fract_div_intCast_eq_div_intCast_mod, bernoulliFun_two]
  push_cast
  rw [← Int.cast_natCast (a 0 : ZMod N).val, hval]
  field_simp

/-- The holomorphic unit factor `ψ_{N, v}(τ)` in `g_{v/N}(τ)^{12N} = q_N^{m(v)} ψ_{N, v}(τ)`. -/
private def siegelUnitFun (N : ℕ) (v : Fin 2 → ZMod N) (τ : ℍ) : ℂ :=
  let ω := cexp (2 * π * I / N) ^ (v 1).val
  ω ^ (6 * (v 0).val) *
    (1 - ω * 𝕢 N τ ^ (v 0).val) ^ (12 * N) *
    qPochhammerFun N (N + (v 0).val) ω (𝕢 N τ) ^ (12 * N) *
    qPochhammerFun N (N - (v 0).val) (ω ^ (N - 1)) (𝕢 N τ) ^ (12 * N)

private theorem tprod_siegel_eq_qPochhammer {N r₀ : ℕ} (hN : 0 < N) (hr₀ : r₀ ≤ N)
    {ω : ℂ} (hωN : ω ^ N = 1) (τ : ℍ) :
    (∏' n : ℕ, (1 - (𝕢 N τ ^ N) ^ (n + 1) * (ω * 𝕢 N τ ^ r₀))) =
        qPochhammerFun N (N + r₀) ω (𝕢 N τ) ∧
      (∏' n : ℕ, (1 - (𝕢 N τ ^ N) ^ (n + 1) * (ω * 𝕢 N τ ^ r₀)⁻¹)) =
        qPochhammerFun N (N - r₀) (ω ^ (N - 1)) (𝕢 N τ) := by
  have hω_inv : ω⁻¹ = ω ^ (N - 1) :=
    inv_eq_of_mul_eq_one_right (by rw [← pow_succ', Nat.sub_add_cancel hN, hωN])
  refine ⟨tprod_congr fun n ↦ ?_, tprod_congr fun n ↦ ?_⟩
  · congr 1
    rw [← pow_mul, mul_left_comm, ← pow_add]
    exact congrArg (fun k ↦ ω * 𝕢 N (τ : ℂ) ^ k) (by ring)
  · have hq_ne : 𝕢 N (τ : ℂ) ≠ 0 := Function.Periodic.qParam_ne_zero _
    have hexp_sub : (𝕢 N (τ : ℂ) ^ N) ^ (n + 1) * (𝕢 N (τ : ℂ) ^ r₀)⁻¹ =
        𝕢 N (τ : ℂ) ^ (N * n + (N - r₀)) := by
      refine (mul_inv_eq_iff_eq_mul₀ (pow_ne_zero r₀ hq_ne)).mpr ?_
      rw [← pow_mul, ← pow_add, add_assoc, Nat.sub_add_cancel hr₀]
      exact congrArg (𝕢 N (τ : ℂ) ^ ·) (by ring)
    rw [mul_inv, hω_inv]
    congr 1
    calc (𝕢 N (τ : ℂ) ^ N) ^ (n + 1) * (ω ^ (N - 1) * (𝕢 N (τ : ℂ) ^ r₀)⁻¹)
        = ω ^ (N - 1) * ((𝕢 N (τ : ℂ) ^ N) ^ (n + 1) * (𝕢 N (τ : ℂ) ^ r₀)⁻¹) := by ring
      _ = ω ^ (N - 1) * 𝕢 N (τ : ℂ) ^ (N * n + (N - r₀)) := by rw [hexp_sub]

/-- Exact factorization `g_{v/N}(τ)^{12 N} = q_N^{siegelCuspOrder N v} * siegelUnitFun N v τ`. -/
private theorem siegelFunction_zmod_pow_twelve_mul_eq {N : ℕ} [NeZero N] (v : Fin 2 → ZMod N)
    (τ : ℍ) :
    siegelFunction (fun i ↦ ((v i).val : ℝ) / N) τ ^ (12 * N) =
      𝕢 N τ ^ siegelCuspOrder N v * siegelUnitFun N v τ := by
  have hN : 0 < N := NeZero.pos N
  have hNC : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  let ω := cexp (2 * π * I / N) ^ (v 1).val
  have hωN : ω ^ N = 1 := by
    rw [← pow_mul, mul_comm (v 1).val N, pow_mul,
      (Complex.isPrimitiveRoot_exp N hN.ne').pow_eq_one, one_pow]
  have hq1 : cexp (2 * π * I * (τ : ℂ)) = 𝕢 N τ ^ N := by
    simpa [Function.Periodic.qParam] using
      (TauCeti.Periodic.qParam_nat_mul_pow (h := 1) hN.ne' (τ : ℂ)).symm
  have hw : cexp (2 * π * I * ((((v 0).val : ℝ) / N : ℝ) * (τ : ℂ) +
      (((v 1).val : ℝ) / N : ℝ))) = ω * 𝕢 N τ ^ (v 0).val := by
    simp only [ω, Function.Periodic.qParam, ← Complex.exp_nat_mul, ← Complex.exp_add]
    congr 1; push_cast; field_simp; ring
  have hB : cexp (π * I * bernoulliFun 2 (((v 0).val : ℝ) / N) * (τ : ℂ)) ^ (12 * N) =
      𝕢 N τ ^ siegelCuspOrder N v := by
    rw [Function.Periodic.qParam, ← Complex.exp_nat_mul, ← Complex.exp_int_mul, bernoulliFun_two,
      siegelCuspOrder]
    congr 1; push_cast; field_simp; ring
  have hph : cexp (π * I * ((((v 1).val : ℝ) / N : ℝ) : ℂ) *
      ((((v 0).val : ℝ) / N : ℝ) - 1)) ^ (12 * N) = ω ^ (6 * (v 0).val) := by
    have hexp : ((12 * N : ℕ) : ℂ) * (π * I * ((((v 1).val : ℝ) / N : ℝ) : ℂ) *
        ((((v 0).val : ℝ) / N : ℝ) - 1)) =
        ((6 * (v 0).val * (v 1).val : ℕ) : ℂ) * (2 * π * I / N) +
          (-(6 * ((v 1).val : ℤ)) : ℤ) * (2 * π * I) := by push_cast; field_simp; ring
    rw [← Complex.exp_nat_mul, hexp, Complex.exp_add, Complex.exp_int_mul,
      exp_two_pi_mul_I, _root_.one_zpow, mul_one, Complex.exp_nat_mul]
    simp only [ω, ← pow_mul, mul_comm (6 * (v 0).val) (v 1).val, mul_assoc]
  obtain ⟨hp₁, hp₂⟩ := tprod_siegel_eq_qPochhammer hN (v 0).val_lt.le hωN τ
  have hsign : (-1 : ℂ) ^ (12 * N) = 1 := Even.neg_one_pow ⟨6 * N, by ring⟩
  rw [siegelFunction_eq_mul_tprod_mul_tprod _ τ.im_pos, Complex.exp_neg, hq1, hw, hp₁, hp₂]
  have hpow : ∀ a b c d e : ℂ, (-a * b * c * (d * e)) ^ (12 * N) =
      (-1 : ℂ) ^ (12 * N) * a ^ (12 * N) * b ^ (12 * N) *
        c ^ (12 * N) * d ^ (12 * N) * e ^ (12 * N) := fun _ _ _ _ _ ↦ by ring
  rw [hpow, hsign, one_mul, hB, hph, siegelUnitFun]
  dsimp only [ω]
  ring

/-! ### Universal polynomial Laurent series and diagonal cyclotomic action -/

/-- Universal power series over `ℤ[X]` whose evaluation at `X = ζ_N` is the `q_N`-expansion of
`siegelUnitFun N v`. -/
def siegelUnitPowerSeries (N : ℕ) (v : Fin 2 → ZMod N) : PowerSeries ℤ[X] :=
  PowerSeries.C (Polynomial.X ^ (6 * (v 0).val * (v 1).val)) *
    (1 - PowerSeries.C (Polynomial.X ^ (v 1).val) * PowerSeries.X ^ (v 0).val) ^ (12 * N) *
    qPochhammerSeries N (N + (v 0).val) (Polynomial.X ^ (v 1).val) ^ (12 * N) *
    qPochhammerSeries N (N - (v 0).val) (Polynomial.X ^ ((N - 1) * (v 1).val)) ^ (12 * N)

/-- **Universal polynomial Laurent series of `g_{v/N}^{12N}`**: a formal Laurent series in
`HahnSeries ℤ ℤ[X]` whose coefficientwise evaluation at `X = e^{2π i / N}` is the Laurent
`q_N`-expansion of `g_{v/N}^{12 N}`. -/
def siegelPowerLaurentPoly (N : ℕ) (v : Fin 2 → ZMod N) : HahnSeries ℤ ℤ[X] :=
  HahnSeries.single (siegelCuspOrder N v) 1 *
    HahnSeries.ofPowerSeries ℤ ℤ[X] (siegelUnitPowerSeries N v)

private theorem analyticAt_cuspFunction_siegelUnitFun {N : ℕ} [NeZero N] (v : Fin 2 → ZMod N) :
    AnalyticAt ℂ (cuspFunction N (siegelUnitFun N v)) 0 := by
  have hN : 0 < N := NeZero.pos N
  have hNR : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  set ω := cexp (2 * π * I / N) ^ (v 1).val
  have han_lin := (analyticAt_and_qExpansion_one_sub_mul_qParam_pow hNR (v 0).val ω).1
  have han₁ := analyticAt_cuspFunction_qPochhammer hNR hN (N + (v 0).val) ω
  have han₂ := analyticAt_cuspFunction_qPochhammer hNR hN (N - (v 0).val) (ω ^ (N - 1))
  have han_pow {f : ℍ → ℂ} (hf : AnalyticAt ℂ (cuspFunction N f) 0) (k : ℕ) :
      AnalyticAt ℂ (cuspFunction N (f ^ k)) 0 := by
    rw [UpperHalfPlane.cuspFunction_pow hf.continuousAt k]; exact hf.pow k
  have han_mul {f g : ℍ → ℂ} (hf : AnalyticAt ℂ (cuspFunction N f) 0)
      (hg : AnalyticAt ℂ (cuspFunction N g) 0) :
      AnalyticAt ℂ (cuspFunction N (f * g)) 0 := by
    rw [UpperHalfPlane.cuspFunction_mul hf.continuousAt hg.continuousAt]; exact hf.mul hg
  have han_c : AnalyticAt ℂ (cuspFunction N fun _ : ℍ ↦ ω ^ (6 * (v 0).val)) 0 := by
    rw [UpperHalfPlane.cuspFunction_const]; exact analyticAt_const
  exact han_mul (han_mul (han_mul han_c (han_pow han_lin (12 * N)))
    (han_pow han₁ (12 * N))) (han_pow han₂ (12 * N))

private theorem qExpansion_siegelUnitFun {N : ℕ} [NeZero N] (v : Fin 2 → ZMod N) :
    qExpansion N (siegelUnitFun N v) =
      (siegelUnitPowerSeries N v).map (Polynomial.aeval (cexp (2 * π * I / N))).toRingHom := by
  have hN : 0 < N := NeZero.pos N
  have hNR : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  set ζ := cexp (2 * π * I / N)
  set ω := ζ ^ (v 1).val
  have hr₀ : (v 0).val < N := (v 0).val_lt
  obtain ⟨han_lin, hq_lin⟩ := analyticAt_and_qExpansion_one_sub_mul_qParam_pow hNR (v 0).val ω
  have han₁ := analyticAt_cuspFunction_qPochhammer hNR hN (N + (v 0).val) ω
  have han₂ := analyticAt_cuspFunction_qPochhammer hNR hN (N - (v 0).val) (ω ^ (N - 1))
  have han_pow {f : ℍ → ℂ} (hf : AnalyticAt ℂ (cuspFunction N f) 0) (k : ℕ) :
      AnalyticAt ℂ (cuspFunction N (f ^ k)) 0 := by
    rw [UpperHalfPlane.cuspFunction_pow hf.continuousAt k]; exact hf.pow k
  have han_mul {f g : ℍ → ℂ} (hf : AnalyticAt ℂ (cuspFunction N f) 0)
      (hg : AnalyticAt ℂ (cuspFunction N g) 0) :
      AnalyticAt ℂ (cuspFunction N (f * g)) 0 := by
    rw [UpperHalfPlane.cuspFunction_mul hf.continuousAt hg.continuousAt]; exact hf.mul hg
  have han1 : AnalyticAt ℂ (cuspFunction N (1 : ℍ → ℂ)) 0 := by
    rw [UpperHalfPlane.cuspFunction_one]; exact analyticAt_const
  have hconst : qExpansion N (fun _ : ℍ ↦ ω ^ (6 * (v 0).val)) =
      PowerSeries.C (ω ^ (6 * (v 0).val)) := by
    have hc : (fun _ : ℍ ↦ ω ^ (6 * (v 0).val)) = ω ^ (6 * (v 0).val) • (1 : ℍ → ℂ) := by
      funext; simp
    rw [hc, UpperHalfPlane.qExpansion_smul han1, UpperHalfPlane.qExpansion_one,
      Algebra.smul_def, mul_one]
    rfl
  change qExpansion N
    ((fun _ : ℍ ↦ ω ^ (6 * (v 0).val)) * (fun τ : ℍ ↦ 1 - ω * 𝕢 N τ ^ (v 0).val) ^ (12 * N) *
      (fun τ : ℍ ↦ qPochhammerFun N (N + (v 0).val) ω (𝕢 N τ)) ^ (12 * N) *
      (fun τ : ℍ ↦ qPochhammerFun N (N - (v 0).val) (ω ^ (N - 1)) (𝕢 N τ)) ^ (12 * N)) = _
  have han_c : AnalyticAt ℂ (cuspFunction N fun _ : ℍ ↦ ω ^ (6 * (v 0).val)) 0 := by
    rw [UpperHalfPlane.cuspFunction_const]; exact analyticAt_const
  rw [UpperHalfPlane.qExpansion_mul (han_mul (han_mul han_c (han_pow han_lin _)) (han_pow han₁ _))
      (han_pow han₂ _),
    UpperHalfPlane.qExpansion_mul (han_mul han_c (han_pow han_lin _)) (han_pow han₁ _),
    UpperHalfPlane.qExpansion_mul han_c (han_pow han_lin _),
    hconst, UpperHalfPlane.qExpansion_pow han_lin, UpperHalfPlane.qExpansion_pow han₁,
    UpperHalfPlane.qExpansion_pow han₂, hq_lin,
    qExpansion_qPochhammer hNR hN (by omega) ω,
    qExpansion_qPochhammer hNR hN (by omega) (ω ^ (N - 1)), siegelUnitPowerSeries]
  simp only [map_mul, map_pow, map_sub, map_one, PowerSeries.map_C, PowerSeries.map_X,
    map_qPochhammerSeries, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Polynomial.aeval_X]
  simp only [ω, map_pow, ← pow_mul, mul_comm (v 1).val]

/-- Twisting an analytic cusp function by an arbitrary integer power `𝕢 h ^ M` produces a
meromorphic cusp function with Laurent `q`-expansion `single M 1 * qExpansion h ψ`. -/
private theorem meromorphicAt_and_laurentQExpansion_qParam_zpow_mul {h : ℝ} (hh : 0 < h)
    (M : ℤ) {ψ : ℍ → ℂ} (hψ : AnalyticAt ℂ (cuspFunction h ψ) 0) :
    MeromorphicAt (cuspFunction h fun τ : ℍ ↦ 𝕢 h τ ^ M * ψ τ) 0 ∧
      UpperHalfPlane.laurentQExpansion h (fun τ : ℍ ↦ 𝕢 h τ ^ M * ψ τ) =
        HahnSeries.single M 1 * (qExpansion h ψ : LaurentSeries ℂ) := by
  obtain ⟨k, rfl | rfl⟩ := Int.eq_nat_or_neg M
  · have han : AnalyticAt ℂ (cuspFunction h fun τ : ℍ ↦ 𝕢 h τ ^ (k : ℤ) * ψ τ) 0 := by
      simp only [zpow_natCast]
      have hmul := UpperHalfPlane.cuspFunction_mul
        (UpperHalfPlane.analyticAt_cuspFunction_qParam_pow h k).continuousAt hψ.continuousAt
      change AnalyticAt ℂ (cuspFunction h ((fun τ : ℍ ↦ 𝕢 h τ ^ k) * ψ)) 0
      rw [hmul]
      exact (UpperHalfPlane.analyticAt_cuspFunction_qParam_pow h k).mul hψ
    refine ⟨han.meromorphicAt, ?_⟩
    rw [UpperHalfPlane.laurentQExpansion_of_analyticAt han]
    simp only [zpow_natCast]
    have hfun : (fun τ : ℍ ↦ 𝕢 h τ ^ k * ψ τ) = (fun τ : ℍ ↦ 𝕢 h τ ^ k) * ψ := rfl
    rw [hfun, UpperHalfPlane.qExpansion_mul (UpperHalfPlane.analyticAt_cuspFunction_qParam_pow h k)
      hψ, UpperHalfPlane.qExpansion_qParam_pow hh, PowerSeries.coe_mul, PowerSeries.coe_pow,
      PowerSeries.coe_X, HahnSeries.single_pow, one_pow, nsmul_one]
  · have hcancel : (fun τ : ℍ ↦ 𝕢 h τ ^ k * (𝕢 h τ ^ (-(k : ℤ)) * ψ τ)) = ψ := by
      funext τ
      rw [← mul_assoc, ← zpow_natCast, ← zpow_add₀ (Function.Periodic.qParam_ne_zero _),
        add_neg_cancel, zpow_zero, one_mul]
    have han' : AnalyticAt ℂ
        (cuspFunction h fun τ : ℍ ↦ 𝕢 h τ ^ k * (𝕢 h τ ^ (-(k : ℤ)) * ψ τ)) 0 := by
      rwa [hcancel]
    have htw := UpperHalfPlane.cuspFunction_qParam_pow_mul_eventuallyEq hh k
      (fun τ : ℍ ↦ 𝕢 h τ ^ (-(k : ℤ)) * ψ τ)
    have hmer : MeromorphicAt (cuspFunction h fun τ : ℍ ↦ 𝕢 h τ ^ (-(k : ℤ)) * ψ τ) 0 := by
      refine ((analyticAt_id.pow k).meromorphicAt.inv.mul han'.meromorphicAt).congr ?_
      filter_upwards [htw, self_mem_nhdsWithin] with q h₁ hq
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hq
      simp only [Pi.mul_apply, Pi.inv_apply, Pi.pow_apply, id_eq, h₁,
        inv_mul_cancel_left₀ (pow_ne_zero k hq)]
    exact ⟨hmer, by
      rw [UpperHalfPlane.laurentQExpansion_eq_of_analyticAt_qParam_pow_mul hh han', hcancel]⟩

/-- **Diagonal cyclotomic action on the Laurent `q_N`-expansion of `g_{v/N}^{12N}`.**
Evaluating the universal polynomial Laurent series `siegelPowerLaurentPoly N v` at
`X = e^{2π i / N}^d` yields the Laurent `q_N`-expansion of `g_{(v₀, d v₁)/N}^{12 N}`. -/
theorem map_aeval_siegelPowerLaurentPoly {N : ℕ} [NeZero N] (v : Fin 2 → ZMod N) (d : ℕ) :
    HahnSeries.mapRingHom (Polynomial.aeval (cexp (2 * π * I / N) ^ d)).toRingHom
        (siegelPowerLaurentPoly N v) =
      UpperHalfPlane.laurentQExpansion N (fun τ : ℍ ↦
        siegelFunction (fun i ↦ ((![v 0, (d : ZMod N) * v 1] i).val : ℝ) / N) τ ^ (12 * N)) := by
  set v' : Fin 2 → ZMod N := ![v 0, (d : ZMod N) * v 1]
  have hN : 0 < N := NeZero.pos N
  set ζ := cexp (2 * π * I / N)
  have hζN : ζ ^ N = 1 := (Complex.isPrimitiveRoot_exp N hN.ne').pow_eq_one
  have hpow : (ζ ^ d) ^ (v 1).val = ζ ^ (v' 1).val := by
    have hv1 : (v' 1).val = (d * (v 1).val) % N := by simp [v', ZMod.val_mul]
    rw [← pow_mul, hv1]
    conv_lhs => rw [← Nat.div_add_mod (d * (v 1).val) N]
    rw [pow_add, pow_mul, hζN, one_pow, one_mul]
  have hord : siegelCuspOrder N v = siegelCuspOrder N v' := by simp [siegelCuspOrder, v']
  have hunit : (siegelUnitPowerSeries N v).map (Polynomial.aeval (ζ ^ d)).toRingHom =
      (siegelUnitPowerSeries N v').map (Polynomial.aeval ζ).toRingHom := by
    simp only [siegelUnitPowerSeries, map_mul, map_pow, map_sub, map_one, PowerSeries.map_C,
      PowerSeries.map_X, map_qPochhammerSeries, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      Polynomial.aeval_X]
    have h0 : (v' 0).val = (v 0).val := rfl
    have h6 : (PowerSeries.C ζ ^ d) ^ (6 * (v 0).val * (v 1).val) =
        PowerSeries.C ζ ^ (6 * (v' 0).val * (v' 1).val) := by
      have hexp : d * (6 * (v 0).val * (v 1).val) = d * (v 1).val * (6 * (v 0).val) := by ring
      rw [← pow_mul, ← map_pow, ← map_pow, hexp, pow_mul, pow_mul ζ d, hpow,
        ← pow_mul, h0, mul_comm]
    have h1 : (PowerSeries.C ζ ^ d) ^ (v 1).val = PowerSeries.C ζ ^ (v' 1).val := by
      rw [← pow_mul, ← map_pow, ← map_pow, pow_mul, hpow]
    have hN1 : (ζ ^ d) ^ ((N - 1) * (v 1).val) = ζ ^ ((N - 1) * (v' 1).val) := by
      rw [mul_comm (N - 1), pow_mul, hpow, ← pow_mul, mul_comm]
    rw [h6, h1, hN1, hpow, h0]
  have hsingle : HahnSeries.mapRingHom (Polynomial.aeval (R := ℤ) (ζ ^ d)).toRingHom
      (HahnSeries.single (siegelCuspOrder N v) 1) = HahnSeries.single (siegelCuspOrder N v) 1 := by
    ext k; by_cases hk : k = siegelCuspOrder N v <;> simp [hk]
  have hfun : (fun τ : ℍ ↦ siegelFunction (fun i ↦ ((v' i).val : ℝ) / N) τ ^ (12 * N)) =
      fun τ : ℍ ↦ 𝕢 N τ ^ siegelCuspOrder N v' * siegelUnitFun N v' τ :=
    funext (siegelFunction_zmod_pow_twelve_mul_eq v')
  rw [hfun, (meromorphicAt_and_laurentQExpansion_qParam_zpow_mul (Nat.cast_pos.mpr hN)
      (siegelCuspOrder N v') (analyticAt_cuspFunction_siegelUnitFun v')).2,
    qExpansion_siegelUnitFun v', ← hunit, ← hord, siegelPowerLaurentPoly, map_mul, hsingle,
    HahnSeries.mapRingHom_apply, HahnSeries.map_ofPowerSeries]

/-- Evaluating `siegelPowerLaurentPoly N v` at `ζ_N = e^{2π i / N}` gives the Laurent
`q_N`-expansion of `g_{v/N}^{12 N}`. -/
theorem map_aeval_exp_siegelPowerLaurentPoly {N : ℕ} [NeZero N] (v : Fin 2 → ZMod N) :
    HahnSeries.mapRingHom (Polynomial.aeval (cexp (2 * π * I / N))).toRingHom
        (siegelPowerLaurentPoly N v) =
      UpperHalfPlane.laurentQExpansion N (fun τ : ℍ ↦
        siegelFunction (fun i ↦ ((v i).val : ℝ) / N) τ ^ (12 * N)) := by
  have hv : (fun i ↦ ((![v 0, ((1 : ℕ) : ZMod N) * v 1] i).val : ℝ) / N) =
      fun i ↦ ((v i).val : ℝ) / N := by
    ext i; fin_cases i <;> simp
  have h := map_aeval_siegelPowerLaurentPoly v 1
  rwa [pow_one, hv] at h

/-- **Every Laurent `q_N`-coefficient of `g_{a/N}^{12 N}` lies in `ℤ[ζ_N]`**, where
`ζ_N = e^{2π i / N}`. -/
theorem laurentQExpansion_siegelFunction_div_pow_twelve_mul_coeff_mem_adjoin {N : ℕ}
    (a : Fin 2 → ℤ) (n : ℤ) :
    (UpperHalfPlane.laurentQExpansion N (fun τ : ℍ ↦
        siegelFunction (fun i ↦ (a i : ℝ) / N) τ ^ (12 * N))).coeff n ∈
      Algebra.adjoin ℤ {cexp (2 * π * I / N)} := by
  rcases eq_or_ne N 0 with rfl | hN
  · have h1 : (fun τ : ℍ ↦ siegelFunction (fun i ↦ (a i : ℝ) / (0 : ℕ)) τ ^ (12 * 0)) = 1 :=
      funext fun _ ↦ by simp
    rw [h1, UpperHalfPlane.laurentQExpansion_one]
    by_cases hn : n = 0 <;> simp [hn, one_mem, zero_mem]
  have : NeZero N := ⟨hN⟩
  set v : Fin 2 → ZMod N := fun i ↦ (a i : ZMod N)
  have hfun : (fun τ : ℍ ↦ siegelFunction (fun i ↦ (a i : ℝ) / N) τ ^ (12 * N)) =
      fun τ : ℍ ↦ siegelFunction (fun i ↦ ((v i).val : ℝ) / N) τ ^ (12 * N) :=
    funext fun τ ↦ siegelFunction_div_pow_twelve_mul_eq_zmod a τ.im_pos
  rw [hfun, ← map_aeval_exp_siegelPowerLaurentPoly v, HahnSeries.coeff_mapRingHom,
    AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.adjoin_singleton_eq_range_aeval]
  exact ⟨(siegelPowerLaurentPoly N v).coeff n, rfl⟩

/-! ### Cusp meromorphy, cusp orders, and leading coefficients -/

/-- The constant term of `siegelUnitFun N v` at `i∞` (`q_N = 0`). -/
private theorem qExpansion_siegelUnitFun_coeff_zero {N : ℕ} [NeZero N] (v : Fin 2 → ZMod N) :
    (qExpansion N (siegelUnitFun N v)).coeff 0 =
      cexp (2 * π * I / N) ^ (6 * (v 0).val * (v 1).val) *
        (if (v 0).val = 0 then (1 - cexp (2 * π * I / N) ^ (v 1).val) ^ (12 * N) else 1) := by
  rw [qExpansion_siegelUnitFun, PowerSeries.coeff_map, PowerSeries.coeff_zero_eq_constantCoeff,
    siegelUnitPowerSeries]
  simp only [map_mul, map_pow, map_sub, map_one, ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
    coeff_zero_qPochhammerSeries, one_pow, mul_one, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
  by_cases hv0 : (v 0).val = 0 <;> simp [hv0, zero_pow]

/-- For `v ≠ 0` in `Fin 2 → ZMod N`, the leading unit term of `g_{v/N}^{12N}` at `i∞` is nonzero. -/
private theorem qExpansion_siegelUnitFun_coeff_zero_ne_zero {N : ℕ} [NeZero N]
    {v : Fin 2 → ZMod N} (hv : v ≠ 0) :
    (qExpansion N (siegelUnitFun N v)).coeff 0 ≠ 0 := by
  rw [qExpansion_siegelUnitFun_coeff_zero]
  refine mul_ne_zero (pow_ne_zero _ (Complex.exp_ne_zero _)) ?_
  split_ifs with hv0
  · refine pow_ne_zero _ (sub_ne_zero.mpr fun h1 ↦ hv ?_)
    have hprim := Complex.isPrimitiveRoot_exp N (NeZero.ne N)
    have hdvd : N ∣ (v 1).val := hprim.dvd_of_pow_eq_one (v 1).val h1.symm
    have hv1 : (v 1).val = 0 := Nat.eq_zero_of_dvd_of_lt hdvd (v 1).val_lt
    ext i
    fin_cases i
    · exact ZMod.val_injective N (by simpa using hv0)
    · exact ZMod.val_injective N (by simpa using hv1)
  · exact one_ne_zero

/-- **The exact leading Laurent `q_N`-coefficient of `g_{v/N}^{12 N}`** at
`q_N^{siegelCuspOrder N v}`. -/
theorem laurentQExpansion_siegelFunction_div_pow_twelve_mul_coeff_siegelCuspOrder
    {N : ℕ} [NeZero N] (v : Fin 2 → ZMod N) :
    (UpperHalfPlane.laurentQExpansion N (fun τ : ℍ ↦
        siegelFunction (fun i ↦ ((v i).val : ℝ) / N) τ ^ (12 * N))).coeff (siegelCuspOrder N v) =
      cexp (2 * π * I / N) ^ (6 * (v 0).val * (v 1).val) *
        (if (v 0).val = 0 then (1 - cexp (2 * π * I / N) ^ (v 1).val) ^ (12 * N) else 1) := by
  have hfun : (fun τ : ℍ ↦ siegelFunction (fun i ↦ ((v i).val : ℝ) / N) τ ^ (12 * N)) =
      fun τ : ℍ ↦ 𝕢 N τ ^ siegelCuspOrder N v * siegelUnitFun N v τ :=
    funext (siegelFunction_zmod_pow_twelve_mul_eq v)
  rw [hfun, (meromorphicAt_and_laurentQExpansion_qParam_zpow_mul (Nat.cast_pos.mpr (NeZero.pos N))
      (siegelCuspOrder N v) (analyticAt_cuspFunction_siegelUnitFun v)).2,
    HahnSeries.coeff_single_mul, one_mul, PowerSeries.coeff_coe]
  simpa using qExpansion_siegelUnitFun_coeff_zero v

private theorem vecMul_div_eq (N : ℕ) (a : Fin 2 → ℤ) (γ : SL(2, ℤ)) :
    ((fun i ↦ (a i : ℝ) / N) ᵥ* (γ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom ℝ)) =
      fun j ↦ ((a ᵥ* (γ : Matrix (Fin 2) (Fin 2) ℤ)) j : ℝ) / N := by
  ext j
  simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two, add_div, mul_div_right_comm]

/-- **`g_{a/N}(γ • τ)^{12 N}` is meromorphic at `q_N = 0` for every cusp `γ • ∞`.** -/
theorem meromorphicAt_cuspFunction_siegelFunction_div_pow_twelve_mul (N : ℕ) (a : Fin 2 → ℤ)
    (γ : SL(2, ℤ)) :
    MeromorphicAt (cuspFunction N fun τ : ℍ ↦
      siegelFunction (fun i ↦ (a i : ℝ) / N) ↑(γ • τ) ^ (12 * N)) 0 := by
  rcases eq_or_ne N 0 with rfl | hN
  · simp only [mul_zero, pow_zero]
    exact UpperHalfPlane.meromorphicAt_cuspFunction_const 1
  have : NeZero N := ⟨hN⟩
  set b := a ᵥ* (γ : Matrix (Fin 2) (Fin 2) ℤ)
  set v : Fin 2 → ZMod N := fun i ↦ (b i : ZMod N)
  have hfun : (fun τ : ℍ ↦ siegelFunction (fun i ↦ (a i : ℝ) / N) ↑(γ • τ) ^ (12 * N)) =
      fun τ : ℍ ↦ 𝕢 N τ ^ siegelCuspOrder N v * siegelUnitFun N v τ := by
    funext τ
    rw [siegelFunction_pow_twelve_mul_smul, vecMul_div_eq,
      siegelFunction_div_pow_twelve_mul_eq_zmod b τ.im_pos,
      siegelFunction_zmod_pow_twelve_mul_eq v τ]
  rw [hfun]
  exact (meromorphicAt_and_laurentQExpansion_qParam_zpow_mul (Nat.cast_pos.mpr (NeZero.pos N))
    (siegelCuspOrder N v) (analyticAt_cuspFunction_siegelUnitFun v)).1

/-- **Cusp order of `g_{a/N}^{12 N}` at `γ • ∞`.** For `a ∉ N ℤ²`, the `q_N`-order of
`τ ↦ g_{a/N}(γ • τ)^{12 N}` at `i∞` is `siegelCuspOrder N ((a γ) mod N)`. -/
theorem meromorphicOrderAt_cuspFunction_siegelFunction_div_pow_twelve_mul {N : ℕ} [NeZero N]
    {a : Fin 2 → ℤ} (ha : (fun i ↦ (a i : ZMod N)) ≠ 0) (γ : SL(2, ℤ)) :
    meromorphicOrderAt (cuspFunction N fun τ : ℍ ↦
        siegelFunction (fun i ↦ (a i : ℝ) / N) ↑(γ • τ) ^ (12 * N)) 0 =
      siegelCuspOrder N (fun i ↦ ((a ᵥ* (γ : Matrix (Fin 2) (Fin 2) ℤ)) i : ZMod N)) := by
  set b := a ᵥ* (γ : Matrix (Fin 2) (Fin 2) ℤ)
  set v : Fin 2 → ZMod N := fun i ↦ (b i : ZMod N)
  have hv : v ≠ 0 := by
    intro hv0
    apply ha
    ext i
    have hb : b ᵥ* (↑γ⁻¹ : Matrix (Fin 2) (Fin 2) ℤ) = a := by
      simp only [b, Matrix.vecMul_vecMul, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
        Matrix.SpecialLinearGroup.coe_one, Matrix.vecMul_one]
    rw [← hb]
    have h0 : ∀ j, (b j : ZMod N) = 0 := congrFun hv0
    simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two, h0]
  have hmer := meromorphicAt_cuspFunction_siegelFunction_div_pow_twelve_mul N a γ
  rw [← UpperHalfPlane.orderTop_laurentQExpansion hmer]
  have hfun : (fun τ : ℍ ↦ siegelFunction (fun i ↦ (a i : ℝ) / N) ↑(γ • τ) ^ (12 * N)) =
      fun τ : ℍ ↦ 𝕢 N τ ^ siegelCuspOrder N v * siegelUnitFun N v τ := by
    funext τ
    rw [siegelFunction_pow_twelve_mul_smul, vecMul_div_eq,
      siegelFunction_div_pow_twelve_mul_eq_zmod b τ.im_pos,
      siegelFunction_zmod_pow_twelve_mul_eq v τ]
  rw [hfun, (meromorphicAt_and_laurentQExpansion_qParam_zpow_mul (Nat.cast_pos.mpr (NeZero.pos N))
      (siegelCuspOrder N v) (analyticAt_cuspFunction_siegelUnitFun v)).2,
    HahnSeries.orderTop_mul, HahnSeries.orderTop_single one_ne_zero, PowerSeries.orderTop_coe]
  have hord : (qExpansion N (siegelUnitFun N v)).order = 0 :=
    nonpos_iff_eq_zero.mp (PowerSeries.order_le 0 (qExpansion_siegelUnitFun_coeff_zero_ne_zero hv))
  simp [hord]

/-! ### Cusp meromorphy and cusp orders of `Γ(N)`-invariant Siegel products -/

private theorem isBoundedAtImInfty_of_tendsto_pow {g : ℍ → ℂ} {n : ℕ} (hn : 0 < n) {L : ℂ}
    (hL : Tendsto (fun τ : ℍ ↦ g τ ^ n) atImInfty (𝓝 L)) :
    IsBoundedAtImInfty g := by
  rw [IsBoundedAtImInfty, BoundedAtFilter, Asymptotics.isBigO_iff]
  refine ⟨max 1 (‖L‖ + 1), ?_⟩
  filter_upwards [hL.norm.eventually (gt_mem_nhds (lt_add_one ‖L‖))] with τ hτ
  simp only [Pi.one_apply, norm_one, mul_one]
  by_contra! hgt
  have h1 : 1 < ‖g τ‖ := (le_max_left 1 (‖L‖ + 1)).trans_lt hgt
  have hn_ge : ‖g τ‖ ≤ ‖g τ‖ ^ n := by
    conv_lhs => rw [← pow_one ‖g τ‖]
    exact pow_le_pow_right₀ h1.le hn
  rw [norm_pow] at hτ
  linarith [le_max_right 1 (‖L‖ + 1)]

/-- If `f` is holomorphic and `h`-periodic on `ℍ` and `f ^ n` (`n > 0`) has a meromorphic cusp
function at `0`, then so does `f`. -/
private theorem meromorphicAt_cuspFunction_of_pow {h : ℝ} (hh : 0 < h) {f : ℍ → ℂ}
    (hf : MDiff f) (hper : Function.Periodic (f ∘ ofComplex) h) {n : ℕ} (hn : 0 < n)
    (hpow : MeromorphicAt (cuspFunction h (f ^ n)) 0) :
    MeromorphicAt (cuspFunction h f) 0 := by
  obtain ⟨k, hk⟩ :
      ∃ k : ℕ, ((-k : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt (cuspFunction h (f ^ n)) 0 := by
    cases meromorphicOrderAt (cuspFunction h (f ^ n)) 0 using WithTop.recTopCoe with
    | top => exact ⟨0, le_top⟩
    | coe m => exact ⟨(-m).toNat, WithTop.coe_le_coe.mpr (by omega)⟩
  have han_pow := UpperHalfPlane.analyticAt_cuspFunction_qParam_pow_mul hpow hk
  have hper_pow : Function.Periodic ((fun τ : ℍ ↦ 𝕢 h τ ^ k * (f ^ n) τ) ∘ ofComplex) h :=
    fun z ↦ by
      simpa [Pi.pow_apply] using congrArg₂ (· * ·)
        (congrArg (· ^ k) (UpperHalfPlane.periodic_qParam_comp_ofComplex z))
        (congrArg (· ^ n) (hper z))
  have htend_pow : Tendsto (fun τ : ℍ ↦ 𝕢 h τ ^ k * f τ ^ n) atImInfty
      (𝓝 (cuspFunction h (fun τ : ℍ ↦ 𝕢 h τ ^ k * (f ^ n) τ) 0)) :=
    (han_pow.continuousAt.tendsto.comp (qParam_tendsto_atImInfty hh)).congr fun τ ↦
      eq_cuspFunction τ hh.ne' hper_pow
  set g : ℍ → ℂ := fun τ ↦ 𝕢 h τ ^ k * f τ
  have hL₀ : Tendsto (fun τ : ℍ ↦ 𝕢 h τ ^ ((n - 1) * k)) atImInfty
      (𝓝 ((0 : ℂ) ^ ((n - 1) * k))) :=
    ((continuous_pow ((n - 1) * k)).tendsto 0).comp (qParam_tendsto_atImInfty hh)
  have hL : Tendsto (fun τ : ℍ ↦ g τ ^ n) atImInfty
      (𝓝 ((0 : ℂ) ^ ((n - 1) * k) * cuspFunction h (fun τ : ℍ ↦ 𝕢 h τ ^ k * (f ^ n) τ) 0)) := by
    refine (hL₀.mul htend_pow).congr fun τ ↦ ?_
    simp only [g, mul_pow, ← pow_mul, ← mul_assoc]
    exact congrArg (· * f τ ^ n) (by
      rw [← pow_add]
      exact congrArg (𝕢 h (τ : ℂ) ^ ·)
        (by calc (n - 1) * k + k = (n - 1 + 1) * k := by ring
          _ = k * n := by rw [Nat.sub_add_cancel hn, mul_comm]))
  have hg_per : Function.Periodic (g ∘ ofComplex) h := fun z ↦ by
    simpa [g] using congrArg₂ (· * ·)
      (congrArg (· ^ k) (UpperHalfPlane.periodic_qParam_comp_ofComplex z)) (hper z)
  have hg_mdiff : MDiff g :=
    ((Function.Periodic.differentiable_qParam.mdifferentiable.comp
      mdifferentiable_coe).pow k).mul hf
  have han_g := _root_.UpperHalfPlane.analyticAt_cuspFunction_zero hh hg_per hg_mdiff
    (isBoundedAtImInfty_of_tendsto_pow hn hL)
  refine ((analyticAt_id.pow k).meromorphicAt.inv.mul han_g.meromorphicAt).congr ?_
  filter_upwards [UpperHalfPlane.cuspFunction_qParam_pow_mul_eventuallyEq hh k f,
    self_mem_nhdsWithin] with q h₁ hq
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hq
  change (q ^ k)⁻¹ * cuspFunction h (fun τ : ℍ ↦ 𝕢 h τ ^ k * f τ) q = cuspFunction h f q
  rw [h₁, inv_mul_cancel_left₀ (pow_ne_zero k hq)]

private theorem periodic_smul_of_Gamma_invariant {N : ℕ} {F : ℍ → ℂ}
    (hinv : ∀ {δ : SL(2, ℤ)}, δ ∈ CongruenceSubgroup.Gamma N → ∀ τ : ℍ, F (δ • τ) = F τ)
    (γ : SL(2, ℤ)) :
    Function.Periodic ((fun τ : ℍ ↦ F (γ • τ)) ∘ ofComplex) N := by
  refine UpperHalfPlane.periodic_comp_ofComplex fun τ ↦ ?_
  have hTN : ModularGroup.T ^ (N : ℤ) ∈ CongruenceSubgroup.Gamma N := by
    simpa using CongruenceSubgroup.ModularGroup_T_pow_mem_Gamma N N dvd_rfl
  have hconj : γ * ModularGroup.T ^ (N : ℤ) * γ⁻¹ ∈ CongruenceSubgroup.Gamma N := by
    simpa using (CongruenceSubgroup.Gamma_normal N).conj_mem _ hTN γ
  have hsmul : (N : ℝ) +ᵥ τ = (ModularGroup.T ^ (N : ℤ)) • τ := by
    simpa using (UpperHalfPlane.modular_T_zpow_smul τ (N : ℤ)).symm
  rw [hsmul, ← mul_smul]
  have hgrp : γ * ModularGroup.T ^ (N : ℤ) = (γ * ModularGroup.T ^ (N : ℤ) * γ⁻¹) * γ := by group
  rw [hgrp, mul_smul]
  exact hinv hconj (γ • τ)

private theorem meromorphicAt_cuspFunction_finset_prod {h : ℝ} {ι : Type*} (s : Finset ι)
    {f : ι → ℍ → ℂ} (hf : ∀ i ∈ s, MeromorphicAt (cuspFunction h (f i)) 0) :
    MeromorphicAt (cuspFunction h fun τ : ℍ ↦ ∏ i ∈ s, f i τ) 0 := by
  induction s using Finset.cons_induction with
  | empty =>
    simp
  | cons x t hxt ih =>
    simp only [Finset.prod_cons]
    exact UpperHalfPlane.meromorphicAt_cuspFunction_mul (hf x (Finset.mem_cons_self x t))
      (ih fun i hi ↦ hf i (Finset.mem_cons_of_mem hi))

private theorem meromorphicAt_cuspFunction_prod_siegelFunction_div_zpow_of_ne_zero
    {N : ℕ} [NeZero N] {ι : Type*} (s : Finset ι) (a : ι → Fin 2 → ℤ) (m : ι → ℤ)
    (ha : ∀ i ∈ s, (fun j ↦ (a i j : ZMod N)) ≠ 0)
    (h₀ : ((Nat.gcd 2 N * N : ℕ) : ℤ) ∣ ∑ i ∈ s, m i * a i 0 ^ 2)
    (h₁ : ((Nat.gcd 2 N * N : ℕ) : ℤ) ∣ ∑ i ∈ s, m i * a i 1 ^ 2)
    (h₀₁ : (N : ℤ) ∣ ∑ i ∈ s, m i * (a i 0 * a i 1))
    (h₁₂ : (12 : ℤ) ∣ Nat.gcd 12 N * ∑ i ∈ s, m i) (γ : SL(2, ℤ)) :
    MeromorphicAt (cuspFunction N fun τ : ℍ ↦
      ∏ i ∈ s, siegelFunction (fun j ↦ (a i j : ℝ) / N) ↑(γ • τ) ^ m i) 0 := by
  set F : ℍ → ℂ := fun τ ↦ ∏ i ∈ s, siegelFunction (fun j ↦ (a i j : ℝ) / N) τ ^ m i
  have hF_mdiff : MDiff F := by
    have hF_eq : F = ∏ i ∈ s, fun τ : ℍ ↦ siegelFunction (fun j ↦ (a i j : ℝ) / N) τ ^ m i :=
      funext fun τ ↦ by simp [F]
    rw [hF_eq]
    refine MDifferentiable.prod fun i hi τ ↦ ?_
    have hne := siegelFunction_ne_zero
      ((forall_div_ne_intCast_iff_zmod_ne_zero (a i)).mpr (ha i hi)) τ.im_pos
    rcases Int.eq_nat_or_neg (m i) with ⟨k, hk | hk⟩
    · simp only [hk, zpow_natCast]
      exact (mdifferentiable_siegelFunction _ τ).pow k
    · simp only [hk, zpow_neg, zpow_natCast]
      exact ((mdifferentiable_siegelFunction _ τ).pow k).inv (pow_ne_zero k hne)
  have hγ : MDiff (fun τ : ℍ ↦ γ • τ) := by
    have hsmul : (fun τ : ℍ ↦ Matrix.SpecialLinearGroup.mapGL ℝ γ • τ) = fun τ : ℍ ↦ γ • τ :=
      funext fun τ ↦ Matrix.SpecialLinearGroup.mapGL_smul γ τ
    rw [← hsmul]
    exact mdifferentiable_smul (g := Matrix.SpecialLinearGroup.mapGL ℝ γ) (by simp)
  have hper : Function.Periodic ((fun τ : ℍ ↦ F (γ • τ)) ∘ ofComplex) N :=
    periodic_smul_of_Gamma_invariant
      (fun hδ τ ↦ prod_siegelFunction_div_zpow_smul_of_mem_Gamma s a m h₀ h₁ h₀₁ h₁₂ hδ τ) γ
  refine meromorphicAt_cuspFunction_of_pow (Nat.cast_pos.mpr (NeZero.pos N))
    (hF_mdiff.comp hγ) hper (by have := NeZero.pos N; positivity : 0 < 12 * N) ?_
  have hpow_eq : ((fun τ : ℍ ↦ F (γ • τ)) ^ (12 * N)) =
      fun τ : ℍ ↦ ∏ i ∈ s,
        (siegelFunction (fun j ↦ (a i j : ℝ) / N) ↑(γ • τ) ^ (12 * N)) ^ m i := by
    funext τ
    simp only [F, Pi.pow_apply, ← Finset.prod_pow]
    refine Finset.prod_congr rfl fun i _ ↦ ?_
    rw [← zpow_natCast, ← zpow_mul, mul_comm (m i), zpow_mul, zpow_natCast]
  rw [hpow_eq]
  refine meromorphicAt_cuspFunction_finset_prod s fun i _ ↦ ?_
  exact ((meromorphicAt_cuspFunction_siegelFunction_div_pow_twelve_mul N (a i) γ).zpow (m i)).congr
    (UpperHalfPlane.cuspFunction_map_eventuallyEq (· ^ m i) _).symm

/-- **Cusp meromorphy of `Γ(N)`-invariant Kubert–Lang products.** Every product
`∏ i ∈ s, g_{aᵢ/N}^{mᵢ}` satisfying the Kubert–Lang congruence relations is meromorphic at every
cusp `γ • ∞`. -/
theorem meromorphicAt_cuspFunction_prod_siegelFunction_div_zpow {N : ℕ}
    {ι : Type*} (s : Finset ι) (a : ι → Fin 2 → ℤ) (m : ι → ℤ)
    (h₀ : ((Nat.gcd 2 N * N : ℕ) : ℤ) ∣ ∑ i ∈ s, m i * a i 0 ^ 2)
    (h₁ : ((Nat.gcd 2 N * N : ℕ) : ℤ) ∣ ∑ i ∈ s, m i * a i 1 ^ 2)
    (h₀₁ : (N : ℤ) ∣ ∑ i ∈ s, m i * (a i 0 * a i 1))
    (h₁₂ : (12 : ℤ) ∣ Nat.gcd 12 N * ∑ i ∈ s, m i) (γ : SL(2, ℤ)) :
    MeromorphicAt (cuspFunction N fun τ : ℍ ↦
      ∏ i ∈ s, siegelFunction (fun j ↦ (a i j : ℝ) / N) ↑(γ • τ) ^ m i) 0 := by
  rcases eq_or_ne N 0 with rfl | hN
  · have hconst : (fun τ : ℍ ↦
        ∏ i ∈ s, siegelFunction (fun j ↦ (a i j : ℝ) / (0 : ℕ)) ↑(γ • τ) ^ m i) =
        Function.const ℍ (∏ i ∈ s, (0 : ℂ) ^ m i) := by
      funext τ
      simp [div_zero, show (fun _ : Fin 2 ↦ (0 : ℝ)) = 0 from rfl]
    rw [hconst]
    exact UpperHalfPlane.meromorphicAt_cuspFunction_const _
  have : NeZero N := ⟨hN⟩
  let s' := s.filter fun i ↦ m i ≠ 0
  have hprod : (fun τ : ℍ ↦ ∏ i ∈ s, siegelFunction (fun j ↦ (a i j : ℝ) / N) ↑(γ • τ) ^ m i) =
      fun τ : ℍ ↦ ∏ i ∈ s', siegelFunction (fun j ↦ (a i j : ℝ) / N) ↑(γ • τ) ^ m i := by
    funext τ
    refine (Finset.prod_subset (Finset.filter_subset _ s) fun i hi hni ↦ ?_).symm
    have hm0 : m i = 0 := by simpa [s', hi] using hni
    simp [hm0]
  have hsum (w : ι → ℤ) : ∑ i ∈ s, m i * w i = ∑ i ∈ s', m i * w i := by
    refine (Finset.sum_subset (Finset.filter_subset _ s) fun i hi hni ↦ ?_).symm
    have hm0 : m i = 0 := by simpa [s', hi] using hni
    simp [hm0]
  have hsum1 : ∑ i ∈ s, m i = ∑ i ∈ s', m i := by simpa using hsum fun _ ↦ 1
  by_cases ha : ∀ i ∈ s', (fun j ↦ (a i j : ZMod N)) ≠ 0
  · rw [hprod]
    exact meromorphicAt_cuspFunction_prod_siegelFunction_div_zpow_of_ne_zero s' a m ha
      (hsum (fun i ↦ a i 0 ^ 2) ▸ h₀) (hsum (fun i ↦ a i 1 ^ 2) ▸ h₁)
      (hsum (fun i ↦ a i 0 * a i 1) ▸ h₀₁) (hsum1 ▸ h₁₂) γ
  · obtain ⟨i₀, hi₀, hz⟩ := by push Not at ha; exact ha
    obtain ⟨t, ht⟩ : ∃ t : Fin 2 → ℤ, (fun j ↦ (a i₀ j : ℝ) / N) = fun j ↦ (t j : ℝ) := by
      by_contra! ht
      exact (forall_div_ne_intCast_iff_zmod_ne_zero (a i₀)).mp ht hz
    have h0 : (fun τ : ℍ ↦ ∏ i ∈ s', siegelFunction (fun j ↦ (a i j : ℝ) / N) ↑(γ • τ) ^ m i) =
        Function.const ℍ 0 :=
      funext fun τ ↦ Finset.prod_eq_zero hi₀
        (by rw [ht, siegelFunction_intCast, zero_zpow _ (Finset.mem_filter.mp hi₀).2])
    rw [hprod, h0]
    exact UpperHalfPlane.meromorphicAt_cuspFunction_const 0

/-- **Cusp order of a `Γ(N)`-invariant Kubert–Lang product at `γ • ∞`.** Multiplied by `12 N`, the
`q_N`-order at `γ • ∞` of `∏ i ∈ s, g_{aᵢ/N}^{mᵢ}` equals
`∑ i ∈ s, mᵢ * siegelCuspOrder N ((aᵢ γ) mod N)`. -/
theorem meromorphicOrderAt_cuspFunction_prod_siegelFunction_div_zpow {N : ℕ} [NeZero N]
    {ι : Type*} (s : Finset ι) (a : ι → Fin 2 → ℤ) (m : ι → ℤ)
    (ha : ∀ i ∈ s, (fun j ↦ (a i j : ZMod N)) ≠ 0)
    (h₀ : ((Nat.gcd 2 N * N : ℕ) : ℤ) ∣ ∑ i ∈ s, m i * a i 0 ^ 2)
    (h₁ : ((Nat.gcd 2 N * N : ℕ) : ℤ) ∣ ∑ i ∈ s, m i * a i 1 ^ 2)
    (h₀₁ : (N : ℤ) ∣ ∑ i ∈ s, m i * (a i 0 * a i 1))
    (h₁₂ : (12 : ℤ) ∣ Nat.gcd 12 N * ∑ i ∈ s, m i) (γ : SL(2, ℤ)) :
    ↑(12 * N) * meromorphicOrderAt (cuspFunction N fun τ : ℍ ↦
        ∏ i ∈ s, siegelFunction (fun j ↦ (a i j : ℝ) / N) ↑(γ • τ) ^ m i) 0 =
      ((∑ i ∈ s, m i *
        siegelCuspOrder N (fun j ↦ ((a i ᵥ* (γ : Matrix (Fin 2) (Fin 2) ℤ)) j : ZMod N)) : ℤ) :
          WithTop ℤ) := by
  have hmer := meromorphicAt_cuspFunction_prod_siegelFunction_div_zpow s a m h₀ h₁ h₀₁ h₁₂ γ
  rw [← meromorphicOrderAt_pow (n := 12 * N) hmer, Pi.pow_def, ← meromorphicOrderAt_congr
    (UpperHalfPlane.cuspFunction_map_eventuallyEq (· ^ (12 * N)) _)]
  have hpow_eq : (fun τ : ℍ ↦ (∏ i ∈ s,
      siegelFunction (fun j ↦ (a i j : ℝ) / N) ↑(γ • τ) ^ m i) ^ (12 * N)) =
      fun τ : ℍ ↦ ∏ i ∈ s,
        (siegelFunction (fun j ↦ (a i j : ℝ) / N) ↑(γ • τ) ^ (12 * N)) ^ m i := by
    funext τ
    rw [← Finset.prod_pow]
    refine Finset.prod_congr rfl fun i _ ↦ ?_
    rw [← zpow_natCast, ← zpow_mul, mul_comm (m i), zpow_mul, zpow_natCast]
  rw [hpow_eq]
  clear hmer hpow_eq h₀ h₁ h₀₁ h₁₂
  have hfactor_mer (i : ι) : MeromorphicAt (cuspFunction N fun τ : ℍ ↦
      (siegelFunction (fun j ↦ (a i j : ℝ) / N) ↑(γ • τ) ^ (12 * N)) ^ m i) 0 :=
    ((meromorphicAt_cuspFunction_siegelFunction_div_pow_twelve_mul N (a i) γ).zpow (m i)).congr
      (UpperHalfPlane.cuspFunction_map_eventuallyEq (· ^ m i) _).symm
  induction s using Finset.cons_induction with
  | empty => simp [meromorphicOrderAt_const]
  | cons x t hxt ih =>
    have hx_ne := ha x (Finset.mem_cons_self x t)
    have ht_ne : ∀ i ∈ t, (fun j ↦ (a i j : ZMod N)) ≠ 0 :=
      fun i hi ↦ ha i (Finset.mem_cons_of_mem hi)
    have hx_ord : meromorphicOrderAt (cuspFunction N fun τ : ℍ ↦
        (siegelFunction (fun j ↦ (a x j : ℝ) / N) ↑(γ • τ) ^ (12 * N)) ^ m x) 0 =
        ((m x * siegelCuspOrder N
          (fun j ↦ ((a x ᵥ* (γ : Matrix (Fin 2) (Fin 2) ℤ)) j : ZMod N)) : ℤ) : WithTop ℤ) := by
      have hm0 := meromorphicAt_cuspFunction_siegelFunction_div_pow_twelve_mul N (a x) γ
      rw [meromorphicOrderAt_congr (UpperHalfPlane.cuspFunction_map_eventuallyEq (· ^ m x) _)]
      change meromorphicOrderAt
        ((cuspFunction N fun τ : ℍ ↦
          siegelFunction (fun j ↦ (a x j : ℝ) / N) ↑(γ • τ) ^ (12 * N)) ^ m x) 0 = _
      rw [meromorphicOrderAt_zpow hm0,
        meromorphicOrderAt_cuspFunction_siegelFunction_div_pow_twelve_mul hx_ne γ,
        ← WithTop.coe_mul]
    simp only [Finset.prod_cons, Finset.sum_cons]
    rw [meromorphicOrderAt_congr (UpperHalfPlane.cuspFunction_map₂_eventuallyEq (· * ·) _ _),
      ← Pi.mul_def, meromorphicOrderAt_mul (hfactor_mer x)
        (meromorphicAt_cuspFunction_finset_prod t fun i _ ↦ hfactor_mer i),
      hx_ord, ih ht_ne, ← WithTop.coe_add]

end TauCeti.ModularForm
