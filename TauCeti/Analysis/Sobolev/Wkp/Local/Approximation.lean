/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Wkp.Approximation
public import TauCeti.Analysis.Sobolev.Wkp.Mollification
public import TauCeti.Analysis.Sobolev.Wkp.Zero
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import TauCeti.MeasureTheory.Function.LpSeminorm.ContinuousOn

/-!
# Local smooth approximation in higher-order Sobolev spaces

On an open subdomain with compact closure inside `Ω`, restrictions of test functions on `Ω`
approximate every `W^{k,p}(Ω)` function in the full Sobolev norm, for `1 ≤ p < ∞`.
No regularity of the boundary is needed. The approximants control every weak derivative through
order `k`, and are smooth on the entire larger domain. This is the local approximation step
in the Meyers–Serrin theorem; it does not assert global density on an arbitrary open domain.

The construction mollifies zero extensions at radii smaller than the distance to the boundary,
then multiplies the smooth representative by a fixed test function equal to one near the
smaller domain. Interior derivative identities identify all its derivatives with mollified
weak derivative fields.

The mollified fields `TauCeti.Wkp.smoothField` converge in `Lᵖ(Ω)` as the bump radii tend to zero
(`TauCeti.Wkp.tendsto_eLpNorm_smoothField_sub`). For a map `A` continuous on `Ω` whose weak
derivative is `Lᵖ` on compact subsets, they converge uniformly on every compact `K ⊆ Ω`, with
derivatives converging in `Lᵖ(K)`
(`TauCeti.HasWeakFDerivOn.exists_contDiff_tendsto_of_continuousOn`). For a `W^{2,p}(Ω)` function
with a continuous representative `ū`, a single mollification is then a smooth function close to `ū`
uniformly on a given compact subset `K` of `Ω` and with Hessian close to the weak Hessian in `Lᵖ(K)`
(`TauCeti.Wkp.exists_contDiff_abs_sub_le_and_eLpNorm_fderiv_gradient_sub_le`). This is how estimates
for classical solutions of second-order equations pass to strong solutions.

## References

L. C. Evans, *Partial Differential Equations*, Chapter 5, §5.3.1. The proof uses the
interior convolution identities and the local `Lᵖ` approximate identity already in Tau Ceti.
-/

public section

noncomputable section

namespace TauCeti.Wkp

open Filter MeasureTheory Set TopologicalSpace
open scoped Convolution Distributions ENNReal Gradient Topology

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {Omega U : Opens E} {p : ENNReal} [Fact (1 ≤ p)]

local instance : (mu.restrict (univ : Set E)).IsAddHaarMeasure := by
  rw [Measure.restrict_univ]
  infer_instance

/-- A localized smooth representative, with compact support in the original domain. -/
private def localTest (chi : 𝓓(Omega, ℝ)) (phi : ContDiffBump (0 : E))
    (k : ℕ) (u : Wkp mu Omega p k) : 𝓓(Omega, ℝ) :=
  ⟨fun x => chi x * smoothField phi (value k u) x,
    chi.contDiff.mul (contDiff_smoothField phi _),
    chi.hasCompactSupport.mul_right,
    tsupport_mul_subset_left.trans chi.tsupport_subset⟩

private theorem localTest_lowerOrder (chi : 𝓓(Omega, ℝ)) (phi : ContDiffBump (0 : E))
    (k : ℕ) (u : Wkp mu Omega p (k + 1)) :
    localTest chi phi k (lowerOrder k u) = localTest chi phi (k + 1) u := by
  ext x
  simp only [localTest, value_succ]

private theorem localTest_eventuallyEq (chi : 𝓓(Omega, ℝ))
    (hchi : ∀ x ∈ U, chi x = 1) (phi : ContDiffBump (0 : E))
    (k : ℕ) (u : Wkp mu Omega p k) (x : E) (hx : x ∈ U) :
    (localTest chi phi k u : E → ℝ) =ᶠ[𝓝 x] smoothField phi (value k u) := by
  filter_upwards [U.isOpen.mem_nhds hx] with y hy
  simp [localTest, hchi y hy]

private theorem iteratedGradient_localTest (chi : 𝓓(Omega, ℝ))
    (hchi : ∀ x ∈ U, chi x = 1) (phi : ContDiffBump (0 : E))
    (hphi : ∀ x ∈ U, Metric.closedBall x phi.rOut ⊆ Omega) :
    ∀ (k : ℕ) (u : Wkp mu Omega p (k + 1)) (x : E), x ∈ U →
      iteratedGradientTestFunction (localTest chi phi (k + 1) u) k x =
        smoothField phi (iteratedGradient k u) x := by
  intro k
  induction k with
  | zero =>
      intro u x hx
      simp only [iteratedGradientTestFunction_zero]
      rw [(localTest_eventuallyEq chi hchi phi 1 u x hx).gradient_eq]
      exact gradient_smoothField u phi x (hphi x hx)
  | succ k ih =>
      intro u x hx
      rw [iteratedGradientTestFunction_succ, ← localTest_lowerOrder chi phi (k + 1) u]
      have heq : iteratedGradientTestFunction
          (localTest chi phi (k + 1) (lowerOrder (k + 1) u)) k =ᶠ[𝓝 x]
          smoothField phi (iteratedGradient k (lowerOrder (k + 1) u)) := by
        filter_upwards [U.isOpen.mem_nhds hx] with y hy using ih _ y hy
      rw [heq.fderiv_eq]
      exact fderiv_smoothField k u phi x (hphi x hx)

/-- The restricted `Lᵖ` class of a mollified zero extension used in the approximation. -/
private def localAverage {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (hp : p ≠ ∞) (phi : ContDiffBump (0 : E))
    (f : Lp F p (mu.restrict Omega)) : Lp F p (mu.restrict U) :=
  Lp.LpToLpOfMeasureLeSMul (c := 1) (by simp) (by
    simpa only [one_smul] using Measure.restrict_mono_set mu (subset_univ (U : Set E)))
      (normedBumpLp hp phi (mu.restrict univ)
        (extendByZeroLpₗᵢ ℝ mu Omega.isOpen.measurableSet (subset_univ _) f))

private theorem localAverage_ae {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace F] (hp : p ≠ ∞) (phi : ContDiffBump (0 : E))
    (f : Lp F p (mu.restrict Omega)) :
    localAverage (U := U) hp phi f =ᵐ[mu.restrict U] smoothField phi f := by
  have he := normedBumpLp_extendByZero_ae_eq_convolution hp phi Omega.isOpen.measurableSet f
  have he' := he.filter_mono
    (ae_mono (Measure.restrict_mono_set mu (subset_univ (U : Set E))))
  exact (Lp.coeFn_LpToLpOfMeasureLeSMul _ _ _).trans (by
    simpa only [Measure.restrict_univ, smoothField_def] using he')

/-- As the bump radii tend to zero, the mollifications of a zero-extended field
`f ∈ Lᵖ(Ω; F)`, `p < ∞`, converge to `f` in `Lᵖ(Ω; F)`. -/
theorem tendsto_eLpNorm_smoothField_sub {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace F] (hp : p ≠ ∞) {I : Type*} {l : Filter I} {phi : I → ContDiffBump (0 : E)}
    (hphi : Tendsto (fun i => (phi i).rOut) l (𝓝 0)) (f : Lp F p (mu.restrict Omega)) :
    Tendsto (fun i => eLpNorm (smoothField (phi i) f - (f : E → F)) p (mu.restrict Omega)) l
      (𝓝 0) := by
  have h := (Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ _).1
    (tendsto_normedBumpLp_extendByZero_restrict hp Omega.isOpen.measurableSet subset_rfl hphi f)
  refine h.congr fun i => eLpNorm_congr_ae ?_
  filter_upwards [localAverage_ae (U := Omega) hp (phi i) f,
    Lp.coeFn_LpToLpOfMeasureLeSMul (μ := mu.restrict (Omega : Set E))
      (ν := mu.restrict (Omega : Set E)) (c := 1) (by simp) (by simp) f] with x h1 h2
  simp only [Pi.sub_apply, ← h1, h2, localAverage]

/-- The restriction to `U` of the `W^{k,p}(Ω)` element of a test function is represented on `U`
by that test function. -/
theorem value_restrictL_ofTestFunctionₗ_ae (hU : U ≤ Omega) (k : ℕ) (phi : 𝓓(Omega, ℝ)) :
    (value k (restrictL hU k (ofTestFunctionₗ (mu := mu) (p := p) k phi)) : E → ℝ)
      =ᵐ[mu.restrict U] phi := by
  have hmono : ae (mu.restrict (U : Set E)) ≤ ae (mu.restrict (Omega : Set E)) :=
    ae_mono (Measure.restrict_mono_set mu (SetLike.coe_subset_coe.mpr hU))
  filter_upwards [value_restrictL_ae hU k (ofTestFunctionₗ (mu := mu) (p := p) k phi),
    (testFunctionLp_apply_ae (mu := mu) p phi).filter_mono hmono] with x h1 h2
  rw [h1, value_ofTestFunctionₗ, h2]

private theorem value_restrict_localTest (hp : p ≠ ∞) (hU : U ≤ Omega)
    (chi : 𝓓(Omega, ℝ)) (hchi : ∀ x ∈ U, chi x = 1)
    (phi : ContDiffBump (0 : E)) (k : ℕ) (u : Wkp mu Omega p k) :
    value k (restrictL hU k (ofTestFunctionₗ (mu := mu) (p := p) k (localTest chi phi k u))) =
      localAverage hp phi (value k u) := by
  apply Lp.ext
  filter_upwards [value_restrictL_ofTestFunctionₗ_ae (mu := mu) (p := p) hU k
      (localTest chi phi k u),
    localAverage_ae (U := U) hp phi (value k u), ae_restrict_mem U.isOpen.measurableSet]
    with x hr ha hx
  rw [hr, ha]
  simp [localTest, hchi x hx]

private theorem iteratedGradient_restrict_localTest (hp : p ≠ ∞) (hU : U ≤ Omega)
    (chi : 𝓓(Omega, ℝ)) (hchi : ∀ x ∈ U, chi x = 1)
    (phi : ContDiffBump (0 : E))
    (hphi : ∀ x ∈ U, Metric.closedBall x phi.rOut ⊆ Omega)
    (k : ℕ) (u : Wkp mu Omega p (k + 1)) :
    iteratedGradient k (restrictL hU (k + 1)
      (ofTestFunctionₗ (mu := mu) (p := p) (k + 1) (localTest chi phi (k + 1) u))) =
        localAverage hp phi (iteratedGradient k u) := by
  apply Lp.ext
  filter_upwards [iteratedGradient_restrictL_ae hU k
      (ofTestFunctionₗ (mu := mu) (p := p) (k + 1) (localTest chi phi (k + 1) u)),
    iteratedGradientTestFunctionLp_apply_ae (mu := mu) p k
      (localTest chi phi (k + 1) u) |>.filter_mono
        (ae_mono (Measure.restrict_mono_set mu (SetLike.coe_subset_coe.mpr hU))),
    localAverage_ae (U := U) hp phi (iteratedGradient k u),
    ae_restrict_mem U.isOpen.measurableSet] with x hr ht ha hx
  rw [hr, iteratedGradient_ofTestFunctionₗ, ht, ha]
  exact iteratedGradient_localTest chi hchi phi hphi k u x hx

private theorem tendsto_restrict_localTest (hp : p ≠ ∞) (hU : U ≤ Omega)
    (chi : 𝓓(Omega, ℝ)) (hchi : ∀ x ∈ U, chi x = 1)
    {I : Type*} {l : Filter I} {phi : I → ContDiffBump (0 : E)}
    (hphi : Tendsto (fun i => (phi i).rOut) l (𝓝 0))
    (hinterior : ∀ i x, x ∈ U → Metric.closedBall x (phi i).rOut ⊆ Omega) :
    ∀ (k : ℕ) (u : Wkp mu Omega p k),
      Tendsto (fun i => restrictL hU k
        (ofTestFunctionₗ (mu := mu) (p := p) k (localTest chi (phi i) k u)))
        l (𝓝 (restrictL hU k u)) := by
  intro k u
  refine tendsto_of_tendsto_iteratedGradient (P := fun _ _ => True) (fun _ _ _ => trivial)
    (v := fun k u _ i => restrictL hU k
      (ofTestFunctionₗ (mu := mu) (p := p) k (localTest chi (phi i) k u)))
    (w := fun k u => restrictL hU k u) (fun k u _ i => ?_)
    (fun k u => lowerOrder_restrictL hU k u) (fun u _ => ?_) (fun k u _ => ?_) k u trivial
  · rw [lowerOrder_restrictL, lowerOrder_ofTestFunctionₗ, localTest_lowerOrder]
  · have h : Tendsto (fun i => localAverage hp (phi i) (value 0 u)) l
        (𝓝 (value 0 (restrictL hU 0 u))) :=
      Wkp.tendsto_mollified_value hp hU hphi 0 u
    simp only [value_zero] at h
    convert h using 1
    funext i
    simpa only [value_zero] using value_restrict_localTest hp hU chi hchi (phi i) 0 u
  · have h : Tendsto (fun i => localAverage hp (phi i) (iteratedGradient k u)) l
        (𝓝 (iteratedGradient k (restrictL hU (k + 1) u))) :=
      Wkp.tendsto_mollified_iteratedGradient hp hU hphi k u
    simpa only [← iteratedGradient_restrict_localTest hp hU chi hchi _ (hinterior _) k u] using h

/-- On every open subdomain with compact closure inside `Ω`, restrictions of test functions
on `Ω` approximate the restriction of a `W^{k,p}(Ω)` element in the full Sobolev norm.
The order is arbitrary, and no boundary regularity is assumed. -/
theorem exists_testFunction_approximation_restrictL (hp : p ≠ ∞)
    (hcompact : IsCompact (closure (U : Set E)))
    (hclosure : closure (U : Set E) ⊆ Omega) (k : ℕ) (u : Wkp mu Omega p k) :
    ∃ psi : ℕ → 𝓓(Omega, ℝ),
      Tendsto (fun j => restrictL (SetLike.coe_subset_coe.mp (subset_closure.trans hclosure)) k
        (ofTestFunctionₗ (mu := mu) (p := p) k (psi j))) atTop
        (𝓝 (restrictL (SetLike.coe_subset_coe.mp (subset_closure.trans hclosure)) k u)) := by
  obtain ⟨chi, hchi, -, hchi_one, hchi_cpt, hchi_ts⟩ :=
    hcompact.exists_contDiff_cutoff_eventuallyEq_one Omega.isOpen hclosure
  let chiTest : 𝓓(Omega, ℝ) := ⟨chi, hchi, hchi_cpt, hchi_ts⟩
  have hchiU : ∀ x ∈ U, chiTest x = 1 := by
    intro x hx
    simpa only [chiTest, TestFunction.coe_mk] using
      (hchi_one x (subset_closure hx)).self_of_nhds
  obtain ⟨δ, hδ, hδO⟩ := hcompact.exists_cthickening_subset_open Omega.isOpen hclosure
  let phi : ℕ → ContDiffBump (0 : E) := fun j =>
    ⟨(δ / ((j : ℝ) + 1)) / 2, δ / ((j : ℝ) + 1), by positivity,
      half_lt_self (by positivity)⟩
  have hphi : Tendsto (fun j => (phi j).rOut) atTop (𝓝 0) := by
    simpa only [phi, div_eq_mul_inv, one_mul, mul_zero] using
      (tendsto_const_nhds (x := δ)).mul tendsto_one_div_add_atTop_nhds_zero_nat
  refine ⟨fun j => localTest chiTest (phi j) k u,
    tendsto_restrict_localTest hp _ chiTest hchiU hphi ?_ k u⟩
  intro j x hx
  exact (Metric.closedBall_subset_closedBall (by
    dsimp [phi]
    exact div_le_self hδ.le (by nlinarith [Nat.cast_nonneg (α := ℝ) j]))).trans
      ((Metric.closedBall_subset_cthickening (subset_closure hx) δ).trans hδO)

/-- The restriction of a `W^{k,p}(Ω)` function to an open subdomain compactly contained in `Ω`
is in the Sobolev-norm closure of restrictions of test functions on the larger domain. -/
theorem restrictL_mem_closure_range_ofTestFunctionₗ (hp : p ≠ ∞)
    (hcompact : IsCompact (closure (U : Set E)))
    (hclosure : closure (U : Set E) ⊆ Omega) (k : ℕ) (u : Wkp mu Omega p k) :
    restrictL (SetLike.coe_subset_coe.mp (subset_closure.trans hclosure)) k u ∈
      closure (Set.range (fun psi : 𝓓(Omega, ℝ) =>
        restrictL (SetLike.coe_subset_coe.mp (subset_closure.trans hclosure)) k
          (ofTestFunctionₗ (mu := mu) (p := p) k psi))) := by
  obtain ⟨psi, hpsi⟩ := exists_testFunction_approximation_restrictL hp hcompact hclosure k u
  exact mem_closure_of_tendsto hpsi (Eventually.of_forall fun j => ⟨psi j, rfl⟩)

/-- The order-one case of `TauCeti.Wkp.restrictL_mem_closure_range_ofTestFunctionₗ`, stated with
`W1p.restrictL` and `W1p.ofTestFunctionₗ` so that first-order callers need not rewrite through
`Wkp.restrictL_one` and `Wkp.ofTestFunctionₗ_one`. -/
theorem _root_.TauCeti.W1p.restrictL_mem_closure_range_ofTestFunctionₗ (hp : p ≠ ∞)
    (hcompact : IsCompact (closure (U : Set E)))
    (hclosure : closure (U : Set E) ⊆ Omega) (u : W1p mu Omega p) :
    W1p.restrictL (SetLike.coe_subset_coe.mp (subset_closure.trans hclosure)) u ∈
      closure (Set.range (fun psi : 𝓓(Omega, ℝ) =>
        W1p.restrictL (SetLike.coe_subset_coe.mp (subset_closure.trans hclosure))
          (W1p.ofTestFunctionₗ mu Omega p psi))) := by
  have h := Wkp.restrictL_mem_closure_range_ofTestFunctionₗ hp hcompact hclosure 1 u
  simp only [Wkp.restrictL_one, Wkp.ofTestFunctionₗ_one] at h
  exact h

/-- **Smooth approximation of a continuous Sobolev map near a compact set.** Let `A` be continuous
on `Ω` with a weak derivative `DA` that is `Lᵖ` on every compact subset of `Ω`, `p < ∞`. For every
compact `K ⊆ Ω` there are smooth maps `A' n` with `A' n → A` uniformly on `K` and
`fderiv (A' n) → DA` in `Lᵖ(K)`. -/
theorem _root_.TauCeti.HasWeakFDerivOn.exists_contDiff_tendsto_of_continuousOn {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] (hp : p ≠ ∞) {A : E → F} {DA : E → E →L[ℝ] F}
    (hA : HasWeakFDerivOn mu Omega A DA) (hAc : ContinuousOn A Omega)
    (hDA : ∀ L, IsCompact L → L ⊆ Omega → MemLp DA p (mu.restrict L)) {K : Set E}
    (hK : IsCompact K) (hKΩ : K ⊆ Omega) :
    ∃ A' : ℕ → E → F, (∀ n, ContDiff ℝ (⊤ : ℕ∞) (A' n)) ∧ TendstoUniformlyOn A' A atTop K ∧
      Tendsto (fun n => eLpNorm (fderiv ℝ (A' n) - DA) p (mu.restrict K)) atTop (𝓝 0) := by
  have := hA.completeSpace
  obtain ⟨W, hWo, hKW, hWΩ, hWc⟩ := exists_open_between_and_isCompact_closure hK Omega.isOpen hKΩ
  let U : Opens E := ⟨W, hWo⟩
  have hUΩ : U ≤ Omega := subset_closure.trans hWΩ
  obtain ⟨δ, hδ, hKδ⟩ := hK.exists_cthickening_subset_open hWo hKW
  have : IsFiniteMeasure (mu.restrict (U : Set E)) :=
    isFiniteMeasure_restrict.2 ((measure_mono subset_closure).trans_lt hWc.measure_lt_top).ne
  have hAp : MemLp A p (mu.restrict (U : Set E)) :=
    ((hAc.mono hWΩ).memLp_top_restrict_of_subset_isCompact hWc hWo.measurableSet
      subset_closure).mono_exponent le_top
  have hDAp : MemLp DA p (mu.restrict (U : Set E)) :=
    (hDA _ hWc hWΩ).mono_measure (Measure.restrict_mono subset_closure le_rfl)
  let φ : ℕ → ContDiffBump (0 : E) := fun n =>
    ⟨((n : ℝ) + 1)⁻¹ / 2, ((n : ℝ) + 1)⁻¹, by positivity, half_lt_self (by positivity)⟩
  have hφ : Tendsto (fun n => (φ n).rOut) atTop (𝓝 0) := by
    simpa only [one_div] using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  set fA : Lp F p (mu.restrict (U : Set E)) := hAp.toLp A
  set fD : Lp (E →L[ℝ] F) p (mu.restrict (U : Set E)) := hDAp.toLp DA
  have hfA : (fA : E → F) =ᵐ[mu.restrict (U : Set E)] A := hAp.coeFn_toLp
  have hfD : (fD : E → E →L[ℝ] F) =ᵐ[mu.restrict (U : Set E)] DA := hDAp.coeFn_toLp
  have hball : ∀ᶠ n in atTop, ∀ x ∈ K, Metric.closedBall x (φ n).rOut ⊆ U := by
    filter_upwards [(tendsto_order.1 hφ).2 δ hδ] with n hn x hx
    exact (Metric.closedBall_subset_closedBall hn.le).trans
      ((Metric.closedBall_subset_cthickening hx δ).trans hKδ)
  refine ⟨fun n => smoothField (φ n) fA, fun n => contDiff_smoothField _ _, ?_, ?_⟩
  · -- uniform convergence on `K`, from the uniform continuity of `A` near `K`
    have hAu : UniformContinuousOn A (closure W) :=
      hWc.uniformContinuousOn_of_continuous (hAc.mono hWΩ)
    refine Metric.tendstoUniformlyOn_iff.2 fun ε hε => ?_
    obtain ⟨δ', hδ', hu⟩ := Metric.uniformContinuousOn_iff_le.1 hAu (ε / 2) (half_pos hε)
    filter_upwards [hball, (tendsto_order.1 hφ).2 δ' hδ'] with n hn hn' x hx
    rw [dist_comm]
    refine (dist_smoothField_le (φ n) hfA
      (Metric.ball_subset_closedBall.trans (hn x hx)) fun y hy => ?_).trans_lt (half_lt_self hε)
    have hyx : dist y x ≤ δ' := (Metric.mem_ball.1 hy).le.trans hn'.le
    exact hu y (subset_closure (Metric.ball_subset_closedBall.trans (hn x hx) hy)) x
      (subset_closure (hKW hx)) hyx
  · -- convergence of the derivatives in `Lᵖ(K)`, from the `Lᵖ` approximate identity
    have hA' : HasWeakFDerivOn mu U (fA : E → F) (fD : E → E →L[ℝ] F) :=
      ((hA.mono hUΩ).congr_ae hfA.symm).congr_ae_deriv hfD.symm
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      (tendsto_eLpNorm_smoothField_sub hp hφ fD) (Eventually.of_forall fun _ => by simp) ?_
    filter_upwards [hball] with n hn
    have hae : fderiv ℝ (smoothField (φ n) fA) - DA =ᵐ[mu.restrict K]
        smoothField (φ n) fD - (fD : E → E →L[ℝ] F) := by
      filter_upwards [ae_restrict_of_ae_restrict_of_subset hKW hfD,
        ae_restrict_mem hK.measurableSet] with x hx hxK
      simp only [Pi.sub_apply, hx]
      congr 1
      simpa only [smoothField_def, convolution_flip] using
        hA'.fderiv_indicator_convolution_normed (Lp.memLp fA) (Lp.memLp fD) Fact.out Fact.out
          (φ n) x (hn x hxK)
    rw [eLpNorm_congr_ae hae]
    exact eLpNorm_mono_measure _ (Measure.restrict_mono hKW le_rfl)

/-- **Smooth approximation of a `W^{2,p}` function on a compact set.** Let `u ∈ W^{2,p}(Ω)`,
`p < ∞`, have a representative `ū` continuous on `Ω`, and let `K ⊆ Ω` be compact. For every
`η > 0` there is a smooth function `v` on the whole space with `|v - ū| ≤ η` on `K` whose Hessian
`D²v` is within `η` of the weak Hessian of `u` in `Lᵖ(K)`. -/
theorem exists_contDiff_abs_sub_le_and_eLpNorm_fderiv_gradient_sub_le (hp : p ≠ ∞)
    (u : Wkp mu Omega p 2) {ū : E → ℝ} (hcont : ContinuousOn ū Omega)
    (hū : (value 2 u : E → ℝ) =ᵐ[mu.restrict Omega] ū) {K : Set E} (hK : IsCompact K)
    (hKΩ : K ⊆ Omega) {η : ℝ} (hη : 0 < η) :
    ∃ v : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) v ∧ (∀ y ∈ K, |v y - ū y| ≤ η) ∧
      eLpNorm (fun y => fderiv ℝ (∇ v) y - iteratedGradient 1 u y) p (mu.restrict K) ≤
        ENNReal.ofReal η := by
  obtain ⟨δ, hδ, hδΩ⟩ := hK.exists_cthickening_subset_open Omega.isOpen hKΩ
  obtain ⟨ρ, hρ, hucont⟩ := Metric.uniformContinuousOn_iff.1
    ((hK.cthickening (r := δ)).uniformContinuousOn_of_continuous (hcont.mono hδΩ)) η hη
  -- Mollifiers of radius `min δ ρ / (j + 2) < min δ ρ`.
  set r : ℕ → ℝ := fun j => min δ ρ / ((j : ℝ) + 2)
  have hr (j : ℕ) : 0 < r j := by have := lt_min hδ hρ; positivity
  have hrlt (j : ℕ) : r j < min δ ρ :=
    div_lt_self (lt_min hδ hρ) (by linarith [Nat.cast_nonneg (α := ℝ) j])
  let phi : ℕ → ContDiffBump (0 : E) := fun j => ⟨r j / 2, r j, half_pos (hr j),
    half_lt_self (hr j)⟩
  have hphi : Tendsto (fun j => (phi j).rOut) atTop (𝓝 0) :=
    (tendsto_const_nhds (x := min δ ρ)).div_atTop
      (tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop)
  -- Near each point of `K`, the bump balls stay in `Ω`.
  have hball (j : ℕ) {y : E} (hy : y ∈ K) {z : E} (hz : z ∈ Metric.ball y (δ - r j)) :
      Metric.closedBall z (phi j).rOut ⊆ Omega := by
    refine Subset.trans ?_ ((Metric.closedBall_subset_cthickening hy δ).trans hδΩ)
    refine Metric.closedBall_subset_closedBall' ?_
    have hzy := Metric.mem_ball.1 hz
    have hrj : (phi j).rOut = r j := rfl
    rw [hrj]
    linarith
  have hrδ (j : ℕ) : 0 < δ - r j := sub_pos.2 ((hrlt j).trans_le (min_le_left _ _))
  obtain ⟨j, hj⟩ := ((tendsto_eLpNorm_smoothField_sub hp hphi (iteratedGradient 1 u)).eventually
    (ge_mem_nhds (ENNReal.ofReal_pos.2 hη))).exists
  refine ⟨smoothField (phi j) (value 2 u), contDiff_smoothField _ _, fun y hy => ?_, ?_⟩
  · -- The mollification at `y` averages `ū` over a ball of radius less than `ρ`.
    rw [← Real.dist_eq]
    refine dist_smoothField_le (phi j) hū
      (Metric.ball_subset_closedBall.trans (hball j hy (Metric.mem_ball_self (hrδ j))))
      fun z hz => (hucont z ?_ y (Metric.self_subset_cthickening K hy) ?_).le
    · exact Metric.mem_cthickening_of_dist_le z y δ K hy
        ((Metric.mem_ball.1 hz).le.trans ((hrlt j).le.trans (min_le_left _ _)))
    · exact (Metric.mem_ball.1 hz).trans ((hrlt j).trans_le (min_le_right _ _))
  · -- On `K` the Hessian of the mollification is the mollified weak Hessian.
    refine le_trans (le_of_eq (eLpNorm_congr_ae ?_))
      ((eLpNorm_mono_measure _ (Measure.restrict_mono hKΩ le_rfl)).trans hj)
    filter_upwards [ae_restrict_mem hK.measurableSet] with y hy
    rw [Pi.sub_apply, fderiv_gradient_smoothField_value u (phi j)
      (Filter.eventually_of_mem (Metric.ball_mem_nhds y (hrδ j)) fun z hz => hball j hy hz)]

end TauCeti.Wkp
