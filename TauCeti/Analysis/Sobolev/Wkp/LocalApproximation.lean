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

/-- The smooth convolution representative of a zero-extended derivative field. -/
private def smoothField {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (phi : ContDiffBump (0 : E)) (f : Lp F p (mu.restrict Omega)) : E → F :=
  phi.normed mu ⋆[ContinuousLinearMap.lsmul ℝ ℝ, mu] (Omega : Set E).indicator (f : E → F)

private theorem contDiff_smoothField {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (phi : ContDiffBump (0 : E)) (f : Lp F p (mu.restrict Omega)) :
    ContDiff ℝ (⊤ : ℕ∞) (smoothField phi f) := by
  have hmem := (memLp_indicator_iff_restrict Omega.isOpen.measurableSet.nullMeasurableSet).2
    (Lp.memLp f)
  exact phi.hasCompactSupport_normed.contDiff_convolution_left
    (ContinuousLinearMap.lsmul ℝ ℝ) phi.contDiff_normed (hmem.locallyIntegrable Fact.out)

private theorem fderiv_smoothField (k : ℕ) (u : Wkp mu Omega p (k + 2))
    (phi : ContDiffBump (0 : E)) (x : E)
    (hx : Metric.closedBall x phi.rOut ⊆ Omega) :
    fderiv ℝ (smoothField phi (iteratedGradient k (lowerOrder (k + 1) u))) x =
      smoothField phi (iteratedGradient (k + 1) u) x := by
  simpa only [smoothField, convolution_flip] using
    fderiv_indicator_convolution_normed_iteratedGradient k u phi x hx

private theorem gradient_smoothField (u : Wkp mu Omega p 1)
    (phi : ContDiffBump (0 : E)) (x : E)
    (hx : Metric.closedBall x phi.rOut ⊆ Omega) :
    gradient (smoothField phi (value 1 u)) x =
      smoothField phi (iteratedGradient 0 u) x := by
  apply (InnerProductSpace.toDual ℝ E).injective
  rw [toDual_gradient]
  have hd := fderiv_indicator_convolution_normed_value u phi x hx
  rw [convolution_flip, convolution_flip] at hd
  rw [smoothField, hd]
  have hmem := (memLp_indicator_iff_restrict Omega.isOpen.measurableSet.nullMeasurableSet).2
    (Lp.memLp (iteratedGradient 0 u))
  have hi := (phi.hasCompactSupport_normed (μ := mu)).convolutionExists_left
    (ContinuousLinearMap.lsmul ℝ ℝ) phi.continuous_normed (hmem.locallyIntegrable Fact.out) x
  -- Passing the Riesz map through the integral identifies the vector convolution's dual.
  symm
  rw [smoothField, convolution_def]
  refine ((InnerProductSpace.toDual ℝ E).toLinearIsometry.toContinuousLinearMap
    |>.integral_comp_comm hi).symm.trans ?_
  apply integral_congr_ae
  filter_upwards with y
  by_cases hy : x - y ∈ Omega <;> simp [hy, ContinuousLinearMap.lsmul_apply]

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
    simpa only [Measure.restrict_univ, smoothField] using he')

private theorem value_restrict_localTest (hp : p ≠ ∞) (hU : U ≤ Omega)
    (chi : 𝓓(Omega, ℝ)) (hchi : ∀ x ∈ U, chi x = 1)
    (phi : ContDiffBump (0 : E)) (k : ℕ) (u : Wkp mu Omega p k) :
    value k (restrictL hU k (ofTestFunctionₗ (mu := mu) (p := p) k (localTest chi phi k u))) =
      localAverage hp phi (value k u) := by
  apply Lp.ext
  filter_upwards [value_restrictL_ae hU k
      (ofTestFunctionₗ (mu := mu) (p := p) k (localTest chi phi k u)),
    testFunctionLp_apply_ae (mu := mu) p (localTest chi phi k u) |>.filter_mono
      (ae_mono (Measure.restrict_mono_set mu (SetLike.coe_subset_coe.mpr hU))),
    localAverage_ae (U := U) hp phi (value k u), ae_restrict_mem U.isOpen.measurableSet]
    with x hr ht ha hx
  rw [hr, value_ofTestFunctionₗ, ht, ha]
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
  intro k
  -- Orders zero and one use convergence of the value and gradient in `Lᵖ`; successive
  -- orders use the two components of the closed weak-derivative graph.
  induction k using Nat.twoStepInduction with
  | zero =>
      intro u
      have h : Tendsto (fun i => localAverage hp (phi i) (value 0 u)) l
          (𝓝 (value 0 (restrictL hU 0 u))) :=
        Wkp.tendsto_mollified_value hp hU hphi 0 u
      simp only [value_zero] at h
      convert h using 1
      funext i
      simpa only [value_zero] using value_restrict_localTest hp hU chi hchi (phi i) 0 u
  | one =>
      intro u
      refine W1p.tendsto_iff_value_gradient.2 ⟨?_, ?_⟩
      · have h : Tendsto (fun i => localAverage hp (phi i) (value 1 u)) l
            (𝓝 (value 1 (restrictL hU 1 u))) :=
          Wkp.tendsto_mollified_value hp hU hphi 1 u
        simp only [value_one] at h
        convert h using 1
        funext i
        simpa only [value_one] using value_restrict_localTest hp hU chi hchi (phi i) 1 u
      · have h : Tendsto (fun i => localAverage hp (phi i) (iteratedGradient 0 u)) l
            (𝓝 (iteratedGradient 0 (restrictL hU 1 u))) :=
          Wkp.tendsto_mollified_iteratedGradient hp hU hphi 0 u
        simp only [iteratedGradient_zero] at h
        convert h using 1
        funext i
        simpa only [iteratedGradient_zero] using
          iteratedGradient_restrict_localTest hp hU chi hchi (phi i) (hinterior i) 0 u
  | more k _ ih =>
      intro u
      rw [tendsto_iff_lowerOrder_iteratedGradient (k + 1)]
      constructor
      · have h := ih (lowerOrder (k + 1) u)
        simp_rw [localTest_lowerOrder] at h
        convert h using 1
        · funext i
          rw [lowerOrder_restrictL, lowerOrder_ofTestFunctionₗ]
        · rw [lowerOrder_restrictL]
      · have h : Tendsto (fun i => localAverage hp (phi i) (iteratedGradient (k + 1) u)) l
            (𝓝 (iteratedGradient (k + 1) (restrictL hU (k + 2) u))) :=
          Wkp.tendsto_mollified_iteratedGradient hp hU hphi (k + 1) u
        simpa only [← iteratedGradient_restrict_localTest hp hU chi hchi _
          (hinterior _) (k + 1) u] using h

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
    hcompact.exists_contDiff_cutoff Omega.isOpen hclosure
  let chiTest : 𝓓(Omega, ℝ) := ⟨chi, hchi, hchi_cpt, hchi_ts⟩
  have hchiU : ∀ x ∈ U, chiTest x = 1 := by
    intro x hx
    simpa only [chiTest, TestFunction.coe_mk, mem_preimage, mem_singleton_iff] using
      (interior_subset (hchi_one (subset_closure hx)))
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

end TauCeti.Wkp
