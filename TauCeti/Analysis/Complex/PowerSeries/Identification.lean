/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.PowerSeries.Coefficient
public import TauCeti.MeasureTheory.Integral.Torus.ContinuousMap
public import Mathlib.Analysis.Analytic.Basic

/-!
# Identifying multivariate Cauchy coefficients of native series

The Cauchy coefficient with exponent vector `m` of a function represented by a native
multilinear series `p` is a finite sum of basis evaluations of `p (∑ i, m i)`. The sum runs over
assignments of coordinates to multilinear slots with the prescribed multiplicities. This
identifies contour coefficients with the native presentation even when its multilinear maps
are not symmetric.

The extraction formula allows any expansion center and unequal positive contour radii bounded
strictly inside the ball of representation. It includes the constant coefficient and dimension
zero.

The proof combines `ContinuousMultilinearMap.torusIntegral_cauchyCoeff`, homogeneous-degree
orthogonality, uniform convergence of native partial sums, and `TauCeti.torusIntegralCLM`.

## References

L. Hörmander, *An Introduction to Complex Analysis in Several Variables*, §2.2.
-/

public section

open Complex Filter MeasureTheory Metric Set Topology
open scoped Real ENNReal NNReal

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
  {n : ℕ} {f : (Fin n → ℂ) → F}
  {p : FormalMultilinearSeries ℂ (Fin n → ℂ) F}
  {c : Fin n → ℂ} {R : Fin n → ℝ} {r : ℝ≥0∞}

/-- A multivariate Cauchy coefficient of an analytic function is the finite sum of basis
values of the native multilinear term of the corresponding total degree. No symmetry of
that term is assumed. The contour radii are positive and bounded strictly inside the ball
on which the given series represents the function. -/
theorem HasFPowerSeriesOnBall.torusIntegral_cauchyCoeff
    (hf : HasFPowerSeriesOnBall f p c r) {s : ℝ≥0}
    (hs : (s : ℝ≥0∞) < r) (hR : ∀ i, 0 < R i) (hRs : ∀ i, R i ≤ s)
    (m : Fin n → ℕ) :
    ((2 * π * I : ℂ) ^ n)⁻¹ •
        (∯ z in T(c, R), (∏ i, (z i - c i) ^ (m i + 1))⁻¹ • f z) =
      ∑ a ∈ Finset.univ.filter (fun a : Fin (∑ i, m i) → Fin n ↦
        ∀ i, Fintype.card {j // a j = i} = m i),
        p (∑ i, m i) (fun j ↦ Pi.single (a j) 1) := by
  classical
  let A : ℕ → F := fun k ↦ ((2 * π * I : ℂ) ^ n)⁻¹ •
    (∯ z in T(c, R), (∏ i, (z i - c i) ^ (m i + 1))⁻¹ • p k (fun _ ↦ z - c))
  have htranslate (k : ℕ) : A k = ((2 * π * I : ℂ) ^ n)⁻¹ •
      (∯ z in T(0, R), (∏ i, (z i)⁻¹ ^ (m i + 1)) • p k (fun _ ↦ z)) := by
    -- Translation preserves the parametrized torus differential as well as the integrand.
    simp only [A, torusIntegral, ← Pi.sub_apply, torusMap_sub_center,
      Finset.prod_inv_distrib, inv_pow]
  have hzero (k : ℕ) (hk : k ≠ ∑ i, m i) : A k = 0 := by
    rw [htranslate]
    exact (p k).torusIntegral_cauchyCoeff_eq_zero m hR (by simpa using hk.symm)
  -- Restrict the uniformly convergent partial sums to the compact boundary.
  let K := (i : Fin n) → sphere (c i) |R i|
  let v : K → Fin n → ℂ := fun z i ↦ z i
  have hv : Continuous v := by fun_prop
  have hbound (z : K) : ‖v z - c‖ ≤ s := by
    apply (pi_norm_le_iff_of_nonneg s.2).2
    intro i
    exact (mem_sphere_iff_norm.1 (z i).2).le.trans (by rw [abs_of_pos (hR i)]; exact hRs i)
  have hmem (z : K) : v z ∈ eball c r := by
    rw [mem_eball, edist_eq_enorm_sub]
    exact lt_of_le_of_lt (by exact_mod_cast hbound z) hs
  let G : C(K, F) := ⟨fun z ↦ f (v z), hf.continuousOn.comp_continuous hv hmem⟩
  let P : ℕ → C(K, F) := fun k ↦ ⟨fun z ↦ p k (fun _ ↦ v z - c), by fun_prop⟩
  have hconv : Tendsto (fun N ↦ ∑ k ∈ Finset.range N, P k) atTop (𝓝 G) := by
    obtain ⟨t, hst, htr⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hs
    have hvt (z : K) : v z ∈ ball c t := by
      rw [mem_ball, dist_eq_norm]
      exact (hbound z).trans_lt (by exact_mod_cast hst)
    apply ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn.mpr
    intro S _
    have h := ((hf.tendstoUniformlyOn' htr).comp v).mono (s' := S) (fun z _ ↦ hvt z)
    simpa only [P, G, ContinuousMap.coe_sum, ContinuousMap.coe_mk, Finset.sum_apply,
      FormalMultilinearSeries.partialSum, Function.comp_def] using h
  -- The Cauchy weight is continuous on the boundary, since every radius is positive.
  let W : C(K, ℂ) := ⟨fun z ↦ (∏ i, (v z i - c i) ^ (m i + 1))⁻¹, by
    apply Continuous.inv₀ (by fun_prop)
    intro z
    apply Finset.prod_ne_zero_iff.mpr
    intro i _
    apply pow_ne_zero
    exact sub_ne_zero.mpr (ne_of_mem_sphere (z i).2 (abs_ne_zero.mpr (hR i).ne'))⟩
  have hW : Continuous (fun u : C(K, F) ↦ W • u) := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    exact (W.continuous.comp continuous_snd).smul continuous_eval
  have hL : Continuous (fun u : C(K, F) ↦
      ((2 * π * I : ℂ) ^ n)⁻¹ • TauCeti.torusIntegralCLM c R (W • u)) :=
    continuous_const.smul ((TauCeti.torusIntegralCLM c R).continuous.comp hW)
  have hlimit := (hL.tendsto G).comp hconv
  have hterm (k : ℕ) : ((2 * π * I : ℂ) ^ n)⁻¹ •
      TauCeti.torusIntegralCLM c R (W • P k) = A k := by
    rw [TauCeti.torusIntegralCLM_eq_torusIntegral c R _
      (fun z ↦ (∏ i, (z i - c i) ^ (m i + 1))⁻¹ • p k (fun _ ↦ z - c))
      (fun _ ↦ rfl)]
  have hstable : ∀ᶠ N in atTop,
      ((2 * π * I : ℂ) ^ n)⁻¹ •
        TauCeti.torusIntegralCLM c R (W • ∑ k ∈ Finset.range N, P k) = A (∑ i, m i) := by
    filter_upwards [eventually_gt_atTop (∑ i, m i)] with N hN
    rw [Finset.smul_sum, map_sum, Finset.smul_sum]
    simp_rw [hterm]
    exact Finset.sum_eq_single (∑ i, m i) (fun k _ hk ↦ hzero k hk)
      (fun hn ↦ (hn (Finset.mem_range.mpr hN)).elim)
  have hvalue := tendsto_nhds_unique hlimit
    (tendsto_const_nhds.congr' (hstable.mono fun _ h ↦ h.symm))
  rw [TauCeti.torusIntegralCLM_eq_torusIntegral c R _
    (fun z ↦ (∏ i, (z i - c i) ^ (m i + 1))⁻¹ • f z) (fun _ ↦ rfl)] at hvalue
  rw [hvalue, htranslate]
  exact (p (∑ i, m i)).torusIntegral_cauchyCoeff m hR
