/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.PowerSeries.Coefficient
public import TauCeti.MeasureTheory.Integral.Torus.ContinuousMap
public import Mathlib.Analysis.Analytic.Basic
import TauCeti.Analysis.Analytic.ContinuousMap

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
orthogonality, uniform convergence of native partial sums on a compact family of points, and
`TauCeti.torusIntegralCLM`.

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

omit [CompleteSpace F] in
/-- Translating the center of a torus integral of a homogeneous term turns the Cauchy weight
into `(z i)⁻¹ ^ (m i + 1)` on the torus centered at the origin. -/
private theorem torusIntegral_cauchyCoeff_translate (p : FormalMultilinearSeries ℂ (Fin n → ℂ) F)
    (m : Fin n → ℕ) (k : ℕ) :
    ((2 * π * I : ℂ) ^ n)⁻¹ •
        (∯ z in T(c, R), (∏ i, (z i - c i) ^ (m i + 1))⁻¹ • p k (fun _ ↦ z - c)) =
      ((2 * π * I : ℂ) ^ n)⁻¹ •
        (∯ z in T(0, R), (∏ i, (z i)⁻¹ ^ (m i + 1)) • p k (fun _ ↦ z)) := by
  -- Translation preserves the parametrized torus differential as well as the integrand.
  simp only [torusIntegral, ← Pi.sub_apply, torusMap_sub_center,
    Finset.prod_inv_distrib, inv_pow]

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
  have hzero (k : ℕ) (hk : k ≠ ∑ i, m i) : A k = 0 := by
    exact (torusIntegral_cauchyCoeff_translate p m k).trans
      ((p k).torusIntegral_cauchyCoeff_eq_zero m hR (by simpa using hk.symm))
  -- Restrict the uniformly convergent partial sums to the compact boundary.
  let K := (i : Fin n) → sphere (c i) |R i|
  let v : K → Fin n → ℂ := fun z i ↦ z i
  have hv : Continuous v := by fun_prop
  have hbound (z : K) : ‖v z - c‖ ≤ s := by
    refine (pi_norm_le_iff_of_nonneg s.2).2 fun i ↦ ?_
    exact (mem_sphere_iff_norm.1 (z i).2).le.trans (by rw [abs_of_pos (hR i)]; exact hRs i)
  have hmem (z : K) : v z ∈ eball c r := by
    rw [mem_eball, edist_eq_enorm_sub]
    exact lt_of_le_of_lt (by exact_mod_cast hbound z) hs
  let G : C(K, F) := ⟨fun z ↦ f (v z), hf.continuousOn.comp_continuous hv hmem⟩
  let P : ℕ → C(K, F) := fun k ↦ ⟨fun z ↦ p k (fun _ ↦ v z - c), by fun_prop⟩
  have hconv : Tendsto (fun N ↦ ∑ k ∈ Finset.range N, P k) atTop (𝓝 G) :=
    (hf.hasSum_compact ⟨v, hv⟩ hs hbound).tendsto_sum_nat
  -- The Cauchy weight is continuous on the boundary, since every radius is positive.
  let W : C(K, ℂ) := ⟨_, TauCeti.continuous_inv_prod_sub_pow (c := c) hR m⟩
  have hW : Continuous (fun u : C(K, F) ↦ W • u) := by
    exact ContinuousMap.continuous_of_continuous_uncurry _
      ((W.continuous.comp continuous_snd).smul continuous_eval)
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
    simp only [map_sum, Finset.smul_sum, hterm]
    exact Finset.sum_eq_single (∑ i, m i) (fun k _ hk ↦ hzero k hk)
      (fun hn ↦ (hn (Finset.mem_range.mpr hN)).elim)
  have hvalue := tendsto_nhds_unique hlimit
    (tendsto_const_nhds.congr' (hstable.mono fun _ h ↦ h.symm))
  rw [TauCeti.torusIntegralCLM_eq_torusIntegral c R _
    (fun z ↦ (∏ i, (z i - c i) ^ (m i + 1))⁻¹ • f z) (fun _ ↦ rfl)] at hvalue
  exact hvalue.trans ((torusIntegral_cauchyCoeff_translate p m _).trans
    ((p (∑ i, m i)).torusIntegral_cauchyCoeff m hR))
