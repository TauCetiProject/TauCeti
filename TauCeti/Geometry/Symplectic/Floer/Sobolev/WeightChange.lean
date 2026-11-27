/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fredholm.ContinuousFamily
public import TauCeti.Geometry.Symplectic.Floer.Sobolev.Parametrix
import Mathlib.Analysis.Convex.Basic
import TauCeti.Analysis.Normed.Group.Basic

/-!
# The index of the weighted linearized Floer operator under changes of weight

Let `F` be a finite-dimensional complex inner product space with symplectic form
`ω = Im ⟪·, ·⟫`, and let `D_u - c(s) : W^{1,2}(ℝ × S¹, F) → L²(ℝ × S¹, F)` be the linearized
Floer operator along `u` conjugated by an exponential weight `e^{κ(s)}` of slope `c = κ'`
(`TauCeti.SymplecticForm.floerWeightedSobolevOperator`), for Floer data `(i, K_s, K_t)` that are
cylindrical near the ends and a continuous slope equal to constants `δ±` near `±∞`. It is Fredholm
as soon as the shifted fields `dX_{H±_t}(x±(t)) - δ± i` at the asymptotic loops have nondegenerate
return maps, that is, as soon as `δ±` avoid the spectra of the asymptotic operators at the ends
(`TauCeti.SymplecticForm.isFredholm_floerWeightedSobolevOperator_of_cylindrical`).

This file shows that the index of the weighted operator does not change as long as the end
weights do not cross the spectra of the asymptotic operators. The operator depends
Lipschitz-continuously on the slope in operator norm
(`TauCeti.SymplecticForm.norm_floerWeightedSobolevOperator_sub_le`), so along the straight line
between two slopes it is a continuous family of Fredholm operators whenever the end weights stay
off the spectra, and the index is locally constant on such families
(`ContinuousOn.index_eq_of_isPreconnected`). Consequently the index depends only on the end
weights and not on the profile of the slope, it agrees with the index of the unweighted operator
`D_u` when no eigenvalue lies between `0` and `δ±`, and in particular it agrees with the index of
`D_u` for all weights small enough, when the ends are nondegenerate orbits. Small weights are the
ones used on the punctured domains of Floer theory, where they give the same index as the
unweighted operator; how the index jumps when a weight crosses an eigenvalue is not treated here.

## Main results

* `TauCeti.SymplecticForm.index_floerWeightedSobolevOperator_eq_of_forall_mem_uIcc`: for two
  slopes whose end weights are joined by segments free of spectrum at both ends, the two weighted
  operators have the same index.
* `TauCeti.SymplecticForm.index_floerWeightedSobolevOperator_eq_of_cylindrical`: the index depends
  only on the end weights.
* `TauCeti.SymplecticForm.index_floerWeightedSobolevOperator_eq_index_floerSobolevOperator`: if
  no eigenvalue lies between `0` and `δ±`, the weighted operator has the index of `D_u`.
* `TauCeti.SymplecticForm.exists_pos_forall_index_floerWeightedSobolevOperator_eq`: between
  nondegenerate orbits, every weight small enough gives the index of `D_u`.

## References

* R. B. Lockhart and R. C. McOwen, *Elliptic differential operators on noncompact manifolds*,
  Ann. Scuola Norm. Sup. Pisa Cl. Sci. (4) 12 (1985), 409–447, on the constancy of the index on
  exponentially weighted spaces as long as the weights avoid the spectra of the asymptotic
  operators.
-/

public section

noncomputable section

open Filter Set Function MeasureTheory Topology
open scoped NNReal Manifold

namespace TauCeti.SymplecticForm

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]

/-- **The index of the weighted linearized Floer operator does not change while the weights
avoid the spectra.** Let `F` be a finite-dimensional complex inner product space whose symplectic
form `ω` is `Im ⟪·, ·⟫`, and let the Floer data `(i, K_s, K_t)` and the asymptotic loops `x±` be as
in `TauCeti.SymplecticForm.isFredholm_floerWeightedSobolevOperator_of_cylindrical`. Let `c₀` and
`c₁` be continuous slopes, with `cⱼ = δ±ⱼ` beyond `±R`. If for every weight `δ` between `δ-₀` and
`δ-₁` the shifted field `dX_{H₋_t}(x₋(t)) - δ i` has a nondegenerate return map, and likewise at
`x₊` for every weight between `δ+₀` and `δ+₁`, then the realizations `D_u - c₀(s)` and
`D_u - c₁(s)` on `W^{1,2}(ℝ × S¹, F)` have the same index. -/
theorem index_floerWeightedSobolevOperator_eq_of_forall_mem_uIcc (ω : SymplecticForm F)
    (hω : ∀ v w, ω v w = (inner ℂ v w).im) {Ks Kt : ℝ × ℝ → F → ℝ} {Hm Hp : ℝ → F → ℝ} {R : ℝ}
    {u : ℝ × ℝ → F}
    (hcyl : Floer.IsCylindricalNearEnds (fun _ _ ↦ AlmostComplexStructure.ofComplexModule F) Ks
      Kt (fun _ _ ↦ AlmostComplexStructure.ofComplexModule F)
      (fun _ _ ↦ AlmostComplexStructure.ofComplexModule F) Hm Hp R u)
    (hu : Continuous u) {c₀ c₁ : ℝ → ℝ} (hc₀ : Continuous c₀) (hc₁ : Continuous c₁)
    {δm₀ δp₀ δm₁ δp₁ : ℝ} (hcm₀ : ∀ s ≤ -R, c₀ s = δm₀) (hcp₀ : ∀ s, R ≤ s → c₀ s = δp₀)
    (hcm₁ : ∀ s ≤ -R, c₁ s = δm₁) (hcp₁ : ∀ s, R ≤ s → c₁ s = δp₁)
    (hHm : ContDiff ℝ 3 (uncurry Hm)) (hHmper : Periodic Hm 1) {xm : ℝ → F}
    (hxm : ContDiff ℝ 1 xm) (hxmper : Periodic xm 1)
    (hdetm : ∀ δ ∈ uIcc δm₀ δm₁, LinearMap.det ((1 - dysonSeriesLeft (fun t ↦
      fderiv ℝ (ω.hamiltonianVectorField (Hm t)) (xm t) -
        δ • (AlmostComplexStructure.ofComplexModule F).toLinearMap.toContinuousLinearMap) 1 :
          F →L[ℝ] F) : F →ₗ[ℝ] F) ≠ 0)
    (huxm : TendstoUniformlyOn (fun s t ↦ u (s, t)) xm atBot (Icc 0 1))
    (hHp : ContDiff ℝ 3 (uncurry Hp)) (hHpper : Periodic Hp 1) {xp : ℝ → F}
    (hxp : ContDiff ℝ 1 xp) (hxpper : Periodic xp 1)
    (hdetp : ∀ δ ∈ uIcc δp₀ δp₁, LinearMap.det ((1 - dysonSeriesLeft (fun t ↦
      fderiv ℝ (ω.hamiltonianVectorField (Hp t)) (xp t) -
        δ • (AlmostComplexStructure.ofComplexModule F).toLinearMap.toContinuousLinearMap) 1 :
          F →L[ℝ] F) : F →ₗ[ℝ] F) ≠ 0)
    (huxp : TendstoUniformlyOn (fun s t ↦ u (s, t)) xp atTop (Icc 0 1)) :
    (ω.floerWeightedSobolevOperator
      (fun _ _ ↦ (AlmostComplexStructure.ofComplexModule F).toLinearMap.toContinuousLinearMap)
        Ks Kt u c₀).index =
      (ω.floerWeightedSobolevOperator
        (fun _ _ ↦ (AlmostComplexStructure.ofComplexModule F).toLinearMap.toContinuousLinearMap)
          Ks Kt u c₁).index := by
  set J₀ : ℝ × ℝ → F → F →L[ℝ] F :=
    fun _ _ ↦ (AlmostComplexStructure.ofComplexModule F).toLinearMap.toContinuousLinearMap
  -- The slopes `c r = c₀ + r (c₁ - c₀)` join `c₀` to `c₁`; for `r ∈ [0, 1]` their end weights lie
  -- on the segments between `δ±₀` and `δ±₁`, so the operators are Fredholm.
  set c : ℝ → ℝ → ℝ := fun r s ↦ c₀ s + r * (c₁ s - c₀ s)
  have hc (r : ℝ) : Continuous (c r) := hc₀.add (continuous_const.mul (hc₁.sub hc₀))
  have hcm (r : ℝ) : ∀ s ≤ -R, c r s = δm₀ + r • (δm₁ - δm₀) := fun s hs ↦ by
    simp only [c, smul_eq_mul, hcm₀ s hs, hcm₁ s hs]
  have hcp (r : ℝ) : ∀ s, R ≤ s → c r s = δp₀ + r • (δp₁ - δp₀) := fun s hs ↦ by
    simp only [c, smul_eq_mul, hcp₀ s hs, hcp₁ s hs]
  have hFred (r : ℝ) (hr : r ∈ Icc (0 : ℝ) 1) :
      (ω.floerWeightedSobolevOperator J₀ Ks Kt u (c r)).IsFredholm :=
    ω.isFredholm_floerWeightedSobolevOperator_of_cylindrical hω hcyl hu (hc r) (hcm r) (hcp r)
      hHm hHmper hxm hxmper
      (hdetm _ ((convex_uIcc δm₀ δm₁).add_smul_sub_mem left_mem_uIcc right_mem_uIcc hr)) huxm
      hHp hHpper hxp hxpper
      (hdetp _ ((convex_uIcc δp₀ δp₁).add_smul_sub_mem left_mem_uIcc right_mem_uIcc hr)) huxp
  -- Since `c₁ - c₀` is bounded, the family depends Lipschitz-continuously on `r`.
  obtain ⟨B, hB⟩ := exists_forall_norm_le_of_eventually_eq (hc₁.sub hc₀)
    (Aminus := δm₁ - δm₀) (Aplus := δp₁ - δp₀)
    (eventually_atBot.2 ⟨-R, fun s hs ↦ by simp only [Pi.sub_apply, hcm₀ s hs, hcm₁ s hs]⟩)
    (eventually_atTop.2 ⟨R, fun s hs ↦ by simp only [Pi.sub_apply, hcp₀ s hs, hcp₁ s hs]⟩)
  have hcont : Continuous fun r ↦ ω.floerWeightedSobolevOperator J₀ Ks Kt u (c r) := by
    have hL : LipschitzWith (Real.toNNReal B)
        fun r ↦ ω.floerWeightedSobolevOperator J₀ Ks Kt u (c r) := by
      refine LipschitzWith.of_dist_le' fun r r' ↦ ?_
      rw [dist_eq_norm, Real.dist_eq, mul_comm]
      refine ω.norm_floerWeightedSobolevOperator_sub_le J₀ Ks Kt u (hc r).measurable
        (hc r').measurable fun s ↦ ?_
      calc |c r s - c r' s| = |r - r'| * |c₁ s - c₀ s| := by
            rw [← abs_mul]
            congr 1
            ring
        _ ≤ |r - r'| * B := mul_le_mul_of_nonneg_left (hB s) (abs_nonneg _)
    exact hL.continuous
  have h := hcont.continuousOn.index_eq_of_isPreconnected hFred isPreconnected_Icc
    (left_mem_Icc.2 zero_le_one) (right_mem_Icc.2 zero_le_one)
  have h₀ : c 0 = c₀ := funext fun s ↦ by simp only [c, zero_mul, add_zero]
  have h₁ : c 1 = c₁ := funext fun s ↦ by simp only [c, one_mul, add_sub_cancel]
  rwa [h₀, h₁] at h

/-- **The index of the weighted linearized Floer operator depends only on the end weights.**
Under the hypotheses of
`TauCeti.SymplecticForm.isFredholm_floerWeightedSobolevOperator_of_cylindrical`, two continuous
slopes `c₀` and `c₁` that both equal `δ₋` for `s ≤ -R` and `δ₊` for `s ≥ R` give weighted
operators `D_u - c₀(s)` and `D_u - c₁(s)` with the same index. -/
theorem index_floerWeightedSobolevOperator_eq_of_cylindrical (ω : SymplecticForm F)
    (hω : ∀ v w, ω v w = (inner ℂ v w).im) {Ks Kt : ℝ × ℝ → F → ℝ} {Hm Hp : ℝ → F → ℝ} {R : ℝ}
    {u : ℝ × ℝ → F}
    (hcyl : Floer.IsCylindricalNearEnds (fun _ _ ↦ AlmostComplexStructure.ofComplexModule F) Ks
      Kt (fun _ _ ↦ AlmostComplexStructure.ofComplexModule F)
      (fun _ _ ↦ AlmostComplexStructure.ofComplexModule F) Hm Hp R u)
    (hu : Continuous u) {c₀ c₁ : ℝ → ℝ} (hc₀ : Continuous c₀) (hc₁ : Continuous c₁)
    {δm δp : ℝ} (hcm₀ : ∀ s ≤ -R, c₀ s = δm) (hcp₀ : ∀ s, R ≤ s → c₀ s = δp)
    (hcm₁ : ∀ s ≤ -R, c₁ s = δm) (hcp₁ : ∀ s, R ≤ s → c₁ s = δp)
    (hHm : ContDiff ℝ 3 (uncurry Hm)) (hHmper : Periodic Hm 1) {xm : ℝ → F}
    (hxm : ContDiff ℝ 1 xm) (hxmper : Periodic xm 1)
    (hdetm : LinearMap.det ((1 - dysonSeriesLeft (fun t ↦
      fderiv ℝ (ω.hamiltonianVectorField (Hm t)) (xm t) -
        δm • (AlmostComplexStructure.ofComplexModule F).toLinearMap.toContinuousLinearMap) 1 :
          F →L[ℝ] F) : F →ₗ[ℝ] F) ≠ 0)
    (huxm : TendstoUniformlyOn (fun s t ↦ u (s, t)) xm atBot (Icc 0 1))
    (hHp : ContDiff ℝ 3 (uncurry Hp)) (hHpper : Periodic Hp 1) {xp : ℝ → F}
    (hxp : ContDiff ℝ 1 xp) (hxpper : Periodic xp 1)
    (hdetp : LinearMap.det ((1 - dysonSeriesLeft (fun t ↦
      fderiv ℝ (ω.hamiltonianVectorField (Hp t)) (xp t) -
        δp • (AlmostComplexStructure.ofComplexModule F).toLinearMap.toContinuousLinearMap) 1 :
          F →L[ℝ] F) : F →ₗ[ℝ] F) ≠ 0)
    (huxp : TendstoUniformlyOn (fun s t ↦ u (s, t)) xp atTop (Icc 0 1)) :
    (ω.floerWeightedSobolevOperator
      (fun _ _ ↦ (AlmostComplexStructure.ofComplexModule F).toLinearMap.toContinuousLinearMap)
        Ks Kt u c₀).index =
      (ω.floerWeightedSobolevOperator
        (fun _ _ ↦ (AlmostComplexStructure.ofComplexModule F).toLinearMap.toContinuousLinearMap)
          Ks Kt u c₁).index :=
  ω.index_floerWeightedSobolevOperator_eq_of_forall_mem_uIcc hω hcyl hu hc₀ hc₁ hcm₀ hcp₀ hcm₁
    hcp₁ hHm hHmper hxm hxmper (fun δ hδ ↦ by
      rw [uIcc_self, mem_singleton_iff] at hδ
      rwa [hδ]) huxm hHp
    hHpper hxp hxpper (fun δ hδ ↦ by
      rw [uIcc_self, mem_singleton_iff] at hδ
      rwa [hδ]) huxp

/-- **The weighted linearized Floer operator has the index of `D_u` when no eigenvalue lies
between `0` and the weights.** Under the hypotheses of
`TauCeti.SymplecticForm.isFredholm_floerWeightedSobolevOperator_of_cylindrical`, if for every
weight `δ` between `0` and `δ₋` the shifted field `dX_{H₋_t}(x₋(t)) - δ i` has a nondegenerate
return map, and likewise at `x₊` for every weight between `0` and `δ₊`, then `D_u - c(s)` has the
same index as the realization `D_u` of the unweighted operator. -/
theorem index_floerWeightedSobolevOperator_eq_index_floerSobolevOperator (ω : SymplecticForm F)
    (hω : ∀ v w, ω v w = (inner ℂ v w).im) {Ks Kt : ℝ × ℝ → F → ℝ} {Hm Hp : ℝ → F → ℝ} {R : ℝ}
    {u : ℝ × ℝ → F}
    (hcyl : Floer.IsCylindricalNearEnds (fun _ _ ↦ AlmostComplexStructure.ofComplexModule F) Ks
      Kt (fun _ _ ↦ AlmostComplexStructure.ofComplexModule F)
      (fun _ _ ↦ AlmostComplexStructure.ofComplexModule F) Hm Hp R u)
    (hu : Continuous u) {c : ℝ → ℝ} (hc : Continuous c) {δm δp : ℝ} (hcm : ∀ s ≤ -R, c s = δm)
    (hcp : ∀ s, R ≤ s → c s = δp)
    (hHm : ContDiff ℝ 3 (uncurry Hm)) (hHmper : Periodic Hm 1) {xm : ℝ → F}
    (hxm : ContDiff ℝ 1 xm) (hxmper : Periodic xm 1)
    (hdetm : ∀ δ ∈ uIcc 0 δm, LinearMap.det ((1 - dysonSeriesLeft (fun t ↦
      fderiv ℝ (ω.hamiltonianVectorField (Hm t)) (xm t) -
        δ • (AlmostComplexStructure.ofComplexModule F).toLinearMap.toContinuousLinearMap) 1 :
          F →L[ℝ] F) : F →ₗ[ℝ] F) ≠ 0)
    (huxm : TendstoUniformlyOn (fun s t ↦ u (s, t)) xm atBot (Icc 0 1))
    (hHp : ContDiff ℝ 3 (uncurry Hp)) (hHpper : Periodic Hp 1) {xp : ℝ → F}
    (hxp : ContDiff ℝ 1 xp) (hxpper : Periodic xp 1)
    (hdetp : ∀ δ ∈ uIcc 0 δp, LinearMap.det ((1 - dysonSeriesLeft (fun t ↦
      fderiv ℝ (ω.hamiltonianVectorField (Hp t)) (xp t) -
        δ • (AlmostComplexStructure.ofComplexModule F).toLinearMap.toContinuousLinearMap) 1 :
          F →L[ℝ] F) : F →ₗ[ℝ] F) ≠ 0)
    (huxp : TendstoUniformlyOn (fun s t ↦ u (s, t)) xp atTop (Icc 0 1)) :
    (ω.floerWeightedSobolevOperator
      (fun _ _ ↦ (AlmostComplexStructure.ofComplexModule F).toLinearMap.toContinuousLinearMap)
        Ks Kt u c).index =
      (ω.floerSobolevOperator 2
        (fun _ _ ↦ (AlmostComplexStructure.ofComplexModule F).toLinearMap.toContinuousLinearMap)
          Ks Kt u).index := by
  rw [← floerWeightedSobolevOperator_zero]
  exact (ω.index_floerWeightedSobolevOperator_eq_of_forall_mem_uIcc hω hcyl hu continuous_const hc
    (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) hcm hcp hHm hHmper hxm hxmper hdetm huxm hHp hHpper hxp
    hxpper hdetp huxp).symm

/-- **Small weights do not change the index of the linearized Floer operator.** Let `F` be a
finite-dimensional complex inner product space whose symplectic form `ω` is `Im ⟪·, ·⟫`, let `H±`
be one-periodic, jointly `C³` time-dependent Hamiltonians with globally Lipschitz suspended vector
fields, and let `x±` be one-periodic orbits of `H±` with `x±(0)` a nondegenerate fixed point of the
time-one map. Then there is `ε > 0`, depending only on these ends, with the following property.
For Floer data `(i, K_s, K_t)` cylindrical near the ends with end Hamiltonians `H±`, every
continuous map `u` whose loops converge uniformly to `x₋` at `-∞` and to `x₊` at `+∞`, and every
continuous slope `c` equal to `δ₋` for `s ≤ -R` and to `δ₊` for `s ≥ R` with `|δ±| < ε`, the
weighted operator `D_u - c(s)` has the same index as `D_u`. -/
theorem exists_pos_forall_index_floerWeightedSobolevOperator_eq (ω : SymplecticForm F)
    (hω : ∀ v w, ω v w = (inner ℂ v w).im) {Hm Hp : ℝ → F → ℝ}
    {Km : ℝ≥0} (hXm : LipschitzWith Km (ω.timeDependentHamiltonianSuspension Hm))
    (hHm : ContDiff ℝ 3 (uncurry Hm)) (hHmper : Periodic Hm 1) {xm : ℝ → F}
    (hxm : ∀ t, HasDerivAt xm (ω.hamiltonianVectorField (Hm t) (xm t)) t) (hxmper : Periodic xm 1)
    (hndm : IsNondegenerateFixedPt 𝓘(ℝ, F) (ω.timeDependentHamiltonianFlow Hm hXm 0 1) (xm 0))
    {Kp : ℝ≥0} (hXp : LipschitzWith Kp (ω.timeDependentHamiltonianSuspension Hp))
    (hHp : ContDiff ℝ 3 (uncurry Hp)) (hHpper : Periodic Hp 1) {xp : ℝ → F}
    (hxp : ∀ t, HasDerivAt xp (ω.hamiltonianVectorField (Hp t) (xp t)) t) (hxpper : Periodic xp 1)
    (hndp : IsNondegenerateFixedPt 𝓘(ℝ, F) (ω.timeDependentHamiltonianFlow Hp hXp 0 1) (xp 0)) :
    ∃ ε > 0, ∀ {Ks Kt : ℝ × ℝ → F → ℝ} {R : ℝ} {u : ℝ × ℝ → F},
      Floer.IsCylindricalNearEnds (fun _ _ ↦ AlmostComplexStructure.ofComplexModule F) Ks Kt
        (fun _ _ ↦ AlmostComplexStructure.ofComplexModule F)
        (fun _ _ ↦ AlmostComplexStructure.ofComplexModule F) Hm Hp R u →
      Continuous u → TendstoUniformlyOn (fun s t ↦ u (s, t)) xm atBot (Icc 0 1) →
      TendstoUniformlyOn (fun s t ↦ u (s, t)) xp atTop (Icc 0 1) →
      ∀ {c : ℝ → ℝ}, Continuous c → ∀ {δm δp : ℝ}, (∀ s ≤ -R, c s = δm) →
        (∀ s, R ≤ s → c s = δp) → |δm| < ε → |δp| < ε →
      (ω.floerWeightedSobolevOperator
        (fun _ _ ↦ (AlmostComplexStructure.ofComplexModule F).toLinearMap.toContinuousLinearMap)
          Ks Kt u c).index =
        (ω.floerSobolevOperator 2
          (fun _ _ ↦ (AlmostComplexStructure.ofComplexModule F).toLinearMap.toContinuousLinearMap)
            Ks Kt u).index := by
  -- Near `0` the shifted fields at both ends keep nondegenerate return maps.
  obtain ⟨εm, hεm, hdetm⟩ := Metric.eventually_nhds_iff.1
    (ω.eventually_det_one_sub_dysonSeriesLeft_sub_smul_ne_zero_of_isNondegenerateFixedPt hXm
      (hHm.of_le (by norm_num)) hxm hndm
      (J := fun _ ↦ AlmostComplexStructure.ofComplexModule F) continuous_const)
  obtain ⟨εp, hεp, hdetp⟩ := Metric.eventually_nhds_iff.1
    (ω.eventually_det_one_sub_dysonSeriesLeft_sub_smul_ne_zero_of_isNondegenerateFixedPt hXp
      (hHp.of_le (by norm_num)) hxp hndp
      (J := fun _ ↦ AlmostComplexStructure.ofComplexModule F) continuous_const)
  refine ⟨min εm εp, lt_min hεm hεp, fun hcyl hu huxm huxp c hc δm δp hcm hcp hδm hδp ↦ ?_⟩
  -- Every weight between `0` and `δ±` is at most `|δ±| < ε` in absolute value.
  have hsmall {δ δ' ε' : ℝ} (hε' : min εm εp ≤ ε') (hδ : |δ| < min εm εp) (hδ' : δ' ∈ uIcc 0 δ) :
      dist δ' 0 < ε' := by
    rw [Real.dist_eq]
    exact ((abs_sub_left_of_mem_uIcc hδ').trans_lt (by rwa [sub_zero])).trans_le hε'
  exact ω.index_floerWeightedSobolevOperator_eq_index_floerSobolevOperator hω hcyl hu hc hcm hcp
    hHm hHmper (ω.contDiff_one_of_hasDerivAt_hamiltonianVectorField (hHm.of_le (by norm_num)) hxm)
    hxmper (fun δ hδ ↦ hdetm (hsmall (min_le_left _ _) hδm hδ)) huxm hHp hHpper
    (ω.contDiff_one_of_hasDerivAt_hamiltonianVectorField (hHp.of_le (by norm_num)) hxp)
    hxpper (fun δ hδ ↦ hdetp (hsmall (min_le_right _ _) hδp hδ)) huxp

end TauCeti.SymplecticForm
