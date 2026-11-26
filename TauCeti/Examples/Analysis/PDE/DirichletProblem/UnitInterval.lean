/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.IntervalDomain
public import TauCeti.Analysis.Sobolev.W1p.Interval.Trace
import TauCeti.Analysis.PDE.DirichletProblem
import TauCeti.Analysis.Sobolev.W1p.Interval.AbsolutelyContinuous

/-!
# The Dirichlet problem for `-u'' = 1` on the unit interval

On the interval `(0, 1)`, realized as the open subset `TauCeti.PDE.intervalDomain 0 1` of the
Euclidean line, this file solves the weak Dirichlet problem for `-u'' = 1` explicitly, first with
zero boundary values and then with the boundary values `u(0) = 0`, `u(1) = 1`. The weak form asks
for `u ∈ H¹(0, 1)` with `∫ u' v' = ∫ v` for every `v ∈ H¹₀(0, 1)`, and the boundary condition is
`u - g ∈ H¹₀(0, 1)` for a lifting `g ∈ H¹(0, 1)` of the boundary values, as in
`TauCeti.PDE.existsUnique_sub_mem_w1p0Submodule_forall_energyFormH1_eq`.

* **Zero boundary values.** The weak solutions in `H¹₀(0, 1)` are exactly the functions equal to
  `x (1 - x) / 2` (`mem_w1p0Submodule_and_forall_energyFormH1_eq_iff`).
* **Boundary values `0` and `1`.** The weak solutions whose endpoint values
  (`TauCeti.W1p.intervalTraceL`) are `(0, 1)` are exactly the functions equal to
  `x (1 - x) / 2 + x` (`intervalTraceL_eq_and_forall_energyFormH1_eq_iff`).
* **The lifting `g = x`.** The function `x` lies in `H¹(0, 1)`
  (`exists_value_ae_eq_coord`) and has these boundary values, so the boundary condition
  `u - x ∈ H¹₀(0, 1)` selects the same solution `x (1 - x) / 2 + x`
  (`sub_mem_w1p0Submodule_and_forall_energyFormH1_eq_iff`): the solution with boundary values
  `0, 1` is the solution with zero boundary values plus the lifting, and the difference of the
  solution and the lifting is the zero-boundary solution `x (1 - x) / 2 ∈ H¹₀(0, 1)`.

Uniqueness in each case is the coercive Dirichlet problem with boundary values, through the
Poincaré inequality on the bounded domain `(0, 1)`
(`TauCeti.PDE.exists_isCoercive_laplacian_of_isBounded`). The explicit solutions are checked on
the real interval `(0, 1)` along the isometry `t ↦ t e₀` of `ℝ` onto the Euclidean line
(`TauCeti.PDE.intervalDomainEquivL`), where an integration by parts against the derivative
`k - t` of `k t - t² / 2` shows `∫ v' (k - t) = ∫ v` for every `v ∈ H¹₀(0, 1)`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., §6.2.1–§6.2.2 (boundary liftings and
  the Lax–Milgram solution of the Dirichlet problem).
* H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*, §8.4
  (one-dimensional boundary value problems).
-/

public section

noncomputable section

open MeasureTheory Set TopologicalSpace TauCeti TauCeti.PDE

namespace TauCeti.Examples.DirichletProblemUnitInterval

/-- A `C¹` function on `ℝ` restricts to a function in `H¹(0, 1)` with weak derivative its
derivative. -/
private theorem exists_value_gradient_ae_eq {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) :
    ∃ w : W1p volume (⟨Ioo 0 1, isOpen_Ioo⟩ : Opens ℝ) 2,
      W1p.value w =ᵐ[volume.restrict (Ioo 0 1)] f ∧
      W1p.gradient w =ᵐ[volume.restrict (Ioo 0 1)] deriv f :=
  AbsolutelyContinuousOnInterval.exists_w1p_value_gradient_ae_eq (p := 2)
    hf.contDiffOn.absolutelyContinuousOnInterval
    ((hf.continuous_deriv le_rfl).continuousOn.memLp_restrict_of_subset_isCompact isCompact_Icc
      measurableSet_Ioo Ioo_subset_Icc_self 2)

/-- A function in `H¹(0, 1)` equal to a continuous `f` has the endpoint values `(f 0, f 1)`. -/
private theorem intervalTraceL_eq_of_value_ae_eq {f : ℝ → ℝ} (hf : Continuous f)
    {w : W1p volume (⟨Ioo 0 1, isOpen_Ioo⟩ : Opens ℝ) 2}
    (hw : W1p.value w =ᵐ[volume.restrict (Ioo 0 1)] f) :
    W1p.intervalTraceL zero_lt_one w = (f 0, f 1) := by
  have hrep := (W1p.intervalRepresentativeL_eq_iff zero_lt_one w
    ⟨fun t => f t, hf.comp continuous_subtypeVal⟩).2 (by
      filter_upwards [hw, ae_restrict_mem measurableSet_Ioo] with t ht htI
      simpa [projIcc_of_mem zero_le_one (Ioo_subset_Icc_self htI)] using ht)
  simp [W1p.intervalTraceL_apply, hrep]

/-- **Integration by parts against `k - t` on `(0, 1)`**: for `v ∈ H¹₀(0, 1)`,
`∫ v' (k - t) = ∫ v`, the boundary terms vanishing with the endpoint values of `v`. -/
private theorem setIntegral_gradient_mul_sub (k : ℝ)
    {v : W1p volume (⟨Ioo 0 1, isOpen_Ioo⟩ : Opens ℝ) 2}
    (hv : v ∈ w1p0Submodule volume (⟨Ioo 0 1, isOpen_Ioo⟩ : Opens ℝ) 2) :
    ∫ t in Ioo 0 1, W1p.gradient v t * (k - t) = ∫ t in Ioo 0 1, W1p.value v t := by
  have hf : AbsolutelyContinuousOnInterval (fun t : ℝ => k - t) 0 1 :=
    (contDiff_const.sub contDiff_id).contDiffOn.absolutelyContinuousOnInterval
  have h := hf.integral_mul_deriv_eq_deriv_mul_of_ae_hasDerivAt (f' := fun _ => -1)
    (W1p.absolutelyContinuousOnInterval_intervalRepresentativeL zero_lt_one v)
    (ae_of_all _ fun t _ => by simpa using (hasDerivAt_id t).const_sub k)
    (W1p.ae_hasDerivAt_intervalRepresentativeL zero_lt_one v)
  have htr := W1p.intervalTraceL_eq_zero_of_mem_w1p0Submodule zero_lt_one hv
  rw [W1p.intervalTraceL_apply, Prod.mk_eq_zero] at htr
  simp only [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo] at h
  rw [projIcc_left, projIcc_right, htr.1, htr.2] at h
  rw [integral_congr_ae (W1p.value_ae_eq_intervalRepresentativeL zero_lt_one v)]
  simp only [mul_comm (W1p.gradient v _)]
  rw [h]
  simp only [mul_zero, sub_zero, zero_sub, neg_mul, one_mul, integral_neg, neg_neg]

/-- The explicit solution `k x - x² / 2` of `-u'' = 1` on the interval domain, with endpoint
values `(0, k - 1/2)`. -/
private theorem exists_solution (k : ℝ) :
    ∃ u : W1p volume (intervalDomain 0 1) 2,
      W1p.value u =ᵐ[volume.restrict (intervalDomain 0 1 : Set (EuclideanSpace ℝ (Fin 1)))]
          (fun x => k * x 0 - x 0 ^ 2 / 2) ∧
        W1p.intervalTraceL zero_lt_one (intervalDomainEquivL 0 1 2 u) = (0, k - 1 / 2) ∧
        ∀ v ∈ w1p0Submodule volume (intervalDomain 0 1) 2,
          energyFormH1 (fun _ => 1) 0 0 u v = ∫ x in intervalDomain 0 1, W1p.value v x := by
  have hd : deriv (fun t : ℝ => k * t - t ^ 2 / 2) = fun t => k - t := funext fun t => by
    have h : HasDerivAt (fun t : ℝ => k * t - t ^ 2 / 2) (k * 1 - 2 * t ^ (2 - 1) / 2) t :=
      ((hasDerivAt_id' t).const_mul k).sub ((hasDerivAt_pow 2 t).div_const 2)
    rw [h.deriv]
    ring
  obtain ⟨w, hw, hg⟩ := exists_value_gradient_ae_eq (f := fun t : ℝ => k * t - t ^ 2 / 2)
    (by fun_prop)
  rw [hd] at hg
  refine ⟨(intervalDomainEquivL 0 1 2).symm w, ?_, ?_, fun v hv => ?_⟩
  · filter_upwards [value_intervalDomainEquivL_symm_ae w,
      measurePreserving_lineEquiv_symm_restrict.quasiMeasurePreserving.ae hw] with x h1 h2
    rw [h1]
    simpa using h2
  · rw [ContinuousLinearEquiv.apply_symm_apply,
      intervalTraceL_eq_of_value_ae_eq (by fun_prop) hw]
    norm_num
  · rw [energyFormH1_one_zero_zero_eq_setIntegral_intervalDomainEquivL,
      ContinuousLinearEquiv.apply_symm_apply, setIntegral_value_intervalDomainEquivL,
      integral_congr_ae (hg.mono fun t ht => by rw [ht]),
      setIntegral_gradient_mul_sub k (intervalDomainEquivL_mem_w1p0Submodule_iff.2 hv)]

/-- Two weak solutions of `-u'' = 1` on `(0, 1)` with the same boundary values are equal: the
energy form of `-Δ` is coercive on `H¹₀(0, 1)`. -/
private theorem eq_of_sub_mem_w1p0Submodule {u u' : W1p volume (intervalDomain 0 1) 2}
    (h : u - u' ∈ w1p0Submodule volume (intervalDomain 0 1) 2)
    (hu : ∀ v ∈ w1p0Submodule volume (intervalDomain 0 1) 2,
      energyFormH1 (fun _ => 1) 0 0 u v = ∫ x in intervalDomain 0 1, W1p.value v x)
    (hu' : ∀ v ∈ w1p0Submodule volume (intervalDomain 0 1) 2,
      energyFormH1 (fun _ => 1) 0 0 u' v = ∫ x in intervalDomain 0 1, W1p.value v x) :
    u = u' := by
  obtain ⟨hcoeff, hcoercive⟩ := exists_isCoercive_laplacian_of_isBounded (n := 0)
    (Omega := intervalDomain 0 1) isBounded_intervalDomain
  let ℓ : StrongDual ℝ (W1p0 volume (intervalDomain 0 1) 2) :=
    W1p.integralL.comp (w1p0Submodule volume (intervalDomain 0 1) 2).toSubmodule.subtypeL
  refine (existsUnique_sub_mem_w1p0Submodule_forall_energyFormH1_eq hcoeff hcoercive u' ℓ).unique
    ⟨h, fun v => ?_⟩ ⟨by simp, fun v => ?_⟩
  · simpa [ℓ, W1p.integralL_apply] using hu v v.property
  · simpa [ℓ, W1p.integralL_apply] using hu' v v.property

/-- On the interval domain, equal endpoint values of the transfers to the real interval are the
boundary condition modulo `H¹₀(0, 1)`. -/
private theorem intervalTraceL_eq_iff_sub_mem {u u' : W1p volume (intervalDomain 0 1) 2} :
    W1p.intervalTraceL zero_lt_one (intervalDomainEquivL 0 1 2 u) =
        W1p.intervalTraceL zero_lt_one (intervalDomainEquivL 0 1 2 u') ↔
      u - u' ∈ w1p0Submodule volume (intervalDomain 0 1) 2 := by
  rw [W1p.intervalTraceL_eq_iff_sub_mem_w1p0Submodule (by norm_num) zero_lt_one, ← map_sub,
    intervalDomainEquivL_mem_w1p0Submodule_iff]

/-- **The Dirichlet problem `-u'' = 1`, `u(0) = u(1) = 0` on `(0, 1)`.** An element
`u ∈ H¹(0, 1)` of the interval domain is a weak solution, that is `u ∈ H¹₀(0, 1)` and
`∫ u' v' = ∫ v` for every `v ∈ H¹₀(0, 1)`, exactly when `u = x (1 - x) / 2`. -/
theorem mem_w1p0Submodule_and_forall_energyFormH1_eq_iff {u : W1p volume (intervalDomain 0 1) 2} :
    (u ∈ w1p0Submodule volume (intervalDomain 0 1) 2 ∧
      ∀ v ∈ w1p0Submodule volume (intervalDomain 0 1) 2,
        energyFormH1 (fun _ => 1) 0 0 u v = ∫ x in intervalDomain 0 1, W1p.value v x) ↔
      W1p.value u =ᵐ[volume.restrict (intervalDomain 0 1 : Set (EuclideanSpace ℝ (Fin 1)))]
        fun x => x 0 * (1 - x 0) / 2 := by
  obtain ⟨u₀, hval, htr, hsol⟩ := exists_solution (1 / 2)
  have hval' : W1p.value u₀ =ᵐ[volume.restrict
      (intervalDomain 0 1 : Set (EuclideanSpace ℝ (Fin 1)))]
      fun x => x 0 * (1 - x 0) / 2 := hval.mono fun x hx => by rw [hx]; ring
  have hmem : u₀ ∈ w1p0Submodule volume (intervalDomain 0 1) 2 := by
    rw [← intervalDomainEquivL_mem_w1p0Submodule_iff,
      W1p.mem_w1p0Submodule_iff_intervalTraceL_eq_zero (by norm_num) zero_lt_one, htr]
    norm_num
  refine ⟨fun hu => ?_, fun hu => ?_⟩
  · have : u = u₀ := eq_of_sub_mem_w1p0Submodule
      (Submodule.sub_mem _ hu.1 hmem) hu.2 hsol
    exact this ▸ hval'
  · have : u = u₀ := W1p.ext_value (Lp.ext (hu.trans hval'.symm))
    exact this ▸ ⟨hmem, hsol⟩

/-- **The Dirichlet problem `-u'' = 1`, `u(0) = 0`, `u(1) = 1` on `(0, 1)`.** An element
`u ∈ H¹(0, 1)` of the interval domain has the endpoint values `(0, 1)` and satisfies
`∫ u' v' = ∫ v` for every `v ∈ H¹₀(0, 1)` exactly when `u = x (1 - x) / 2 + x`. -/
theorem intervalTraceL_eq_and_forall_energyFormH1_eq_iff {u : W1p volume (intervalDomain 0 1) 2} :
    (W1p.intervalTraceL zero_lt_one (intervalDomainEquivL 0 1 2 u) = (0, 1) ∧
      ∀ v ∈ w1p0Submodule volume (intervalDomain 0 1) 2,
        energyFormH1 (fun _ => 1) 0 0 u v = ∫ x in intervalDomain 0 1, W1p.value v x) ↔
      W1p.value u =ᵐ[volume.restrict (intervalDomain 0 1 : Set (EuclideanSpace ℝ (Fin 1)))]
        fun x => x 0 * (1 - x 0) / 2 + x 0 := by
  obtain ⟨u₁, hval, htr, hsol⟩ := exists_solution (3 / 2)
  have hval' : W1p.value u₁ =ᵐ[volume.restrict
      (intervalDomain 0 1 : Set (EuclideanSpace ℝ (Fin 1)))]
      fun x => x 0 * (1 - x 0) / 2 + x 0 := hval.mono fun x hx => by rw [hx]; ring
  have htr' : W1p.intervalTraceL zero_lt_one (intervalDomainEquivL 0 1 2 u₁) = (0, 1) := by
    rw [htr]
    norm_num
  refine ⟨fun hu => ?_, fun hu => ?_⟩
  · have : u = u₁ := eq_of_sub_mem_w1p0Submodule
      (intervalTraceL_eq_iff_sub_mem.1 (hu.1.trans htr'.symm)) hu.2 hsol
    exact this ▸ hval'
  · have : u = u₁ := W1p.ext_value (Lp.ext (hu.trans hval'.symm))
    exact this ▸ ⟨htr', hsol⟩

/-- **The lifting `x` of the boundary values `0, 1`.** The coordinate `x` lies in `H¹(0, 1)` of
the interval domain. -/
theorem exists_value_ae_eq_coord :
    ∃ g : W1p volume (intervalDomain 0 1) 2,
      W1p.value g =ᵐ[volume.restrict (intervalDomain 0 1 : Set (EuclideanSpace ℝ (Fin 1)))]
        fun x => x 0 := by
  obtain ⟨w, hw, -⟩ := exists_value_gradient_ae_eq (f := id) contDiff_id
  refine ⟨(intervalDomainEquivL 0 1 2).symm w, ?_⟩
  filter_upwards [value_intervalDomainEquivL_symm_ae w,
    measurePreserving_lineEquiv_symm_restrict.quasiMeasurePreserving.ae hw] with x h1 h2
  rw [h1]
  simpa using h2

/-- **The Dirichlet problem `-u'' = 1` on `(0, 1)` with the lifting `g = x`.** For any
`g ∈ H¹(0, 1)` equal to `x`, an element `u ∈ H¹(0, 1)` of the interval domain satisfies
`u - g ∈ H¹₀(0, 1)` and `∫ u' v' = ∫ v` for every `v ∈ H¹₀(0, 1)` exactly when
`u = x (1 - x) / 2 + x`: the solution with zero boundary values plus the lifting. -/
theorem sub_mem_w1p0Submodule_and_forall_energyFormH1_eq_iff
    {g u : W1p volume (intervalDomain 0 1) 2}
    (hg : W1p.value g =ᵐ[volume.restrict (intervalDomain 0 1 : Set (EuclideanSpace ℝ (Fin 1)))]
      fun x => x 0) :
    (u - g ∈ w1p0Submodule volume (intervalDomain 0 1) 2 ∧
      ∀ v ∈ w1p0Submodule volume (intervalDomain 0 1) 2,
        energyFormH1 (fun _ => 1) 0 0 u v = ∫ x in intervalDomain 0 1, W1p.value v x) ↔
      W1p.value u =ᵐ[volume.restrict (intervalDomain 0 1 : Set (EuclideanSpace ℝ (Fin 1)))]
        fun x => x 0 * (1 - x 0) / 2 + x 0 := by
  have hgtr : W1p.intervalTraceL zero_lt_one (intervalDomainEquivL 0 1 2 g) = (0, 1) := by
    refine intervalTraceL_eq_of_value_ae_eq continuous_id ?_
    filter_upwards [value_intervalDomainEquivL_ae g,
      measurePreserving_lineEquiv_restrict.quasiMeasurePreserving.ae hg] with t h1 h2
    rw [h1, h2, lineEquiv_apply_zero, id]
  rw [← intervalTraceL_eq_iff_sub_mem, hgtr]
  exact intervalTraceL_eq_and_forall_energyFormH1_eq_iff

end TauCeti.Examples.DirichletProblemUnitInterval
