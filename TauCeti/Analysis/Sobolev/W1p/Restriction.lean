/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.W1p.CompactSupport

/-!
# Restriction of first-order Sobolev functions

A weakly differentiable function on an open set remains weakly differentiable on every smaller
open set.  This file packages that operation as the contractive continuous linear map
`TauCeti.W1p.restrictL`.  Its value and weak gradient are represented by the same functions on
the smaller domain, and restriction is functorial.

Restriction is the basic localization operation for Sobolev spaces.  In particular, it lets
local smooth approximations be compared with a given Sobolev function on relatively compact
subdomains, as required in the Meyers--Serrin density theorem, and lets interior regularity
arguments pass from a weak solution on `Ω` to smaller open sets.

## Main declarations

* `TauCeti.W1p.restrictL`: the contractive restriction map from `W^{1,p}(Ω)` to
  `W^{1,p}(U)` for `U ⊆ Ω`.
* `TauCeti.W1p.value_restrictL_ae` and `TauCeti.W1p.gradient_restrictL_ae`: restriction keeps
  the value and weak-gradient representatives on the smaller domain.
* `TauCeti.W1p.restrictL_self` and `TauCeti.W1p.restrictL_restrictL`: restriction is functorial.
* `TauCeti.W1p.restrictL_mem_closure_range_ofTestFunctionₗ`: on a relatively compact subdomain,
  every restriction is a Sobolev-norm limit of restrictions of test functions on the larger
  domain.

## References

L. C. Evans, *Partial Differential Equations*, Chapter 5, §5.2.
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory Set TopologicalSpace
open scoped Distributions ENNReal Gradient

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {Omega U V : Opens E} {p : ENNReal} [Fact (1 ≤ p)]

/-! ### Restriction of ambient jets -/

omit [FiniteDimensional ℝ E] [mu.IsAddHaarMeasure] in
/-- Restriction of an `Lᵖ` value-gradient jet to a smaller open set. -/
def Sobolev1JetLp.restrictL (hU : U ≤ Omega) :
    Sobolev1JetLp mu Omega p →L[ℝ] Sobolev1JetLp mu U p :=
  Lp.LpToLpOfMeasureLeSMul (c := 1) (by simp) (by
    simpa only [one_smul] using
      Measure.restrict_mono_set mu (SetLike.coe_subset_coe.mpr hU))

omit [FiniteDimensional ℝ E] [BorelSpace E] [mu.IsAddHaarMeasure] in
/-- Restricting an ambient jet keeps the same representative on the smaller open set. -/
theorem Sobolev1JetLp.coeFn_restrictL (hU : U ≤ Omega) (J : Sobolev1JetLp mu Omega p) :
    Sobolev1JetLp.restrictL hU J =ᵐ[mu.restrict U] J := by
  exact Lp.coeFn_LpToLpOfMeasureLeSMul (by simp)
    (by simpa only [one_smul] using
      Measure.restrict_mono_set mu (SetLike.coe_subset_coe.mpr hU)) J

omit [FiniteDimensional ℝ E] [BorelSpace E] [mu.IsAddHaarMeasure] in
/-- Restriction of ambient jets does not increase the `Lᵖ` norm. -/
theorem Sobolev1JetLp.norm_restrictL_le (hU : U ≤ Omega) (J : Sobolev1JetLp mu Omega p) :
    ‖Sobolev1JetLp.restrictL hU J‖ ≤ ‖J‖ := by
  have hop : ‖Sobolev1JetLp.restrictL (mu := mu) (p := p) hU‖ ≤ 1 := by
    simpa only [Sobolev1JetLp.restrictL, ENNReal.toReal_one, Real.one_rpow] using
      Lp.norm_LpToLpOfMeasureLeSMul_le (E := Sobolev1Jet E) (p := p)
        (μ := mu.restrict U) (ν := mu.restrict Omega) (c := 1) (by simp)
        (by simpa only [one_smul] using
          Measure.restrict_mono_set mu (SetLike.coe_subset_coe.mpr hU))
  calc
    ‖Sobolev1JetLp.restrictL hU J‖ ≤ ‖Sobolev1JetLp.restrictL (mu := mu) (p := p) hU‖ * ‖J‖ :=
      (Sobolev1JetLp.restrictL hU).le_opNorm J
    _ ≤ 1 * ‖J‖ := mul_le_mul_of_nonneg_right hop (norm_nonneg J)
    _ = ‖J‖ := one_mul _

/-! ### Restriction of Sobolev functions -/

/-- The restricted jet still satisfies the weak-derivative identity. -/
private theorem Sobolev1JetLp.restrictL_mem_w1pSubmodule (hU : U ≤ Omega)
    (u : W1p mu Omega p) :
    Sobolev1JetLp.restrictL hU (u : Sobolev1JetLp mu Omega p) ∈ w1pSubmodule mu U p := by
  rw [mem_w1pSubmodule_iff_hasWeakFDerivOn]
  let J := Sobolev1JetLp.restrictL hU (u : Sobolev1JetLp mu Omega p)
  have hJ := Sobolev1JetLp.coeFn_restrictL (mu := mu) (p := p) hU
    (u : Sobolev1JetLp mu Omega p)
  have hu_value := (W1p.value_apply_ae u).filter_mono
    (MeasureTheory.ae_mono (Measure.restrict_mono_set mu (SetLike.coe_subset_coe.mpr hU)))
  have hvalue : Sobolev1JetLp.value J =ᵐ[mu.restrict U] W1p.value u := by
    filter_upwards [Sobolev1JetLp.value_apply_ae J, hu_value, hJ] with x hJv huv hJu
    rw [hJv, huv, hJu]
  have hu_gradient := (W1p.gradient_apply_ae u).filter_mono
    (MeasureTheory.ae_mono (Measure.restrict_mono_set mu (SetLike.coe_subset_coe.mpr hU)))
  have hgradient : Sobolev1JetLp.gradient J =ᵐ[mu.restrict U] W1p.gradient u := by
    filter_upwards [Sobolev1JetLp.gradient_apply_ae J, hu_gradient, hJ]
      with x hJg hug hJu
    rw [hJg, hug, hJu]
  refine ((W1p.hasWeakFDerivOn u).mono hU).congr_ae hvalue.symm |>.congr_ae_deriv ?_
  filter_upwards [hgradient] with x hx
  apply ContinuousLinearMap.ext
  intro v
  rw [Sobolev1JetLp.candidateWeakFDeriv_apply, innerSL_apply_apply, real_inner_comm, hx]

/-- **Restriction of first-order Sobolev functions.**  If `U ⊆ Ω`, this is the continuous
linear map `W^{1,p}(Ω) → W^{1,p}(U)` obtained by restricting both the value and weak gradient.
It has operator norm at most one. -/
def W1p.restrictL (hU : U ≤ Omega) : W1p mu Omega p →L[ℝ] W1p mu U p :=
  ContinuousLinearMap.codRestrict
    ((Sobolev1JetLp.restrictL hU).comp (w1pSubmodule mu Omega p).toSubmodule.subtypeL)
    (w1pSubmodule mu U p).toSubmodule
    (Sobolev1JetLp.restrictL_mem_w1pSubmodule hU)

/-- The ambient jet of a restricted Sobolev function is the restriction of its ambient jet. -/
@[simp]
theorem W1p.coe_restrictL (hU : U ≤ Omega) (u : W1p mu Omega p) :
    ((W1p.restrictL hU u : W1p mu U p) : Sobolev1JetLp mu U p) =
      Sobolev1JetLp.restrictL hU (u : Sobolev1JetLp mu Omega p) :=
  (rfl)

/-- Restriction keeps the same value representative on the smaller open set. -/
theorem W1p.value_restrictL_ae (hU : U ≤ Omega) (u : W1p mu Omega p) :
    W1p.value (W1p.restrictL hU u) =ᵐ[mu.restrict U] W1p.value u := by
  have hJ := Sobolev1JetLp.coeFn_restrictL hU (u : Sobolev1JetLp mu Omega p)
  have hu := (W1p.value_apply_ae u).filter_mono
    (MeasureTheory.ae_mono (Measure.restrict_mono_set mu (SetLike.coe_subset_coe.mpr hU)))
  filter_upwards [W1p.value_apply_ae (W1p.restrictL hU u), hu, hJ]
    with x hres hu hx
  rw [hres, hu, W1p.coe_restrictL, hx]

/-- Restriction keeps the same weak-gradient representative on the smaller open set. -/
theorem W1p.gradient_restrictL_ae (hU : U ≤ Omega) (u : W1p mu Omega p) :
    W1p.gradient (W1p.restrictL hU u) =ᵐ[mu.restrict U] W1p.gradient u := by
  have hJ := Sobolev1JetLp.coeFn_restrictL hU (u : Sobolev1JetLp mu Omega p)
  have hu := (W1p.gradient_apply_ae u).filter_mono
    (MeasureTheory.ae_mono (Measure.restrict_mono_set mu (SetLike.coe_subset_coe.mpr hU)))
  filter_upwards [W1p.gradient_apply_ae (W1p.restrictL hU u), hu, hJ]
    with x hres hu hx
  rw [hres, hu, W1p.coe_restrictL, hx]

/-- Restriction does not increase the Sobolev norm. -/
theorem W1p.norm_restrictL_le (hU : U ≤ Omega) (u : W1p mu Omega p) :
    ‖W1p.restrictL hU u‖ ≤ ‖u‖ :=
  Sobolev1JetLp.norm_restrictL_le hU (u : Sobolev1JetLp mu Omega p)

/-- The restriction operator has norm at most one. -/
theorem W1p.norm_restrictL_le_one (hU : U ≤ Omega) :
    ‖W1p.restrictL (mu := mu) (p := p) hU‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun u => by
    simpa only [one_mul] using W1p.norm_restrictL_le hU u

/-- Restricting a Sobolev function to its original domain does nothing. -/
@[simp]
theorem W1p.restrictL_self (u : W1p mu Omega p) : W1p.restrictL le_rfl u = u := by
  apply W1p.ext_value
  apply Lp.ext
  exact W1p.value_restrictL_ae le_rfl u

/-- Restriction is functorial: restricting from `Ω` to `U` and then to `V` agrees with direct
restriction from `Ω` to `V`. -/
@[simp]
theorem W1p.restrictL_restrictL (hU : U ≤ Omega) (hV : V ≤ U) (u : W1p mu Omega p) :
    W1p.restrictL hV (W1p.restrictL hU u) = W1p.restrictL (hV.trans hU) u := by
  apply W1p.ext_value
  apply Lp.ext
  have hsecond : W1p.value (W1p.restrictL hU u) =ᵐ[mu.restrict V] W1p.value u :=
    (W1p.value_restrictL_ae hU u).filter_mono
      (MeasureTheory.ae_mono (Measure.restrict_mono_set mu (SetLike.coe_subset_coe.mpr hV)))
  exact ((W1p.value_restrictL_ae hV (W1p.restrictL hU u)).trans hsecond).trans
    (W1p.value_restrictL_ae (hV.trans hU) u).symm

/-! ### Local approximation by test functions -/

/-- **Local smooth approximation.**  Let `U` be relatively compact in `Ω`.  For
`1 ≤ p < ∞`, the restriction to `U` of every `u ∈ W^{1,p}(Ω)` lies in the closure of the
restrictions of test functions on `Ω`.

The approximants are smooth on all of `Ω`, not merely on `U`.  This is the local approximation
step in Meyers--Serrin density: a smooth cutoff equal to one on `closure U` first localizes `u`
away from `∂Ω`, after which density of test functions in `W^{1,p}_0(Ω)` applies. -/
theorem W1p.restrictL_mem_closure_range_ofTestFunctionₗ (hp : p ≠ ∞) (hU : U ≤ Omega)
    (hcompact : IsCompact (closure (U : Set E)))
    (hclosure : closure (U : Set E) ⊆ (Omega : Set E)) (u : W1p mu Omega p) :
    W1p.restrictL hU u ∈ closure (Set.range (fun (phi : 𝓓(Omega, ℝ)) =>
      W1p.restrictL hU (W1p.ofTestFunctionₗ mu Omega p phi))) := by
  obtain ⟨chi, hchi, hchi_range, hchi_one_nhds, hchi_cpt, hchi_ts⟩ :=
    hcompact.exists_contDiff_cutoff Omega.isOpen hclosure
  have hchi_mem : ∀ x, chi x ∈ Icc (0 : ℝ) 1 := fun x => hchi_range (mem_range_self x)
  obtain ⟨C, hC⟩ := (hchi.continuous_fderiv (by simp)).norm.bddAbove_range_of_hasCompactSupport
    ((hchi_cpt.fderiv ℝ).norm)
  let M : ℝ := max 1 C
  have hM0 : (0 : ℝ) ≤ M := zero_le_one.trans (le_max_left _ _)
  have hchiM : ∀ x ∈ (Omega : Set E), |chi x| ≤ M := fun x _ => by
    rw [abs_of_nonneg (hchi_mem x).1]
    exact (hchi_mem x).2.trans (le_max_left _ _)
  have hchigradM : ∀ x ∈ (Omega : Set E), ‖∇ chi x‖ ≤ M := fun x _ => by
    rw [_root_.gradient, LinearIsometryEquiv.norm_map]
    exact (hC ⟨x, rfl⟩).trans (le_max_right _ _)
  let v := W1p.contDiffSMul chi hchi hM0 hchiM hchigradM u
  have hv_zero : v ∈ w1p0Submodule mu Omega p :=
    W1p.contDiffSMul_mem_w1p0Submodule_of_hasCompactSupport hp hchi hM0 hchiM hchigradM
      hchi_cpt hchi_ts u
  have hv_closure : v ∈ closure (Set.range (W1p.ofTestFunctionₗ mu Omega p)) := by
    rw [← coe_w1p0Submodule]
    exact hv_zero
  have hrestrict : W1p.restrictL hU v = W1p.restrictL hU u := by
    apply W1p.ext_value
    apply Lp.ext
    have hv_value := (W1p.value_contDiffSMul_ae hchi hM0 hchiM hchigradM u).filter_mono
      (MeasureTheory.ae_mono (Measure.restrict_mono_set mu
        (SetLike.coe_subset_coe.mpr hU)))
    filter_upwards [W1p.value_restrictL_ae hU v, W1p.value_restrictL_ae hU u,
      hv_value, ae_restrict_mem U.isOpen.measurableSet] with x hv hu hmul hxU
    rw [hv, hu, hmul]
    have hxpre : x ∈ chi ⁻¹' ({1} : Set ℝ) :=
      interior_subset (hchi_one_nhds (subset_closure hxU))
    have hx_one : chi x = 1 := by simpa only [mem_preimage, mem_singleton_iff] using hxpre
    rw [hx_one, one_smul]
  rw [← hrestrict]
  refine map_mem_closure (W1p.restrictL hU).continuous hv_closure ?_
  rintro _ ⟨phi, rfl⟩
  exact ⟨phi, rfl⟩

end TauCeti
