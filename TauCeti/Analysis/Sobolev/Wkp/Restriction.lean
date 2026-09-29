/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Wkp.Basic
public import TauCeti.Analysis.Sobolev.W1p.Restriction

/-!
# Restriction of arbitrary-order Sobolev functions

Restriction to an open subdomain is a contraction on `W^{k,p}` for every natural order `k`
and every `1 ≤ p ≤ ∞`. It commutes with the value, lower-order, and highest weak derivative
projections. This supplies localization for smooth approximation and interior estimates without
any boundary regularity assumption.

The construction uses `W1p.restrictL` at first order and restricts the successive weak derivative
fields through Mathlib's `Lp.LpToLpOfMeasureLeSMul`.

## References

L. C. Evans, *Partial Differential Equations*, Chapter 5, §§5.2–5.3.
-/

public section

noncomputable section

namespace TauCeti.Wkp

open MeasureTheory Set TopologicalSpace
open scoped ENNReal

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {Omega U V : Opens E} {p : ENNReal} [Fact (1 ≤ p)]

private theorem exists_restrict_step (hU : U ≤ Omega) (k : ℕ)
    (u : Wkp mu Omega p (k + 2)) (v : Wkp mu U p (k + 1))
    (hv : value (k + 1) v =ᵐ[mu.restrict U] value (k + 1) (lowerOrder (k + 1) u))
    (hDv : iteratedGradient k v =ᵐ[mu.restrict U]
      iteratedGradient k (lowerOrder (k + 1) u))
    (hnorm : ‖v‖ ≤ ‖lowerOrder (k + 1) u‖) :
    ∃ w : Wkp mu U p (k + 2),
      value (k + 2) w =ᵐ[mu.restrict U] value (k + 2) u ∧
      iteratedGradient (k + 1) w =ᵐ[mu.restrict U] iteratedGradient (k + 1) u ∧
      ‖w‖ ≤ ‖u‖ := by
  let r : Lp (IteratedGradient E (k + 1)) p (mu.restrict Omega) →L[ℝ]
      Lp (IteratedGradient E (k + 1)) p (mu.restrict U) :=
    Lp.LpToLpOfMeasureLeSMul (c := 1) (by simp) (by
      simpa only [one_smul] using
        Measure.restrict_mono_set mu (SetLike.coe_subset_coe.mpr hU))
  let D := r (iteratedGradient (k + 1) u)
  have hD : D =ᵐ[mu.restrict U] iteratedGradient (k + 1) u :=
    Lp.coeFn_LpToLpOfMeasureLeSMul _ _ _
  have hweak : HasWeakFDerivOn mu U (iteratedGradient k v) D :=
    ((hasWeakFDerivOn_iteratedGradient k u).mono hU).congr_ae hDv.symm
      |>.congr_ae_deriv hD.symm
  refine ⟨mk k v D hweak, ?_, ?_, ?_⟩
  · simpa only [value_succ, lowerOrder_mk] using hv
  · simpa only [iteratedGradient_mk] using hD
  · have hDn : ‖D‖ ≤ ‖iteratedGradient (k + 1) u‖ := by
      have hop : ‖r‖ ≤ 1 := by
        simpa only [ENNReal.toReal_one, Real.one_rpow] using
          Lp.norm_LpToLpOfMeasureLeSMul_le
            (E := IteratedGradient E (k + 1)) (p := p) (c := 1) (by simp)
            (by simpa only [one_smul] using
              Measure.restrict_mono_set mu (SetLike.coe_subset_coe.mpr hU))
      simpa only [one_mul] using r.le_of_opNorm_le hop (iteratedGradient (k + 1) u)
    have ht := norm_sq_eq_norm_lowerOrder_sq_add_norm_iteratedGradient_sq_add_two k u
    have hn := sq_le_sq₀ (norm_nonneg v) (norm_nonneg _) |>.2 hnorm
    have hd := sq_le_sq₀ (norm_nonneg D) (norm_nonneg _) |>.2 hDn
    have heq := norm_sq_eq_norm_lowerOrder_sq_add_norm_iteratedGradient_sq_add_two k
      (mk k v D hweak)
    simp only [lowerOrder_mk, iteratedGradient_mk] at heq
    nlinarith [norm_nonneg (mk k v D hweak), norm_nonneg u]

private theorem exists_restrict_succ (hU : U ≤ Omega) : ∀ (k : ℕ)
    (u : Wkp mu Omega p (k + 1)), ∃ v : Wkp mu U p (k + 1),
      value (k + 1) v =ᵐ[mu.restrict U] value (k + 1) u ∧
      iteratedGradient k v =ᵐ[mu.restrict U] iteratedGradient k u ∧ ‖v‖ ≤ ‖u‖ := by
  intro k
  induction k with
  | zero =>
      intro u
      refine ⟨W1p.restrictL hU u, ?_, ?_, W1p.norm_restrictL_le hU u⟩
      · simpa only [Nat.reduceAdd, value_one] using W1p.value_restrictL_ae hU u
      · simpa only [iteratedGradient_zero] using W1p.gradient_restrictL_ae hU u
  | succ k ih =>
      intro u
      obtain ⟨v, hv, hDv, hnorm⟩ := ih (lowerOrder (k + 1) u)
      exact exists_restrict_step hU k u v hv hDv hnorm

private def restrictAux (hU : U ≤ Omega) : (k : ℕ) → Wkp mu Omega p k → Wkp mu U p k
  | 0, u => Lp.LpToLpOfMeasureLeSMul (c := 1) (by simp) (by
      simpa only [one_smul] using
        Measure.restrict_mono_set mu (SetLike.coe_subset_coe.mpr hU)) u
  | k + 1, u => (exists_restrict_succ hU k u).choose

private theorem value_restrictAux_ae (hU : U ≤ Omega) (k : ℕ) (u : Wkp mu Omega p k) :
    value k (restrictAux hU k u) =ᵐ[mu.restrict U] value k u := by
  cases k with
  | zero =>
      simp only [value_zero, restrictAux]
      exact Lp.coeFn_LpToLpOfMeasureLeSMul _ _ _
  | succ k => exact (exists_restrict_succ hU k u).choose_spec.1

private theorem value_restrictAux (hU : U ≤ Omega) (k : ℕ) (u : Wkp mu Omega p k) :
    value k (restrictAux hU k u) =
      Lp.LpToLpOfMeasureLeSMul (c := 1) (by simp) (by
        simpa only [one_smul] using
          Measure.restrict_mono_set mu (SetLike.coe_subset_coe.mpr hU)) (value k u) :=
  Lp.ext ((value_restrictAux_ae hU k u).trans
    (Lp.coeFn_LpToLpOfMeasureLeSMul _ _ _).symm)

private theorem norm_restrictAux_le (hU : U ≤ Omega) (k : ℕ) (u : Wkp mu Omega p k) :
    ‖restrictAux hU k u‖ ≤ ‖u‖ := by
  cases k with
  | zero =>
      simp only [restrictAux]
      let r : Lp ℝ p (mu.restrict Omega) →L[ℝ] Lp ℝ p (mu.restrict U) :=
        Lp.LpToLpOfMeasureLeSMul (c := 1) (by simp) (by
          simpa only [one_smul] using
            Measure.restrict_mono_set mu (SetLike.coe_subset_coe.mpr hU))
      have hop : ‖r‖ ≤ 1 := by
        simpa only [ENNReal.toReal_one, Real.one_rpow] using
          Lp.norm_LpToLpOfMeasureLeSMul_le (E := ℝ) (p := p) (c := 1) (by simp)
            (by simpa only [one_smul] using
              Measure.restrict_mono_set mu (SetLike.coe_subset_coe.mpr hU))
      simpa only [one_mul] using r.le_of_opNorm_le hop u
  | succ k => exact (exists_restrict_succ hU k u).choose_spec.2.2

/-- Restrict an arbitrary-order weak Sobolev function to an open subdomain.
This continuous linear map has operator norm at most one. -/
def restrictL (hU : U ≤ Omega) (k : ℕ) : Wkp mu Omega p k →L[ℝ] Wkp mu U p k :=
  LinearMap.mkContinuous
    { toFun := restrictAux hU k
      map_add' := fun u v => by
        apply ext k
        simp only [value_add, value_restrictAux, map_add]
      map_smul' := fun c u => by
        apply ext k
        simp only [value_smul, value_restrictAux, map_smul, RingHom.id_apply] }
    1 (fun u => by
      simpa only [LinearMap.coe_mk, AddHom.coe_mk, one_mul] using norm_restrictAux_le hU k u)

/-- Restriction commutes with the `Lᵖ` value projection. -/
@[simp]
theorem value_restrictL (hU : U ≤ Omega) (k : ℕ) (u : Wkp mu Omega p k) :
    value k (restrictL hU k u) =
      Lp.LpToLpOfMeasureLeSMul (c := 1) (by simp) (by
        simpa only [one_smul] using
          Measure.restrict_mono_set mu (SetLike.coe_subset_coe.mpr hU)) (value k u) :=
  value_restrictAux hU k u

/-- Restriction keeps the same value representative on the smaller domain. -/
theorem value_restrictL_ae (hU : U ≤ Omega) (k : ℕ) (u : Wkp mu Omega p k) :
    value k (restrictL hU k u) =ᵐ[mu.restrict U] value k u :=
  value_restrictAux_ae hU k u

/-- Restriction keeps the same highest weak derivative on the smaller domain. -/
theorem iteratedGradient_restrictL_ae (hU : U ≤ Omega) (k : ℕ)
    (u : Wkp mu Omega p (k + 1)) :
    iteratedGradient k (restrictL hU (k + 1) u) =ᵐ[mu.restrict U] iteratedGradient k u :=
  (exists_restrict_succ hU k u).choose_spec.2.1

/-- Restriction commutes with the highest weak derivative projection.
Use `rw` with this lemma: `simp` does not match its dependently indexed left-hand side. -/
theorem iteratedGradient_restrictL (hU : U ≤ Omega) (k : ℕ)
    (u : Wkp mu Omega p (k + 1)) :
    iteratedGradient k (restrictL hU (k + 1) u) =
      Lp.LpToLpOfMeasureLeSMul (c := 1) (by simp) (by
        simpa only [one_smul] using
          Measure.restrict_mono_set mu (SetLike.coe_subset_coe.mpr hU)) (iteratedGradient k u) :=
  Lp.ext ((iteratedGradient_restrictL_ae hU k u).trans
    (Lp.coeFn_LpToLpOfMeasureLeSMul _ _ _).symm)

/-- Forgetting the highest derivative commutes with restriction.
Use `rw` with this lemma: `simp` does not match its dependently indexed left-hand side. -/
theorem lowerOrder_restrictL (hU : U ≤ Omega) (k : ℕ)
    (u : Wkp mu Omega p (k + 1)) :
    lowerOrder k (restrictL hU (k + 1) u) = restrictL hU k (lowerOrder k u) := by
  apply ext k
  rw [← value_succ, value_restrictL, value_succ, value_restrictL]

/-- Restriction does not increase the Sobolev norm. -/
theorem norm_restrictL_le (hU : U ≤ Omega) (k : ℕ) (u : Wkp mu Omega p k) :
    ‖restrictL hU k u‖ ≤ ‖u‖ :=
  norm_restrictAux_le hU k u

/-- The restriction operator has norm at most one. -/
theorem norm_restrictL_le_one (hU : U ≤ Omega) (k : ℕ) :
    ‖restrictL (mu := mu) (p := p) hU k‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun u => by
    simpa only [one_mul] using norm_restrictL_le hU k u

/-- Restricting to the original domain is the identity. -/
@[simp]
theorem restrictL_self (k : ℕ) (u : Wkp mu Omega p k) : restrictL le_rfl k u = u :=
  ext k (Lp.ext (value_restrictL_ae le_rfl k u))

/-- Restricting along two inclusions agrees with restricting along their composite. -/
@[simp]
theorem restrictL_restrictL (hU : U ≤ Omega) (hV : V ≤ U) (k : ℕ)
    (u : Wkp mu Omega p k) :
    restrictL hV k (restrictL hU k u) = restrictL (hV.trans hU) k u := by
  apply ext k
  apply Lp.ext
  have hsecond := (value_restrictL_ae hU k u).filter_mono
    (MeasureTheory.ae_mono (Measure.restrict_mono_set mu (SetLike.coe_subset_coe.mpr hV)))
  exact ((value_restrictL_ae hV k _).trans hsecond).trans
    (value_restrictL_ae (hV.trans hU) k u).symm

/-- At order zero, Sobolev restriction is Mathlib's `Lᵖ` restriction. -/
@[simp]
theorem restrictL_zero (hU : U ≤ Omega) :
    restrictL (mu := mu) (p := p) hU 0 =
      Lp.LpToLpOfMeasureLeSMul (E := ℝ) (c := 1) (by simp) (by
        simpa only [one_smul] using
          Measure.restrict_mono_set mu (SetLike.coe_subset_coe.mpr hU)) := by
  apply ContinuousLinearMap.ext
  intro u
  simpa only [value_zero] using value_restrictL hU 0 u

/-- At order one, Sobolev restriction agrees with the first-order API. -/
@[simp]
theorem restrictL_one (hU : U ≤ Omega) :
    restrictL (mu := mu) (p := p) hU 1 = W1p.restrictL hU := by
  apply ContinuousLinearMap.ext
  intro u
  apply W1p.ext_value
  rw [W1p.value_restrictL hU u]
  simpa only [value_one] using value_restrictL hU 1 u

end TauCeti.Wkp
