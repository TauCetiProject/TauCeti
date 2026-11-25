/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.LocallyConvex.SeparatingDual
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import TauCeti.MeasureTheory.Measure.IntegerSlabs

/-!
# Bochner integrals of translation-invariant functions

An integrand invariant almost everywhere under translation by a nonzero vector `k` in a real
vector space with a separating dual has Bochner integral `0` against every measure preserved by
translation by `k` (`MeasureTheory.integral_eq_zero_of_ae_add_right_eq`). No integrability
hypothesis is needed, since the Bochner integral of a nonintegrable function is `0`.
-/

public section

open Set

namespace MeasureTheory

/-- An integrand invariant almost everywhere under translation by a nonzero vector `k` of a real
topological vector space with a separating dual has integral `0` against every measure preserved
by translation by `k`. A continuous linear functional `φ` with `φ k = 1` cuts the space into the
slabs `n ≤ φ x < n + 1`, which translation by `k` shifts by one index, so all slabs carry the same
integral of the norm of the integrand; their sum over `ℤ` is finite only when each vanishes. -/
theorem integral_eq_zero_of_ae_add_right_eq {V E : Type*} [AddCommGroup V] [Module ℝ V]
    [TopologicalSpace V] [SeparatingDual ℝ V] [MeasurableSpace V] [OpensMeasurableSpace V]
    [NormedAddCommGroup E] [NormedSpace ℝ E] {ν : Measure V} {k : V} (hk : k ≠ 0)
    (hν : MeasurePreserving (· + k) ν ν) {g : V → E} (hg : ∀ᵐ x ∂ν, g (x + k) = g x) :
    ∫ x, g x ∂ν = 0 := by
  by_cases hint : Integrable g ν
  swap
  · exact integral_undef hint
  obtain ⟨φ, hφ⟩ := SeparatingDual.exists_eq_one (R := ℝ) hk
  let T : ℤ → Set V := fun n ↦ φ ⁻¹' Ico (n : ℝ) (n + 1)
  have hTm : ∀ n : ℤ, MeasurableSet (T n) := fun _ ↦ φ.continuous.measurable measurableSet_Ico
  -- Translation by `k` carries the slab `T n` onto `T (n + 1)`.
  have hTsucc : ∀ n : ℤ, (· + k) ⁻¹' T (n + 1) = T n := fun n ↦ by
    ext x
    simp only [T, mem_preimage, mem_Ico, map_add, hφ, Int.cast_add, Int.cast_one]
    constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith
  have hstep : ∀ n : ℤ, ∫⁻ x in T (n + 1), ‖g x‖ₑ ∂ν = ∫⁻ x in T n, ‖g x‖ₑ ∂ν := fun n ↦ by
    calc ∫⁻ x in T (n + 1), ‖g x‖ₑ ∂ν
        = ∫⁻ x, (T (n + 1)).indicator (fun y ↦ ‖g y‖ₑ) x ∂(ν.map (· + k)) := by
          rw [hν.map_eq, lintegral_indicator (hTm (n + 1))]
      _ = ∫⁻ x, (T (n + 1)).indicator (fun y ↦ ‖g y‖ₑ) (x + k) ∂ν :=
          lintegral_map' (by rw [hν.map_eq]; exact hint.1.eNorm.indicator (hTm (n + 1)))
            hν.measurable.aemeasurable
      _ = ∫⁻ x in T n, ‖g (x + k)‖ₑ ∂ν := by
          rw [← lintegral_indicator (hTm n)]
          refine lintegral_congr fun x ↦ ?_
          rw [← hTsucc n]
          by_cases hx : x + k ∈ T (n + 1) <;> simp [indicator, hx]
      _ = ∫⁻ x in T n, ‖g x‖ₑ ∂ν :=
          setLIntegral_congr_fun_ae (hTm n) (hg.mono fun x hx _ ↦ by rw [hx])
  have hc : ∀ n : ℤ, ∫⁻ x in T n, ‖g x‖ₑ ∂ν = ∫⁻ x in T 0, ‖g x‖ₑ ∂ν := fun n ↦ by
    induction n using Int.induction_on with
    | zero => rfl
    | succ m ih => rw [hstep, ih]
    | pred m ih => rw [← hstep, sub_add_cancel, ih]
  have hsum : ∫⁻ x, ‖g x‖ₑ ∂ν = ∑' _ : ℤ, ∫⁻ x in T 0, ‖g x‖ₑ ∂ν := by
    have h := TauCeti.measure_eq_tsum_inter_preimage_Ico (μ := ν.withDensity fun x ↦ ‖g x‖ₑ)
      φ.continuous.measurable nullMeasurableSet_univ
    simp only [univ_inter, withDensity_apply _ MeasurableSet.univ, setLIntegral_univ,
      withDensity_apply _ (φ.continuous.measurable measurableSet_Ico)] at h
    exact h.trans (tsum_congr hc)
  have h0 : ∫⁻ x in T 0, ‖g x‖ₑ ∂ν = 0 := by
    by_contra h
    have hfin : ∫⁻ x, ‖g x‖ₑ ∂ν < ⊤ := hint.2
    rw [hsum, ENNReal.tsum_const_eq_top_of_ne_zero h] at hfin
    exact lt_irrefl _ hfin
  have hae := (lintegral_eq_zero_iff' hint.1.eNorm).mp (by rw [hsum, h0, tsum_zero])
  exact integral_eq_zero_of_ae (hae.mono fun x hx ↦ eNorm_eq_zero.mp hx)

end MeasureTheory
