/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Divisors
public import TauCeti.NumberTheory.ModularForms.EisensteinSeries.WeightTwo.Basic
public import TauCeti.NumberTheory.ModularForms.CongruenceSubgroups.Basic
public import TauCeti.NumberTheory.ModularForms.QExpansion.Basic

/-!
# Linear independence of corrected weight-two Eisenstein series

For each divisor `d > 1` of `N`, the corrected series `E₂(z) - d E₂(dz)` is a modular form
on `Γ₀(N)`. These forms are linearly independent: the q-coefficient at `q¹` forces the
coefficients in a relation to sum to zero, and then the coefficient at the least divisor with a
nonzero scalar isolates that term. This independence is a useful input when comparing corrected
weight-two Eisenstein series with cusp constant-term data.

## Main results

* `correctedE2AtLevel`: the restriction of the level-`d` corrected series to `Γ₀(N)`.
* `qExpansion_coeff_correctedE2AtLevel`: the coefficients of each restricted series.
* `linearIndependent_correctedE2AtLevel`: independence of this family over all nontrivial
  divisor levels `d` of `N`.
* `finrank_span_correctedE2AtLevel`: the corrected span has dimension `τ(N) - 1` at every
  nonzero level.

## References

* F. Diamond and J. Shurman, *A First Course in Modular Forms*, Chapter 4.
-/

public noncomputable section

open Matrix Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup ModularForm
open scoped MatrixGroups ModularForm ArithmeticFunction.sigma

namespace TauCeti.EisensteinSeries

/-- The corrected weight-two Eisenstein series of level `d`, restricted to `Γ₀(N)`. -/
def correctedE2AtLevel (N : ℕ) (d : {d : ℕ // 1 < d ∧ d ∣ N}) :
    ModularForm ((Gamma0 N).map (mapGL ℝ)) 2 :=
  ModularForm.restrict (Subgroup.map_mono
    (CongruenceSubgroup.Gamma0_le_Gamma0_of_dvd d.2.2)) (@correctedE2 d.val ⟨by omega⟩)

/-- Evaluating a corrected series after restricting its level gives the original series. -/
@[simp]
theorem correctedE2AtLevel_apply (N : ℕ) (d : {d : ℕ // 1 < d ∧ d ∣ N}) (z : ℍ) :
    correctedE2AtLevel N d z = @correctedE2 d.val ⟨by omega⟩ z := by
  simp only [correctedE2AtLevel, ModularForm.coe_restrict]

/-- The q-expansion coefficients of the corrected series restricted from `Γ₀(d)` to `Γ₀(N)`. -/
@[simp]
theorem qExpansion_coeff_correctedE2AtLevel (N : ℕ)
    (d : {d : ℕ // 1 < d ∧ d ∣ N}) (n : ℕ) :
    (UpperHalfPlane.qExpansion 1 (correctedE2AtLevel N d)).coeff n =
    if n = 0 then 1 - (d.val : ℂ) else
        -24 * ((σ 1 n : ℂ) -
          if d.val ∣ n then d.val * (σ 1 (n / d.val) : ℂ) else 0) := by
  simpa only [correctedE2AtLevel, ModularForm.coe_restrict] using
    @qExpansion_coeff_correctedE2 d.val ⟨by omega⟩ n

private lemma coeff_sum_eq_zero (N : ℕ) (s : Finset {d : ℕ // 1 < d ∧ d ∣ N})
    (g : {d : ℕ // 1 < d ∧ d ∣ N} → ℂ)
    (hsum : ∑ j ∈ s, g j • correctedE2AtLevel N j = 0)
    (n : ℕ) (hn : n ≠ 0) :
    ∑ j ∈ s, g j * (-24 * ((σ 1 n : ℂ) -
      if j.val ∣ n then j.val * (σ 1 (n / j.val) : ℂ) else 0)) = 0 := by
  let Q := ModularForm.qExpansionLinearMap one_pos (one_mem_strictPeriods_Gamma0_map N) 2
  let Qcoeff : ModularForm ((Gamma0 N).map (mapGL ℝ)) 2 →ₗ[ℂ] ℂ :=
    (PowerSeries.coeff n).comp Q
  have hc := congrArg Qcoeff hsum
  rw [map_sum] at hc
  simp only [Qcoeff, Q, LinearMap.comp_apply, map_smul, map_zero,
    ModularForm.qExpansionLinearMap_apply, qExpansion_coeff_correctedE2AtLevel, hn] at hc
  simpa [smul_eq_mul] using hc

private lemma sum_coefficients_eq_zero (N : ℕ)
    (s : Finset {d : ℕ // 1 < d ∧ d ∣ N})
    (g : {d : ℕ // 1 < d ∧ d ∣ N} → ℂ)
    (hcoeff : ∀ n, n ≠ 0 →
      ∑ j ∈ s, g j * (-24 * ((σ 1 n : ℂ) -
        if j.val ∣ n then j.val * (σ 1 (n / j.val) : ℂ) else 0)) = 0) :
    ∑ j ∈ s, g j = 0 := by
  have h := hcoeff 1 one_ne_zero
  have hnotdiv (j : {d : ℕ // 1 < d ∧ d ∣ N}) : ¬j.val ∣ 1 := by
    intro hd
    have := Nat.le_of_dvd (by omega) hd
    omega
  have h' : (∑ j ∈ s, g j) * (-24) = 0 := by
    convert h using 1
    all_goals simp [hnotdiv, ArithmeticFunction.sigma_one, ← Finset.sum_mul]
  exact (mul_eq_zero.mp h').resolve_right (by norm_num)

private lemma least_divisor_correction_eq (N : ℕ)
    (s : Finset {d : ℕ // 1 < d ∧ d ∣ N})
    (g : {d : ℕ // 1 < d ∧ d ∣ N} → ℂ)
    (m : {d : ℕ // 1 < d ∧ d ∣ N}) (hm : m ∈ s)
    (hmin : ∀ j ∈ s, g j ≠ 0 → m.val ≤ j.val) :
    ∑ j ∈ s, g j * (if j.val ∣ m.val then
      24 * (j.val : ℂ) * σ 1 (m.val / j.val) else 0) =
      g m * (24 * (m.val : ℂ)) := by
  rw [Finset.sum_eq_single_of_mem m hm (fun j hj hneq ↦ by
    by_cases hgj : g j = 0
    · simp [hgj]
    · by_cases hdiv : j.val ∣ m.val
      · have hmj := hmin j hj hgj
        have hjm' : j.val ≤ m.val := Nat.le_of_dvd (by omega) hdiv
        have heq : j = m := Subtype.ext (Nat.le_antisymm hjm' hmj)
        exact (hneq heq).elim
      · simp [hdiv])]
  simp [Nat.div_self (by omega : 0 < m.val)]

/-- **Independence of the corrected weight-two Eisenstein series.** For fixed `N`, the
corrected series at the divisor levels `d > 1` of `N` are linearly independent in
`M₂(Γ₀(N))`. -/
theorem linearIndependent_correctedE2AtLevel (N : ℕ) :
    LinearIndependent ℂ (correctedE2AtLevel N : {d : ℕ // 1 < d ∧ d ∣ N} →
      ModularForm ((Gamma0 N).map (mapGL ℝ)) 2) := by
  classical
  rw [linearIndependent_iff']
  intro s g hsum i hi
  by_contra hgi
  let t := s.filter fun j ↦ g j ≠ 0
  have hti : i ∈ t := Finset.mem_filter.mpr ⟨hi, hgi⟩
  let m := t.min' ⟨i, hti⟩
  have hm : m ∈ t := Finset.min'_mem t ⟨i, hti⟩
  have hmin (j : {d : ℕ // 1 < d ∧ d ∣ N}) (hj : j ∈ t) : m.val ≤ j.val := by
    exact_mod_cast (Finset.min'_le t j hj)
  have hcoeff (n : ℕ) (hn : n ≠ 0) := coeff_sum_eq_zero N s g hsum n hn
  -- The `q¹` coefficient has no divisor corrections because each level `d` is greater than one.
  have hsum_g := sum_coefficients_eq_zero N s g hcoeff
  have hmpos : m.val ≠ 0 := by omega
  have hcoeff_m := hcoeff m.val hmpos
  -- After this common term cancels, only the least supported divisor can contribute at `qᵐ`.
  have hcorrection :
      ∑ j ∈ s, g j * (if j.val ∣ m.val then
        24 * (j.val : ℂ) * σ 1 (m.val / j.val) else 0) = 0 := by
    have hrewrite :
        ∑ j ∈ s, g j * (-24 * ((σ 1 m.val : ℂ) -
          if j.val ∣ m.val then j.val * (σ 1 (m.val / j.val) : ℂ) else 0)) =
        (-24 * (σ 1 m.val : ℂ)) * (∑ j ∈ s, g j) +
          ∑ j ∈ s, g j * (if j.val ∣ m.val then
            24 * (j.val : ℂ) * σ 1 (m.val / j.val) else 0) := by
      calc
        _ = ∑ j ∈ s, (-24 * (σ 1 m.val : ℂ) * g j +
            g j * (if j.val ∣ m.val then
              24 * (j.val : ℂ) * σ 1 (m.val / j.val) else 0)) := by
          apply Finset.sum_congr rfl
          intro j hj
          by_cases hd : j.val ∣ m.val <;> simp [hd] <;> ring
        _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [hrewrite, hsum_g] at hcoeff_m
    simpa using hcoeff_m
  have hcorrection_eq :
      ∑ j ∈ s, g j * (if j.val ∣ m.val then
        24 * (j.val : ℂ) * σ 1 (m.val / j.val) else 0) =
        g m * (24 * (m.val : ℂ)) :=
    least_divisor_correction_eq N s g m (Finset.mem_filter.mp hm).1
      (fun j hj hgj ↦ hmin j (Finset.mem_filter.mpr ⟨hj, hgj⟩))
  rw [hcorrection_eq] at hcorrection
  have hgm : g m ≠ 0 := (Finset.mem_filter.mp hm).2
  have hscale : (24 : ℂ) * (m.val : ℂ) ≠ 0 :=
    mul_ne_zero (by norm_num) (Nat.cast_ne_zero.mpr hmpos)
  exact (mul_ne_zero hgm hscale) hcorrection

/-- The corrected weight-two Eisenstein span has dimension `τ(N) - 1`, at any nonzero level. -/
theorem finrank_span_correctedE2AtLevel {N : ℕ} [NeZero N] :
    Module.finrank ℂ (Submodule.span ℂ (Set.range (correctedE2AtLevel N))) =
      N.divisors.card - 1 := by
  classical
  let _ := Fintype.ofEquiv _ (nontrivialDivisorEquiv (N := N)).symm
  rw [finrank_span_eq_card (linearIndependent_correctedE2AtLevel N),
    Fintype.card_congr (nontrivialDivisorEquiv (N := N))]
  simp

end TauCeti.EisensteinSeries
