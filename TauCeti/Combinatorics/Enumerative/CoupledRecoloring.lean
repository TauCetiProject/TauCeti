/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exp
import TauCeti.Combinatorics.Enumerative.RandomColoring

/-!
# Coupled low-discrepancy recolorings

* `TauCeti.exists_coupled_recoloring_abs_card_filter_sub_le`: coupled low-discrepancy recoloring
  bounding both total-variation edits on `S` and color discrepancies on test subsets `T i ⊆ S`.
-/

public section

open Finset Real

namespace TauCeti

variable {ι κ : Type*} [Fintype κ]

section
variable (m p : κ → ℝ)
private def couplingDeficit : ℝ := ∑ b, max (p b - m b) 0
open Classical in
private noncomputable def couplingKernel (c c' : κ) : ℝ := if m c ≤ p c then if c' = c then 1 else
  0 else (if c' = c then p c / m c else 0) + ((m c - p c) / m c) * (max (p c' - m c') 0 /
  couplingDeficit m p)
private theorem couplingDeficit_eq_surplus (hsum : ∑ b, m b = ∑ b, p b) : couplingDeficit m p = ∑
    b, max (m b - p b) 0 := by
  have h0 : ∑ b, (max (p b - m b) 0 - max (m b - p b) 0) = 0 := by
    rw [show ∑ b, (max (p b - m b) 0 - max (m b - p b) 0) = ∑ b, (p b - m b) from sum_congr rfl fun
      b _ ↦ by
        rcases le_total (m b) (p b) with h | h
        · rw [max_eq_left (sub_nonneg.2 h), max_eq_right (sub_nonpos.2 h), sub_zero]
        · rw [max_eq_right (sub_nonpos.2 h), max_eq_left (sub_nonneg.2 h)]; ring,
      sum_sub_distrib, hsum, sub_self]
  rwa [sum_sub_distrib, sub_eq_zero] at h0
private theorem couplingDeficit_eq_half_sum_abs (hsum : ∑ b, m b = ∑ b, p b) : ∑ b, max (m b - p b)
    0 = (∑ b, |m b - p b|) / 2 := by
  have hadd : ∑ b, max (m b - p b) 0 + couplingDeficit m p = ∑ b, |m b - p b| := by
    rw [couplingDeficit, ← sum_add_distrib]; refine sum_congr rfl fun b _ ↦ ?_
    rcases le_total (p b) (m b) with h | h
    · rw [max_eq_left (sub_nonneg.2 h), max_eq_right (sub_nonpos.2 h), add_zero, abs_of_nonneg
        (sub_nonneg.2 h)]
    · rw [max_eq_right (sub_nonpos.2 h), max_eq_left (sub_nonneg.2 h), zero_add, abs_of_nonpos
        (sub_nonpos.2 h)]; ring
  linarith [couplingDeficit_eq_surplus m p hsum]
private theorem couplingDeficit_pos_of_lt (hsum : ∑ b, m b = ∑ b, p b) {c : κ} (hc : p c < m c) : 0
    < couplingDeficit m p := couplingDeficit_eq_surplus m p hsum ▸ (lt_max_of_lt_left (sub_pos.2
    hc)).trans_le (single_le_sum (f := fun b ↦ max (m b - p b) 0) (fun _ _ ↦ le_max_right _ _)
    (mem_univ c))
private theorem couplingKernel_nonneg (hp : ∀ b, 0 ≤ p b) (hsum : ∑ b, m b = ∑ b, p b) (c c' : κ) :
    0 ≤ couplingKernel m p c c' := by
  classical
  unfold couplingKernel; by_cases hle : m c ≤ p c; · rw [ite_eq_left hle]; split_ifs <;> norm_num
  rw [ite_eq_right hle]; have hlt := not_le.1 hle; have hmc := (hp c).trans_lt hlt
  exact add_nonneg (by split_ifs; exacts [div_nonneg (hp c) hmc.le, le_rfl]) (mul_nonneg
    (div_nonneg (sub_nonneg.2 hlt.le) hmc.le) (div_nonneg (le_max_right _ _)
    (couplingDeficit_pos_of_lt m p hsum hlt).le))
private theorem sum_couplingKernel (hp : ∀ b, 0 ≤ p b) (hsum : ∑ b, m b = ∑ b, p b) (c : κ) : ∑ c',
    couplingKernel m p c c' = 1 := by
  classical
  unfold couplingKernel; by_cases hle : m c ≤ p c; · simp [hle]
  have hlt := not_le.1 hle; have hmc := (hp c).trans_lt hlt
  simp only [hle, ↓reduceIte, sum_add_distrib, sum_ite_eq', mem_univ, ← mul_sum, ← sum_div]
  rw [← couplingDeficit, div_self (couplingDeficit_pos_of_lt m p hsum hlt).ne', mul_one, ← add_div,
    add_sub_cancel, div_self hmc.ne']
private theorem couplingKernel_le_one (hp : ∀ b, 0 ≤ p b) (hsum : ∑ b, m b = ∑ b, p b) (c c' : κ) :
    couplingKernel m p c c' ≤ 1 := sum_couplingKernel m p hp hsum c ▸ single_le_sum (fun b _ ↦
    couplingKernel_nonneg m p hp hsum c b) (mem_univ c')
private theorem mul_couplingKernel_self (hp : ∀ b, 0 ≤ p b) (c : κ) : m c * couplingKernel m p c c
    = min (m c) (p c) := by
  classical
  unfold couplingKernel; by_cases hle : m c ≤ p c; · simp [hle]
  have hlt := not_le.1 hle; simp [hle, max_eq_right (sub_nonpos.2 hlt.le), min_eq_right hlt.le,
    mul_div_cancel₀ (p c) ((hp c).trans_lt hlt).ne']
private theorem sum_mul_couplingKernel (hp : ∀ b, 0 ≤ p b) (hsum : ∑ b, m b = ∑ b, p b) (c' : κ) :
    ∑ c, m c * couplingKernel m p c c' = p c' := by
  classical
  by_cases hD : couplingDeficit m p = 0
  · have hm_le (c : κ) : m c ≤ p c := by
      by_contra hlt; exact (couplingDeficit_pos_of_lt m p hsum (not_le.1 hlt)).ne' hD
    have hp_le : p c' - m c' ≤ 0 := (le_max_left _ 0).trans <| (single_le_sum (f := fun b ↦ max (p
      b - m b) 0) (fun _ _ ↦ le_max_right _ _) (mem_univ c')).trans_eq hD
    simp only [show ∀ c, m c * couplingKernel m p c c' = if c' = c then m c else 0 from fun c ↦ by
      simp [couplingKernel, hm_le c], sum_ite_eq, mem_univ, ↓reduceIte]; linarith [hm_le c']
  · have hterm (c : κ) : m c * couplingKernel m p c c' = (if c' = c then min (m c) (p c) else 0) +
        max (m c - p c) 0 * (max (p c' - m c') 0 / couplingDeficit m p) := by
      unfold couplingKernel; by_cases hle : m c ≤ p c
      · rw [ite_eq_left hle, min_eq_left hle, max_eq_right (sub_nonpos.2 hle), zero_mul, add_zero]
        split_ifs <;> ring
      · have hlt := not_le.1 hle; have hmc := ((hp c).trans_lt hlt).ne'
        rw [ite_eq_right hle, min_eq_right hlt.le, max_eq_left (sub_nonneg.2 hlt.le), mul_add, ←
          mul_assoc, mul_div_cancel₀ _ hmc]
        congr 1; split_ifs; exacts [mul_div_cancel₀ (p c) hmc, by ring]
    simp only [hterm, sum_add_distrib, sum_ite_eq, mem_univ, ↓reduceIte, ← sum_mul, ←
      couplingDeficit_eq_surplus m p hsum, mul_div_cancel₀ _ hD]
    rcases le_total (m c') (p c') with h | h
    · rw [min_eq_left h, max_eq_left (sub_nonneg.2 h)]; ring
    · rw [min_eq_right h, max_eq_right (sub_nonpos.2 h), add_zero]
end
/-- **Coupled low-discrepancy recoloring.** -/
theorem exists_coupled_recoloring_abs_card_filter_sub_le [DecidableEq κ] (S : Finset ι) (x₀ : ι →
    κ) {p : κ → ℝ} (hp : ∀ c, 0 ≤ p c) (hp1 : ∑ c, p c = 1) {I : Type*} [Fintype I] (T : I → Finset
    ι) (hT : ∀ i, T i ⊆ S) {a : ℝ} (ha : 0 < a) (h : 2 * (Fintype.card I + 1) * Fintype.card κ *
    exp (-2 * a ^ 2 / #S) < 1) : ∃ x : ι → κ, (∀ e ∉ S, x e = x₀ e) ∧ (#{e ∈ S | x e ≠ x₀ e} : ℝ) ≤
    (∑ c, |(#{e ∈ S | x₀ e = c} : ℝ) - p c * #S|) / 2 + Fintype.card κ * a ∧ ∀ i c', |(#{e ∈ T i |
    x e = c'} : ℝ) - p c' * #(T i)| ≤ Fintype.card κ * a + ∑ c, |(#{e ∈ T i | x₀ e = c} : ℝ) - (#{e
    ∈ S | x₀ e = c} : ℝ) / #S * #(T i)| := by
  have := Classical.decEq ι
  have hκ : 0 < Fintype.card κ := Fintype.card_pos_iff.2 (by by_contra! h0; simp at hp1)
  have hSpos : 0 < #S := Nat.pos_of_ne_zero fun hS0 ↦ h.not_ge <| by
    rw [hS0, Nat.cast_zero, div_zero, exp_zero, mul_one]
    nlinarith [Nat.one_le_cast (α := ℝ).2 hκ, Nat.cast_nonneg (α := ℝ) (Fintype.card I)]
  have hSposR : (0 : ℝ) < #S := Nat.cast_pos.2 hSpos; let Sc (c : κ) := {e ∈ S | x₀ e = c}
  let m (c : κ) : ℝ := #(Sc c); let P (c : κ) : ℝ := p c * #S
  have hP_nn (c : κ) : 0 ≤ P c := mul_nonneg (hp c) hSposR.le
  have hm_sum : ∑ c, m c = #S := by simp_rw [m, Sc, ← Nat.cast_sum,
    ← card_eq_sum_card_fiberwise (f := x₀) (t := univ) fun _ _ ↦ mem_univ _]
  have hmP_sum : ∑ c, m c = ∑ c, P c := (by rw [hm_sum, ← sum_mul, hp1, one_mul])
  let Topt (c : κ) : Option I → Finset ι | none => Sc c | some i => T i ∩ Sc c
  have hTopt_le (c : κ) : ∀ o, #(Topt c o) ≤ #S
    | none => card_le_card (filter_subset _ S)
    | some _ => card_le_card (inter_subset_right.trans (filter_subset _ S))
  choose y hy using fun c ↦ exists_forall_abs_card_filter_sub_mul_card_lt (couplingKernel_nonneg m
    P hP_nn hmP_sum c) (sum_couplingKernel m P hP_nn hmP_sum c) (Topt c) (hTopt_le c) ha
    (by simpa [Fintype.card_option, Nat.cast_add] using h)
  let x (e : ι) : κ := if e ∈ S then y (x₀ e) e else x₀ e
  refine ⟨x, fun e he ↦ ite_eq_right he, ?_, fun i c' ↦ ?_⟩
  · have hkeep : #{e ∈ S | x e = x₀ e} = ∑ c, #{e ∈ Sc c | y c e = c} := by
      rw [card_eq_sum_card_fiberwise (f := x₀) (t := univ) fun _ _ ↦ mem_univ _]
      refine sum_congr rfl fun c _ ↦ congrArg card (ext fun e ↦ ?_)
      simp only [mem_filter, Sc, x]; exact ⟨fun ⟨⟨he, hxe⟩, rfl⟩ ↦ ⟨⟨he, rfl⟩, by
        rwa [ite_eq_left he] at hxe⟩, fun ⟨⟨he, rfl⟩, hyc⟩ ↦ ⟨⟨he, by simp [he, hyc]⟩, rfl⟩⟩
    have hedits : (#{e ∈ S | x e ≠ x₀ e} : ℝ) = ∑ c, (m c - (#{e ∈ Sc c | y c e = c} : ℝ)) := by
      have hpart : (#{e ∈ S | x e = x₀ e} : ℝ) + #{e ∈ S | x e ≠ x₀ e} = #S := mod_cast
        card_filter_add_card_filter_not (s := S) fun e ↦ x e = x₀ e
      rw [show (#{e ∈ S | x e ≠ x₀ e} : ℝ) = #S - #{e ∈ S | x e = x₀ e}
        by linarith, hkeep, Nat.cast_sum, ← hm_sum, ← sum_sub_distrib]
    have hfiber (c : κ) : m c - (#{e ∈ Sc c | y c e = c} : ℝ) ≤ max (m c - P c) 0 + a := by
      have hnone := (abs_lt.1 (hy c none c)).1
      have hself : couplingKernel m P c c * #(Sc c) = min (m c) (P c) := by
        rw [mul_comm]; exact mul_couplingKernel_self m P hP_nn c
      rcases le_total (m c) (P c) with hle | hle <;> simp only [Topt] at hnone <;> linarith
        [min_eq_left hle, max_eq_right (sub_nonpos.2 hle), min_eq_right hle, max_eq_left
        (sub_nonneg.2 hle)]
    exact (hedits ▸ sum_le_sum fun c _ ↦ hfiber c).trans_eq (by
      rw [sum_add_distrib, sum_const, card_univ, nsmul_eq_mul, couplingDeficit_eq_half_sum_abs m P
        hmP_sum])
  · have hTi_Sc (c : κ) : T i ∩ Sc c = {e ∈ T i | x₀ e = c} := ext fun e ↦ by
      simp only [mem_inter, mem_filter, Sc]
      exact ⟨fun ⟨h1, _, h2⟩ ↦ ⟨h1, h2⟩, fun ⟨h1, h2⟩ ↦ ⟨h1, hT i h1, h2⟩⟩
    have hcount : (#{e ∈ T i | x e = c'} : ℝ) = ∑ c, (#{e ∈ T i ∩ Sc c | y c e = c'} : ℝ) := by
      rw [card_eq_sum_card_fiberwise (f := x₀) (t := univ) fun _ _ ↦ mem_univ _, Nat.cast_sum]
      refine sum_congr rfl fun c _ ↦ congrArg (Nat.cast ∘ card) (ext fun e ↦ ?_)
      simp only [mem_filter, mem_inter, Sc, x]
      exact ⟨fun ⟨⟨heT, hxe⟩, rfl⟩ ↦ ⟨⟨heT, hT i heT, rfl⟩,
        by rwa [ite_eq_left (hT i heT)] at hxe⟩, fun ⟨⟨heT, heS, rfl⟩, hyc⟩ ↦ ⟨⟨heT,
        by simp [heS, hyc]⟩, rfl⟩⟩
    have htarget : p c' * #(T i) = ∑ c, couplingKernel m P c c' * (m c / #S * #(T i)) := by
      rw [← mul_div_cancel_right₀ (p c') hSposR.ne', ← show P c' = p c' * #S from rfl, ←
        sum_mul_couplingKernel m P hP_nn hmP_sum c', div_mul_eq_mul_div, sum_mul, sum_div]
      exact sum_congr rfl fun c _ ↦ by ring
    rw [hcount, htarget, ← sum_sub_distrib]
    refine (abs_sum_le_sum_abs _ _).trans ((sum_le_sum (g := fun c ↦ a + |(#{e ∈ T i | x₀ e = c} :
      ℝ) - m c / #S * #(T i)|) fun c _ ↦ ?_).trans_eq
      (by rw [sum_add_distrib, sum_const, card_univ, nsmul_eq_mul]))
    rw [show (#{e ∈ T i ∩ Sc c | y c e = c'} : ℝ) - couplingKernel m P c c' * (m c / #S * #(T i)) =
      ((#{e ∈ T i ∩ Sc c | y c e = c'} : ℝ) - couplingKernel m P c c' * #(T i ∩ Sc c)) +
      couplingKernel m P c c' * ((#(T i ∩ Sc c) : ℝ) - m c / #S * #(T i)) by ring]
    refine (abs_add_le _ _).trans (add_le_add (hy c (some i) c').le ?_)
    rw [abs_mul, abs_of_nonneg (couplingKernel_nonneg m P hP_nn hmP_sum c c'), hTi_Sc c]
    exact mul_le_of_le_one_left (abs_nonneg _) (couplingKernel_le_one m P hP_nn hmP_sum c c')
end TauCeti
