/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Green.Polygonal.Basic
public import TauCeti.Algebra.BigOperators.Fin
public import TauCeti.Analysis.Green.AbsolutelyContinuous
public import TauCeti.MeasureTheory.Function.AbsolutelyContinuous.PolygonalApproximation

/-!
# Circulation of raw polygonal curves

Affine interpolation on each closed subdivision interval identifies the actual raw circulation
with the curve integral of its straight segment. Summing over the finite subdivision gives
the integer-chain integral of the successive vertices, without replacing the raw curve or
assuming any equality of integrals as input.
-/

public section

noncomputable section

open MeasureTheory Set

namespace TauCeti.Green

/-- A raw curve that agrees with affine interpolation on a nondegenerate interval has the
same circulation as the corresponding existing straight path. -/
theorem integral_circulationFun_eq_curveIntegral_segment {γ : ℝ → ℂ} {a b : ℝ}
    {p q : ℂ} (hab : a < b)
    (hγ : ∀ t ∈ Icc a b, γ t = p + ((t - a) / (b - a)) • (q - p))
    (P Q : ℂ → ℝ) :
    (∫ t in a..b, circulationFun P Q γ t) =
      curveIntegral (oneForm P Q) (Path.segment p q) := by
  let k : ℝ → ℝ := fun t ↦ oneForm P Q (AffineMap.lineMap p q t) (q - p)
  have heq : (∫ t in a..b, circulationFun P Q γ t) =
      ∫ t in a..b, (b - a)⁻¹ • k ((t - a) / (b - a)) := by
    apply intervalIntegral.integral_congr_ae_restrict
    rw [uIoc_of_le hab.le, ← restrict_Ioo_eq_restrict_Ioc]
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    have hd : HasDerivAt γ ((b - a)⁻¹ • (q - p)) t := by
      have h := ((((hasDerivAt_id t).sub_const a).div_const (b - a)).smul_const
        (q - p)).const_add p
      have h' : HasDerivAt (fun u ↦ p + ((u - a) / (b - a)) • (q - p))
          ((b - a)⁻¹ • (q - p)) t := by simpa only [one_div, id_eq] using h
      apply h'.congr_of_eventuallyEq
      filter_upwards [Icc_mem_nhds ht.1 ht.2] with u hu
      exact hγ u hu
    rw [circulationFun_eq_oneForm, hd.deriv, map_smul, hγ t (Ioo_subset_Icc_self ht)]
    congr 2
    rw [AffineMap.lineMap_apply_module']
    congr 1
    exact add_comm _ _
  rw [heq, intervalIntegral.integral_smul]
  have hs : (∫ t in a..b, k ((t - a) / (b - a))) =
      ∫ t in (0 : ℝ)..(b - a), k (t / (b - a)) := by
    simpa only [sub_self] using
      intervalIntegral.integral_comp_sub_right (a := a) (b := b)
        (fun t ↦ k (t / (b - a))) a
  rw [hs, intervalIntegral.inv_smul_integral_comp_div]
  simpa only [zero_div, div_self (sub_ne_zero.mpr hab.ne'), k] using
    (curveIntegral_segment (oneForm P Q) p q).symm

/-- The circulation of an absolutely continuous raw polygonal curve is the actual finite
integer-chain sum of its segment curve integrals. The partition may be nonuniform. -/
theorem integral_circulationFun_eq_polygon {γ : ℝ → ℂ} {a b : ℝ} {N : ℕ}
    {s : Fin (N + 1) → ℝ} (hs : StrictMono s) (ha : s 0 = a) (hb : s (Fin.last N) = b)
    (hsegments : ∀ i : Fin N, ∀ t ∈ Icc (s i.castSucc) (s i.succ),
      γ t = γ (s i.castSucc) + ((t - s i.castSucc) / (s i.succ - s i.castSucc)) •
        (γ (s i.succ) - γ (s i.castSucc)))
    (hγ : AbsolutelyContinuousOnInterval γ a b) {P Q : ℂ → ℝ}
    (hP : ContinuousOn P (γ '' uIcc a b)) (hQ : ContinuousOn Q (γ '' uIcc a b)) :
    (∫ t in a..b, circulationFun P Q γ t) =
      Finsupp.linearCombination ℤ (fun η : Arc ↦ curveIntegral (oneForm P Q) η.2.2)
        (BoundaryChain.polygon (γ ∘ s)) := by
  have hab : a ≤ b := by rw [← ha, ← hb]; exact hs.monotone (Fin.zero_le _)
  have hmem (i : Fin (N + 1)) : s i ∈ Icc a b := by
    rw [← ha, ← hb]
    exact ⟨hs.monotone (Fin.zero_le _), hs.monotone (Fin.le_last _)⟩
  have hint := intervalIntegrable_circulationFun hγ hP hQ
  let F : Fin (N + 1) → ℝ := fun i ↦ ∫ t in a..s i, circulationFun P Q γ t
  have hstep (i : Fin N) :
      curveIntegral (oneForm P Q) (Path.segment (γ (s i.castSucc)) (γ (s i.succ))) =
        F i.succ - F i.castSucc := by
    rw [← integral_circulationFun_eq_curveIntegral_segment (hs i.castSucc_lt_succ)
      (hsegments i) P Q]
    have hleft := hint.mono_set (show uIcc a (s i.castSucc) ⊆ uIcc a b by
      rw [uIcc_of_le hab]
      exact uIcc_subset_Icc (left_mem_Icc.mpr hab) (hmem i.castSucc))
    have hcell := hint.mono_set (show uIcc (s i.castSucc) (s i.succ) ⊆ uIcc a b by
      rw [uIcc_of_le hab]
      exact uIcc_subset_Icc (hmem i.castSucc) (hmem i.succ))
    exact eq_sub_iff_add_eq.mpr (by
      simpa only [F, add_comm] using
        intervalIntegral.integral_add_adjacent_intervals hleft hcell)
  rw [BoundaryChain.polygon_def, map_sum]
  simp only [BoundaryChain.ofPath_def, Finsupp.linearCombination_single, one_smul,
    Function.comp_apply, hstep, Fin.sum_sub_succ]
  simp [F, ha, hb]


end TauCeti.Green
