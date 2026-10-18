/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Green.Polygonal.Basic
public import TauCeti.Analysis.Green.AbsolutelyContinuous
public import TauCeti.MeasureTheory.Function.AbsolutelyContinuous.PolygonalApproximation
import TauCeti.MeasureTheory.Function.AbsolutelyContinuous.Gluing

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
    {P Q : ℂ → ℝ}
    (hP : ContinuousOn P (γ '' uIcc a b)) (hQ : ContinuousOn Q (γ '' uIcc a b)) :
    (∫ t in a..b, circulationFun P Q γ t) =
      Finsupp.linearCombination ℤ (fun η : Arc ↦ curveIntegral (oneForm P Q) η.2.2)
        (BoundaryChain.polygon (γ ∘ s)) := by
  have hγ := AbsolutelyContinuousOnInterval.of_affine_subdivision hs ha hb hsegments
  have hab : a ≤ b := by rw [← ha, ← hb]; exact hs.monotone (Fin.zero_le _)
  have hmem (i : Fin (N + 1)) : s i ∈ Icc a b := by
    rw [← ha, ← hb]
    exact ⟨hs.monotone (Fin.zero_le _), hs.monotone (Fin.le_last _)⟩
  have hint := hγ.intervalIntegrable_circulationFun hP hQ
  let t : ℕ → ℝ := fun k ↦ s (Fin.ofNat (N + 1) k)
  have ht (i : Fin (N + 1)) : t i = s i := by simp [t]
  have hcast (i : Fin N) : t i = s i.castSucc := ht i.castSucc
  have hsucc (i : Fin N) : t (i + 1) = s i.succ := ht i.succ
  have ht0 : t 0 = a := (ht 0).trans ha
  have htN : t N = b := (ht (Fin.last N)).trans hb
  have hcell (i : Fin N) :
      IntervalIntegrable (circulationFun P Q γ) volume (t i) (t (i + 1)) := by
    rw [hcast i, hsucc i]
    apply hint.mono_set
    rw [uIcc_of_le hab]
    exact uIcc_subset_Icc (hmem i.castSucc) (hmem i.succ)
  have hsum := intervalIntegral.sum_integral_adjacent_intervals (n := N) (a := t) (by
    intro k hk
    simpa only [Fin.val_mk] using hcell ⟨k, hk⟩)
  rw [← Fin.sum_univ_eq_sum_range, ht0, htN] at hsum
  rw [← hsum, BoundaryChain.polygon_def, map_sum]
  simp only [BoundaryChain.ofPath_def, Finsupp.linearCombination_single, one_smul,
    Function.comp_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [hcast i, hsucc i]
  exact integral_circulationFun_eq_curveIntegral_segment (hs i.castSucc_lt_succ) (hsegments i) P Q


end TauCeti.Green
