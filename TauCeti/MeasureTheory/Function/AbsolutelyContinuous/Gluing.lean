/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Function.MetricDerivative.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Gluing absolutely continuous curves

Absolute continuity on adjacent intervals implies absolute continuity on their union in a
pseudometric space. This permits splitting and reassembling raw curves with either orientation,
and gluing finite subdivisions, including subdivisions into affine cells. In particular a
polygonal curve (`TauCeti.IsPolygonalOnInterval`) is absolutely continuous.
-/

public section

open MeasureTheory Set TauCeti

namespace AbsolutelyContinuousOnInterval

variable {X : Type*} [PseudoMetricSpace X] {γ : ℝ → X} {a b c : ℝ}

private theorem of_adjacent (h₁ : AbsolutelyContinuousOnInterval γ a c)
    (h₂ : AbsolutelyContinuousOnInterval γ c b) (hac : a ≤ c) (hcb : c ≤ b) :
    AbsolutelyContinuousOnInterval γ a b := by
  have hadd {s u : ℝ} (hsc : s ≤ c) (hcu : c ≤ u) :
      (∫⁻ r in Ioc s u, metricDerivative γ r) =
        (∫⁻ r in Ioc s c, metricDerivative γ r) +
          ∫⁻ r in Ioc c u, metricDerivative γ r := by
    rw [← Ioc_union_Ioc_eq_Ioc hsc hcu]
    exact lintegral_union measurableSet_Ioc (Ioc_disjoint_Ioc_of_le le_rfl)
  apply absolutelyContinuousOnInterval_of_edist_le_lintegral
  · rw [uIoc_of_le (hac.trans hcb), hadd hac hcb]
    exact (ENNReal.add_lt_top.mpr ⟨by simpa [uIoc_of_le hac] using
      h₁.lintegral_metricDerivative_lt_top, by simpa [uIoc_of_le hcb] using
      h₂.lintegral_metricDerivative_lt_top⟩).ne
  · intro s hs u hu
    wlog hsu : s ≤ u generalizing s u
    · simpa only [edist_comm, uIoc_comm] using this u hu s hs (le_of_not_ge hsu)
    rw [uIcc_of_le (hac.trans hcb)] at hs hu
    by_cases huc : u ≤ c
    · exact h₁.edist_le_lintegral_metricDerivative
        (by simpa [uIcc_of_le hac] using And.intro hs.1 (hsu.trans huc))
        (by simpa [uIcc_of_le hac] using And.intro hu.1 huc)
    by_cases hcs : c ≤ s
    · exact h₂.edist_le_lintegral_metricDerivative
        (by simpa [uIcc_of_le hcb] using And.intro hcs hs.2)
        (by simpa [uIcc_of_le hcb] using And.intro (hcs.trans hsu) hu.2)
    have hsc : s ≤ c := (le_of_not_ge hcs)
    have hcu : c ≤ u := (le_of_not_ge huc)
    rw [uIoc_of_le hsu, hadd hsc hcu]
    refine (edist_triangle (γ s) (γ c) (γ u)).trans (add_le_add ?_ ?_)
    · have hs₁ : s ∈ uIcc a c := by simpa [uIcc_of_le hac] using And.intro hs.1 hsc
      have h := h₁.edist_le_lintegral_metricDerivative (s := s) (u := c) hs₁ right_mem_uIcc
      rwa [uIoc_of_le hsc] at h
    · have hu₂ : u ∈ uIcc c b := by simpa [uIcc_of_le hcb] using And.intro hcu hu.2
      have h := h₂.edist_le_lintegral_metricDerivative (s := c) (u := u) left_mem_uIcc hu₂
      rwa [uIoc_of_le hcu] at h

/-- Absolute continuity on two intervals sharing an endpoint implies absolute continuity
between their other endpoints, in either orientation. -/
theorem trans (h₁ : AbsolutelyContinuousOnInterval γ a c)
    (h₂ : AbsolutelyContinuousOnInterval γ c b) :
    AbsolutelyContinuousOnInterval γ a b := by
  wlog hab : a ≤ b generalizing a b c
  · exact (this h₂.symm h₁.symm (le_of_not_ge hab)).symm
  by_cases hac : a ≤ c
  · by_cases hcb : c ≤ b
    · exact of_adjacent h₁ h₂ hac hcb
    · apply h₁.mono
      rw [uIcc_of_le hab, uIcc_of_le hac]
      exact Icc_subset_Icc le_rfl (le_of_not_ge hcb)
  · apply h₂.mono
    rw [uIcc_of_le hab, uIcc_of_le ((le_of_not_ge hac).trans hab)]
    exact Icc_subset_Icc (le_of_not_ge hac) le_rfl

/-- Absolute continuity can be checked on the two pieces of a parameter interval. -/
theorem _root_.TauCeti.absolutelyContinuousOnInterval_iff_and (hc : c ∈ uIcc a b) :
    AbsolutelyContinuousOnInterval γ a b ↔
      AbsolutelyContinuousOnInterval γ a c ∧ AbsolutelyContinuousOnInterval γ c b :=
  ⟨fun h ↦ ⟨h.mono (uIcc_subset_uIcc left_mem_uIcc hc),
    h.mono (uIcc_subset_uIcc hc right_mem_uIcc)⟩, fun h ↦ h.1.trans h.2⟩

/-- Glue absolute continuity on all successive cells of a finite subdivision. -/
theorem of_subdivision {N : ℕ} {s : Fin (N + 1) → ℝ}
    (h : ∀ i : Fin N, AbsolutelyContinuousOnInterval γ (s i.castSucc) (s i.succ)) :
    AbsolutelyContinuousOnInterval γ (s 0) (s (Fin.last N)) := by
  induction N with
  | zero => exact .refl γ _
  | succ N ih =>
    have hprev : ∀ i : Fin N, AbsolutelyContinuousOnInterval γ
        (s i.castSucc.castSucc) (s i.succ.castSucc) := by
      intro i
      simpa only [Fin.castSucc_succ] using h i.castSucc
    have hp : AbsolutelyContinuousOnInterval γ (s 0) (s (Fin.last N).castSucc) :=
      ih (s := fun j ↦ s j.castSucc) hprev
    exact hp.trans (h (Fin.last N))

/-- A finite increasing subdivision with affine interpolation on every cell gives an absolutely
continuous curve. The subdivision may have no cells. -/
theorem of_affine_subdivision {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} {a b : ℝ} {N : ℕ} {s : Fin (N + 1) → ℝ}
    (hs : StrictMono s) (ha : s 0 = a) (hb : s (Fin.last N) = b)
    (hsegments : ∀ i : Fin N, ∀ t ∈ Set.Icc (s i.castSucc) (s i.succ),
      f t = f (s i.castSucc) +
        ((t - s i.castSucc) / (s i.succ - s i.castSucc)) •
          (f (s i.succ) - f (s i.castSucc))) :
    AbsolutelyContinuousOnInterval f a b := by
  have hedge (i : Fin N) :
      AbsolutelyContinuousOnInterval f (s i.castSucc) (s i.succ) := by
    have hc : ContDiffOn ℝ 1
        (fun t : ℝ ↦ f (s i.castSucc) +
          ((t - s i.castSucc) / (s i.succ - s i.castSucc)) •
            (f (s i.succ) - f (s i.castSucc)))
        (Set.uIcc (s i.castSucc) (s i.succ)) := by fun_prop
    apply hc.absolutelyContinuousOnInterval.congr
    intro t ht
    rw [Set.uIcc_of_le (hs i.castSucc_lt_succ).le] at ht
    exact (hsegments i t ht).symm
  simpa only [ha, hb] using of_subdivision hedge

end AbsolutelyContinuousOnInterval

/-- A raw curve is polygonal on an interval if a finite increasing subdivision expresses it as
the affine interpolation of its successive vertex values on every closed cell. -/
@[expose] def TauCeti.IsPolygonalOnInterval {F : Type*} [AddCommGroup F] [Module ℝ F]
    (f : ℝ → F) (a b : ℝ) : Prop :=
  ∃ N : ℕ, 0 < N ∧ ∃ s : Fin (N + 1) → ℝ,
    StrictMono s ∧ s 0 = a ∧ s (Fin.last N) = b ∧
      ∀ i : Fin N, ∀ t ∈ Icc (s i.castSucc) (s i.succ),
        f t = f (s i.castSucc) +
          ((t - s i.castSucc) / (s i.succ - s i.castSucc)) •
            (f (s i.succ) - f (s i.castSucc))

/-- A polygonal curve is absolutely continuous: its finitely many affine cells glue together. -/
theorem TauCeti.IsPolygonalOnInterval.absolutelyContinuousOnInterval {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {f : ℝ → E} {a b : ℝ}
    (h : TauCeti.IsPolygonalOnInterval f a b) : AbsolutelyContinuousOnInterval f a b := by
  obtain ⟨N, _, s, hs, ha, hb, hsegments⟩ := h
  exact AbsolutelyContinuousOnInterval.of_affine_subdivision hs ha hb hsegments
