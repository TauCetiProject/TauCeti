/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Green.Approximation
public import TauCeti.Analysis.Green.WindingWeight.FiniteSum

/-!
# Simultaneous polygonal approximation of finite curve families

Finite families of closed AC curves admit endpoint-preserving polygonal approximations with
uniform and derivative `L¹` convergence on each curve's own parameter interval. The total
integer-weighted winding weight converges in `L¹`. All traces eventually remain in a common
open field domain and the total index still vanishes outside it, even when individual indices
cancel in holes.
-/

public section

noncomputable section

open MeasureTheory Set Filter
open scoped Topology

namespace TauCeti.Green

variable {ι : Type*} {s : Finset ι} {γ : ι → ℝ → ℂ} {γn : ℕ → ι → ℝ → ℂ}
  {a b : ι → ℝ} {w : ι → ℤ} {U : Set ℂ}

/-- Joint uniform approximation preserves every off-domain index eventually, so it preserves
the total integer-weighted index without any individual index-vanishing assumption. -/
theorem eventually_sum_windingNumber_eq_on_compl_of_tendstoUniformlyOn
    (hγ : ∀ i ∈ s, AbsolutelyContinuousOnInterval (γ i) (a i) (b i))
    (hγn : ∀ n, ∀ i ∈ s, AbsolutelyContinuousOnInterval (γn n i) (a i) (b i))
    (hclosed : ∀ i ∈ s, γ i (a i) = γ i (b i))
    (hclosedn : ∀ n, ∀ i ∈ s, γn n i (a i) = γn n i (b i))
    (hconv : ∀ i ∈ s, TendstoUniformlyOn (fun n ↦ γn n i) (γ i) atTop (uIcc (a i) (b i)))
    (hU : IsOpen U) (htrace : ∀ i ∈ s, γ i '' uIcc (a i) (b i) ⊆ U) :
    ∀ᶠ n in atTop, (∀ i ∈ s, γn n i '' uIcc (a i) (b i) ⊆ U) ∧
      ∀ z ∉ U, (∑ i ∈ s, (w i : ℂ) * Contour.windingNumber (γn n i) (a i) (b i) z) =
        ∑ i ∈ s, (w i : ℂ) * Contour.windingNumber (γ i) (a i) (b i) z := by
  have he := (Filter.eventually_all_finset s).mpr fun i hi ↦
    eventually_windingNumber_eq_on_compl_of_tendstoUniformlyOn (hγ i hi)
      (fun n ↦ hγn n i hi) (hclosed i hi) (fun n ↦ hclosedn n i hi)
      (hconv i hi) hU (htrace i hi)
  filter_upwards [he] with n hn
  refine ⟨fun i hi ↦ (hn i hi).1, fun z hz ↦ ?_⟩
  exact Finset.sum_congr rfl fun i hi ↦ congrArg ((w i : ℂ) * ·) ((hn i hi).2 z hz)

/-- Per-curve uniform and derivative `L¹` convergence imply `L¹` convergence of the actual total
real winding weight. No uniform bound on the indices is assumed. -/
theorem tendsto_integral_abs_sum_windingWeight_sub
    (hab : ∀ i ∈ s, a i ≤ b i)
    (hγ : ∀ i ∈ s, AbsolutelyContinuousOnInterval (γ i) (a i) (b i))
    (hγn : ∀ n, ∀ i ∈ s, AbsolutelyContinuousOnInterval (γn n i) (a i) (b i))
    (hclosed : ∀ i ∈ s, γ i (a i) = γ i (b i))
    (hclosedn : ∀ n, ∀ i ∈ s, γn n i (a i) = γn n i (b i))
    (hconv : ∀ i ∈ s, TendstoUniformlyOn (fun n ↦ γn n i) (γ i) atTop (Icc (a i) (b i)))
    (hdconv : ∀ i ∈ s, Tendsto
      (fun n ↦ ∫ t in a i..b i, ‖deriv (γn n i) t - deriv (γ i) t‖) atTop (nhds 0)) :
    Tendsto (fun n ↦ ∫ z : ℂ,
      |(∑ i ∈ s, (w i : ℝ) * windingWeight (γn n i) (a i) (b i) z) -
        ∑ i ∈ s, (w i : ℝ) * windingWeight (γ i) (a i) (b i) z|) atTop (nhds 0) := by
  have hd (n : ℕ) (i : ι) (hi : i ∈ s) :
      Integrable (fun z ↦ |windingWeight (γn n i) (a i) (b i) z -
        windingWeight (γ i) (a i) (b i) z|) := by
    simpa only [Real.norm_eq_abs, Pi.sub_apply] using
      ((integrable_windingWeight (hγn n i hi) (hclosedn n i hi)).sub
        (integrable_windingWeight (hγ i hi) (hclosed i hi))).norm
  have hlim : Tendsto
      (fun n ↦ ∑ i ∈ s, |(w i : ℝ)| *
        ∫ z : ℂ, |windingWeight (γn n i) (a i) (b i) z - windingWeight (γ i) (a i) (b i) z|)
      atTop (nhds 0) := by
    simpa only [mul_zero, Finset.sum_const_zero] using tendsto_finsetSum s (fun i hi ↦
      Tendsto.const_mul |(w i : ℝ)|
        (tendsto_integral_abs_windingWeight_sub (hab i hi) (fun n ↦ hγn n i hi)
          (hγ i hi) (fun n ↦ hclosedn n i hi) (hclosed i hi) (hconv i hi) (hdconv i hi)))
  apply squeeze_zero (fun n ↦ integral_nonneg fun _ ↦ abs_nonneg _) (fun n ↦ ?_) hlim
  have htotal : Integrable (fun z ↦
      |(∑ i ∈ s, (w i : ℝ) * windingWeight (γn n i) (a i) (b i) z) -
        ∑ i ∈ s, (w i : ℝ) * windingWeight (γ i) (a i) (b i) z|) := by
    simpa only [Real.norm_eq_abs, Pi.sub_apply] using
      ((integrable_sum_windingWeight (fun i hi ↦ hγn n i hi) (fun i hi ↦ hclosedn n i hi)).sub
        (integrable_sum_windingWeight hγ hclosed)).norm
  calc
    _ ≤ ∫ z : ℂ, ∑ i ∈ s, |(w i : ℝ)| *
        |windingWeight (γn n i) (a i) (b i) z - windingWeight (γ i) (a i) (b i) z| := by
      apply integral_mono htotal (integrable_finsetSum _ fun i hi ↦ (hd n i hi).const_mul _)
      intro z
      dsimp only
      rw [← Finset.sum_sub_distrib]
      have heq : ∀ i, (w i : ℝ) * windingWeight (γn n i) (a i) (b i) z -
          (w i : ℝ) * windingWeight (γ i) (a i) (b i) z =
          (w i : ℝ) * (windingWeight (γn n i) (a i) (b i) z -
            windingWeight (γ i) (a i) (b i) z) := fun i ↦ (mul_sub _ _ _).symm
      simp_rw [heq]
      simpa only [abs_mul] using Finset.abs_sum_le_sum_abs
        (f := fun i ↦ (w i : ℝ) * (windingWeight (γn n i) (a i) (b i) z -
          windingWeight (γ i) (a i) (b i) z)) s
    _ = _ := by
      rw [integral_finsetSum s (fun i hi ↦ (hd n i hi).const_mul _)]
      simp only [integral_const_mul]

/-- Closed AC curves admit simultaneous polygonal approximations preserving their own endpoints,
all three analytic convergences, and total-index vanishing outside a common field domain.
Individual indices may be nonzero outside that domain. -/
theorem exists_polygonal_approximation_winding_sum
    (hab : ∀ i ∈ s, a i < b i)
    (hγ : ∀ i ∈ s, AbsolutelyContinuousOnInterval (γ i) (a i) (b i))
    (hclosed : ∀ i ∈ s, γ i (a i) = γ i (b i))
    (hU : IsOpen U) (htrace : ∀ i ∈ s, γ i '' uIcc (a i) (b i) ⊆ U)
    (hindex : ∀ z ∉ U,
      ∑ i ∈ s, (w i : ℂ) * Contour.windingNumber (γ i) (a i) (b i) z = 0) :
    ∃ γn : ℕ → ι → ℝ → ℂ,
      (∀ n, ∀ i ∈ s, IsPolygonalOnInterval (γn n i) (a i) (b i) ∧
        AbsolutelyContinuousOnInterval (γn n i) (a i) (b i) ∧
        γn n i (a i) = γ i (a i) ∧ γn n i (b i) = γ i (b i) ∧
        γn n i (a i) = γn n i (b i)) ∧
      (∀ i ∈ s, TendstoUniformlyOn (fun n ↦ γn n i) (γ i) atTop (Icc (a i) (b i))) ∧
      (∀ i ∈ s, Tendsto (fun n ↦ ∫ t in a i..b i, ‖deriv (γn n i) t - deriv (γ i) t‖)
        atTop (nhds 0)) ∧
      Tendsto (fun n ↦ ∫ z : ℂ,
        |(∑ i ∈ s, (w i : ℝ) * windingWeight (γn n i) (a i) (b i) z) -
          ∑ i ∈ s, (w i : ℝ) * windingWeight (γ i) (a i) (b i) z|) atTop (nhds 0) ∧
      ∀ᶠ n in atTop, (∀ i ∈ s, γn n i '' uIcc (a i) (b i) ⊆ U) ∧
        ∀ z ∉ U, ∑ i ∈ s, (w i : ℂ) * Contour.windingNumber (γn n i) (a i) (b i) z = 0 := by
  classical
  have hex (i : ι) : ∃ f : ℕ → ℝ → ℂ, ∀ _hi : i ∈ s,
      (∀ n, IsPolygonalOnInterval (f n) (a i) (b i) ∧
        AbsolutelyContinuousOnInterval (f n) (a i) (b i) ∧
        f n (a i) = γ i (a i) ∧ f n (b i) = γ i (b i)) ∧
      TendstoUniformlyOn f (γ i) atTop (Icc (a i) (b i)) ∧
      Tendsto (fun n ↦ ∫ t in a i..b i, ‖deriv (f n) t - deriv (γ i) t‖) atTop (nhds 0) := by
    by_cases hi : i ∈ s
    · obtain ⟨f, hf⟩ := (hγ i hi).exists_polygonal_approximation (hab i hi)
      exact ⟨f, fun _ ↦ hf⟩
    · exact ⟨fun _ ↦ γ i, fun h ↦ False.elim (hi h)⟩
  choose f hf using hex
  let γn : ℕ → ι → ℝ → ℂ := fun n i ↦ f i n
  have hAC (n) (i) (hi : i ∈ s) : AbsolutelyContinuousOnInterval (γn n i) (a i) (b i) :=
    ((hf i hi).1 n).2.1
  have hcl (n) (i) (hi : i ∈ s) : γn n i (a i) = γn n i (b i) :=
    ((hf i hi).1 n).2.2.1.trans ((hclosed i hi).trans ((hf i hi).1 n).2.2.2.symm)
  have hu (i) (hi : i ∈ s) : TendstoUniformlyOn (fun n ↦ γn n i) (γ i) atTop (Icc (a i) (b i)) :=
    (hf i hi).2.1
  have hd (i) (hi : i ∈ s) := (hf i hi).2.2
  refine ⟨γn, fun n i hi ↦ ⟨((hf i hi).1 n).1, hAC n i hi,
    ((hf i hi).1 n).2.2.1, ((hf i hi).1 n).2.2.2, hcl n i hi⟩, hu, hd,
    tendsto_integral_abs_sum_windingWeight_sub (fun i hi ↦ (hab i hi).le)
      hγ hAC hclosed hcl hu hd, ?_⟩
  have hu' (i) (hi : i ∈ s) :
      TendstoUniformlyOn (fun n ↦ γn n i) (γ i) atTop (uIcc (a i) (b i)) := by
    simpa only [uIcc_of_le (hab i hi).le] using hu i hi
  filter_upwards [eventually_sum_windingNumber_eq_on_compl_of_tendstoUniformlyOn
    hγ hAC hclosed hcl hu' hU htrace] with n hn
  exact ⟨hn.1, fun z hz ↦ (hn.2 z hz).trans (hindex z hz)⟩

end TauCeti.Green
