/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.OptimalTransport.Duality.Attainment

/-!
# Bounded-Lipschitz Kantorovich–Rubinstein duality

For probability measures on a Polish metric space and `R ≥ 0`, transport with the bounded cost
`min (dist x y) (2 * R)` equals the supremum of differences of expectations over real functions
that are `1`-Lipschitz and bounded in absolute value by `R`. The supremum is attained. In
particular, `R = 1` gives the bounded-Lipschitz (Fortet–Mourier) convention with both the
Lipschitz constant and the supremum norm at most one. The corresponding primal cap is **two**.
No moment assumption is needed, because every test function and the cost are bounded.

The proof uses the existing dual-attainment theorem for bounded continuous costs. A conjugate
potential is Lipschitz and has oscillation at most `2 * R`; centering its range gives a test
function bounded by `R`. The module exposes weak duality, an attained maximum, and the exact
supremum formulas, with signed and absolute differences of expectations.

## References

* C. Villani, *Optimal Transport: Old and New*, Springer, 2009, Particular Case 5.16,
  for Kantorovich–Rubinstein duality. Here the ground distance is truncated at `2 * R`.
-/

public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace TauCeti

variable {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
  {μ ν : Measure X} {R : ℝ}

/-- Bounded-Lipschitz weak duality for the truncated distance cost. The bound `R` on each
potential produces the cap `2 * R` on the cost. -/
theorem ofReal_integral_sub_integral_le_transportCost_truncated_dist
    [OpensMeasurableSpace X] [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {f : X → ℝ} (hf : LipschitzWith 1 f) (hfb : ∀ x, ‖f x‖ ≤ R) :
    ENNReal.ofReal (∫ x, f x ∂μ - ∫ x, f x ∂ν) ≤
      transportCost (fun z : X × X ↦ ENNReal.ofReal (min (dist z.1 z.2) (2 * R))) μ ν := by
  have hi (ρ : Measure X) [IsFiniteMeasure ρ] : Integrable f ρ :=
    .of_bound hf.continuous.aestronglyMeasurable R (ae_of_all _ hfb)
  have hfeas : DualFeasible
      (fun z : X × X ↦ ENNReal.ofReal (min (dist z.1 z.2) (2 * R))) f (fun y ↦ -f y) := by
    refine dualFeasible_iff_ofReal_add_le.2 fun x y ↦ ENNReal.ofReal_le_ofReal ?_
    have hdist := hf.le_add_mul x y
    have hx := (abs_le.1 (hfb x)).2
    have hy := (abs_le.1 (hfb y)).1
    simp only [NNReal.coe_one, one_mul] at hdist
    exact le_min (by linarith) (by linarith)
  simpa only [kantorovichDualValue_def, integral_neg, sub_eq_add_neg] using
    hfeas.ofReal_kantorovichDualValue_le_transportCost (hi μ) (hi ν).neg

omit [MeasurableSpace X] in
/-- Center the range of a conjugate potential of the truncated distance cost. -/
private theorem exists_boundedLipschitz_shift [Nonempty X] (hR : 0 ≤ R)
    {φ ψ : X → ℝ}
    (hfeas : ∀ x y, φ x + ψ y ≤ min (dist x y) (2 * R))
    (hφ : ∀ x, φ x = ⨅ y, (min (dist x y) (2 * R) - ψ y)) :
    ∃ (f : X → ℝ) (a : ℝ), LipschitzWith 1 f ∧ (∀ x, ‖f x‖ ≤ R) ∧
      ∀ x, f x = φ x - a := by
  have hbdd (x : X) : BddBelow (range fun y ↦ min (dist x y) (2 * R) - ψ y) :=
    ⟨φ x, forall_mem_range.2 fun y ↦ by linarith [hfeas x y]⟩
  have hosc (x x' : X) : φ x ≤ φ x' + 2 * R := by
    rw [← sub_le_iff_le_add, hφ x']
    refine le_ciInf fun y ↦ ?_
    have h := ciInf_le (hbdd x) y
    rw [← hφ x] at h
    linarith [min_le_right (dist x y) (2 * R),
      le_min (dist_nonneg (x := x') (y := y)) (by positivity : 0 ≤ 2 * R)]
  have hφlip : LipschitzWith 1 φ := LipschitzWith.of_le_add fun x x' ↦ by
    rw [← sub_le_iff_le_add, hφ x']
    refine le_ciInf fun y ↦ ?_
    have h := ciInf_le (hbdd x) y
    rw [← hφ x] at h
    have hlip := ((LipschitzWith.dist_left y).min_const (2 * R)).le_add_mul x x'
    simp only [NNReal.coe_one, one_mul] at hlip
    linarith
  obtain ⟨x₀⟩ := ‹Nonempty X›
  have hφbdd : BddBelow (range φ) :=
    ⟨φ x₀ - 2 * R, forall_mem_range.2 fun x ↦ by linarith [hosc x₀ x]⟩
  let m : ℝ := ⨅ x, φ x
  have hm (x : X) : m ≤ φ x := ciInf_le hφbdd x
  have hupper (x : X) : φ x ≤ m + 2 * R := by
    rw [← sub_le_iff_le_add]
    exact le_ciInf fun y ↦ by linarith [hosc x y]
  let f : X → ℝ := fun x ↦ φ x - (m + R)
  have hflip : LipschitzWith 1 f := LipschitzWith.of_le_add fun x y ↦ by
    have h := hφlip.le_add_mul x y
    simp only [NNReal.coe_one, one_mul] at h
    dsimp only [f]
    linarith
  refine ⟨f, m + R, hflip, fun x ↦ ?_, fun _ ↦ rfl⟩
  rw [Real.norm_eq_abs, abs_le]
  dsimp only [f]
  constructor <;> linarith [hm x, hupper x]

section Polish

variable [PolishSpace X] [BorelSpace X] [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

/-- Transport with truncated distance admits a maximizing `1`-Lipschitz test function bounded
by half the cap. This holds for every pair of probability measures, including laws with infinite
first moment and the zero-cap case. -/
theorem exists_lipschitzWith_norm_le_integral_sub_integral_eq_transportCost_truncated_dist
    (hR : 0 ≤ R) :
    ∃ f : X → ℝ, LipschitzWith 1 f ∧ (∀ x, ‖f x‖ ≤ R) ∧
      ENNReal.ofReal (∫ x, f x ∂μ - ∫ x, f x ∂ν) =
        transportCost (fun z : X × X ↦ ENNReal.ofReal (min (dist z.1 z.2) (2 * R))) μ ν := by
  have : Nonempty X := μ.nonempty_of_neZero
  let c : X × X → ℝ := fun z ↦ min (dist z.1 z.2) (2 * R)
  have hc : Continuous c := continuous_dist.min continuous_const
  have hc0 : ∀ z, 0 ≤ c z := fun z ↦ le_min dist_nonneg (by positivity)
  obtain ⟨π, φ, ψ, hcert, hφ, -⟩ := exists_isDualCertificate_of_continuous
    (μ := μ) (ν := ν) hc hc0 ⟨2 * R, forall_mem_range.2 fun _ ↦ min_le_right _ _⟩
  have hfeas := (dualFeasible_ofReal_iff hc0 φ ψ).1 hcert.dualFeasible
  obtain ⟨f, a, hf, hfb, hshift⟩ := exists_boundedLipschitz_shift hR hfeas hφ
  -- The shift makes the potential bounded, hence integrable against either marginal.
  have hfi (ρ : Measure X) [IsFiniteMeasure ρ] : Integrable f ρ :=
    .of_bound hf.continuous.aestronglyMeasurable R (ae_of_all _ hfb)
  have hφν : Integrable φ ν := by
    convert (hfi ν).add (integrable_const a) using 1
    ext x
    simp [hshift]
  have hψ : ∀ y, ψ y ≤ -φ y := fun y ↦ by
    have h := hfeas y y
    have hcy : c (y, y) = 0 := by simp [c, hR]
    rw [hcy] at h
    linarith
  -- Replacing the second potential by `-φ` improves the dual value.
  have hvalue : kantorovichDualValue μ ν φ ψ ≤ ∫ x, φ x ∂μ - ∫ x, φ x ∂ν := by
    have h := integral_mono hcert.integrable_right hφν.neg hψ
    simp only [Pi.neg_apply, integral_neg] at h
    rw [kantorovichDualValue_def]
    linarith
  have hint : ∫ x, f x ∂μ - ∫ x, f x ∂ν = ∫ x, φ x ∂μ - ∫ x, φ x ∂ν := by
    simp only [hshift, integral_sub hcert.integrable_left (integrable_const _),
      integral_sub hφν (integrable_const _), integral_const, probReal_univ, one_smul,
      sub_sub_sub_cancel_right]
  refine ⟨f, hf, hfb, le_antisymm
    (ofReal_integral_sub_integral_le_transportCost_truncated_dist hf hfb) ?_⟩
  rw [hint, hcert.transportCost_eq]
  exact ENNReal.ofReal_le_ofReal hvalue

/-- **Bounded-Lipschitz Kantorovich–Rubinstein duality with attainment.** The cost capped at
`2 * R` is the greatest difference of expectations of a `1`-Lipschitz function bounded by `R`.
Both constraints are separate; this is the maximum-norm convention, not their sum. -/
theorem isGreatest_ofReal_integral_sub_integral_boundedLipschitz (hR : 0 ≤ R) :
    IsGreatest {r : ℝ≥0∞ | ∃ f : X → ℝ, LipschitzWith 1 f ∧ (∀ x, ‖f x‖ ≤ R) ∧
      ENNReal.ofReal (∫ x, f x ∂μ - ∫ x, f x ∂ν) = r}
      (transportCost (fun z : X × X ↦ ENNReal.ofReal (min (dist z.1 z.2) (2 * R))) μ ν) := by
  refine ⟨exists_lipschitzWith_norm_le_integral_sub_integral_eq_transportCost_truncated_dist hR,
    ?_⟩
  rintro r ⟨f, hf, hfb, rfl⟩
  exact ofReal_integral_sub_integral_le_transportCost_truncated_dist hf hfb

/-- **Bounded-Lipschitz duality in supremum form.** A uniform bound `R` on the test functions
corresponds to truncation of the ground distance at `2 * R`. -/
theorem transportCost_truncated_dist_eq_iSup (hR : 0 ≤ R) :
    transportCost (fun z : X × X ↦ ENNReal.ofReal (min (dist z.1 z.2) (2 * R))) μ ν =
      ⨆ (f : X → ℝ) (_ : LipschitzWith 1 f) (_ : ∀ x, ‖f x‖ ≤ R),
        ENNReal.ofReal (∫ x, f x ∂μ - ∫ x, f x ∂ν) := by
  obtain ⟨f, hf, hfb, heq⟩ :=
    exists_lipschitzWith_norm_le_integral_sub_integral_eq_transportCost_truncated_dist
      (μ := μ) (ν := ν) hR
  refine le_antisymm ?_ (iSup_le fun g ↦ iSup_le fun hg ↦ iSup_le fun hgb ↦
    ofReal_integral_sub_integral_le_transportCost_truncated_dist hg hgb)
  rw [← heq]
  exact le_iSup_of_le f (le_iSup_of_le hf (le_iSup_of_le hfb le_rfl))

/-- The absolute-difference form of bounded-Lipschitz duality. The test class is closed under
negation, so its signed and absolute suprema coincide. -/
theorem transportCost_truncated_dist_eq_iSup_abs (hR : 0 ≤ R) :
    transportCost (fun z : X × X ↦ ENNReal.ofReal (min (dist z.1 z.2) (2 * R))) μ ν =
      ⨆ (f : X → ℝ) (_ : LipschitzWith 1 f) (_ : ∀ x, ‖f x‖ ≤ R),
        ENNReal.ofReal |∫ x, f x ∂μ - ∫ x, f x ∂ν| := by
  refine le_antisymm ?_ ?_
  · rw [transportCost_truncated_dist_eq_iSup hR]
    exact iSup_mono fun f ↦ iSup_mono fun _ ↦ iSup_mono fun _ ↦
      ENNReal.ofReal_le_ofReal (le_abs_self _)
  · refine iSup_le fun f ↦ iSup_le fun hf ↦ iSup_le fun hfb ↦ ?_
    have hpos := ofReal_integral_sub_integral_le_transportCost_truncated_dist
      (μ := μ) (ν := ν) hf hfb
    have hneg := ofReal_integral_sub_integral_le_transportCost_truncated_dist
      (μ := μ) (ν := ν) hf.neg (fun x ↦ by simpa using hfb x)
    simp only [Pi.neg_apply, integral_neg] at hneg
    rw [abs_sub_comm]
    rcases le_total (∫ x, f x ∂μ) (∫ x, f x ∂ν) with h | h
    · rw [abs_of_nonneg (sub_nonneg.2 h)]
      convert hneg using 1
      congr 1
      ring
    · rw [abs_of_nonpos (sub_nonpos.2 h)]
      convert hpos using 1
      congr 1
      ring

end Polish

end TauCeti
