/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Integral.Average
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import TauCeti.Analysis.Calculus.BumpFunction.LipschitzCutoff
import TauCeti.MeasureTheory.Integral.Average
import TauCeti.MeasureTheory.Measure.Haar.NormedSpace
import TauCeti.MeasureTheory.Measure.OpenPos

/-!
# Small mean oscillation below a radius extends to every scale near a ball

Let `β : ℝ^{n+1} → F` be a locally integrable field with values in a real normed space, and
suppose that on every ball `B(c, r)` of radius at most `r₀` some constant `P`, satisfying a
property `Q c r`, approximates `β` with mean deviation `⨍_{B(c, r)} ‖β - P‖ ≤ δ`. For a ball
`B(x₀, R)` with `4R ≤ r₀`, this file produces a continuous cutoff `ψ ∈ [0, 1]` equal to one on
`B(x₀, R)` and a constant `P₀` satisfying `Q x₀ (4R)` such that the field `ψ β + (1 - ψ) P₀`,
which agrees with `β` on `B(x₀, R)`, has mean deviation at most `4 · 8^(n + 1) δ` on every ball,
of any radius, from a convex combination of `P₀` and a constant satisfying `Q`
(`TauCeti.exists_forall_setAverage_norm_cutoff_sub_le`). This is how fields of vanishing mean
oscillation, which are close to constants only on small balls, meet estimates that ask for small
mean oscillation at every scale.

The key step bounds the drift of the approximating constants along the dyadic balls
`B(c, 2ᵏ r)`: consecutive constants differ by `O(δ)`
(`TauCeti.norm_sub_le_of_forall_setAverage_le`), so a constant of a small ball `B(c, r)` near
`x₀` is within `O(log(R / r) δ)` of `P₀`, and `(r / R) log(R / r)` is bounded
(`TauCeti.exists_setAverage_le_and_div_mul_norm_sub_le`).

The proof takes `ψ` vanishing outside `B(x₀, 2R)` and `2 / R`-Lipschitz, and `P₀` the constant of
`B(x₀, 4R)`.

* On a ball `B` of radius `r ≥ R`, the field stays close to `P₀`: the deviation `ψ ‖β - P₀‖`
  lives on `B(x₀, 2R)`, and its integral is at most `δ |B(x₀, 4R)| ≤ 4^(n + 1) δ |B|`.
* On a ball `B = B(c, r)` with `r < R` far from `x₀`, the field is `P₀`.
* On a ball `B = B(c, r)` with `r < R` near `x₀`, compare the field with
  `ψ(c) P + (1 - ψ(c)) P₀`, where `P` is a constant of `B`. The error is at most
  `δ + (2 r / R) ‖P - P₀‖`, which the drift bound makes `O(δ)`.

## Main declarations

* `TauCeti.norm_sub_le_of_forall_setAverage_le`: the drift of approximating constants along
  concentric dyadic balls.
* `TauCeti.exists_setAverage_le_and_div_mul_norm_sub_le`: the drift from a large ball to a small
  ball near its centre, weighted by the ratio of the radii.
* `TauCeti.exists_forall_setAverage_norm_cutoff_sub_le`: the cutoff extension of a field of small
  mean oscillation below a radius to a field of small mean oscillation at every scale.

## References

* N. V. Krylov, *Parabolic and elliptic equations with VMO coefficients*, Comm. Partial
  Differential Equations **32** (2007), 453–475.
-/

public section

open MeasureTheory Metric Set
open scoped NNReal

namespace TauCeti

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F]

/-- A locally integrable field `β` stays within integrable distance of any constant on every
ball. -/
private theorem integrableOn_norm_sub {β : EuclideanSpace ℝ (Fin (n + 1)) → F}
    (hβ : LocallyIntegrable β volume) (P : F) (c : EuclideanSpace ℝ (Fin (n + 1))) (r : ℝ) :
    IntegrableOn (fun x => ‖β x - P‖) (ball c r) :=
  (((hβ.integrableOn_isCompact (isCompact_closedBall c r)).mono_set ball_subset_closedBall).sub
    (integrableOn_const measure_ball_lt_top.ne)).norm

/-- A locally integrable field `β`, multiplied by a measurable weight `w` bounded by one, stays
within integrable distance of any constant on every ball. -/
private theorem integrableOn_mul_norm_sub {β : EuclideanSpace ℝ (Fin (n + 1)) → F}
    (hβ : LocallyIntegrable β volume)
    {w : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} (hw : AEStronglyMeasurable w volume)
    (hw1 : ∀ x, |w x| ≤ 1) (P : F) (c : EuclideanSpace ℝ (Fin (n + 1))) (r : ℝ) :
    IntegrableOn (fun x => w x * ‖β x - P‖) (ball c r) :=
  (integrableOn_norm_sub hβ P c r).mono'
    (hw.mul (hβ.aestronglyMeasurable.sub aestronglyMeasurable_const).norm).restrict
    (.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_mul, abs_norm]
      exact mul_le_of_le_one_left (norm_nonneg _) (hw1 x))

/-- **Drift of approximating constants along concentric balls.** If on each ball `B(c, 2ᵏ r)`,
`k ≤ m`, the constant `P k` approximates `β` with mean deviation at most `δ`, then `P 0` and `P m`
differ by at most `m (1 + 2^(n + 1)) δ`. -/
theorem norm_sub_le_of_forall_setAverage_le {β : EuclideanSpace ℝ (Fin (n + 1)) → F}
    (hβ : LocallyIntegrable β volume)
    {c : EuclideanSpace ℝ (Fin (n + 1))} {r δ : ℝ} (hr : 0 < r) {P : ℕ → F} :
    ∀ m : ℕ, (∀ k ≤ m, ⨍ x in ball c (2 ^ k * r), ‖β x - P k‖ ≤ δ) →
      ‖P 0 - P m‖ ≤ m * ((1 + 2 ^ (n + 1)) * δ)
  | 0, _ => by simp
  | m + 1, hP => by
    have ih := norm_sub_le_of_forall_setAverage_le hβ hr m
      fun k hk => hP k (hk.trans m.le_succ)
    have hrm : 0 < 2 ^ m * r := by positivity
    have hstep := norm_sub_le_setAverage_add_div_mul_setAverage_of_subset
      (s := ball c (2 ^ m * r)) (t := ball c (2 ^ (m + 1) * r))
      (ball_subset_ball (by rw [pow_succ]; nlinarith)) (measure_ball_pos _ _ hrm).ne'
      measure_ball_lt_top.ne (integrableOn_norm_sub hβ (P m) c _)
      (integrableOn_norm_sub hβ (P (m + 1)) c _)
    rw [Measure.addHaar_real_ball_div_addHaar_real_ball _ _ _ hrm (by positivity),
      finrank_euclideanSpace_fin,
      show 2 ^ (m + 1) * r / (2 ^ m * r) = 2 by field_simp; ring] at hstep
    calc ‖P 0 - P (m + 1)‖ ≤ ‖P 0 - P m‖ + ‖P m - P (m + 1)‖ :=
          norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ m * ((1 + 2 ^ (n + 1)) * δ) + (δ + 2 ^ (n + 1) * δ) := by
          gcongr
          exact hstep.trans (add_le_add (hP m m.le_succ)
            (mul_le_mul_of_nonneg_left (hP (m + 1) le_rfl) (by positivity)))
      _ = ((m + 1 : ℕ) : ℝ) * ((1 + 2 ^ (n + 1)) * δ) := by push_cast; ring

/-- **The cutoff field on a large ball.** Let `ψ ∈ [0, 1]` vanish outside `B(x₀, 2R)`, and let the
constant `P₀` approximate `β` on `B(x₀, 4R)` with mean deviation at most `δ`. On every ball of
radius `r ≥ R`, the field `ψ β + (1 - ψ) P₀` then deviates from `P₀` on average by at most
`4^(n + 1) δ`. -/
private theorem setAverage_norm_cutoff_sub_le_of_le [NormedSpace ℝ F]
    {β : EuclideanSpace ℝ (Fin (n + 1)) → F} (hβ : LocallyIntegrable β volume)
    {ψ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} (hψm : Continuous ψ) (hψ : ∀ x, ψ x ∈ Icc 0 1)
    {x₀ c : EuclideanSpace ℝ (Fin (n + 1))} {R r δ : ℝ}
    (hψ0 : ∀ x, 2 * R ≤ dist x x₀ → ψ x = 0) (hR : 0 < R) (hRr : R ≤ r) {P₀ : F}
    (hδ : ⨍ x in ball x₀ (4 * R), ‖β x - P₀‖ ≤ δ) :
    ⨍ x in ball c r, ‖ψ x • β x + (1 - ψ x) • P₀ - P₀‖ ≤ 4 ^ (n + 1) * δ := by
  have hr : 0 < r := hR.trans_le hRr
  have hψ1 : ∀ x, |ψ x| ≤ 1 := fun x => abs_le.2 ⟨by linarith [(hψ x).1], (hψ x).2⟩
  have hpt : ∀ x, ‖ψ x • β x + (1 - ψ x) • P₀ - P₀‖ = ψ x * ‖β x - P₀‖ := fun x => by
    rw [show ψ x • β x + (1 - ψ x) • P₀ - P₀ = ψ x • (β x - P₀) by module, norm_smul,
      Real.norm_of_nonneg (hψ x).1]
  have hint := integrableOn_mul_norm_sub hβ hψm.aestronglyMeasurable hψ1 P₀ x₀ (4 * R)
  -- The integrand vanishes off `B(x₀, 2R)`, so its integral over `B(c, r)` is at most its
  -- integral over `B(x₀, 4R)`.
  have hI : ∫ x in ball c r, ψ x * ‖β x - P₀‖ ≤ ∫ x in ball x₀ (4 * R), ‖β x - P₀‖ := by
    calc ∫ x in ball c r, ψ x * ‖β x - P₀‖
        = ∫ x in ball c r, (ball x₀ (4 * R)).indicator (fun x => ψ x * ‖β x - P₀‖) x := by
          refine integral_congr_ae (.of_forall fun x => ?_)
          dsimp only
          by_cases hx : x ∈ ball x₀ (4 * R)
          · rw [indicator_of_mem hx]
          · rw [indicator_of_notMem hx, hψ0 x (by rw [mem_ball, not_lt] at hx; linarith),
              zero_mul]
      _ = ∫ x in ball c r ∩ ball x₀ (4 * R), ψ x * ‖β x - P₀‖ := setIntegral_indicator
          measurableSet_ball
      _ ≤ ∫ x in ball x₀ (4 * R), ψ x * ‖β x - P₀‖ :=
          setIntegral_mono_set hint (.of_forall fun x => mul_nonneg (hψ x).1 (norm_nonneg _))
            (.of_forall inter_subset_right)
      _ ≤ _ := setIntegral_mono_on hint (integrableOn_norm_sub hβ P₀ x₀ _) measurableSet_ball
          fun x _ => mul_le_of_le_one_left (norm_nonneg _) (hψ x).2
  have hvol := Measure.addHaar_real_ball_div_addHaar_real_ball volume c x₀ hr
    (by positivity : 0 < 4 * R)
  rw [finrank_euclideanSpace_fin] at hvol
  have hvol0 : 0 < volume.real (ball c r) := Metric.measureReal_ball_pos volume _ hr
  simp_rw [hpt]
  simp only [setAverage_eq, smul_eq_mul] at hδ ⊢
  calc (volume.real (ball c r))⁻¹ * ∫ x in ball c r, ψ x * ‖β x - P₀‖
      ≤ (volume.real (ball c r))⁻¹ * ∫ x in ball x₀ (4 * R), ‖β x - P₀‖ := by gcongr
    _ = (4 * R / r) ^ (n + 1) * ((volume.real (ball x₀ (4 * R)))⁻¹ *
          ∫ x in ball x₀ (4 * R), ‖β x - P₀‖) := by
        have : volume.real (ball x₀ (4 * R)) ≠ 0 :=
          (Metric.measureReal_ball_pos volume _ (by positivity)).ne'
        rw [← hvol]
        field_simp
    _ ≤ 4 ^ (n + 1) * δ := by
        gcongr
        rw [div_le_iff₀ hr]
        linarith

/-- **The cutoff field on a small ball.** Let `ψ ∈ [0, 1]` be `K`-Lipschitz, and let the constant
`P` approximate `β` on `B(c, r)` with mean deviation at most `δ`. Then on `B(c, r)` the field
`ψ β + (1 - ψ) P₀` deviates on average from the constant `ψ(c) P + (1 - ψ(c)) P₀` by at most
`δ + K r ‖P - P₀‖`. -/
private theorem setAverage_norm_cutoff_sub_le [NormedSpace ℝ F]
    {β : EuclideanSpace ℝ (Fin (n + 1)) → F} (hβ : LocallyIntegrable β volume)
    {ψ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} (hψ : ∀ x, ψ x ∈ Icc 0 1)
    {K : ℝ≥0} (hψlip : LipschitzWith K ψ) {c : EuclideanSpace ℝ (Fin (n + 1))}
    {r δ : ℝ} (hr : 0 < r) {P₀ P : F} (hδ : ⨍ x in ball c r, ‖β x - P‖ ≤ δ) :
    ⨍ x in ball c r, ‖ψ x • β x + (1 - ψ x) • P₀ - (ψ c • P + (1 - ψ c) • P₀)‖ ≤
      δ + K * r * ‖P - P₀‖ := by
  have hvol0 : 0 < volume.real (ball c r) := Metric.measureReal_ball_pos volume _ hr
  have hint := integrableOn_norm_sub hβ P c r
  have hpt : ∀ x ∈ ball c r, ‖ψ x • β x + (1 - ψ x) • P₀ - (ψ c • P + (1 - ψ c) • P₀)‖ ≤
      ‖β x - P‖ + K * r * ‖P - P₀‖ := fun x hx => by
    rw [show ψ x • β x + (1 - ψ x) • P₀ - (ψ c • P + (1 - ψ c) • P₀) =
      ψ x • (β x - P) + (ψ x - ψ c) • (P - P₀) by module]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_smul, Real.norm_of_nonneg (hψ x).1]
      exact mul_le_of_le_one_left (norm_nonneg _) (hψ x).2
    · rw [norm_smul, ← dist_eq_norm]
      gcongr
      exact (hψlip.dist_le_mul x c).trans
        (mul_le_mul_of_nonneg_left (mem_ball.1 hx).le K.coe_nonneg)
  have hmeas : AEStronglyMeasurable
      (fun x => ‖ψ x • β x + (1 - ψ x) • P₀ - (ψ c • P + (1 - ψ c) • P₀)‖) volume :=
    (((hψlip.continuous.aestronglyMeasurable.smul hβ.aestronglyMeasurable).add
      ((continuous_const.sub hψlip.continuous).aestronglyMeasurable.smul_const P₀)).sub
        aestronglyMeasurable_const).norm
  have hsum : IntegrableOn (fun x => ‖β x - P‖ + K * r * ‖P - P₀‖) (ball c r) :=
    hint.add (integrableOn_const measure_ball_lt_top.ne)
  have hint' : IntegrableOn
      (fun x => ‖ψ x • β x + (1 - ψ x) • P₀ - (ψ c • P + (1 - ψ c) • P₀)‖) (ball c r) :=
    hsum.mono' hmeas.restrict
      ((ae_restrict_iff' measurableSet_ball).2 (.of_forall fun x hx => by
        rw [Real.norm_of_nonneg (norm_nonneg _)]; exact hpt x hx))
  simp only [setAverage_eq, smul_eq_mul] at hδ ⊢
  calc _ ≤ (volume.real (ball c r))⁻¹ * ∫ x in ball c r, (‖β x - P‖ + K * r * ‖P - P₀‖) :=
        mul_le_mul_of_nonneg_left (setIntegral_mono_on hint' hsum measurableSet_ball hpt)
          (inv_nonneg.2 hvol0.le)
    _ = (volume.real (ball c r))⁻¹ * (∫ x in ball c r, ‖β x - P‖) + K * r * ‖P - P₀‖ := by
        rw [integral_add hint (integrableOn_const measure_ball_lt_top.ne), setIntegral_const,
          smul_eq_mul]
        field_simp
    _ ≤ _ := by gcongr

/-- **The cutoff field on a ball where the cutoff vanishes** is the constant `P₀`. -/
private theorem setAverage_norm_cutoff_sub_eq_zero [NormedSpace ℝ F]
    {β : EuclideanSpace ℝ (Fin (n + 1)) → F} {ψ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ}
    {c : EuclideanSpace ℝ (Fin (n + 1))} {r : ℝ} (hψ0 : ∀ x ∈ ball c r, ψ x = 0) (P₀ : F) :
    ⨍ x in ball c r, ‖ψ x • β x + (1 - ψ x) • P₀ - P₀‖ = 0 := by
  rw [setAverage_eq, setIntegral_congr_fun measurableSet_ball (g := fun _ => (0 : ℝ))
    fun x hx => by simp [hψ0 x hx]]
  simp

/-- **Approximating constants on small balls near the centre.** Let the constants satisfying a
property `Q c r` approximate `β` on every ball `B(c, r)` of radius at most `r₀` with mean deviation
at most `δ`, and let `P₀` approximate `β` on `B(x₀, 4R)`, `R ≤ r₀`. Then every ball `B(c, r)` with
`r ≤ R` and `c ∈ B(x₀, 3R)` has such a constant `P` with
`‖P - P₀‖ ≤ (R / r) (2 + 2^(n + 1) + 8^(n + 1)) δ`: the approximating constants drift at most
logarithmically in `R / r` along the dyadic balls `B(c, 2ᵏ r)`. -/
theorem exists_setAverage_le_and_div_mul_norm_sub_le
    {β : EuclideanSpace ℝ (Fin (n + 1)) → F} (hβ : LocallyIntegrable β volume)
    {Q : EuclideanSpace ℝ (Fin (n + 1)) → ℝ → F → Prop} {δ r₀ : ℝ}
    (hosc : ∀ (c : EuclideanSpace ℝ (Fin (n + 1))) (r : ℝ), 0 < r → r ≤ r₀ →
      ∃ P, Q c r P ∧ ⨍ x in ball c r, ‖β x - P‖ ≤ δ)
    {x₀ c : EuclideanSpace ℝ (Fin (n + 1))} {R r : ℝ} {P₀ : F}
    (hδ₀ : ⨍ x in ball x₀ (4 * R), ‖β x - P₀‖ ≤ δ) (hRr₀ : R ≤ r₀) (hr : 0 < r) (hrR : r ≤ R)
    (hc : dist c x₀ < 3 * R) :
    ∃ P, Q c r P ∧ ⨍ x in ball c r, ‖β x - P‖ ≤ δ ∧
      r / R * ‖P - P₀‖ ≤ (2 + 2 ^ (n + 1) + 8 ^ (n + 1)) * δ := by
  have hR : 0 < R := hr.trans_le hrR
  have hδ : 0 ≤ δ := (average_nonneg fun _ => norm_nonneg _).trans hδ₀
  -- `2ᵐ r ≤ R < 2ᵐ⁺¹ r`.
  obtain ⟨m, hm, hm'⟩ := exists_nat_pow_near ((one_le_div hr).2 hrR) one_lt_two
  rw [le_div_iff₀ hr] at hm
  rw [div_lt_iff₀ hr] at hm'
  have hfam : ∀ k : ℕ, ∃ P, k ≤ m →
      Q c (2 ^ k * r) P ∧ ⨍ x in ball c (2 ^ k * r), ‖β x - P‖ ≤ δ := by
    intro k
    by_cases hk : k ≤ m
    · obtain ⟨P, hP⟩ := hosc c (2 ^ k * r) (by positivity)
        (le_trans (by gcongr; norm_num) (hm.trans hRr₀))
      exact ⟨P, fun _ => hP⟩
    · exact ⟨0, fun h => absurd h hk⟩
  choose P hP using hfam
  have hchain := norm_sub_le_of_forall_setAverage_le hβ hr m fun k hk => (hP k hk).2
  -- The last dyadic ball `B(c, 2ᵐ r)` lies in `B(x₀, 4R)`, with volume ratio below `8^(n + 1)`.
  have hmr : 0 < 2 ^ m * r := by positivity
  have hlast := norm_sub_le_setAverage_add_div_mul_setAverage_of_subset
    (s := ball c (2 ^ m * r)) (t := ball x₀ (4 * R))
    (ball_subset_ball' (by linarith)) (measure_ball_pos _ _ hmr).ne' measure_ball_lt_top.ne
    (integrableOn_norm_sub hβ (P m) c _) (integrableOn_norm_sub hβ P₀ x₀ _)
  rw [Measure.addHaar_real_ball_div_addHaar_real_ball _ _ _ hmr (by positivity),
    finrank_euclideanSpace_fin] at hlast
  have hratio : (4 * R / (2 ^ m * r)) ^ (n + 1) ≤ 8 ^ (n + 1) := by
    gcongr
    rw [div_le_iff₀ hmr]
    linarith [show (2 : ℝ) ^ (m + 1) * r = 2 * (2 ^ m * r) by ring]
  have hlast' : ‖P m - P₀‖ ≤ (1 + 8 ^ (n + 1)) * δ :=
    hlast.trans ((add_le_add (hP m le_rfl).2 (mul_le_mul hratio hδ₀
      (average_nonneg fun _ => norm_nonneg _) (by positivity))).trans_eq (by ring))
  -- `(r / R) m ≤ m / 2ᵐ ≤ 1` and `r / R ≤ 1`.
  have hrR1 : r / R ≤ 1 := (div_le_one hR).2 hrR
  have hrRm : r / R * m ≤ 1 := by
    have h2m : (m : ℝ) ≤ 2 ^ m := by exact_mod_cast Nat.lt_two_pow_self.le
    calc r / R * m ≤ r / R * 2 ^ m := by gcongr
      _ = 2 ^ m * r / R := by ring
      _ ≤ 1 := (div_le_one hR).2 hm
  refine ⟨P 0, by simpa using (hP 0 m.zero_le).1, by simpa using (hP 0 m.zero_le).2, ?_⟩
  calc r / R * ‖P 0 - P₀‖ ≤ r / R * (‖P 0 - P m‖ + ‖P m - P₀‖) := by
        gcongr
        exact norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ r / R * (m * ((1 + 2 ^ (n + 1)) * δ) + (1 + 8 ^ (n + 1)) * δ) := by gcongr
    _ = r / R * m * ((1 + 2 ^ (n + 1)) * δ) + r / R * ((1 + 8 ^ (n + 1)) * δ) := by ring
    _ ≤ 1 * ((1 + 2 ^ (n + 1)) * δ) + 1 * ((1 + 8 ^ (n + 1)) * δ) := by gcongr
    _ = (2 + 2 ^ (n + 1) + 8 ^ (n + 1)) * δ := by ring

/-- **The cutoff field on a small ball near the centre.** Under the hypotheses of
`exists_setAverage_le_and_div_mul_norm_sub_le`, for a `K`-Lipschitz cutoff `ψ ∈ [0, 1]` with
`K R ≤ 2` the field `ψ β + (1 - ψ) P₀` has mean deviation at most `4 · 8^(n + 1) δ` on `B(c, r)`
from the constant `ψ(c) P + (1 - ψ(c)) P₀`, for some `P` satisfying `Q c r`. -/
private theorem exists_setAverage_norm_cutoff_sub_le [NormedSpace ℝ F]
    {β : EuclideanSpace ℝ (Fin (n + 1)) → F} (hβ : LocallyIntegrable β volume)
    {Q : EuclideanSpace ℝ (Fin (n + 1)) → ℝ → F → Prop} {δ r₀ : ℝ}
    (hosc : ∀ (c : EuclideanSpace ℝ (Fin (n + 1))) (r : ℝ), 0 < r → r ≤ r₀ →
      ∃ P, Q c r P ∧ ⨍ x in ball c r, ‖β x - P‖ ≤ δ)
    {ψ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} (hψ : ∀ x, ψ x ∈ Icc 0 1)
    {x₀ c : EuclideanSpace ℝ (Fin (n + 1))} {R r : ℝ} {K : ℝ≥0} (hψlip : LipschitzWith K ψ)
    (hKR : K * R ≤ 2) {P₀ : F}
    (hδ₀ : ⨍ x in ball x₀ (4 * R), ‖β x - P₀‖ ≤ δ) (hRr₀ : R ≤ r₀) (hr : 0 < r) (hrR : r ≤ R)
    (hc : dist c x₀ < 3 * R) :
    ∃ P, Q c r P ∧
      ⨍ x in ball c r, ‖ψ x • β x + (1 - ψ x) • P₀ - (ψ c • P + (1 - ψ c) • P₀)‖ ≤
        4 * 8 ^ (n + 1) * δ := by
  have hδ : 0 ≤ δ := (average_nonneg fun _ => norm_nonneg _).trans hδ₀
  obtain ⟨P, hQ, hPδ, hdrift⟩ :=
    exists_setAverage_le_and_div_mul_norm_sub_le hβ hosc hδ₀ hRr₀ hr hrR hc
  have hR : 0 < R := hr.trans_le hrR
  refine ⟨P, hQ, (setAverage_norm_cutoff_sub_le hβ hψ hψlip hr hPδ).trans ?_⟩
  have hKr : K * r * ‖P - P₀‖ ≤ 2 * (r / R * ‖P - P₀‖) := by
    rw [show (K : ℝ) * r * ‖P - P₀‖ = K * R * (r / R * ‖P - P₀‖) by field_simp]
    exact mul_le_mul_of_nonneg_right hKR (by positivity)
  have h2 : (2 : ℝ) ≤ 2 ^ (n + 1) := le_self_pow₀ (by norm_num) n.succ_ne_zero
  have h4 : (4 : ℝ) ≤ 4 ^ (n + 1) := le_self_pow₀ (by norm_num) n.succ_ne_zero
  have h8 : (8 : ℝ) ^ (n + 1) = 2 ^ (n + 1) * 4 ^ (n + 1) := by rw [← mul_pow]; norm_num
  have hK : (5 + 2 * 2 ^ (n + 1) + 2 * 8 ^ (n + 1) : ℝ) ≤ 4 * 8 ^ (n + 1) := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_right hK hδ]

/-- **Small mean oscillation below a radius extends to every scale near a ball.** Let `β` be a
locally integrable field on `ℝ^{n+1}` such that on every ball `B(c, r)` of radius at most `r₀` some
constant satisfying a property `Q c r` has mean deviation at most `δ` from `β`. Then for every ball
`B(x₀, R)` with `4R ≤ r₀` there are a continuous cutoff `ψ ∈ [0, 1]` equal to one on `B(x₀, R)` and
a constant `P₀` satisfying `Q x₀ (4R)` such that on every ball `B(c, r)`, of any radius, the field
`ψ β + (1 - ψ) P₀` has mean deviation at most `4 · 8^(n + 1) δ` from a convex combination
`t P + (1 - t) P₀`, where `P` is `P₀` or satisfies `Q c r`. -/
theorem exists_forall_setAverage_norm_cutoff_sub_le [NormedSpace ℝ F]
    {β : EuclideanSpace ℝ (Fin (n + 1)) → F} (hβ : LocallyIntegrable β volume)
    {Q : EuclideanSpace ℝ (Fin (n + 1)) → ℝ → F → Prop} {δ r₀ R : ℝ}
    (hosc : ∀ (c : EuclideanSpace ℝ (Fin (n + 1))) (r : ℝ), 0 < r → r ≤ r₀ →
      ∃ P, Q c r P ∧ ⨍ x in ball c r, ‖β x - P‖ ≤ δ)
    (x₀ : EuclideanSpace ℝ (Fin (n + 1))) (hR : 0 < R) (hRr₀ : 4 * R ≤ r₀) :
    ∃ ψ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ, Continuous ψ ∧ (∀ x, ψ x ∈ Icc 0 1) ∧
      EqOn ψ 1 (ball x₀ R) ∧ ∃ P₀, Q x₀ (4 * R) P₀ ∧
        ∀ (c : EuclideanSpace ℝ (Fin (n + 1))) (r : ℝ), 0 < r →
          ∃ P, (P = P₀ ∨ Q c r P) ∧ ∃ t ∈ Icc (0 : ℝ) 1,
            ⨍ x in ball c r, ‖ψ x • β x + (1 - ψ x) • P₀ - (t • P + (1 - t) • P₀)‖ ≤
              4 * 8 ^ (n + 1) * δ := by
  obtain ⟨P₀, hQ₀, hδ₀⟩ := hosc x₀ (4 * R) (by positivity) hRr₀
  have hδ : 0 ≤ δ := (average_nonneg fun _ => norm_nonneg _).trans hδ₀
  obtain ⟨ψ, hψs, hψr, hψ1, hψsupp, hψlip⟩ :=
    exists_contDiff_cutoff_closedBall_lipschitzWith_mul_inv x₀ (r := R) hR (t := 2) one_lt_two
  have hψ : ∀ x, ψ x ∈ Icc 0 1 := fun x => hψr (mem_range_self x)
  have hψ0 : ∀ x, 2 * R ≤ dist x x₀ → ψ x = 0 := fun x hx =>
    Function.notMem_support.1 fun h => (mem_ball.1 (hψsupp h)).not_ge (by linarith)
  have hKR : ((2 * R.toNNReal⁻¹ : ℝ≥0) : ℝ) * R ≤ 2 := by
    simp [Real.coe_toNNReal _ hR.le, hR.ne']
  refine ⟨ψ, hψs.continuous, hψ, hψ1.mono ball_subset_closedBall, P₀, hQ₀, fun c r hr => ?_⟩
  rcases le_or_gt R r with hRr | hrR
  · -- A large ball: compare with `P₀`.
    refine ⟨P₀, .inl rfl, 0, ⟨le_rfl, zero_le_one⟩, ?_⟩
    simp only [zero_smul, sub_zero, one_smul, zero_add]
    refine (setAverage_norm_cutoff_sub_le_of_le hβ hψs.continuous hψ hψ0 hR hRr hδ₀).trans
      (mul_le_mul_of_nonneg_right ?_ hδ)
    have h48 : (4 : ℝ) ^ (n + 1) ≤ 8 ^ (n + 1) := by gcongr; norm_num
    linarith [pow_pos (by norm_num : (0 : ℝ) < 8) (n + 1)]
  rcases le_or_gt (3 * R) (dist c x₀) with hfar | hnear
  · -- A small ball far from `x₀`, where the field is `P₀`.
    refine ⟨P₀, .inl rfl, 0, ⟨le_rfl, zero_le_one⟩, ?_⟩
    simp only [zero_smul, sub_zero, one_smul, zero_add]
    rw [setAverage_norm_cutoff_sub_eq_zero
      fun x hx => hψ0 x (by linarith [dist_triangle_right c x₀ x, mem_ball'.1 hx, dist_comm x x₀])]
    positivity
  · -- A small ball near `x₀`: compare with a convex combination of `P₀` and a constant of the ball.
    obtain ⟨P, hQ, hP⟩ := exists_setAverage_norm_cutoff_sub_le hβ hosc hψ hψlip hKR hδ₀
      (by linarith) hr hrR.le hnear
    exact ⟨P, .inr hQ, ψ c, hψ c, hP⟩

end TauCeti
