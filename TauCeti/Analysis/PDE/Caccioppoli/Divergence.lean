/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Caccioppoli.Basic
import TauCeti.Analysis.PDE.EnergyForm.Restriction
import TauCeti.MeasureTheory.Function.L2Space

/-!
# The Caccioppoli inequality for a right-hand side in divergence form

Let `u ∈ H¹(Ω)` be a weak solution of the divergence-form equation

`-∂ᵢ(aⁱʲ ∂ⱼu) = ∂ᵢFⁱ` in `Ω`, with `F ∈ L²(Ω; ℝⁿ)`,

meaning `∫_Ω ⟨a ∇u, ∇v⟩ = -∫_Ω ⟪F, ∇v⟫` for every `v ∈ H¹₀(Ω)`; no boundary condition is imposed
on `u`. If the coefficient `a` is measurable and uniformly elliptic with constants `0 < λ ≤ Λ`,
then for every smooth cutoff `ψ` compactly supported in `Ω`,

`∫_Ω ψ² ‖∇u‖² ≤ 2 ((2Λ/λ)² + 1) ∫_Ω ‖∇ψ‖² u² + (12/λ²) ∫_Ω ψ² ‖F‖²`.

Unlike the forcing term `∫ ψ² f u` of the scalar right-hand side
(`TauCeti.PDE.UniformlyEllipticOn.setIntegral_sq_mul_norm_gradient_sq_le`), the divergence datum
pairs with `∇(ψ² u)`, which contains `∇u`; Young's inequality absorbs that part into the
left-hand side, so the datum enters only through `‖F‖²`. On concentric balls
`B(x₀, r) ⊆ B(x₀, R) ⊆ Ω` this gives

`∫_{B(x₀, r)} ‖∇u‖² ≤ 2 ((2Λ/λ)² + 1) (C / (R - r))² ∫_{B(x₀, R)} u² + (12/λ²) ∫_{B(x₀, R)} ‖F‖²`,

with `C` depending only on the dimension. Combined with a Sobolev–Poincaré inequality, this is the
reverse Hölder inequality for `‖∇u‖` behind Meyers' higher integrability theorem; the datum
`F` enters there at the integrability that one wants for `∇u`.

## Main declarations

* `TauCeti.PDE.UniformlyEllipticOn.setIntegral_sq_mul_norm_gradient_sq_le_divergence`: the
  Caccioppoli inequality for a datum in divergence form.
* `TauCeti.PDE.exists_setIntegral_ball_norm_gradient_sq_le_divergence`: its form on concentric
  balls.
* `TauCeti.PDE.exists_setIntegral_ball_norm_gradient_sq_le_sub_setAverage_divergence`: the form
  on `B(y, ρ) ⊆ B(y, 2ρ)` with the mean of `u` over the larger ball subtracted.

## References

* M. Giaquinta, L. Martinazzi, *An Introduction to the Regularity Theory for Elliptic Systems,
  Harmonic Maps and Minimal Graphs*, Theorem 4.4.
* N. G. Meyers, *An `Lᵖ`-estimate for the gradient of solutions of second order elliptic
  divergence equations*, Ann. Scuola Norm. Sup. Pisa **17** (1963), 189–206.
-/

public section

noncomputable section

open MeasureTheory Matrix Set TopologicalSpace
open scoped ContDiff Gradient InnerProductSpace

namespace TauCeti

namespace PDE

variable {ι : Type*} [Fintype ι] {mu : Measure (EuclideanSpace ℝ ι)}
  [mu.IsAddHaarMeasure] {Omega : Opens (EuclideanSpace ℝ ι)}
  {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {lam Lam : ℝ}
  {F : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}

/-- The pointwise Young bound on the divergence datum paired with `∇(ψ² u)`: at a point where
`ψ = z`, `u = w`, `∇u = g`, `∇ψ = q` and `F = f`, the gradient of `ψ² u` is
`z (z g + w q) + z w q`, and `-(2/λ) ⟪f, ∇(ψ² u)⟫` is at most half the energy density
`z² ‖g‖²`, plus `‖q‖² w²`, plus `(6/λ²) z² ‖f‖²`. -/
private theorem two_div_mul_neg_inner_le (hlam : 0 < lam) (z w : ℝ)
    (f g q : EuclideanSpace ℝ ι) :
    2 / lam * -⟪f, z • (z • g + w • q) + (z * w) • q⟫_ℝ ≤
      1 / 2 * (z ^ 2 * ‖g‖ ^ 2) + ‖q‖ ^ 2 * w ^ 2 + 6 / lam ^ 2 * (z ^ 2 * ‖f‖ ^ 2) := by
  have hexp : ⟪f, z • (z • g + w • q) + (z * w) • q⟫_ℝ =
      z ^ 2 * ⟪f, g⟫_ℝ + 2 * (z * w) * ⟪f, q⟫_ℝ := by
    simp only [inner_add_right, inner_smul_right]
    ring
  -- Write `‖f‖ = λ s`.
  set s := ‖f‖ / lam
  have hf : ‖f‖ = lam * s := by
    simp only [s]
    field_simp
  have hA : -⟪f, g⟫_ℝ ≤ lam * s * ‖g‖ :=
    hf ▸ (neg_le_abs _).trans (abs_real_inner_le_norm f g)
  have hB : -(z * w * ⟪f, q⟫_ℝ) ≤ |z| * |w| * (lam * s * ‖q‖) := by
    refine (neg_le_abs _).trans ?_
    rw [abs_mul, abs_mul, ← hf]
    exact mul_le_mul_of_nonneg_left (abs_real_inner_le_norm f q) (by positivity)
  have hrhs : 6 / lam ^ 2 * (z ^ 2 * ‖f‖ ^ 2) = 6 * z ^ 2 * s ^ 2 := by
    rw [hf]
    field_simp
  rw [hexp, hrhs]
  have hz : z ^ 2 = |z| ^ 2 := (sq_abs z).symm
  have hw : w ^ 2 = |w| ^ 2 := (sq_abs w).symm
  have hlhs : 2 / lam * -(z ^ 2 * ⟪f, g⟫_ℝ + 2 * (z * w) * ⟪f, q⟫_ℝ) ≤
      2 * z ^ 2 * s * ‖g‖ + 4 * |z| * |w| * s * ‖q‖ := by
    have h2 : 0 < 2 / lam := by positivity
    calc 2 / lam * -(z ^ 2 * ⟪f, g⟫_ℝ + 2 * (z * w) * ⟪f, q⟫_ℝ)
        = 2 / lam * (z ^ 2 * -⟪f, g⟫_ℝ + 2 * -(z * w * ⟪f, q⟫_ℝ)) := by ring
      _ ≤ 2 / lam * (z ^ 2 * (lam * s * ‖g‖) + 2 * (|z| * |w| * (lam * s * ‖q‖))) := by
          gcongr
      _ = 2 * z ^ 2 * s * ‖g‖ + 4 * |z| * |w| * s * ‖q‖ := by
          field_simp
          ring
  refine hlhs.trans ?_
  nlinarith [sq_nonneg (z * (‖g‖ - 2 * s)), sq_nonneg (|w| * ‖q‖ - 2 * |z| * s)]

variable [DecidableEq ι]

/-- **The Caccioppoli inequality for a datum in divergence form.** Let `a` be measurable and
uniformly elliptic on `Ω` with constants `0 < λ ≤ Λ`, let `F ∈ L²(Ω; ℝⁿ)`, and let `u ∈ H¹(Ω)` be
a weak solution of `-∂ᵢ(aⁱʲ ∂ⱼu) = ∂ᵢFⁱ` in `Ω`, in the sense that `a(u, v) = -∫_Ω ⟪F, ∇v⟫` for
every `v ∈ H¹₀(Ω)`, with no boundary condition on `u`. Then for every smooth `ψ` compactly
supported in `Ω`,

`∫_Ω ψ² ‖∇u‖² ≤ 2 ((2Λ/λ)² + 1) ∫_Ω ‖∇ψ‖² u² + (12/λ²) ∫_Ω ψ² ‖F‖²`. -/
theorem UniformlyEllipticOn.setIntegral_sq_mul_norm_gradient_sq_le_divergence
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (ha : AEStronglyMeasurable a (mu.restrict Omega)) (hF : MemLp F 2 (mu.restrict Omega))
    {u : W1p mu Omega 2}
    (hu : ∀ v : W1p0 mu Omega 2, energyFormH1 a 0 0 u (v : W1p mu Omega 2) =
      -∫ x in Omega, ⟪F x, W1p.gradient (v : W1p mu Omega 2) x⟫_ℝ ∂mu)
    {ψ : EuclideanSpace ℝ ι → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hcpt : HasCompactSupport ψ)
    (hts : tsupport ψ ⊆ (Omega : Set (EuclideanSpace ℝ ι))) :
    ∫ x in Omega, ψ x ^ 2 * ‖W1p.gradient u x‖ ^ 2 ∂mu ≤
      2 * ((2 * Lam / lam) ^ 2 + 1) * ∫ x in Omega, ‖∇ ψ x‖ ^ 2 * W1p.value u x ^ 2 ∂mu
        + 12 / lam ^ 2 * ∫ x in Omega, ψ x ^ 2 * ‖F x‖ ^ 2 ∂mu := by
  obtain ⟨v, -, hgradv, hstep⟩ :=
    h.exists_setIntegral_sq_mul_norm_gradient_sq_le_energyFormH1 ha u hψ hcpt hts
  -- By the weak equation, the energy is `∫_Ω G` with `G = -⟪F, ∇(ψ² u)⟫`.
  set G : EuclideanSpace ℝ ι → ℝ := fun x => -⟪F x, W1p.gradient (v : W1p mu Omega 2) x⟫_ℝ
  have hG : Integrable G (mu.restrict Omega) :=
    (hF.integrable_inner (Lp.memLp (W1p.gradient (v : W1p mu Omega 2)))).neg
  have hGae : ∀ᵐ x ∂mu.restrict Omega, G x = -⟪F x, ψ x • (ψ x • W1p.gradient u x +
      W1p.value u x • ∇ ψ x) + (ψ x * W1p.value u x) • ∇ ψ x⟫_ℝ := by
    filter_upwards [hgradv] with x hx
    simp only [G, hx]
  rw [hu v, ← integral_neg] at hstep
  obtain ⟨M, -, hψM, hgradM⟩ := (hψ.of_le (by simp)).exists_abs_le_and_norm_gradient_le hcpt
  -- Young's inequality absorbs the part of the datum term that contains `∇u`.
  have hψ2 : AEStronglyMeasurable (fun x => ψ x ^ 2) (mu.restrict Omega) :=
    (hψ.continuous.pow 2).aestronglyMeasurable
  have hψ2M : ∀ᵐ x ∂mu.restrict Omega, ‖ψ x ^ 2‖ ≤ M ^ 2 := Filter.Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs, abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (hψM x) 2
  have hI1 : Integrable (fun x => ψ x ^ 2 * ‖W1p.gradient u x‖ ^ 2) (mu.restrict Omega) :=
    (W1p.integrable_norm_gradient_sq u).bdd_mul hψ2 hψ2M
  have hI2 : Integrable (fun x => ‖∇ ψ x‖ ^ 2 * W1p.value u x ^ 2) (mu.restrict Omega) :=
    (Lp.memLp (W1p.value u)).integrable_sq.bdd_mul
      ((ContDiff.continuous_gradient hψ).norm.pow 2).aestronglyMeasurable (c := M ^ 2)
      (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_pow, abs_norm]
        exact pow_le_pow_left₀ (norm_nonneg _) (hgradM x) 2)
  have hI3 : Integrable (fun x => ψ x ^ 2 * ‖F x‖ ^ 2) (mu.restrict Omega) :=
    hF.norm.integrable_sq.bdd_mul hψ2 hψ2M
  have hGle : ∫ x in Omega, 2 / lam * G x ∂mu ≤
      ∫ x in Omega, (1 / 2 * (ψ x ^ 2 * ‖W1p.gradient u x‖ ^ 2)
        + ‖∇ ψ x‖ ^ 2 * W1p.value u x ^ 2 + 6 / lam ^ 2 * (ψ x ^ 2 * ‖F x‖ ^ 2)) ∂mu := by
    refine integral_mono_ae (hG.const_mul _)
      (((hI1.const_mul _).add hI2).add (hI3.const_mul _)) ?_
    filter_upwards [hGae] with x hx
    rw [hx]
    exact two_div_mul_neg_inner_le h.pos (ψ x) (W1p.value u x) (F x) (W1p.gradient u x) (∇ ψ x)
  rw [integral_const_mul, integral_add _ (hI3.const_mul _), integral_add (hI1.const_mul _) hI2,
    integral_const_mul, integral_const_mul] at hGle
  · linear_combination 2 * hstep + 2 * hGle
  · exact (hI1.const_mul _).add hI2

open Filter Metric in
/-- **The Caccioppoli inequality for a datum in divergence form, on concentric balls.** There is
a constant `C > 0`, depending only on the dimension, such that the following holds for every
additive Haar measure `μ`. Let `a` be measurable and uniformly elliptic on `Ω` with constants
`0 < λ ≤ Λ`, let `F ∈ L²(Ω; ℝⁿ)`, and let `u ∈ H¹(Ω)` satisfy `a(u, v) = -∫_Ω ⟪F, ∇v⟫` for every
`v ∈ H¹₀(Ω)`. For every pair of balls `B(x₀, r) ⊆ B(x₀, R) ⊆ Ω` with `0 < r < R`,

`∫_{B(x₀, r)} ‖∇u‖² ≤ 2 ((2Λ/λ)² + 1) (C / (R - r))² ∫_{B(x₀, R)} u² + (12/λ²) ∫_{B(x₀, R)} ‖F‖²`.
-/
theorem exists_setIntegral_ball_norm_gradient_sq_le_divergence :
    ∃ C : ℝ, 0 < C ∧ ∀ {mu : Measure (EuclideanSpace ℝ ι)} [mu.IsAddHaarMeasure]
      {Omega : Opens (EuclideanSpace ℝ ι)} {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {lam Lam : ℝ}
      {F : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {u : W1p mu Omega 2}
      {x₀ : EuclideanSpace ℝ ι} {r R : ℝ},
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam →
      AEStronglyMeasurable a (mu.restrict Omega) → MemLp F 2 (mu.restrict Omega) →
      (∀ v : W1p0 mu Omega 2, energyFormH1 a 0 0 u (v : W1p mu Omega 2) =
        -∫ x in Omega, ⟪F x, W1p.gradient (v : W1p mu Omega 2) x⟫_ℝ ∂mu) →
      0 < r → r < R → ball x₀ R ⊆ (Omega : Set (EuclideanSpace ℝ ι)) →
      ∫ x in ball x₀ r, ‖W1p.gradient u x‖ ^ 2 ∂mu ≤
        2 * ((2 * Lam / lam) ^ 2 + 1) * (C / (R - r)) ^ 2 *
            ∫ x in ball x₀ R, W1p.value u x ^ 2 ∂mu
          + 12 / lam ^ 2 * ∫ x in ball x₀ R, ‖F x‖ ^ 2 ∂mu := by
  obtain ⟨C, hC0, hC⟩ := exists_setIntegral_ball_norm_gradient_sq_le_add_setIntegral_of_cutoff
    (ι := ι)
  refine ⟨C, hC0, ?_⟩
  intro mu _ Omega a lam Lam F u x₀ r R h ha hF hu hr hrR hball
  -- The datum density `g = (12/λ²) ‖F‖²`.
  have hloc := hC u (A := 2 * ((2 * Lam / lam) ^ 2 + 1)) (g := fun x => 12 / lam ^ 2 * ‖F x‖ ^ 2)
    (by positivity) (hF.norm.integrable_sq.const_mul _)
    (Eventually.of_forall fun x => by positivity) hr hrR hball fun ψ hψ hcpt hts => by
      simp_rw [mul_left_comm (ψ _ ^ 2), integral_const_mul]
      exact h.setIntegral_sq_mul_norm_gradient_sq_le_divergence ha hF hu hψ hcpt hts
  rwa [integral_const_mul] at hloc

open Filter Metric in
/-- **The Caccioppoli inequality for a datum in divergence form, with the mean subtracted.**
There is a constant `C > 0`, depending only on the dimension, such that the following holds for
every additive Haar measure `μ`. Let `a` be measurable and uniformly elliptic on `Ω` with constants
`0 < λ ≤ Λ`, let `F ∈ L²(Ω; ℝⁿ)`, and let `u ∈ H¹(Ω)` satisfy `a(u, v) = -∫_Ω ⟪F, ∇v⟫` for every
`v ∈ H¹₀(Ω)`. For every ball with `B(y, 2ρ) ⊆ Ω`, writing `m` for the mean of `u` over
`B(y, 2ρ)`,

`∫_{B(y, ρ)} ‖∇u‖² ≤ 2 ((2Λ/λ)² + 1) (C / ρ)² ∫_{B(y, 2ρ)} |u - m|² + (12/λ²) ∫_{B(y, 2ρ)} ‖F‖²`.

Constants are not Sobolev functions on `Ω` unless `Ω` has finite measure, so `u - m` is formed on
the ball, where it is again a weak solution of the same equation. -/
theorem exists_setIntegral_ball_norm_gradient_sq_le_sub_setAverage_divergence :
    ∃ C : ℝ, 0 < C ∧ ∀ {mu : Measure (EuclideanSpace ℝ ι)} [mu.IsAddHaarMeasure]
      {Omega : Opens (EuclideanSpace ℝ ι)} {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {lam Lam : ℝ}
      {F : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {u : W1p mu Omega 2}
      {y : EuclideanSpace ℝ ι} {ρ : ℝ},
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam →
      AEStronglyMeasurable a (mu.restrict Omega) → MemLp F 2 (mu.restrict Omega) →
      (∀ v : W1p0 mu Omega 2, energyFormH1 a 0 0 u (v : W1p mu Omega 2) =
        -∫ x in Omega, ⟪F x, W1p.gradient (v : W1p mu Omega 2) x⟫_ℝ ∂mu) →
      0 < ρ → ball y (2 * ρ) ⊆ (Omega : Set (EuclideanSpace ℝ ι)) →
      ∫ x in ball y ρ, ‖W1p.gradient u x‖ ^ 2 ∂mu ≤
        2 * ((2 * Lam / lam) ^ 2 + 1) * (C / ρ) ^ 2 *
            ∫ x in ball y (2 * ρ), (W1p.value u x - ⨍ z in ball y (2 * ρ), W1p.value u z ∂mu) ^ 2
              ∂mu
          + 12 / lam ^ 2 * ∫ x in ball y (2 * ρ), ‖F x‖ ^ 2 ∂mu := by
  obtain ⟨C, hC0, hC⟩ := exists_setIntegral_ball_norm_gradient_sq_le_divergence (ι := ι)
  refine ⟨C, hC0, ?_⟩
  intro mu _ Omega a lam Lam F u y ρ h ha hF hu hρ hball
  -- The ball `B = B(y, 2ρ)`, as a domain of its own, on which constants are Sobolev functions.
  set B : Opens (EuclideanSpace ℝ ι) := ⟨ball y (2 * ρ), isOpen_ball⟩
  have hB : B ≤ Omega := hball
  have : IsFiniteMeasure (mu.restrict (B : Set (EuclideanSpace ℝ ι))) :=
    isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
  set uB := W1p.restrictL hB u
  set m := ⨍ z in ball y (2 * ρ), W1p.value u z ∂mu
  have hm : ⨍ z in (B : Set (EuclideanSpace ℝ ι)), W1p.value uB z ∂mu = m :=
    average_congr (W1p.value_restrictL_ae hB u)
  -- `w = u - m` solves the same equation on `B`.
  set w : W1p mu B 2 := uB + W1p.const (-m)
  have hw : ∀ v : W1p0 mu B 2, energyFormH1 a 0 0 w (v : W1p mu B 2) =
      -∫ x in B, ⟪F x, W1p.gradient (v : W1p mu B 2) x⟫_ℝ ∂mu := fun v => by
    rw [energyFormH1_add_const_left]
    exact energyFormH1_restrictL_eq_neg_setIntegral_inner hB hu v
  have hcacc := hC (mu := mu) (Omega := B) (u := w) (x₀ := y) (r := ρ) (R := 2 * ρ)
    (h.mono_set hball) (ha.mono_measure (Measure.restrict_mono hball le_rfl))
    (hF.mono_measure (Measure.restrict_mono hball le_rfl)) hw hρ (by linarith) subset_rfl
  -- On `B`, `∇w = ∇u` and `w = u - m`.
  have e1 : ∫ x in ball y ρ, ‖W1p.gradient w x‖ ^ 2 ∂mu =
      ∫ x in ball y ρ, ‖W1p.gradient u x‖ ^ 2 ∂mu := by
    refine integral_congr_ae (ae_restrict_of_ae_restrict_of_subset
      (ball_subset_ball (by linarith) : ball y ρ ⊆ ball y (2 * ρ)) ?_)
    rw [W1p.gradient_add_const]
    filter_upwards [W1p.gradient_restrictL_ae hB u] with x hx
    rw [hx]
  have e2 : ∫ x in ball y (2 * ρ), W1p.value w x ^ 2 ∂mu =
      ∫ x in ball y (2 * ρ), (W1p.value u x - m) ^ 2 ∂mu := by
    refine integral_congr_ae ?_
    filter_upwards [W1p.value_add_const_ae uB (-m), W1p.value_restrictL_ae hB u] with x h1 h2
    rw [h1, h2, sub_eq_add_neg]
  have hρ2 : 2 * ρ - ρ = ρ := by ring
  rwa [e1, e2, hρ2] at hcacc

end PDE

end TauCeti
