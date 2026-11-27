/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Caccioppoli.Basic
import TauCeti.Analysis.PDE.EnergyForm.Restriction
import TauCeti.MeasureTheory.Function.L2Space
import TauCeti.MeasureTheory.Function.Lp.Norm
import TauCeti.MeasureTheory.Integral.Bochner.Set

/-!
# The Caccioppoli inequality for a right-hand side in divergence form

Let `u ∈ H¹(Ω)` be a weak solution of the divergence-form equation

`-∂ᵢ(aⁱʲ ∂ⱼu) = ∂ᵢFⁱ` in `Ω`, with `F ∈ L²(Ω; ℝⁿ)`,

meaning `∫_Ω ⟨a ∇u, ∇v⟩ = -∫_Ω ⟪F, ∇v⟫` for every `v ∈ H¹₀(Ω)`; no boundary condition is imposed
on `u`. If the coefficient `a` is measurable and uniformly elliptic with constants `0 < λ ≤ Λ`,
then for every smooth cutoff `ψ` compactly supported in `Ω`,

`∫_Ω ψ² ‖∇u‖² ≤ 2 ((2Λ/λ)² + 1) ∫_Ω ‖∇ψ‖² u² + (12/λ²) ∫_Ω ψ² ‖F‖²`.

When `u ∈ H¹₀(Ω)` the support of `ψ` may meet `∂Ω`, which gives the inequality up to the boundary.

Unlike the forcing term `∫ ψ² f u` of the scalar right-hand side
(`TauCeti.PDE.UniformlyEllipticOn.setIntegral_sq_mul_norm_gradient_sq_le`), the divergence datum
pairs with `∇(ψ² u)`, which contains `∇u`; Young's inequality absorbs that part into the
left-hand side, so the datum enters only through `‖F‖²`. On concentric balls
`B(x₀, r) ⊆ B(x₀, R) ⊆ Ω` this gives

`∫_{B(x₀, r)} ‖∇u‖² ≤ 2 ((2Λ/λ)² + 1) (C / (R - r))² ∫_{B(x₀, R)} u² + (12/λ²) ∫_{B(x₀, R)} ‖F‖²`,

with `C` depending only on the dimension. Combined with a Sobolev–Poincaré inequality, this is the
reverse Hölder inequality for `‖∇u‖` behind Meyers' higher integrability theorem; the datum
`F` enters there at the integrability that one wants for `∇u`.

A scalar datum `f` as well, in the equation `-∂ᵢ(aⁱʲ ∂ⱼu) = f + ∂ᵢFⁱ`, adds the term
`(4/λ) ∫_Ω ψ² f u`, and `(4/λ) ∫_{B(x₀, R)} |f u|` on balls. This is the form needed for the
interior Schauder estimate of divergence-form equations, whose datum has both parts.

## Main declarations

* `TauCeti.PDE.UniformlyEllipticOn.setIntegral_sq_mul_norm_gradient_sq_le_add_divergence`: the
  Caccioppoli inequality for a right-hand side `f + div F`.
* `TauCeti.PDE.exists_setIntegral_ball_norm_gradient_sq_le_add_divergence`: its form on
  concentric balls.
* `TauCeti.PDE.UniformlyEllipticOn.setIntegral_sq_mul_norm_gradient_sq_le_divergence`: the
  Caccioppoli inequality for a datum in divergence form, the case `f = 0`.
* `TauCeti.PDE.exists_setIntegral_ball_norm_gradient_sq_le_divergence`: its form on concentric
  balls.
* `TauCeti.PDE.exists_setIntegral_ball_norm_gradient_sq_le_of_forall_testFunction`: the same for
  a solution tested against test functions, with `a` and the datum controlled only on the larger
  ball.
* `TauCeti.PDE.exists_eLpNorm_gradient_ball_le_of_forall_testFunction`: its form in `L²` norms.
* `TauCeti.PDE.exists_setIntegral_ball_norm_gradient_sq_le_sub_setAverage_divergence`: the form
  on concentric balls with the mean of `u` over the larger ball subtracted.
* `TauCeti.PDE.exists_setIntegral_ball_norm_indicator_gradient_sq_le_divergence`: the form on
  concentric balls up to the boundary, for the zero extension of `u ∈ H¹₀(Ω)`.

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

/-- **The Caccioppoli inequality for a right-hand side `f + div F`.** Let `a` be measurable and
uniformly elliptic on `Ω` with constants `0 < λ ≤ Λ`, let `f ∈ L²(Ω)` and `F ∈ L²(Ω; ℝⁿ)`, and let
`u ∈ H¹(Ω)` be a weak solution of `-∂ᵢ(aⁱʲ ∂ⱼu) = f + ∂ᵢFⁱ` in `Ω`, in the sense that
`a(u, v) = ∫_Ω f v - ∫_Ω ⟪F, ∇v⟫` for every `v ∈ H¹₀(Ω)`, with no boundary condition on `u`. Then
for every smooth `ψ` with compact support, either contained in `Ω` or arbitrary when
`u ∈ H¹₀(Ω)`,

`∫_Ω ψ² ‖∇u‖² ≤ 2 ((2Λ/λ)² + 1) ∫_Ω ‖∇ψ‖² u² + (12/λ²) ∫_Ω ψ² ‖F‖² + (4/λ) ∫_Ω ψ² f u`. -/
theorem UniformlyEllipticOn.setIntegral_sq_mul_norm_gradient_sq_le_add_divergence
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (ha : AEStronglyMeasurable a (mu.restrict Omega)) {f : EuclideanSpace ℝ ι → ℝ}
    (hF : MemLp F 2 (mu.restrict Omega)) {u : W1p mu Omega 2}
    (hu : ∀ v : W1p0 mu Omega 2, energyFormH1 a 0 0 u (v : W1p mu Omega 2) =
      ∫ x in Omega, f x * W1p.value (v : W1p mu Omega 2) x ∂mu -
        ∫ x in Omega, ⟪F x, W1p.gradient (v : W1p mu Omega 2) x⟫_ℝ ∂mu)
    {ψ : EuclideanSpace ℝ ι → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hcpt : HasCompactSupport ψ)
    (hts : tsupport ψ ⊆ (Omega : Set (EuclideanSpace ℝ ι)) ∨ u ∈ w1p0Submodule mu Omega 2) :
    ∫ x in Omega, ψ x ^ 2 * ‖W1p.gradient u x‖ ^ 2 ∂mu ≤
      2 * ((2 * Lam / lam) ^ 2 + 1) * ∫ x in Omega, ‖∇ ψ x‖ ^ 2 * W1p.value u x ^ 2 ∂mu
        + 12 / lam ^ 2 * ∫ x in Omega, ψ x ^ 2 * ‖F x‖ ^ 2 ∂mu
        + 4 / lam * ∫ x in Omega, ψ x ^ 2 * f x * W1p.value u x ∂mu := by
  obtain ⟨v, hvalue, hgradv, hstep⟩ :=
    h.exists_setIntegral_sq_mul_norm_gradient_sq_le_energyFormH1 ha u hψ hcpt hts
  -- By the weak equation, the energy is `∫_Ω ψ² f u + ∫_Ω G` with `G = -⟪F, ∇(ψ² u)⟫`.
  set G : EuclideanSpace ℝ ι → ℝ := fun x => -⟪F x, W1p.gradient (v : W1p mu Omega 2) x⟫_ℝ
  have hG : Integrable G (mu.restrict Omega) :=
    (hF.integrable_inner (Lp.memLp (W1p.gradient (v : W1p mu Omega 2)))).neg
  have hGae : ∀ᵐ x ∂mu.restrict Omega, G x = -⟪F x, ψ x • (ψ x • W1p.gradient u x +
      W1p.value u x • ∇ ψ x) + (ψ x * W1p.value u x) • ∇ ψ x⟫_ℝ := by
    filter_upwards [hgradv] with x hx
    simp only [G, hx]
  have hfv : ∫ x in Omega, f x * W1p.value (v : W1p mu Omega 2) x ∂mu =
      ∫ x in Omega, ψ x ^ 2 * f x * W1p.value u x ∂mu := by
    refine integral_congr_ae ?_
    filter_upwards [hvalue] with x hx
    rw [hx]
    ring
  rw [hu v, hfv, sub_eq_add_neg, ← integral_neg] at hstep
  obtain ⟨M, -, hψM, hgradM⟩ := (hψ.of_le (by simp)).exists_abs_le_and_norm_gradient_le hcpt
  -- Young's inequality absorbs the part of the datum term that contains `∇u`.
  have hψ2 : AEStronglyMeasurable (fun x => ψ x ^ 2) (mu.restrict Omega) :=
    (hψ.continuous.pow 2).aestronglyMeasurable
  have hψ2M : ∀ᵐ x ∂mu.restrict Omega, ‖ψ x ^ 2‖ ≤ M ^ 2 := Filter.Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs, abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (hψM x) 2
  have hI1 : Integrable (fun x => ψ x ^ 2 * ‖W1p.gradient u x‖ ^ 2) (mu.restrict Omega) :=
    (Lp.memLp (W1p.gradient u)).norm.integrable_sq.bdd_mul hψ2 hψ2M
  have hI2 : Integrable (fun x => ‖∇ ψ x‖ ^ 2 * W1p.value u x ^ 2) (mu.restrict Omega) :=
    (Lp.memLp (W1p.value u)).integrable_sq.bdd_mul
      ((ContDiff.continuous_gradient hψ (by simp)).norm.pow 2).aestronglyMeasurable (c := M ^ 2)
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

/-- **The Caccioppoli inequality for a datum in divergence form.** Let `a` be measurable and
uniformly elliptic on `Ω` with constants `0 < λ ≤ Λ`, let `F ∈ L²(Ω; ℝⁿ)`, and let `u ∈ H¹(Ω)` be
a weak solution of `-∂ᵢ(aⁱʲ ∂ⱼu) = ∂ᵢFⁱ` in `Ω`, in the sense that `a(u, v) = -∫_Ω ⟪F, ∇v⟫` for
every `v ∈ H¹₀(Ω)`, with no boundary condition on `u`. Then for every smooth `ψ` with compact
support, either contained in `Ω` or arbitrary when `u ∈ H¹₀(Ω)`,

`∫_Ω ψ² ‖∇u‖² ≤ 2 ((2Λ/λ)² + 1) ∫_Ω ‖∇ψ‖² u² + (12/λ²) ∫_Ω ψ² ‖F‖²`.

This is the case `f = 0` of
`TauCeti.PDE.UniformlyEllipticOn.setIntegral_sq_mul_norm_gradient_sq_le_add_divergence`. -/
theorem UniformlyEllipticOn.setIntegral_sq_mul_norm_gradient_sq_le_divergence
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (ha : AEStronglyMeasurable a (mu.restrict Omega)) (hF : MemLp F 2 (mu.restrict Omega))
    {u : W1p mu Omega 2}
    (hu : ∀ v : W1p0 mu Omega 2, energyFormH1 a 0 0 u (v : W1p mu Omega 2) =
      -∫ x in Omega, ⟪F x, W1p.gradient (v : W1p mu Omega 2) x⟫_ℝ ∂mu)
    {ψ : EuclideanSpace ℝ ι → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hcpt : HasCompactSupport ψ)
    (hts : tsupport ψ ⊆ (Omega : Set (EuclideanSpace ℝ ι)) ∨ u ∈ w1p0Submodule mu Omega 2) :
    ∫ x in Omega, ψ x ^ 2 * ‖W1p.gradient u x‖ ^ 2 ∂mu ≤
      2 * ((2 * Lam / lam) ^ 2 + 1) * ∫ x in Omega, ‖∇ ψ x‖ ^ 2 * W1p.value u x ^ 2 ∂mu
        + 12 / lam ^ 2 * ∫ x in Omega, ψ x ^ 2 * ‖F x‖ ^ 2 ∂mu := by
  simpa using h.setIntegral_sq_mul_norm_gradient_sq_le_add_divergence ha (f := 0) hF
    (fun v => by simp [hu v]) hψ hcpt hts

open Filter Metric in
/-- **The Caccioppoli inequality for a right-hand side `f + div F`, on concentric balls.** There
is a constant `C > 0`, depending only on the dimension, such that the following holds for every
additive Haar measure `μ`. Let `a` be measurable and uniformly elliptic on `Ω` with constants
`0 < λ ≤ Λ`, let `f ∈ L²(Ω)` and `F ∈ L²(Ω; ℝⁿ)`, and let `u ∈ H¹(Ω)` satisfy
`a(u, v) = ∫_Ω f v - ∫_Ω ⟪F, ∇v⟫` for every `v ∈ H¹₀(Ω)`. For every pair of balls
`B(x₀, r) ⊆ B(x₀, R) ⊆ Ω` with `r < R`,

`∫_{B(x₀, r)} ‖∇u‖² ≤ 2 ((2Λ/λ)² + 1) (C / (R - r))² ∫_{B(x₀, R)} u²`
`  + (12/λ²) ∫_{B(x₀, R)} ‖F‖² + (4/λ) ∫_{B(x₀, R)} |f u|`. -/
theorem exists_setIntegral_ball_norm_gradient_sq_le_add_divergence :
    ∃ C : ℝ, 0 < C ∧ ∀ {mu : Measure (EuclideanSpace ℝ ι)} [mu.IsAddHaarMeasure]
      {Omega : Opens (EuclideanSpace ℝ ι)} {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {lam Lam : ℝ}
      {f : EuclideanSpace ℝ ι → ℝ} {F : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
      {u : W1p mu Omega 2} {x₀ : EuclideanSpace ℝ ι} {r R : ℝ},
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam →
      AEStronglyMeasurable a (mu.restrict Omega) → MemLp f 2 (mu.restrict Omega) →
      MemLp F 2 (mu.restrict Omega) →
      (∀ v : W1p0 mu Omega 2, energyFormH1 a 0 0 u (v : W1p mu Omega 2) =
        ∫ x in Omega, f x * W1p.value (v : W1p mu Omega 2) x ∂mu -
          ∫ x in Omega, ⟪F x, W1p.gradient (v : W1p mu Omega 2) x⟫_ℝ ∂mu) →
      r < R → ball x₀ R ⊆ (Omega : Set (EuclideanSpace ℝ ι)) →
      ∫ x in ball x₀ r, ‖W1p.gradient u x‖ ^ 2 ∂mu ≤
        2 * ((2 * Lam / lam) ^ 2 + 1) * (C / (R - r)) ^ 2 *
            ∫ x in ball x₀ R, W1p.value u x ^ 2 ∂mu
          + 12 / lam ^ 2 * ∫ x in ball x₀ R, ‖F x‖ ^ 2 ∂mu
          + 4 / lam * ∫ x in ball x₀ R, |f x * W1p.value u x| ∂mu := by
  obtain ⟨C, hC0, hC⟩ := exists_setIntegral_ball_norm_gradient_sq_le_add_setIntegral_of_cutoff
    (ι := ι)
  refine ⟨C, hC0, ?_⟩
  intro mu _ Omega a lam Lam f F u x₀ r R h ha hf hF hu hrR hball
  have hlam := h.pos
  have hfu : Integrable (fun x => f x * W1p.value u x) (mu.restrict Omega) :=
    hf.integrable_mul (Lp.memLp (W1p.value u))
  have hFi : Integrable (fun x => ‖F x‖ ^ 2) (mu.restrict Omega) := hF.norm.integrable_sq
  -- The datum density `g = (12/λ²) ‖F‖² + (4/λ) |f u|`.
  have hloc := hC u (A := 2 * ((2 * Lam / lam) ^ 2 + 1))
    (g := fun x => 12 / lam ^ 2 * ‖F x‖ ^ 2 + 4 / lam * |f x * W1p.value u x|)
    (by positivity) ((hFi.const_mul _).add (hfu.abs.const_mul _))
    (Eventually.of_forall fun x => by positivity) hrR hball fun ψ hψ hcpt hts => by
      obtain ⟨M, -, hψM, -⟩ := (hψ.of_le (by simp)).exists_abs_le_and_norm_gradient_le hcpt
      have hψ2 : AEStronglyMeasurable (fun x => ψ x ^ 2) (mu.restrict Omega) :=
        (hψ.continuous.pow 2).aestronglyMeasurable
      have hψ2M : ∀ᵐ x ∂mu.restrict Omega, ‖ψ x ^ 2‖ ≤ M ^ 2 := Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_pow]
        exact pow_le_pow_left₀ (abs_nonneg _) (hψM x) 2
      have hI3 := hFi.bdd_mul hψ2 hψ2M
      have hI4 := hfu.bdd_mul hψ2 hψ2M
      have hI5 := hfu.abs.bdd_mul hψ2 hψ2M
      refine (h.setIntegral_sq_mul_norm_gradient_sq_le_add_divergence ha hF hu hψ hcpt
        (.inl hts)).trans ?_
      -- Only `f u ≤ |f u|` remains.
      have hmono : ∫ x in Omega, ψ x ^ 2 * f x * W1p.value u x ∂mu ≤
          ∫ x in Omega, ψ x ^ 2 * |f x * W1p.value u x| ∂mu := by
        refine integral_mono (hI4.congr (Eventually.of_forall fun x => by simp only; ring)) hI5
          fun x => ?_
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left (le_abs_self _) (sq_nonneg _)
      simp_rw [mul_add, mul_left_comm (ψ _ ^ 2)]
      rw [integral_add (hI3.const_mul _) (hI5.const_mul _), integral_const_mul,
        integral_const_mul, ← add_assoc]
      gcongr
  have hFB : IntegrableOn (fun x => 12 / lam ^ 2 * ‖F x‖ ^ 2) (ball x₀ R) mu :=
    IntegrableOn.mono_set (hFi.const_mul _) hball
  have hfuB : IntegrableOn (fun x => 4 / lam * |f x * W1p.value u x|) (ball x₀ R) mu :=
    IntegrableOn.mono_set (hfu.abs.const_mul _) hball
  rwa [integral_add hFB hfuB, integral_const_mul, integral_const_mul, ← add_assoc] at hloc

open Filter Metric in
/-- **The Caccioppoli inequality for a datum in divergence form, on concentric balls.** There is
a constant `C > 0`, depending only on the dimension, such that the following holds for every
additive Haar measure `μ`. Let `a` be measurable and uniformly elliptic on `Ω` with constants
`0 < λ ≤ Λ`, let `F ∈ L²(Ω; ℝⁿ)`, and let `u ∈ H¹(Ω)` satisfy `a(u, v) = -∫_Ω ⟪F, ∇v⟫` for every
`v ∈ H¹₀(Ω)`. For every pair of balls `B(x₀, r) ⊆ B(x₀, R) ⊆ Ω` with `r < R`,

`∫_{B(x₀, r)} ‖∇u‖² ≤ 2 ((2Λ/λ)² + 1) (C / (R - r))² ∫_{B(x₀, R)} u² + (12/λ²) ∫_{B(x₀, R)} ‖F‖²`.

This is the case `f = 0` of
`TauCeti.PDE.exists_setIntegral_ball_norm_gradient_sq_le_add_divergence`. -/
theorem exists_setIntegral_ball_norm_gradient_sq_le_divergence :
    ∃ C : ℝ, 0 < C ∧ ∀ {mu : Measure (EuclideanSpace ℝ ι)} [mu.IsAddHaarMeasure]
      {Omega : Opens (EuclideanSpace ℝ ι)} {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {lam Lam : ℝ}
      {F : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {u : W1p mu Omega 2}
      {x₀ : EuclideanSpace ℝ ι} {r R : ℝ},
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam →
      AEStronglyMeasurable a (mu.restrict Omega) → MemLp F 2 (mu.restrict Omega) →
      (∀ v : W1p0 mu Omega 2, energyFormH1 a 0 0 u (v : W1p mu Omega 2) =
        -∫ x in Omega, ⟪F x, W1p.gradient (v : W1p mu Omega 2) x⟫_ℝ ∂mu) →
      r < R → ball x₀ R ⊆ (Omega : Set (EuclideanSpace ℝ ι)) →
      ∫ x in ball x₀ r, ‖W1p.gradient u x‖ ^ 2 ∂mu ≤
        2 * ((2 * Lam / lam) ^ 2 + 1) * (C / (R - r)) ^ 2 *
            ∫ x in ball x₀ R, W1p.value u x ^ 2 ∂mu
          + 12 / lam ^ 2 * ∫ x in ball x₀ R, ‖F x‖ ^ 2 ∂mu := by
  obtain ⟨C, hC0, hC⟩ := exists_setIntegral_ball_norm_gradient_sq_le_add_divergence (ι := ι)
  refine ⟨C, hC0, fun h ha hF hu hrR hball => ?_⟩
  simpa using hC h ha (f := 0) MemLp.zero hF (fun v => by simp [hu v]) hrR hball

open Metric Distributions in
/-- **The Caccioppoli inequality for a datum in divergence form, tested against test functions.**
There is a constant `C > 0`, depending only on the dimension, such that the following holds for
every additive Haar measure `μ`. Let `u ∈ H¹(Ω)` solve `-∂ᵢ(aⁱʲ ∂ⱼu) = -div G` in `Ω` against
test functions, `a(u, φ) = ∫_Ω ⟪G, ∇φ⟫` for every `φ ∈ 𝓓(Ω)`. Let `B(x₀, r) ⊆ B(x₀, R) ⊆ Ω` with
`r < R`, let `a` be measurable and uniformly elliptic with constants `0 < λ ≤ Λ` on `B(x₀, R)`,
and let `G ∈ L²(B(x₀, R))`. Then

`∫_{B(x₀, r)} ‖∇u‖² ≤ 2 ((2Λ/λ)² + 1) (C / (R - r))² ∫_{B(x₀, R)} u² + (12/λ²) ∫_{B(x₀, R)} ‖G‖²`.

Unlike `TauCeti.PDE.exists_setIntegral_ball_norm_gradient_sq_le_divergence`, nothing is assumed of
`a` and `G` outside `B(x₀, R)`: the equation is restricted to that ball, where it holds against
`H¹₀(B(x₀, R))`, by
`TauCeti.PDE.forall_energyFormH1_restrictL_eq_setIntegral_sub_setIntegral_neg_inner`. -/
theorem exists_setIntegral_ball_norm_gradient_sq_le_of_forall_testFunction :
    ∃ C : ℝ, 0 < C ∧ ∀ {mu : Measure (EuclideanSpace ℝ ι)} [mu.IsAddHaarMeasure]
      {Omega : Opens (EuclideanSpace ℝ ι)} {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {lam Lam : ℝ}
      {G : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {u : W1p mu Omega 2}
      {x₀ : EuclideanSpace ℝ ι} {r R : ℝ},
      UniformlyEllipticOn (ball x₀ R) a lam Lam → AEStronglyMeasurable a (mu.restrict (ball x₀ R)) →
      MemLp G 2 (mu.restrict (ball x₀ R)) →
      (∀ φ : 𝓓(Omega, ℝ), energyFormH1 a 0 0 u (W1p.ofTestFunctionₗ mu Omega 2 φ) =
        ∫ x in Omega, ⟪G x, ∇ (φ : EuclideanSpace ℝ ι → ℝ) x⟫_ℝ ∂mu) →
      r < R → ball x₀ R ⊆ (Omega : Set (EuclideanSpace ℝ ι)) →
      ∫ x in ball x₀ r, ‖W1p.gradient u x‖ ^ 2 ∂mu ≤
        2 * ((2 * Lam / lam) ^ 2 + 1) * (C / (R - r)) ^ 2 *
            ∫ x in ball x₀ R, W1p.value u x ^ 2 ∂mu
          + 12 / lam ^ 2 * ∫ x in ball x₀ R, ‖G x‖ ^ 2 ∂mu := by
  obtain ⟨C, hC0, hC⟩ := exists_setIntegral_ball_norm_gradient_sq_le_divergence (ι := ι)
  refine ⟨C, hC0, fun {mu} _ {Omega a lam Lam G u x₀ r R} hell ham hG hu hrR hball => ?_⟩
  set B : Opens (EuclideanSpace ℝ ι) := ⟨ball x₀ R, isOpen_ball⟩
  have hB : B ≤ Omega := hball
  have hcoeff : MemLp (fun x => energyIntegrand (a x) 0 0) ⊤ (mu.restrict B) :=
    memLp_energyIntegrand_of_bounds (beta := 0) (gamma := 0) hell.upper_nonneg ham
      aestronglyMeasurable_const aestronglyMeasurable_const (fun _ hx => hell.upper_bound hx)
      (fun _ _ => by simp) (fun _ _ => by simp)
  -- On `B`, the restriction of `u` solves `-∂ᵢ(aⁱʲ ∂ⱼu) = div F` with `F = -G`, against `H¹₀(B)`.
  have hw (v : W1p0 mu B 2) : energyFormH1 a 0 0 (W1p.restrictL hB u) (v : W1p mu B 2) =
      -∫ x in B, ⟪(-G) x, W1p.gradient (v : W1p mu B 2) x⟫_ℝ ∂mu := by
    simpa using forall_energyFormH1_restrictL_eq_setIntegral_sub_setIntegral_neg_inner hB hcoeff
      (f := 0) (fun φ => by simp [hu φ]) hG MemLp.zero v
  have hcacc := hC (mu := mu) (Omega := B) (u := W1p.restrictL hB u) hell ham hG.neg hw hrR
    subset_rfl
  -- On `B`, the jets of the restriction are those of `u`.
  have e1 : ∫ x in ball x₀ r, ‖W1p.gradient (W1p.restrictL hB u) x‖ ^ 2 ∂mu =
      ∫ x in ball x₀ r, ‖W1p.gradient u x‖ ^ 2 ∂mu := by
    refine integral_congr_ae (ae_restrict_of_ae_restrict_of_subset (ball_subset_ball hrR.le) ?_)
    filter_upwards [W1p.gradient_restrictL_ae hB u] with x hx
    rw [hx]
  have e2 : ∫ x in ball x₀ R, W1p.value (W1p.restrictL hB u) x ^ 2 ∂mu =
      ∫ x in ball x₀ R, W1p.value u x ^ 2 ∂mu := by
    refine integral_congr_ae ?_
    filter_upwards [W1p.value_restrictL_ae hB u] with x hx
    rw [hx]
  simp only [Pi.neg_apply, norm_neg] at hcacc
  rwa [e1, e2] at hcacc

open Metric Distributions in
/-- **The Caccioppoli inequality in `L²` norms, tested against test functions.** There are
constants `α` and `β`, depending only on the dimension, `λ` and `Λ`, such that under the
hypotheses of `TauCeti.PDE.exists_setIntegral_ball_norm_gradient_sq_le_of_forall_testFunction`

`‖∇u‖_{L²(B(x₀, r))} ≤ α (R - r)⁻¹ ‖u‖_{L²(B(x₀, R))} + β ‖G‖_{L²(B(x₀, R))}`.

This is that inequality after taking square roots. -/
theorem exists_eLpNorm_gradient_ball_le_of_forall_testFunction (lam Lam : ℝ) :
    ∃ α β : ℝ, ∀ {mu : Measure (EuclideanSpace ℝ ι)} [mu.IsAddHaarMeasure]
      {Omega : Opens (EuclideanSpace ℝ ι)} {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ}
      {G : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {u : W1p mu Omega 2}
      {x₀ : EuclideanSpace ℝ ι} {r R : ℝ},
      UniformlyEllipticOn (ball x₀ R) a lam Lam → AEStronglyMeasurable a (mu.restrict (ball x₀ R)) →
      MemLp G 2 (mu.restrict (ball x₀ R)) →
      (∀ φ : 𝓓(Omega, ℝ), energyFormH1 a 0 0 u (W1p.ofTestFunctionₗ mu Omega 2 φ) =
        ∫ x in Omega, ⟪G x, ∇ (φ : EuclideanSpace ℝ ι → ℝ) x⟫_ℝ ∂mu) →
      r < R → ball x₀ R ⊆ (Omega : Set (EuclideanSpace ℝ ι)) →
      eLpNorm (W1p.gradient u) 2 (mu.restrict (ball x₀ r)) ≤
        ENNReal.ofReal α * ENNReal.ofReal (R - r)⁻¹ *
            eLpNorm (W1p.value u) 2 (mu.restrict (ball x₀ R)) +
          ENNReal.ofReal β * eLpNorm G 2 (mu.restrict (ball x₀ R)) := by
  obtain ⟨K, hK0, hK⟩ := exists_setIntegral_ball_norm_gradient_sq_le_of_forall_testFunction (ι := ι)
  set c₁ : ℝ := 2 * ((2 * Lam / lam) ^ 2 + 1) with hc₁_def
  set c₂ : ℝ := 12 / lam ^ 2 with hc₂_def
  refine ⟨√c₁ * K, √c₂, fun {mu} _ {Omega a G u x₀ r R} hell ham hG hu hrR hball => ?_⟩
  have hcacc := hK hell ham hG hu hrR hball
  rw [← hc₁_def, ← hc₂_def] at hcacc
  have hgrad : MemLp (W1p.gradient u) 2 (mu.restrict (ball x₀ r)) :=
    (Lp.memLp _).mono_measure
      (Measure.restrict_mono ((ball_subset_ball hrR.le).trans hball) le_rfl)
  have hval : MemLp (W1p.value u) 2 (mu.restrict (ball x₀ R)) :=
    (Lp.memLp _).mono_measure (Measure.restrict_mono hball le_rfl)
  rw [hgrad.eLpNorm_two_eq_ofReal_sqrt_integral, hval.eLpNorm_two_eq_ofReal_sqrt_integral,
    hG.eLpNorm_two_eq_ofReal_sqrt_integral]
  simp only [Real.norm_eq_abs, sq_abs]
  set I₂ := ∫ x in ball x₀ R, W1p.value u x ^ 2 ∂mu
  set I₃ := ∫ x in ball x₀ R, ‖G x‖ ^ 2 ∂mu
  have hc₁ : 0 ≤ c₁ := by positivity
  have hI₂ : 0 ≤ I₂ := integral_nonneg fun _ => by positivity
  have hI₃ : 0 ≤ I₃ := integral_nonneg fun _ => by positivity
  rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity) (by positivity)]
  refine ENNReal.ofReal_le_ofReal (Real.sqrt_le_iff.2 ⟨by positivity, hcacc.trans ?_⟩)
  -- `(√c₁ K (R - r)⁻¹ √I₂ + √c₂ √I₃)² ≥ c₁ (K / (R - r))² I₂ + c₂ I₃`.
  have hA : (√c₁ * K * (R - r)⁻¹ * √I₂) ^ 2 = c₁ * (K / (R - r)) ^ 2 * I₂ := by
    rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt hc₁, Real.sq_sqrt hI₂, div_pow, inv_pow,
      div_eq_mul_inv]
    ring
  have hB : (√c₂ * √I₃) ^ 2 = c₂ * I₃ := by
    rw [mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt hI₃]
  have hcross : 0 ≤ √c₁ * K * (R - r)⁻¹ * √I₂ * (√c₂ * √I₃) := by positivity
  nlinarith [hA, hB, hcross]

open Filter Metric in
/-- **The Caccioppoli inequality for a datum in divergence form, with the mean subtracted.**
There is a constant `C > 0`, depending only on the dimension, such that the following holds for
every additive Haar measure `μ`. Let `a` be measurable and uniformly elliptic on `Ω` with constants
`0 < λ ≤ Λ`, let `F ∈ L²(Ω; ℝⁿ)`, and let `u ∈ H¹(Ω)` satisfy `a(u, v) = -∫_Ω ⟪F, ∇v⟫` for every
`v ∈ H¹₀(Ω)`. For every pair of balls `B(y, r) ⊆ B(y, R) ⊆ Ω` with `r < R`, writing `m` for the
mean of `u` over `B(y, R)`,

`∫_{B(y, r)} ‖∇u‖² ≤ 2 ((2Λ/λ)² + 1) (C / (R - r))² ∫_{B(y, R)} |u - m|²`
`  + (12/λ²) ∫_{B(y, R)} ‖F‖²`.

Constants are not Sobolev functions on `Ω` unless `Ω` has finite measure, so `u - m` is formed on
the ball, where it is again a weak solution of the same equation. -/
theorem exists_setIntegral_ball_norm_gradient_sq_le_sub_setAverage_divergence :
    ∃ C : ℝ, 0 < C ∧ ∀ {mu : Measure (EuclideanSpace ℝ ι)} [mu.IsAddHaarMeasure]
      {Omega : Opens (EuclideanSpace ℝ ι)} {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {lam Lam : ℝ}
      {F : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {u : W1p mu Omega 2}
      {y : EuclideanSpace ℝ ι} {r R : ℝ},
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam →
      AEStronglyMeasurable a (mu.restrict Omega) → MemLp F 2 (mu.restrict Omega) →
      (∀ v : W1p0 mu Omega 2, energyFormH1 a 0 0 u (v : W1p mu Omega 2) =
        -∫ x in Omega, ⟪F x, W1p.gradient (v : W1p mu Omega 2) x⟫_ℝ ∂mu) →
      r < R → ball y R ⊆ (Omega : Set (EuclideanSpace ℝ ι)) →
      ∫ x in ball y r, ‖W1p.gradient u x‖ ^ 2 ∂mu ≤
        2 * ((2 * Lam / lam) ^ 2 + 1) * (C / (R - r)) ^ 2 *
            ∫ x in ball y R, (W1p.value u x - ⨍ z in ball y R, W1p.value u z ∂mu) ^ 2 ∂mu
          + 12 / lam ^ 2 * ∫ x in ball y R, ‖F x‖ ^ 2 ∂mu := by
  obtain ⟨C, hC0, hC⟩ := exists_setIntegral_ball_norm_gradient_sq_le_divergence (ι := ι)
  refine ⟨C, hC0, ?_⟩
  intro mu _ Omega a lam Lam F u y r R h ha hF hu hrR hball
  -- The ball `B = B(y, R)`, as a domain of its own, on which constants are Sobolev functions.
  set B : Opens (EuclideanSpace ℝ ι) := ⟨ball y R, isOpen_ball⟩
  have hB : B ≤ Omega := hball
  have : IsFiniteMeasure (mu.restrict (B : Set (EuclideanSpace ℝ ι))) :=
    isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
  set uB := W1p.restrictL hB u
  set m := ⨍ z in ball y R, W1p.value u z ∂mu
  -- `w = u - m` solves the same equation on `B`.
  set w : W1p mu B 2 := uB + W1p.const (-m)
  have hw : ∀ v : W1p0 mu B 2, energyFormH1 a 0 0 w (v : W1p mu B 2) =
      -∫ x in B, ⟪F x, W1p.gradient (v : W1p mu B 2) x⟫_ℝ ∂mu := fun v => by
    rw [energyFormH1_add_const_left]
    exact energyFormH1_restrictL_eq_neg_setIntegral_inner hB hu v
  have hcacc := hC (mu := mu) (Omega := B) (u := w) (x₀ := y) (r := r) (R := R)
    (h.mono_set hball) (ha.mono_measure (Measure.restrict_mono hball le_rfl))
    (hF.mono_measure (Measure.restrict_mono hball le_rfl)) hw hrR subset_rfl
  -- On `B`, `∇w = ∇u` and `w = u - m`.
  have e1 : ∫ x in ball y r, ‖W1p.gradient w x‖ ^ 2 ∂mu =
      ∫ x in ball y r, ‖W1p.gradient u x‖ ^ 2 ∂mu := by
    refine integral_congr_ae (ae_restrict_of_ae_restrict_of_subset
      (ball_subset_ball hrR.le : ball y r ⊆ ball y R) ?_)
    rw [W1p.gradient_add_const]
    filter_upwards [W1p.gradient_restrictL_ae hB u] with x hx
    rw [hx]
  have e2 : ∫ x in ball y R, W1p.value w x ^ 2 ∂mu =
      ∫ x in ball y R, (W1p.value u x - m) ^ 2 ∂mu := by
    refine integral_congr_ae ?_
    filter_upwards [W1p.value_restrictL_add_const_ae hB u (-m)] with x hx
    rw [hx, sub_eq_add_neg]
  rwa [e1, e2] at hcacc

open Filter Metric in
/-- **The Caccioppoli inequality up to the boundary.** There is `C > 0`, depending only on the
dimension, such that the following holds for every additive Haar measure `μ`. Let `a` be
measurable and uniformly elliptic on `Ω` with constants `0 < λ ≤ Λ`, let `F ∈ L²(Ω; ℝⁿ)`, and let
`u ∈ H¹₀(Ω)` satisfy `a(u, v) = -∫_Ω ⟪F, ∇v⟫` for every `v ∈ H¹₀(Ω)`. Then the zero
extensions `1_Ω u` and `1_Ω ∇u` of `u` and of its gradient satisfy, on every pair of concentric
balls `B(y, r) ⊆ B(y, R)` with `r < R`, which need not lie in `Ω`,

`∫_{B(y, r)} ‖1_Ω ∇u‖² ≤ 2 ((2Λ/λ)² + 1) (C / (R - r))² ∫_{B(y, R)} (1_Ω u)²`
`  + (12/λ²) ∫_{B(y, R)} ‖1_Ω F‖²`. -/
theorem exists_setIntegral_ball_norm_indicator_gradient_sq_le_divergence :
    ∃ C : ℝ, 0 < C ∧ ∀ {mu : Measure (EuclideanSpace ℝ ι)} [mu.IsAddHaarMeasure]
      {Omega : Opens (EuclideanSpace ℝ ι)} {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ}
      {lam Lam : ℝ} {F : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {u : W1p0 mu Omega 2}
      {y : EuclideanSpace ℝ ι} {r R : ℝ},
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam →
      AEStronglyMeasurable a (mu.restrict Omega) → MemLp F 2 (mu.restrict Omega) →
      (∀ v : W1p0 mu Omega 2, energyFormH1 a 0 0 (u : W1p mu Omega 2) (v : W1p mu Omega 2) =
        -∫ x in Omega, ⟪F x, W1p.gradient (v : W1p mu Omega 2) x⟫_ℝ ∂mu) →
      r < R →
      ∫ x in ball y r, ‖(Omega : Set (EuclideanSpace ℝ ι)).indicator
          (W1p.gradient (u : W1p mu Omega 2)) x‖ ^ 2 ∂mu ≤
        2 * ((2 * Lam / lam) ^ 2 + 1) * (C / (R - r)) ^ 2 *
            ∫ x in ball y R, ‖(Omega : Set (EuclideanSpace ℝ ι)).indicator
              (W1p.value (u : W1p mu Omega 2)) x‖ ^ 2 ∂mu
          + 12 / lam ^ 2 *
            ∫ x in ball y R, ‖(Omega : Set (EuclideanSpace ℝ ι)).indicator F x‖ ^ 2 ∂mu := by
  obtain ⟨C, hC0, hC⟩ := exists_setIntegral_ball_norm_gradient_sq_le_add_setIntegral_of_cutoff
    (ι := ι)
  refine ⟨C, hC0, ?_⟩
  intro mu _ Omega a lam Lam F u y r R h ha hF hu hrR
  have hOm : MeasurableSet (Omega : Set (EuclideanSpace ℝ ι)) := Omega.isOpen.measurableSet
  -- The zero extension `u₀ ∈ H¹(ℝⁿ)` of `u`, whose components are `1_Ω u` and `1_Ω ∇u`.
  have hval := W1p0.value_extendByZeroL_top_ae u
  have hgrad := W1p0.gradient_extendByZeroL_top_ae u
  set u₀ : W1p mu ⊤ 2 := (W1p0.extendByZeroL le_top u : W1p mu ⊤ 2)
  have htop : mu.restrict ((⊤ : Opens (EuclideanSpace ℝ ι)) : Set (EuclideanSpace ℝ ι)) = mu := by
    rw [Opens.coe_top, Measure.restrict_univ]
  -- Caccioppoli's inequality for `u` on `Ω`, with a cutoff whose support may meet `∂Ω`, is the
  -- cutoff inequality for `u₀` on the whole space.
  have hF0 : MemLp ((Omega : Set (EuclideanSpace ℝ ι)).indicator F) 2 mu :=
    (memLp_indicator_iff_restrict hOm.nullMeasurableSet).2 hF
  have hloc := hC u₀ (A := 2 * ((2 * Lam / lam) ^ 2 + 1)) (x₀ := y)
    (g := fun x => 12 / lam ^ 2 * ‖(Omega : Set (EuclideanSpace ℝ ι)).indicator F x‖ ^ 2)
    (by positivity) (by simpa only [htop] using hF0.norm.integrable_sq.const_mul _)
    (Eventually.of_forall fun x => by positivity) hrR (by simp) fun ψ hψ hcpt _ => by
      have hcacc :=
        h.setIntegral_sq_mul_norm_gradient_sq_le_divergence ha hF hu hψ hcpt (.inr u.property)
      have e1 := integral_eq_setIntegral_of_ae_eq_indicator hOm.nullMeasurableSet
        (fun x v => ψ x ^ 2 * ‖v‖ ^ 2) (by simp) hgrad
      have e2 := integral_eq_setIntegral_of_ae_eq_indicator hOm.nullMeasurableSet
        (fun x v => ‖∇ ψ x‖ ^ 2 * v ^ 2) (by simp) hval
      have e3 : ∫ x, ψ x ^ 2 *
            (12 / lam ^ 2 * ‖(Omega : Set (EuclideanSpace ℝ ι)).indicator F x‖ ^ 2) ∂mu =
          12 / lam ^ 2 * ∫ x in Omega, ψ x ^ 2 * ‖F x‖ ^ 2 ∂mu := by
        rw [integral_eq_setIntegral_of_ae_eq_indicator hOm.nullMeasurableSet
          (fun x v => ψ x ^ 2 * (12 / lam ^ 2 * ‖v‖ ^ 2)) (by simp) .rfl, ← integral_const_mul]
        exact integral_congr_ae (.of_forall fun x => by ring)
      simp only [htop]
      rw [e1, e2, e3]
      exact hcacc
  have e1 : ∫ x in ball y r, ‖W1p.gradient u₀ x‖ ^ 2 ∂mu =
      ∫ x in ball y r, ‖(Omega : Set (EuclideanSpace ℝ ι)).indicator
        (W1p.gradient (u : W1p mu Omega 2)) x‖ ^ 2 ∂mu :=
    integral_congr_ae (ae_restrict_of_ae (hgrad.mono fun x hx => by simp only [hx]))
  have e2 : ∫ x in ball y R, W1p.value u₀ x ^ 2 ∂mu =
      ∫ x in ball y R, ‖(Omega : Set (EuclideanSpace ℝ ι)).indicator
        (W1p.value (u : W1p mu Omega 2)) x‖ ^ 2 ∂mu :=
    integral_congr_ae (ae_restrict_of_ae (hval.mono fun x hx => by simp [hx]))
  rwa [e1, e2, integral_const_mul] at hloc

end PDE

end TauCeti
