/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.Interior.Basic
import TauCeti.Analysis.PDE.Caccioppoli.LowerOrder
import TauCeti.MeasureTheory.Function.Lp.Restriction
import TauCeti.Topology.Instances.Matrix

/-!
# The interior `H²` estimate in terms of the forcing and the solution

Let `a` be uniformly elliptic and Lipschitz on `B(x₀, 4 r)`, let `b, c` be bounded there, and let
`u ∈ H¹(Ω)` be a weak solution of

`-∂ᵢ(aⁱʲ ∂ⱼu) + ⟨b, ∇u⟩ + c u = f` in `Ω ⊇ B(x₀, 4 r)`, with `f ∈ L²(Ω)`.

The interior estimate on balls
(`TauCeti.PDE.UniformlyEllipticOn.exists_norm_le_hasWeakLineDerivOn_gradient_ball`) bounds the
second weak derivatives of `u` on `B(x₀, r)` by the `L²` norms of `f`, `∇u` and `u` on
`B(x₀, 2 r)`. This file removes `∇u` from the right-hand side: by Caccioppoli's inequality with
lower-order terms (`TauCeti.PDE.exists_sq_toReal_eLpNorm_gradient_ball_le`), the gradient on
`B(x₀, 2 r)` is bounded by `f` and `u` on `B(x₀, 4 r)`. The result is the classical
form of the interior estimate,

`‖D²u‖_{L²(B(x₀, r))} ≤ C (‖f‖_{L²(B(x₀, 4 r))} / λ + ‖u‖_{L²(B(x₀, 4 r))} / r²)`,

with `C` depending only on the dimension and on a bound `M` for the dimensionless coefficient
parameters `Λ / λ`, `r β / λ`, `r K / λ` and `r² γ / λ`, where `K` is the Lipschitz constant of
`a` and `β`, `γ` bound `b`, `c`. It is quantitative in the solution as well as in the data, as it
must be: the equation with `f = 0` is invariant under `u ↦ t u`. Together with that Caccioppoli
inequality, which bounds `‖∇u‖_{L²(B(x₀, r))}` in the same terms, it bounds the full
`H²(B(x₀, r))` norm of `u` by `f` and `u` alone.

## Main declarations

* `TauCeti.PDE.UniformlyEllipticOn.exists_norm_le_eLpNorm_value_hasWeakLineDerivOn_gradient_ball`:
  **the interior `H²` estimate on balls** in terms of the forcing and the solution.

## References

* L. C. Evans, *Partial Differential Equations*, §6.3.1, Theorem 1.
* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Theorem 8.8.
-/

public section

open MeasureTheory Filter Set TopologicalSpace
open scoped ENNReal NNReal InnerProductSpace

namespace TauCeti

namespace PDE

variable {ι : Type*} [Fintype ι]

/-- The coefficient of `‖u‖²` in Caccioppoli's inequality from `B(x₀, 2 r)` to `B(x₀, 4 r)` is at
most `((Q + 1) / r)²`, with `Q = 2 M² C² + 4 M² + 4 M + 1/8`, under the dimensionless bounds
`Λ, r β, r² γ ≤ M λ`. -/
private theorem le_sq_div_of_le_mul {Lam lam β γ r C M : ℝ} (hlam : 0 < lam) (hr : 0 < r)
    (hΛ0 : 0 ≤ Lam) (hβ0 : 0 ≤ β) (hΛ : Lam ≤ M * lam) (hβ : r * β ≤ M * lam)
    (hγ : r ^ 2 * γ ≤ M * lam) :
    2 * (2 * Lam / lam) ^ 2 * (C / (4 * r - 2 * r)) ^ 2 + (2 * β / lam) ^ 2 + 4 * γ / lam +
        2 / (4 * r) ^ 2 ≤ ((2 * M ^ 2 * C ^ 2 + 4 * M ^ 2 + 4 * M + 1 / 8 + 1) / r) ^ 2 := by
  have hM : 0 ≤ M := nonneg_of_mul_nonneg_left (hΛ0.trans hΛ) hlam
  have h1 : Lam / lam ≤ M := by rw [div_le_iff₀ hlam]; linarith
  have h2 : r * β / lam ≤ M := by rw [div_le_iff₀ hlam]; linarith
  have h3 : r ^ 2 * γ / lam ≤ M := by rw [div_le_iff₀ hlam]; linarith
  have he : 2 * (2 * Lam / lam) ^ 2 * (C / (4 * r - 2 * r)) ^ 2 + (2 * β / lam) ^ 2 +
      4 * γ / lam + 2 / (4 * r) ^ 2 = (2 * (Lam / lam) ^ 2 * C ^ 2 + 4 * (r * β / lam) ^ 2 +
        4 * (r ^ 2 * γ / lam) + 1 / 8) / r ^ 2 := by
    field_simp
    ring
  have hQ : 2 * (Lam / lam) ^ 2 * C ^ 2 + 4 * (r * β / lam) ^ 2 + 4 * (r ^ 2 * γ / lam) + 1 / 8 ≤
      2 * M ^ 2 * C ^ 2 + 4 * M ^ 2 + 4 * M + 1 / 8 := by
    have : 0 ≤ Lam / lam := by positivity
    have : 0 ≤ r * β / lam := by positivity
    gcongr
  rw [he, div_pow (_ + 1) r 2, div_le_div_iff_of_pos_right (by positivity)]
  have : 0 ≤ 2 * M ^ 2 * C ^ 2 + 4 * M ^ 2 + 4 * M + 1 / 8 := by positivity
  nlinarith

/-- Caccioppoli's inequality from `B(x₀, 2 r)` to `B(x₀, 4 r)`, in terms of the norms `G₂` of
`∇u`, and `U₄`, `F₄` of `u` and `f`, gives `G₂ ≤ (Q + 1) U₄ / r + 6 r F₄ / λ` under the
dimensionless bounds `Λ, r β, r² γ ≤ M λ`. -/
private theorem le_div_mul_add_mul_of_sq_le {Lam lam β γ r C M G₂ U₄ F₄ : ℝ} (hlam : 0 < lam)
    (hr : 0 < r) (hΛ0 : 0 ≤ Lam) (hβ0 : 0 ≤ β) (hG₂ : 0 ≤ G₂) (hU₄ : 0 ≤ U₄) (hF₄ : 0 ≤ F₄)
    (hΛ : Lam ≤ M * lam) (hβ : r * β ≤ M * lam) (hγ : r ^ 2 * γ ≤ M * lam)
    (hcacc : G₂ ^ 2 ≤ (2 * (2 * Lam / lam) ^ 2 * (C / (4 * r - 2 * r)) ^ 2 + (2 * β / lam) ^ 2 +
      4 * γ / lam + 2 / (4 * r) ^ 2) * U₄ ^ 2 + 2 * (4 * r / lam) ^ 2 * F₄ ^ 2) :
    G₂ ≤ (2 * M ^ 2 * C ^ 2 + 4 * M ^ 2 + 4 * M + 1 / 8 + 1) / r * U₄ + 6 * r / lam * F₄ := by
  have hM : 0 ≤ M := nonneg_of_mul_nonneg_left (hΛ0.trans hΛ) hlam
  have hP := le_sq_div_of_le_mul (C := C) hlam hr hΛ0 hβ0 hΛ hβ hγ
  set Q := 2 * M ^ 2 * C ^ 2 + 4 * M ^ 2 + 4 * M + 1 / 8 + 1
  have h6 : 2 * (4 * r / lam) ^ 2 ≤ (6 * r / lam) ^ 2 := by
    rw [div_pow, div_pow, ← mul_div_assoc, div_le_div_iff_of_pos_right (by positivity)]
    nlinarith
  refine (pow_le_pow_iff_left₀ hG₂ (by positivity) two_ne_zero).1 ?_
  nlinarith [mul_le_mul_of_nonneg_right hP (sq_nonneg U₄),
    mul_le_mul_of_nonneg_right h6 (sq_nonneg F₄),
    mul_nonneg (mul_nonneg (by positivity : (0 : ℝ) ≤ Q / r) hU₄)
      (mul_nonneg (by positivity : (0 : ℝ) ≤ 6 * r / lam) hF₄)]

/-- The arithmetic of the interior `H²` estimate in terms of the forcing and the solution: the
interior estimate on balls with norms `F₂`, `G₂`, `U₂` of `f`, `∇u`, `u` on `B(x₀, 2 r)`, and
Caccioppoli's inequality bounding `G₂` by the norms `F₄`, `U₄` on `B(x₀, 4 r)`, give a bound by
`F₄ / λ + U₄ / r²` alone. -/
private theorem le_mul_div_add_div_of_le {X Y F₂ F₄ G₂ U₂ U₄ Lam lam β γ r K C₁ C₂ M : ℝ}
    (hlam : 0 < lam) (hr : 0 < r) (hΛ0 : 0 ≤ Lam) (hβ0 : 0 ≤ β)
    (hC₁ : 0 ≤ C₁) (hY : 0 ≤ Y) (hG₂ : 0 ≤ G₂) (hU₂ : 0 ≤ U₂) (hF₄ : 0 ≤ F₄)
    (hΛ : Lam ≤ M * lam) (hβ : r * β ≤ M * lam) (hK : r * K ≤ M * lam) (hγ : r ^ 2 * γ ≤ M * lam)
    (hF : F₂ ≤ F₄) (hU : U₂ ≤ U₄)
    (hX : X ≤ Y * (F₂ + (β + 2 * K + C₁ * Lam / r) * G₂ +
      (γ + C₁ * K / r + C₁ * Lam / r ^ 2) * U₂) / lam)
    (hcacc : G₂ ^ 2 ≤ (2 * (2 * Lam / lam) ^ 2 * (C₂ / (4 * r - 2 * r)) ^ 2 + (2 * β / lam) ^ 2 +
      4 * γ / lam + 2 / (4 * r) ^ 2) * U₄ ^ 2 + 2 * (4 * r / lam) ^ 2 * F₄ ^ 2) :
    X ≤ (1 + 6 * ((3 + C₁) * M) + ((3 + C₁) * M * (2 * M ^ 2 * C₂ ^ 2 + 4 * M ^ 2 + 4 * M +
      1 / 8 + 1) + (1 + 2 * C₁) * M)) * Y * (F₄ / lam + U₄ / r ^ 2) := by
  have hM : 0 ≤ M := nonneg_of_mul_nonneg_left (hΛ0.trans hΛ) hlam
  set Q := 2 * M ^ 2 * C₂ ^ 2 + 4 * M ^ 2 + 4 * M + 1 / 8 + 1
  have hU₄ : 0 ≤ U₄ := hU₂.trans hU
  have hG := le_div_mul_add_mul_of_sq_le hlam hr hΛ0 hβ0 hG₂ hU₄ hF₄ hΛ hβ hγ hcacc
  -- The coefficients of the gradient and value terms are at most `m₁ λ / r` and `m₂ λ / r²`.
  set m₁ := (3 + C₁) * M
  set m₂ := (1 + 2 * C₁) * M
  have hA₁ : (β + 2 * K + C₁ * Lam / r) * G₂ ≤ m₁ * Q * lam * (U₄ / r ^ 2) + 6 * m₁ * F₄ := by
    have : β + 2 * K + C₁ * Lam / r ≤ m₁ * lam / r := by
      rw [le_div_iff₀ hr, add_mul, add_mul, div_mul_cancel₀ _ hr.ne']
      nlinarith [mul_le_mul_of_nonneg_left hΛ hC₁]
    calc (β + 2 * K + C₁ * Lam / r) * G₂ ≤ m₁ * lam / r * G₂ :=
          mul_le_mul_of_nonneg_right this hG₂
      _ ≤ m₁ * lam / r * (Q / r * U₄ + 6 * r / lam * F₄) :=
          mul_le_mul_of_nonneg_left hG (by positivity)
      _ = _ := by field_simp
  have hA₂ : (γ + C₁ * K / r + C₁ * Lam / r ^ 2) * U₂ ≤ m₂ * lam * (U₄ / r ^ 2) := by
    have : γ + C₁ * K / r + C₁ * Lam / r ^ 2 ≤ m₂ * lam / r ^ 2 := by
      rw [le_div_iff₀ (by positivity)]
      have e : (γ + C₁ * K / r + C₁ * Lam / r ^ 2) * r ^ 2 =
          r ^ 2 * γ + C₁ * (r * K) + C₁ * Lam := by
        field_simp
      rw [e]
      nlinarith [mul_le_mul_of_nonneg_left hΛ hC₁, mul_le_mul_of_nonneg_left hK hC₁]
    calc (γ + C₁ * K / r + C₁ * Lam / r ^ 2) * U₂ ≤ m₂ * lam / r ^ 2 * U₂ :=
          mul_le_mul_of_nonneg_right this hU₂
      _ ≤ m₂ * lam / r ^ 2 * U₄ := mul_le_mul_of_nonneg_left hU (by positivity)
      _ = _ := by ring
  have hsum : (F₂ + (β + 2 * K + C₁ * Lam / r) * G₂ + (γ + C₁ * K / r + C₁ * Lam / r ^ 2) * U₂)
      / lam ≤ (1 + 6 * m₁ + (m₁ * Q + m₂)) * (F₄ / lam + U₄ / r ^ 2) := by
    rw [div_le_iff₀ hlam]
    have e : (1 + 6 * m₁ + (m₁ * Q + m₂)) * (F₄ / lam + U₄ / r ^ 2) * lam =
        F₄ + 6 * m₁ * F₄ + m₁ * Q * lam * (U₄ / r ^ 2) + m₂ * lam * (U₄ / r ^ 2) +
          (m₁ * Q + m₂) * F₄ + (1 + 6 * m₁) * lam * (U₄ / r ^ 2) := by
      field_simp
      ring
    rw [e]
    have h₁ : 0 ≤ (m₁ * Q + m₂) * F₄ := by positivity
    have h₂ : 0 ≤ (1 + 6 * m₁) * lam * (U₄ / r ^ 2) := by positivity
    linarith
  calc X ≤ Y * ((F₂ + (β + 2 * K + C₁ * Lam / r) * G₂ +
        (γ + C₁ * K / r + C₁ * Lam / r ^ 2) * U₂) / lam) := by rwa [mul_div_assoc] at hX
    _ ≤ Y * ((1 + 6 * m₁ + (m₁ * Q + m₂)) * (F₄ / lam + U₄ / r ^ 2)) :=
        mul_le_mul_of_nonneg_left hsum hY
    _ = _ := by ring

/-- **The interior `H²` estimate on balls, in terms of the forcing and the solution** (Evans,
§6.3.1, Theorem 1; Gilbarg–Trudinger, Theorem 8.8). Fix `M`. There is a constant `C`, depending
only on the dimension `n` and on `M`, with the following property. Let `a` be uniformly elliptic
on `B(x₀, 4 r) ⊆ Ω` with constants `λ ≤ Λ`, with `x ↦ a(x)` `K`-Lipschitz there in the operator
norm of its bilinear forms, let `b, c ∈ L∞(Ω)` with `‖b‖ ≤ β` and `|c| ≤ γ` almost everywhere on
`B(x₀, 4 r)`, and suppose that the dimensionless coefficient parameters are bounded:

`Λ ≤ M λ`, `r β ≤ M λ`, `r K ≤ M λ`, `r² γ ≤ M λ`.

Let `u ∈ H¹(Ω)` be a weak solution of

`-∂ᵢ(aⁱʲ ∂ⱼu) + ⟨b, ∇u⟩ + c u = f` in `Ω`, with `f ∈ L²(Ω)`

and no boundary condition. Then on `B(x₀, r)` every derivative `∂_y u` has a weak derivative in
every direction `w`, with

`‖∂_w ∂_y u‖_{L²(B(x₀, r))} ≤ C ‖y‖ ‖w‖ (‖f‖ / λ + ‖u‖ / r²)`,

the norms on the right being those of `L²(B(x₀, 4 r))`. Unlike
`TauCeti.PDE.UniformlyEllipticOn.exists_norm_le_hasWeakLineDerivOn_gradient_ball`, the right-hand
side does not involve `∇u`. The estimate is invariant under the dilations `x ↦ x₀ + r x` and under
`(a, b, c, f) ↦ (a, b, c, f) / λ`. No sign of `c`, smallness of `b` or regularity of `∂Ω` is
assumed. -/
theorem UniformlyEllipticOn.exists_norm_le_eLpNorm_value_hasWeakLineDerivOn_gradient_ball
    [DecidableEq ι] (M : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (mu : Measure (EuclideanSpace ℝ ι)) [mu.IsAddHaarMeasure]
      ⦃Omega : Opens (EuclideanSpace ℝ ι)⦄ ⦃a : EuclideanSpace ℝ ι → Matrix ι ι ℝ⦄
      ⦃b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι⦄ ⦃c : EuclideanSpace ℝ ι → ℝ⦄
      ⦃x₀ : EuclideanSpace ℝ ι⦄ ⦃r lam Lam β γ : ℝ⦄ ⦃K : ℝ≥0⦄
      ⦃f : Lp ℝ 2 (mu.restrict Omega)⦄ ⦃u : W1p mu Omega 2⦄,
      0 < r → Metric.ball x₀ (4 * r) ⊆ Omega →
      UniformlyEllipticOn (Metric.ball x₀ (4 * r)) a lam Lam →
      LipschitzOnWith K (fun x => matrixBilinearForm (a x)) (Metric.ball x₀ (4 * r)) →
      MemLp b ⊤ (mu.restrict Omega) → MemLp c ⊤ (mu.restrict Omega) →
      (∀ᵐ x ∂mu.restrict (Metric.ball x₀ (4 * r)), ‖b x‖ ≤ β) →
      (∀ᵐ x ∂mu.restrict (Metric.ball x₀ (4 * r)), |c x| ≤ γ) →
      Lam ≤ M * lam → r * β ≤ M * lam → r * K ≤ M * lam → r ^ 2 * γ ≤ M * lam →
      (∀ v : W1p0 mu Omega 2, energyFormH1 a b c u (v : W1p mu Omega 2) =
        ∫ x in Omega, f x * W1p.value (v : W1p mu Omega 2) x ∂mu) →
      ∀ y w : EuclideanSpace ℝ ι, ∃ G : Lp ℝ 2 (mu.restrict (Metric.ball x₀ r)),
        ‖G‖ ≤ C * ‖y‖ * ‖w‖ *
          ((eLpNorm f 2 (mu.restrict (Metric.ball x₀ (4 * r)))).toReal / lam +
            (eLpNorm (W1p.value u) 2 (mu.restrict (Metric.ball x₀ (4 * r)))).toReal / r ^ 2) ∧
        HasWeakLineDerivOn mu ⟨Metric.ball x₀ r, Metric.isOpen_ball⟩
          (fun x => ⟪W1p.gradient u x, y⟫_ℝ) G w := by
  obtain ⟨C₁, hC₁, hball⟩ :=
    UniformlyEllipticOn.exists_norm_le_hasWeakLineDerivOn_gradient_ball (ι := ι)
  obtain ⟨C₂, hcacc⟩ := exists_sq_toReal_eLpNorm_gradient_ball_le (ι := ι)
  set M' := max M 0
  refine ⟨1 + 6 * ((3 + C₁) * M') + ((3 + C₁) * M' * (2 * M' ^ 2 * C₂ ^ 2 + 4 * M' ^ 2 +
    4 * M' + 1 / 8 + 1) + (1 + 2 * C₁) * M'), by positivity, ?_⟩
  intro mu _ Omega a b c x₀ r lam Lam β γ K f u hr hΩ ha hK hb hc hβ hγ hMΛ hMβ hMK hMγ hu y w
  have hlam := ha.pos
  have hMlam : M * lam ≤ M' * lam := mul_le_mul_of_nonneg_right (le_max_left _ _) hlam.le
  -- The ball has positive measure, so the almost everywhere bound forces `0 ≤ β`.
  have : (ae (mu.restrict (Metric.ball x₀ (4 * r)))).NeBot :=
    ae_restrict_neBot.2 (Metric.measure_ball_pos mu x₀ (by positivity)).ne'
  have hβ0 : 0 ≤ β := let ⟨_, hx⟩ := hβ.exists; (norm_nonneg _).trans hx
  have h24 : Metric.ball x₀ (2 * r) ⊆ Metric.ball x₀ (4 * r) :=
    Metric.ball_subset_ball (by linarith)
  -- The interior estimate on `B(x₀, r)`, with the norms of `f`, `∇u` and `u` on `B(x₀, 2 r)`.
  obtain ⟨G, hG, hGd⟩ := hball mu hr (h24.trans hΩ) (ha.mono_set h24) (hK.mono h24) hb hc
    (ae_restrict_of_ae_restrict_of_subset h24 hβ) (ae_restrict_of_ae_restrict_of_subset h24 hγ)
    hu y w
  refine ⟨G, ?_, hGd⟩
  -- Caccioppoli's inequality bounds `∇u` on `B(x₀, 2 r)` by `u` and `f` on `B(x₀, 4 r)`.
  have hcU := hcacc mu (r := 2 * r) (by positivity) (by linarith) hΩ ha
    ((continuousOn_of_continuousOn_matrixBilinearForm hK.continuousOn).aestronglyMeasurable
      Metric.isOpen_ball.measurableSet) hb hc hβ hγ hu
  rw [mul_assoc _ ‖y‖]
  exact le_mul_div_add_div_of_le hlam hr ha.upper_nonneg hβ0 hC₁ (by positivity)
    ENNReal.toReal_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg (hMΛ.trans hMlam)
    (hMβ.trans hMlam) (hMK.trans hMlam) (hMγ.trans hMlam) (Lp.toReal_eLpNorm_restrict_mono f h24 hΩ)
    (Lp.toReal_eLpNorm_restrict_mono _ h24 hΩ) hG hcU

end PDE

end TauCeti
