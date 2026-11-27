/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.MetricSpace.Thickening
public import TauCeti.Analysis.PDE.Regularity.Interior.Basic
import TauCeti.Analysis.PDE.Caccioppoli.LowerOrder
import TauCeti.Analysis.Sobolev.WeakDeriv.Local
import TauCeti.MeasureTheory.Function.Lp.Restriction
import TauCeti.MeasureTheory.Function.LpSeminorm.Ball
import TauCeti.Topology.Instances.Matrix

/-!
# The interior `H²` estimate in terms of the forcing and the solution

Let `a` be uniformly elliptic and Lipschitz on `B(x₀, 4 r)`, let `b, c ∈ L∞(Ω)` with `‖b‖ ≤ β`
and `|c| ≤ γ` on `B(x₀, 4 r)`, and let `u ∈ H¹(Ω)` be a weak solution of

`-∂ᵢ(aⁱʲ ∂ⱼu) + ⟨b, ∇u⟩ + c u = f` in `Ω ⊇ B(x₀, 4 r)`, with `f ∈ L²(Ω)`.

The interior estimate on balls
(`TauCeti.PDE.UniformlyEllipticOn.exists_norm_le_hasWeakLineDerivOn_gradient_ball`) bounds the
second weak derivatives of `u` on `B(x₀, r)` by the `L²` norms of `f`, `∇u` and `u` on
`B(x₀, 2 r)`. This file removes `∇u` from the right-hand side: by Caccioppoli's inequality with
lower-order terms (`TauCeti.PDE.exists_sq_toReal_eLpNorm_gradient_ball_le_lowerOrder`), the
gradient on `B(x₀, 2 r)` is bounded by `f` and `u` on `B(x₀, 4 r)`. The result is the classical
form of the interior estimate,

`‖D²u‖_{L²(B(x₀, r))} ≤ C (‖f‖_{L²(B(x₀, 4 r))} / λ + ‖u‖_{L²(B(x₀, 4 r))} / r²)`,

with `C` depending only on the dimension and on a bound `M` for the dimensionless coefficient
parameters `Λ / λ`, `r β / λ`, `r K / λ` and `r² γ / λ`, where `K` is the Lipschitz constant of
`a` and `β`, `γ` bound `b`, `c`. It is quantitative in the solution as well as in the data, as it
must be: the equation with `f = 0` is invariant under `u ↦ t u`. Together with that Caccioppoli
inequality, which bounds `‖∇u‖_{L²(B(x₀, r))}` in the same terms, it bounds the full
`H²(B(x₀, r))` norm of `u` by `f` and `u` alone.

The same bounds hold on every open set `V` at distance at least `δ` from the boundary, in the sense
that its `δ`-thickening `V_δ`, the points at distance less than `δ` from `V`, lies in `Ω`:

`‖D²u‖_{L²(V)} ≤ C (‖f‖ / λ + ‖u‖ / δ²)` and `‖∇u‖_{L²(V)} ≤ C (δ ‖f‖ / λ + ‖u‖ / δ)`,

with norms on `V_δ` on the right and `C` depending only on the dimension and on a bound for the
dimensionless parameters `Λ / λ`, `δ β / λ`, `δ K / λ` and `δ² γ / λ`. Together they bound the
`W^{2,2}(V)` norm of `u`: this is the classical estimate
`‖u‖_{H²(V)} ≤ C (‖f‖_{L²(Ω)} + ‖u‖_{L²(Ω)})`, with the dependence on `dist(V, ∂Ω)` explicit. `V`
need not be bounded. The estimates on the balls `B(z, r)` of a fixed radius `r ∼ δ` that meet `V`
are averaged over their centres (`TauCeti.eLpNorm_restrict_le_of_forall_ball_inter_nonempty`),
which replaces a covering of `V` by balls with bounded overlap, and the local second derivatives
on these balls glue to weak derivatives on `V` (`TauCeti.exists_hasWeakLineDerivOn_iSup`).

## Main declarations

* `TauCeti.PDE.UniformlyEllipticOn.exists_norm_le_eLpNorm_value_hasWeakLineDerivOn_gradient_ball`:
  **the interior `H²` estimate on balls** in terms of the forcing and the solution.
* `TauCeti.PDE.exists_toReal_eLpNorm_gradient_ball_le_eLpNorm_value`: Caccioppoli's inequality on
  balls in dimensionless form, `‖∇u‖_{L²(B(x₀, r))} ≤ C (‖u‖ / r + r ‖f‖ / λ)`.
* `TauCeti.PDE.exists_toReal_eLpNorm_gradient_le_of_thickening`: the interior gradient
  estimate on a set at distance `δ` from the boundary.
* **The interior `H²` estimate on a set at distance `δ` from the boundary**, in the
  `TauCeti.PDE` namespace:
  `UniformlyEllipticOn.exists_norm_le_eLpNorm_value_hasWeakLineDerivOn_gradient_of_thickening`.
* `TauCeti.PDE.UniformlyEllipticOn.exists_lowerOrder_eq_restrictL_and_norm_le_of_thickening`:
  the same estimate in the norm of `W^{2,2}(V)`.

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
  obtain ⟨C₂, hcacc⟩ := exists_sq_toReal_eLpNorm_gradient_ball_le_lowerOrder (ι := ι)
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
      Metric.isOpen_ball.measurableSet)
    (hb.aestronglyMeasurable.mono_measure (Measure.restrict_mono hΩ le_rfl))
    (hc.aestronglyMeasurable.mono_measure (Measure.restrict_mono hΩ le_rfl)) hβ hγ hu
  rw [mul_assoc _ ‖y‖]
  exact le_mul_div_add_div_of_le hlam hr ha.upper_nonneg hβ0 hC₁ (by positivity)
    ENNReal.toReal_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg (hMΛ.trans hMlam)
    (hMβ.trans hMlam) (hMK.trans hMlam) (hMγ.trans hMlam) (Lp.toReal_eLpNorm_restrict_mono f h24 hΩ)
    (Lp.toReal_eLpNorm_restrict_mono _ h24 hΩ) hG hcU

/-! ### The interior estimates on a set at positive distance from the boundary -/

/-- If `δ t ≤ m` and `0 ≤ m`, then `r t ≤ m` for `0 ≤ r ≤ δ`, whatever the sign of `t`. -/
private theorem mul_le_of_mul_le_of_le {r δ t m : ℝ} (hr : 0 ≤ r) (hrδ : r ≤ δ)
    (h : δ * t ≤ m) (hm : 0 ≤ m) : r * t ≤ m := by
  rcases le_total 0 t with ht | ht <;> nlinarith

/-- A ball `B(y, r)` that meets `V` has its enlargement `B(y, κ r)` in the `δ`-thickening of `V`
when `(κ + 1) r ≤ δ`. -/
private theorem ball_mul_subset_thickening {V : Set (EuclideanSpace ℝ ι)} {y : EuclideanSpace ℝ ι}
    {r κ δ : ℝ} (hy : (Metric.ball y r ∩ V).Nonempty) (h : (κ + 1) * r ≤ δ) :
    Metric.ball y (κ * r) ⊆ Metric.thickening δ V := by
  obtain ⟨x, hxy, hxV⟩ := hy
  refine (Metric.ball_subset_ball' ?_).trans (Metric.ball_subset_thickening hxV δ)
  rw [dist_comm]
  linarith [Metric.mem_ball.1 hxy]

/-- A real bound `X ≤ c₁ A + c₂ B` between finite extended reals, with `c₁, c₂ ≥ 0`, in the form
`X ≤ ofReal c₁ * A + ofReal c₂ * B` that the averaging over balls consumes. -/
private theorem le_ofReal_mul_add_ofReal_mul_of_toReal_le {X A B : ℝ≥0∞} {c₁ c₂ : ℝ}
    (hX : X ≠ ⊤) (hA : A ≠ ⊤) (hB : B ≠ ⊤) (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂)
    (h : X.toReal ≤ c₁ * A.toReal + c₂ * B.toReal) :
    X ≤ ENNReal.ofReal c₁ * A + ENNReal.ofReal c₂ * B := by
  rw [← ENNReal.ofReal_toReal hX, ← ENNReal.ofReal_toReal hA, ← ENNReal.ofReal_toReal hB,
    ← ENNReal.ofReal_mul hc₁, ← ENNReal.ofReal_mul hc₂,
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  exact ENNReal.ofReal_le_ofReal h

/-- The output `2 κ ^ n (c₁ A + c₂ B)` of the averaging over balls, with `A`, `B` finite, is at
most `ofReal X` for every real `X ≥ 2 κ ^ n (c₁ A + c₂ B)`. -/
private theorem two_mul_ofReal_pow_mul_add_le {A B : ℝ≥0∞} {κ c₁ c₂ X : ℝ} {n : ℕ}
    (hA : A ≠ ⊤) (hB : B ≠ ⊤) (hκ : 0 ≤ κ) (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂)
    (h : 2 * κ ^ n * (c₁ * A.toReal + c₂ * B.toReal) ≤ X) :
    2 * ENNReal.ofReal κ ^ n * (ENNReal.ofReal c₁ * A + ENNReal.ofReal c₂ * B) ≤
      ENNReal.ofReal X := by
  rw [← ENNReal.ofReal_toReal hA, ← ENNReal.ofReal_toReal hB, ← ENNReal.ofReal_mul hc₁,
    ← ENNReal.ofReal_mul hc₂, ← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_pow hκ, ← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul zero_le_two,
    ← ENNReal.ofReal_mul (by positivity)]
  exact ENNReal.ofReal_le_ofReal h

/-- The arithmetic of the averaged gradient estimate on a set, with balls of radius `δ / 3`. -/
private theorem two_mul_two_pow_mul_add_le {C₀ U F lam δ : ℝ} (n : ℕ) (hC₀ : 0 ≤ C₀)
    (hF : 0 ≤ F) (hlam : 0 < lam) (hδ : 0 < δ) :
    2 * 2 ^ n * (C₀ / (δ / 3) * U + C₀ * (δ / 3) / lam * F) ≤
      6 * 2 ^ n * C₀ * (δ * F / lam + U / δ) := by
  have e : C₀ / (δ / 3) * U + C₀ * (δ / 3) / lam * F =
      3 * C₀ * (U / δ) + 1 / 3 * (C₀ * (δ * F / lam)) := by
    field_simp
  rw [e]
  have : 0 ≤ (2 : ℝ) ^ n * (C₀ * (δ * F / lam)) := by positivity
  nlinarith

/-- The arithmetic of the averaged second-derivative estimate on a set, with balls of radius
`δ / 5`. -/
private theorem two_mul_four_pow_mul_add_le {c₀ F W lam δ : ℝ} (n : ℕ) (hc₀ : 0 ≤ c₀)
    (hF : 0 ≤ F) (hlam : 0 < lam) (hδ : 0 < δ) :
    2 * 4 ^ n * (c₀ / lam * F + c₀ / (δ / 5) ^ 2 * W) ≤
      50 * 4 ^ n * c₀ * (F / lam + W / δ ^ 2) := by
  have e : c₀ / lam * F + c₀ / (δ / 5) ^ 2 * W = c₀ * (F / lam) + 25 * (c₀ * (W / δ ^ 2)) := by
    field_simp
    ring
  rw [e]
  have : 0 ≤ (4 : ℝ) ^ n * (c₀ * (F / lam)) := by positivity
  nlinarith

/-- The arithmetic of the `W^{2,2}` estimate on a set: with `t = δ⁻¹` and
`P = δ² ‖f‖ / λ + ‖u‖ ≥ ‖u‖`, the value, gradient and second-derivative bounds `W ≤ P`,
`C₂ t P` and `N t² P` sum to at most `(1 + C₂ + N) (1 + t²) P`. -/
private theorem add_mul_add_mul_le {W P t C₂ N : ℝ} (hW : W ≤ P) (hP : 0 ≤ P) (hC₂ : 0 ≤ C₂)
    (hN : 0 ≤ N) :
    W + C₂ * (t * P) + N * (t ^ 2 * P) ≤ (1 + C₂ + N) * (1 + t ^ 2) * P := by
  have ht' : t ≤ 1 + t ^ 2 := by nlinarith [sq_nonneg (t - 1)]
  nlinarith [mul_le_mul_of_nonneg_right ht' hP, mul_nonneg hC₂ hP, mul_nonneg hN hP,
    mul_nonneg (mul_nonneg hN hP) (sq_nonneg t), mul_nonneg hP (sq_nonneg t),
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right ht' hP) hC₂]

/-- Weak derivatives of `g` in the direction `w` on the balls `B(z, r)` that meet `V`, with local
`L²` bounds by `f₁` and `f₂` on the enlarged balls `B(z, κ r) ⊆ T`, glue to a weak derivative on `V`
whose `L²(V)` norm satisfies the averaged bound. -/
private theorem exists_hasWeakLineDerivOn_eLpNorm_le_of_forall_ball_inter_nonempty
    {mu : Measure (EuclideanSpace ℝ ι)} [mu.IsAddHaarMeasure] {V : Opens (EuclideanSpace ℝ ι)}
    {T : Set (EuclideanSpace ℝ ι)} (hT : MeasurableSet T) {g f₁ f₂ : EuclideanSpace ℝ ι → ℝ}
    (hf₁ : AEStronglyMeasurable f₁ (mu.restrict T)) (hf₂ : AEStronglyMeasurable f₂ (mu.restrict T))
    {w : EuclideanSpace ℝ ι} {r κ c₁ c₂ : ℝ} (hr : 0 < r) (hκ : 1 ≤ κ)
    (h : ∀ z, (Metric.ball z r ∩ V).Nonempty → Metric.ball z (κ * r) ⊆ T ∧
      ∃ G : EuclideanSpace ℝ ι → ℝ,
        HasWeakLineDerivOn mu ⟨Metric.ball z r, Metric.isOpen_ball⟩ g G w ∧
        eLpNorm G 2 (mu.restrict (Metric.ball z r)) ≤
          ENNReal.ofReal c₁ * eLpNorm f₁ 2 (mu.restrict (Metric.ball z (κ * r))) +
            ENNReal.ofReal c₂ * eLpNorm f₂ 2 (mu.restrict (Metric.ball z (κ * r)))) :
    ∃ G : EuclideanSpace ℝ ι → ℝ, HasWeakLineDerivOn mu V g G w ∧
      eLpNorm G 2 (mu.restrict V) ≤ 2 * ENNReal.ofReal κ ^ Fintype.card ι *
        (ENNReal.ofReal c₁ * eLpNorm f₁ 2 (mu.restrict T) +
          ENNReal.ofReal c₂ * eLpNorm f₂ 2 (mu.restrict T)) := by
  choose hsub G hGd hGle using h
  -- The balls meeting `V` cover it, and the local derivatives glue along them.
  let Z := {z : EuclideanSpace ℝ ι // (Metric.ball z r ∩ V).Nonempty}
  let B : Z → Opens (EuclideanSpace ℝ ι) := fun z =>
    ⟨Metric.ball (z : EuclideanSpace ℝ ι) r, Metric.isOpen_ball⟩
  have hB : ∀ z : Z, HasWeakLineDerivOn mu (B z) g (G z z.property) w := fun z =>
    hGd z z.property
  obtain ⟨G₀, hG₀, hG₀z⟩ := exists_hasWeakLineDerivOn_iSup B (fun z => G z z.property) hB
  have hGV := hG₀.mono (Ω' := V) fun x hx =>
    Opens.mem_iSup.2 ⟨⟨x, x, Metric.mem_ball_self hr, hx⟩, Metric.mem_ball_self hr⟩
  refine ⟨G₀, hGV, ?_⟩
  rw [← finrank_euclideanSpace (𝕜 := ℝ)]
  exact eLpNorm_restrict_le_of_forall_ball_inter_nonempty one_le_two ENNReal.ofNat_ne_top
    V.isOpen.measurableSet hT hGV.locallyIntegrableOn_deriv.aestronglyMeasurable hf₁ hf₂ hκ hr
    fun z hz => ⟨hsub z hz, (eLpNorm_congr_ae (hG₀z ⟨z, hz⟩)).trans_le (hGle z hz)⟩

/-- **Caccioppoli's inequality on balls, in dimensionless form.** Fix `M`. There is a constant `C`,
depending only on the dimension `n` and on `M`, with the following property. Let `a` be measurable
and uniformly elliptic on `B(x₀, 2 r) ⊆ Ω` with constants `λ ≤ Λ`, let `b`, `c` be measurable on
`B(x₀, 2 r)` with `‖b‖ ≤ β` and `|c| ≤ γ` almost everywhere there, and suppose that `Λ ≤ M λ`,
`r β ≤ M λ` and `r² γ ≤ M λ`. Let `u ∈ H¹(Ω)` be a weak solution of

`-∂ᵢ(aⁱʲ ∂ⱼu) + ⟨b, ∇u⟩ + c u = f` in `Ω`, with `f ∈ L²(Ω)`

and no boundary condition. Then

`‖∇u‖_{L²(B(x₀, r))} ≤ C (‖u‖ / r + r ‖f‖ / λ)`,

the norms on the right being those of `L²(B(x₀, 2 r))`. Both sides scale in the same way under the
dilations `x ↦ x₀ + r x`. -/
theorem exists_toReal_eLpNorm_gradient_ball_le_eLpNorm_value [DecidableEq ι] (M : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (mu : Measure (EuclideanSpace ℝ ι)) [mu.IsAddHaarMeasure]
      ⦃Omega : Opens (EuclideanSpace ℝ ι)⦄ ⦃a : EuclideanSpace ℝ ι → Matrix ι ι ℝ⦄
      ⦃b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι⦄ ⦃c : EuclideanSpace ℝ ι → ℝ⦄
      ⦃x₀ : EuclideanSpace ℝ ι⦄ ⦃r lam Lam β γ : ℝ⦄
      ⦃f : Lp ℝ 2 (mu.restrict Omega)⦄ ⦃u : W1p mu Omega 2⦄,
      0 < r → Metric.ball x₀ (2 * r) ⊆ Omega →
      UniformlyEllipticOn (Metric.ball x₀ (2 * r)) a lam Lam →
      AEStronglyMeasurable a (mu.restrict (Metric.ball x₀ (2 * r))) →
      AEStronglyMeasurable b (mu.restrict (Metric.ball x₀ (2 * r))) →
      AEStronglyMeasurable c (mu.restrict (Metric.ball x₀ (2 * r))) →
      (∀ᵐ x ∂mu.restrict (Metric.ball x₀ (2 * r)), ‖b x‖ ≤ β) →
      (∀ᵐ x ∂mu.restrict (Metric.ball x₀ (2 * r)), |c x| ≤ γ) →
      Lam ≤ M * lam → r * β ≤ M * lam → r ^ 2 * γ ≤ M * lam →
      (∀ v : W1p0 mu Omega 2, energyFormH1 a b c u (v : W1p mu Omega 2) =
        ∫ x in Omega, f x * W1p.value (v : W1p mu Omega 2) x ∂mu) →
      (eLpNorm (W1p.gradient u) 2 (mu.restrict (Metric.ball x₀ r))).toReal ≤
        C * ((eLpNorm (W1p.value u) 2 (mu.restrict (Metric.ball x₀ (2 * r)))).toReal / r +
          r * (eLpNorm f 2 (mu.restrict (Metric.ball x₀ (2 * r)))).toReal / lam) := by
  obtain ⟨C₂, hcacc⟩ := exists_sq_toReal_eLpNorm_gradient_ball_le_lowerOrder (ι := ι)
  set Q := 2 * M ^ 2 * C₂ ^ 2 + 4 * M ^ 2 + 4 * M + 1 / 8 + 1
  refine ⟨3 * max Q 0, by positivity, ?_⟩
  intro mu _ Omega a b c x₀ r lam Lam β γ f u hr hΩ ha ham hbm hcm hβ hγ hMΛ hMβ hMγ hu
  have hlam := ha.pos
  have hM0 : 0 ≤ M * lam := ha.upper_nonneg.trans hMΛ
  have hM : 0 ≤ M := nonneg_of_mul_nonneg_left hM0 hlam
  have hQ : 1 ≤ Q := by simp only [Q]; nlinarith
  -- The ball has positive measure, so the almost everywhere bound forces `0 ≤ β`.
  have : (ae (mu.restrict (Metric.ball x₀ (2 * r)))).NeBot :=
    ae_restrict_neBot.2 (Metric.measure_ball_pos mu x₀ (by positivity)).ne'
  have hβ0 : 0 ≤ β := let ⟨_, hx⟩ := hβ.exists; (norm_nonneg _).trans hx
  -- Caccioppoli's inequality from `B(x₀, 2 (r / 2))` to `B(x₀, 4 (r / 2))`, in real form.
  have hcU := hcacc mu (r := r) (R := 2 * r) (by positivity) (by linarith) hΩ ha ham hbm hcm hβ hγ
    hu
  rw [show 2 * r - r = 4 * (r / 2) - 2 * (r / 2) by ring, show 2 * r = 4 * (r / 2) by ring] at hcU
  have hG := le_div_mul_add_mul_of_sq_le (C := C₂) (r := r / 2) hlam (by positivity)
    ha.upper_nonneg hβ0 ENNReal.toReal_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg hMΛ
    (mul_le_of_mul_le_of_le (by positivity) (by linarith) hMβ hM0)
    (mul_le_of_mul_le_of_le (by positivity) (by nlinarith) hMγ hM0) hcU
  rw [show 4 * (r / 2) = 2 * r by ring] at hG
  set U := (eLpNorm (W1p.value u) 2 (mu.restrict (Metric.ball x₀ (2 * r)))).toReal
  set F := (eLpNorm f 2 (mu.restrict (Metric.ball x₀ (2 * r)))).toReal
  have e : Q / (r / 2) * U + 6 * (r / 2) / lam * F = 2 * Q * (U / r) + 3 * (r * F / lam) := by
    field_simp
    ring
  rw [e] at hG
  rw [max_eq_left (zero_le_one.trans hQ)]
  have hUr : 0 ≤ U / r := by positivity
  have hFr : 0 ≤ r * F / lam := by positivity
  nlinarith [mul_nonneg (zero_le_one.trans hQ) hUr, mul_nonneg (sub_nonneg.2 hQ) hFr]

/-- **The interior gradient estimate on a set at positive distance from the boundary.** Fix `M`.
There is a constant `C`, depending only on the dimension `n` and on `M`, with the following
property. Let `V` be open, let `δ > 0`, and let the `δ`-thickening `V_δ` of `V`, the points at
distance less than `δ` from `V`, lie in `Ω`. Let `a` be measurable and uniformly elliptic on `V_δ`
with constants `λ ≤ Λ`, let `b`, `c` be measurable on `V_δ` with `‖b‖ ≤ β` and `|c| ≤ γ` almost
everywhere there, and suppose that `Λ ≤ M λ`, `δ β ≤ M λ` and `δ² γ ≤ M λ`. Let `u ∈ H¹(Ω)` be a
weak solution of

`-∂ᵢ(aⁱʲ ∂ⱼu) + ⟨b, ∇u⟩ + c u = f` in `Ω`, with `f ∈ L²(Ω)`

and no boundary condition. Then

`‖∇u‖_{L²(V)} ≤ C (δ ‖f‖ / λ + ‖u‖ / δ)`,

the norms on the right being those of `L²(V_δ)`. `V` need not be bounded, and the coefficients need
not be continuous. -/
theorem exists_toReal_eLpNorm_gradient_le_of_thickening [DecidableEq ι] (M : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (mu : Measure (EuclideanSpace ℝ ι)) [mu.IsAddHaarMeasure]
      ⦃Omega V : Opens (EuclideanSpace ℝ ι)⦄ ⦃a : EuclideanSpace ℝ ι → Matrix ι ι ℝ⦄
      ⦃b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι⦄ ⦃c : EuclideanSpace ℝ ι → ℝ⦄
      ⦃δ lam Lam β γ : ℝ⦄ ⦃f : Lp ℝ 2 (mu.restrict Omega)⦄ ⦃u : W1p mu Omega 2⦄,
      0 < δ → Metric.thickening δ (V : Set (EuclideanSpace ℝ ι)) ⊆ Omega →
      UniformlyEllipticOn (Metric.thickening δ (V : Set (EuclideanSpace ℝ ι))) a lam Lam →
      AEStronglyMeasurable a (mu.restrict (Metric.thickening δ (V : Set (EuclideanSpace ℝ ι)))) →
      AEStronglyMeasurable b (mu.restrict (Metric.thickening δ (V : Set (EuclideanSpace ℝ ι)))) →
      AEStronglyMeasurable c (mu.restrict (Metric.thickening δ (V : Set (EuclideanSpace ℝ ι)))) →
      (∀ᵐ x ∂mu.restrict (Metric.thickening δ (V : Set (EuclideanSpace ℝ ι))), ‖b x‖ ≤ β) →
      (∀ᵐ x ∂mu.restrict (Metric.thickening δ (V : Set (EuclideanSpace ℝ ι))), |c x| ≤ γ) →
      Lam ≤ M * lam → δ * β ≤ M * lam → δ ^ 2 * γ ≤ M * lam →
      (∀ v : W1p0 mu Omega 2, energyFormH1 a b c u (v : W1p mu Omega 2) =
        ∫ x in Omega, f x * W1p.value (v : W1p mu Omega 2) x ∂mu) →
      (eLpNorm (W1p.gradient u) 2 (mu.restrict V)).toReal ≤
        C * (δ * (eLpNorm f 2
            (mu.restrict (Metric.thickening δ (V : Set (EuclideanSpace ℝ ι))))).toReal / lam +
          (eLpNorm (W1p.value u) 2
            (mu.restrict (Metric.thickening δ (V : Set (EuclideanSpace ℝ ι))))).toReal / δ) := by
  obtain ⟨C₀, hC₀, hball⟩ := exists_toReal_eLpNorm_gradient_ball_le_eLpNorm_value (ι := ι) M
  refine ⟨6 * 2 ^ Fintype.card ι * C₀, by positivity, ?_⟩
  intro mu _ Omega V a b c δ lam Lam β γ f u hδ hΩ ha ham hbm hcm hβ hγ hMΛ hMβ hMγ hu
  set T := Metric.thickening δ (V : Set (EuclideanSpace ℝ ι))
  have hr : 0 < δ / 3 := by positivity
  have hM0 : 0 ≤ M * lam := ha.upper_nonneg.trans hMΛ
  -- Every ball `B(z, δ / 3)` meeting `V` has `B(z, 2 δ / 3) ⊆ V_δ`.
  have hsub : ∀ z, (Metric.ball z (δ / 3) ∩ V).Nonempty → Metric.ball z (2 * (δ / 3)) ⊆ T :=
    fun z hz => ball_mul_subset_thickening hz (by linarith)
  -- Average Caccioppoli's inequality on these balls over their centres.
  have hest := eLpNorm_restrict_le_of_forall_ball_inter_nonempty (μ := mu) (p := 2) one_le_two
    ENNReal.ofNat_ne_top V.isOpen.measurableSet Metric.isOpen_thickening.measurableSet
    ((Lp.aestronglyMeasurable (W1p.gradient u)).mono_measure
      (Measure.restrict_mono ((Metric.self_subset_thickening hδ _).trans hΩ) le_rfl))
    ((Lp.aestronglyMeasurable (W1p.value u)).mono_measure (Measure.restrict_mono hΩ le_rfl))
    ((Lp.aestronglyMeasurable f).mono_measure (Measure.restrict_mono hΩ le_rfl))
    (c₁ := C₀ / (δ / 3)) (c₂ := C₀ * (δ / 3) / lam) one_le_two hr fun z hz => ⟨hsub z hz, ?_⟩
  · have hlam := ha.pos
    rw [finrank_euclideanSpace] at hest
    exact ENNReal.toReal_le_of_le_ofReal (by positivity) (hest.trans
      (two_mul_ofReal_pow_mul_add_le (Lp.eLpNorm_restrict_ne_top _ hΩ)
        (Lp.eLpNorm_restrict_ne_top f hΩ) zero_le_two (by positivity) (by positivity)
        (two_mul_two_pow_mul_add_le _ hC₀ ENNReal.toReal_nonneg hlam hδ)))
  -- The local estimate on a ball meeting `V`.
  have hzT := hsub z hz
  exact le_ofReal_mul_add_ofReal_mul_of_toReal_le
    (Lp.eLpNorm_restrict_ne_top _ ((Metric.ball_subset_ball (by linarith)).trans (hzT.trans hΩ)))
    (Lp.eLpNorm_restrict_ne_top _ (hzT.trans hΩ)) (Lp.eLpNorm_restrict_ne_top _ (hzT.trans hΩ))
    (by positivity) (by have := ha.pos; positivity) ((hball mu hr (hzT.trans hΩ) (ha.mono_set hzT)
      (ham.mono_measure (Measure.restrict_mono hzT le_rfl))
      (hbm.mono_measure (Measure.restrict_mono hzT le_rfl))
      (hcm.mono_measure (Measure.restrict_mono hzT le_rfl))
      (ae_restrict_of_ae_restrict_of_subset hzT hβ) (ae_restrict_of_ae_restrict_of_subset hzT hγ)
      hMΛ (mul_le_of_mul_le_of_le hr.le (by linarith) hMβ hM0)
      (mul_le_of_mul_le_of_le (by positivity) (pow_le_pow_left₀ hr.le (by linarith) 2) hMγ hM0)
      hu).trans_eq (by ring))

namespace UniformlyEllipticOn

/-- **The interior `H²` estimate on a set at positive distance from the boundary** (Evans, §6.3.1,
Theorem 1; Gilbarg–Trudinger, Theorem 8.8). Fix `M`. There is a constant `C`, depending only on
the dimension `n` and on `M`, with the following property. Let `V` be open, let `δ > 0`, and let
the `δ`-thickening `V_δ` of `V`, the points at distance less than `δ` from `V`, lie in `Ω`. Let `a`
be uniformly elliptic on `V_δ` with constants `λ ≤ Λ`, with `x ↦ a(x)` `K`-Lipschitz there in the
operator norm of its bilinear forms, let `b, c ∈ L∞(Ω)` with `‖b‖ ≤ β` and `|c| ≤ γ` almost
everywhere on `V_δ`, and suppose that the dimensionless coefficient parameters are bounded:

`Λ ≤ M λ`, `δ β ≤ M λ`, `δ K ≤ M λ`, `δ² γ ≤ M λ`.

Let `u ∈ H¹(Ω)` be a weak solution of

`-∂ᵢ(aⁱʲ ∂ⱼu) + ⟨b, ∇u⟩ + c u = f` in `Ω`, with `f ∈ L²(Ω)`

and no boundary condition. Then on `V` every derivative `∂_y u` has a weak derivative in every
direction `w`, with

`‖∂_w ∂_y u‖_{L²(V)} ≤ C ‖y‖ ‖w‖ (‖f‖ / λ + ‖u‖ / δ²)`,

the norms on the right being those of `L²(V_δ)`. Every point of `V` is at distance at least `δ`
from the complement of `Ω`, and the constant depends on `δ` only through the dimensionless
parameters. `V` need not be bounded. -/
theorem exists_norm_le_eLpNorm_value_hasWeakLineDerivOn_gradient_of_thickening
    [DecidableEq ι] (M : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (mu : Measure (EuclideanSpace ℝ ι)) [mu.IsAddHaarMeasure]
      ⦃Omega V : Opens (EuclideanSpace ℝ ι)⦄ ⦃a : EuclideanSpace ℝ ι → Matrix ι ι ℝ⦄
      ⦃b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι⦄ ⦃c : EuclideanSpace ℝ ι → ℝ⦄
      ⦃δ lam Lam β γ : ℝ⦄ ⦃K : ℝ≥0⦄
      ⦃f : Lp ℝ 2 (mu.restrict Omega)⦄ ⦃u : W1p mu Omega 2⦄,
      0 < δ → Metric.thickening δ (V : Set (EuclideanSpace ℝ ι)) ⊆ Omega →
      UniformlyEllipticOn (Metric.thickening δ (V : Set (EuclideanSpace ℝ ι))) a lam Lam →
      LipschitzOnWith K (fun x => matrixBilinearForm (a x))
        (Metric.thickening δ (V : Set (EuclideanSpace ℝ ι))) →
      MemLp b ⊤ (mu.restrict Omega) → MemLp c ⊤ (mu.restrict Omega) →
      (∀ᵐ x ∂mu.restrict (Metric.thickening δ (V : Set (EuclideanSpace ℝ ι))), ‖b x‖ ≤ β) →
      (∀ᵐ x ∂mu.restrict (Metric.thickening δ (V : Set (EuclideanSpace ℝ ι))), |c x| ≤ γ) →
      Lam ≤ M * lam → δ * β ≤ M * lam → δ * K ≤ M * lam → δ ^ 2 * γ ≤ M * lam →
      (∀ v : W1p0 mu Omega 2, energyFormH1 a b c u (v : W1p mu Omega 2) =
        ∫ x in Omega, f x * W1p.value (v : W1p mu Omega 2) x ∂mu) →
      ∀ y w : EuclideanSpace ℝ ι, ∃ G : Lp ℝ 2 (mu.restrict V),
        ‖G‖ ≤ C * ‖y‖ * ‖w‖ * ((eLpNorm f 2
            (mu.restrict (Metric.thickening δ (V : Set (EuclideanSpace ℝ ι))))).toReal / lam +
          (eLpNorm (W1p.value u) 2
            (mu.restrict (Metric.thickening δ (V : Set (EuclideanSpace ℝ ι))))).toReal / δ ^ 2) ∧
        HasWeakLineDerivOn mu V (fun x => ⟪W1p.gradient u x, y⟫_ℝ) G w := by
  obtain ⟨C₀, hC₀, hball⟩ :=
    UniformlyEllipticOn.exists_norm_le_eLpNorm_value_hasWeakLineDerivOn_gradient_ball (ι := ι) M
  refine ⟨50 * 4 ^ Fintype.card ι * C₀, by positivity, ?_⟩
  intro mu _ Omega V a b c δ lam Lam β γ K f u hδ hΩ ha hK hb hc hβ hγ hMΛ hMβ hMK hMγ hu y w
  set T := Metric.thickening δ (V : Set (EuclideanSpace ℝ ι))
  have hr : 0 < δ / 5 := by positivity
  have hrδ : δ / 5 ≤ δ := by linarith
  have hlam := ha.pos
  have hM0 : 0 ≤ M * lam := ha.upper_nonneg.trans hMΛ
  set c₀ := C₀ * ‖y‖ * ‖w‖
  -- The estimate on balls applies on every ball `B(z, δ / 5)` meeting `V`: `B(z, 4 δ / 5) ⊆ V_δ`.
  have hsub : ∀ z, (Metric.ball z (δ / 5) ∩ V).Nonempty → Metric.ball z (4 * (δ / 5)) ⊆ T :=
    fun z hz => ball_mul_subset_thickening hz (by linarith)
  -- Glue the local second derivatives and average their bounds.
  obtain ⟨G₀, hGV, hglob⟩ := exists_hasWeakLineDerivOn_eLpNorm_le_of_forall_ball_inter_nonempty
    Metric.isOpen_thickening.measurableSet
    ((Lp.aestronglyMeasurable f).mono_measure (Measure.restrict_mono hΩ le_rfl))
    ((Lp.aestronglyMeasurable (W1p.value u)).mono_measure (Measure.restrict_mono hΩ le_rfl))
    (c₁ := c₀ / lam) (c₂ := c₀ / (δ / 5) ^ 2) (κ := 4) hr (by norm_num) fun z hz => by
      have hzΩ := (hsub z hz).trans hΩ
      obtain ⟨G, hG, hGd⟩ := hball mu hr hzΩ (ha.mono_set (hsub z hz)) (hK.mono (hsub z hz)) hb hc
        (ae_restrict_of_ae_restrict_of_subset (hsub z hz) hβ)
        (ae_restrict_of_ae_restrict_of_subset (hsub z hz) hγ) hMΛ
        (mul_le_of_mul_le_of_le hr.le hrδ hMβ hM0) (mul_le_of_mul_le_of_le hr.le hrδ hMK hM0)
        (mul_le_of_mul_le_of_le (by positivity) (pow_le_pow_left₀ hr.le hrδ 2) hMγ hM0) hu y w
      exact ⟨hsub z hz, G, hGd, le_ofReal_mul_add_ofReal_mul_of_toReal_le (Lp.eLpNorm_ne_top _)
        (Lp.eLpNorm_restrict_ne_top f hzΩ) (Lp.eLpNorm_restrict_ne_top _ hzΩ) (by positivity)
        (by positivity) (hG.trans_eq (by ring))⟩
  -- The glued derivative lies in `L²(V)`, with the stated norm.
  replace hglob := hglob.trans (two_mul_ofReal_pow_mul_add_le (Lp.eLpNorm_restrict_ne_top f hΩ)
    (Lp.eLpNorm_restrict_ne_top _ hΩ) (by norm_num) (by positivity) (by positivity)
    (two_mul_four_pow_mul_add_le _ (by positivity) ENNReal.toReal_nonneg hlam hδ))
  have hmem : MemLp G₀ 2 (mu.restrict V) := hglob.trans_lt ENNReal.ofReal_lt_top
  refine ⟨hmem.toLp G₀, ?_, hGV.congr_ae_deriv hmem.coeFn_toLp.symm⟩
  rw [Lp.norm_toLp]
  exact (ENNReal.toReal_le_of_le_ofReal (by positivity) hglob).trans_eq (by ring)

end UniformlyEllipticOn

/-- **The interior `H²` estimate on a set at positive distance from the boundary, in the norm of
`W^{2,2}`.** Fix `M`. There is a constant `C`, depending only on the dimension `n` and on `M`, with
the following property. Let `V` be open, let `δ > 0`, and let the `δ`-thickening `V_δ` of `V` lie
in `Ω`. Let `a` be uniformly elliptic on `V_δ` with constants `λ ≤ Λ`, with `x ↦ a(x)` `K`-Lipschitz
there in the operator norm of its bilinear forms, let `b, c ∈ L∞(Ω)` with `‖b‖ ≤ β` and `|c| ≤ γ`
almost everywhere on `V_δ`, and suppose that `Λ ≤ M λ`, `δ β ≤ M λ`, `δ K ≤ M λ` and
`δ² γ ≤ M λ`. Let `u ∈ H¹(Ω)` be a weak solution of

`-∂ᵢ(aⁱʲ ∂ⱼu) + ⟨b, ∇u⟩ + c u = f` in `Ω`, with `f ∈ L²(Ω)`

and no boundary condition. Then the restriction of `u` to `V` is the first-order part of some
`U ∈ W^{2,2}(V)` with

`‖U‖ ≤ C (1 + δ⁻²) (δ² ‖f‖ / λ + ‖u‖)`,

the norms on the right being those of `L²(V_δ)`. This is the estimate
`‖u‖_{H²(V)} ≤ C (‖f‖_{L²(Ω)} + ‖u‖_{L²(Ω)})` of Evans, §6.3.1, Theorem 1, with the dependence of
`C` on `dist(V, ∂Ω) ≥ δ` explicit. -/
theorem UniformlyEllipticOn.exists_lowerOrder_eq_restrictL_and_norm_le_of_thickening
    [DecidableEq ι] (M : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (mu : Measure (EuclideanSpace ℝ ι)) [mu.IsAddHaarMeasure]
      ⦃Omega V : Opens (EuclideanSpace ℝ ι)⦄ ⦃a : EuclideanSpace ℝ ι → Matrix ι ι ℝ⦄
      ⦃b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι⦄ ⦃c : EuclideanSpace ℝ ι → ℝ⦄
      ⦃δ lam Lam β γ : ℝ⦄ ⦃K : ℝ≥0⦄
      ⦃f : Lp ℝ 2 (mu.restrict Omega)⦄ ⦃u : W1p mu Omega 2⦄ (hδ : 0 < δ)
      (hΩ : Metric.thickening δ (V : Set (EuclideanSpace ℝ ι)) ⊆ Omega),
      UniformlyEllipticOn (Metric.thickening δ (V : Set (EuclideanSpace ℝ ι))) a lam Lam →
      LipschitzOnWith K (fun x => matrixBilinearForm (a x))
        (Metric.thickening δ (V : Set (EuclideanSpace ℝ ι))) →
      MemLp b ⊤ (mu.restrict Omega) → MemLp c ⊤ (mu.restrict Omega) →
      (∀ᵐ x ∂mu.restrict (Metric.thickening δ (V : Set (EuclideanSpace ℝ ι))), ‖b x‖ ≤ β) →
      (∀ᵐ x ∂mu.restrict (Metric.thickening δ (V : Set (EuclideanSpace ℝ ι))), |c x| ≤ γ) →
      Lam ≤ M * lam → δ * β ≤ M * lam → δ * K ≤ M * lam → δ ^ 2 * γ ≤ M * lam →
      (∀ v : W1p0 mu Omega 2, energyFormH1 a b c u (v : W1p mu Omega 2) =
        ∫ x in Omega, f x * W1p.value (v : W1p mu Omega 2) x ∂mu) →
      ∃ U : Wkp mu V 2 2, Wkp.lowerOrder 1 U = W1p.restrictL (SetLike.coe_subset_coe.mp
          ((Metric.self_subset_thickening hδ _).trans hΩ)) u ∧
        ‖U‖ ≤ C * (1 + δ⁻¹ ^ 2) * (δ ^ 2 * (eLpNorm f 2
            (mu.restrict (Metric.thickening δ (V : Set (EuclideanSpace ℝ ι))))).toReal / lam +
          (eLpNorm (W1p.value u) 2
            (mu.restrict (Metric.thickening δ (V : Set (EuclideanSpace ℝ ι))))).toReal) := by
  obtain ⟨C₁, hC₁, hsecond⟩ :=
    exists_norm_le_eLpNorm_value_hasWeakLineDerivOn_gradient_of_thickening (ι := ι) M
  obtain ⟨C₂, hC₂, hgrad⟩ := exists_toReal_eLpNorm_gradient_le_of_thickening (ι := ι) M
  refine ⟨1 + C₂ + Fintype.card ι ^ 2 * C₁, by positivity, ?_⟩
  intro mu _ Omega V a b c δ lam Lam β γ K f u hδ hΩ ha hK hb hc hβ hγ hMΛ hMβ hMK hMγ hu
  have hgradV := hgrad mu hδ hΩ ha
    ((continuousOn_of_continuousOn_matrixBilinearForm hK.continuousOn).aestronglyMeasurable
      Metric.isOpen_thickening.measurableSet)
    (hb.aestronglyMeasurable.mono_measure (Measure.restrict_mono hΩ le_rfl))
    (hc.aestronglyMeasurable.mono_measure (Measure.restrict_mono hΩ le_rfl)) hβ hγ hMΛ hMβ hMγ hu
  set T := Metric.thickening δ (V : Set (EuclideanSpace ℝ ι))
  set e := EuclideanSpace.basisFun ι ℝ
  have hVT : (V : Set (EuclideanSpace ℝ ι)) ⊆ T := Metric.self_subset_thickening hδ _
  set hVΩ : V ≤ Omega := SetLike.coe_subset_coe.mp (hVT.trans hΩ)
  set F := (eLpNorm f 2 (mu.restrict T)).toReal
  set W := (eLpNorm (W1p.value u) 2 (mu.restrict T)).toReal
  have hlam := ha.pos
  -- The second derivatives `∂ᵢ ⟪∇u, eⱼ⟫` on `V` give `U ∈ W^{2,2}(V)`.
  choose G hGle hG using fun i j => hsecond mu hδ hΩ ha hK hb hc hβ hγ hMΛ hMβ hMK hMγ hu
    (e j) (e i)
  have hG' : ∀ i j, HasWeakLineDerivOn mu V
      (fun x => ⟪W1p.gradient (W1p.restrictL hVΩ u) x, e j⟫_ℝ) (G i j) (e i) := fun i j =>
    (hG i j).congr_ae ((W1p.gradient_restrictL_ae hVΩ u).mono fun x hx => by simp only [hx])
  obtain ⟨U, hU⟩ :=
    W1p.exists_lowerOrder_eq_of_forall_hasWeakLineDerivOn (W1p.restrictL hVΩ u) e
      fun i j => ⟨G i j, hG' i j⟩
  refine ⟨U, hU, ?_⟩
  -- The bounds on `V` in terms of `t = δ⁻¹` and `P = δ² ‖f‖ / λ + ‖u‖`.
  have hP : 0 ≤ δ ^ 2 * F / lam + W := by positivity
  have hlow : ‖W1p.restrictL hVΩ u‖ ≤ W + C₂ * (δ⁻¹ * (δ ^ 2 * F / lam + W)) := by
    refine (W1p.norm_le_norm_value_add_norm_gradient _).trans (add_le_add ?_ ?_)
    · rw [Lp.norm_def, eLpNorm_congr_ae (W1p.value_restrictL_ae hVΩ u)]
      exact Lp.toReal_eLpNorm_restrict_mono _ hVT hΩ
    · rw [Lp.norm_def, eLpNorm_congr_ae (W1p.gradient_restrictL_ae hVΩ u)]
      exact hgradV.trans_eq (by field_simp)
  have hHess : ‖Wkp.iteratedGradient 1 U‖ ≤
      Fintype.card ι ^ 2 * C₁ * (δ⁻¹ ^ 2 * (δ ^ 2 * F / lam + W)) := by
    refine (Wkp.norm_iteratedGradient_one_le_sum U e (g := G) (by rw [hU]; exact hG')).trans ?_
    refine (Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hGle i j).trans_eq ?_
    simp only [e.orthonormal.1 _, mul_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp
    ring
  calc ‖U‖ ≤ ‖Wkp.lowerOrder 1 U‖ + ‖Wkp.iteratedGradient 1 U‖ :=
        Wkp.norm_le_norm_lowerOrder_add_norm_iteratedGradient 1 U
    _ ≤ _ := by rw [hU]; exact add_le_add hlow hHess
    _ ≤ _ := add_mul_add_mul_le (le_add_of_nonneg_left (by positivity)) hP hC₂ (by positivity)

end PDE

end TauCeti
