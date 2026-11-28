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
import TauCeti.Data.ENNReal.Mul
import TauCeti.MeasureTheory.Function.Lp.Restriction
import TauCeti.MeasureTheory.Function.LpSeminorm.Ball
import TauCeti.Topology.Instances.Matrix
import TauCeti.Topology.MetricSpace.Thickening

/-!
# The interior `H²` estimate in terms of the forcing and the solution

Let `a` be uniformly elliptic and Lipschitz on `B(x₀, 4 r)`, let `b, c ∈ L∞(Ω)` with `‖b‖ ≤ β`
and `|c| ≤ γ` on `B(x₀, 4 r)`, and let `u ∈ H¹(Ω)` be a weak solution of

`-∂ᵢ(aⁱʲ ∂ⱼu) + ⟨b, ∇u⟩ + c u = f` in `Ω ⊇ B(x₀, 4 r)`, with `f ∈ L²(Ω)`.

The interior estimate on balls
(`TauCeti.PDE.UniformlyEllipticOn.exists_norm_le_hasWeakLineDerivOn_gradient_ball`) bounds the
second weak derivatives of `u` on `B(x₀, r)` by the `L²` norms of `f`, `∇u` and `u` on
`B(x₀, 2 r)`. This file removes `∇u` from the right-hand side: by Caccioppoli's inequality with
lower-order terms (`TauCeti.PDE.exists_toReal_eLpNorm_gradient_ball_le_eLpNorm_value`), the
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
on these balls glue to weak derivatives on `V`
(`TauCeti.exists_hasWeakLineDerivOn_eLpNorm_le_of_forall_ball_inter_nonempty`).

## Main declarations

* `TauCeti.PDE.UniformlyEllipticOn.exists_norm_le_eLpNorm_value_hasWeakLineDerivOn_gradient_ball`:
  **the interior `H²` estimate on balls** in terms of the forcing and the solution.
* `TauCeti.PDE.exists_toReal_eLpNorm_gradient_le_of_thickening`: the interior gradient
  estimate on a set at distance `δ` from the boundary.
* `TauCeti.PDE.UniformlyEllipticOn.exists_norm_restrictL_le_of_continuousOn`: for continuous
  lower-order coefficients, the `H¹` norm of `u` on a compactly contained open set in terms of the
  `L²` norms of `f` and `u` on `Ω`.
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

/-- The arithmetic of the interior `H²` estimate in terms of the forcing and the solution: the
interior estimate on balls with norms `F₂`, `G₂`, `U₂` of `f`, `∇u`, `u` on `B(x₀, 2 r)`, and
Caccioppoli's inequality bounding `G₂` by the norms `F₄`, `U₄` on `B(x₀, 4 r)`, give a bound by
`F₄ / λ + U₄ / r²` alone. -/
private theorem le_mul_div_add_div_of_le {X Y F₂ F₄ G₂ U₂ U₄ Lam lam β γ r K C₁ C₂ M : ℝ}
    (hlam : 0 < lam) (hr : 0 < r) (hΛ0 : 0 ≤ Lam) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (hY : 0 ≤ Y)
    (hG₂ : 0 ≤ G₂) (hU₂ : 0 ≤ U₂) (hF₄ : 0 ≤ F₄)
    (hΛ : Lam ≤ M * lam) (hβ : r * β ≤ M * lam) (hK : r * K ≤ M * lam) (hγ : r ^ 2 * γ ≤ M * lam)
    (hF : F₂ ≤ F₄) (hU : U₂ ≤ U₄)
    (hX : X ≤ Y * (F₂ + (β + 2 * K + C₁ * Lam / r) * G₂ +
      (γ + C₁ * K / r + C₁ * Lam / r ^ 2) * U₂) / lam)
    (hG : G₂ ≤ C₂ * (U₄ / (2 * r) + 2 * r * F₄ / lam)) :
    X ≤ (1 + 2 * ((3 + C₁) * M * C₂) + ((3 + C₁) * M * C₂ + (1 + 2 * C₁) * M)) * Y *
      (F₄ / lam + U₄ / r ^ 2) := by
  have hM : 0 ≤ M := nonneg_of_mul_nonneg_left (hΛ0.trans hΛ) hlam
  have hU₄ : 0 ≤ U₄ := hU₂.trans hU
  -- The coefficients of the gradient and value terms are at most `m₁ λ / r` and `m₂ λ / r²`.
  set m₁ := (3 + C₁) * M
  set m₂ := (1 + 2 * C₁) * M
  have hA₁ : (β + 2 * K + C₁ * Lam / r) * G₂ ≤ m₁ * C₂ * lam * (U₄ / r ^ 2) + 2 * m₁ * C₂ * F₄ := by
    have : β + 2 * K + C₁ * Lam / r ≤ m₁ * lam / r := by
      rw [le_div_iff₀ hr, add_mul, add_mul, div_mul_cancel₀ _ hr.ne']
      nlinarith [mul_le_mul_of_nonneg_left hΛ hC₁]
    have h₀ : 0 ≤ m₁ * C₂ * lam * (U₄ / r ^ 2) := by positivity
    calc (β + 2 * K + C₁ * Lam / r) * G₂ ≤ m₁ * lam / r * G₂ :=
          mul_le_mul_of_nonneg_right this hG₂
      _ ≤ m₁ * lam / r * (C₂ * (U₄ / (2 * r) + 2 * r * F₄ / lam)) :=
          mul_le_mul_of_nonneg_left hG (by positivity)
      _ = m₁ * C₂ * lam * (U₄ / r ^ 2) / 2 + 2 * m₁ * C₂ * F₄ := by field_simp
      _ ≤ _ := by linarith
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
      / lam ≤ (1 + 2 * (m₁ * C₂) + (m₁ * C₂ + m₂)) * (F₄ / lam + U₄ / r ^ 2) := by
    rw [div_le_iff₀ hlam]
    have e : (1 + 2 * (m₁ * C₂) + (m₁ * C₂ + m₂)) * (F₄ / lam + U₄ / r ^ 2) * lam =
        F₄ + 2 * m₁ * C₂ * F₄ + m₁ * C₂ * lam * (U₄ / r ^ 2) + m₂ * lam * (U₄ / r ^ 2) +
          (m₁ * C₂ + m₂) * F₄ + (1 + 2 * (m₁ * C₂)) * lam * (U₄ / r ^ 2) := by
      field_simp
      ring
    rw [e]
    have h₁ : 0 ≤ (m₁ * C₂ + m₂) * F₄ := by positivity
    have h₂ : 0 ≤ (1 + 2 * (m₁ * C₂)) * lam * (U₄ / r ^ 2) := by positivity
    linarith
  calc X ≤ Y * ((F₂ + (β + 2 * K + C₁ * Lam / r) * G₂ +
        (γ + C₁ * K / r + C₁ * Lam / r ^ 2) * U₂) / lam) := by rwa [mul_div_assoc] at hX
    _ ≤ Y * ((1 + 2 * (m₁ * C₂) + (m₁ * C₂ + m₂)) * (F₄ / lam + U₄ / r ^ 2)) :=
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
  set M' := max M 0
  -- Caccioppoli's inequality on `B(x₀, 2 r) ⊆ B(x₀, 4 r)`, whose dimensionless parameters are at
  -- most `4 M'`.
  obtain ⟨C₂, hC₂, hcacc⟩ := exists_toReal_eLpNorm_gradient_ball_le_eLpNorm_value (ι := ι) (4 * M')
  refine ⟨1 + 2 * ((3 + C₁) * M' * C₂) + ((3 + C₁) * M' * C₂ + (1 + 2 * C₁) * M'), by positivity,
    ?_⟩
  intro mu _ Omega a b c x₀ r lam Lam β γ K f u hr hΩ ha hK hb hc hβ hγ hMΛ hMβ hMK hMγ hu y w
  have hlam := ha.pos
  have hMlam : M * lam ≤ M' * lam := mul_le_mul_of_nonneg_right (le_max_left _ _) hlam.le
  have hM'lam : 0 ≤ M' * lam := mul_nonneg (le_max_right _ _) hlam.le
  have h24 : Metric.ball x₀ (2 * r) ⊆ Metric.ball x₀ (4 * r) :=
    Metric.ball_subset_ball (by linarith)
  -- The interior estimate on `B(x₀, r)`, with the norms of `f`, `∇u` and `u` on `B(x₀, 2 r)`.
  obtain ⟨G, hG, hGd⟩ := hball mu hr (h24.trans hΩ) (ha.mono_set h24) (hK.mono h24) hb hc
    (ae_restrict_of_ae_restrict_of_subset h24 hβ) (ae_restrict_of_ae_restrict_of_subset h24 hγ)
    hu y w
  refine ⟨G, ?_, hGd⟩
  -- Caccioppoli's inequality bounds `∇u` on `B(x₀, 2 r)` by `u` and `f` on `B(x₀, 4 r)`.
  have hcU : (eLpNorm (W1p.gradient u) 2 (mu.restrict (Metric.ball x₀ (2 * r)))).toReal ≤
      C₂ * ((eLpNorm (W1p.value u) 2 (mu.restrict (Metric.ball x₀ (4 * r)))).toReal / (2 * r) +
        2 * r * (eLpNorm f 2 (mu.restrict (Metric.ball x₀ (4 * r)))).toReal / lam) := by
    have h4 : 4 * r = 2 * (2 * r) := by ring
    have ham : AEStronglyMeasurable a (mu.restrict (Metric.ball x₀ (4 * r))) :=
      (continuousOn_of_continuousOn_matrixBilinearForm hK.continuousOn).aestronglyMeasurable
        Metric.isOpen_ball.measurableSet
    rw [h4] at hΩ ha ham hβ hγ ⊢
    exact hcacc mu (by positivity) hΩ ha ham
      (hb.aestronglyMeasurable.mono_measure (Measure.restrict_mono hΩ le_rfl))
      (hc.aestronglyMeasurable.mono_measure (Measure.restrict_mono hΩ le_rfl)) hβ hγ
      (by nlinarith) (by nlinarith) (by nlinarith) hu
  rw [mul_assoc _ ‖y‖]
  exact le_mul_div_add_div_of_le hlam hr ha.upper_nonneg hC₁ hC₂ (by positivity)
    ENNReal.toReal_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg (hMΛ.trans hMlam)
    (hMβ.trans hMlam) (hMK.trans hMlam) (hMγ.trans hMlam) (Lp.toReal_eLpNorm_restrict_mono f h24 hΩ)
    (Lp.toReal_eLpNorm_restrict_mono _ h24 hΩ) hG hcU

/-! ### The interior estimates on a set at positive distance from the boundary -/

/-- If `δ t ≤ m` and `0 ≤ m`, then `r t ≤ m` for `0 ≤ r ≤ δ`, whatever the sign of `t`. -/
private theorem mul_le_of_mul_le_of_le {r δ t m : ℝ} (hr : 0 ≤ r) (hrδ : r ≤ δ)
    (h : δ * t ≤ m) (hm : 0 ≤ m) : r * t ≤ m := by
  rcases le_total 0 t with ht | ht <;> nlinarith

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
    fun z hz => ball_subset_thickening_of_inter_nonempty hz (by linarith)
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
      (ENNReal.mul_ofReal_mul_add_ofReal_mul_le_ofReal (by finiteness)
        (Lp.eLpNorm_restrict_ne_top _ hΩ) (Lp.eLpNorm_restrict_ne_top f hΩ) (by positivity)
        (by positivity) (by
          rw [show (2 * ENNReal.ofReal 2 ^ Fintype.card ι).toReal = 2 * 2 ^ Fintype.card ι by simp]
          exact two_mul_two_pow_mul_add_le _ hC₀ ENNReal.toReal_nonneg hlam hδ)))
  -- The local estimate on a ball meeting `V`.
  have hzT := hsub z hz
  exact ENNReal.le_ofReal_mul_add_ofReal_mul_of_toReal_le
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

/-- **Caccioppoli's inequality on a compactly contained set.** Let `a` be uniformly elliptic and
measurable on `Ω`, let the drift `b` and the mass `c` be continuous on `Ω`, and let `W` be an open
set whose closure is compact and contained in `Ω`. Then there is a constant `C`, depending on `W`,
`Ω` and the coefficients, such that every weak solution `u ∈ H¹(Ω)` of

`-∂ᵢ(aⁱʲ ∂ⱼu) + ⟪b, ∇u⟫ + c u = f` in `Ω`, with `f ∈ L²(Ω)`,

and no boundary condition satisfies `‖u‖_{H¹(W)} ≤ C (‖f‖_{L²(Ω)} + ‖u‖_{L²(Ω)})`. This is
`TauCeti.PDE.exists_toReal_eLpNorm_gradient_le_of_thickening` on a thickening of `W` inside a
compact subset of `Ω`, where `b` and `c` are bounded. -/
theorem UniformlyEllipticOn.exists_norm_restrictL_le_of_continuousOn [DecidableEq ι]
    {mu : Measure (EuclideanSpace ℝ ι)} [mu.IsAddHaarMeasure] {Omega : Opens (EuclideanSpace ℝ ι)}
    {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {lam Lam : ℝ}
    (ha : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (ham : AEStronglyMeasurable a (mu.restrict Omega))
    {b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {c : EuclideanSpace ℝ ι → ℝ}
    (hb : ContinuousOn b Omega) (hc : ContinuousOn c Omega)
    {W : Opens (EuclideanSpace ℝ ι)} (hW : IsCompact (closure (W : Set (EuclideanSpace ℝ ι))))
    (hWΩ : closure (W : Set (EuclideanSpace ℝ ι)) ⊆ Omega) :
    ∃ C, 0 ≤ C ∧ ∀ (f : Lp ℝ 2 (mu.restrict Omega)) (u : W1p mu Omega 2),
      (∀ v : W1p0 mu Omega 2, energyFormH1 a b c u (v : W1p mu Omega 2) =
        ∫ x in Omega, f x * W1p.value (v : W1p mu Omega 2) x ∂mu) →
      ‖W1p.restrictL (SetLike.coe_subset_coe.mp (subset_closure.trans hWΩ)) u‖ ≤
        C * (‖f‖ + ‖W1p.value u‖) := by
  -- A thickening `T` of `W` inside a compact subset `closure W₂` of `Ω`.
  obtain ⟨W₂, hW₂, hWW₂, hW₂Ω, hW₂c⟩ :=
    exists_open_between_and_isCompact_closure hW Omega.isOpen hWΩ
  obtain ⟨δ, hδ, hδW⟩ := hW.exists_thickening_subset_open hW₂ hWW₂
  set T := Metric.thickening δ (W : Set (EuclideanSpace ℝ ι))
  have hTW₂ : T ⊆ closure W₂ :=
    ((Metric.thickening_subset_of_subset δ subset_closure).trans hδW).trans subset_closure
  have hTΩ : T ⊆ Omega := hTW₂.trans hW₂Ω
  have hmT : MeasurableSet T := Metric.isOpen_thickening.measurableSet
  have hTm : mu.restrict T ≤ mu.restrict Omega := Measure.restrict_mono hTΩ le_rfl
  -- The lower-order coefficients are bounded on `closure W₂`.
  obtain ⟨β, hβ⟩ := hW₂c.exists_bound_of_continuousOn (hb.mono hW₂Ω)
  obtain ⟨γ, hγ⟩ := hW₂c.exists_bound_of_continuousOn (hc.mono hW₂Ω)
  have hlam := ha.pos
  obtain ⟨C₂, hC₂, hgrad⟩ := exists_toReal_eLpNorm_gradient_le_of_thickening (ι := ι)
    (max (Lam / lam) (max (δ * β / lam) (δ ^ 2 * γ / lam)))
  refine ⟨1 + C₂ * δ / lam + C₂ / δ, by positivity, fun f u hu => ?_⟩
  have hWΩ' : (W : Set (EuclideanSpace ℝ ι)) ⊆ Omega := subset_closure.trans hWΩ
  -- Caccioppoli's inequality at distance `δ` from `∂Ω` bounds the gradient on `W`.
  have hgradW := hgrad mu hδ hTΩ (ha.mono_set hTΩ) (ham.mono_measure hTm)
    ((hb.mono hTΩ).aestronglyMeasurable hmT) ((hc.mono hTΩ).aestronglyMeasurable hmT)
    (ae_restrict_of_forall_mem hmT fun x hx => hβ x (hTW₂ hx))
    (ae_restrict_of_forall_mem hmT fun x hx => (Real.norm_eq_abs _).symm.trans_le (hγ x (hTW₂ hx)))
    (by rw [← div_le_iff₀ hlam]; exact le_max_left _ _)
    (by rw [← div_le_iff₀ hlam]; exact (le_max_left _ _).trans (le_max_right _ _))
    (by rw [← div_le_iff₀ hlam]; exact (le_max_right _ _).trans (le_max_right _ _)) hu
  set A := ‖f‖
  set B := ‖W1p.value u‖
  have hval : ‖W1p.value (W1p.restrictL (SetLike.coe_subset_coe.mp hWΩ') u)‖ ≤ B := by
    rw [Lp.norm_def, eLpNorm_congr_ae (W1p.value_restrictL_ae _ u)]
    exact Lp.toReal_eLpNorm_restrict_le_norm _ hWΩ'
  have hgrad' : ‖W1p.gradient (W1p.restrictL (SetLike.coe_subset_coe.mp hWΩ') u)‖ ≤
      C₂ * (δ * A / lam + B / δ) := by
    rw [Lp.norm_def, eLpNorm_congr_ae (W1p.gradient_restrictL_ae _ u)]
    refine hgradW.trans (mul_le_mul_of_nonneg_left (add_le_add ?_ ?_) hC₂)
    · exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
        (Lp.toReal_eLpNorm_restrict_le_norm _ hTΩ) hδ.le) hlam.le
    · exact div_le_div_of_nonneg_right (Lp.toReal_eLpNorm_restrict_le_norm _ hTΩ) hδ.le
  have e : (1 + C₂ * δ / lam + C₂ / δ) * (A + B) =
      B + C₂ * (δ * A / lam + B / δ) + A + C₂ * δ / lam * B + C₂ / δ * A := by ring
  have h₁ : 0 ≤ C₂ * δ / lam * B := by positivity
  have h₂ : 0 ≤ C₂ / δ * A := by positivity
  have h₃ : 0 ≤ A := norm_nonneg _
  have := (W1p.norm_le_norm_value_add_norm_gradient _).trans (add_le_add hval hgrad')
  linarith


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
    fun z hz => ball_subset_thickening_of_inter_nonempty hz (by linarith)
  -- Glue the local second derivatives and average their bounds.
  obtain ⟨G₀, hGV, hglob⟩ := exists_hasWeakLineDerivOn_eLpNorm_le_of_forall_ball_inter_nonempty
    one_le_two ENNReal.ofNat_ne_top Metric.isOpen_thickening.measurableSet
    ((Lp.aestronglyMeasurable f).mono_measure (Measure.restrict_mono hΩ le_rfl))
    ((Lp.aestronglyMeasurable (W1p.value u)).mono_measure (Measure.restrict_mono hΩ le_rfl))
    (c₁ := c₀ / lam) (c₂ := c₀ / (δ / 5) ^ 2) (κ := 4) hr (by norm_num) fun z hz => by
      have hzΩ := (hsub z hz).trans hΩ
      obtain ⟨G, hG, hGd⟩ := hball mu hr hzΩ (ha.mono_set (hsub z hz)) (hK.mono (hsub z hz)) hb hc
        (ae_restrict_of_ae_restrict_of_subset (hsub z hz) hβ)
        (ae_restrict_of_ae_restrict_of_subset (hsub z hz) hγ) hMΛ
        (mul_le_of_mul_le_of_le hr.le hrδ hMβ hM0) (mul_le_of_mul_le_of_le hr.le hrδ hMK hM0)
        (mul_le_of_mul_le_of_le (by positivity) (pow_le_pow_left₀ hr.le hrδ 2) hMγ hM0) hu y w
      exact ⟨hsub z hz, G, hGd, ENNReal.le_ofReal_mul_add_ofReal_mul_of_toReal_le
        (Lp.eLpNorm_ne_top _) (Lp.eLpNorm_restrict_ne_top f hzΩ) (Lp.eLpNorm_restrict_ne_top _ hzΩ)
        (by positivity) (by positivity) (hG.trans_eq (by ring))⟩
  -- The glued derivative lies in `L²(V)`, with the stated norm.
  rw [finrank_euclideanSpace] at hglob
  replace hglob := hglob.trans (ENNReal.mul_ofReal_mul_add_ofReal_mul_le_ofReal (by finiteness)
    (Lp.eLpNorm_restrict_ne_top f hΩ) (Lp.eLpNorm_restrict_ne_top _ hΩ) (by positivity)
    (by positivity) (by
      rewrite [show (2 * ENNReal.ofReal 4 ^ Fintype.card ι).toReal = 2 * 4 ^ Fintype.card ι by simp]
      exact two_mul_four_pow_mul_add_le _ (by positivity) ENNReal.toReal_nonneg hlam hδ))
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
