/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.Hessian.Interior
public import TauCeti.Topology.Instances.Matrix
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import TauCeti.MeasureTheory.Function.LpSeminorm.Ball

/-!
# The Calderón–Zygmund estimate in `W^{2,p}(ℝⁿ)` for uniformly continuous coefficients

Let `0 < n` and `1 < p < ∞`. This file proves the global `W^{2,p}` estimate on the whole space for
strong solutions of a non-divergence-form equation `∑ᵢⱼ aᵢⱼ ∂ᵢ∂ⱼu = f` whose coefficients are
uniformly elliptic, bounded and uniformly continuous: there is a constant `C` such that every
`u ∈ W^{2,p}(ℝⁿ)` with `∑ᵢⱼ aᵢⱼ ∂ᵢ∂ⱼu = f ∈ Lᵖ(ℝⁿ)` almost everywhere satisfies

`‖D²u‖_{Lᵖ} ≤ C (‖f‖_{Lᵖ} + ‖u‖_{Lᵖ})`,

where `D²u` is the weak Hessian `TauCeti.Wkp.iteratedGradient 1 u`.

The dependence of `C` on the coefficients is explicit
(`TauCeti.PDE.exists_norm_iteratedGradient_le_of_sum_mul_inner_eq_of_dist_lt_abs_sub_le`). There
are `C₀` and `δ > 0`, depending only on `n` and `p`, such that if `λ ‖ξ‖² ≤ ξᵀ a(x) ξ` with
`0 < λ`, `|aᵢⱼ(x)| ≤ Λ`, and the entries of `a` vary by at most `δ λ` between points at distance
less than `ρ`, then

`‖D²u‖_{Lᵖ} ≤ C₀ (‖f‖_{Lᵖ} / λ + (1 + Λ / λ)² / ρ² ‖u‖_{Lᵖ})`.

Uniformly continuous coefficients admit such a `ρ` for every `δ`, which gives the qualitative
form (`TauCeti.PDE.exists_norm_iteratedGradient_le_of_sum_mul_inner_eq_of_uniformContinuous`).
No condition at infinity is imposed on `a` beyond these uniform bounds. This is the a priori
estimate behind strong solvability in `W^{2,p}(ℝⁿ)` by the method of continuity.

## The argument

The interior estimate on balls
(`TauCeti.PDE.exists_mul_lpNorm_iteratedGradient_ball_le_of_sum_mul_inner_add_inner_add_mul_eq`),
with the coefficients frozen at `a(y)`, bounds `‖D²u‖_{Lᵖ(B(y, ρ/2))}` by the `Lᵖ(B(y, ρ))` norms of
`f` and `u`, with constants independent of the centre `y`. Averaging the `p`-th powers of these
local estimates over all centres `y ∈ ℝⁿ` turns them into the global estimate, at the cost of
the volume ratio `|B(0, ρ)| / |B(0, ρ/2)| = 2ⁿ`
(`TauCeti.lpNorm_le_of_ae_lpNorm_restrict_ball_le_add`). This replaces a covering of `ℝⁿ` by balls
with bounded overlap.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Theorem 9.11 and its proof (local estimates on balls of small oscillation).
-/

public section

noncomputable section

namespace TauCeti

namespace PDE

open MeasureTheory TopologicalSpace Metric Module Filter
open scoped ENNReal NNReal InnerProductSpace

variable {n : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **The Calderón–Zygmund estimate in `W^{2,p}(ℝⁿ)` for coefficients of small local
oscillation.** Let `0 < n` and `1 < p < ∞`. There are constants `C` and `δ > 0`, depending only on
`n` and `p`, with the following property. Let `a` be a measurable matrix-valued coefficient with
`λ ‖ξ‖² ≤ ξᵀ a(x) ξ`, `0 < λ`, and `|aᵢⱼ(x)| ≤ Λ` for every `x`, whose entries vary by at most
`δ λ` between points at distance less than `ρ`, where `0 < ρ`. Then every `u ∈ W^{2,p}(ℝⁿ)` with
`∑ᵢⱼ aᵢⱼ ∂ᵢ∂ⱼu = f ∈ Lᵖ(ℝⁿ)` almost everywhere satisfies

`‖D²u‖_{Lᵖ} ≤ C (‖f‖_{Lᵖ} / λ + (1 + Λ / λ)² / ρ² ‖u‖_{Lᵖ})`,

where `D²u` is the weak Hessian `TauCeti.Wkp.iteratedGradient 1 u`. -/
theorem exists_norm_iteratedGradient_le_of_sum_mul_inner_eq_of_dist_lt_abs_sub_le (hn : 0 < n)
    (hp : 1 < p) (hp_top : p ≠ ∞) :
    ∃ C : ℝ≥0, ∃ δ : ℝ, 0 < δ ∧ ∀ {lam Λ ρ : ℝ}, 0 < lam → 0 < ρ →
      ∀ {a : EuclideanSpace ℝ (Fin n) → Matrix (Fin n) (Fin n) ℝ}, AEStronglyMeasurable a volume →
        (∀ x (ξ : EuclideanSpace ℝ (Fin n)), lam * ‖ξ‖ ^ 2 ≤ (a x).toQuadraticForm' ξ) →
        (∀ x i j, |a x i j| ≤ Λ) →
        (∀ x y, dist x y < ρ → ∀ i j, |a x i j - a y i j| ≤ δ * lam) →
      ∀ (u : Wkp (volume : Measure (EuclideanSpace ℝ (Fin n))) ⊤ p 2)
        (f : Lp ℝ p ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict
          (⊤ : Opens (EuclideanSpace ℝ (Fin n))))),
        (∀ᵐ x, ∑ i, ∑ j, a x i j * ⟪Wkp.iteratedGradient 1 u x (EuclideanSpace.single i 1),
          EuclideanSpace.single j 1⟫_ℝ = f x) →
        ‖Wkp.iteratedGradient 1 u‖ ≤
          C * (‖f‖ / lam + (1 + Λ / lam) ^ 2 / ρ ^ 2 * ‖Wkp.value 2 u‖) := by
  obtain ⟨C₀, δ, hδ, hball⟩ :=
    exists_mul_lpNorm_iteratedGradient_ball_le_of_sum_mul_inner_add_inner_add_mul_eq hn hp hp_top
  refine ⟨8 * 2 ^ n * C₀, δ, hδ, fun {lam Λ ρ} hlam hρ {a} ha hA haΛ hosc u f heq => ?_⟩
  have hμ : (volume : Measure (EuclideanSpace ℝ (Fin n))).restrict
      ((⊤ : Opens (EuclideanSpace ℝ (Fin n))) : Set (EuclideanSpace ℝ (Fin n))) = volume := by
    simp
  -- Elements of `Lᵖ` over `⊤` are `Lᵖ` functions for `volume`, with the same norm.
  have hmem : ∀ {G : Type} [NormedAddCommGroup G]
      (g : Lp G p ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict
        (⊤ : Opens (EuclideanSpace ℝ (Fin n))))), MemLp g p volume := fun g => by
    convert Lp.memLp g using 1
    exact hμ.symm
  have hnorm : ∀ {G : Type} [NormedAddCommGroup G]
      (g : Lp G p ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict
        (⊤ : Opens (EuclideanSpace ℝ (Fin n))))), ‖g‖ = lpNorm g p volume := fun g => by
    rw [Lp.norm_def, ← toReal_eLpNorm]
    exact congrArg (fun ν => (eLpNorm (⇑g) p ν).toReal) hμ
  set r := ρ / 2 with hr_def
  have hr : 0 < r := half_pos hρ
  have h2r : 2 * r = ρ := by rw [hr_def]; ring
  set c₁ : ℝ := 4 * C₀ / lam with hc₁_def
  set c₂ : ℝ := 4 * C₀ * (1 + Λ / lam) ^ 2 / ρ ^ 2 with hc₂_def
  -- The interior estimate on `B(y, ρ)`, with the coefficients frozen at `a(y)`, divided by
  -- `(ρ - r)² = ρ² / 4`.
  have hlocal : ∀ y, lpNorm (Wkp.iteratedGradient 1 u) p (volume.restrict (ball y r)) ≤
      c₁ * lpNorm f p (volume.restrict (ball y (2 * r))) +
        c₂ * lpNorm (Wkp.value 2 u) p (volume.restrict (ball y (2 * r))) := fun y => by
    -- Apply the interior estimate without lower-order terms.
    have key := hball (b := 0) (c := 0) (β := 0) (γ := 0) hlam (hA y) (half_lt_self hρ)
      (by simp) ha.restrict le_rfl
      (Eventually.of_forall fun x hx i j => hosc x y (mem_ball.1 hx) i j)
      (Eventually.of_forall fun x _ i j => haΛ x i j) aestronglyMeasurable_const
      (Eventually.of_forall fun _ _ => by simp) aestronglyMeasurable_const
      (Eventually.of_forall fun _ _ => by simp) u f
      (ae_restrict_of_ae (heq.mono fun x hx => by simpa using hx))
    simp only [zero_mul, add_zero] at key
    rw [show ρ - r = r by rw [hr_def]; ring] at key
    rw [h2r]
    refine le_of_mul_le_mul_left (key.trans_eq ?_) (by positivity : 0 < r ^ 2)
    rw [hr_def, hc₁_def, hc₂_def]
    field_simp
    ring
  have hglobal := lpNorm_le_of_ae_lpNorm_restrict_ball_le_add hp.le hp_top (hmem _) (hmem f)
    (hmem _) (by positivity) (by positivity) hr (Eventually.of_forall hlocal)
  rw [finrank_euclideanSpace_fin, ← hnorm, ← hnorm, ← hnorm] at hglobal
  refine hglobal.trans_eq ?_
  rw [hc₁_def, hc₂_def]
  push_cast
  ring

/-- **The Calderón–Zygmund estimate in `W^{2,p}(ℝⁿ)` for uniformly continuous coefficients.**
Let `0 < n` and `1 < p < ∞`, and let `a` be a uniformly continuous matrix-valued coefficient with
`λ ‖ξ‖² ≤ ξᵀ a(x) ξ`, `0 < λ`, and `|aᵢⱼ(x)| ≤ Λ` for every `x`. Then there is a constant `C`,
depending on `n`, `p`, `λ`, `Λ` and the modulus of continuity of `a`, such that every
`u ∈ W^{2,p}(ℝⁿ)` with `∑ᵢⱼ aᵢⱼ ∂ᵢ∂ⱼu = f ∈ Lᵖ(ℝⁿ)` almost everywhere satisfies

`‖D²u‖_{Lᵖ} ≤ C (‖f‖_{Lᵖ} + ‖u‖_{Lᵖ})`,

where `D²u` is the weak Hessian `TauCeti.Wkp.iteratedGradient 1 u`. -/
theorem exists_norm_iteratedGradient_le_of_sum_mul_inner_eq_of_uniformContinuous (hn : 0 < n)
    (hp : 1 < p) (hp_top : p ≠ ∞) {a : EuclideanSpace ℝ (Fin n) → Matrix (Fin n) (Fin n) ℝ}
    (ha : UniformContinuous a) {lam Λ : ℝ} (hlam : 0 < lam)
    (hA : ∀ x (ξ : EuclideanSpace ℝ (Fin n)), lam * ‖ξ‖ ^ 2 ≤ (a x).toQuadraticForm' ξ)
    (haΛ : ∀ x i j, |a x i j| ≤ Λ) :
    ∃ C : ℝ, ∀ (u : Wkp (volume : Measure (EuclideanSpace ℝ (Fin n))) ⊤ p 2)
      (f : Lp ℝ p ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict
        (⊤ : Opens (EuclideanSpace ℝ (Fin n))))),
      (∀ᵐ x, ∑ i, ∑ j, a x i j * ⟪Wkp.iteratedGradient 1 u x (EuclideanSpace.single i 1),
        EuclideanSpace.single j 1⟫_ℝ = f x) →
      ‖Wkp.iteratedGradient 1 u‖ ≤ C * (‖f‖ + ‖Wkp.value 2 u‖) := by
  obtain ⟨C, δ, hδ, hest⟩ :=
    exists_norm_iteratedGradient_le_of_sum_mul_inner_eq_of_dist_lt_abs_sub_le hn hp hp_top
  obtain ⟨ρ, hρ, hosc⟩ := ha.exists_pos_forall_abs_sub_le (mul_pos hδ hlam)
  set M := max lam⁻¹ ((1 + Λ / lam) ^ 2 / ρ ^ 2)
  refine ⟨C * M, fun u f heq => ?_⟩
  refine (hest hlam hρ ha.continuous.aestronglyMeasurable hA haΛ hosc u f heq).trans ?_
  rw [mul_assoc]
  gcongr
  rw [div_eq_inv_mul, mul_add]
  gcongr
  exacts [le_max_left _ _, le_max_right _ _]

end PDE

end TauCeti
