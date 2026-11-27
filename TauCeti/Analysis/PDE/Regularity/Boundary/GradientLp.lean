/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.SmallMeanOscillation
import TauCeti.Analysis.PDE.Regularity.Boundary.SmallMeanOscillation
import TauCeti.MeasureTheory.Integral.Average

/-!
# The `W^{1,p}` estimate up to a flat boundary, near an elliptic matrix

Let `H = {x | c₀ < ⟪x, ν⟫}` be an open half-space in `ℝ^{n+1}` and let `u ∈ H¹(ℝ^{n+1})` vanish
off `H` and solve

`-∂ᵢ(aⁱʲ ∂ⱼu) = -div G` in `H`,

that is `∫_H ⟨a ∇u, ∇v⟩ = ∫_H ⟨G, ∇v⟩` for every `v ∈ H¹₀(H)`. So `u` is a weak solution in the
half-space with zero boundary values on the hyperplane. If `a` is close to a single constant matrix
`A`, uniformly elliptic and not necessarily symmetric, wherever `∇u` does not vanish, then

`‖∇u‖_{Lᵖ} ≤ C ‖G‖_{Lᵖ(H)}`, `2 < p < ∞`,

for every such `u` whose gradient lies in `Lᵖ`, with `C` depending only on `n`, `p` and the
ellipticity constants
(`TauCeti.PDE.exists_eLpNorm_gradient_le_of_norm_sub_le_of_ae_gradient_eq_zero`).
This is the form a frozen-coefficient argument at a boundary point uses: for continuous
coefficients, `a` is close to its value at the point on a small half-ball, and that value can be
any elliptic matrix.

## The argument

The field `b` equal to `a` where `∇u` does not vanish and to `A` elsewhere gives the same weak
equation (`TauCeti.PDE.energyFormH1_eq_of_eqOn_of_ae_gradient_eq_zero`) and is within `δ` of `A`
everywhere on `H`. So its mean deviation from `A` over every half-ball is at most `δ`, and the
estimate for coefficients of small mean oscillation on the half-balls,
`TauCeti.PDE.exists_eLpNorm_gradient_le_of_setAverage_inter_le`, applies to `b` with the frozen
matrix `A` on every half-ball.
-/

public section

noncomputable section

open MeasureTheory Metric Set TopologicalSpace InnerProductSpace
open scoped Distributions ENNReal Gradient NNReal

namespace TauCeti

namespace PDE

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin (n + 1))

/-- **The `W^{1,p}` estimate up to a flat boundary, near an elliptic matrix.** Let `2 < p < ∞`
and `0 < λ ≤ Λ`. There are constants `C` and `δ > 0`, depending only on `n`, `p`, `λ` and `Λ`,
with the following property. Let `H = {x | c₀ < ⟪x, ν⟫}` with `ν ≠ 0`, and let `A` be a constant
matrix, uniformly elliptic with constants `λ, Λ` and not necessarily symmetric. Let `a` be a
coefficient matrix measurable on `H` whose bilinear form is within `δ` of that of `A`, in operator
norm, on `s ∩ H` for a measurable set `s`. Let `u ∈ H¹(ℝ^{n+1})` vanish off `H`, let `∇u` vanish
off `s`, and let `u` solve `-∂ᵢ(aⁱʲ ∂ⱼu) = -div G` weakly in `H`, that is
`∫_H ⟨a ∇u, ∇v⟩ = ∫_H ⟨G, ∇v⟩` for every `v ∈ H¹₀(H)`, with `G ∈ Lᵖ(H)`. If `∇u` lies in `Lᵖ`,
then

`‖∇u‖_{Lᵖ} ≤ C ‖G‖_{Lᵖ(H)}`.

No continuity of `a` and no bound on `a` off `s` are assumed. For coefficients continuous up to
the boundary, `A` can be their value at a boundary point and `s` a small ball centred at it. -/
theorem exists_eLpNorm_gradient_le_of_norm_sub_le_of_ae_gradient_eq_zero {p : ℝ≥0∞} (hp : 2 < p)
    (hp_top : p ≠ ∞) (lam Lam : ℝ) :
    ∃ C : ℝ≥0, ∃ δ : ℝ, 0 < δ ∧
      ∀ {H : Opens E} {ν : E} {c₀ : ℝ} {a : E → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
        {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {s : Set E},
        ν ≠ 0 → (∀ x, x ∈ H ↔ c₀ < ⟪x, ν⟫_ℝ) → MeasurableSet s →
        AEStronglyMeasurable a (volume.restrict H) →
        UniformlyEllipticOn univ (fun _ : E => A) lam Lam →
        (∀ x ∈ s, x ∈ H → ‖matrixBilinearForm (a x) - matrixBilinearForm A‖ ≤ δ) →
        ∀ (u : W1p volume (⊤ : Opens E) 2) (G : E → E),
          (∀ᵐ x, x ∉ H → W1p.value u x = 0) → (∀ᵐ x, x ∉ s → W1p.gradient u x = 0) →
          (∀ v : W1p0 volume H 2,
            energyFormH1 a 0 0 (W1p.restrictL (le_top : H ≤ ⊤) u) (v : W1p volume H 2) =
              ∫ x in H, ⟪G x, W1p.gradient (v : W1p volume H 2) x⟫_ℝ) →
          MemLp (W1p.gradient u : E → E) p volume → MemLp G p (volume.restrict H) →
          eLpNorm (W1p.gradient u : E → E) p volume ≤ C * eLpNorm G p (volume.restrict H) := by
  obtain ⟨C, δ, hδ, h⟩ :=
    exists_eLpNorm_gradient_le_of_setAverage_inter_le (n := n) hp hp_top lam (Lam + 1)
  have hm : 0 ≤ min δ 1 := (lt_min hδ one_pos).le
  refine ⟨C, min δ 1, lt_min hδ one_pos, ?_⟩
  intro H ν c₀ a A s hν hH hs ham hA hsA u G hu0 hus hu hgp hGp
  classical
  -- Replace `a` by `A` off `s ∩ H`, where `∇u` vanishes.
  set b : E → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ := (s ∩ H).piecewise a (fun _ => A) with hbdef
  have hbA (y : E) : ‖matrixBilinearForm (b y) - matrixBilinearForm A‖ ≤ min δ 1 := by
    by_cases hy : y ∈ s ∩ H
    · rw [hbdef, piecewise_eq_of_mem _ _ _ hy]
      exact hsA y hy.1 hy.2
    · rw [hbdef, piecewise_eq_of_notMem _ _ _ hy]
      refine ContinuousLinearMap.opNorm_le_bound₂ _ hm fun η ξ => ?_
      simp only [FunLike.coe_sub, Pi.sub_apply, sub_self, zero_apply, norm_zero]
      positivity
  -- `u` solves the equation with `b`, which agrees with `a` where `∇u` does not vanish.
  have hub (v : W1p0 volume H 2) :
      energyFormH1 b 0 0 (W1p.restrictL (le_top : H ≤ ⊤) u) (v : W1p volume H 2) =
        ∫ x in H, ⟪G x, W1p.gradient (v : W1p volume H 2) x⟫_ℝ := by
    rw [← hu v]
    refine energyFormH1_eq_of_eqOn_of_ae_gradient_eq_zero (s := s ∩ H)
      (fun y hy => by rw [hbdef, piecewise_eq_of_mem _ _ _ hy]) 0 0 ?_ _
    filter_upwards [W1p.gradient_restrictL_ae (le_top : H ≤ ⊤) u,
      ae_restrict_of_ae (μ := volume) (s := (H : Set E)) hus,
      ae_restrict_mem H.isOpen.measurableSet]
      with x h1 h2 h3 hx
    rw [h1]
    exact h2 fun hxs => hx ⟨hxs, h3⟩
  refine h (a := b) hν hH
    (ham.restrict.piecewise (hs.inter H.isOpen.measurableSet).nullMeasurableSet
      aestronglyMeasurable_const) (fun x _ => ?_) (fun c r _ _ => ⟨A, ?_, ?_⟩) u G hu0
    (fun φ => ?_) hgp hGp
  · -- `b x` is within `1` of `A`, whose form has norm at most `Λ`.
    exact (norm_le_insert' (matrixBilinearForm (b x)) (matrixBilinearForm A)).trans
      (add_le_add (hA.opNorm_matrixBilinearForm_le (mem_univ 0)) ((hbA x).trans (min_le_right _ _)))
  · exact (hA.mono_set (subset_univ _)).mono_constants hA.pos le_rfl (by linarith)
  · -- `b` is within `min δ 1` of `A` everywhere, so on average over every half-ball.
    refine (Real.le_norm_self _).trans
      ((norm_setAverage_le_of_norm_le_const hm fun x _ => ?_).trans (min_le_left _ _))
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact hbA x
  · -- Test functions lie in `H¹₀(H)`, and their gradients are the classical ones.
    rw [hub ⟨_, W1p.ofTestFunctionₗ_mem_w1p0Submodule φ⟩]
    refine integral_congr_ae ?_
    filter_upwards [gradientTestFunctionLp_apply_ae (mu := volume) (Omega := H) 2 φ] with x hx
    rw [W1p.gradient_ofTestFunctionₗ, hx]

end PDE

end TauCeti
