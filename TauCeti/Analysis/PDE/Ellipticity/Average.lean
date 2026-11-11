/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Average
public import TauCeti.Analysis.PDE.Ellipticity.Basic

/-!
# Averages of uniformly elliptic coefficient fields

Let `a` be a matrix-valued coefficient field, uniformly elliptic with constants `0 < λ ≤ Λ` on a
set `s` of positive finite measure. Its entrywise average `ā = ⨍_s a` is again uniformly elliptic
with the same constants (`TauCeti.PDE.UniformlyEllipticOn.setAverage`): the bilinear form of `ā`
is the average of the bilinear forms of `a`
(`TauCeti.PDE.dotProduct_mulVec_setAverage`), and both defining inequalities survive averaging.

Freezing a variable coefficient at its average over a ball, rather than at its value at a point,
is how equations with coefficients of vanishing mean oscillation are compared with
constant-coefficient equations: the frozen operator is uniformly elliptic, and the error of the
comparison is measured by the mean oscillation `⨍_s |a - ā|` of the coefficients, which makes
sense for discontinuous `a`.
-/

public section

open MeasureTheory Matrix

namespace TauCeti

namespace PDE

variable {X n : Type*} [MeasurableSpace X] [Fintype n] {μ : Measure X} {s : Set X}
  {a : X → Matrix n n ℝ} {lam Lam : ℝ}

/-- The bilinear form of the entrywise average of a matrix field is the average of its bilinear
forms: `η ⬝ (⨍_s a) ξ = ⨍_s η ⬝ a ξ`. -/
theorem dotProduct_mulVec_setAverage (ha : ∀ i j, IntegrableOn (fun x => a x i j) s μ)
    (η ξ : n → ℝ) :
    η ⬝ᵥ ((Matrix.of fun i j => ⨍ x in s, a x i j ∂μ) *ᵥ ξ) = ⨍ x in s, η ⬝ᵥ (a x *ᵥ ξ) ∂μ := by
  have hrow : ∀ i, IntegrableOn (fun x => ∑ j, a x i j * ξ j) s μ := fun i =>
    integrable_finsetSum _ fun j _ => (ha i j).mul_const _
  simp only [dotProduct, mulVec, of_apply, setAverage_eq, smul_eq_mul]
  rw [integral_finsetSum _ fun i _ => (hrow i).const_mul _, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_const_mul, integral_finsetSum _ fun j _ => (ha i j).mul_const _, Finset.mul_sum,
    Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_mul_const]
  ring

/-- **Averages of uniformly elliptic fields.** If `a` is uniformly elliptic with constants
`λ, Λ` on a measurable set `s` of positive finite measure and has integrable entries there, then
its entrywise average `⨍_s a` is a constant coefficient matrix that is uniformly elliptic with the
same constants. -/
theorem UniformlyEllipticOn.setAverage [DecidableEq n] {Y : Type*}
    (h : UniformlyEllipticOn s a lam Lam) (hs : MeasurableSet s) (hμ0 : μ s ≠ 0) (hμ : μ s ≠ ⊤)
    (ha : ∀ i j, IntegrableOn (fun x => a x i j) s μ) (t : Set Y) :
    UniformlyEllipticOn t (fun _ => Matrix.of fun i j => ⨍ x in s, a x i j ∂μ) lam Lam := by
  have hint : ∀ η ξ : n → ℝ, IntegrableOn (fun x => η ⬝ᵥ (a x *ᵥ ξ)) s μ := fun η ξ => by
    simp only [dotProduct, mulVec]
    exact integrable_finsetSum _ fun i _ =>
      (integrable_finsetSum _ fun j _ => (ha i j).mul_const _).const_mul _
  have hpos : 0 < (μ s).toReal⁻¹ := inv_pos.2 (ENNReal.toReal_pos hμ0 hμ)
  -- An average of functions bounded below by `c` on `s` is bounded below by `c`.
  have hle : ∀ (c : ℝ) (g : X → ℝ), IntegrableOn g s μ → (∀ x ∈ s, c ≤ g x) →
      c ≤ ⨍ x in s, g x ∂μ := fun c g hg hcg => by
    rw [← setAverage_const hμ0 hμ c, setAverage_eq, setAverage_eq, smul_eq_mul, smul_eq_mul]
    exact mul_le_mul_of_nonneg_left (setIntegral_mono_on (integrableOn_const hμ) hg hs hcg)
      hpos.le
  refine UniformlyEllipticOn.of_bounds h.pos h.le (fun _ _ ξ => ?_) (fun _ _ η ξ => ?_)
  · rw [toQuadraticForm'_apply, dotProduct_mulVec_setAverage ha]
    refine hle _ _ (hint _ _) fun x hx => ?_
    rw [← toQuadraticForm'_apply]
    exact h.lower_bound hx ξ
  · rw [dotProduct_mulVec_setAverage ha, abs_le]
    constructor
    · refine hle _ _ (hint _ _) fun x hx => ?_
      exact neg_le_of_abs_le (h.upper_bound hx η ξ)
    · rw [← neg_le_neg_iff, ← average_neg]
      refine hle _ _ (hint _ _).neg fun x hx => ?_
      exact neg_le_neg (le_of_abs_le (h.upper_bound hx η ξ))

end PDE

end TauCeti
