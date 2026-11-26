/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Interpolation.ComplexMethod.Basic
import TauCeti.Analysis.Normed.Interpolation.ComplexMethod.Symmetry
import TauCeti.Analysis.SpecialFunctions.Exp.Bounds

/-!
# Endpoint norm formulas for the complex interpolation method

At the boundary points `θ = 0` and `θ = 1`, the complex interpolation norm of the class of an
admissible trace pair `g = (g₀, g₁)` reduces to the endpoint norm of the trace evaluated at `0`:

* `TauCeti.CompatibleCouple.ComplexMethodSpace.norm_mk_zero`: `‖mk 0 g‖ = ‖g₀ 0‖`;
* `TauCeti.CompatibleCouple.ComplexMethodSpace.norm_mk_one`: `‖mk 1 g‖ = ‖g₁ 0‖`;
* `TauCeti.CompatibleCouple.ComplexMethodSpace.norm_toFst`: `‖toFst u‖ = ‖u‖`;
* `TauCeti.CompatibleCouple.ComplexMethodSpace.norm_toSnd`: `‖toSnd u‖ = ‖u‖`;
* `TauCeti.CompatibleCouple.ComplexMethodSpace.norm_ofInter_zero`,
  `TauCeti.CompatibleCouple.ComplexMethodSpace.norm_ofInter_one`: `‖ofInter 0 x‖ = ‖C.interFst x‖`
  and `‖ofInter 1 x‖ = ‖C.interSnd x‖`.

These identities hold for any compatible couple of normed spaces without completeness or density
assumptions, by multiplying with Gaussian-type holomorphic cutoff factors `exp (A (z² - 2 z))` and
using symmetry (`ComplexMethodSpace.swap`). Consequently, boundary evaluation at `0` (`toFst`,
`toSnd`) is an isometric embedding on `[X₀, X₁]_0` and `[X₀, X₁]_1` into the endpoint spaces
`X₀` and `X₁`, and these endpoint identifications supply the `θ = 0` and `θ = 1` boundary cases of
Bergh–Löfström's sequence-space theorem `ComplexMethodSpace.piLpEquiv`.
-/

public noncomputable section

open Complex Complex.HadamardThreeLines Set TauCeti.Complex.HadamardThreeLines
open scoped ZeroAtInfty

namespace TauCeti.CompatibleCouple.ComplexMethodSpace

variable {X₀ X₁ V : Type*}
  [NormedAddCommGroup X₀] [NormedSpace ℂ X₀] [NormedAddCommGroup X₁] [NormedSpace ℂ X₁]
  [AddCommGroup V] [Module ℂ V] [TopologicalSpace V] [ContinuousAdd V] [T1Space V]
  {C : CompatibleCouple ℂ X₀ X₁ V}

private theorem norm_mk_zero_le (g : C.stripTraces) : ‖mk 0 g‖ ≤ ‖g.val.1 0‖ := by
  refine le_of_forall_pos_lt_add fun ε hε => ?_
  obtain ⟨δ, hδ, hclose⟩ := Metric.continuousAt_iff.1
    ((map_continuous g.val.1).continuousAt (x := 0)) (ε / 2) (half_pos hε)
  obtain ⟨A, hAgt⟩ := exists_gt (max 0 (max (2 * ‖g.val.1‖ / (δ ^ 2 * ε)) (2 * ‖g.val.2‖ / ε)))
  have hA : 0 < A := (le_max_left _ _).trans_lt hAgt
  let c : ℂ → ℂ := fun z => Complex.exp (-(A : ℂ)) * stripGaussian A 1 z
  have hc_norm (z : ℂ) : ‖c z‖ = Real.exp (-A + A * ((z.re - 1) ^ 2 - z.im ^ 2)) := by
    simp only [c, norm_mul, Complex.norm_exp, neg_re, ofReal_re, norm_stripGaussian, ← Real.exp_add]
  have hc_zero : ‖c ((0 : ℝ) : ℂ)‖ = 1 := by rw [hc_norm]; simp
  have hc_fst (t : ℝ) : ‖c (t * I)‖ = Real.exp (-(A * t ^ 2)) := by
    rw [hc_norm]; congr 1; simp only [mul_I_re, ofReal_im, neg_zero, mul_I_im, ofReal_re]; ring
  have hc_snd (t : ℝ) : ‖c (1 + t * I)‖ = Real.exp (-(A * (1 + t ^ 2))) := by
    rw [hc_norm]; congr 1; simp only [add_re, one_re, mul_I_re, ofReal_im, neg_zero, add_zero,
      add_im, one_im, mul_I_im, ofReal_re, zero_add]; ring
  have hc_le (z : ℂ) (hz : z ∈ verticalClosedStrip 0 1) : ‖c z‖ ≤ 1 := by
    rw [hc_norm]
    exact Real.exp_le_one_iff.2 <| by
      nlinarith [(sq_le_one_iff_abs_le_one (z.re - 1)).2
        (abs_le.2 ⟨by linarith [hz.1], by linarith [hz.2]⟩), sq_nonneg z.im, hA.le]
  have hbound := norm_smul_mk_le_of_diffContOnCl 0 g
    ((differentiable_stripGaussian A 1).const_mul (Complex.exp (-(A : ℂ)))).diffContOnCl hc_le
    (B := ‖g.val.1 0‖ + ε / 2)
    (fun t => by
      rw [norm_smul]; by_cases ht : |t| < δ
      · have hd := hclose (by simpa [Real.dist_eq] using ht); rw [dist_eq_norm] at hd
        exact (mul_le_of_le_one_left (norm_nonneg _) (hc_le _ (by simp))).trans
          (by linarith [norm_sub_norm_le (g.val.1 t) (g.val.1 0)])
      · have hsq : δ ^ 2 ≤ t ^ 2 := by simpa [sq_abs] using pow_le_pow_left₀ hδ.le (not_lt.1 ht) 2
        have hA1' : 2 * ‖g.val.1‖ / ε < A * δ ^ 2 := (div_lt_iff₀ hε).2 <| by
          nlinarith [(div_lt_iff₀ (by positivity)).1
            (((le_max_left _ _).trans (le_max_right _ _)).trans_lt hAgt)]
        rw [hc_fst]
        exact (exp_neg_mul_le_half_of_le (norm_nonneg _) (g.val.1.norm_coe_le_norm t)
          (by positivity) (by nlinarith) hε hA1').trans (le_add_of_nonneg_left (norm_nonneg _)))
    (fun t => by
      rw [norm_smul, hc_snd]
      exact (exp_neg_mul_le_half_of_le (norm_nonneg _) (g.val.2.norm_coe_le_norm t)
        hA (by nlinarith [sq_nonneg t]) hε
        (((le_max_right _ _).trans (le_max_right _ _)).trans_lt hAgt)).trans
        (le_add_of_nonneg_left (norm_nonneg _)))
  rw [norm_smul, hc_zero, one_mul] at hbound; linarith [half_lt_self hε]

/-- At `θ = 0`, the quotient norm of an admissible trace pair is the norm in `X₀` of its left
boundary trace at `0`. -/
@[simp] theorem norm_mk_zero (g : C.stripTraces) : ‖mk 0 g‖ = ‖(g : C₀(ℝ, X₀) × C₀(ℝ, X₁)).1 0‖ :=
  le_antisymm (norm_mk_zero_le g) (by simpa only [toFst_mk] using norm_toFst_le (mk 0 g))

/-- At `θ = 1`, the quotient norm of an admissible trace pair is the norm in `X₁` of its right
boundary trace at `0`. -/
@[simp] theorem norm_mk_one (g : C.stripTraces) : ‖mk 1 g‖ = ‖(g : C₀(ℝ, X₀) × C₀(ℝ, X₁)).2 0‖ := by
  rw [← (swap C 1).norm_map (mk 1 g), swap_mk, sub_self, norm_mk_zero]
  simp only [stripTracesSwap_apply_fst, neg_zero]

/-- `ComplexMethodSpace.toFst : [X₀, X₁]_0 →L[ℂ] X₀` preserves norms without completeness
assumptions. -/
@[simp] theorem norm_toFst (u : C.ComplexMethodSpace 0) : ‖toFst u‖ = ‖u‖ := by
  obtain ⟨g, rfl⟩ := mk_surjective u; simp

/-- `ComplexMethodSpace.toSnd : [X₀, X₁]_1 →L[ℂ] X₁` preserves norms without completeness
assumptions. -/
@[simp] theorem norm_toSnd (u : C.ComplexMethodSpace 1) : ‖toSnd u‖ = ‖u‖ := by
  obtain ⟨g, rfl⟩ := mk_surjective u; simp

/-- On `X₀ ∩ X₁`, the `[X₀, X₁]_0` norm coincides with the `X₀` norm without completeness
assumptions. -/
@[simp] theorem norm_ofInter_zero (x : C.inter) : ‖ofInter 0 x‖ = ‖C.interFst x‖ := by
  rw [← norm_toFst, toFst_ofInter]

/-- On `X₀ ∩ X₁`, the `[X₀, X₁]_1` norm coincides with the `X₁` norm without completeness
assumptions. -/
@[simp] theorem norm_ofInter_one (x : C.inter) : ‖ofInter 1 x‖ = ‖C.interSnd x‖ := by
  rw [← norm_toSnd, toSnd_ofInter]

end TauCeti.CompatibleCouple.ComplexMethodSpace
