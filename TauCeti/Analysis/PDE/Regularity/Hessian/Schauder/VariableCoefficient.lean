/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.Hessian.Schauder.Basic
public import Mathlib.Topology.MetricSpace.HolderNorm
import TauCeti.Analysis.Holder.Lp
import TauCeti.Analysis.InnerProductSpace.Orthonormal.Multilinear
import TauCeti.Analysis.Normed.Operator.Holder
import TauCeti.Topology.MetricSpace.Holder.Basic

/-!
# Schauder estimates for coefficients of small oscillation

This file proves a global a priori Schauder estimate for a non-divergence-form operator with
Hölder coefficients close to a constant elliptic matrix. The solution is assumed `C²`, with a
globally Hölder Hessian in `L²`. The resulting Hölder constant depends only on the forcing,
the `L²` Hessian, the coefficient bounds and the chosen scale; its initial Hölder constant is
absorbed. Compactly supported `C^{2,α}` functions are an important application.

The scale condition combines the uniform oscillation `ε` with `L r^α`, where `L` bounds the
coefficient Hölder constants. Thus an arbitrary finite `L` is allowed by taking `r` sufficiently
small, provided the uniform oscillation is strictly below the perturbation threshold. This is
the global estimate used after applying an interior cutoff; localization and covering are
separate from the estimate here.

The proof freezes the coefficients, uses
`TauCeti.PDE.exists_holderOnWith_iteratedFDeriv_two_of_sum_smul_fderiv_fderiv`, and absorbs the
Hölder norm of the Hessian. The pointwise interpolation estimate is the arbitrary-scale form
of `HolderWith.enorm_le_add_eLpNorm`.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Chapter 6, proof of the interior Schauder estimate by freezing coefficients.
-/

public section

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal ENNReal

namespace TauCeti.PDE

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin (n + 1))

/-- The error of freezing a Hölder coefficient field has the product Hölder bound. -/
private theorem holderWith_frozen_hessian_error {α ε L J B : ℝ≥0}
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    {a : E → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {H : E → E [×2]→L[ℝ] ℝ}
    (ha : ∀ x i j, |a x i j - A i j| ≤ ε)
    (hL : ∀ i j, HolderWith L α (fun x => a x i j))
    (hJ : HolderWith J α H) (hB : ∀ x, ‖H x‖ ≤ B) :
    HolderWith (((n + 1 : ℝ≥0) ^ 2) * (ε * J + B * L)) α
      (fun x => ∑ i, ∑ j, (A i j - a x i j) *
        H x ![EuclideanSpace.single i 1, EuclideanSpace.single j 1]) := by
  have hterm (i j : Fin (n + 1)) : HolderWith (ε * J + B * L) α (fun x => (A i j - a x i j) *
      H x ![EuclideanSpace.single i 1, EuclideanSpace.single j 1]) := by
    have hc : HolderWith L α (fun x => A i j - a x i j) := fun x y => by
      simpa only [edist_sub_left] using hL i j x y
    have hh : HolderWith J α (fun x => H x
        ![EuclideanSpace.single i 1, EuclideanSpace.single j 1]) := by
      simpa using holderOnWith_univ.mp
        ((holderOnWith_univ.mpr hJ).apply_orthonormalBasis (EuclideanSpace.basisFun _ ℝ) i j)
    have hp := (ContinuousLinearMap.mul ℝ ℝ).holderWith_comp₂ hc hh
      (Mf := ε) (Mg := B)
      (fun x => by simpa [Real.norm_eq_abs, abs_sub_comm] using ha x i j)
      (fun x => by
        simpa using ((H x).norm_apply_orthonormalBasis_le (EuclideanSpace.basisFun _ ℝ) i j).trans
          (hB x))
    simpa only [ContinuousLinearMap.opNNNorm_mul, one_mul,
      ContinuousLinearMap.mul_apply'] using hp
  exact (HolderWith.sum fun i _ => HolderWith.sum fun j _ => hterm i j).mono
    (le_of_eq (by simp [Finset.card_univ]; ring))

/-- **Global a priori Schauder estimate for coefficients of small oscillation.**
For `0 < α < 1` there is `C > 0`, depending only on dimension and `α`, with the following
property. Put `κ = C (Λ / λ)^(1 + (n+1)/4 + α/2)`. Let `A` have ellipticity bounds `λ, Λ`, with
`λ > 0`, and assume every coefficient entry is globally `α`-Hölder with constant `L` and within
`ε` of the corresponding entry of `A`. If

`2 κ (n+1)² (ε + L r^α) ≤ λ`,

then a global `C²` function with globally `α`-Hölder Hessian `H ∈ L²` satisfies

`[H]_α ≤ 2 κ ([Lu]_α / λ + ((n+1)² L / λ |B_r|^(-1/2) + r^(-(n+1)/2-α)) ‖H‖₂)`.

The Hölder hypothesis on the Hessian is an a priori regularity assumption; its constant does
not occur in the conclusion. No compact-support or boundary hypothesis is imposed. -/
theorem exists_holderWith_iteratedFDeriv_two_of_sum_smul_fderiv_fderiv_of_abs_sub_le
    {α : ℝ≥0} (hα : 0 < α) (hα1 : α < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {lam Lam : ℝ},
      0 < lam → (∀ ξ : E, lam * ‖ξ‖ ^ 2 ≤ A.toQuadraticForm' ξ) →
      (∀ ξ : E, A.toQuadraticForm' ξ ≤ Lam * ‖ξ‖ ^ 2) →
      ∀ {a : E → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {ε L K : ℝ≥0} {r : ℝ},
      0 < r →
      2 * (C * (Lam / lam) ^ (1 + ((n : ℝ) + 1) / 4 + α / 2)) * ((n : ℝ) + 1) ^ 2 *
        (ε + L * r ^ (α : ℝ)) ≤ lam →
      (∀ x i j, |a x i j - A i j| ≤ ε) →
      (∀ i j, HolderWith L α (fun x => a x i j)) →
      ∀ {u : E → ℝ}, ContDiff ℝ 2 u → MemHolder α (iteratedFDeriv ℝ 2 u) →
      MemLp (iteratedFDeriv ℝ 2 u) 2 volume →
      HolderWith K α (fun x => ∑ i, ∑ j, a x i j • fderiv ℝ (fderiv ℝ u) x
        (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) →
      HolderWith (2 * (C * (Lam / lam) ^ (1 + ((n : ℝ) + 1) / 4 + α / 2)) *
        (K / lam + (((n : ℝ) + 1) ^ 2 * L / lam *
          (volume (ball (0 : E) r) ^ (-((2 : ℝ)⁻¹))).toReal +
          r ^ (-(((n : ℝ) + 1) / 2 + α))) *
            (eLpNorm (iteratedFDeriv ℝ 2 u) 2 volume).toReal)).toNNReal
        α (iteratedFDeriv ℝ 2 u) := by
  obtain ⟨C₀, hC₀, hS⟩ :=
    exists_holderOnWith_iteratedFDeriv_two_of_sum_smul_fderiv_fderiv hα hα1 (n := n)
  refine ⟨C₀ + 1, by positivity, fun {A lam Lam} hlam hA hA' {a ε L K r} hr hsmall ha hL
    {u} hu hH hH2 hf => ?_⟩
  let H := iteratedFDeriv ℝ 2 u
  let J : ℝ≥0 := nnHolderNorm α H
  let M : ℝ := (eLpNorm H 2 volume).toReal
  let V : ℝ := (volume (ball (0 : E) r) ^ (-((2 : ℝ)⁻¹))).toReal
  let κ : ℝ := (C₀ + 1) * (Lam / lam) ^ (1 + ((n : ℝ) + 1) / 4 + α / 2)
  have hLam : 0 < Lam := by
    have := (hA (EuclideanSpace.single 0 1)).trans (hA' _)
    have hlamLam : lam ≤ Lam := by simpa using this
    exact hlam.trans_le hlamLam
  have hκ : 0 ≤ κ := by positivity
  have hM : 0 ≤ M := ENNReal.toReal_nonneg
  have hV : 0 ≤ V := ENNReal.toReal_nonneg
  have hJ : HolderWith J α H := hH.holderWith
  have hvol : volume (ball (0 : E) r) ^ (-((2 : ℝ)⁻¹)) ≠ ∞ :=
    ENNReal.rpow_ne_top_of_ne_zero (measure_ball_pos volume 0 hr).ne' measure_ball_lt_top.ne
  -- Interpolation at scale `r` makes the supremum term absorbable too.
  have hsup (x : E) : ‖H x‖ ≤ J * r ^ (α : ℝ) + V * M := by
    have hx := hJ.enorm_le_add_eLpNorm (by norm_num) (by norm_num) hH2 hr x
    have hfin : (J : ℝ≥0∞) * ENNReal.ofReal r ^ (α : ℝ) +
        volume (ball (0 : E) r) ^ (-((2 : ℝ)⁻¹)) * eLpNorm H 2 volume ≠ ∞ := by
      finiteness
    have hx' := (ENNReal.toReal_le_toReal enorm_ne_top hfin).2 hx
    rw [ENNReal.toReal_add (by finiteness) (ENNReal.mul_ne_top hvol hH2.eLpNorm_ne_top),
      ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.coe_toReal, ← ENNReal.toReal_rpow,
      ENNReal.toReal_ofReal hr.le] at hx'
    simpa only [toReal_enorm] using hx'
  let Q : ℝ≥0 := (ε * J + L * (J * r ^ (α : ℝ) + V * M)).toNNReal
  have hQ : (Q : ℝ) = ε * J + L * (J * r ^ (α : ℝ) + V * M) := by
    exact Real.coe_toNNReal _ (by positivity)
  let e : E → ℝ := fun x => ∑ i, ∑ j, (A i j - a x i j) *
    H x ![EuclideanSpace.single i 1, EuclideanSpace.single j 1]
  have he : HolderWith (((n + 1 : ℝ≥0) ^ 2) * Q) α e := by
    have hB : ∀ x, ‖H x‖ ≤ ((J * r ^ (α : ℝ) + V * M).toNNReal : ℝ) := fun x =>
      (hsup x).trans_eq (Real.coe_toNNReal _ (by positivity)).symm
    have herror := holderWith_frozen_hessian_error ha hL hJ hB
    have hconst : ε * J + (J * r ^ (α : ℝ) + V * M).toNNReal * L = Q := by
      apply NNReal.coe_injective
      rw [NNReal.coe_add, NNReal.coe_mul, NNReal.coe_mul,
        Real.coe_toNNReal _ (by positivity), hQ]
      ring
    simpa only [hconst] using herror
  let g : E → ℝ := fun x => ∑ i, ∑ j, A i j • fderiv ℝ (fderiv ℝ u) x
    (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)
  have hg : HolderWith (K + ((n + 1 : ℝ≥0) ^ 2) * Q) α g := by
    convert hf.add he using 1
    funext x
    simp only [Pi.add_apply, e, g, H, iteratedFDeriv_two_apply, smul_eq_mul,
      ← Finset.sum_add_distrib, Matrix.cons_val_zero, Matrix.cons_val_one]
    congr 1
    ext i
    congr 1
    ext j
    ring
  -- Apply the interior frozen estimate to each two-point set, with one common global bound.
  have hglobal : HolderWith (κ * ((K + ((n + 1 : ℝ≥0) ^ 2) * Q) / lam +
      r ^ (-(((n : ℝ) + 1) / 2 + α)) * M)).toNNReal α H := by
    apply holderOnWith_univ.mp
    apply HolderOnWith.of_dist_le
    intro x _ y _
    have hxyBounded : Bornology.IsBounded ({x, y} : Set E) :=
      ((finite_singleton y).insert x).isBounded
    have hxy := hS hlam hA hA' isOpen_univ hu.contDiffOn hxyBounded
      hr (subset_univ _) (hg.holderOnWith _)
    have hb := hxy.dist_le (by simp : x ∈ ({x, y} : Set E)) (by simp : y ∈ ({x, y} : Set E))
    rw [Real.coe_toNNReal _ (by positivity)] at hb ⊢
    refine hb.trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
    have hLp : (eLpNorm H 2 (volume.restrict (thickening r ({x, y} : Set E)))).toReal ≤ M :=
      ENNReal.toReal_mono hH2.eLpNorm_ne_top (eLpNorm_mono_measure H Measure.restrict_le_self)
    calc C₀ * (Lam / lam) ^ (1 + ((n : ℝ) + 1) / 4 + α / 2) *
          ((K + ((n + 1 : ℝ≥0) ^ 2) * Q) / lam +
            r ^ (-(((n : ℝ) + 1) / 2 + α)) *
              (eLpNorm H 2 (volume.restrict (thickening r ({x, y} : Set E)))).toReal)
        ≤ C₀ * (Lam / lam) ^ (1 + ((n : ℝ) + 1) / 4 + α / 2) *
          ((K + ((n + 1 : ℝ≥0) ^ 2) * Q) / lam +
            r ^ (-(((n : ℝ) + 1) / 2 + α)) * M) := by gcongr
      _ ≤ _ := by dsimp [κ]; gcongr; linarith
  have hbound : (J : ℝ) ≤ ((κ * ((K + ((n + 1 : ℝ≥0) ^ 2) * Q) / lam +
      r ^ (-(((n : ℝ) + 1) / 2 + α)) * M)).toNNReal : ℝ) := by
    exact_mod_cast hglobal.nnholderNorm_le
  rw [Real.coe_toNNReal _ (by positivity)] at hbound
  have hbound' : (J : ℝ) ≤ κ * ((K + ((n : ℝ) + 1) ^ 2 *
      (ε * J + L * (J * r ^ (α : ℝ) + V * M))) / lam +
        r ^ (-(((n : ℝ) + 1) / 2 + α)) * M) := by
    simpa only [NNReal.coe_add, NNReal.coe_mul, NNReal.coe_pow, NNReal.coe_natCast,
      NNReal.coe_one, hQ] using hbound
  have hsmall' : κ * ((n : ℝ) + 1) ^ 2 * (ε + L * r ^ (α : ℝ)) / lam ≤ 1 / 2 := by
    apply (div_le_iff₀ hlam).2
    dsimp [κ] at *
    linarith
  have hfinal : (J : ℝ) ≤ 2 * κ * (K / lam +
      (((n : ℝ) + 1) ^ 2 * L / lam * V + r ^ (-(((n : ℝ) + 1) / 2 + α))) * M) := by
    have heq : κ * ((K + ((n : ℝ) + 1) ^ 2 *
        (ε * J + L * (J * r ^ (α : ℝ) + V * M))) / lam +
          r ^ (-(((n : ℝ) + 1) / 2 + α)) * M) =
        κ * (K / lam + (((n : ℝ) + 1) ^ 2 * L / lam * V +
          r ^ (-(((n : ℝ) + 1) / 2 + α))) * M) +
          (κ * ((n : ℝ) + 1) ^ 2 * (ε + L * r ^ (α : ℝ)) / lam) * J := by ring
    rw [heq] at hbound'
    have := mul_le_mul_of_nonneg_right hsmall' J.coe_nonneg
    linarith
  exact hJ.mono (by
    rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ (by positivity)]
    exact hfinal)

end TauCeti.PDE
