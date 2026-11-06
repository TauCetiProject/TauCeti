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
import TauCeti.Topology.MetricSpace.Holder

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

/-- The upper ellipticity bound of a matrix with a positive lower bound is positive. -/
private theorem pos_of_toQuadraticForm'_bounds {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    {lam Lam : ℝ} (hlam : 0 < lam) (hA : ∀ ξ : E, lam * ‖ξ‖ ^ 2 ≤ A.toQuadraticForm' ξ)
    (hA' : ∀ ξ : E, A.toQuadraticForm' ξ ≤ Lam * ‖ξ‖ ^ 2) : 0 < Lam := by
  have := (hA (EuclideanSpace.single 0 1)).trans (hA' _)
  have hlamLam : lam ≤ Lam := by simpa using this
  exact hlam.trans_le hlamLam

/-- Freezing the coefficients of `∑ aᵢⱼ ∂ᵢ∂ⱼ u` at a constant matrix `A` changes its Hölder
constant by at most `(n+1)² (ε J + L b)`, where `b` bounds the Hessian pointwise. -/
private theorem holderWith_sum_smul_fderiv_fderiv_frozen {α ε L J K : ℝ≥0} {b : ℝ} (hb : 0 ≤ b)
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    {a : E → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {u : E → ℝ}
    (ha : ∀ x i j, |a x i j - A i j| ≤ ε) (hL : ∀ i j, HolderWith L α (fun x => a x i j))
    (hJ : HolderWith J α (iteratedFDeriv ℝ 2 u)) (hB : ∀ x, ‖iteratedFDeriv ℝ 2 u x‖ ≤ b)
    (hf : HolderWith K α (fun x => ∑ i, ∑ j, a x i j • fderiv ℝ (fderiv ℝ u) x
      (EuclideanSpace.single i 1) (EuclideanSpace.single j 1))) :
    HolderWith (K + ((n + 1 : ℝ≥0) ^ 2) * (ε * J + L * b).toNNReal) α
      (fun x => ∑ i, ∑ j, A i j • fderiv ℝ (fderiv ℝ u) x
        (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) := by
  have hB' : ∀ x, ‖iteratedFDeriv ℝ 2 u x‖ ≤ (b.toNNReal : ℝ) := fun x =>
    (hB x).trans_eq (Real.coe_toNNReal _ hb).symm
  have herror := holderWith_frozen_hessian_error ha hL hJ hB'
  have hconst : ε * J + b.toNNReal * L = (ε * J + L * b).toNNReal := by
    apply NNReal.coe_injective
    rw [NNReal.coe_add, NNReal.coe_mul, NNReal.coe_mul, Real.coe_toNNReal _ hb,
      Real.coe_toNNReal _ (by positivity)]
    ring
  rw [hconst] at herror
  convert hf.add herror using 1
  funext x
  simp only [Pi.add_apply, iteratedFDeriv_two_apply, smul_eq_mul, ← Finset.sum_add_distrib,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  congr 1
  ext i
  congr 1
  ext j
  ring

/-- Global form of the frozen-coefficient interior estimate: the Hölder constant of the Hessian
is bounded by the Hölder constant of the frozen operator and the global `L²` norm of the
Hessian, at any scale `r`. -/
private theorem exists_holderWith_iteratedFDeriv_two_of_sum_smul_fderiv_fderiv_of_memLp
    {α : ℝ≥0} (hα : 0 < α) (hα1 : α < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {lam Lam : ℝ},
      0 < lam → (∀ ξ : E, lam * ‖ξ‖ ^ 2 ≤ A.toQuadraticForm' ξ) →
      (∀ ξ : E, A.toQuadraticForm' ξ ≤ Lam * ‖ξ‖ ^ 2) →
      ∀ {K : ℝ≥0} {r : ℝ} {u : E → ℝ}, 0 < r → ContDiff ℝ 2 u →
      MemLp (iteratedFDeriv ℝ 2 u) 2 volume →
      HolderWith K α (fun x => ∑ i, ∑ j, A i j • fderiv ℝ (fderiv ℝ u) x
        (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) →
      HolderWith (C * (Lam / lam) ^ (1 + ((n : ℝ) + 1) / 4 + α / 2) *
        (K / lam + r ^ (-(((n : ℝ) + 1) / 2 + α)) *
          (eLpNorm (iteratedFDeriv ℝ 2 u) 2 volume).toReal)).toNNReal α
        (iteratedFDeriv ℝ 2 u) := by
  obtain ⟨C, hC, hS⟩ :=
    exists_holderOnWith_iteratedFDeriv_two_of_sum_smul_fderiv_fderiv hα hα1 (n := n)
  refine ⟨C, hC, fun {A lam Lam} hlam hA hA' {K r u} hr hu hH2 hg => ?_⟩
  have hLam := pos_of_toQuadraticForm'_bounds hlam hA hA'
  have hM : 0 ≤ (eLpNorm (iteratedFDeriv ℝ 2 u) 2 volume).toReal := ENNReal.toReal_nonneg
  apply holderOnWith_univ.mp
  apply HolderOnWith.of_dist_le
  intro x _ y _
  have hxyBounded : Bornology.IsBounded ({x, y} : Set E) :=
    ((finite_singleton y).insert x).isBounded
  have hxy := hS hlam hA hA' isOpen_univ hu.contDiffOn hxyBounded
    hr (subset_univ _) (hg.holderOnWith _)
  have hb := hxy.dist_le (by simp : x ∈ ({x, y} : Set E)) (by simp : y ∈ ({x, y} : Set E))
  rw [Real.coe_toNNReal _ (by positivity)] at hb
  rw [Real.coe_toNNReal _ (by positivity)]
  have hLp := ENNReal.toReal_mono hH2.eLpNorm_ne_top
    (eLpNorm_mono_measure (iteratedFDeriv ℝ 2 u)
      (Measure.restrict_le_self (s := thickening r {x, y})))
  refine hb.trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
  gcongr

/-- Absorbing the Hölder constant `J` on the right-hand side of the a priori estimate. -/
private theorem le_two_mul_of_le_mul_add_mul {J κ K lam L V M R ε ρ N : ℝ} (hlam : 0 < lam)
    (hJ : 0 ≤ J)
    (hbound : J ≤ κ * ((K + N * (ε * J + L * (J * ρ + V * M))) / lam + R * M))
    (hsmall : 2 * κ * N * (ε + L * ρ) ≤ lam) :
    J ≤ 2 * κ * (K / lam + (N * L / lam * V + R) * M) := by
  have hsmall' : κ * N * (ε + L * ρ) / lam ≤ 1 / 2 := by
    apply (div_le_iff₀ hlam).2
    linarith
  have heq : κ * ((K + N * (ε * J + L * (J * ρ + V * M))) / lam + R * M) =
      κ * (K / lam + (N * L / lam * V + R) * M) + (κ * N * (ε + L * ρ) / lam) * J := by
    field_simp
    ring
  rw [heq] at hbound
  have := mul_le_mul_of_nonneg_right hsmall' hJ
  linarith

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
    exists_holderWith_iteratedFDeriv_two_of_sum_smul_fderiv_fderiv_of_memLp hα hα1 (n := n)
  refine ⟨C₀ + 1, by positivity, fun {A lam Lam} hlam hA hA' {a ε L K r} hr hsmall ha hL
    {u} hu hH hH2 hf => ?_⟩
  let H := iteratedFDeriv ℝ 2 u
  let J : ℝ≥0 := nnHolderNorm α H
  let M : ℝ := (eLpNorm H 2 volume).toReal
  let V : ℝ := (volume (ball (0 : E) r) ^ (-((2 : ℝ)⁻¹))).toReal
  let κ : ℝ := (C₀ + 1) * (Lam / lam) ^ (1 + ((n : ℝ) + 1) / 4 + α / 2)
  have hLam := pos_of_toQuadraticForm'_bounds hlam hA hA'
  have hκ : 0 ≤ κ := by positivity
  have hM : 0 ≤ M := ENNReal.toReal_nonneg
  have hV : 0 ≤ V := ENNReal.toReal_nonneg
  have hJ : HolderWith J α H := hH.holderWith
  -- Interpolation at scale `r` makes the supremum term absorbable too.
  have hsup (x : E) : ‖H x‖ ≤ J * r ^ (α : ℝ) + V * M := by
    simpa using hJ.norm_le_add_toReal_eLpNorm (by norm_num) (by norm_num) hH2 hr x
  have hg := holderWith_sum_smul_fderiv_fderiv_frozen (by positivity) ha hL hJ hsup hf
  have hglobal : HolderWith (κ * ((K + ((n + 1 : ℝ≥0) ^ 2) *
      (ε * J + L * (J * r ^ (α : ℝ) + V * M)).toNNReal) / lam +
        r ^ (-(((n : ℝ) + 1) / 2 + α)) * M)).toNNReal α H := by
    refine (hS hlam hA hA' hr hu hH2 hg).mono (Real.toNNReal_le_toNNReal ?_)
    dsimp [κ]
    gcongr
    linarith
  have hbound := NNReal.coe_le_coe.2 hglobal.nnholderNorm_le
  have hfinal : (J : ℝ) ≤ 2 * κ * (K / lam +
      (((n : ℝ) + 1) ^ 2 * L / lam * V + r ^ (-(((n : ℝ) + 1) / 2 + α))) * M) := by
    refine le_two_mul_of_le_mul_add_mul hlam J.coe_nonneg ?_ hsmall
    rw [Real.coe_toNNReal _ (by positivity)] at hbound
    simpa only [NNReal.coe_add, NNReal.coe_mul, NNReal.coe_pow, NNReal.coe_natCast,
      NNReal.coe_one, Real.coe_toNNReal _ (by positivity : 0 ≤ ε * J + L * (J * r ^ (α : ℝ) +
        V * M))] using hbound
  exact hJ.mono (by
    rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ (by positivity)]
    exact hfinal)

end TauCeti.PDE
