/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.Hessian.Schauder.Basic
public import Mathlib.Topology.MetricSpace.HolderNorm
import TauCeti.Algebra.Order.Field.Basic
import TauCeti.Analysis.Holder.Lp
import TauCeti.Analysis.InnerProductSpace.Orthonormal.Multilinear
import TauCeti.Analysis.Normed.Operator.Holder
import TauCeti.Analysis.PDE.Ellipticity.Basic
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
Hölder norm of the Hessian. The freezing step
(`TauCeti.PDE.holderOnWith_sum_smul_fderiv_fderiv_of_abs_sub_le`) and the absorption step
(`TauCeti.PDE.holderOnWith_of_forall_holderOnWith_dist_le`) are stated on an arbitrary set, so
that they also serve the estimate up to a flat boundary. The pointwise interpolation estimate is
the arbitrary-scale form of `HolderWith.enorm_le_add_eLpNorm`.

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

/-- The error of freezing a coefficient field that is Hölder on a set has the product Hölder
bound there. -/
private theorem holderOnWith_frozen_hessian_error {α ε L J B : ℝ≥0} {s : Set E}
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    {a : E → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {H : E → E [×2]→L[ℝ] ℝ}
    (ha : ∀ x ∈ s, ∀ i j, |a x i j - A i j| ≤ ε)
    (hL : ∀ i j, HolderOnWith L α (fun x => a x i j) s)
    (hJ : HolderOnWith J α H s) (hB : ∀ x ∈ s, ‖H x‖ ≤ B) :
    HolderOnWith (((n + 1 : ℝ≥0) ^ 2) * (ε * J + B * L)) α
      (fun x => ∑ i, ∑ j, (A i j - a x i j) *
        H x ![EuclideanSpace.single i 1, EuclideanSpace.single j 1]) s := by
  have hterm (i j : Fin (n + 1)) : HolderOnWith (ε * J + B * L) α (fun x => (A i j - a x i j) *
      H x ![EuclideanSpace.single i 1, EuclideanSpace.single j 1]) s := by
    have hc : HolderOnWith L α (fun x => A i j - a x i j) s := fun x hx y hy => by
      simpa only [edist_sub_left] using hL i j x hx y hy
    have hh : HolderOnWith J α (fun x => H x
        ![EuclideanSpace.single i 1, EuclideanSpace.single j 1]) s := by
      simpa using hJ.apply_orthonormalBasis (EuclideanSpace.basisFun _ ℝ) i j
    have hp := (ContinuousLinearMap.mul ℝ ℝ).holderOnWith_comp₂ hc hh
      (Mf := ε) (Mg := B)
      (fun x hx => by simpa [Real.norm_eq_abs, abs_sub_comm] using ha x hx i j)
      (fun x hx => by
        simpa using ((H x).norm_apply_orthonormalBasis_le (EuclideanSpace.basisFun _ ℝ) i j).trans
          (hB x hx))
    simpa only [ContinuousLinearMap.opNNNorm_mul, one_mul,
      ContinuousLinearMap.mul_apply'] using hp
  -- Sum the entries as Hölder functions on the subtype `s`.
  refine HolderWith.restrict_iff.1 ((HolderWith.sum fun i _ => HolderWith.sum fun j _ =>
    (hterm i j).holderWith).mono (le_of_eq (by simp [Finset.card_univ]; ring)))

/-- **Freezing the coefficients on a set.** The frozen operator `∑ᵢⱼ Aᵢⱼ ∂ᵢ∂ⱼu` is `α`-Hölder on a
set `s` when the operator with coefficients `a`, within `ε` of `A` and `L`-Hölder on `s`, is
`K`-Hölder on `s` and the Hessian is `J`-Hölder on `s` and bounded by `B` there, with constant
`K + (n + 1)² (ε J + B L)`. -/
theorem holderOnWith_sum_smul_fderiv_fderiv_of_abs_sub_le {α ε L J K B : ℝ≥0} {s : Set E}
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    {a : E → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {u : E → ℝ}
    (ha : ∀ x ∈ s, ∀ i j, |a x i j - A i j| ≤ ε)
    (hL : ∀ i j, HolderOnWith L α (fun x => a x i j) s)
    (hJ : HolderOnWith J α (iteratedFDeriv ℝ 2 u) s)
    (hB : ∀ x ∈ s, ‖iteratedFDeriv ℝ 2 u x‖ ≤ B)
    (hf : HolderOnWith K α (fun x => ∑ i, ∑ j, a x i j • fderiv ℝ (fderiv ℝ u) x
      (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) s) :
    HolderOnWith (K + ((n + 1 : ℝ≥0) ^ 2) * (ε * J + B * L)) α
      (fun x => ∑ i, ∑ j, A i j • fderiv ℝ (fderiv ℝ u) x
        (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) s := by
  convert hf.add (holderOnWith_frozen_hessian_error ha hL hJ hB) using 1
  funext x
  simp only [Pi.add_apply, iteratedFDeriv_two_apply, smul_eq_mul, ← Finset.sum_add_distrib,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  congr 1
  ext i
  congr 1
  ext j
  ring

/-- **The absorption step of the perturbation argument.** Let `H` be `α`-Hölder on `s`. Suppose
every `α`-Hölder constant `J` of `H` on `s` gives, for all `x, y ∈ s`, the two-point bound

`dist (H x) (H y) ≤ κ ((K + N (ε J + (J ρ + V M) L)) / λ + Q M) dist x y ^ α`,

which freezing the coefficients yields for a Hessian `H` bounded by `J ρ + V M`. If the
smallness condition `2 κ N (ε + L ρ) ≤ λ` holds, then the terms in `J` are absorbed and `H` is
`α`-Hölder on `s` with constant `2 κ (K / λ + (N L / λ V + Q) M)`. -/
theorem holderOnWith_of_forall_holderOnWith_dist_le {X Y : Type*} [MetricSpace X]
    [MetricSpace Y] {α : ℝ≥0} {s : Set X} {H : X → Y} {κ N K ε L ρ V M Q lam : ℝ}
    (hH : ∃ J, HolderOnWith J α H s) (hlam : 0 < lam) (hsmall : 2 * κ * N * (ε + L * ρ) ≤ lam)
    (h : ∀ J : ℝ≥0, HolderOnWith J α H s → ∀ x ∈ s, ∀ y ∈ s, dist (H x) (H y) ≤
      κ * ((K + N * (ε * J + (J * ρ + V * M) * L)) / lam + Q * M) * dist x y ^ (α : ℝ)) :
    HolderOnWith (2 * κ * (K / lam + (N * L / lam * V + Q) * M)).toNNReal α H s := by
  obtain ⟨J₀, hJ₀⟩ := hH
  -- Apply the two-point bound to the best Hölder constant `J` of `H` on `s`.
  let J : ℝ≥0 := nnHolderNorm α (s.domRestrict H)
  have hJ : HolderOnWith J α H s :=
    HolderWith.restrict_iff.1 (hJ₀.holderWith.memHolder.holderWith : HolderWith J α _)
  have hbound := (HolderWith.restrict_iff.2 (HolderOnWith.of_dist_le fun x hx y hy =>
    (h J hJ x hx y hy).trans (mul_le_mul_of_nonneg_right (Real.le_coe_toNNReal _)
      (by positivity)))).nnholderNorm_le
  refine hJ.mono_const ?_
  rw [← NNReal.coe_le_coe, Real.coe_toNNReal'] at hbound ⊢
  rcases le_max_iff.1 hbound with hb | hb
  · have hX : κ * N * (ε + L * ρ) / lam ≤ 1 / 2 := by
      rw [div_le_iff₀ hlam]
      linarith
    refine le_max_of_le_left ((le_two_mul_of_le_add_mul J.coe_nonneg hX
      (Y := κ * (K / lam + (N * L / lam * V + Q) * M)) (hb.trans_eq ?_)).trans_eq (by ring))
    field_simp
    ring
  · exact le_max_of_le_right hb

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
  let M : ℝ := (eLpNorm H 2 volume).toReal
  let V : ℝ := (volume (ball (0 : E) r) ^ (-((2 : ℝ)⁻¹))).toReal
  have hLam : 0 < Lam := hlam.trans_le (le_of_mul_norm_sq_le_toQuadraticForm'_le hA hA')
  -- Absorbing the terms in `J` reduces the estimate to a two-point bound for each constant `J`.
  refine holderOnWith_univ.mp (holderOnWith_of_forall_holderOnWith_dist_le
    ⟨_, hH.holderWith.holderOnWith univ⟩ hlam hsmall fun J hJ x _ y _ => ?_)
  replace hJ : HolderWith J α H := holderOnWith_univ.mp hJ
  -- Interpolation at scale `r` makes the supremum term absorbable too.
  have hsup (x : E) : ‖H x‖ ≤ J * r ^ (α : ℝ) + V * M := by
    simpa [V, M] using hJ.norm_le_add_eLpNorm_toReal (by norm_num) hH2 hr x
  let B : ℝ≥0 := (J * r ^ (α : ℝ) + V * M).toNNReal
  have hBc : (B : ℝ) = J * r ^ (α : ℝ) + V * M := Real.coe_toNNReal _ (by positivity)
  have hg := holderOnWith_univ.mp (holderOnWith_sum_smul_fderiv_fderiv_of_abs_sub_le
    (fun x _ => ha x) (fun i j => (hL i j).holderOnWith univ) (hJ.holderOnWith univ)
    (fun x _ => (hsup x).trans_eq hBc.symm) (hf.holderOnWith univ))
  -- Apply the interior frozen estimate to the two-point set `{x, y}`.
  have hxy := hS hlam hA hA' isOpen_univ hu.contDiffOn ((finite_singleton y).insert x).isBounded
    hr (subset_univ _) (hg.holderOnWith _)
  have hb := hxy.dist_le (by simp : x ∈ ({x, y} : Set E)) (by simp : y ∈ ({x, y} : Set E))
  rw [Real.coe_toNNReal _ (by positivity)] at hb
  refine hb.trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
  have hLp : (eLpNorm H 2 (volume.restrict (thickening r ({x, y} : Set E)))).toReal ≤ M :=
    ENNReal.toReal_mono hH2.eLpNorm_ne_top (eLpNorm_mono_measure H Measure.restrict_le_self)
  push_cast
  rw [hBc]
  gcongr
  linarith

end TauCeti.PDE
