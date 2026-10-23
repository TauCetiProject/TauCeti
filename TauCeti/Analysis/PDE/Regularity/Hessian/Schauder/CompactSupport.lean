/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.Hessian.Schauder.VariableCoefficient

import TauCeti.Analysis.Normed.Module.Ball.Retraction

/-!
# Schauder estimates with compactly supported Hessian

This file derives a variable-coefficient Schauder estimate for functions whose Hessian is
supported in a ball. The coefficients need only be Hölder on that ball: radial retraction replaces
them by globally Hölder coefficients uniformly close to their value at the centre without changing
the equation, because the Hessian vanishes outside the ball.

This compact-support estimate is the form used after multiplying an interior solution by a smooth
cutoff. It removes the global small-oscillation hypothesis from the perturbative estimate, replacing
it by the natural requirement that the support ball and the interpolation scale are small compared
with the Hölder modulus of the coefficients.

## Main declaration

* `TauCeti.PDE.exists_holderWith_iteratedFDeriv_two_of_support_subset_closedBall`: the global
  Hölder estimate for the Hessian of a function whose Hessian is supported in a ball.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Chapter 6, proof of the interior Schauder estimate by freezing coefficients and localization.
-/

public section

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal ENNReal

namespace TauCeti.PDE

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin (n + 1))

/-- **Schauder estimate for a Hessian supported in a ball.** Let `0 < α < 1`. There is
`C > 0`, depending only on dimension and `α`, with the following property. Let `a` be
`α`-Hölder entrywise with constant `L` on the support ball, and suppose `a x₀` has
ellipticity bounds `λ, Λ`,
with `λ > 0`. Put

`Lu = ∑ᵢⱼ aᵢⱼ ∂ᵢⱼu`.

If the Hessian of a global `C²` function `u` is supported in the closed ball of radius `R`
about `x₀` and is globally `α`-Hölder a priori, then the scale condition

`2 κ (n+1)² (L Rᵅ + 2ᵅ L rᵅ) ≤ λ`,

where `κ = C (Λ / λ)^(1 + (n+1)/4 + α/2)`, implies the estimate

`[D²u]ᵅ ≤ 2 κ ([Lu]ᵅ / λ + ((n+1)² 2ᵅ L / λ |Bᵣ|⁻¹/²
  + r^(-(n+1)/2-α)) ‖D²u‖₂)`.

Thus no uniform comparison of `a` with one constant matrix is assumed: the support condition
allows the coefficients to be retracted to the support ball and frozen at its centre. -/
theorem exists_holderWith_iteratedFDeriv_two_of_support_subset_closedBall
    {α : ℝ≥0} (hα : 0 < α) (hα1 : α < 1) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {a : E → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {x₀ : E} {lam Lam : ℝ},
      0 < lam → (∀ ξ : E, lam * ‖ξ‖ ^ 2 ≤ (a x₀).toQuadraticForm' ξ) →
      (∀ ξ : E, (a x₀).toQuadraticForm' ξ ≤ Lam * ‖ξ‖ ^ 2) →
      ∀ {L K : ℝ≥0} {R r : ℝ}, 0 ≤ R → 0 < r →
      2 * (C * (Lam / lam) ^ (1 + ((n : ℝ) + 1) / 4 + α / 2)) * ((n : ℝ) + 1) ^ 2 *
        (L * R ^ (α : ℝ) + (L * 2 ^ (α : ℝ)) * r ^ (α : ℝ)) ≤ lam →
      (∀ i j, HolderOnWith L α (fun x => a x i j) (closedBall x₀ R)) →
      ∀ {u : E → ℝ}, ContDiff ℝ 2 u → MemHolder α (iteratedFDeriv ℝ 2 u) →
      Function.support (iteratedFDeriv ℝ 2 u) ⊆ closedBall x₀ R →
      HolderWith K α (fun x => ∑ i, ∑ j, a x i j • fderiv ℝ (fderiv ℝ u) x
        (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) →
      HolderWith (2 * (C * (Lam / lam) ^ (1 + ((n : ℝ) + 1) / 4 + α / 2)) *
        (K / lam + (((n : ℝ) + 1) ^ 2 * (L * 2 ^ (α : ℝ)) / lam *
          (volume (ball (0 : E) r) ^ (-((2 : ℝ)⁻¹))).toReal +
          r ^ (-(((n : ℝ) + 1) / 2 + α))) *
            (eLpNorm (iteratedFDeriv ℝ 2 u) 2 volume).toReal)).toNNReal
        α (iteratedFDeriv ℝ 2 u) := by
  obtain ⟨C₀, hC₀, hS⟩ :=
    exists_holderWith_iteratedFDeriv_two_of_sum_smul_fderiv_fderiv_of_abs_sub_le
      hα hα1 (n := n)
  refine ⟨C₀, hC₀, fun {a x₀ lam Lam} hlam hEll hEll' {L K R r} hR hr hsmall hL
    {u} hu hH hsupp hf => ?_⟩
  let q : E → E := TauCeti.centeredRadialRetraction x₀ R
  let a' : E → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ := fun x => a (q x)
  have hq_eq {x : E} (hx : x ∈ closedBall x₀ R) : q x = x :=
    TauCeti.centeredRadialRetraction_of_mem_closedBall hx
  have ha'_holder (i j : Fin (n + 1)) :
      HolderWith (L * 2 ^ (α : ℝ)) α (fun x => a' x i j) := by
    simpa only [a', q, Function.comp_def] using (hL i j).comp_centeredRadialRetraction hR
  have ha'_close (x : E) (i j : Fin (n + 1)) :
      |a' x i j - a x₀ i j| ≤ L * R ^ (α : ℝ) := by
    have hmem := TauCeti.centeredRadialRetraction_mem_closedBall (x₀ := x₀) hR x
    have hdist : dist (TauCeti.centeredRadialRetraction x₀ R x) x₀ ≤ R :=
      mem_closedBall.1 hmem
    simpa only [a', q, Real.dist_eq] using
      ((hL i j).dist_le hmem (mem_closedBall_self hR)).trans (by gcongr)
  have hf' : HolderWith K α (fun x => ∑ i, ∑ j, a' x i j •
      fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.single i 1)
        (EuclideanSpace.single j 1)) := by
    convert hf using 1
    funext x
    by_cases hx : x ∈ Function.support (iteratedFDeriv ℝ 2 u)
    · simp only [a', hq_eq (hsupp hx)]
    · have hzero : iteratedFDeriv ℝ 2 u x = 0 := by simpa [Function.mem_support] using hx
      have hentry (i j : Fin (n + 1)) : fderiv ℝ (fderiv ℝ u) x
          (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) = 0 := by
        have hzero' := congrArg (fun H : E [×2]→L[ℝ] ℝ =>
          H ![EuclideanSpace.single i 1, EuclideanSpace.single j 1]) hzero
        simpa only [iteratedFDeriv_two_apply, zero_apply, Matrix.cons_val_zero,
          Matrix.cons_val_one] using hzero'
      simp [hentry]
  have hH2 : MemLp (iteratedFDeriv ℝ 2 u) 2 volume :=
    (hu.continuous_iteratedFDeriv (by norm_num)).memLp_of_hasCompactSupport
      (HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall x₀ R) hsupp)
  let ε : ℝ≥0 := (L * R ^ (α : ℝ)).toNNReal
  have hε : (ε : ℝ) = L * R ^ (α : ℝ) := by
    exact Real.coe_toNNReal _ (mul_nonneg L.coe_nonneg (Real.rpow_nonneg hR _))
  have hsmall' :
      2 * (C₀ * (Lam / lam) ^ (1 + ((n : ℝ) + 1) / 4 + α / 2)) * ((n : ℝ) + 1) ^ 2 *
        ((ε : ℝ) + (L * 2 ^ (α : ℝ) : ℝ≥0) * r ^ (α : ℝ)) ≤ lam := by
    simpa only [hε, NNReal.coe_mul, NNReal.coe_rpow, NNReal.coe_ofNat] using hsmall
  have ha'_close' (x : E) (i j : Fin (n + 1)) : |a' x i j - a x₀ i j| ≤ ε := by
    simpa only [hε] using ha'_close x i j
  exact hS (A := a x₀) (a := a') hlam hEll hEll' (L := L * 2 ^ (α : ℝ))
    (K := K) (ε := ε) hr hsmall' ha'_close' ha'_holder hu hH hH2 hf'

end TauCeti.PDE
