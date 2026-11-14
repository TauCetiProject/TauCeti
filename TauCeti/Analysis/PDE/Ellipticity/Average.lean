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

Averaging a uniformly elliptic coefficient field over a set of finite positive measure gives a
constant matrix that is uniformly elliptic with the same constants: the bilinear form of the
averaged matrix is the average of the bilinear forms, and an average lies between two values of the
averaged function. Freezing the coefficients at such averages is the first step of perturbation
arguments for non-divergence-form equations whose coefficients have small mean oscillation.

## Main declarations

* `TauCeti.PDE.UniformlyEllipticOn.setAverage`: averages of uniformly elliptic coefficients are
  uniformly elliptic with the same constants.
-/

public section

open Matrix MeasureTheory
open scoped ENNReal

namespace TauCeti

namespace PDE

/-- **Averages of uniformly elliptic coefficients are uniformly elliptic.** If `a` is uniformly
elliptic with constants `λ, Λ` on a set `s` of finite positive measure, and its entries are
integrable on `s`, then the constant matrix of the averages `⨍_s aᵢⱼ` is uniformly elliptic with
the same constants. -/
theorem UniformlyEllipticOn.setAverage {X Y ι : Type*} [MeasurableSpace X] [Fintype ι]
    [DecidableEq ι] {μ : Measure X} {s : Set X} {a : X → Matrix ι ι ℝ} {lam Lam : ℝ}
    (h : UniformlyEllipticOn s a lam Lam) (hs0 : μ s ≠ 0) (hstop : μ s ≠ ∞)
    (hint : ∀ i j, IntegrableOn (fun x => a x i j) s μ) (Ω : Set Y) :
    UniformlyEllipticOn Ω (fun _ => Matrix.of fun i j => ⨍ x in s, a x i j ∂μ) lam Lam := by
  have hint' : ∀ η ξ : EuclideanSpace ℝ ι,
      IntegrableOn (fun x => η ⬝ᵥ (a x *ᵥ ξ)) s μ := fun η ξ => by
    simp only [dotProduct, mulVec]
    exact integrable_finsetSum _ fun i _ =>
      (integrable_finsetSum _ fun j _ => (hint i j).mul_const _).const_mul _
  -- The bilinear form of the averaged matrix is the average of the bilinear forms.
  have hform : ∀ η ξ : EuclideanSpace ℝ ι,
      η ⬝ᵥ ((Matrix.of fun i j => ⨍ x in s, a x i j ∂μ) *ᵥ ξ) = ⨍ x in s, η ⬝ᵥ (a x *ᵥ ξ) ∂μ := by
    intro η ξ
    simp only [dotProduct, mulVec, of_apply, setAverage_eq, smul_eq_mul]
    rw [integral_finsetSum _ fun i _ =>
      (integrable_finsetSum _ fun j _ => (hint i j).mul_const _).const_mul _, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_const_mul, integral_finsetSum _ fun j _ => (hint i j).mul_const _,
      Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_mul_const]
    ring
  refine uniformlyEllipticOn_iff.2 ⟨h.pos, h.le, fun _ _ => ⟨fun ξ => ?_, fun η ξ => ?_⟩⟩
  · -- Lower bound: some point of `s` lies below the average.
    rw [toQuadraticForm'_apply, hform]
    obtain ⟨x, hx, hle⟩ := exists_le_setAverage hs0 hstop (hint' ξ ξ)
    refine le_trans ?_ hle
    rw [← toQuadraticForm'_apply]
    exact (h.lower_bound hx) ξ
  · -- Upper bound: the average lies between two values of the bilinear form.
    rw [hform, abs_le]
    obtain ⟨x, hx, hle⟩ := exists_le_setAverage hs0 hstop (hint' η ξ)
    obtain ⟨y, hy, hge⟩ := exists_setAverage_le hs0 hstop (hint' η ξ)
    exact ⟨(neg_le_of_abs_le ((h.upper_bound hx) η ξ)).trans hle,
      hge.trans (le_of_abs_le ((h.upper_bound hy) η ξ))⟩

end PDE

end TauCeti
