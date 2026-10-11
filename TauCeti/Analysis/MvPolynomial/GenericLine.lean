/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPolynomial.DirectionalOrder
public import TauCeti.Analysis.Polynomial.Order

/-!
# Generic lines detecting the order of a plane polynomial

A plane polynomial has a line of slope outside any prescribed finite set on which its
analytic order equals its ambient order at a specified point. The first coordinate of the
direction is fixed to one. This permits comparison with a ramified splitting in that coordinate
without introducing a second power substitution.
-/

public section

open Filter Topology

namespace MvPolynomial

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

/-- A nonzero plane polynomial admits a line of slope outside any finite forbidden set
that detects its ambient order at a specified point. -/
theorem exists_analyticOrderAt_eval_finTwo_eq (p : MvPolynomial (Fin 2) 𝕜)
    (hp : p ≠ 0) (a : Fin 2 → 𝕜) (s : Finset 𝕜) :
    ∃ c ∉ s, analyticOrderAt (fun t : 𝕜 ↦ eval ![a 0 + t, a 1 + c * t] p) 0 = p.orderAt a := by
  classical
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.1 ((orderAt_eq_top_iff (p := p) (a := a)).not.2 hp)
  -- Exclude bad slopes while choosing a direction detecting the first Taylor term.
  let H := homogeneousComponent m (taylor a p)
  have hH : H ≠ 0 := p.homogeneousComponent_ne_zero_of_orderAt_eq a hm.symm
  have hlinear (b : 𝕜) : (X 1 - C b * X 0 : MvPolynomial (Fin 2) 𝕜) ≠ 0 := by
    intro hzero
    have := congrArg (fun q : MvPolynomial (Fin 2) 𝕜 ↦ q.coeff (Finsupp.single 1 1)) hzero
    simp [coeff_X, coeff_C_mul, Finsupp.single_left_inj one_ne_zero] at this
  have hQ : H * X 0 * ∏ b ∈ s, (X 1 - C b * X 0) ≠ 0 :=
    mul_ne_zero (mul_ne_zero hH (X_ne_zero 0))
      (Finset.prod_ne_zero_iff.2 fun b _ ↦ hlinear b)
  obtain ⟨v, hv⟩ : ∃ v, eval v (H * X 0 * ∏ b ∈ s, (X 1 - C b * X 0)) ≠ 0 := by
    by_contra h
    apply hQ
    exact MvPolynomial.funext fun v ↦ by
      simpa only [map_zero] using (not_exists.mp h v |> not_not.mp)
  simp only [map_mul, eval_X, map_prod, map_sub, eval_C, mul_ne_zero_iff,
    Finset.prod_ne_zero_iff] at hv
  have hv0 : v 0 ≠ 0 := hv.1.2
  have hc : v 1 / v 0 ∉ s := by
    intro hmem
    exact hv.2 _ hmem (by rw [div_mul_cancel₀ _ hv0, sub_self])
  let q := aeval (fun i ↦ Polynomial.C (a i) + Polynomial.C (v i) * Polynomial.X) p
  have hqm : q.coeff m ≠ 0 := by
    simpa only [q, coeff_aeval_C_add_C_mul_X, H] using hv.1.1
  have hq : q ≠ 0 := fun hzero ↦ hqm (by simp [hzero])
  have hdegree : q.natTrailingDegree = m := by
    apply le_antisymm (Polynomial.natTrailingDegree_le_of_ne_zero hqm)
    apply Polynomial.le_natTrailingDegree hq
    intro k hk
    simpa [q] using p.coeff_aeval_C_add_C_mul_X_eq_zero a v (by simpa [← hm] using hk)
  have heval := p.eval_aeval_C_add_C_mul_X a v
  have heq : (fun t : 𝕜 ↦ eval (a + t • v) p) = fun t ↦ q.eval t := by
    funext t
    exact (heval t).symm
  have horder : analyticOrderAt (fun t : 𝕜 ↦ eval (a + t • v) p) 0 = m := by
    rw [heq, Polynomial.analyticOrderAt_eval_zero,
      Polynomial.trailingDegree_eq_natTrailingDegree hq, hdegree]
  have ha : AnalyticAt 𝕜 (fun t : 𝕜 ↦ eval (a + t • v) p) 0 := by
    rw [heq]
    exact (AnalyticOnNhd.eval_polynomial q) 0 (Set.mem_univ _)
  -- Rescaling the line parameter fixes its first coordinate to one.
  have hg : AnalyticAt 𝕜 (fun t : 𝕜 ↦ (v 0)⁻¹ * t) 0 :=
    analyticAt_const.mul analyticAt_id
  have hgorder : analyticOrderAt (fun t : 𝕜 ↦ (v 0)⁻¹ * t) 0 = 1 := by
    apply hg.analyticOrderAt_eq_natCast.2
    exact ⟨fun _ ↦ (v 0)⁻¹, analyticAt_const, inv_ne_zero hv0,
      .of_forall fun t ↦ by simp [smul_eq_mul, mul_comm]⟩
  have hscale := AnalyticAt.analyticOrderAt_comp
    (f := fun t : 𝕜 ↦ eval (a + t • v) p) (g := fun t : 𝕜 ↦ (v 0)⁻¹ * t)
    (by simpa only [mul_zero] using ha) hg
  simp only [mul_zero, sub_zero, hgorder, mul_one] at hscale
  have hpoint (t : 𝕜) : a + ((v 0)⁻¹ * t) • v = ![a 0 + t, a 1 + (v 1 / v 0) * t] := by
    ext i
    fin_cases i <;> simp [div_eq_mul_inv, hv0, mul_comm, mul_assoc]
  refine ⟨v 1 / v 0, hc, ?_⟩
  simpa [Function.comp_def, hpoint, horder, hm] using hscale

end MvPolynomial
