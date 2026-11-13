/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.MvPolynomial.DirectionalOrder
import TauCeti.Algebra.MvPolynomial.Fin.Two

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
  have hH : homogeneousComponent m (taylor a p) ≠ 0 :=
    p.homogeneousComponent_ne_zero_of_orderAt_eq a hm.symm
  obtain ⟨v, hv, hv0, hc⟩ := exists_eval_ne_zero_and_div_notMem hH s
  obtain ⟨ha, horder⟩ := analyticAt_and_analyticOrderAt_eval_add_smul p a v hm hv
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
