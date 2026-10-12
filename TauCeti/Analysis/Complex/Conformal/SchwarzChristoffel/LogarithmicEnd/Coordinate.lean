/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.LogarithmicEnd.Basic
import TauCeti.Analysis.Complex.Conformal.LocalDegree

/-!
# Exponential coordinates at logarithmic Schwarz--Christoffel ends

At a real prevertex of total exponent `-1`, exponentiating the normalized
Schwarz--Christoffel primitive removes its logarithmic singularity. After a translation
in the target, this exponential extends to a holomorphic coordinate with value `0` and
derivative `1` at the prevertex. The coordinate is injective on a full disc, so the
primitive itself is injective on a sufficiently small upper half-disc.

These coordinates compactify individual parallel-sided ends, without assuming global
univalence or integrability at other prevertices. They provide local single-sheetedness
at the finite parameters representing ends at infinity.

## References

* L. Ahlfors, *Complex Analysis*, Chapter 6, Section 2.
* T. Driscoll and L. Trefethen, *Schwarz--Christoffel Mapping*, Chapter 2.
-/

public section

open Complex Filter Metric Set Topology UpperHalfPlane

namespace TauCeti

variable {ι : Type*} [Fintype ι]

/-- **A normalized exponential coordinate at a logarithmic prevertex.** If the total
exponent at `p` is `-1`, then for some translation `c`, the exponential of `(F - c) / C`
extends across `p` to a holomorphic injection on a disc, with value `0` and derivative `1`
at `p`. Here `F` is the Schwarz--Christoffel primitive and `C` its nonzero prevertex
coefficient. No hypotheses on the other prevertices or global injectivity are needed. -/
theorem exists_analyticOnNhd_injOn_exp_schwarzChristoffelPrimitive_of_sum_eq_neg_one
    (a e : ι → ℝ) (z₀ : UpperHalfPlane) (p : ℝ)
    (he : ∑ i with a i = p, e i = -1) :
    ∃ (c : ℂ) (G : ℂ → ℂ) (r : ℝ), 0 < r ∧
      AnalyticOnNhd ℂ G (ball (p : ℂ) r) ∧ InjOn G (ball (p : ℂ) r) ∧
      G p = 0 ∧ HasDerivAt G 1 (p : ℂ) ∧
      ∀ z ∈ ball (p : ℂ) r ∩ upperHalfPlaneSet,
        G z = exp ((schwarzChristoffelPrimitive a e z₀ z - c) /
          schwarzChristoffelPrevertexCoefficient a e p) := by
  obtain ⟨H, R, hR, hH, hF⟩ :=
    exists_analyticOnNhd_eq_schwarzChristoffelPrimitive_sub_log_of_sum_eq_neg_one
      a e z₀ p he
  let C := schwarzChristoffelPrevertexCoefficient a e p
  let G : ℂ → ℂ := fun z => (z - (p : ℂ)) * exp ((H z - H p) / C)
  have hGan : AnalyticOnNhd ℂ G (ball (p : ℂ) R) := fun z hz =>
    (analyticAt_id.sub analyticAt_const).mul
      (((hH z hz).sub analyticAt_const).div_const (c := C)).cexp
  have hGderiv : HasDerivAt G 1 (p : ℂ) := by
    have hHd := (hH _ (mem_ball_self hR)).differentiableAt.hasDerivAt
    simpa [G] using ((hasDerivAt_id (p : ℂ)).sub_const (p : ℂ)).fun_mul
      ((hHd.sub_const (H p)).div_const C).cexp
  -- The local injectivity criterion supplies a neighbourhood that we restrict to a disc.
  obtain ⟨V, hV, hVinj⟩ :=
    (exists_injOn_nhds_iff_deriv_ne_zero (hGan _ (mem_ball_self hR))).mpr
      (by rw [hGderiv.deriv]; exact one_ne_zero)
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp
    (inter_mem hV (ball_mem_nhds (p : ℂ) hR))
  refine ⟨H p, G, r, hr, hGan.mono (fun z hz => (hball hz).2), ?_, ?_, hGderiv, ?_⟩
  · exact hVinj.mono (fun z hz => (hball hz).1)
  · simp [G]
  · intro z hz
    have hC : C ≠ 0 := schwarzChristoffelPrevertexCoefficient_ne_zero a e p
    have hzp : z - (p : ℂ) ≠ 0 := by
      intro h
      have hzreal := sub_eq_zero.mp h
      simpa [hzreal] using hz.2
    have hformula : (schwarzChristoffelPrimitive a e z₀ z - H p) / C =
        log (z - (p : ℂ)) + (H z - H p) / C := by
      have h := hF z ⟨(hball hz.1).2, hz.2⟩
      dsimp only [C] at hC ⊢
      rw [← h]
      field_simp
      ring
    rw [hformula, exp_add, exp_log hzp]

/-- **Local univalence at a logarithmic Schwarz--Christoffel end.** The primitive is
injective on some upper half-disc about any real point of total exponent `-1`, even if
its other prevertices are nonintegrable or its global image overlaps itself. -/
theorem exists_injOn_schwarzChristoffelPrimitive_halfDisc_of_sum_eq_neg_one
    (a e : ι → ℝ) (z₀ : UpperHalfPlane) (p : ℝ)
    (he : ∑ i with a i = p, e i = -1) :
    ∃ r : ℝ, 0 < r ∧ InjOn (schwarzChristoffelPrimitive a e z₀)
      (ball (p : ℂ) r ∩ upperHalfPlaneSet) := by
  obtain ⟨c, G, r, hr, _, hGinj, _, _, hG⟩ :=
    exists_analyticOnNhd_injOn_exp_schwarzChristoffelPrimitive_of_sum_eq_neg_one a e z₀ p he
  refine ⟨r, hr, fun x hx y hy hxy => hGinj hx.1 hy.1 ?_⟩
  rw [hG x hx, hG y hy, hxy]

end TauCeti
