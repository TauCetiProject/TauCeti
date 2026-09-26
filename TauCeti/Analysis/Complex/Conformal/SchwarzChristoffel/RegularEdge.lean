/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.Boundary
import TauCeti.Analysis.Complex.Conformal.LocalDegree

/-!
# Local continuation across a regular Schwarz--Christoffel edge

At a real point away from the turning prevertices, the Schwarz--Christoffel primitive extends
holomorphically through the edge. Its derivative on the edge is the positive boundary density
times the edge direction, so the extension is locally injective. This gives the local sheet of
the primitive needed to determine the degree of its covering of a simple polygonal domain.

## References

* L. Ahlfors, *Complex Analysis*, Ch. 6, Section 2.
* T. Driscoll and L. Trefethen, *Schwarz--Christoffel Mapping*, Ch. 2.
-/

public section

noncomputable section

open Complex Filter Set Topology UpperHalfPlane

namespace TauCeti

variable {ι : Type*} [Fintype ι]

/-- At a point of a prevertex-free boundary interval, the Schwarz--Christoffel primitive has a
holomorphic continuation which is injective on a neighbourhood of that point. Its value at the
point is the canonical boundary value, and its derivative throughout the neighbourhood is the
continued integrand times the fixed edge direction. -/
theorem exists_injOn_schwarzChristoffelPrimitive_continuation
    (a e : ι → ℝ) (z₀ : UpperHalfPlane) {p q x : ℝ}
    (ha : ∀ i, e i ≠ 0 → a i ∉ Ioo p q) (hx : x ∈ Ioo p q) :
    ∃ U : Set ℂ, IsOpen U ∧ (x : ℂ) ∈ U ∧ ∃ G : ℂ → ℂ,
      EqOn G (schwarzChristoffelPrimitive a e z₀) (U ∩ upperHalfPlaneSet) ∧
      InjOn G U ∧ G x = schwarzChristoffelBoundary a e z₀ x ∧
      ∀ z ∈ U, HasDerivAt G
        (Complex.exp (schwarzChristoffelEdgeAngle a e p * Complex.I) *
          schwarzChristoffelContinuedIntegrand a e p z) z := by
  let c : ℂ := (((p + q) / 2 : ℝ) : ℂ)
  let r : ℝ := (q - p) / 2
  let B : Set ℂ := Metric.ball c r
  let g : ℂ → ℂ := fun z =>
    Complex.exp (schwarzChristoffelEdgeAngle a e p * Complex.I) *
      schwarzChristoffelContinuedIntegrand a e p z
  have hxB : (x : ℂ) ∈ B := by
    simp only [B, Metric.mem_ball]
    rw [Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs, abs_lt]
    constructor <;> dsimp [c, r] <;> norm_num <;> linarith [hx.1, hx.2]
  obtain ⟨G, hGdiff, hGeq⟩ :=
    exists_hasDerivAt_schwarzChristoffelPrimitive_continuation a e z₀ ha
  have hapos : ∀ i, e i ≠ 0 → x ≠ a i := by
    intro i hi hxi
    exact ha i hi (hxi ▸ hx)
  have hgx : g x ≠ 0 := by
    have hlo : ∀ i, e i ≠ 0 → a i ≤ p → a i < x :=
      fun _ _ h => h.trans_lt hx.1
    have hhi : ∀ i, e i ≠ 0 → p < a i → x < a i := by
      intro i hi hip
      have hq : q ≤ a i := le_of_not_gt fun h => ha i hi ⟨hip, h⟩
      exact hx.2.trans_le hq
    simp only [g, schwarzChristoffelContinuedIntegrand_ofReal a e hlo hhi]
    exact mul_ne_zero (Complex.exp_ne_zero _) (by
      exact_mod_cast (schwarzChristoffelDensity_pos a e hapos).ne')
  have hGdiffOn : DifferentiableOn ℂ G B :=
    fun z hz => (hGdiff z hz).differentiableAt.differentiableWithinAt
  have hGan : AnalyticAt ℂ G x :=
    hGdiffOn.analyticAt (Metric.isOpen_ball.mem_nhds hxB)
  have hGderiv : deriv G x ≠ 0 := by
    rw [(hGdiff x hxB).deriv]
    exact hgx
  obtain ⟨W, hW, hWinj⟩ :=
    (exists_injOn_nhds_iff_deriv_ne_zero hGan).mpr hGderiv
  obtain ⟨U, hUW, hUopen, hxU⟩ := mem_nhds_iff.mp (inter_mem hW
    (Metric.isOpen_ball.mem_nhds hxB))
  have hUB : U ⊆ B := fun z hz => (hUW hz).2
  have hUG : EqOn G (schwarzChristoffelPrimitive a e z₀) (U ∩ upperHalfPlaneSet) := by
    intro z hz
    exact hGeq ⟨hUB hz.1, hz.2⟩
  have hGval : G x = schwarzChristoffelBoundary a e z₀ x := by
    symm
    apply schwarzChristoffelBoundary_eq_of_tendsto
    refine Tendsto.congr' ?_ ((hGdiff x hxB).continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds)
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (hUopen.mem_nhds hxU)] with z hz hzU
    exact hUG ⟨hzU, hz⟩
  exact ⟨U, hUopen, hxU, G, hUG, hWinj.mono (fun z hz => (hUW hz).1), hGval,
    fun z hz => hGdiff z (hUB hz)⟩

end TauCeti
