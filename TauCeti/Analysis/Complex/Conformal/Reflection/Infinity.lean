/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.PreSchwarzian
public import TauCeti.Analysis.Complex.Conformal.Reflection.Injective
public import TauCeti.Analysis.Complex.UpperHalfPlane.Topology

/-!
# Decay of a reflected pre-Schwarzian at infinity

Suppose that the inverse coordinate `g(w) = f(-1 / w)` of a conformal map extends continuously
and injectively to a straight boundary edge through `w = 0`. Normalize the target edge to the
real axis, with the interior on its upper side. Schwarz reflection extends `g` holomorphically
across zero with nonzero derivative. The pre-Schwarzian chain rule then gives
`z * f''(z) / f'(z) → -2` along the upper half-plane, and in particular `f'' / f' → 0`.

The final theorem transfers this decay to any conjugation-symmetric continuation of the
pre-Schwarzian which is continuous near infinity. It supplies the full-plane limit needed in
the partial-fraction characterization of the Schwarz--Christoffel differential equation.
The straight-edge hypotheses concern the map in the inverse coordinate, rather than assuming
any differentiability of that map on the boundary.  A second form of the decay theorem is stated
for the original map, whose normalized inverse coordinate is the one assumed to extend across
zero.

## References

* L. Ahlfors, *Complex Analysis*, Ch. 6, Section 2.
* T. Driscoll and L. Trefethen, *Schwarz--Christoffel Mapping*, Ch. 2.
-/

public section

open Bornology Complex Filter Set Topology UpperHalfPlane

namespace TauCeti

variable {Ω : Set ℂ} {g : ℂ → ℂ}

/-- At a straight boundary edge in the inverse coordinate, the pre-Schwarzian has the
asymptotic `z * f'' / f' → -2`. The edge is normalized to the real axis. -/
theorem tendsto_mul_logDeriv_deriv_comp_neg_inv_upperHalfPlaneSet
    (hΩopen : IsOpen Ω) (hΩ : MapsTo (starRingEnd ℂ) Ω Ω) (hzero : (0 : ℂ) ∈ Ω)
    (hcont : ContinuousOn g (Ω ∩ {z : ℂ | 0 ≤ z.im}))
    (hholo : DifferentiableOn ℂ g (Ω ∩ upperHalfPlaneSet))
    (hreal : ∀ z ∈ Ω, z.im = 0 → (g z).im = 0)
    (hupper : MapsTo g (Ω ∩ upperHalfPlaneSet) upperHalfPlaneSet)
    (hinj : InjOn g (Ω ∩ {z : ℂ | 0 ≤ z.im})) :
    Tendsto (fun z : ℂ => z * logDeriv (deriv (fun w => g (-w⁻¹))) z)
      (cobounded ℂ ⊓ 𝓟 upperHalfPlaneSet) (𝓝 (-2)) := by
  have hG := differentiableOn_schwarzReflection_of_symmetric hΩopen hΩ hcont hholo hreal
  have hn := deriv_schwarzReflection_ne_zero hΩopen hΩ hcont hholo hreal hupper hinj hzero
  have ht := (tendsto_mul_logDeriv_deriv_comp_neg_inv
    (hG.analyticAt (hΩopen.mem_nhds hzero)) hn).mono_left
      (inf_le_left : cobounded ℂ ⊓ 𝓟 upperHalfPlaneSet ≤ cobounded ℂ)
  apply ht.congr'
  rw [eventuallyEq_inf_principal_iff]
  apply Eventually.of_forall
  intro z hz
  have heq : (fun w : ℂ => schwarzReflection g (-w⁻¹)) =ᶠ[𝓝 z]
      (fun w : ℂ => g (-w⁻¹)) := by
    filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds hz] with w hw
    apply schwarzReflection_of_im_nonneg
    simp only [neg_im, inv_im, neg_div, neg_neg]
    exact div_nonneg hw.le (Complex.normSq_nonneg _)
  rw [(logDeriv_congr_nhds heq.deriv).eq_of_nhds]

/-- A continuation of a polygon map's pre-Schwarzian that is conjugation-symmetric near infinity
tends to zero there when the inverse coordinate maps a neighborhood of zero to a straight edge.
Continuity near infinity holds, in particular, for a continuation holomorphic off finitely many
prevertices. -/
theorem tendsto_zero_cobounded_of_eqOn_logDeriv_deriv_comp_neg_inv
    (hΩopen : IsOpen Ω) (hΩ : MapsTo (starRingEnd ℂ) Ω Ω) (hzero : (0 : ℂ) ∈ Ω)
    (hcont : ContinuousOn g (Ω ∩ {z : ℂ | 0 ≤ z.im}))
    (hholo : DifferentiableOn ℂ g (Ω ∩ upperHalfPlaneSet))
    (hreal : ∀ z ∈ Ω, z.im = 0 → (g z).im = 0)
    (hupper : MapsTo g (Ω ∩ upperHalfPlaneSet) upperHalfPlaneSet)
    (hinj : InjOn g (Ω ∩ {z : ℂ | 0 ≤ z.im}))
    {φ : ℂ → ℂ} (hφcont : ∀ᶠ z in cobounded ℂ, z.im = 0 → ContinuousAt φ z)
    (hφconj : ∀ᶠ z in cobounded ℂ, φ ((starRingEnd ℂ) z) = (starRingEnd ℂ) (φ z))
    (hφ : EqOn φ (logDeriv (deriv (fun w => g (-w⁻¹)))) upperHalfPlaneSet) :
    Tendsto φ (cobounded ℂ) (𝓝 0) := by
  apply tendsto_zero_cobounded_of_tendsto_upperHalfPlaneSet hφcont hφconj
  have ht := (tendsto_mul_logDeriv_deriv_comp_neg_inv_upperHalfPlaneSet
    hΩopen hΩ hzero hcont hholo hreal hupper hinj).mul
      ((tendsto_inv₀_cobounded (α := ℂ)).mono_left
        (inf_le_left : cobounded ℂ ⊓ 𝓟 upperHalfPlaneSet ≤ cobounded ℂ))
  simp only [mul_zero] at ht
  apply ht.congr'
  rw [eventuallyEq_inf_principal_iff]
  apply Eventually.of_forall
  intro z hz
  rw [hφ hz]
  have hz0 : z ≠ 0 := by rintro rfl; simp at hz
  field_simp

/-- **Decay of a continued pre-Schwarzian derivative at infinity.** Read the map `f` of the upper
half-plane in the coordinate `w ↦ -1 / w` at infinity and normalize the target by `w ↦ (w - q) / b`.
If the result extends to a function `g` which is continuous and injective up to a real segment
through `0`, holomorphic and upper half-plane valued above it, and real on it, then every
conjugation-symmetric continuation `φ` of the pre-Schwarzian derivative of `f` which is continuous
near infinity on the real axis tends to `0` at infinity.

This is the form the Schwarz--Christoffel converse uses: `φ` is holomorphic off the finitely many
prevertices, so it is automatically continuous near infinity, and the hypotheses on `g` say that
the point at infinity is an interior point of a side of the polygon. -/
theorem tendsto_zero_cobounded_of_eqOn_logDeriv_deriv {f φ : ℂ → ℂ} {q b : ℂ} {r : ℝ}
    (hr : 0 < r) (hb : b ≠ 0) (hgf : ∀ w : ℂ, w ≠ 0 → g w = (f (-w⁻¹) - q) / b)
    (hcont : ContinuousOn g (Metric.ball 0 r ∩ {z : ℂ | 0 ≤ z.im}))
    (hholo : DifferentiableOn ℂ g (Metric.ball 0 r ∩ upperHalfPlaneSet))
    (hreal : ∀ z ∈ Metric.ball (0 : ℂ) r, z.im = 0 → (g z).im = 0)
    (hupper : MapsTo g (Metric.ball 0 r ∩ upperHalfPlaneSet) upperHalfPlaneSet)
    (hinj : InjOn g (Metric.ball 0 r ∩ {z : ℂ | 0 ≤ z.im}))
    (hφcont : ∀ᶠ z in cobounded ℂ, z.im = 0 → ContinuousAt φ z)
    (hφconj : ∀ z, φ ((starRingEnd ℂ) z) = (starRingEnd ℂ) (φ z))
    (hφf : EqOn φ (logDeriv (deriv f)) upperHalfPlaneSet) :
    Tendsto φ (cobounded ℂ) (𝓝 0) := by
  have hball : MapsTo (starRingEnd ℂ) (Metric.ball (0 : ℂ) r) (Metric.ball 0 r) := fun z hz => by
    rw [Metric.mem_ball, ← map_zero (starRingEnd ℂ), Complex.dist_conj_conj]
    exact hz
  refine tendsto_zero_cobounded_of_eqOn_logDeriv_deriv_comp_neg_inv Metric.isOpen_ball hball
    (Metric.mem_ball_self hr) hcont hholo hreal hupper hinj hφcont
    (Eventually.of_forall hφconj) fun z hz => ?_
  have hz0 : z ≠ 0 := fun h => by simp [h] at hz
  -- Off the origin, the inverse coordinate of the inverse coordinate is the original map.
  have heq : (fun w : ℂ => g (-w⁻¹)) =ᶠ[𝓝 z] fun w : ℂ => (f w - q) / b := by
    filter_upwards [isOpen_compl_singleton.mem_nhds (by simpa using hz0)] with w hw
    have hw0 : w ≠ 0 := hw
    rw [hgf _ (by simpa using hw0), inv_neg, inv_inv, neg_neg]
  have hderiv : (deriv fun w : ℂ => (f w - q) / b) = fun w => deriv f w / b := by
    ext w
    simp only [deriv_div_const, deriv_sub_const]
  rw [hφf hz, (logDeriv_congr_nhds heq.deriv).eq_of_nhds, hderiv]
  simp only [div_eq_mul_inv, logDeriv_mul_const z b⁻¹ (inv_ne_zero hb)]

end TauCeti
