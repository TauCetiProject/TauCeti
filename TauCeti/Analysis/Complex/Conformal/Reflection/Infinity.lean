/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.PreSchwarzian
public import TauCeti.Analysis.Complex.Conformal.Reflection.Injective
public import TauCeti.Analysis.Complex.UpperHalfPlane.Topology
import TauCeti.Analysis.Complex.Conformal.ImageSimplyConnected
import TauCeti.Analysis.Complex.Conformal.Inverse.Function
import TauCeti.Analysis.Complex.Conformal.Reflection.Corner

/-!
# Decay of a reflected pre-Schwarzian at infinity

Suppose that the inverse coordinate `g(w) = f(-1 / w)` of a conformal map extends continuously
and injectively to a straight boundary edge through `w = 0`. Normalize the target edge to the
real axis, with the interior on its upper side. Schwarz reflection extends `g` holomorphically
across zero with nonzero derivative. The pre-Schwarzian chain rule then gives
`z * f''(z) / f'(z) → -2` along the upper half-plane, and in particular `f'' / f' → 0`.

`TauCeti.tendsto_zero_cobounded_of_eqOn_logDeriv_deriv` transfers this decay to any
conjugation-symmetric continuation of the pre-Schwarzian which is continuous near infinity.  It
supplies the full-plane limit needed in the partial-fraction characterization of the
Schwarz--Christoffel differential equation.
The straight-edge hypotheses concern the map in the inverse coordinate, rather than assuming
any differentiability of that map on the boundary.  The asymptotic and the decay theorem are also
stated for the original map, whose normalized inverse coordinate is the one assumed to extend
across zero; in that form the asymptotic is what forces the exponents of a Schwarz--Christoffel
map to sum to `-2`.

The point at infinity may instead be sent to a vertex at infinity of the target: the map tends to
infinity there, and far out its image is a sector of opening `β * π`, `0 < β < 2`, with vertex
some point `c`.  Inverting the target about `c` turns this into a corner at `0` in the inverse
coordinate, and the power coordinate at that corner gives `z * f''(z) / f'(z) → β - 1` instead
(`TauCeti.tendsto_mul_logDeriv_deriv_upperHalfPlaneSet_of_eqOn_div_neg_inv`).  If instead far out
its image is a half-strip between two parallel rays, the exponential of the normalized map has a
straight edge through `0` in the inverse coordinate, and the map is a logarithm of its Schwarz
reflection, which gives `z * f''(z) / f'(z) → -1`
(`TauCeti.tendsto_mul_logDeriv_deriv_upperHalfPlaneSet_of_eqOn_exp_neg_inv`).

More generally, the limit of `z * f''(z) / f'(z)` at infinity does not change when `f` is
replaced by `f ∘ φ` for a map `φ` that fixes infinity and is conformal across it
(`TauCeti.tendsto_mul_logDeriv_deriv_upperHalfPlaneSet_of_eqOn_comp_neg_inv`).  This compares an
end of a domain that has no elementary straightening coordinate with an explicit model map.

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
    exact im_neg_inv_nonneg.mpr hw.le
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
  exact tendsto_zero_cobounded_of_tendsto_mul_upperHalfPlaneSet
    (tendsto_mul_logDeriv_deriv_comp_neg_inv_upperHalfPlaneSet
      hΩopen hΩ hzero hcont hholo hreal hupper hinj) hφcont hφconj hφ

/-- Holomorphy is preserved when a half-plane map is read in the coordinate `w ↦ -1 / w`
and affinely normalized. -/
theorem differentiableOn_of_eqOn_neg_inv {f g : ℂ → ℂ} {q b : ℂ} {r : ℝ}
    (hf : DifferentiableOn ℂ f upperHalfPlaneSet)
    (hgf : EqOn g (fun w => (f (-w⁻¹) - q) / b) (Metric.ball 0 r ∩ upperHalfPlaneSet)) :
    DifferentiableOn ℂ g (Metric.ball 0 r ∩ upperHalfPlaneSet) := by
  refine DifferentiableOn.congr ?_ fun w hw => hgf hw
  intro w hw
  have hw0 : w ≠ 0 := fun h => by simp [h] at hw
  have hnegInv : -w⁻¹ ∈ upperHalfPlaneSet := im_neg_inv_pos.mpr hw.2
  exact (((hf (-w⁻¹) hnegInv).differentiableAt
    (isOpen_upperHalfPlaneSet.mem_nhds hnegInv)).comp w
      (differentiableAt_inv hw0).neg).sub_const q |>.div_const b |>.differentiableWithinAt

/-- **The pre-Schwarzian of a map with a straight side at infinity.** Read the map `f` of the
upper half-plane in the coordinate `w ↦ -1 / w` at infinity and normalize the target by
`w ↦ (w - q) / b`. If the result extends to a function `g` which is continuous and injective up to
a real segment through `0`, holomorphic and upper half-plane valued above it, and real on it, then
`z * f''(z) / f'(z) → -2` as `z` tends to infinity in the upper half-plane. -/
theorem tendsto_mul_logDeriv_deriv_upperHalfPlaneSet_of_eqOn_neg_inv
    {f : ℂ → ℂ} {q b : ℂ} {r : ℝ}
    (hr : 0 < r) (hb : b ≠ 0)
    (hgf : EqOn g (fun w => (f (-w⁻¹) - q) / b)
      (Metric.ball 0 r ∩ upperHalfPlaneSet))
    (hcont : ContinuousOn g (Metric.ball 0 r ∩ {z : ℂ | 0 ≤ z.im}))
    (hholo : DifferentiableOn ℂ g (Metric.ball 0 r ∩ upperHalfPlaneSet))
    (hreal : ∀ z ∈ Metric.ball (0 : ℂ) r, z.im = 0 → (g z).im = 0)
    (hupper : MapsTo g (Metric.ball 0 r ∩ upperHalfPlaneSet) upperHalfPlaneSet)
    (hinj : InjOn g (Metric.ball 0 r ∩ {z : ℂ | 0 ≤ z.im})) :
    Tendsto (fun z : ℂ => z * logDeriv (deriv f) z)
      (cobounded ℂ ⊓ 𝓟 upperHalfPlaneSet) (𝓝 (-2)) := by
  have hball : MapsTo (starRingEnd ℂ) (Metric.ball (0 : ℂ) r) (Metric.ball 0 r) := fun z hz => by
    rw [Metric.mem_ball, ← map_zero (starRingEnd ℂ), Complex.dist_conj_conj]
    exact hz
  apply (tendsto_mul_logDeriv_deriv_comp_neg_inv_upperHalfPlaneSet Metric.isOpen_ball
    hball (Metric.mem_ball_self hr) hcont hholo hreal hupper hinj).congr'
  rw [eventuallyEq_inf_principal_iff]
  have hinv : Tendsto (fun z : ℂ => -z⁻¹) (cobounded ℂ) (nhds 0) := by
    simpa only [neg_zero] using (tendsto_inv₀_cobounded (α := ℂ)).neg
  filter_upwards [hinv.eventually (Metric.ball_mem_nhds (0 : ℂ) hr)] with z hzball hz
  have hz0 : z ≠ 0 := fun h => by simp [h] at hz
  have hnegInv : -z⁻¹ ∈ upperHalfPlaneSet := im_neg_inv_pos.mpr hz
  -- Off the origin, the inverse coordinate of the inverse coordinate is the original map.
  have heq : (fun w : ℂ => g (-w⁻¹)) =ᶠ[𝓝 z] fun w : ℂ => (f w - q) / b := by
    filter_upwards [((continuousAt_inv₀ hz0).neg).preimage_mem_nhds
      ((Metric.isOpen_ball.inter isOpen_upperHalfPlaneSet).mem_nhds
        ⟨hzball, hnegInv⟩)] with w hw
    calc
      g (-w⁻¹) = (f (-(-w⁻¹)⁻¹) - q) / b := hgf hw
      _ = (f w - q) / b := by rw [inv_neg, inv_inv, neg_neg]
  have hderiv : (deriv fun w : ℂ => (f w - q) / b) = fun w => deriv f w / b := by
    ext w
    simp only [deriv_div_const, deriv_sub_const]
  rw [(logDeriv_congr_nhds heq.deriv).eq_of_nhds, hderiv]
  simp only [div_eq_mul_inv, logDeriv_mul_const z b⁻¹ (inv_ne_zero hb)]

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
    (hr : 0 < r) (hb : b ≠ 0)
    (hgf : EqOn g (fun w => (f (-w⁻¹) - q) / b)
      (Metric.ball 0 r ∩ upperHalfPlaneSet))
    (hcont : ContinuousOn g (Metric.ball 0 r ∩ {z : ℂ | 0 ≤ z.im}))
    (hholo : DifferentiableOn ℂ g (Metric.ball 0 r ∩ upperHalfPlaneSet))
    (hreal : ∀ z ∈ Metric.ball (0 : ℂ) r, z.im = 0 → (g z).im = 0)
    (hupper : MapsTo g (Metric.ball 0 r ∩ upperHalfPlaneSet) upperHalfPlaneSet)
    (hinj : InjOn g (Metric.ball 0 r ∩ {z : ℂ | 0 ≤ z.im}))
    (hφcont : ∀ᶠ z in cobounded ℂ, z.im = 0 → ContinuousAt φ z)
    (hφconj : Filter.Eventually
      (fun z => φ ((starRingEnd ℂ) z) = (starRingEnd ℂ) (φ z)) (cobounded ℂ))
    (hφf : EqOn φ (logDeriv (deriv f)) upperHalfPlaneSet) :
    Tendsto φ (cobounded ℂ) (𝓝 0) := by
  exact tendsto_zero_cobounded_of_tendsto_mul_upperHalfPlaneSet
    (tendsto_mul_logDeriv_deriv_upperHalfPlaneSet_of_eqOn_neg_inv
      hr hb hgf hcont hholo hreal hupper hinj) hφcont hφconj hφf

/-- **The pre-Schwarzian of a map with a vertex at infinity.**  Read the map `f` of the upper
half-plane in the coordinate `w ↦ -1 / w` at infinity and invert the target about `c` by
`w ↦ b / (w - c)`.  Suppose the result extends to a function `g` with `g 0 = 0` which is continuous
and injective up to a real segment through `0`, takes the upper part of that neighbourhood into the
sector `|arg w| < β * π / 2` of opening `β * π`, where `0 < β < 2`, and takes the other real points
to the two bounding rays of that sector.  Then `z * f''(z) / f'(z) → β - 1` as `z` tends to
infinity in the upper half-plane.

In terms of `f`, the hypotheses say that `f` tends to infinity at infinity and that far out it
fills the sector of opening `β * π` with vertex `c`, with the far parts of the real axis carried to
the two bounding rays.  For a Schwarz--Christoffel map the limit is the sum of the turning
exponents, so the finite vertices then
turn through `(β - 1) * π` in total. -/
theorem tendsto_mul_logDeriv_deriv_upperHalfPlaneSet_of_eqOn_div_neg_inv
    {f : ℂ → ℂ} {c b : ℂ} {r β : ℝ} (hr : 0 < r) (hb : b ≠ 0) (hβ : β ∈ Ioo (0 : ℝ) 2)
    (hf : DifferentiableOn ℂ f upperHalfPlaneSet)
    (hfn : ∀ z ∈ upperHalfPlaneSet, deriv f z ≠ 0)
    (hgf : EqOn g (fun w => b / (f (-w⁻¹) - c)) (Metric.ball 0 r ∩ upperHalfPlaneSet))
    (hg0 : g 0 = 0)
    (hcont : ContinuousOn g (Metric.ball 0 r ∩ {z : ℂ | 0 ≤ z.im}))
    (hinj : InjOn g (Metric.ball 0 r ∩ {z : ℂ | 0 ≤ z.im}))
    (hsector : ∀ z ∈ Metric.ball (0 : ℂ) r, 0 < z.im → |(g z).arg| < β * Real.pi / 2)
    (hrays : ∀ z ∈ Metric.ball (0 : ℂ) r, z.im = 0 → g z ≠ 0 →
      |(g z).arg| = β * Real.pi / 2) :
    Tendsto (fun z : ℂ => z * logDeriv (deriv f) z)
      (cobounded ℂ ⊓ 𝓟 upperHalfPlaneSet) (𝓝 ((β : ℂ) - 1)) := by
  set s := Metric.ball (0 : ℂ) r ∩ upperHalfPlaneSet with hs_def
  have hs : IsOpen s := Metric.isOpen_ball.inter isOpen_upperHalfPlaneSet
  have hball : MapsTo (starRingEnd ℂ) (Metric.ball (0 : ℂ) r) (Metric.ball 0 r) := fun z hz => by
    rw [Metric.mem_ball, ← map_zero (starRingEnd ℂ), Complex.dist_conj_conj]
    exact hz
  have hsH : ∀ w ∈ s, w ∈ Metric.ball (0 : ℂ) r ∩ {z : ℂ | 0 ≤ z.im} :=
    fun w hw => ⟨hw.1, ofPred_subset_ofPred.mpr (fun _ => le_of_lt) hw.2⟩
  -- Above the axis `g` omits its value `0` at the origin, so `f` omits `c` near infinity.
  have hden : ∀ w ∈ s, f (-w⁻¹) - c ≠ 0 := fun w hw h0 => by
    have hw0 := hinj (hsH w hw) ⟨Metric.mem_ball_self hr, by simp⟩
      ((hgf hw).trans (by simp [h0, hg0]))
    have him : 0 < w.im := hw.2
    simp [hw0] at him
  have hholo : DifferentiableOn ℂ g (Metric.ball 0 r ∩ {z : ℂ | 0 < z.im}) := by
    have hF : DifferentiableOn ℂ (fun w => f (-w⁻¹) - c) s :=
      differentiableOn_of_eqOn_neg_inv (q := c) (b := 1) hf fun w _ => by simp
    exact ((differentiableOn_const b).div hF hden).congr fun w hw => hgf hw
  -- The power coordinate at the corner `0` of `g`: `g = h ^ β` with `h` having a simple zero.
  obtain ⟨h, hh, -, hh0, hdh, hpow, hre, -, -⟩ :=
    exists_differentiableOn_injOn_cpow_eq_of_sector (f := g) (x := 0) hβ Metric.isOpen_ball hball
      (by simpa using Metric.mem_ball_self (x := (0 : ℂ)) hr) (by simpa using hg0) hcont hholo hinj
      hsector hrays
  rw [ofReal_zero] at hh0 hdh
  -- So the normalized map `(f (-1 / w) - c) / b = g⁻¹` is the corner power `h ^ (-β)`.
  have hpowF : EqOn (fun w => (f (-w⁻¹) - c) / b) (fun w => 0 + h w ^ (-(β : ℂ))) s := by
    intro w hw
    have hgw : h w ^ (β : ℂ) = g w := hpow (hsH w hw)
    simp only [zero_add, cpow_neg]
    rw [hgw, hgf hw, inv_div]
  have hne : (𝓝[s] (0 : ℂ)).NeBot := by
    rw [hs_def, nhdsWithin_inter_of_mem (mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds 0 hr))]
    simpa using Real.nhdsWithin_upperHalfPlaneSet_neBot 0
  have hcorner := tendsto_sub_mul_logDeriv_deriv_of_eqOn_add_cpow Metric.isOpen_ball
    (Metric.mem_ball_self hr) hh hh0 hdh hs hne inter_subset_left
    (fun w hw => mem_slitPlane_iff.mpr (Or.inl (hre w hw.1 hw.2)))
    (neg_ne_zero.mpr (ofReal_ne_zero.mpr hβ.1.ne')) hpowF
  -- Pass back to the original coordinate by the pre-Schwarzian chain rule.
  have hlim := tendsto_mul_logDeriv_deriv_of_tendsto_mul_logDeriv_deriv_neg_inv hr hb hf hfn
    (by simpa only [sub_zero] using hcorner)
  rwa [show -(-(β : ℂ) - 1) - 2 = (β : ℂ) - 1 by ring] at hlim

/-- **The pre-Schwarzian of a map with a parallel-sided end at infinity.**  Read the map `f` of
the upper half-plane in the coordinate `w ↦ -1 / w` at infinity, normalize the target by
`w ↦ (w - c) / b`, and exponentiate.  If the result extends to a function `g` with `g 0 = 0`
which is continuous and injective up to a real segment through `0`, upper half-plane valued
above it, and real on it, then `z * f''(z) / f'(z) → -1` as `z` tends to infinity in the upper
half-plane.

The hypotheses are local at `w = 0`, that is near infinity in the source: they constrain `f` only
through `g` on the upper half of the ball of radius `r`, and say nothing about the rest of the
image of `f`.  The typical source of such a `g` is a map `f` which far out fills a half-strip
between two parallel rays, with the far parts of the real axis carried to those rays, where `c`
and `b` are chosen so that `w ↦ (w - c) / b` carries that half-strip to
`{w | w.re < 0 ∧ 0 < w.im ∧ w.im < π}`, which the exponential maps onto the upper half of the unit
disc; the polygonal-domain theorems derive the hypotheses on `g` from such geometry.  This is
the opening `β = 0` counterpart of
`TauCeti.tendsto_mul_logDeriv_deriv_upperHalfPlaneSet_of_eqOn_div_neg_inv`. -/
theorem tendsto_mul_logDeriv_deriv_upperHalfPlaneSet_of_eqOn_exp_neg_inv
    {f : ℂ → ℂ} {c b : ℂ} {r : ℝ} (hr : 0 < r) (hb : b ≠ 0)
    (hf : DifferentiableOn ℂ f upperHalfPlaneSet)
    (hfn : ∀ z ∈ upperHalfPlaneSet, deriv f z ≠ 0)
    (hgf : EqOn g (fun w => exp ((f (-w⁻¹) - c) / b)) (Metric.ball 0 r ∩ upperHalfPlaneSet))
    (hg0 : g 0 = 0)
    (hcont : ContinuousOn g (Metric.ball 0 r ∩ {z : ℂ | 0 ≤ z.im}))
    (hreal : ∀ z ∈ Metric.ball (0 : ℂ) r, z.im = 0 → (g z).im = 0)
    (hupper : MapsTo g (Metric.ball 0 r ∩ upperHalfPlaneSet) upperHalfPlaneSet)
    (hinj : InjOn g (Metric.ball 0 r ∩ {z : ℂ | 0 ≤ z.im})) :
    Tendsto (fun z : ℂ => z * logDeriv (deriv f) z)
      (cobounded ℂ ⊓ 𝓟 upperHalfPlaneSet) (𝓝 (-1)) := by
  have hs : IsOpen (Metric.ball (0 : ℂ) r ∩ upperHalfPlaneSet) :=
    Metric.isOpen_ball.inter isOpen_upperHalfPlaneSet
  have hball : MapsTo (starRingEnd ℂ) (Metric.ball (0 : ℂ) r) (Metric.ball 0 r) := fun z hz => by
    rw [Metric.mem_ball, ← map_zero (starRingEnd ℂ), Complex.dist_conj_conj]
    exact hz
  have hF : DifferentiableOn ℂ (fun w => (f (-w⁻¹) - c) / b)
      (Metric.ball 0 r ∩ upperHalfPlaneSet) :=
    differentiableOn_of_eqOn_neg_inv hf fun _ _ => rfl
  have hholo : DifferentiableOn ℂ g (Metric.ball 0 r ∩ upperHalfPlaneSet) :=
    hF.cexp.congr fun w hw => hgf hw
  -- Schwarz reflection continues `g` across the axis with a simple zero at `0`.
  have hzero : (0 : ℂ) ∈ Metric.ball 0 r := Metric.mem_ball_self hr
  have hG := differentiableOn_schwarzReflection_of_symmetric Metric.isOpen_ball hball hcont
    hholo hreal
  have hG0 : schwarzReflection g 0 = 0 := by
    rw [schwarzReflection_of_im_nonneg (by simp), hg0]
  have hdG := deriv_schwarzReflection_ne_zero Metric.isOpen_ball hball hcont hholo hreal hupper
    hinj hzero
  -- So `(f (-1 / w) - c) / b` is a logarithm of a function with a simple zero at `0`.
  have hexp : EqOn (fun w => exp ((f (-w⁻¹) - c) / b)) (schwarzReflection g)
      (Metric.ball 0 r ∩ upperHalfPlaneSet) := fun w hw => by
    rw [schwarzReflection_of_im_nonneg (le_of_lt hw.2), hgf hw]
  have hlog := tendsto_sub_mul_logDeriv_deriv_of_eqOn_exp
    (hG.analyticAt (Metric.isOpen_ball.mem_nhds hzero)) hG0 hdG hs hF hexp
  have hlim := tendsto_mul_logDeriv_deriv_of_tendsto_mul_logDeriv_deriv_neg_inv hr hb hf hfn
    (by simpa only [sub_zero] using hlog)
  rwa [show -(-1 : ℂ) - 2 = -1 by ring] at hlim

/-- **The pre-Schwarzian chain rule at infinity for a composite.**  If `f (-1 / w) = q (-1 / H w)`
on an open set `T` on which `H` is holomorphic with nonvanishing derivative and takes values in
the upper half-plane, where `q` is holomorphic with nonvanishing derivative, then on `T`
the residue term `w * F''(w) / F'(w)` of `F w = f (-1 / w)` is computed from that of `q` at
`ζ = -1 / H w` and from `H`. -/
private theorem mul_logDeriv_deriv_comp_neg_inv_eq_of_eqOn {f q H : ℂ → ℂ} {T : Set ℂ}
    (hq : DifferentiableOn ℂ q upperHalfPlaneSet) (hqn : ∀ z ∈ upperHalfPlaneSet, deriv q z ≠ 0)
    (hT : IsOpen T) (hHd : DifferentiableOn ℂ H T) (hdH : ∀ w ∈ T, deriv H w ≠ 0)
    (hHT : ∀ w ∈ T, H w ∈ upperHalfPlaneSet)
    (hFq : EqOn (fun w => f (-w⁻¹)) (fun w => q (-(H w)⁻¹)) T) {w : ℂ} (hw : w ∈ T) :
    w * logDeriv (deriv fun w => f (-w⁻¹)) w =
      (-((-(H w)⁻¹) * logDeriv (deriv q) (-(H w)⁻¹)) - 2) * (w * logDeriv H w) +
        w * logDeriv (deriv H) w := by
  have hsim : 0 < (H w).im := hHT w hw
  have hs0 : H w ≠ 0 := fun h => by simp [h] at hsim
  have hζ : -(H w)⁻¹ ∈ upperHalfPlaneSet := im_neg_inv_pos.mpr hsim
  have hqζ : AnalyticAt ℂ q (-(H w)⁻¹) := hq.analyticAt (isOpen_upperHalfPlaneSet.mem_nhds hζ)
  -- `Q s = q (-1 / s)` is holomorphic near `H w`, with nonvanishing derivative.
  set Q : ℂ → ℂ := fun s => q (-s⁻¹)
  have hQd : HasDerivAt Q (deriv q (-(H w)⁻¹) * ((H w) ^ 2)⁻¹) (H w) := by
    have hinv : HasDerivAt (fun s : ℂ => -s⁻¹) ((H w) ^ 2)⁻¹ (H w) :=
      (hasDerivAt_inv hs0).neg.congr_deriv (neg_neg _)
    exact hqζ.differentiableAt.hasDerivAt.comp (H w) hinv
  have hQw : AnalyticAt ℂ Q (H w) := by
    refine DifferentiableOn.analyticAt (s := upperHalfPlaneSet) (fun s hs => ?_)
      (isOpen_upperHalfPlaneSet.mem_nhds hsim)
    have hs0' : s ≠ 0 := fun h => by simp [h] at hs
    exact ((hq.differentiableAt (isOpen_upperHalfPlaneSet.mem_nhds (im_neg_inv_pos.mpr hs))).comp
      s (differentiableAt_inv hs0').neg).differentiableWithinAt
  have hdQ : deriv Q (H w) ≠ 0 := by
    rw [hQd.deriv]
    exact mul_ne_zero (hqn _ hζ) (inv_ne_zero (pow_ne_zero 2 hs0))
  -- Chain rule for `F = Q ∘ H`, then the `-1 / s` chain rule for `Q`.
  have heq : deriv (fun w => f (-w⁻¹)) =ᶠ[𝓝 w] deriv (Q ∘ H) :=
    (hFq.eventuallyEq_of_mem (hT.mem_nhds hw)).deriv
  rw [(logDeriv_congr_nhds heq).eq_of_nhds,
    logDeriv_deriv_comp hQw (hHd.analyticAt (hT.mem_nhds hw)) hdQ (hdH w hw),
    logDeriv_deriv_comp_neg_inv hqζ (hqn _ hζ) hs0, logDeriv_apply H w]
  field_simp

/-- **A local inverse of a map conformal across the real axis.**  If `g` is continuous and
injective up to a real segment through `0`, holomorphic and upper half-plane valued above it, real
on it, and `g 0 = 0`, then on an open neighbourhood `V` of `0` there is an injective holomorphic
map `H` with `H 0 = 0` which, above the axis, takes values above the axis and inverts `g`.  It is
the inverse of the Schwarz reflection of `g`. -/
private theorem exists_differentiableOn_injOn_inverse_of_reflection {r : ℝ} (hr : 0 < r)
    (hg0 : g 0 = 0) (hcont : ContinuousOn g (Metric.ball 0 r ∩ {z : ℂ | 0 ≤ z.im}))
    (hholo : DifferentiableOn ℂ g (Metric.ball 0 r ∩ upperHalfPlaneSet))
    (hreal : ∀ z ∈ Metric.ball (0 : ℂ) r, z.im = 0 → (g z).im = 0)
    (hupper : MapsTo g (Metric.ball 0 r ∩ upperHalfPlaneSet) upperHalfPlaneSet)
    (hinj : InjOn g (Metric.ball 0 r ∩ {z : ℂ | 0 ≤ z.im})) :
    ∃ V H : _, IsOpen V ∧ (0 : ℂ) ∈ V ∧ DifferentiableOn ℂ H V ∧ InjOn H V ∧ H 0 = 0 ∧
      ∀ w ∈ V, 0 < w.im → H w ∈ Metric.ball 0 r ∩ upperHalfPlaneSet ∧ g (H w) = w := by
  set Ω := Metric.ball (0 : ℂ) r with hΩ_def
  have hΩ : MapsTo (starRingEnd ℂ) Ω Ω := fun z hz => by
    rw [hΩ_def, Metric.mem_ball, ← map_zero (starRingEnd ℂ), Complex.dist_conj_conj]
    exact hz
  have h0Ω : (0 : ℂ) ∈ Ω := Metric.mem_ball_self hr
  -- Schwarz reflection continues `g` to a conformal map of the ball, which has a holomorphic
  -- inverse on its open image.
  have hGd : DifferentiableOn ℂ (schwarzReflection g) Ω :=
    differentiableOn_schwarzReflection_of_symmetric Metric.isOpen_ball hΩ hcont hholo hreal
  have hGi : InjOn (schwarzReflection g) Ω :=
    injOn_schwarzReflection_of_symmetric hΩ hupper (fun w hw h => (hreal w hw h).ge) hinj
  have hG0 : schwarzReflection g 0 = 0 := by rw [schwarzReflection_of_im_nonneg (by simp), hg0]
  set H := Function.invFunOn (schwarzReflection g) Ω
  have hHmem : ∀ w ∈ schwarzReflection g '' Ω, H w ∈ Ω := fun w hw => Function.invFunOn_mem hw
  have hGH : ∀ w ∈ schwarzReflection g '' Ω, schwarzReflection g (H w) = w :=
    fun w hw => Function.invFunOn_eq hw
  refine ⟨schwarzReflection g '' Ω, H,
    isOpen_image_of_differentiableOn_of_injOn Metric.isOpen_ball hGd hGi, ⟨0, h0Ω, hG0⟩,
    hGd.invFunOn Metric.isOpen_ball hGi, fun w₁ hw₁ w₂ hw₂ h => ?_, ?_, fun w hw hwim => ?_⟩
  · rw [← hGH w₁ hw₁, ← hGH w₂ hw₂, h]
  · have h := hGi.leftInvOn_invFunOn h0Ω
    rwa [hG0] at h
  -- Above the axis the inverse stays above the axis, where the reflection is `g`.
  have hHupper : 0 < (H w).im := by
    by_contra hle
    rcases (not_lt.mp hle).lt_or_eq with hlt | heq
    · have h := mapsTo_schwarzReflection_im_neg hΩ hupper ⟨hHmem w hw, hlt⟩
      rw [mem_ofPred_eq, hGH w hw] at h
      linarith
    · have h := hreal (H w) (hHmem w hw) heq
      rw [← schwarzReflection_of_im_nonneg (f := g) heq.ge, hGH w hw] at h
      linarith
  exact ⟨⟨hHmem w hw, hHupper⟩, by
    rw [← schwarzReflection_of_im_nonneg (f := g) hHupper.le, hGH w hw]⟩

/-- **The pre-Schwarzian asymptotic at infinity is invariant under maps conformal across
infinity.**  Let `q` be holomorphic with nonvanishing derivative on the upper half-plane, with
`ζ * q''(ζ) / q'(ζ) → L` as `ζ` tends to infinity there.  Suppose that `f ∘ φ = q` near infinity,
where `φ` fixes infinity and is conformal across it: in the coordinate `w ↦ -1 / w`, the map
`φ` reads as a function `g` with `g 0 = 0` which is continuous and injective up to a real
segment through `0`, holomorphic and upper half-plane valued above it, and real on it.  Then
also `z * f''(z) / f'(z) → L` as `z` tends to infinity in the upper half-plane.

This compares a far end of a domain with an explicit model map `q` whose asymptotic is computed
directly. -/
theorem tendsto_mul_logDeriv_deriv_upperHalfPlaneSet_of_eqOn_comp_neg_inv
    {f q : ℂ → ℂ} {r : ℝ} {L : ℂ} (hr : 0 < r)
    (hf : DifferentiableOn ℂ f upperHalfPlaneSet)
    (hfn : ∀ z ∈ upperHalfPlaneSet, deriv f z ≠ 0)
    (hq : DifferentiableOn ℂ q upperHalfPlaneSet)
    (hqn : ∀ z ∈ upperHalfPlaneSet, deriv q z ≠ 0)
    (hqL : Tendsto (fun z : ℂ => z * logDeriv (deriv q) z)
      (cobounded ℂ ⊓ 𝓟 upperHalfPlaneSet) (𝓝 L))
    (hgq : EqOn (fun w => f (-(g w)⁻¹)) (fun w => q (-w⁻¹))
      (Metric.ball 0 r ∩ upperHalfPlaneSet))
    (hg0 : g 0 = 0)
    (hcont : ContinuousOn g (Metric.ball 0 r ∩ {z : ℂ | 0 ≤ z.im}))
    (hholo : DifferentiableOn ℂ g (Metric.ball 0 r ∩ upperHalfPlaneSet))
    (hreal : ∀ z ∈ Metric.ball (0 : ℂ) r, z.im = 0 → (g z).im = 0)
    (hupper : MapsTo g (Metric.ball 0 r ∩ upperHalfPlaneSet) upperHalfPlaneSet)
    (hinj : InjOn g (Metric.ball 0 r ∩ {z : ℂ | 0 ≤ z.im})) :
    Tendsto (fun z : ℂ => z * logDeriv (deriv f) z)
      (cobounded ℂ ⊓ 𝓟 upperHalfPlaneSet) (𝓝 L) := by
  obtain ⟨V, H, hV, h0V, hHd, hHi, hH0, hHT⟩ :=
    exists_differentiableOn_injOn_inverse_of_reflection hr hg0 hcont hholo hreal hupper hinj
  have hHan : AnalyticAt ℂ H 0 := hHd.analyticAt (hV.mem_nhds h0V)
  have hdH : ∀ w ∈ V, deriv H w ≠ 0 := fun w hw => deriv_ne_zero_of_injOn hHd hV hHi hw
  -- So `f (-1 / w) = q (-1 / H w)` on the upper part of `V`.
  set T := V ∩ upperHalfPlaneSet
  have hT : IsOpen T := hV.inter isOpen_upperHalfPlaneSet
  have hFq : EqOn (fun w => f (-w⁻¹)) (fun w => q (-(H w)⁻¹)) T := by
    intro w hw
    simpa only [(hHT w hw.1 hw.2).2] using hgq (hHT w hw.1 hw.2).1
  -- Now pass to the limit: `H w → 0` with `-1 / H w → ∞` in the upper half-plane.
  obtain ⟨ρ, hρ, hρV⟩ := Metric.isOpen_iff.mp hV 0 h0V
  set S := Metric.ball (0 : ℂ) ρ ∩ upperHalfPlaneSet
  have hST : S ⊆ T := fun w hw => ⟨hρV hw.1, hw.2⟩
  have hHS : Tendsto H (𝓝[S] 0) (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, eventually_nhdsWithin_of_forall fun w hw h => ?_⟩
    · simpa [hH0] using hHan.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    · have := (hHT w (hST hw).1 (hST hw).2).1.2
      rw [mem_singleton_iff.mp h] at this
      simp at this
  have hinf : Tendsto (fun w => -(H w)⁻¹) (𝓝[S] 0) (cobounded ℂ ⊓ 𝓟 upperHalfPlaneSet) := by
    refine tendsto_inf.mpr ⟨tendsto_neg_cobounded.comp (tendsto_inv₀_nhdsNE_zero.comp hHS),
      tendsto_principal.mpr (eventually_nhdsWithin_of_forall fun w hw => ?_)⟩
    exact im_neg_inv_pos.mpr (hHT w (hST hw).1 (hST hw).2).1.2
  have hfirst : Tendsto (fun w => -((-(H w)⁻¹) * logDeriv (deriv q) (-(H w)⁻¹)) - 2) (𝓝[S] 0)
      (𝓝 (-L - 2)) :=
    ((hqL.comp hinf).neg).sub_const 2
  have hsimple : Tendsto (fun w => w * logDeriv H w) (𝓝[S] 0) (𝓝 1) := by
    have h := hHan.tendsto_mul_logDeriv_simple_zero hH0 (hdH 0 h0V)
    simp only [sub_zero] at h
    refine h.mono_left (nhdsWithin_mono _ fun w hw h0 => ?_)
    have := hw.2
    rw [mem_singleton_iff.mp h0] at this
    simp at this
  have hrest : Tendsto (fun w => w * logDeriv (deriv H) w) (𝓝[S] 0) (𝓝 0) := by
    have hc : ContinuousAt (logDeriv (deriv H)) 0 := by
      simpa only [logDeriv, Pi.div_def] using
        hHan.deriv.deriv.continuousAt.div hHan.deriv.continuousAt (hdH 0 h0V)
    simpa using (continuousAt_id.tendsto.mul hc.tendsto).mono_left
      (nhdsWithin_le_nhds (s := S))
  have hlim : Tendsto (fun w => w * logDeriv (deriv fun w => (f (-w⁻¹) - 0) / 1) w)
      (𝓝[S] 0) (𝓝 (-L - 2)) := by
    refine Tendsto.congr' ?_ (by simpa using (hfirst.mul hsimple).add hrest)
    filter_upwards [self_mem_nhdsWithin] with w hw
    simpa using (mul_logDeriv_deriv_comp_neg_inv_eq_of_eqOn hq hqn (hV.inter
      isOpen_upperHalfPlaneSet) (hHd.mono inter_subset_left) (fun w hw => hdH w hw.1)
      (fun w hw => (hHT w hw.1 hw.2).1.2) hFq (hST hw)).symm
  simpa using tendsto_mul_logDeriv_deriv_of_tendsto_mul_logDeriv_deriv_neg_inv hρ one_ne_zero hf
    hfn hlim

end TauCeti
