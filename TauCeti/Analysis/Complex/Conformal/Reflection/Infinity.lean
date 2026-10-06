/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.PreSchwarzian
public import TauCeti.Analysis.Complex.Conformal.Reflection.Injective
public import TauCeti.Analysis.Complex.UpperHalfPlane.Topology
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

end TauCeti
