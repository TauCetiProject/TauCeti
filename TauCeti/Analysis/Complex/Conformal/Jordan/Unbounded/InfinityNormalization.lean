/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.Jordan.Unbounded.BoundaryPrevertex

import TauCeti.Analysis.Complex.Conformal.Jordan.Unbounded.LocalBoundary
import TauCeti.Analysis.Complex.Conformal.Reflection.Infinity
import TauCeti.Analysis.Complex.UpperHalfPlane.Topology

/-!
# Sending the point at infinity of the half-plane to a finite boundary point

Let `U` be an unbounded simply connected domain with a point `q` outside its closure, and suppose
inversion about `q` gives a domain with locally connected frontier. The Riemann map `f` of the
upper half-plane onto `U` supplied by
`TauCeti.exists_bijOn_upperHalfPlaneSet_of_locallyConnectedSpace_frontier_image_inv_sub` has a
continuous inverted coordinate `g = (f - q)⁻¹` on the closed upper half-plane, and `g` tends to `0`
at infinity: the point at infinity of the half-plane is sent to an access of `U` to infinity.

This file moves the point at infinity of the half-plane to any prescribed finite frontier point
`w` of `U` instead. If `t` is a real parameter with `g t = (w - q)⁻¹`, precomposing with the real
Möbius automorphism `z ↦ t - z⁻¹` of the upper half-plane, which sends infinity to `t` and `0` to
infinity, gives a new Riemann map whose inverted coordinate is still continuous on the closed upper
half-plane, provided it is given the value `0` at `0`, and now tends to `(w - q)⁻¹` at infinity.
The access to infinity formerly at the point at infinity of the half-plane is now at the real
parameter `0`.

When every frontier point of `U` has preconnected approach regions, as for a polygonal domain, the
inverted coordinate stays injective away from its zeros, and its limit `(w - q)⁻¹` at infinity is
not one of its values on the closed upper half-plane. In that form the point at infinity of the
half-plane behaves like an ordinary boundary point of `U`. Choosing `w` on a side of a polygonal
domain gives the classical normalization of the Schwarz--Christoffel formula, in which no
prevertex lies at infinity, even when the domain has several vertices at infinity.

## Main results

* `TauCeti.exists_bijOn_upperHalfPlaneSet_tendsto_of_locallyConnectedSpace_frontier_image_inv_sub`
  -- a Riemann map of an unbounded domain with continuous inverted coordinate on the closed upper
  half-plane, sending the point at infinity of the half-plane to a prescribed finite frontier
  point.
* `TauCeti.exists_bijOn_upperHalfPlaneSet_tendsto_of_isPreconnectedApproachAt` -- the same, with
  injectivity of the inverted coordinate away from its zeros, when every frontier point has
  preconnected approach regions.
* `TauCeti.differentiableOn_update_comp_const_sub_inv`,
  `TauCeti.injOn_update_comp_const_sub_inv` -- holomorphy and injectivity away from the zeros are
  kept when moving infinity to a real point.
* `TauCeti.tendsto_mul_logDeriv_deriv_of_inverted_coordinate_of_side` -- when the point at
  infinity of the half-plane is sent to a point `w` near which `U` is a half-plane, the Riemann map
  `F` satisfies the Schwarz--Christoffel condition `z * F''(z) / F'(z) → -2` at infinity.

## References

* C. Carathéodory, Über die gegenseitige Beziehung der Ränder bei der konformen Abbildung,
  Math. Ann. 73 (1913).
* L. Ahlfors, *Complex Analysis*, Ch. 6, Section 2.
-/

public section

open Bornology Complex Filter Function Set Topology UpperHalfPlane

namespace TauCeti

variable {U : Set ℂ} {q w : ℂ}

/-- **Moving infinity to a real point, holomorphy.** Precomposing a function `g` holomorphic in
the upper half-plane with the Möbius map `z ↦ c - z⁻¹`, whatever its value at `0`, gives a function
holomorphic in the upper half-plane. -/
theorem differentiableOn_update_comp_const_sub_inv {g : ℂ → ℂ}
    (hgd : DifferentiableOn ℂ g upperHalfPlaneSet) (c : ℝ) (L : ℂ) :
    DifferentiableOn ℂ (update (fun z : ℂ => g ((c : ℂ) - z⁻¹)) 0 L) upperHalfPlaneSet := by
  have hH0 : ∀ z ∈ upperHalfPlaneSet, z ≠ 0 := fun z (hz : 0 < z.im) h => by simp [h] at hz
  exact (hgd.comp ((differentiableOn_const _).sub (differentiableOn_id.inv hH0))
    (bijOn_const_sub_inv_upperHalfPlaneSet c).mapsTo).congr fun z hz => update_of_ne (hH0 z hz) _ _

/-- **Moving infinity to a real point, injectivity.** Let `g` be injective on the closed upper
half-plane away from its zeros. Precomposing `g` with the Möbius map `z ↦ c - z⁻¹` and giving it at
`0` a value `L` which is not a nonzero value of `g` there keeps it injective away from its zeros. -/
theorem injOn_update_comp_const_sub_inv {g : ℂ → ℂ}
    (hgi : InjOn g {z : ℂ | 0 ≤ z.im ∧ g z ≠ 0}) {L : ℂ}
    (hL : L ∉ g '' {z : ℂ | 0 ≤ z.im ∧ g z ≠ 0}) (c : ℝ) :
    InjOn (update (fun z : ℂ => g ((c : ℂ) - z⁻¹)) 0 L)
      {z : ℂ | 0 ≤ z.im ∧ update (fun z : ℂ => g ((c : ℂ) - z⁻¹)) 0 L z ≠ 0} := by
  -- away from `0`, the new function is `g` at a point of the closed upper half-plane
  have hT {z : ℂ} (hz : 0 ≤ z.im) (hz0 : z ≠ 0)
      (hGz : update (fun z : ℂ => g ((c : ℂ) - z⁻¹)) 0 L z ≠ 0) :
      (c : ℂ) - z⁻¹ ∈ {z : ℂ | 0 ≤ z.im ∧ g z ≠ 0} :=
    ⟨(im_const_sub_inv_nonneg c).mpr hz, by rwa [update_of_ne hz0] at hGz⟩
  rintro z ⟨hz, hGz⟩ z' ⟨hz', hGz'⟩ h
  rcases eq_or_ne z 0 with rfl | hz0 <;> rcases eq_or_ne z' 0 with rfl | hz0'
  · rfl
  · rw [update_self, update_of_ne hz0'] at h
    exact (hL ⟨_, hT hz' hz0' hGz', h.symm⟩).elim
  · rw [update_self, update_of_ne hz0] at h
    exact (hL ⟨_, hT hz hz0 hGz, h⟩).elim
  · rw [update_of_ne hz0, update_of_ne hz0'] at h
    exact inv_injective (sub_right_injective (hgi (hT hz hz0 hGz) (hT hz' hz0' hGz') h))

/-- Precomposing a Riemann map of the upper half-plane onto `U`, with continuous inverted
coordinate `g₀ = (f₀ - q)⁻¹` tending to `0` at infinity, with the Möbius map `z ↦ t - z⁻¹` gives a
Riemann map whose inverted coordinate tends to `g₀ t` at infinity. Its boundary values are those of
`g₀`, with `g₀ t` exchanged for the value `0` at `0`, and it inherits injectivity away from its
zeros. -/
private theorem exists_inverted_coordinate_tendsto_of_ne_zero {f₀ g₀ : ℂ → ℂ}
    (hfd : DifferentiableOn ℂ f₀ upperHalfPlaneSet) (hfU : BijOn f₀ upperHalfPlaneSet U)
    (hgc : ContinuousOn g₀ {z | 0 ≤ z.im}) (hgd : DifferentiableOn ℂ g₀ upperHalfPlaneSet)
    (hgf : EqOn g₀ (fun z => (f₀ z - q)⁻¹) upperHalfPlaneSet)
    (hgne : ∀ z ∈ upperHalfPlaneSet, g₀ z ≠ 0)
    (hg0 : Tendsto g₀ (cobounded ℂ ⊓ 𝓟 {z | 0 ≤ z.im}) (𝓝 0)) {t : ℝ} (ht : g₀ t ≠ 0) :
    ∃ f g : ℂ → ℂ, DifferentiableOn ℂ f upperHalfPlaneSet ∧ BijOn f upperHalfPlaneSet U ∧
      ContinuousOn g {z | 0 ≤ z.im} ∧ DifferentiableOn ℂ g upperHalfPlaneSet ∧
      EqOn g (fun z => (f z - q)⁻¹) upperHalfPlaneSet ∧
      (∀ z ∈ upperHalfPlaneSet, g z ≠ 0) ∧
      insert (g₀ t) (g '' {z | 0 ≤ z.im}) = insert 0 (g₀ '' {z | 0 ≤ z.im}) ∧
      insert (g₀ t) (g '' {z | z.im = 0}) = insert 0 (g₀ '' {z | z.im = 0}) ∧
      Tendsto g (cobounded ℂ ⊓ 𝓟 {z | 0 ≤ z.im}) (𝓝 (g₀ t)) ∧
      (InjOn g₀ {z | 0 ≤ z.im ∧ g₀ z ≠ 0} →
        InjOn g {z | 0 ≤ z.im ∧ g z ≠ 0} ∧ g₀ t ∉ g '' {z | 0 ≤ z.im}) := by
  have hφ := bijOn_const_sub_inv_upperHalfPlaneSet t
  have hH0 : ∀ z ∈ upperHalfPlaneSet, z ≠ 0 := fun z (hz : 0 < z.im) h => by simp [h] at hz
  have hφd : DifferentiableOn ℂ (fun z : ℂ => (t : ℂ) - z⁻¹) upperHalfPlaneSet :=
    (differentiableOn_const _).sub (differentiableOn_id.inv hH0)
  set G := update (fun z : ℂ => g₀ ((t : ℂ) - z⁻¹)) 0 0
  have hG {z : ℂ} (hz : z ≠ 0) : G z = g₀ ((t : ℂ) - z⁻¹) := update_of_ne hz _ _
  refine ⟨fun z => f₀ ((t : ℂ) - z⁻¹), G, hfd.comp hφd hφ.mapsTo, hfU.comp hφ,
    continuousOn_update_comp_const_sub_inv hgc hg0 t,
    differentiableOn_update_comp_const_sub_inv hgd t 0,
    fun z hz => by rw [hG (hH0 z hz)]; exact hgf (hφ.mapsTo hz),
    fun z hz => by rw [hG (hH0 z hz)]; exact hgne _ (hφ.mapsTo hz),
    insert_image_update_comp_const_sub_inv g₀ 0 (by simp) fun _ => im_const_sub_inv_nonneg t,
    insert_image_update_comp_const_sub_inv g₀ 0 (by simp) fun _ => im_const_sub_inv_eq_zero t,
    tendsto_update_comp_const_sub_inv_cobounded (hgc _ (by simp)) 0, fun hgi =>
      ⟨injOn_update_comp_const_sub_inv hgi (fun ⟨_, hz, h⟩ => hz.2 h) t, ?_⟩⟩
  rintro ⟨z, hz, h⟩
  -- a point where the new coordinate takes the nonzero value `g₀ t` is not `0`
  have hz0 : z ≠ 0 := by
    rintro rfl
    exact ht (h.symm.trans (update_self _ _ _))
  rw [hG hz0] at h
  -- the only parameter carried to `t` by the Möbius map is the point `0` sent to infinity
  have hzt : (t : ℂ) - z⁻¹ = t :=
    hgi ⟨(im_const_sub_inv_nonneg t).mpr hz, h ▸ ht⟩ ⟨by simp, ht⟩ h
  exact hz0 (inv_eq_zero.mp (sub_eq_self.mp hzt))

/-- A finite frontier point `w` of `U` is the image of a real parameter `t` under the inverted
coordinate `g₀` of
`TauCeti.exists_bijOn_upperHalfPlaneSet_of_locallyConnectedSpace_frontier_image_inv_sub`:
`g₀ t = (w - q)⁻¹`, which is nonzero. -/
private theorem exists_inverted_boundary_eq (hUo : IsOpen U) (hq : q ∉ closure U)
    (hUb : ¬IsBounded U) {f₀ g₀ : ℂ → ℂ} (hgc : ContinuousOn g₀ {z | 0 ≤ z.im})
    (hgf : EqOn g₀ (fun z => (f₀ z - q)⁻¹) upperHalfPlaneSet)
    (hgR : insert 0 (g₀ '' {z | z.im = 0}) = frontier ((fun z : ℂ => (z - q)⁻¹) '' U))
    (hw : w ∈ frontier U) : ∃ t : ℝ, g₀ t = (w - q)⁻¹ ∧ g₀ t ≠ 0 := by
  obtain ⟨a, -, ha⟩ := exists_injective_prevertices_of_inverted_boundary hUo hq hUb hgc hgf hgR
    (v := fun _ : Unit => w) (injective_of_subsingleton _) fun _ => hw
  refine ⟨a (), (ha ()).1, ?_⟩
  rw [(ha ()).1]
  exact inv_ne_zero (sub_ne_zero.mpr fun h => hq (h ▸ frontier_subset_closure hw))

/-- **A Riemann map of an unbounded domain sending infinity to a finite frontier point.** Let `U` be
an unbounded simply connected open subset of `ℂ`, let `q ∉ closure U`, and suppose inversion about
`q` gives a domain with locally connected frontier. For every frontier point `w` of `U` there is a
holomorphic bijection `f` from the upper half-plane onto `U` whose inverted coordinate
`g = (f - q)⁻¹` extends continuously to the closed upper half-plane and tends to `(w - q)⁻¹` at
infinity: the point at infinity of the half-plane corresponds to `w`.

Together with that limit, the values of `g` on the closed upper half-plane cover the closure of the
inverted domain, and its real boundary values cover the inverted frontier. -/
theorem exists_bijOn_upperHalfPlaneSet_tendsto_of_locallyConnectedSpace_frontier_image_inv_sub
    (hUo : IsOpen U) (hUs : IsSimplyConnected U) (hq : q ∉ closure U) (hUb : ¬IsBounded U)
    [LocallyConnectedSpace (frontier ((fun z : ℂ => (z - q)⁻¹) '' U))] (hw : w ∈ frontier U) :
    ∃ f g : ℂ → ℂ, DifferentiableOn ℂ f upperHalfPlaneSet ∧ BijOn f upperHalfPlaneSet U ∧
      ContinuousOn g {z | 0 ≤ z.im} ∧ DifferentiableOn ℂ g upperHalfPlaneSet ∧
      EqOn g (fun z => (f z - q)⁻¹) upperHalfPlaneSet ∧
      (∀ z ∈ upperHalfPlaneSet, g z ≠ 0) ∧
      insert (w - q)⁻¹ (g '' {z | 0 ≤ z.im}) = closure ((fun z : ℂ => (z - q)⁻¹) '' U) ∧
      insert (w - q)⁻¹ (g '' {z | z.im = 0}) = frontier ((fun z : ℂ => (z - q)⁻¹) '' U) ∧
      Tendsto g (cobounded ℂ ⊓ 𝓟 {z | 0 ≤ z.im}) (𝓝 (w - q)⁻¹) := by
  obtain ⟨f₀, g₀, hfd, hfU, hgc, hgd, hgf, hgne, hgK, hgR, hg0⟩ :=
    exists_bijOn_upperHalfPlaneSet_of_locallyConnectedSpace_frontier_image_inv_sub hUo hUs hq hUb
  obtain ⟨t, hgt, ht⟩ := exists_inverted_boundary_eq hUo hq hUb hgc hgf hgR hw
  obtain ⟨f, g, hf, hfU', hgc', hgd', hgf', hgne', hK, hR, hlim, -⟩ :=
    exists_inverted_coordinate_tendsto_of_ne_zero hfd hfU hgc hgd hgf hgne hg0 ht
  rw [hgt] at hK hR hlim
  exact ⟨f, g, hf, hfU', hgc', hgd', hgf', hgne', hK.trans hgK, hR.trans hgR, hlim⟩

/-- **Sending infinity to a finite frontier point, with injective boundary values.** Under the
hypotheses of
`TauCeti.exists_bijOn_upperHalfPlaneSet_tendsto_of_locallyConnectedSpace_frontier_image_inv_sub`,
suppose moreover that every frontier point of `U` has preconnected approach regions, as for a
polygonal domain. Then the Riemann map can be chosen so that, besides its other properties, its
inverted coordinate `g` is injective on the closed upper half-plane with its zeros removed, and its
limit `(w - q)⁻¹` at infinity is not a value of `g` on the closed upper half-plane: no point of the
closed upper half-plane corresponds to `w` as well.

The zeros of `g` are the real parameters at which `f` tends to infinity
(`TauCeti.tendsto_cobounded_iff_inverted_boundary_eq_zero`). -/
theorem exists_bijOn_upperHalfPlaneSet_tendsto_of_isPreconnectedApproachAt
    (hUo : IsOpen U) (hUs : IsSimplyConnected U) (hq : q ∉ closure U) (hUb : ¬IsBounded U)
    [LocallyConnectedSpace (frontier ((fun z : ℂ => (z - q)⁻¹) '' U))]
    (hU : ∀ w ∈ frontier U, IsPreconnectedApproachAt U w) (hw : w ∈ frontier U) :
    ∃ f g : ℂ → ℂ, DifferentiableOn ℂ f upperHalfPlaneSet ∧ BijOn f upperHalfPlaneSet U ∧
      ContinuousOn g {z | 0 ≤ z.im} ∧ DifferentiableOn ℂ g upperHalfPlaneSet ∧
      EqOn g (fun z => (f z - q)⁻¹) upperHalfPlaneSet ∧
      (∀ z ∈ upperHalfPlaneSet, g z ≠ 0) ∧
      insert (w - q)⁻¹ (g '' {z | 0 ≤ z.im}) = closure ((fun z : ℂ => (z - q)⁻¹) '' U) ∧
      insert (w - q)⁻¹ (g '' {z | z.im = 0}) = frontier ((fun z : ℂ => (z - q)⁻¹) '' U) ∧
      Tendsto g (cobounded ℂ ⊓ 𝓟 {z | 0 ≤ z.im}) (𝓝 (w - q)⁻¹) ∧
      InjOn g {z | 0 ≤ z.im ∧ g z ≠ 0} ∧ (w - q)⁻¹ ∉ g '' {z | 0 ≤ z.im} := by
  obtain ⟨f₀, g₀, hfd, hfU, hgc, hgd, hgf, hgne, hgK, hgR, hg0⟩ :=
    exists_bijOn_upperHalfPlaneSet_of_locallyConnectedSpace_frontier_image_inv_sub hUo hUs hq hUb
  obtain ⟨t, hgt, ht⟩ := exists_inverted_boundary_eq hUo hq hUb hgc hgf hgR hw
  obtain ⟨f, g, hf, hfU', hgc', hgd', hgf', hgne', hK, hR, hlim, hinj⟩ :=
    exists_inverted_coordinate_tendsto_of_ne_zero hfd hfU hgc hgd hgf hgne hg0 ht
  obtain ⟨hgi, hgt'⟩ := hinj
    (injOn_inverted_boundary_of_isPreconnectedApproachAt hUo hq hUb hgc hgd hgf hfU hgR hg0 hU)
  rw [hgt] at hK hR hlim hgt'
  exact ⟨f, g, hf, hfU', hgc', hgd', hgf', hgne', hK.trans hgK, hR.trans hgR, hlim, hgi, hgt'⟩

/-- **The condition at infinity from a side point.**  Let `g` be continuous on the closed upper
half-plane, holomorphic and nonzero in the open one and injective away from its zeros, with
`q + g⁻¹` mapping the upper half-plane onto `U`.  If `g` tends at infinity to `(w - q)⁻¹ ≠ 0`, which
is not a value of `g`, and `U` is a half-plane near `w`, then `F = q + g⁻¹` satisfies
`z * F''(z) / F'(z) → -2` at infinity. -/
theorem tendsto_mul_logDeriv_deriv_of_inverted_coordinate_of_side {g : ℂ → ℂ}
    (hgc : ContinuousOn g {z : ℂ | 0 ≤ z.im})
    (hgd : DifferentiableOn ℂ g upperHalfPlaneSet) (hgne : ∀ z ∈ upperHalfPlaneSet, g z ≠ 0)
    (hgi : InjOn g {z : ℂ | 0 ≤ z.im ∧ g z ≠ 0})
    (hgU : (fun z => q + (g z)⁻¹) '' upperHalfPlaneSet = U)
    (hginf : Tendsto g (cobounded ℂ ⊓ 𝓟 {z : ℂ | 0 ≤ z.im}) (𝓝 (w - q)⁻¹))
    (hwg : (w - q)⁻¹ ∉ g '' {z : ℂ | 0 ≤ z.im}) (hw0 : (w - q)⁻¹ ≠ 0) {ρ : ℝ} (hρ : 0 < ρ)
    {p n : ℂ} (hn : n ≠ 0) (hUw : ∀ z ∈ Metric.ball w ρ, (z ∈ U ↔ 0 < ((z - p) / n).im)) :
    Tendsto (fun z => z * logDeriv (deriv fun z => q + (g z)⁻¹) z)
      (cobounded ℂ ⊓ 𝓟 upperHalfPlaneSet) (𝓝 (-2)) := by
  -- in the coordinate `z ↦ -z⁻¹` at infinity, `g` extends by its limit `(w - q)⁻¹` at `0`, which
  -- is not a value of `g`
  have hφ := bijOn_const_sub_inv_upperHalfPlaneSet 0
  have hH0 (z : ℂ) (hz : z ∈ upperHalfPlaneSet) : z ≠ 0 := fun h => by
    simp [h, upperHalfPlaneSet] at hz
  set G : ℂ → ℂ := update (fun z => g (((0 : ℝ) : ℂ) - z⁻¹)) 0 (w - q)⁻¹
  have hG {z : ℂ} (hz : z ≠ 0) : G z = g (((0 : ℝ) : ℂ) - z⁻¹) := update_of_ne hz _ _
  have hG0 : G ((0 : ℝ) : ℂ) = (w - q)⁻¹ := by rw [ofReal_zero]; exact update_self _ _ _
  have hGU : (fun z => q + (G z)⁻¹) '' upperHalfPlaneSet = U := by
    calc (fun z => q + (G z)⁻¹) '' upperHalfPlaneSet
        = (fun z => q + (g z)⁻¹) '' ((fun z => ((0 : ℝ) : ℂ) - z⁻¹) '' upperHalfPlaneSet) := by
          rw [image_image]
          exact image_congr fun z hz => by rw [hG (hH0 z hz)]
      _ = U := by rw [hφ.image_eq, hgU]
  have hGne (z : ℂ) (hz : z ∈ upperHalfPlaneSet) : G z ≠ 0 := by
    rw [hG (hH0 z hz)]
    exact hgne _ (hφ.mapsTo hz)
  have hGc : ContinuousOn G {z : ℂ | 0 ≤ z.im} := continuousOn_update_comp_const_sub_inv hgc hginf 0
  have hGi : InjOn G {z : ℂ | 0 ≤ z.im ∧ G z ≠ 0} :=
    injOn_update_comp_const_sub_inv hgi (fun ⟨z, hz, h⟩ => hwg ⟨z, hz.1, h⟩) 0
  have hGd : DifferentiableOn ℂ G upperHalfPlaneSet :=
    differentiableOn_update_comp_const_sub_inv hgd 0 _
  -- the side through `w`, now the image of the real parameter `0`, gives the condition at infinity
  have hUw' : ∀ z ∈ Metric.ball (q + (G ((0 : ℝ) : ℂ))⁻¹) ρ, (z ∈ U ↔ 0 < ((z - p) / n).im) := by
    rwa [hG0, inv_inv, add_sub_cancel]
  obtain ⟨r, hr, hc, hi, hreal, hupper⟩ :=
    exists_ball_side_of_inverted_coordinate hGc hGi hGU (hG0 ▸ hw0) hρ hUw'
  refine tendsto_mul_logDeriv_deriv_upperHalfPlaneSet_of_eqOn_neg_inv
    (f := fun z => q + (g z)⁻¹) (g := fun z => (q + (G z)⁻¹ - p) / n) (q := p) hr hn
    (fun z hz => by simp [hG (hH0 z hz.2)]) ((hc.sub continuousOn_const).div_const n)
    ((((differentiableOn_const q).add (hGd.inv hGne)).mono inter_subset_right).sub_const p
      |>.div_const n)
    hreal (fun z hz => hupper z hz.1 hz.2) fun z hz z' hz' h => hi hz hz' ?_
  simpa [div_left_inj' hn] using h

end TauCeti
