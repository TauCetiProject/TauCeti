/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.Jordan.CrossRatio
public import TauCeti.Analysis.Complex.Conformal.Jordan.Unbounded
import TauCeti.Analysis.Complex.Conformal.ImageSimplyConnected
import TauCeti.Analysis.Complex.PlaneSeparation.RiemannSphere
import TauCeti.Analysis.Complex.UpperHalfPlane.Topology

/-!
# Two-point normalization of conformal maps onto unbounded Jordan domains

Let `U ⊆ ℂ` be an unbounded Jordan domain of the Riemann sphere: its frontier together with the
point at infinity is a Jordan curve. Let `f` and `g` be holomorphic bijections of the upper
half-plane onto `U` that tend to infinity at infinity. Then `g⁻¹ ∘ f` is an automorphism of the
upper half-plane fixing infinity, so it is a real affine map, and it is determined by its values at
two real points. Accordingly, if `f` and `g` have the same boundary limits at two distinct real
points, they coincide. This is the analogue, for
domains with a boundary point at infinity, of the three-point normalization
`TauCeti.eqOn_upperHalfPlaneSet_of_tendsto_of_bijOn` for bounded Jordan domains.

Both results are reduced to the bounded case. The real Möbius map `z ↦ c - z⁻¹` sends `0` to
infinity and preserves the upper half-plane, and the inversion `w ↦ (w - q)⁻¹` about a point `q`
outside the closure of `U`, which exists by
`TauCeti.exists_notMem_closure_of_isJordanCurve_insert_infty`, carries `U` onto a bounded Jordan
domain. After these changes of variable, infinity becomes the real point `0`, where both maps have
the boundary limit `0`.

## Main results

* `TauCeti.eqOn_upperHalfPlaneSet_of_tendsto_of_bijOn_of_isJordanCurve_insert_infty` -- two
  conformal maps onto an unbounded Jordan domain that tend to infinity at infinity coincide as
  soon as they have the same limits at two distinct real points.
* `TauCeti.eq_of_tendsto_of_bijOn_upperHalfPlaneSet_of_isJordanCurve_insert_infty` -- if a
  conformal map onto an unbounded Jordan domain has the same finite boundary limit at two real
  points, then the points are equal.

## References

* L. Ahlfors, *Complex Analysis*, Ch. 6, Sections 1--2.
* C. Carathéodory, Über die gegenseitige Beziehung der Ränder bei der konformen Abbildung,
  Math. Ann. 73 (1913).
-/

public section

open Bornology Complex Filter Function Set Topology UpperHalfPlane
open scoped OnePoint

namespace TauCeti

variable {U : Set ℂ} {q : ℂ}

/-- Precomposing a conformal map `f` of the upper half-plane onto `U` with `z ↦ c - z⁻¹` and
inverting about a point `q` outside the closure of `U` gives a conformal map onto the inverted
domain. -/
private theorem differentiableOn_and_bijOn_inv_sub_comp_const_sub_inv (hq : q ∉ closure U)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f upperHalfPlaneSet)
    (hfU : BijOn f upperHalfPlaneSet U) (c : ℝ) :
    DifferentiableOn ℂ (fun z => (f ((c : ℂ) - z⁻¹) - q)⁻¹) upperHalfPlaneSet ∧
      BijOn (fun z => (f ((c : ℂ) - z⁻¹) - q)⁻¹) upperHalfPlaneSet
        ((fun w : ℂ => (w - q)⁻¹) '' U) := by
  have hφ := bijOn_const_sub_inv_upperHalfPlaneSet c
  have hne : ∀ z ∈ upperHalfPlaneSet, f ((c : ℂ) - z⁻¹) - q ≠ 0 := fun z hz h =>
    hq (subset_closure (sub_eq_zero.mp h ▸ hfU.mapsTo (hφ.mapsTo hz)))
  refine ⟨(DifferentiableOn.sub_const (hf.comp ?_ hφ.mapsTo) q).inv hne,
    (inv_injective.comp (sub_left_injective (b := q))).injOn.bijOn_image.comp (hfU.comp hφ)⟩
  exact (differentiableOn_const _).sub (differentiableOn_id.inv fun z (hz : 0 < z.im) h => by
    simp [h] at hz)

/-- After the changes of variable of `differentiableOn_and_bijOn_inv_sub_comp_const_sub_inv`, a
finite boundary limit `w` of `f` at the real point `x ≠ c` becomes the limit `(w - q)⁻¹` at the
real point `(c - x)⁻¹`. -/
private theorem tendsto_inv_sub_comp_const_sub_inv (hq : q ∉ closure U) {f : ℂ → ℂ}
    (hfU : MapsTo f upperHalfPlaneSet U) {c x : ℝ} (hxc : x ≠ c) {w : ℂ}
    (hx : Tendsto f (𝓝[upperHalfPlaneSet] (x : ℂ)) (𝓝 w)) :
    Tendsto (fun z => (f ((c : ℂ) - z⁻¹) - q)⁻¹) (𝓝[upperHalfPlaneSet] (((c - x)⁻¹ : ℝ) : ℂ))
      (𝓝 (w - q)⁻¹) := by
  have := Real.nhdsWithin_upperHalfPlaneSet_neBot x
  have hwq : w - q ≠ 0 := fun h => hq (sub_eq_zero.mp h ▸
    mem_closure_of_tendsto hx (eventually_nhdsWithin_of_forall fun z hz => hfU hz))
  have hs : (((c - x)⁻¹ : ℝ) : ℂ) ≠ 0 := by
    simpa [sub_eq_zero] using hxc.symm
  have hcont : Tendsto (fun z : ℂ => (c : ℂ) - z⁻¹) (𝓝 (((c - x)⁻¹ : ℝ) : ℂ)) (𝓝 (x : ℂ)) := by
    have h : ContinuousAt (fun z : ℂ => (c : ℂ) - z⁻¹) (((c - x)⁻¹ : ℝ) : ℂ) :=
      continuousAt_const.sub (continuousAt_inv₀ hs)
    convert h.tendsto using 2
    simp
  have hφ : Tendsto (fun z : ℂ => (c : ℂ) - z⁻¹) (𝓝[upperHalfPlaneSet] (((c - x)⁻¹ : ℝ) : ℂ))
      (𝓝[upperHalfPlaneSet] (x : ℂ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hcont.mono_left nhdsWithin_le_nhds,
      eventually_nhdsWithin_of_forall (bijOn_const_sub_inv_upperHalfPlaneSet c).mapsTo⟩
  exact ((hx.comp hφ).sub_const q).inv₀ hwq

/-- After the changes of variable of `differentiableOn_and_bijOn_inv_sub_comp_const_sub_inv`, the
limit of `f` at infinity becomes the limit `0` at the real point `0`. -/
private theorem tendsto_inv_sub_comp_const_sub_inv_zero {f : ℂ → ℂ}
    (hf : Tendsto f (cobounded ℂ ⊓ 𝓟 upperHalfPlaneSet) (cobounded ℂ)) (c : ℝ) :
    Tendsto (fun z => (f ((c : ℂ) - z⁻¹) - q)⁻¹) (𝓝[upperHalfPlaneSet] ((0 : ℝ) : ℂ)) (𝓝 0) := by
  have hφ : Tendsto (fun z : ℂ => (c : ℂ) - z⁻¹) (𝓝[upperHalfPlaneSet] ((0 : ℝ) : ℂ))
      (cobounded ℂ ⊓ 𝓟 upperHalfPlaneSet) := by
    have hsub : upperHalfPlaneSet ⊆ {z : ℂ | 0 ≤ z.im} \ {0} := fun z (hz : 0 < z.im) =>
      ⟨hz.le, by rintro rfl; simp at hz⟩
    rw [ofReal_zero]
    refine tendsto_inf.mpr ⟨((tendsto_const_sub_inv_nhdsWithin_zero c).mono_left
      (nhdsWithin_mono _ hsub)).mono_right inf_le_left, tendsto_principal.mpr
      (eventually_nhdsWithin_of_forall (bijOn_const_sub_inv_upperHalfPlaneSet c).mapsTo)⟩
  exact (tendsto_inv₀_cobounded.comp (tendsto_sub_const_cobounded q)).comp (hf.comp hφ)

/-- **Two-point normalization of conformal maps onto an unbounded Jordan domain.** Let `U` be an
unbounded Jordan domain of the Riemann sphere, and let `f` and `g` be holomorphic bijections of the
upper half-plane onto `U` that tend to infinity at infinity. If, at each of two distinct real
points, `f` and `g` have the same limit along the upper half-plane, then `f` and `g` coincide on the
upper half-plane. -/
theorem eqOn_upperHalfPlaneSet_of_tendsto_of_bijOn_of_isJordanCurve_insert_infty
    (hUJ : IsJordanCurve (insert ∞ (((↑) : ℂ → OnePoint ℂ) '' frontier U)))
    {f g : ℂ → ℂ} (hf : DifferentiableOn ℂ f upperHalfPlaneSet)
    (hg : DifferentiableOn ℂ g upperHalfPlaneSet) (hfU : BijOn f upperHalfPlaneSet U)
    (hgU : BijOn g upperHalfPlaneSet U)
    (hfinf : Tendsto f (cobounded ℂ ⊓ 𝓟 upperHalfPlaneSet) (cobounded ℂ))
    (hginf : Tendsto g (cobounded ℂ ⊓ 𝓟 upperHalfPlaneSet) (cobounded ℂ)) {x₁ x₂ : ℝ}
    (h₁₂ : x₁ ≠ x₂) {w₁ w₂ : ℂ}
    (hf₁ : Tendsto f (𝓝[upperHalfPlaneSet] (x₁ : ℂ)) (𝓝 w₁))
    (hf₂ : Tendsto f (𝓝[upperHalfPlaneSet] (x₂ : ℂ)) (𝓝 w₂))
    (hg₁ : Tendsto g (𝓝[upperHalfPlaneSet] (x₁ : ℂ)) (𝓝 w₁))
    (hg₂ : Tendsto g (𝓝[upperHalfPlaneSet] (x₂ : ℂ)) (𝓝 w₂)) :
    EqOn f g upperHalfPlaneSet := by
  have hUo : IsOpen U := hfU.image_eq ▸
    isOpen_image_of_differentiableOn_of_injOn isOpen_upperHalfPlaneSet hf hfU.injOn
  obtain ⟨q, hq⟩ := exists_notMem_closure_of_isJordanCurve_insert_infty hUo
    (hfU.image_eq ▸ (convex_halfSpace_im_gt (r := 0)).isPreconnected.image f hf.continuousOn) hUJ
  -- the point `c` goes to infinity, so it must differ from `x₁` and `x₂`
  set c : ℝ := max x₁ x₂ + 1
  have h₁ : x₁ ≠ c := ((le_max_left x₁ x₂).trans_lt (lt_add_one _)).ne
  have h₂ : x₂ ≠ c := ((le_max_right x₁ x₂).trans_lt (lt_add_one _)).ne
  have h0 {x : ℝ} (hx : x ≠ c) : (0 : ℝ) ≠ (c - x)⁻¹ :=
    (inv_ne_zero (sub_ne_zero.mpr hx.symm)).symm
  obtain ⟨hFd, hFU⟩ := differentiableOn_and_bijOn_inv_sub_comp_const_sub_inv hq hf hfU c
  obtain ⟨hGd, hGU⟩ := differentiableOn_and_bijOn_inv_sub_comp_const_sub_inv hq hg hgU c
  have hFG := eqOn_upperHalfPlaneSet_of_tendsto_of_bijOn (isBounded_image_inv_sub hq)
    (isJordanCurve_frontier_image_inv_sub hUo hq hUJ) hFd hGd hFU hGU (h0 h₁) (h0 h₂)
    (fun h => h₁₂ (sub_right_injective (inv_injective h)))
    (tendsto_inv_sub_comp_const_sub_inv_zero hfinf c)
    (tendsto_inv_sub_comp_const_sub_inv hq hfU.mapsTo h₁ hf₁)
    (tendsto_inv_sub_comp_const_sub_inv hq hfU.mapsTo h₂ hf₂)
    (tendsto_inv_sub_comp_const_sub_inv_zero hginf c)
    (tendsto_inv_sub_comp_const_sub_inv hq hgU.mapsTo h₁ hg₁)
    (tendsto_inv_sub_comp_const_sub_inv hq hgU.mapsTo h₂ hg₂)
  intro z hz
  obtain ⟨z', hz', rfl⟩ := (bijOn_const_sub_inv_upperHalfPlaneSet c).surjOn hz
  simpa using hFG hz'

/-- **Distinct real points have distinct boundary limits.** If a holomorphic bijection of the upper
half-plane onto an unbounded Jordan domain of the Riemann sphere has the same finite limit along
the upper half-plane at two real points, then these points are equal. -/
theorem eq_of_tendsto_of_bijOn_upperHalfPlaneSet_of_isJordanCurve_insert_infty
    (hUJ : IsJordanCurve (insert ∞ (((↑) : ℂ → OnePoint ℂ) '' frontier U)))
    {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g upperHalfPlaneSet) (hgU : BijOn g upperHalfPlaneSet U)
    {x y : ℝ} {w : ℂ} (hx : Tendsto g (𝓝[upperHalfPlaneSet] (x : ℂ)) (𝓝 w))
    (hy : Tendsto g (𝓝[upperHalfPlaneSet] (y : ℂ)) (𝓝 w)) : x = y := by
  have hUo : IsOpen U := hgU.image_eq ▸
    isOpen_image_of_differentiableOn_of_injOn isOpen_upperHalfPlaneSet hg hgU.injOn
  obtain ⟨q, hq⟩ := exists_notMem_closure_of_isJordanCurve_insert_infty hUo
    (hgU.image_eq ▸ (convex_halfSpace_im_gt (r := 0)).isPreconnected.image g hg.continuousOn) hUJ
  set c : ℝ := max x y + 1
  have hxc : x ≠ c := ((le_max_left x y).trans_lt (lt_add_one _)).ne
  have hyc : y ≠ c := ((le_max_right x y).trans_lt (lt_add_one _)).ne
  obtain ⟨hGd, hGU⟩ := differentiableOn_and_bijOn_inv_sub_comp_const_sub_inv hq hg hgU c
  have h := eq_of_tendsto_of_bijOn_upperHalfPlaneSet (isBounded_image_inv_sub hq)
    (isJordanCurve_frontier_image_inv_sub hUo hq hUJ) hGd hGU
    (tendsto_inv_sub_comp_const_sub_inv hq hgU.mapsTo hxc hx)
    (tendsto_inv_sub_comp_const_sub_inv hq hgU.mapsTo hyc hy)
  exact sub_right_injective (inv_injective h)

end TauCeti

end
