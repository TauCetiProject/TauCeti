/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.Jordan.Unbounded.LocallyConnectedBoundary

import TauCeti.Analysis.Complex.Conformal.LocalFrontier
import TauCeti.Analysis.Complex.Conformal.UpperHalfPlane.LocallyConnectedBoundary
import TauCeti.Analysis.Complex.UpperHalfPlane.Topology

/-!
# Boundary prevertices from an inverted coordinate

For an unbounded domain, a Riemann map need not extend as a finite-valued function at every
boundary parameter.  Inversion about an exterior point replaces it by a bounded holomorphic map
`g`, which can extend continuously to the real axis even when the original map `f` escapes to
infinity there.

This file reads the boundary behaviour of `f` directly from `g`.  A nonzero boundary value of `g`
gives a finite limit of `f`, while a zero is exactly a parameter at which `f` tends to infinity.
Consequently, distinct finite points of the original frontier have distinct real prevertices,
even when several accesses to infinity prevent the boundary extension from being globally
injective.  Moreover, a finite frontier point at which the domain has preconnected approach
regions, such as a point on a side or a vertex of a polygonal domain, has only one real
prevertex.  So away from the zeros of `g` the boundary extension is injective, which is the form of
boundary correspondence that local side and end geometry needs for polygonal domains with several
vertices at infinity.

## Main results

* `TauCeti.tendsto_nhds_of_inverted_boundary_ne_zero`: a nonzero inverted boundary value gives
  the corresponding finite boundary limit.
* `TauCeti.tendsto_cobounded_iff_inverted_boundary_eq_zero`: zeros of the inverted coordinate
  are exactly the boundary parameters at which the original map escapes to infinity.
* `TauCeti.exists_injective_prevertices_of_inverted_boundary`: any injective family of finite
  frontier points has an injective family of real prevertices with the expected limits.
* `TauCeti.subsingleton_inverted_boundary_fiber_of_isPreconnectedApproachAt`: a finite frontier
  point with preconnected approach regions has at most one real prevertex.
* `TauCeti.injOn_inverted_boundary_of_isPreconnectedApproachAt` and
  `TauCeti.injOn_inverted_boundary_of_polygonal`: if every frontier point has preconnected approach
  regions, in particular for a polygonal domain, the inverted coordinate is injective on the closed
  upper half-plane away from its zeros.

## References

* C. Carathéodory, Über die gegenseitige Beziehung der Ränder bei der konformen Abbildung,
  Math. Ann. 73 (1913).
* Ch. Pommerenke, *Boundary Behaviour of Conformal Maps*, Springer, 1992, Ch. 2.
-/

public section

open Bornology Complex Filter Function Set Topology UpperHalfPlane

namespace TauCeti

variable {f g : ℂ → ℂ} {q : ℂ}

/-- On the upper half-plane the map is recovered from its inverted coordinate. -/
theorem eq_add_inv_of_inverted_coordinate
    (hgf : EqOn g (fun z => (f z - q)⁻¹) upperHalfPlaneSet) {z : ℂ}
    (hz : z ∈ upperHalfPlaneSet) : f z = q + (g z)⁻¹ := by
  rw [hgf hz, inv_inv, add_sub_cancel]

/-- A nonvanishing holomorphic inverted coordinate recovers a holomorphic original map. -/
theorem differentiableOn_of_inverted_coordinate
    (hgd : DifferentiableOn ℂ g upperHalfPlaneSet)
    (hgf : EqOn g (fun z => (f z - q)⁻¹) upperHalfPlaneSet)
    (hgne : ∀ z ∈ upperHalfPlaneSet, g z ≠ 0) :
    DifferentiableOn ℂ f upperHalfPlaneSet :=
  ((differentiableOn_const q).add (hgd.inv hgne)).congr fun _ hz =>
    eq_add_inv_of_inverted_coordinate hgf hz

/-- If the continuous inverted coordinate `g = (f - q)⁻¹` has a nonzero value at a real
boundary parameter, then `f` tends there to the corresponding finite point `q + (g x)⁻¹`. -/
theorem tendsto_nhds_of_inverted_boundary_ne_zero {x : ℝ}
    (hgc : ContinuousWithinAt g {z : ℂ | 0 ≤ z.im} (x : ℂ))
    (hgf : EqOn g (fun z => (f z - q)⁻¹) upperHalfPlaneSet) (hx : g x ≠ 0) :
    Tendsto f (𝓝[upperHalfPlaneSet] (x : ℂ)) (𝓝 (q + (g x)⁻¹)) := by
  have hH : upperHalfPlaneSet ⊆ {z : ℂ | 0 ≤ z.im} :=
    ofPred_subset_ofPred.mpr fun _ => le_of_lt
  have hg : Tendsto g (𝓝[upperHalfPlaneSet] (x : ℂ)) (𝓝 (g x)) :=
    (hgc.mono hH).tendsto
  refine Tendsto.congr' (eventually_nhdsWithin_of_forall fun z hz => ?_)
    (tendsto_const_nhds.add (hg.inv₀ hx))
  rw [hgf hz]
  simp

/-- If the continuous inverted coordinate `g = (f - q)⁻¹` vanishes at a real boundary
parameter and is nonzero in the upper half-plane, then `f` tends to infinity at that parameter. -/
theorem tendsto_cobounded_of_inverted_boundary_eq_zero {x : ℝ}
    (hgc : ContinuousWithinAt g {z : ℂ | 0 ≤ z.im} (x : ℂ))
    (hgf : EqOn g (fun z => (f z - q)⁻¹) upperHalfPlaneSet)
    (hgne : ∀ z ∈ upperHalfPlaneSet, g z ≠ 0) (hx : g x = 0) :
    Tendsto f (𝓝[upperHalfPlaneSet] (x : ℂ)) (cobounded ℂ) := by
  have hH : upperHalfPlaneSet ⊆ {z : ℂ | 0 ≤ z.im} :=
    ofPred_subset_ofPred.mpr fun _ => le_of_lt
  have hg : Tendsto g (𝓝[upperHalfPlaneSet] (x : ℂ)) (𝓝 0) := by
    simpa only [hx] using (hgc.mono hH).tendsto
  have hg₀ : Tendsto g (𝓝[upperHalfPlaneSet] (x : ℂ)) (𝓝[≠] 0) :=
    tendsto_nhdsWithin_iff.mpr
      ⟨hg, eventually_nhdsWithin_of_forall fun z hz => hgne z hz⟩
  refine Tendsto.congr' (eventually_nhdsWithin_of_forall fun z hz => ?_)
    ((tendsto_const_add_cobounded q).comp (tendsto_inv₀_nhdsNE_zero.comp hg₀))
  simp only [Function.comp_apply]
  rw [hgf hz]
  simp

/-- A real boundary parameter is a prevertex at infinity exactly when the continuous inverted
coordinate vanishes there. -/
theorem tendsto_cobounded_iff_inverted_boundary_eq_zero {x : ℝ}
    (hgc : ContinuousWithinAt g {z : ℂ | 0 ≤ z.im} (x : ℂ))
    (hgf : EqOn g (fun z => (f z - q)⁻¹) upperHalfPlaneSet)
    (hgne : ∀ z ∈ upperHalfPlaneSet, g z ≠ 0) :
    Tendsto f (𝓝[upperHalfPlaneSet] (x : ℂ)) (cobounded ℂ) ↔ g x = 0 := by
  constructor
  · intro hf
    by_contra hx
    let _ : (𝓝[upperHalfPlaneSet] (x : ℂ)).NeBot :=
      Real.nhdsWithin_upperHalfPlaneSet_neBot x
    exact (tendsto_nhds_of_inverted_boundary_ne_zero hgc hgf hx).not_tendsto
      (Metric.disjoint_nhds_cobounded _) hf
  · exact tendsto_cobounded_of_inverted_boundary_eq_zero hgc hgf hgne

/-- Distinct finite frontier points of an unbounded domain have distinct real prevertices under a
continuous inverted boundary coordinate.  At each chosen prevertex, the original map tends to the
prescribed frontier point.

The equality `hgr` is the boundary-surjectivity conclusion supplied by
`TauCeti.exists_bijOn_upperHalfPlaneSet_of_locallyConnectedSpace_frontier_image_inv_sub`. -/
theorem exists_injective_prevertices_of_inverted_boundary {U : Set ℂ} {q : ℂ}
    (hUo : IsOpen U) (hq : q ∉ closure U) (hUb : ¬IsBounded U)
    (hgc : ContinuousOn g {z : ℂ | 0 ≤ z.im})
    (hgf : EqOn g (fun z => (f z - q)⁻¹) upperHalfPlaneSet)
    (hgr : insert 0 (g '' {z : ℂ | z.im = 0}) =
      frontier ((fun z : ℂ => (z - q)⁻¹) '' U))
    { ι : Type*} {v : ι → ℂ} (hv : Injective v) (hvU : ∀ i, v i ∈ frontier U) :
    ∃ a : ι → ℝ, Injective a ∧ ∀ i,
      g (a i) = (v i - q)⁻¹ ∧
        Tendsto f (𝓝[upperHalfPlaneSet] ((a i : ℝ) : ℂ)) (𝓝 (v i)) := by
  have hvq (i : ι) : v i - q ≠ 0 := fun hi =>
    hq (sub_eq_zero.mp hi ▸ frontier_subset_closure (hvU i))
  have htarget (i : ι) : (v i - q)⁻¹ ∈ g '' {z : ℂ | z.im = 0} := by
    have hmem : (v i - q)⁻¹ ∈
        frontier ((fun z : ℂ => (z - q)⁻¹) '' U) := by
      rw [frontier_image_inv_sub hUo hq hUb]
      exact mem_insert_of_mem _ ⟨v i, hvU i, rfl⟩
    rw [← hgr, mem_insert_iff] at hmem
    exact hmem.resolve_left (inv_ne_zero (hvq i))
  choose z hzR hzg using htarget
  let a : ι → ℝ := fun i => (z i).re
  have hza (i : ι) : ((a i : ℝ) : ℂ) = z i := by
    apply Complex.ext
    · rfl
    · simpa [a] using (hzR i).symm
  have hga (i : ι) : g (a i) = (v i - q)⁻¹ := by
    rw [hza]
    exact hzg i
  refine ⟨a, fun i j hij => hv ?_, fun i => ⟨hga i, ?_⟩⟩
  · have := congrArg g (congrArg ((↑) : ℝ → ℂ) hij)
    rw [hga i, hga j, inv_inj, sub_left_inj] at this
    exact this
  · have hne : g (a i) ≠ 0 := hga i ▸ inv_ne_zero (hvq i)
    simpa [hga i, add_comm] using
      tendsto_nhds_of_inverted_boundary_ne_zero (hgc _ (by simp)) hgf hne

/-- **A finite boundary point with preconnected approach regions has at most one prevertex.** Let
`f` be a holomorphic bijection of the upper half-plane onto `U`, with `q ∉ U`, whose inverted
coordinate `g = (f - q)⁻¹` extends continuously to the closed upper half-plane and tends to `0` at
infinity. If `U` has preconnected approach regions at a point `w ≠ q`, then at most one real
parameter is sent by `g` to `(w - q)⁻¹`.

This holds whatever happens at the other boundary points, in particular when `g` vanishes at
several real parameters because `U` has several accesses to infinity. -/
theorem subsingleton_inverted_boundary_fiber_of_isPreconnectedApproachAt {U : Set ℂ} {w : ℂ}
    (hgc : ContinuousOn g {z : ℂ | 0 ≤ z.im}) (hgd : DifferentiableOn ℂ g upperHalfPlaneSet)
    (hgf : EqOn g (fun z => (f z - q)⁻¹) upperHalfPlaneSet) (hfU : BijOn f upperHalfPlaneSet U)
    (hg0 : Tendsto g (cobounded ℂ ⊓ 𝓟 {z : ℂ | 0 ≤ z.im}) (𝓝 0)) (hqU : q ∉ U) (hwq : w ≠ q)
    (hw : IsPreconnectedApproachAt U w) :
    {x : ℝ | g x = (w - q)⁻¹}.Subsingleton := by
  have hgi : InjOn g upperHalfPlaneSet := fun z hz z' hz' h => by
    rw [hgf hz, hgf hz', inv_inj, sub_left_inj] at h
    exact hfU.injOn hz hz' h
  have himg : g '' upperHalfPlaneSet = (fun z : ℂ => (z - q)⁻¹) '' U := by
    rw [hgf.image_eq, ← hfU.image_eq, image_image]
  have hinv {z : ℂ} (hz : z ≠ q) : ContinuousAt (fun z : ℂ => (z - q)⁻¹) z :=
    (continuousAt_id.sub continuousAt_const).inv₀ (sub_ne_zero.mpr hz)
  refine subsingleton_real_fiber_of_isPreconnectedApproachAt hgc hgd hgi hg0 ?_
  rw [himg]
  -- inversion about `q` is a homeomorphism near `w`, with inverse `y ↦ q + y⁻¹`
  exact hw.image (κ := fun y => q + y⁻¹) (hinv hwq)
    (fun z hz => (hinv fun h => hqU (h ▸ hz)).continuousWithinAt)
    (continuousAt_const.add (continuousAt_inv₀ (inv_ne_zero (sub_ne_zero.mpr hwq))))
    (by simp) fun z hz => by simp

/-- **The inverted coordinate is injective away from the accesses to infinity.** Let `U` be an
unbounded open set with `q ∉ closure U`, and let `f`, `g = (f - q)⁻¹` be as supplied by
`TauCeti.exists_bijOn_upperHalfPlaneSet_of_locallyConnectedSpace_frontier_image_inv_sub`. If `U` has
preconnected approach regions at every point of its frontier, then `g` is injective on the closed
upper half-plane with its zeros removed: distinct real parameters with a finite image have distinct
images, and no real parameter shares its value with an interior point.

The zeros of `g` are the real parameters at which `f` tends to infinity
(`TauCeti.tendsto_cobounded_iff_inverted_boundary_eq_zero`), and there can be several of them. -/
theorem injOn_inverted_boundary_of_isPreconnectedApproachAt {U : Set ℂ}
    (hUo : IsOpen U) (hq : q ∉ closure U) (hUb : ¬IsBounded U)
    (hgc : ContinuousOn g {z : ℂ | 0 ≤ z.im}) (hgd : DifferentiableOn ℂ g upperHalfPlaneSet)
    (hgf : EqOn g (fun z => (f z - q)⁻¹) upperHalfPlaneSet) (hfU : BijOn f upperHalfPlaneSet U)
    (hgr : insert 0 (g '' {z : ℂ | z.im = 0}) =
      frontier ((fun z : ℂ => (z - q)⁻¹) '' U))
    (hg0 : Tendsto g (cobounded ℂ ⊓ 𝓟 {z : ℂ | 0 ≤ z.im}) (𝓝 0))
    (hU : ∀ w ∈ frontier U, IsPreconnectedApproachAt U w) :
    InjOn g {z : ℂ | 0 ≤ z.im ∧ g z ≠ 0} := by
  have hqU : q ∉ U := fun h => hq (subset_closure h)
  set V := (fun z : ℂ => (z - q)⁻¹) '' U
  have hVo : IsOpen V := isOpen_image_inv_sub hUo hqU
  have hgV : MapsTo g upperHalfPlaneSet V := fun z hz => by
    rw [hgf hz]
    exact ⟨f z, hfU.mapsTo hz, rfl⟩
  have hgfr {z : ℂ} (hz : z.im = 0) : g z ∈ frontier V := hgr ▸ mem_insert_of_mem _ ⟨z, hz, rfl⟩
  have hreal {z : ℂ} (hz : z.im = 0) : ((z.re : ℝ) : ℂ) = z := Complex.ext (by simp) (by simp [hz])
  -- a boundary value lies on the frontier of the open set `V`, so it is not an interior value
  have hmix {z z' : ℂ} (hz : z.im = 0) (hz' : 0 < z'.im) : g z ≠ g z' := fun h =>
    (hVo.frontier_eq ▸ hgfr hz).2 (h ▸ hgV hz')
  rintro z ⟨hz, hgz⟩ z' ⟨hz', hgz'⟩ h
  rcases hz.eq_or_lt with hz | hz <;> rcases hz'.eq_or_lt with hz' | hz'
  · -- two real parameters: their common value is `(w - q)⁻¹` for a frontier point `w` of `U`
    have hmem := hgfr hz.symm
    rw [frontier_image_inv_sub hUo hq hUb] at hmem
    obtain ⟨w, hw, hwg⟩ := hmem.resolve_left hgz
    have hwq : w ≠ q := fun h => hq (h ▸ frontier_subset_closure hw)
    have hfib := subsingleton_inverted_boundary_fiber_of_isPreconnectedApproachAt hgc hgd hgf
      hfU hg0 hqU hwq (hU w hw)
    have hre : z.re = z'.re := hfib (x := z.re) (y := z'.re)
      (by rw [mem_ofPred_eq, hreal hz.symm]; exact hwg.symm)
      (by rw [mem_ofPred_eq, hreal hz'.symm, ← h]; exact hwg.symm)
    rw [← hreal hz.symm, ← hreal hz'.symm, hre]
  · exact absurd h (hmix hz.symm hz')
  · exact absurd h.symm (hmix hz'.symm hz)
  · -- two interior points: `g` is injective there because `f` is
    rw [hgf hz, hgf hz', inv_inj, sub_left_inj] at h
    exact hfU.injOn hz hz' h

/-- **The inverted coordinate of a polygonal domain is injective away from its ends.** Let `U` be
an unbounded open set with `q ∉ closure U`, and let `f`, `g = (f - q)⁻¹` be as supplied by
`TauCeti.exists_bijOn_upperHalfPlaneSet_of_locallyConnectedSpace_frontier_image_inv_sub`. Suppose
that `U` coincides near each frontier point other than the vertices `v i` with an open half-plane,
and near `v i` with the open sector of opening `(e i + 1) * π ≤ 2 * π`. Then `g` is injective on
the closed upper half-plane with its zeros, the prevertices of the vertices at infinity, removed. -/
theorem injOn_inverted_boundary_of_polygonal {ι : Type*} {e : ι → ℝ} (he : ∀ i, e i ≤ 1)
    {U : Set ℂ} (hUo : IsOpen U) (hq : q ∉ closure U) (hUb : ¬IsBounded U)
    (hgc : ContinuousOn g {z : ℂ | 0 ≤ z.im}) (hgd : DifferentiableOn ℂ g upperHalfPlaneSet)
    (hgf : EqOn g (fun z => (f z - q)⁻¹) upperHalfPlaneSet) (hfU : BijOn f upperHalfPlaneSet U)
    (hgr : insert 0 (g '' {z : ℂ | z.im = 0}) =
      frontier ((fun z : ℂ => (z - q)⁻¹) '' U))
    (hg0 : Tendsto g (cobounded ℂ ⊓ 𝓟 {z : ℂ | 0 ≤ z.im}) (𝓝 0)) {v : ι → ℂ}
    (hside : ∀ w ∈ frontier U, (∀ i, w ≠ v i) → ∃ ρ > 0, ∃ p b : ℂ, b ≠ 0 ∧
      ∀ z ∈ Metric.ball w ρ, (z ∈ U ↔ 0 < ((z - p) / b).im))
    (hcorner : ∀ i, ∃ ρ > 0, ∃ b : ℂ, b ≠ 0 ∧ ∀ z ∈ Metric.ball (v i) ρ, z ≠ v i →
      (z ∈ U ↔ |((z - v i) / b).arg| < (e i + 1) * Real.pi / 2)) :
    InjOn g {z : ℂ | 0 ≤ z.im ∧ g z ≠ 0} := by
  refine injOn_inverted_boundary_of_isPreconnectedApproachAt hUo hq hUb hgc hgd hgf hfU hgr hg0
    fun w hw => ?_
  by_cases hv : ∃ i, w = v i
  · obtain ⟨i, rfl⟩ := hv
    obtain ⟨ρ, hρ, b, hb, hU⟩ := hcorner i
    exact isPreconnectedApproachAt_of_forall_mem_iff_abs_arg_lt hρ hb
      (by nlinarith [Real.pi_pos, he i]) hU
  · obtain ⟨ρ, hρ, p, b, -, hU⟩ := hside w hw fun i hi => hv ⟨i, hi⟩
    exact isPreconnectedApproachAt_of_forall_mem_iff_im_div_pos hρ hU

end TauCeti
