/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.Jordan.UpperHalfPlane
public import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Topology.Bornology.BoundedOperation

/-!
# Unbounded Jordan domains

An unbounded open set `U ⊆ ℂ` is a Jordan domain of the Riemann sphere when its frontier,
together with the point at infinity, is a Jordan curve in `OnePoint ℂ`: for instance the upper
half-plane, a sector, or an unbounded polygonal domain.  Inverting such a domain about a point `q`
outside its closure, `z ↦ (z - q)⁻¹`, gives a bounded domain whose frontier is the inverted
frontier of `U` together with `0`, the image of infinity; so it is a bounded Jordan domain of the
plane.  Carathéodory's theorem for that bounded domain, read back through the inversion, gives the
Riemann map of `U` on the closed upper half-plane: a homeomorphism onto the closure of `U` which
sends the real line onto the frontier and tends to infinity at infinity.

## Main statements

* `TauCeti.frontier_image_inv_sub`: inverting an open unbounded set about a point outside its
  closure adds `0` to the inverted frontier.
* `TauCeti.isJordanCurve_frontier_image_inv_sub`: the inversion of an unbounded Jordan domain about
  an exterior point is a bounded Jordan domain.
* `TauCeti.exists_continuousOn_bijOn_upperHalfPlaneSet_of_isJordanCurve_insert_infty`:
  Carathéodory's theorem on the closed upper half-plane for an unbounded Jordan domain, with
  infinity sent to infinity.
* `TauCeti.exists_prevertices_of_isJordanCurve_insert_infty`: such a map with real prevertices of
  prescribed frontier points.

## References

* C. Carathéodory, Über die gegenseitige Beziehung der Ränder bei der konformen Abbildung,
  Math. Ann. 73 (1913).
* Ch. Pommerenke, Boundary Behaviour of Conformal Maps, Springer, 1992, Ch. 2.
-/

public section

open Bornology Complex Filter Function Metric Set Topology UpperHalfPlane
open scoped OnePoint

namespace TauCeti

variable {U : Set ℂ} {q : ℂ}

/-- The inversion `z ↦ (z - q)⁻¹` maps an open set not containing `q` to an open set. -/
theorem isOpen_image_inv_sub (hUo : IsOpen U) (hqU : q ∉ U) :
    IsOpen ((fun z : ℂ => (z - q)⁻¹) '' U) := by
  -- the image is the preimage of `U` under `w ↦ q + w⁻¹`, which is continuous away from `0`
  have : (fun z : ℂ => (z - q)⁻¹) '' U = {0}ᶜ ∩ (fun w : ℂ => q + w⁻¹) ⁻¹' U := by
    rw [image_eq_preimage_of_inverse (f := fun z : ℂ => (z - q)⁻¹)
      (g := fun w : ℂ => q + w⁻¹)
      (by intro z; simp) (by intro w; simp)]
    exact (inter_eq_right.mpr fun w hw (hw0 : w = 0) => hqU (by simpa [hw0] using hw)).symm
  rw [this]
  exact (continuousOn_const.add continuousOn_inv₀).isOpen_inter_preimage isOpen_compl_singleton hUo

/-- Inverting a set `U` about a point `q` outside its closure gives a bounded set. -/
theorem isBounded_image_inv_sub (hq : q ∉ closure U) :
    IsBounded ((fun z : ℂ => (z - q)⁻¹) '' U) := by
  -- a ball about `q` misses `U`, so the inversion is bounded by the inverse of its radius
  obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.mp isClosed_closure.isOpen_compl q hq
  refine isBounded_iff_forall_norm_le.mpr ⟨r⁻¹, ?_⟩
  rintro _ ⟨z, hz, rfl⟩
  have hrz : r ≤ ‖z - q‖ := by
    rw [← dist_eq_norm, dist_comm]
    exact not_lt.mp fun h => hrU (mem_ball'.mpr h) (subset_closure hz)
  rw [norm_inv]
  exact inv_anti₀ hr hrz

/-- A Jordan curve of the Riemann sphere through the point at infinity is unbounded in the plane:
were its finite part `S` bounded, infinity would be an isolated point of the curve. -/
theorem not_isBounded_of_isJordanCurve_insert_infty {S : Set ℂ}
    (hS : IsJordanCurve (insert ∞ (((↑) : ℂ → OnePoint ℂ) '' S))) : ¬IsBounded S := by
  intro hSb
  -- infinity and the rest of the curve are separated by the open sets
  -- `(closure S)ᶜ ∪ {∞}` and `{∞}ᶜ`
  obtain ⟨x, hx, hxinf⟩ := (not_subsingleton_iff.mp hS.not_subsingleton).exists_ne ∞
  obtain ⟨y, hyS, hyO, hyinf⟩ := hS.isConnected.isPreconnected
    (((↑) : ℂ → OnePoint ℂ) '' closure S)ᶜ {∞}ᶜ
    (OnePoint.isOpen_compl_image_coe.mpr ⟨isClosed_closure, hSb.isCompact_closure⟩)
    isOpen_compl_singleton (fun z _ => by by_cases h : z = ∞ <;> simp [h])
    ⟨∞, mem_insert _ _, OnePoint.infty_notMem_image_coe⟩ ⟨x, hx, hxinf⟩
  rcases hyS with rfl | ⟨z, hz, rfl⟩
  · exact hyinf rfl
  · exact hyO (mem_image_of_mem _ (subset_closure hz))

/-- An open set whose frontier is, with the point at infinity, a Jordan curve of the Riemann sphere
is unbounded. -/
theorem not_isBounded_of_isJordanCurve_frontier
    (hUJ : IsJordanCurve (insert ∞ (((↑) : ℂ → OnePoint ℂ) '' frontier U))) : ¬IsBounded U :=
  fun h =>
    not_isBounded_of_isJordanCurve_insert_infty hUJ (h.closure.subset frontier_subset_closure)

/-- Inverting an unbounded set `U` about a point `q` outside its closure, the closure of the image
is the image of the closure together with `0`, the image of infinity. -/
theorem closure_image_inv_sub (hq : q ∉ closure U) (hUb : ¬IsBounded U) :
    closure ((fun z : ℂ => (z - q)⁻¹) '' U) = insert 0 ((fun z : ℂ => (z - q)⁻¹) '' closure U) := by
  refine Subset.antisymm (fun w hw => ?_) (insert_subset ?_ ?_)
  · rcases eq_or_ne w 0 with rfl | hw0
    · exact mem_insert _ _
    refine mem_insert_of_mem _ ?_
    rw [image_eq_preimage_of_inverse (f := fun z : ℂ => (z - q)⁻¹)
      (g := fun w : ℂ => q + w⁻¹)
      (by intro z; simp) (by intro w; simp)]
    have hκ : ContinuousAt (fun w : ℂ => q + w⁻¹) w := by fun_prop (disch := exact hw0)
    have h := mem_closure_image hκ hw
    rwa [image_eq_preimage_of_inverse (f := fun z : ℂ => (z - q)⁻¹)
      (g := fun w : ℂ => q + w⁻¹)
      (by intro z; simp) (by intro w; simp),
      image_preimage_eq _ fun z => ⟨(z - q)⁻¹, by simp⟩] at h
  · -- `U` reaches infinity, where the inversion tends to `0`
    have : NeBot (cobounded ℂ ⊓ 𝓟 U) := by
      rw [neBot_iff, Ne, inf_principal_eq_bot, ← isBounded_def]
      exact hUb
    exact mem_closure_of_tendsto
      ((tendsto_inv₀_cobounded.comp (tendsto_sub_const_cobounded q)).mono_left inf_le_left)
      (mem_inf_of_right (mem_principal.mpr fun z hz => mem_image_of_mem _ hz))
  · have hc : ContinuousOn (fun z : ℂ => (z - q)⁻¹) (closure U) :=
      ContinuousOn.inv₀ (f := fun z : ℂ => z - q) (by fun_prop) fun z hz =>
        sub_ne_zero.mpr fun h => hq (h ▸ hz)
    exact hc.image_closure

/-- Inverting an open unbounded set `U` about a point `q` outside its closure, the frontier of the
image is the image of the frontier together with `0`, the image of infinity. -/
theorem frontier_image_inv_sub (hUo : IsOpen U) (hq : q ∉ closure U) (hUb : ¬IsBounded U) :
    frontier ((fun z : ℂ => (z - q)⁻¹) '' U) =
      insert 0 ((fun z : ℂ => (z - q)⁻¹) '' frontier U) := by
  have hU0 : (0 : ℂ) ∉ (fun z : ℂ => (z - q)⁻¹) '' U := by
    rintro ⟨z, hz, hz0⟩
    rw [inv_eq_zero, sub_eq_zero] at hz0
    exact hq (subset_closure (hz0 ▸ hz))
  have hV := isOpen_image_inv_sub hUo fun h => hq (subset_closure h)
  rw [hV.frontier_eq, closure_image_inv_sub hq hUb, insert_sdiff_of_notMem _ hU0,
    hUo.frontier_eq, image_sdiff (f := fun z : ℂ => (z - q)⁻¹)
      (inv_injective.comp (sub_left_injective (b := q)))]

/-- Inverting the finite part of a spherical Jordan curve through infinity about a point off
that curve gives a planar Jordan curve through `0`. No domain or frontier identification is
needed. -/
theorem isJordanCurve_insert_zero_image_inv_sub {S : Set ℂ} (hq : q ∉ S)
    (hS : IsJordanCurve (insert ∞ (((↑) : ℂ → OnePoint ℂ) '' S))) :
    IsJordanCurve (insert 0 ((fun z : ℂ => (z - q)⁻¹) '' S)) := by
  let g : OnePoint ℂ → ℂ := fun x => x.elim 0 fun z => (z - q)⁻¹
  have himg : g '' insert ∞ (((↑) : ℂ → OnePoint ℂ) '' S) =
      insert 0 ((fun z : ℂ => (z - q)⁻¹) '' S) := by
    rw [image_insert_eq, image_image]
    rfl
  rw [← himg]
  refine hS.image (fun x hx => ContinuousAt.continuousWithinAt ?_) ?_
  · cases x with
    | infty =>
      refine OnePoint.continuousAt_infty'.mpr ?_
      rw [coclosedCompact_eq_cocompact, ← Metric.cobounded_eq_cocompact]
      exact tendsto_inv₀_cobounded.comp (tendsto_sub_const_cobounded q)
    | coe z =>
      have hz : z ∈ S := by simpa using hx
      exact OnePoint.continuousAt_coe.mpr (ContinuousAt.inv₀ (by fun_prop)
        (sub_ne_zero.mpr fun h => hq (h ▸ hz)))
  · refine (injOn_insert OnePoint.infty_notMem_image_coe).mpr
      ⟨InjOn.image_of_comp (inv_injective.comp (sub_left_injective (b := q))).injOn, ?_⟩
    rintro ⟨_, ⟨z, hz, rfl⟩, hz0⟩
    have hzq : z = q := by simpa [g, sub_eq_zero] using hz0
    exact hq (hzq ▸ hz)

/-- **Inverting an unbounded Jordan domain gives a bounded Jordan domain.** If the frontier of an
open set `U`, together with infinity, is a spherical Jordan curve, inversion about a point outside
its closure gives a planar Jordan frontier through `0`. -/
theorem isJordanCurve_frontier_image_inv_sub (hUo : IsOpen U) (hq : q ∉ closure U)
    (hUJ : IsJordanCurve (insert ∞ (((↑) : ℂ → OnePoint ℂ) '' frontier U))) :
    IsJordanCurve (frontier ((fun z : ℂ => (z - q)⁻¹) '' U)) := by
  rw [frontier_image_inv_sub hUo hq (not_isBounded_of_isJordanCurve_frontier hUJ)]
  exact isJordanCurve_insert_zero_image_inv_sub
    (fun h => hq (frontier_subset_closure h)) hUJ

/-- **Carathéodory's theorem on the closed upper half-plane for an unbounded Jordan domain.**  Let
`U` be a connected open subset of `ℂ` with a point `q` outside its closure, and suppose that
the frontier of `U` together with the point at infinity is a Jordan curve of the Riemann sphere, so
that `U` is unbounded.  Then there is a map which is continuous on the closed upper half-plane,
holomorphic on the open upper half-plane, a bijection from the open upper half-plane onto `U`, from
the closed upper half-plane onto `closure U` and from the real line onto `frontier U`, and which
tends to infinity at infinity within the closed half-plane.

The Jordan curve theorem on the sphere would supply the exterior point `q` from the other
hypotheses; here it is assumed. -/
theorem exists_continuousOn_bijOn_upperHalfPlaneSet_of_isJordanCurve_insert_infty (hUo : IsOpen U)
    (hUc : IsConnected U) (hq : q ∉ closure U)
    (hUJ : IsJordanCurve (insert ∞ (((↑) : ℂ → OnePoint ℂ) '' frontier U))) :
    ∃ f : ℂ → ℂ, ContinuousOn f {z | 0 ≤ z.im} ∧ DifferentiableOn ℂ f upperHalfPlaneSet ∧
      BijOn f upperHalfPlaneSet U ∧ BijOn f {z | 0 ≤ z.im} (closure U) ∧
      BijOn f {z | z.im = 0} (frontier U) ∧
      Tendsto f (cobounded ℂ ⊓ 𝓟 {z | 0 ≤ z.im}) (cobounded ℂ) := by
  have hqU : q ∉ U := fun h => hq (subset_closure h)
  have hUb := not_isBounded_of_isJordanCurve_frontier hUJ
  -- the inverted domain is a bounded Jordan domain with `0` on its frontier
  have hVo := isOpen_image_inv_sub hUo hqU
  have hVc : IsConnected ((fun z : ℂ => (z - q)⁻¹) '' U) :=
    hUc.image _ ((continuousOn_id.sub continuousOn_const).inv₀ fun z hz =>
      sub_ne_zero.mpr fun (h : z = q) => hqU (h ▸ hz))
  have hVfr := frontier_image_inv_sub hUo hq hUb
  obtain ⟨g, hgc, hgd, hgV, hgcl, hgR, hg0⟩ :=
    exists_continuousOn_bijOn_upperHalfPlaneSet_of_isJordanCurve_frontier hVo hVc
      (isBounded_image_inv_sub hq)
      (isJordanCurve_frontier_image_inv_sub hUo hq hUJ) (hVfr ▸ mem_insert _ _)
  -- removing `0` from the closure or the frontier of the inverted domain leaves the image of the
  -- closure or the frontier of `U`, which `w ↦ q + w⁻¹` carries back
  have h0 {S : Set ℂ} (hS : S ⊆ closure U) : (0 : ℂ) ∉ (fun z : ℂ => (z - q)⁻¹) '' S := by
    rintro ⟨z, hz, hz0⟩
    rw [inv_eq_zero, sub_eq_zero] at hz0
    exact hq (hz0 ▸ hS hz)
  rw [closure_image_inv_sub hq hUb, insert_sdiff_self_of_notMem (h0 subset_rfl)] at hgcl
  rw [hVfr, insert_sdiff_self_of_notMem (h0 frontier_subset_closure)] at hgR
  have hκ (S : Set ℂ) : BijOn (fun w : ℂ => q + w⁻¹) ((fun z : ℂ => (z - q)⁻¹) '' S) S := by
    refine ⟨?_, ((add_right_injective q).comp inv_injective).injOn,
      fun z hz => ⟨_, ⟨z, hz, rfl⟩, by simp⟩⟩
    rintro _ ⟨z, hz, rfl⟩
    simpa using hz
  have hgne : ∀ z ∈ {z : ℂ | 0 ≤ z.im}, g z ≠ 0 := fun z hz hgz =>
    h0 subset_rfl (hgz ▸ hgcl.mapsTo hz)
  have hH0 : upperHalfPlaneSet ⊆ {z : ℂ | 0 ≤ z.im} := ofPred_subset_ofPred.mpr fun _ => le_of_lt
  refine ⟨fun z => q + (g z)⁻¹, continuousOn_const.add (hgc.inv₀ hgne),
    (differentiableOn_const q).add (hgd.inv fun z hz => hgne z (hH0 hz)), (hκ U).comp hgV,
    (hκ _).comp hgcl, (hκ _).comp hgR, ?_⟩
  -- `g` tends to `0` without taking the value `0`, so `q + g⁻¹` tends to infinity
  refine (tendsto_const_add_cobounded q).comp (tendsto_inv₀_nhdsNE_zero.comp ?_)
  exact tendsto_nhdsWithin_iff.mpr
    ⟨hg0, mem_inf_of_right (mem_principal.mpr fun z hz => hgne z hz)⟩

/-- A Carathéodory map of the upper half-plane onto an unbounded Jordan domain `U`, sending
infinity to infinity, together with real prevertices `a i` mapping to prescribed distinct points
`v i` of the frontier of `U`. -/
theorem exists_prevertices_of_isJordanCurve_insert_infty {ι : Type*} (hUo : IsOpen U)
    (hUc : IsConnected U) (hq : q ∉ closure U)
    (hUJ : IsJordanCurve (insert ∞ (((↑) : ℂ → OnePoint ℂ) '' frontier U))) {v : ι → ℂ}
    (hv : Injective v) (hvU : ∀ i, v i ∈ frontier U) :
    ∃ f : ℂ → ℂ, ∃ a : ι → ℝ, Injective a ∧
      DifferentiableOn ℂ f upperHalfPlaneSet ∧ ContinuousOn f {z : ℂ | 0 ≤ z.im} ∧
      InjOn f {z : ℂ | 0 ≤ z.im} ∧ BijOn f upperHalfPlaneSet U ∧ (∀ i, f (a i) = v i) ∧
      Tendsto f (cobounded ℂ ⊓ 𝓟 {z : ℂ | 0 ≤ z.im}) (cobounded ℂ) := by
  obtain ⟨f, hfc, hfd, hfH, hfcl, hfR, hfinf⟩ :=
    exists_continuousOn_bijOn_upperHalfPlaneSet_of_isJordanCurve_insert_infty hUo hUc hq hUJ
  obtain ⟨a, ha, hfa⟩ := exists_injective_forall_eq_of_surjOn_im_eq_zero hfR.surjOn hv hvU
  exact ⟨f, a, ha, hfd, hfc, hfcl.injOn, hfH, hfa, hfinf⟩

end TauCeti
