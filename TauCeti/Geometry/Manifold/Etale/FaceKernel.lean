/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Etale.Basic
public import TauCeti.Topology.CategoryTheory.Groupoid.CornerDomain
public import TauCeti.Topology.CategoryTheory.Groupoid.Effective.Basic
public import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace

import TauCeti.Geometry.Manifold.GroupAction.FaceKernel
import TauCeti.Geometry.Manifold.VectorBundle.Tangent.Basic

/-!
# Faces of corner groupoids have the ambient ineffective kernel

Let `C` be a proper étale groupoid with Hausdorff arrow space and boundaryless object charts over a
real Banach space, and let `ρ : ι → C → ℝ` be finitely many arrow-invariant functions on objects.
The corner domain `0 ≤ ρ i` and its labelled faces are full restrictions of `C`
(`TauCeti.cornerFace`). At an object `x` of the face of a set `s` of labels, suppose each `ρ i` is
`C¹` at `x` and the differentials of the labels active at `x` are linearly independent.

Then an isotropy arrow at `x` is ineffective in the face groupoid, that is it induces the identity
germ on the face, exactly when it is ineffective in `C`
(`TauCeti.mem_ineffectiveArrows_cornerFace_iff`). So the isotropy arrows at `x` forming the
ineffective kernel of a labelled face, or of a labelled intersection of faces, through `x` are
exactly those of the ambient ineffective kernel `TauCeti.ineffectiveKernel`, including at corners
where further labels are active. In particular the kernel order seen from every face through `x`
is the ambient one.

The proof reads the isotropy action at `x` in a retained-arrow local chart
(`TauCeti.exists_contMDiff_isotropy_action_of_proper_source_target`) and applies the
corresponding statement for finite smooth actions with invariant defining functions
(`TauCeti.eventually_nhdsWithin_face_smul_eq_iff`). Arrow invariance of each `ρ i` is
essential: no arrow exchanges two labelled faces.

## References

* I. Moerdijk, *Orbifolds as groupoids: an introduction*, Section 2.
* A. Adem, J. Leida and Y. Ruan, *Orbifolds and Stringy Topology*, Cambridge Tracts in
  Mathematics 171, Cambridge University Press, 2007, Chapter 1.
-/

public section

open CategoryTheory Set Filter Topology
open scoped Manifold ContDiff

namespace TauCeti

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} {n : ℕ∞ω} {C : Type*} [Groupoid C]
  [TopologicalSpace C] [ChartedSpace H C] [IsManifold I n C]
  [TopologicalSpace (Quiver.Total C)] [ChartedSpace H' (Quiver.Total C)]
  [T2Space (Quiver.Total C)] {ι : Type*} [Finite ι] {ρ : ι → C → ℝ}

/-- **Faces detect the ineffective kernel.** In a proper étale groupoid with Hausdorff arrow
space, boundaryless object charts over a real Banach space, continuous units and composition,
and `C^n` source and target local diffeomorphisms (`1 ≤ n`), let `ρ` be finitely many
arrow-invariant functions. At an object `x` of the labelled face of `s`, where each `ρ i` is `C¹`
and the differentials of the active labels are linearly independent, an isotropy arrow at `x` is
ineffective in the face groupoid exactly when it is ineffective in the ambient groupoid. -/
theorem mem_ineffectiveArrows_cornerFace_iff
    (hp : IsProperMap fun a : Quiver.Total C ↦ (a.left, a.right))
    (hs : IsLocalDiffeomorph J I n (Quiver.Total.left : Quiver.Total C → C))
    (ht : IsLocalDiffeomorph J I n (Quiver.Total.right : Quiver.Total C → C))
    (hu : Continuous fun y : C ↦ (⟨y, y, 𝟙 y⟩ : Quiver.Total C))
    (hc : Continuous fun p : {p : Quiver.Total C × Quiver.Total C // p.1.right = p.2.left} ↦
      p.1.1.comp p.1.2 p.2) (hn : 1 ≤ n)
    (hρinv : ∀ i ⦃y z : C⦄, (y ≅ z) → ρ i y = ρ i z) {s : Set ι} {x : C}
    (hx : cornerFace ρ s x) (hρ : ∀ i, ContMDiffAt I 𝓘(ℝ) 1 (ρ i) x)
    (hlin : LinearIndependent ℝ fun i : {i // ρ i x = 0} ↦ mvfderiv I (ρ i) x) (g : x ⟶ x) :
    (⟨⟨x, hx⟩, ⟨x, hx⟩, ObjectProperty.homMk g⟩ : Quiver.Total (cornerFace ρ s).FullSubcategory) ∈
        ineffectiveArrows (cornerFace ρ s).FullSubcategory ↔
      (⟨x, x, g⟩ : Quiver.Total C) ∈ ineffectiveArrows C := by
  refine ⟨fun hF ↦ ?_, fun h ↦ mem_ineffectiveArrows_fullSubcategory_of_mem h⟩
  have := finite_aut_of_proper_source_target hp hs.isLocalHomeomorph x
  obtain ⟨U, hxU, act, F, hsmul, hfix, -, -, -, hopen, -, hsource, htarget, hcentre⟩ :=
    exists_contMDiff_isotropy_action_of_proper_source_target hp hs ht hu hc x
  let : MulAction (Aut x) U := act
  let x₀ : U := ⟨x, hxU⟩
  let gA : Aut x := Aut.of (asIso g)
  -- The arrow labelled `a` from a point `y` of the chart goes from `y` to `a • y`.
  let σ (a : Aut x) (y : U) : Quiver.Total C :=
    ⟨_, _, F.map ((ActionCategory.totalEquiv (Aut x) U).symm (a, y)).hom⟩
  have hl (a : Aut x) (y : U) : (σ a y).left = y := congrFun (hsource a) y
  have hr (a : Aut x) (y : U) : (σ a y).right = (a • y : U) := congrFun (htarget a) y
  let τ := σ gA
  have hτ : τ x₀ = ⟨x, x, g⟩ := hcentre gA
  -- On the chart, the face germ condition is the face condition for the isotropy action.
  have hface : ∀ᶠ y in 𝓝[{y : U | (∀ i, 0 ≤ ρ i y) ∧ ∀ i ∈ s, ρ i y = 0}] x₀, gA • y = y := by
    rw [mem_ineffectiveArrows_iff, isEmbedding_total_fullSubcategory.nhds_eq_comap,
      eventually_comap] at hF
    have hτF := ((hopen gA).continuous.tendsto x₀).eventually (hτ ▸ hF)
    filter_upwards [eventually_nhdsWithin_of_eventually_nhds hτF, self_mem_nhdsWithin]
      with y hy hyF
    have hyF' : cornerFace ρ s (τ y).left := by
      rw [hl, cornerFace_iff, cornerDomain_iff]
      exact hyF
    have hyF'' : cornerFace ρ s (τ y).right :=
      (isClosedUnderIsomorphisms_cornerFace hρinv s).of_iso (asIso (τ y).hom) hyF'
    have h := hy ⟨⟨_, hyF'⟩, ⟨_, hyF''⟩, ObjectProperty.homMk (τ y).hom⟩ rfl
    exact Subtype.ext ((hr gA y).symm.trans
      ((congrArg ObjectProperty.FullSubcategory.obj h).symm.trans (hl gA y)))
  -- Apply the face statement for the finite smooth isotropy action on the chart.
  have hρU (i : ι) : ContMDiffAt I 𝓘(ℝ) 1 (fun y : U ↦ ρ i y) x₀ :=
    (hρ i).comp x₀ (contMDiff_subtype_val.contMDiffAt)
  have hlinU : LinearIndependent ℝ fun i : {i // ρ i x = 0} ↦
      mvfderiv I (fun y : U ↦ ρ i y) x₀ := by
    have h : (fun i : {i // ρ i x = 0} ↦ mvfderiv I (fun y : U ↦ ρ i y) x₀) =
        fun i : {i // ρ i x = 0} ↦ mvfderiv I (ρ i) x :=
      funext fun i ↦ ContinuousLinearMap.ext fun v ↦
        Manifold.mfderiv_comp_subtype_val_apply (f := ρ i) (x := x₀) v
    rw [h]
    exact hlin
  have hgerm := (eventually_nhdsWithin_face_smul_eq_iff (fun g ↦ hsmul.contMDiff_const_smul g) hn
    hfix hρU (fun i a ↦ Eventually.of_forall fun y ↦ ?_) hlinU
    (cornerDomain_iff.mp (cornerFace_iff.mp hx).1) (cornerFace_iff.mp hx).2 gA).mp hface
  · rw [mem_ineffectiveArrows_iff, ← hτ, ← (hopen gA).map_nhds_eq, eventually_map]
    filter_upwards [hgerm] with y hy
    exact (hl gA y).trans ((congrArg Subtype.val hy).symm.trans (hr gA y).symm)
  · rw [← hl a y, ← hr a y]
    exact (hρinv i (asIso (σ a y).hom)).symm

end TauCeti
