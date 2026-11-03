/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.ConnectedSum.Smooth
public import TauCeti.Geometry.Manifold.Orientation.OpenSubset
public import TauCeti.Geometry.Manifold.Orientation.Inversion
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Sum
import TauCeti.Geometry.Manifold.ContMDiff.Subtype

/-!
# The orientation of a connected sum

The connected sum `TauCeti.ConnectedSum e₁ e₂` of two manifolds `M` and `N` removes the centres of
the balls `e₁ : E → M` and `e₂ : E → N` and glues `e₁ v` to `e₂ (inversion 0 1 v)` for `v ≠ 0`. For
oriented summands the result is oriented, provided the balls are chosen to induce opposite
orientations of `E`. This file constructs that orientation.

Let `o₁` and `o₂` be orientations of `M` and `N`, and let `oE` be an orientation of `E` such that
`e₁` preserves orientation from `oE` to `o₁` and `e₂` reverses orientation from `oE` to `o₂`, at
every `v ≠ 0`. The inversion `v ↦ v / ‖v‖²` reverses every orientation of `E`
(`TauCeti.Manifold.Orientation.isOrientationReversingAt_inversion`), so the gluing map
`e₂ ∘ inversion 0 1 ∘ e₁⁻¹` preserves orientation from `o₁` to `o₂`. Hence the orientations of the
punctured summands `M ∖ {e₁ 0}` and `N ∖ {e₂ 0}`, carried to the connected sum by the derivative of
the quotient map, agree wherever both are defined. Choosing a preimage of each point therefore
gives a well-defined orientation of every tangent space of `M # N`. These tangent orientations are
locally constant because, near the image of a point of a punctured summand, they are carried from
an orientation of that summand by a local diffeomorphism
(`IsLocalDiffeomorphAt.eventually_mapOrientation_eq`), so they form an orientation
(`TauCeti.ConnectedSum.orientation`).

If instead both balls preserve orientation from `oE`, then `e₂` reverses orientation from `oE` to
`-o₂`, and the same construction orients `M # N` compatibly with `o₁` and `-o₂`. So the oriented
connected sum depends on the orientations of the summands, not only on the manifolds.

## Main definitions

* `TauCeti.ConnectedSum.orientation`: the orientation of the connected sum of oriented manifolds
  along balls inducing opposite orientations of `E`.

## Main results

* `TauCeti.ConnectedSum.isOrientationPreservingAt_inl`,
  `TauCeti.ConnectedSum.isOrientationPreservingAt_inr`: the inclusions of the punctured summands
  into the connected sum preserve orientation.
* `TauCeti.ConnectedSum.eq_orientation_iff`: this property characterizes the orientation.
* `TauCeti.ConnectedSum.orientable`: the connected sum of oriented manifolds along such balls is
  orientable.

## References

* A. Kosinski, *Differential Manifolds*, Academic Press (1993), Chapter VI, Section 1 (the connected
  sum of oriented manifolds).
* J. M. Lee, *Introduction to Smooth Manifolds*, second edition, Graduate Texts in Mathematics
  218, Springer (2013), Chapter 15 (orientations, and their pullbacks along local
  diffeomorphisms).
-/

public section

noncomputable section

open Set Function Filter Topology TopologicalSpace EuclideanGeometry Module
open scoped Manifold

namespace TauCeti.ConnectedSum

open Manifold.Orientation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T1Space M] [ChartedSpace H M] [IsManifold I 1 M]
  {N : Type*} [TopologicalSpace N] [T1Space N] [ChartedSpace H N] [IsManifold I 1 N]
  {e₁ : E → M} {e₂ : E → N} {ι : Type*} [Fintype ι]
  (h₁ : IsOpenEmbedding e₁) (h₂ : IsOpenEmbedding e₂)
  (d₁ : IsLocalDiffeomorph 𝓘(ℝ, E) I 1 e₁) (d₂ : IsLocalDiffeomorph 𝓘(ℝ, E) I 1 e₂)

/-- The derivative of the quotient map of the connected sum at a point of the first punctured
summand, read through the inclusion of that summand into the disjoint union. -/
private def derivInl (x : puncture e₁) :
    letI := chartedSpace (H := H) h₁ h₂
    TangentSpace I x ≃L[ℝ] TangentSpace I (mk e₁ e₂ (.inl x)) :=
  letI := chartedSpace (H := H) h₁ h₂
  ((isLocalDiffeomorph_sumInl (I := I) (n := 1) (M' := puncture e₂) x
    ).mfderivToContinuousLinearEquiv one_ne_zero).trans
    ((isLocalDiffeomorph_mk (n := 1) h₁ h₂ d₁ d₂ (.inl x)).mfderivToContinuousLinearEquiv
      one_ne_zero)

/-- The derivative of the quotient map of the connected sum at a point of the second punctured
summand, read through the inclusion of that summand into the disjoint union. -/
private def derivInr (y : puncture e₂) :
    letI := chartedSpace (H := H) h₁ h₂
    TangentSpace I y ≃L[ℝ] TangentSpace I (mk e₁ e₂ (.inr y)) :=
  letI := chartedSpace (H := H) h₁ h₂
  ((isLocalDiffeomorph_sumInr (I := I) (n := 1) (M := puncture e₁) y
    ).mfderivToContinuousLinearEquiv one_ne_zero).trans
    ((isLocalDiffeomorph_mk (n := 1) h₁ h₂ d₁ d₂ (.inr y)).mfderivToContinuousLinearEquiv
      one_ne_zero)

omit [FiniteDimensional ℝ E] in
private theorem coe_derivInl (x : puncture e₁) :
    letI := chartedSpace (H := H) h₁ h₂
    (derivInl h₁ h₂ d₁ d₂ x : TangentSpace I x →L[ℝ] TangentSpace I (mk e₁ e₂ (.inl x))) =
      mfderiv I I (mk e₁ e₂ ∘ Sum.inl) x := by
  let := chartedSpace (H := H) h₁ h₂
  have := isManifold (n := 1) h₁ h₂ d₁ d₂
  rw [mfderiv_comp x ((isLocalDiffeomorph_mk (n := 1) h₁ h₂ d₁ d₂ _).mdifferentiableAt
    one_ne_zero) ((isLocalDiffeomorph_sumInl (n := 1) x).mdifferentiableAt one_ne_zero)]
  simp [derivInl, ← ContinuousLinearEquiv.comp_coe]

omit [FiniteDimensional ℝ E] in
private theorem coe_derivInr (y : puncture e₂) :
    letI := chartedSpace (H := H) h₁ h₂
    (derivInr h₁ h₂ d₁ d₂ y : TangentSpace I y →L[ℝ] TangentSpace I (mk e₁ e₂ (.inr y))) =
      mfderiv I I (mk e₁ e₂ ∘ Sum.inr) y := by
  let := chartedSpace (H := H) h₁ h₂
  have := isManifold (n := 1) h₁ h₂ d₁ d₂
  rw [mfderiv_comp y ((isLocalDiffeomorph_mk (n := 1) h₁ h₂ d₁ d₂ _).mdifferentiableAt
    one_ne_zero) ((isLocalDiffeomorph_sumInr (n := 1) y).mdifferentiableAt one_ne_zero)]
  simp [derivInr, ← ContinuousLinearEquiv.comp_coe]

variable (o₁ : Manifold.Orientation I M ι) (o₂ : Manifold.Orientation I N ι)

/-- The tangent orientation at the image of a point `z` of the disjoint union of the punctured
summands, carried from `o₁` or `o₂` by the derivative of the quotient map. -/
private def auxOrientation (z : puncture e₁ ⊕ puncture e₂) :
    letI := chartedSpace (H := H) h₁ h₂
    _root_.Orientation ℝ (TangentSpace I (mk e₁ e₂ z)) ι :=
  letI := chartedSpace (H := H) h₁ h₂
  match z with
  | .inl x => _root_.Orientation.map ι (derivInl h₁ h₂ d₁ d₂ x).toLinearEquiv
      ((o₁.restrict (puncture e₁)).orientationAt x)
  | .inr y => _root_.Orientation.map ι (derivInr h₁ h₂ d₁ d₂ y).toLinearEquiv
      ((o₂.restrict (puncture e₂)).orientationAt y)

variable (oE : Manifold.Orientation 𝓘(ℝ, E) E ι)

/-- **The gluing preserves orientation.** If `e₁` preserves and `e₂` reverses orientation from
`oE`, then at glued points `e₁ v` and `e₂ (inversion 0 1 v)` the orientations carried from `o₁` and
from `o₂` agree. -/
private theorem auxOrientation_inl_eq_inr
    (he₁ : ∀ v ≠ 0, IsOrientationPreservingAt oE o₁ e₁ v)
    (he₂ : ∀ v ≠ 0, IsOrientationReversingAt oE o₂ e₂ v) {v : E} (hv : v ≠ 0)
    (hx : e₁ v ∈ puncture e₁) (hy : e₂ (inversion 0 1 v) ∈ puncture e₂) :
    letI := chartedSpace (H := H) h₁ h₂
    auxOrientation h₁ h₂ d₁ d₂ o₁ o₂ (.inl ⟨e₁ v, hx⟩) =
      auxOrientation h₁ h₂ d₁ d₂ o₁ o₂ (.inr ⟨e₂ (inversion 0 1 v), hy⟩) := by
  let := chartedSpace (H := H) h₁ h₂
  have := isManifold (n := 1) h₁ h₂ d₁ d₂
  -- Both are read off the punctured space `E ∖ {0}`, mapped into the two punctured summands by
  -- `ρ₁ = e₁` and `ρ₂ = e₂ ∘ inversion 0 1`, whose composites with the quotient map agree.
  let P := puncture (id : E → E)
  have hP (w : P) : (w : E) ≠ 0 := mem_puncture.1 w.2
  let ρ₁ : P → puncture e₁ := fun w ↦ ⟨e₁ w, mem_puncture.2 (h₁.injective.ne (hP w))⟩
  let ρ₂ : P → puncture e₂ := fun w ↦
    ⟨e₂ (inversion 0 1 w), apply_inversion_mem_puncture h₂.injective (hP w)⟩
  have hρ : (mk e₁ e₂ ∘ Sum.inl) ∘ ρ₁ = (mk e₁ e₂ ∘ Sum.inr) ∘ ρ₂ :=
    funext fun w ↦ by
      simpa only [comp_apply, mk_inl, mk_inr] using inl_eq_inr (e₁ := e₁) (e₂ := e₂) (w : E) (hP w)
        (ρ₁ w).2 (ρ₂ w).2
  let oP := oE.restrict P
  let w₀ : P := ⟨v, mem_puncture.2 hv⟩
  have hv' : inversion (0 : E) 1 v ≠ 0 := by simpa [inversion_eq_center one_ne_zero] using hv
  -- `ρ₁` and `ρ₂` are differentiable at `w₀` and preserve orientation from `oP`.
  have hinv : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) 1 (inversion (0 : E) 1 ∘ Subtype.val) w₀ :=
    (contDiffAt_const.inversion contDiffAt_const contDiffAt_id hv).contMDiffAt.comp w₀
      contMDiff_subtype_val.contMDiffAt
  have hρ₁d : MDifferentiableAt 𝓘(ℝ, E) I ρ₁ w₀ :=
    ((ContMDiffAt.subtypeVal_comp_iff (puncture e₁) ρ₁ w₀).mp
      (d₁.contMDiff.comp contMDiff_subtype_val).contMDiffAt).mdifferentiableAt one_ne_zero
  have hρ₂d : MDifferentiableAt 𝓘(ℝ, E) I ρ₂ w₀ :=
    ((ContMDiffAt.subtypeVal_comp_iff (puncture e₂) ρ₂ w₀).mp
      (d₂.contMDiff.contMDiffAt.comp w₀ hinv)).mdifferentiableAt one_ne_zero
  have hval₁ : IsOrientationPreservingAt oP o₁ (e₁ ∘ Subtype.val) w₀ :=
    (he₁ v hv).comp (isOrientationPreservingAt_restrict oE P w₀)
  have hval₂ : IsOrientationPreservingAt oP o₂ ((e₂ ∘ inversion 0 1) ∘ Subtype.val) w₀ :=
    ((he₂ _ hv').comp (isOrientationReversingAt_inversion oE one_ne_zero hv)).comp
      (isOrientationPreservingAt_restrict oE P w₀)
  have hρ₁ : IsOrientationPreservingAt oP (o₁.restrict (puncture e₁)) ρ₁ w₀ :=
    (isOrientationPreservingAt_restrict o₁ _ (ρ₁ w₀)).of_comp hval₁ hρ₁d
  have hρ₂ : IsOrientationPreservingAt oP (o₂.restrict (puncture e₂)) ρ₂ w₀ :=
    (isOrientationPreservingAt_restrict o₂ _ (ρ₂ w₀)).of_comp hval₂ hρ₂d
  obtain ⟨A, hA, hAo⟩ := (isOrientationPreservingAt_iff _ _ _ _).1 hρ₁
  obtain ⟨B, hB, hBo⟩ := (isOrientationPreservingAt_iff _ _ _ _).1 hρ₂
  -- The two transports of `oP` agree, being derivatives of the same map `P → M # N`.
  have hd₁ : MDifferentiableAt I I (mk e₁ e₂ ∘ Sum.inl) (ρ₁ w₀) :=
    ((isLocalDiffeomorph_sumInl (n := 1) (ρ₁ w₀)).comp
      (hg := isLocalDiffeomorph_mk (n := 1) h₁ h₂ d₁ d₂ _)).mdifferentiableAt one_ne_zero
  have hd₂ : MDifferentiableAt I I (mk e₁ e₂ ∘ Sum.inr) (ρ₂ w₀) :=
    ((isLocalDiffeomorph_sumInr (n := 1) (ρ₂ w₀)).comp
      (hg := isLocalDiffeomorph_mk (n := 1) h₁ h₂ d₁ d₂ _)).mdifferentiableAt one_ne_zero
  have hL : A.toLinearEquiv.trans (derivInl h₁ h₂ d₁ d₂ (ρ₁ w₀)).toLinearEquiv =
      B.toLinearEquiv.trans (derivInr h₁ h₂ d₁ d₂ (ρ₂ w₀)).toLinearEquiv := by
    have h₁' := mfderiv_comp w₀ hd₁ hρ₁d
    have h₂' := mfderiv_comp w₀ hd₂ hρ₂d
    rw [← coe_derivInl h₁ h₂ d₁ d₂, ← hA, hρ, h₂', ← coe_derivInr h₁ h₂ d₁ d₂, ← hB] at h₁'
    ext u
    exact (congrArg (fun L ↦ L u) h₁').symm
  rw [auxOrientation, auxOrientation, ← hAo, ← hBo, ← _root_.Orientation.map_trans,
    ← _root_.Orientation.map_trans]
  exact congrArg (fun L ↦ _root_.Orientation.map ι L (oP.orientationAt w₀)) hL

variable {o₁ o₂ oE} in
/-- The orientations carried from `o₁` and `o₂` agree at any two points of the disjoint union of
the punctured summands which are identified in the connected sum. -/
private theorem auxOrientation_eq_of_mk_eq
    (he₁ : ∀ v ≠ 0, IsOrientationPreservingAt oE o₁ e₁ v)
    (he₂ : ∀ v ≠ 0, IsOrientationReversingAt oE o₂ e₂ v) {z z' : puncture e₁ ⊕ puncture e₂}
    (h : mk e₁ e₂ z = mk e₁ e₂ z') :
    letI := chartedSpace (H := H) h₁ h₂
    auxOrientation h₁ h₂ d₁ d₂ o₁ o₂ z = auxOrientation h₁ h₂ d₁ d₂ o₁ o₂ z' := by
  rcases (mk_eq_mk_iff h₁.injective h₂.injective).1 h with rfl | hr | hr
  · rfl
  · rcases z with ⟨x, hx⟩ | x <;> rcases z' with y | ⟨y, hy⟩ <;>
      simp only [rel_inl_inr, not_rel_inl_inl, not_rel_inr_inl, not_rel_inr_inr] at hr
    obtain ⟨v, hv, rfl, rfl⟩ := hr
    exact auxOrientation_inl_eq_inr h₁ h₂ d₁ d₂ o₁ o₂ oE he₁ he₂ hv hx hy
  · rcases z with x | ⟨x, hx⟩ <;> rcases z' with ⟨y, hy⟩ | y <;>
      simp only [rel_inl_inr, not_rel_inl_inl, not_rel_inr_inl, not_rel_inr_inr] at hr
    obtain ⟨v, hv, rfl, rfl⟩ := hr
    exact (auxOrientation_inl_eq_inr h₁ h₂ d₁ d₂ o₁ o₂ oE he₁ he₂ hv hy hx).symm

/-- The tangent orientations of the connected sum: at each point, the orientation carried from
`o₁` or `o₂` through a chosen preimage in the disjoint union of the punctured summands. -/
private def tangentOrientation (y : ConnectedSum e₁ e₂) :
    letI := chartedSpace (H := H) h₁ h₂
    _root_.Orientation ℝ (TangentSpace I y) ι :=
  letI := chartedSpace (H := H) h₁ h₂
  auxOrientation h₁ h₂ d₁ d₂ o₁ o₂ (surjInv (mk_surjective e₁ e₂) y)

variable {o₁ o₂ oE} in
private theorem tangentOrientation_mk
    (he₁ : ∀ v ≠ 0, IsOrientationPreservingAt oE o₁ e₁ v)
    (he₂ : ∀ v ≠ 0, IsOrientationReversingAt oE o₂ e₂ v) (z : puncture e₁ ⊕ puncture e₂) :
    letI := chartedSpace (H := H) h₁ h₂
    tangentOrientation h₁ h₂ d₁ d₂ o₁ o₂ (mk e₁ e₂ z) = auxOrientation h₁ h₂ d₁ d₂ o₁ o₂ z :=
  auxOrientation_eq_of_mk_eq h₁ h₂ d₁ d₂ he₁ he₂ (surjInv_eq (mk_surjective e₁ e₂) _)

open Classical in
/-- **The orientation of the connected sum.** Let `o₁` and `o₂` be orientations of `M` and `N`,
and let the balls `e₁` and `e₂` induce opposite orientations of `E`: `e₁` preserves and `e₂`
reverses orientation from an orientation `oE` of `E`, away from the centre. Then the connected sum
`M # N` carries the orientation which agrees with `o₁` on `M ∖ {e₁ 0}` and with `o₂` on
`N ∖ {e₂ 0}` (`TauCeti.ConnectedSum.isOrientationPreservingAt_inl`,
`TauCeti.ConnectedSum.isOrientationPreservingAt_inr`). The two agree on the glued punctured balls
because the inversion `v ↦ v / ‖v‖²` reverses orientation. -/
def orientation (he₁ : ∀ v ≠ 0, IsOrientationPreservingAt oE o₁ e₁ v)
    (he₂ : ∀ v ≠ 0, IsOrientationReversingAt oE o₂ e₂ v) :
    letI := chartedSpace (H := H) h₁ h₂
    Manifold.Orientation I (ConnectedSum e₁ e₂) ι :=
  letI := chartedSpace (H := H) h₁ h₂
  haveI := isManifold (n := 1) h₁ h₂ d₁ d₂
  -- The model orientation only selects a representative lift, which the quotient forgets.
  ofVectorBundleOrientation
    (((finBasisOfFinrankEq ℝ E o₁.card_eq.symm).reindex (Fintype.equivFin ι).symm).orientation)
    o₁.card_eq
    ⟨tangentOrientation h₁ h₂ d₁ d₂ o₁ o₂, fun b ↦ by
      -- Near the image of a point of a punctured summand, the tangent orientations are carried
      -- from that summand by a local diffeomorphism, so they are locally constant.
      obtain ⟨z, rfl⟩ := mk_surjective e₁ e₂ b
      rcases z with x | y
      · exact ((isLocalDiffeomorph_sumInl (n := 1) x).comp
          (hg := isLocalDiffeomorph_mk (n := 1) h₁ h₂ d₁ d₂ _)).eventually_mapOrientation_eq
          (o₁.restrict (puncture e₁)) (tangentOrientation h₁ h₂ d₁ d₂ o₁ o₂)
          (.of_forall fun x' ↦ ⟨derivInl h₁ h₂ d₁ d₂ x', coe_derivInl h₁ h₂ d₁ d₂ x',
            (tangentOrientation_mk h₁ h₂ d₁ d₂ he₁ he₂ (.inl x')).symm⟩)
      · exact ((isLocalDiffeomorph_sumInr (n := 1) y).comp
          (hg := isLocalDiffeomorph_mk (n := 1) h₁ h₂ d₁ d₂ _)).eventually_mapOrientation_eq
          (o₂.restrict (puncture e₂)) (tangentOrientation h₁ h₂ d₁ d₂ o₁ o₂)
          (.of_forall fun y' ↦ ⟨derivInr h₁ h₂ d₁ d₂ y', coe_derivInr h₁ h₂ d₁ d₂ y',
            (tangentOrientation_mk h₁ h₂ d₁ d₂ he₁ he₂ (.inr y')).symm⟩)⟩

variable {o₁ o₂ oE} (he₁ : ∀ v ≠ 0, IsOrientationPreservingAt oE o₁ e₁ v)
  (he₂ : ∀ v ≠ 0, IsOrientationReversingAt oE o₂ e₂ v)

/-- The inclusion of the punctured first summand `M ∖ {e₁ 0}` into the connected sum preserves
orientation at `x`, from any orientation `o` of `M ∖ {e₁ 0}` which agrees with `o₁` at `x`: that
is, for which the inclusion into `M` preserves orientation at `x`. -/
theorem isOrientationPreservingAt_inl {o : Manifold.Orientation I (puncture e₁) ι}
    {x : puncture e₁} (ho : IsOrientationPreservingAt o o₁ Subtype.val x) :
    letI := chartedSpace (H := H) h₁ h₂
    haveI := isManifold (n := 1) h₁ h₂ d₁ d₂
    IsOrientationPreservingAt o (orientation h₁ h₂ d₁ d₂ o₁ o₂ oE he₁ he₂) (inl e₁ e₂) x := by
  let := chartedSpace (H := H) h₁ h₂
  have := isManifold (n := 1) h₁ h₂ d₁ d₂
  -- At `x`, `o` agrees with the restriction of `o₁`, since both are carried to `o₁` by the
  -- derivative of the inclusion.
  obtain ⟨D, hD, hDo⟩ := (isOrientationPreservingAt_iff _ _ _ _).1 ho
  have hx : o.orientationAt x = (o₁.restrict (puncture e₁)).orientationAt x :=
    (_root_.Orientation.map ι D.toLinearEquiv).injective <| hDo.trans
      ((isOrientationPreservingAt_iff_of_coe_eq _ _ _ x D hD).1
        (isOrientationPreservingAt_restrict o₁ _ x)).symm
  rw [← mk_comp_inl,
    isOrientationPreservingAt_iff_of_coe_eq _ _ _ x _ (coe_derivInl h₁ h₂ d₁ d₂ x), orientation,
    orientationAt_ofVectorBundleOrientation, hx]
  exact (tangentOrientation_mk h₁ h₂ d₁ d₂ he₁ he₂ (.inl x)).symm

/-- The inclusion of the punctured second summand `N ∖ {e₂ 0}` into the connected sum preserves
orientation at `y`, from any orientation `o` of `N ∖ {e₂ 0}` which agrees with `o₂` at `y`: that
is, for which the inclusion into `N` preserves orientation at `y`. -/
theorem isOrientationPreservingAt_inr {o : Manifold.Orientation I (puncture e₂) ι}
    {y : puncture e₂} (ho : IsOrientationPreservingAt o o₂ Subtype.val y) :
    letI := chartedSpace (H := H) h₁ h₂
    haveI := isManifold (n := 1) h₁ h₂ d₁ d₂
    IsOrientationPreservingAt o (orientation h₁ h₂ d₁ d₂ o₁ o₂ oE he₁ he₂) (inr e₁ e₂) y := by
  let := chartedSpace (H := H) h₁ h₂
  have := isManifold (n := 1) h₁ h₂ d₁ d₂
  -- At `y`, `o` agrees with the restriction of `o₂`, since both are carried to `o₂` by the
  -- derivative of the inclusion.
  obtain ⟨D, hD, hDo⟩ := (isOrientationPreservingAt_iff _ _ _ _).1 ho
  have hy : o.orientationAt y = (o₂.restrict (puncture e₂)).orientationAt y :=
    (_root_.Orientation.map ι D.toLinearEquiv).injective <| hDo.trans
      ((isOrientationPreservingAt_iff_of_coe_eq _ _ _ y D hD).1
        (isOrientationPreservingAt_restrict o₂ _ y)).symm
  rw [← mk_comp_inr,
    isOrientationPreservingAt_iff_of_coe_eq _ _ _ y _ (coe_derivInr h₁ h₂ d₁ d₂ y), orientation,
    orientationAt_ofVectorBundleOrientation, hy]
  exact (tangentOrientation_mk h₁ h₂ d₁ d₂ he₁ he₂ (.inr y)).symm

/-- **The orientation of the connected sum is characterized by its summands.** For orientations
`o₁'` of `M ∖ {e₁ 0}` and `o₂'` of `N ∖ {e₂ 0}` restricting `o₁` and `o₂`, an orientation of the
connected sum is `TauCeti.ConnectedSum.orientation` exactly when the inclusions of the two punctured
summands preserve orientation from `o₁'` and `o₂'`. -/
theorem eq_orientation_iff {o₁' : Manifold.Orientation I (puncture e₁) ι}
    {o₂' : Manifold.Orientation I (puncture e₂) ι}
    (ho₁ : ∀ x, IsOrientationPreservingAt o₁' o₁ Subtype.val x)
    (ho₂ : ∀ y, IsOrientationPreservingAt o₂' o₂ Subtype.val y)
    {o : letI := chartedSpace (H := H) h₁ h₂; Manifold.Orientation I (ConnectedSum e₁ e₂) ι} :
    letI := chartedSpace (H := H) h₁ h₂
    haveI := isManifold (n := 1) h₁ h₂ d₁ d₂
    o = orientation h₁ h₂ d₁ d₂ o₁ o₂ oE he₁ he₂ ↔
      (∀ x, IsOrientationPreservingAt o₁' o (inl e₁ e₂) x) ∧
        ∀ y, IsOrientationPreservingAt o₂' o (inr e₁ e₂) y := by
  let := chartedSpace (H := H) h₁ h₂
  have := isManifold (n := 1) h₁ h₂ d₁ d₂
  refine ⟨?_, fun ⟨hl, hr⟩ ↦ ?_⟩
  · rintro rfl
    exact ⟨fun x ↦ isOrientationPreservingAt_inl h₁ h₂ d₁ d₂ he₁ he₂ (ho₁ x),
      fun y ↦ isOrientationPreservingAt_inr h₁ h₂ d₁ d₂ he₁ he₂ (ho₂ y)⟩
  ext b
  obtain ⟨x, rfl⟩ | ⟨y, rfl⟩ := (range_inl_union_range_inr e₁ e₂).symm ▸ mem_univ b
  · exact (hl x).orientationAt_eq (isOrientationPreservingAt_inl h₁ h₂ d₁ d₂ he₁ he₂ (ho₁ x))
  · exact (hr y).orientationAt_eq (isOrientationPreservingAt_inr h₁ h₂ d₁ d₂ he₁ he₂ (ho₂ y))

include d₁ d₂ in
/-- **The connected sum of oriented manifolds is orientable**, when the balls induce opposite
orientations of `E`. -/
theorem orientable {o₁ : Manifold.Orientation I M (Fin (finrank ℝ E))}
    {o₂ : Manifold.Orientation I N (Fin (finrank ℝ E))}
    {oE : Manifold.Orientation 𝓘(ℝ, E) E (Fin (finrank ℝ E))}
    (he₁ : ∀ v ≠ 0, IsOrientationPreservingAt oE o₁ e₁ v)
    (he₂ : ∀ v ≠ 0, IsOrientationReversingAt oE o₂ e₂ v) :
    letI := chartedSpace (H := H) h₁ h₂
    Orientable I (ConnectedSum e₁ e₂) :=
  letI := chartedSpace (H := H) h₁ h₂
  ⟨⟨orientation h₁ h₂ d₁ d₂ o₁ o₂ oE he₁ he₂⟩⟩

end TauCeti.ConnectedSum
