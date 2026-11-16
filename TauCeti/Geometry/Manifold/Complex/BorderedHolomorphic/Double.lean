/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Complex.BorderedHolomorphic.Basic
public import TauCeti.Analysis.Complex.Conformal.Reflection.Principle
-- Non-public: the non-differentiability of the absolute value is used only in a proof.
import Mathlib.Analysis.Calculus.Deriv.Abs

/-!
# Reflected chart changes for the Schottky double

The Schottky double of a Riemann surface with boundary glues the surface to its conjugate along
the boundary, using `z ↦ conj z` on boundary charts. A chart change `e` of the closed upper
half-plane that sends real points, and only those, to real points then induces the chart change
`ClosedUpperHalfPlane.schwarzDouble e` of the plane: it is `e` on the closed upper half-plane and
`z ↦ conj (e (conj z))` on the lower half-plane, that is, the Schwarz reflection
`schwarzReflection (closedUpperHalfPlaneModel ∘ e ∘ closedUpperHalfPlaneModel.symm)`.
Its source is the preimage of `e.source` under the fold `ClosedUpperHalfPlane.fold`, which sends
`z` to `re z + |im z| i`, so it is open in the plane because `e.source` is relatively open in the
closed upper half-plane.

When `e` belongs to the bordered holomorphic groupoid, the reflected chart change is
holomorphic with holomorphic inverse, by the Schwarz reflection principle; it lies in
`contDiffGroupoid ω 𝓘(ℂ)`, the groupoid of a Riemann surface without boundary. Reflection
commutes with conjugation, restricts to `e` on the closed upper half-plane, and respects
`OpenPartialHomeomorph.symm`, `OpenPartialHomeomorph.trans` (up to
`OpenPartialHomeomorph.EqOnSource`) and `OpenPartialHomeomorph.refl`. These are the properties of
chart changes needed to give the Schottky double a holomorphic atlas; the double itself is not
constructed here.

The translation `z ↦ z + 1` and the dilation `z ↦ 2z` reflect to the same maps of the plane. The
outer conjugation in `z ↦ conj (e (conj z))` matters: with `z ↦ -conj z` in its place, the
identity would become the piecewise map that is `z` on the closed upper half-plane and `-z` on the
lower half-plane, which is not complex differentiable at any real point.

## Main definitions

* `TauCeti.ClosedUpperHalfPlane.schwarzDouble`: the reflected chart change of the plane, for a
  chart change satisfying `TauCeti.ClosedUpperHalfPlane.PreservesRealAxis`.

## Main results

* `TauCeti.ClosedUpperHalfPlane.schwarzDouble_mem_contDiffGroupoid`: reflecting a member of the
  bordered holomorphic groupoid gives a holomorphic chart change of the plane.
* `TauCeti.ClosedUpperHalfPlane.schwarzDouble_conj`: the reflected chart change commutes with
  conjugation.
* `TauCeti.ClosedUpperHalfPlane.schwarzDouble_coe`: it restricts to `e` on the closed upper
  half-plane.
* `TauCeti.ClosedUpperHalfPlane.schwarzDouble_symm`, `schwarzDouble_trans`, `schwarzDouble_refl`:
  compatibility with the groupoid operations.
* `TauCeti.ClosedUpperHalfPlane.not_differentiableAt_negConj_glue`: the piecewise map that is `z`
  on the closed upper half-plane and `-conj (conj z) = -z` on the lower half-plane is not complex
  differentiable at any real point.

## References

* L. V. Ahlfors and L. Sario, *Riemann Surfaces*, Princeton University Press, 1960, Ch. II, for
  the double of a bordered Riemann surface.
-/

public section

noncomputable section

open Set Complex
open scoped Manifold ContDiff ComplexConjugate

namespace TauCeti

namespace ClosedUpperHalfPlane

variable {e e' : OpenPartialHomeomorph ClosedUpperHalfPlane ClosedUpperHalfPlane}

/-! ### The reflected chart change -/

/-- The value of the Schwarz reflection of a chart change, through the fold. -/
private theorem schwarzReflection_apply_fold (e : OpenPartialHomeomorph ClosedUpperHalfPlane
    ClosedUpperHalfPlane) (z : ℂ) :
    schwarzReflection (closedUpperHalfPlaneModel ∘ e ∘ closedUpperHalfPlaneModel.symm) z =
      if 0 ≤ z.im then (e (fold z) : ℂ) else conj (e (fold z) : ℂ) := by
  rw [schwarzReflection_def]
  split_ifs with hz
  · simp [closedUpperHalfPlaneModel_symm_eq_fold hz]
  · have hc : 0 ≤ (conj z).im := by simpa using (not_le.1 hz).le
    simp [closedUpperHalfPlaneModel_symm_eq_fold hc]

private theorem schwarzReflection_of_im_nonneg_fold (e : OpenPartialHomeomorph
    ClosedUpperHalfPlane ClosedUpperHalfPlane) {z : ℂ} (hz : 0 ≤ z.im) :
    schwarzReflection (closedUpperHalfPlaneModel ∘ e ∘ closedUpperHalfPlaneModel.symm) z =
      e (fold z) := by
  simp only [schwarzReflection_apply_fold, hz, ↓reduceIte]

private theorem schwarzReflection_of_im_neg_fold (e : OpenPartialHomeomorph
    ClosedUpperHalfPlane ClosedUpperHalfPlane) {z : ℂ} (hz : z.im < 0) :
    schwarzReflection (closedUpperHalfPlaneModel ∘ e ∘ closedUpperHalfPlaneModel.symm) z =
      conj (e (fold z) : ℂ) := by
  simp only [schwarzReflection_apply_fold, not_le.2 hz, ↓reduceIte]

/-- The fold of the reflected value is the value of `e` at the fold. -/
private theorem fold_schwarzReflection (e : OpenPartialHomeomorph ClosedUpperHalfPlane
    ClosedUpperHalfPlane) (z : ℂ) :
    fold (schwarzReflection (closedUpperHalfPlaneModel ∘ e ∘ closedUpperHalfPlaneModel.symm) z) =
      e (fold z) := by
  rw [schwarzReflection_apply_fold]
  split_ifs <;> simp

/-- The reflected value lies in the lower half-plane at the points of the lower half-plane. -/
private theorem im_schwarzReflection_neg (he : PreservesRealAxis e) {z : ℂ}
    (hz : fold z ∈ e.source) (hneg : z.im < 0) :
    (schwarzReflection (closedUpperHalfPlaneModel ∘ e ∘ closedUpperHalfPlaneModel.symm) z).im
      < 0 := by
  rw [schwarzReflection_of_im_neg_fold e hneg, conj_im, neg_neg_iff_pos]
  exact (he.im_pos_iff hz).1 (by simpa using hneg.ne)

/-- Reflecting the inverse undoes reflecting the chart change on the preimage of the source under
the fold. -/
private theorem schwarzReflection_symm_schwarzReflection (he : PreservesRealAxis e) {z : ℂ}
    (hz : fold z ∈ e.source) :
    schwarzReflection (closedUpperHalfPlaneModel ∘ e.symm ∘ closedUpperHalfPlaneModel.symm)
      (schwarzReflection (closedUpperHalfPlaneModel ∘ e ∘ closedUpperHalfPlaneModel.symm) z) =
        z := by
  rcases le_or_gt 0 z.im with hnn | hneg
  · have hw : 0 ≤ (schwarzReflection
        (closedUpperHalfPlaneModel ∘ e ∘ closedUpperHalfPlaneModel.symm) z).im := by
      rw [schwarzReflection_of_im_nonneg_fold e hnn]
      exact (e (fold z)).property
    rw [schwarzReflection_of_im_nonneg_fold _ hw, fold_schwarzReflection, e.left_inv hz,
      coe_fold_of_im_nonneg hnn]
  · rw [schwarzReflection_of_im_neg_fold _ (im_schwarzReflection_neg he hz hneg),
      fold_schwarzReflection, e.left_inv hz, coe_fold_of_im_nonpos hneg.le, conj_conj]

/-- In the coordinate of the plane, a chart change is continuous on the closed upper part of the
preimage of its source under the fold. -/
private theorem continuousOn_model_comp (e : OpenPartialHomeomorph ClosedUpperHalfPlane
    ClosedUpperHalfPlane) :
    ContinuousOn (closedUpperHalfPlaneModel ∘ e ∘ closedUpperHalfPlaneModel.symm)
      (fold ⁻¹' e.source ∩ {z | 0 ≤ z.im}) := by
  refine closedUpperHalfPlaneModel.continuous.comp_continuousOn
    (e.continuousOn.comp closedUpperHalfPlaneModel.continuous_symm.continuousOn ?_)
  intro z hz
  simpa [closedUpperHalfPlaneModel_symm_eq_fold hz.2] using hz.1

/-- In the coordinate of the plane, a chart change preserving the real axis is real on the real
points of the preimage of its source under the fold. -/
private theorem im_model_comp_eq_zero (he : PreservesRealAxis e) {z : ℂ}
    (hz : z ∈ fold ⁻¹' e.source) (hz0 : z.im = 0) :
    ((closedUpperHalfPlaneModel ∘ e ∘ closedUpperHalfPlaneModel.symm) z).im = 0 := by
  have hz' : closedUpperHalfPlaneModel.symm z = fold z :=
    closedUpperHalfPlaneModel_symm_eq_fold hz0.ge
  simpa [hz', hz0] using (he.im_eq_zero_iff hz).1 (by simp [hz0])

/-- The reflected chart change is continuous on the preimage of the source under the fold. -/
private theorem continuousOn_schwarzReflection_fold_preimage (he : PreservesRealAxis e) :
    ContinuousOn
      (schwarzReflection (closedUpperHalfPlaneModel ∘ e ∘ closedUpperHalfPlaneModel.symm))
      (fold ⁻¹' e.source) :=
  continuousOn_schwarzReflection_of_symmetric (fun z hz ↦ by simpa using hz)
    (continuousOn_model_comp e) fun _ hz hz0 ↦ im_model_comp_eq_zero he hz hz0

/-- The chart change of the plane obtained from a chart change `e` of the closed upper half-plane
that preserves the real axis by Schwarz reflection: it is `e` on the closed upper half-plane and
`z ↦ conj (e (conj z))` on the lower half-plane. This is the chart change of the Schottky double
glued along the real axis by `z ↦ conj z`. -/
def schwarzDouble (e : OpenPartialHomeomorph ClosedUpperHalfPlane ClosedUpperHalfPlane)
    (he : PreservesRealAxis e) : OpenPartialHomeomorph ℂ ℂ where
  toFun := schwarzReflection (closedUpperHalfPlaneModel ∘ e ∘ closedUpperHalfPlaneModel.symm)
  invFun := schwarzReflection (closedUpperHalfPlaneModel ∘ e.symm ∘ closedUpperHalfPlaneModel.symm)
  source := fold ⁻¹' e.source
  target := fold ⁻¹' e.target
  map_source' z hz := by
    simpa [mem_preimage, fold_schwarzReflection] using e.map_source hz
  map_target' z hz := by
    simpa [mem_preimage, fold_schwarzReflection] using e.symm.map_source hz
  left_inv' _ hz := schwarzReflection_symm_schwarzReflection he hz
  right_inv' _ hz := schwarzReflection_symm_schwarzReflection (e := e.symm) he.symm hz
  open_source := e.open_source.preimage continuous_fold
  open_target := e.open_target.preimage continuous_fold
  continuousOn_toFun := continuousOn_schwarzReflection_fold_preimage he
  continuousOn_invFun := continuousOn_schwarzReflection_fold_preimage (e := e.symm) he.symm

variable (he : PreservesRealAxis e) (he' : PreservesRealAxis e')

theorem coe_schwarzDouble :
    ⇑(schwarzDouble e he) =
      schwarzReflection (closedUpperHalfPlaneModel ∘ e ∘ closedUpperHalfPlaneModel.symm) :=
  (rfl)

@[simp]
theorem schwarzDouble_source : (schwarzDouble e he).source = fold ⁻¹' e.source :=
  (rfl)

@[simp]
theorem schwarzDouble_target : (schwarzDouble e he).target = fold ⁻¹' e.target :=
  (rfl)

@[simp]
theorem schwarzDouble_symm : (schwarzDouble e he).symm = schwarzDouble e.symm he.symm :=
  (rfl)

theorem schwarzDouble_apply_of_im_nonneg {z : ℂ} (hz : 0 ≤ z.im) :
    schwarzDouble e he z = e (fold z) :=
  schwarzReflection_of_im_nonneg_fold e hz

theorem schwarzDouble_apply_of_im_neg {z : ℂ} (hz : z.im < 0) :
    schwarzDouble e he z = conj (e (fold z) : ℂ) :=
  schwarzReflection_of_im_neg_fold e hz

/-- On the closed upper half-plane the reflected chart change is `e`. -/
@[simp]
theorem schwarzDouble_coe (z : ClosedUpperHalfPlane) : schwarzDouble e he z = e z := by
  rw [schwarzDouble_apply_of_im_nonneg he z.property, fold_coe]

@[simp]
theorem fold_schwarzDouble (z : ℂ) : fold (schwarzDouble e he z) = e (fold z) :=
  fold_schwarzReflection e z

theorem coe_mem_schwarzDouble_source_iff {z : ClosedUpperHalfPlane} :
    (z : ℂ) ∈ (schwarzDouble e he).source ↔ z ∈ e.source := by
  simp

/-- The source of the reflected chart change is invariant under conjugation. -/
theorem conj_mem_schwarzDouble_source_iff {z : ℂ} :
    conj z ∈ (schwarzDouble e he).source ↔ z ∈ (schwarzDouble e he).source := by
  simp

/-- The reflected chart change commutes with conjugation. -/
theorem schwarzDouble_conj {z : ℂ} (hz : z ∈ (schwarzDouble e he).source) :
    schwarzDouble e he (conj z) = conj (schwarzDouble e he z) :=
  schwarzReflection_conj_of_real_on_axis (Ω := fold ⁻¹' e.source)
    (fun _ hw hw0 ↦ im_model_comp_eq_zero he hw hw0) hz

/-- The reflected chart change sends the lower half-plane to the lower half-plane. -/
theorem im_schwarzDouble_neg {z : ℂ} (hz : z ∈ (schwarzDouble e he).source) (hneg : z.im < 0) :
    (schwarzDouble e he z).im < 0 :=
  im_schwarzReflection_neg he hz hneg

/-- Reflection respects composition of chart changes. -/
theorem schwarzDouble_trans : schwarzDouble (e.trans e') (he.trans he') ≈
    (schwarzDouble e he).trans (schwarzDouble e' he') := by
  refine (OpenPartialHomeomorph.eqOnSource_iff _ _).2 ⟨?_, fun z hz ↦ ?_⟩
  · ext z
    simp
  · simp only [OpenPartialHomeomorph.coe_toPartialEquiv,
      OpenPartialHomeomorph.trans_apply]
    have hz' : fold z ∈ e.source := hz.1
    rcases le_or_gt 0 z.im with hnn | hneg
    · have hw : 0 ≤ (schwarzDouble e he z).im := by
        rw [schwarzDouble_apply_of_im_nonneg he hnn]
        exact (e (fold z)).property
      rw [schwarzDouble_apply_of_im_nonneg (he.trans he') hnn,
        schwarzDouble_apply_of_im_nonneg he' hw, fold_schwarzDouble]
      simp
    · rw [schwarzDouble_apply_of_im_neg (he.trans he') hneg,
        schwarzDouble_apply_of_im_neg he' (im_schwarzDouble_neg he hz' hneg), fold_schwarzDouble]
      simp

/-- Reflecting the identity of the closed upper half-plane gives the identity of the plane. -/
@[simp]
theorem schwarzDouble_refl :
    schwarzDouble (OpenPartialHomeomorph.refl ClosedUpperHalfPlane) preservesRealAxis_refl =
      OpenPartialHomeomorph.refl ℂ := by
  have h : ∀ z, schwarzDouble (OpenPartialHomeomorph.refl ClosedUpperHalfPlane)
      preservesRealAxis_refl z = z := fun z ↦ by
    rcases le_or_gt 0 z.im with hnn | hneg
    · simp [schwarzDouble_apply_of_im_nonneg _ hnn, coe_fold_of_im_nonneg hnn]
    · simp [schwarzDouble_apply_of_im_neg _ hneg, coe_fold_of_im_nonpos hneg.le]
  refine OpenPartialHomeomorph.ext _ _ h (fun z ↦ ?_) (by simp)
  simpa using h z

/-! ### Holomorphy -/

/-- Reflecting a member of the bordered holomorphic groupoid gives a map that is complex
differentiable on its source, by the Schwarz reflection principle. -/
theorem differentiableOn_schwarzDouble (hmem : e ∈ borderedHolomorphicGroupoid) :
    DifferentiableOn ℂ (schwarzDouble e he) (schwarzDouble e he).source := by
  refine differentiableOn_schwarzReflection_of_symmetric (schwarzDouble e he).open_source
    (fun z hz ↦ by simpa using hz) (continuousOn_model_comp e)
    (((mem_borderedHolomorphicGroupoid_iff.1 hmem).2.1).mono ?_)
    fun _ hw hw0 ↦ im_model_comp_eq_zero he hw hw0
  rintro z ⟨hz, hzim⟩
  refine ⟨?_, hzim⟩
  simpa [mem_preimage, closedUpperHalfPlaneModel_symm_eq_fold hzim.le] using hz

/-- **Reflected chart changes are holomorphic.** Reflecting a member of the bordered holomorphic
groupoid along the real axis gives a holomorphic chart change of the plane with holomorphic
inverse. -/
theorem schwarzDouble_mem_contDiffGroupoid (hmem : e ∈ borderedHolomorphicGroupoid) :
    schwarzDouble e he ∈ contDiffGroupoid ω 𝓘(ℂ) := by
  rw [contDiffGroupoid, mem_groupoid_of_pregroupoid]
  simp only [contDiffPregroupoid, modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
    Function.id_comp, Function.comp_id, preimage_id_eq, id_eq, range_id, inter_univ]
  refine ⟨(differentiableOn_schwarzDouble he hmem).contDiffOn
    (schwarzDouble e he).open_source, ?_⟩
  rw [schwarzDouble_symm]
  exact (differentiableOn_schwarzDouble he.symm (borderedHolomorphicGroupoid.symm hmem)).contDiffOn
    (schwarzDouble e.symm he.symm).open_source

/-! ### Checks -/

/-- Reflecting the translation `z ↦ z + 1` of the closed upper half-plane gives the translation
`z ↦ z + 1` of the plane. -/
theorem schwarzDouble_addOne (h : PreservesRealAxis addOne.toOpenPartialHomeomorph) :
    schwarzDouble addOne.toOpenPartialHomeomorph h =
      (Homeomorph.addRight (1 : ℂ)).toOpenPartialHomeomorph := by
  refine OpenPartialHomeomorph.ext _ _ (fun z ↦ ?_) (fun z ↦ ?_) (by simp)
  · rcases le_or_gt 0 z.im with hnn | hneg
    · simp [schwarzDouble_apply_of_im_nonneg _ hnn, coe_fold_of_im_nonneg hnn]
    · simp [schwarzDouble_apply_of_im_neg _ hneg, coe_fold_of_im_nonpos hneg.le]
  · rw [schwarzDouble_symm]
    rcases le_or_gt 0 z.im with hnn | hneg
    · simp [schwarzDouble_apply_of_im_nonneg _ hnn, coe_fold_of_im_nonneg hnn,
        Homeomorph.addRight_symm, sub_eq_add_neg]
    · simp [schwarzDouble_apply_of_im_neg _ hneg, coe_fold_of_im_nonpos hneg.le,
        Homeomorph.addRight_symm, sub_eq_add_neg]

/-- Reflecting the dilation `z ↦ 2z` of the closed upper half-plane gives the dilation
`z ↦ 2z` of the plane. -/
theorem schwarzDouble_twoMul (h : PreservesRealAxis twoMul.toOpenPartialHomeomorph) :
    schwarzDouble twoMul.toOpenPartialHomeomorph h =
      (Homeomorph.mulLeft₀ (2 : ℂ) two_ne_zero).toOpenPartialHomeomorph := by
  refine OpenPartialHomeomorph.ext _ _ (fun z ↦ ?_) (fun z ↦ ?_) (by simp)
  · rcases le_or_gt 0 z.im with hnn | hneg
    · simp [schwarzDouble_apply_of_im_nonneg _ hnn, coe_fold_of_im_nonneg hnn]
    · simp [schwarzDouble_apply_of_im_neg _ hneg, coe_fold_of_im_nonpos hneg.le, map_ofNat]
  · rw [schwarzDouble_symm]
    rcases le_or_gt 0 z.im with hnn | hneg
    · simp [schwarzDouble_apply_of_im_nonneg _ hnn, coe_fold_of_im_nonneg hnn]
    · simp [schwarzDouble_apply_of_im_neg _ hneg, coe_fold_of_im_nonpos hneg.le, map_ofNat]

/-- The piecewise map that is `z` on the closed upper half-plane and `-conj (conj z) = -z` on the
lower half-plane is not complex differentiable at any real point `x`: its imaginary part along the
vertical line through `x` is `t ↦ |t|`. This is what the lower-half formula `conj (e (conj z))` of
`schwarzDouble` gives for the identity `e` if the outer `conj` is replaced by `z ↦ -conj z`. -/
theorem not_differentiableAt_negConj_glue (x : ℝ) :
    ¬ DifferentiableAt ℂ (fun z : ℂ ↦ if 0 ≤ z.im then z else -conj (conj z)) x := by
  intro hd
  have hline : DifferentiableAt ℝ (fun t : ℝ ↦ (x : ℂ) + t * I) 0 := by fun_prop
  have hx : (fun t : ℝ ↦ (x : ℂ) + t * I) 0 = x := by simp
  rw [← hx] at hd
  have hcomp := Complex.imCLM.differentiableAt.comp _ ((hd.restrictScalars ℝ).comp (0 : ℝ) hline)
  refine not_differentiableAt_abs_zero (hcomp.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun t ↦ ?_))
  rcases le_or_gt 0 t with ht | ht
  · simp [ht, abs_of_nonneg ht]
  · simp [ht.not_ge, abs_of_neg ht]

end ClosedUpperHalfPlane

end TauCeti
