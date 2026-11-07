/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.ContMDiff.Atlas
public import Mathlib.Geometry.Manifold.MFDeriv.Atlas
public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Trivialization
public import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import TauCeti.Geometry.Manifold.MFDeriv.Chart.Basic
import TauCeti.Geometry.Manifold.VectorBundle.Tangent.Basic
import TauCeti.Topology.VectorBundle.Coordinates

/-!
# Finite almost complex structures in charts and reconstruction

Let `J` be a finite-regularity almost complex structure on a smooth manifold `M` modelled on `E`.
Read in the
trivialization of the tangent bundle at `x`, along the inverse of the extended chart at `x`, the
structure becomes a map `E → (E →L[ℝ] E)`. It squares to `-1` on the chart target and equals
`J x` at the chart point. For smooth structures the coordinate field is differentiable there,
and its derivative at the chart point anticommutes with `J x`.

The finite field is C^n on the full extended target, with ordinary pointwise C^n regularity in
boundaryless models. `ContMDiffAlmostComplexStructure.chartEquiv` reconstructs an actual structure
on the intrinsic open chart source from a C^n model-endomorphism field on the open target in H.
For models with corners that target need not be open in E. Both reconstruction round trips are
part of the equivalence; native tangent-frame transitions give coordinate conjugation.

## Main declarations

* `ContMDiffAlmostComplexStructure.inChart`, `contDiffOn_inChart`: the full finite coordinate field.
* `ContMDiffAlmostComplexStructure.chartEquiv`: chart-source reconstruction and both round trips.
* `ContMDiffAlmostComplexStructure.inChart_extChartAt_eq_conj`: derivative conjugation on overlaps.

* `TauCeti.SmoothAlmostComplexStructure.inChart`: the almost complex structure read in a chart.
* `TauCeti.SmoothAlmostComplexStructure.inChart_apply_eq_mfderiv`,
  `TauCeti.SmoothAlmostComplexStructure.inChart_extChartAt_apply_eq_mfderiv`: it is `J`
  conjugated by the derivatives of the chart and of its inverse.
* `TauCeti.SmoothAlmostComplexStructure.fderiv_extChartAt_comp_apply_eq_inChart`,
  `TauCeti.SmoothAlmostComplexStructure.fderiv_comp_extChartAt_symm_inChart_apply`: relations
  between derivatives of maps into and out of `M` involving `J` read in the chart.
* `TauCeti.SmoothAlmostComplexStructure.inChart_inChart`: it squares to `-1` on the chart target.
* `TauCeti.SmoothAlmostComplexStructure.inChart_extChartAt_self`: it is `J x` at the chart point.
* `TauCeti.SmoothAlmostComplexStructure.fderivWithin_inChart_apply_apply`: its derivative at the
  chart point anticommutes with `J x`.
-/

public section

noncomputable section

open Bundle Bundle.Trivialization
open scoped ContDiff Manifold Topology

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

namespace ContMDiffAlmostComplexStructure

variable {n m : ℕ∞} (J : ContMDiffAlmostComplexStructure I n M) (x : M)

/-- Read a finite-regularity structure through the inverse extended chart and its tangent frame.
The formula is total; the square and regularity assertions concern the actual chart target. -/
def inChart (z : E) : E →L[ℝ] E :=
  almostComplexCoordinates (trivializationAt E (TangentSpace I) x) J ((extChartAt I x).symm z)

/-- The finite chart field is the native Hom-bundle coordinate expression. -/
theorem inChart_def (z : E) :
    J.inChart x z = ContinuousLinearMap.inCoordinates E (TangentSpace I) E (TangentSpace I) x
      ((extChartAt I x).symm z) x ((extChartAt I x).symm z)
        (J.toEndomorphism ((extChartAt I x).symm z)) := by
  unfold inChart
  ext v
  rw [almostComplexCoordinates_apply]
  rfl

/-- The full coordinate field has the specified finite regularity on the full extended target.
For a model with corners this is regularity within that target, not a claim that it is open in E. -/
theorem contDiffOn_inChart : ContDiffOn ℝ n (J.inChart x) (extChartAt I x).target := by
  apply contMDiffOn_iff_contDiffOn.1
  exact (contMDiffOn_almostComplexCoordinates _ J).comp (contMDiffOn_extChartAt_symm x)
    fun _ hz ↦ TangentBundle.extChartAt_symm_mem_trivializationAt_baseSet hz

/-- On the actual chart target the model endomorphism squares to minus the identity. -/
theorem inChart_inChart {z : E} (hz : z ∈ (extChartAt I x).target) (v : E) :
    J.inChart x z (J.inChart x z v) = -v :=
  almostComplexCoordinates_apply_apply _ J
    (TangentBundle.extChartAt_symm_mem_trivializationAt_baseSet hz) v

/-- At the chart center the model field agrees with the original fibre endomorphism. -/
theorem inChart_extChartAt_self : J.inChart x (extChartAt I x x) = J.toEndomorphism x := by
  rw [inChart_def, extChartAt_to_inv]
  ext w
  simp only [ContinuousLinearMap.inCoordinates,
    TangentBundle.continuousLinearMapAt_trivializationAt (mem_chart_source H x),
    TangentBundle.symmL_trivializationAt (mem_chart_source H x), mfderiv_extChartAt_self,
    mfderivWithin_range_extChartAt_symm]
  -- Both chart derivatives are the identities on the native model tangent spaces.
  rfl

@[simp]
theorem inChart_ofLE (h : m ≤ n) : (J.ofLE h).inChart x = J.inChart x := by
  funext z
  simp [inChart]

@[simp]
theorem inChart_neg : (-J).inChart x = -J.inChart x := by
  funext z
  simp [inChart]

/-- At each point of a boundaryless chart target the coordinate field is an ordinary C^n map. -/
theorem contDiffAt_inChart [I.Boundaryless] {z : E} (hz : z ∈ (extChartAt I x).target) :
    ContDiffAt ℝ n (J.inChart x) z :=
  (J.contDiffOn_inChart x z hz).contDiffAt ((isOpen_extChartAt_target x).mem_nhds hz)

/-- Chart-coordinate fields are conjugated by the actual derivative of the chart transition.
`tangentCoordChange` is the native derivative within `range I` of the extended transition map. -/
theorem inChart_extChartAt_eq_conj {y : M} (hy : y ∈ (chartAt H x).source)
    {x' : M} (hy' : y ∈ (chartAt H x').source) :
    J.inChart x' (extChartAt I x' y) =
      (tangentCoordChange I x x' y).comp
        ((J.inChart x (extChartAt I x y)).comp (tangentCoordChange I x' x y)) := by
  have hchange {a b : M} (ha : y ∈ (chartAt H a).source) (hb : y ∈ (chartAt H b).source) :
      ((trivializationAt E (TangentSpace I) a).coordChangeL ℝ
        (trivializationAt E (TangentSpace I) b) y).toContinuousLinearMap =
          tangentCoordChange I a b y :=
    (tangentBundleCore I M).trivializationAt_coordChangeL ⟨ha, hb⟩
  unfold inChart
  rw [(extChartAt I x).left_inv (by simpa only [extChartAt_source] using hy),
    (extChartAt I x').left_inv (by simpa only [extChartAt_source] using hy')]
  have h := almostComplexCoordinates_eq_conj
    (trivializationAt E (TangentSpace I) x) (trivializationAt E (TangentSpace I) x') J
    (by simpa using hy) (by simpa using hy')
  rw [hchange hy hy', hchange hy' hy] at h
  exact h

/-- Exact reconstruction on an intrinsic open chart source from finite-regularity endomorphism
fields on its open target in H. For models with corners the target need not be open in E. -/
def chartEquiv (x : M) :
    ContMDiffAlmostComplexStructure I n
      (⟨(chartAt H x).source, (chartAt H x).open_source⟩ : TopologicalSpace.Opens M) ≃
      {A : ContMDiffMap I 𝓘(ℝ, E →L[ℝ] E)
        (⟨(chartAt H x).target, (chartAt H x).open_target⟩ : TopologicalSpace.Opens H)
        (E →L[ℝ] E) n // ∀ z v, A z (A z v) = -v} :=
  almostComplexEquiv
    (trivializationAt E (TangentSpace I :
      (⟨(chartAt H x).source, (chartAt H x).open_source⟩ : TopologicalSpace.Opens M) → Type _)
        (⟨x, mem_chart_source H x⟩ :
          (⟨(chartAt H x).source, (chartAt H x).open_source⟩ : TopologicalSpace.Opens M)))
    (TangentBundle.trivializationAt_chartSource_baseSet (I := I) x)
    ((chartAt H x).toDiffeomorphSourceTarget
      (IsManifold.chart_mem_maximalAtlas (I := I) (n := (n : ℕ∞ω)) x))

/-- Reconstruct on the intrinsic chart source directly from a normed-space field on the
extended target. Its finite regularity and square identity are required only on that target. -/
def ofChart (A : E → E →L[ℝ] E)
    (hA : ContDiffOn ℝ n A (extChartAt I x).target)
    (hAA : ∀ z ∈ (extChartAt I x).target, ∀ v, A z (A z v) = -v) :
    ContMDiffAlmostComplexStructure I n
      (⟨(chartAt H x).source, (chartAt H x).open_source⟩ : TopologicalSpace.Opens M) :=
  (chartEquiv (I := I) (n := n) x).symm
    ⟨⟨fun z ↦ A (I z.val), by
      have hOn : ContMDiffOn I 𝓘(ℝ, E →L[ℝ] E) n (fun z : H ↦ A (I z))
          (chartAt H x).target :=
        hA.contMDiffOn.comp I.contMDiff.contMDiffOn fun z hz ↦ by
          rw [extChartAt_target]
          exact ⟨by simpa only [Set.mem_preimage, I.left_inv] using hz, ⟨z, rfl⟩⟩
      intro z
      exact contMDiffAt_subtype_iff.2
        ((hOn z.val z.property).contMDiffAt ((chartAt H x).open_target.mem_nhds z.property))⟩,
      fun z v ↦ hAA (I z.val) (by
        rw [extChartAt_target]
        exact ⟨by simpa only [Set.mem_preimage, I.left_inv, TopologicalSpace.Opens.mem_mk]
          using z.property, ⟨z.val, rfl⟩⟩) v⟩

/-- Reading the reconstructed chart structure recovers the prescribed normed-space field. -/
@[simp]
theorem chartEquiv_ofChart (A : E → E →L[ℝ] E)
    (hA : ContDiffOn ℝ n A (extChartAt I x).target)
    (hAA : ∀ z ∈ (extChartAt I x).target, ∀ v, A z (A z v) = -v)
    (z : (⟨(chartAt H x).target, (chartAt H x).open_target⟩ : TopologicalSpace.Opens H)) :
    (chartEquiv (I := I) (n := n) x (ofChart x A hA hAA)).val z = A (I z.val) := by
  unfold ofChart
  rw [Equiv.apply_symm_apply]
  rfl

/-- The chart equivalence evaluates the coordinate field at the forward chart value. -/
theorem chartEquiv_apply
    (Jc : ContMDiffAlmostComplexStructure I n
      (⟨(chartAt H x).source, (chartAt H x).open_source⟩ : TopologicalSpace.Opens M))
    (y : (⟨(chartAt H x).source, (chartAt H x).open_source⟩ : TopologicalSpace.Opens M)) :
    (chartEquiv (I := I) (n := n) x Jc).val
      (⟨chartAt H x y, (chartAt H x).map_source y.property⟩ :
        (⟨(chartAt H x).target, (chartAt H x).open_target⟩ : TopologicalSpace.Opens H)) =
      almostComplexCoordinates
        (trivializationAt E (TangentSpace I)
          (⟨x, mem_chart_source H x⟩ :
            (⟨(chartAt H x).source, (chartAt H x).open_source⟩ : TopologicalSpace.Opens M)))
        Jc y := by
  let h := (chartAt H x).toDiffeomorphSourceTarget
    (IsManifold.chart_mem_maximalAtlas (I := I) (n := (n : ℕ∞ω)) x)
  have hy : h y = ⟨chartAt H x y, (chartAt H x).map_source y.property⟩ :=
    Subtype.ext ((chartAt H x).toDiffeomorphSourceTarget_apply_coe _ y)
  unfold chartEquiv
  rw [← hy, almostComplexEquiv_apply, h.symm_apply_apply]

/-- The inverse chart equivalence is inverse tangent-frame conjugation of the given field. -/
theorem chartEquiv_symm_apply
    (A : {A : ContMDiffMap I 𝓘(ℝ, E →L[ℝ] E)
      (⟨(chartAt H x).target, (chartAt H x).open_target⟩ : TopologicalSpace.Opens H)
      (E →L[ℝ] E) n // ∀ z v, A z (A z v) = -v})
    (y : (⟨(chartAt H x).source, (chartAt H x).open_source⟩ : TopologicalSpace.Opens M))
    (v : TangentSpace I y) :
    (chartEquiv (I := I) (n := n) x).symm A y v =
      (trivializationAt E (TangentSpace I)
        (⟨x, mem_chart_source H x⟩ :
          (⟨(chartAt H x).source, (chartAt H x).open_source⟩ : TopologicalSpace.Opens M))).symmL
        ℝ y (A.val ⟨chartAt H x y, (chartAt H x).map_source y.property⟩
          (continuousLinearMapAt ℝ
            (trivializationAt E (TangentSpace I)
              (⟨x, mem_chart_source H x⟩ :
                (⟨(chartAt H x).source, (chartAt H x).open_source⟩ : TopologicalSpace.Opens M)))
            y v)) := by
  let h := (chartAt H x).toDiffeomorphSourceTarget
    (IsManifold.chart_mem_maximalAtlas (I := I) (n := (n : ℕ∞ω)) x)
  have hy : h y = ⟨chartAt H x y, (chartAt H x).map_source y.property⟩ :=
    Subtype.ext ((chartAt H x).toDiffeomorphSourceTarget_apply_coe _ y)
  unfold chartEquiv
  rw [almostComplexEquiv_symm_apply, hy]

/-- The chart-coordinate equivalence preserves the underlying field when regularity is lowered. -/
theorem chartEquiv_ofLE
    (Jc : ContMDiffAlmostComplexStructure I n
      (⟨(chartAt H x).source, (chartAt H x).open_source⟩ : TopologicalSpace.Opens M))
    (h : m ≤ n) :
    ⇑(chartEquiv (I := I) (n := m) x (Jc.ofLE h)).val =
      ⇑(chartEquiv (I := I) (n := n) x Jc).val := by
  funext z
  unfold chartEquiv
  rw [almostComplexEquiv_apply, almostComplexEquiv_apply]
  simp only [almostComplexCoordinates_ofLE]
  congr 1
  apply Subtype.ext
  rw [OpenPartialHomeomorph.toDiffeomorphSourceTarget_symm_apply_coe,
    OpenPartialHomeomorph.toDiffeomorphSourceTarget_symm_apply_coe]

/-- Negating a structure negates its chart-coordinate field. -/
theorem chartEquiv_neg
    (Jc : ContMDiffAlmostComplexStructure I n
      (⟨(chartAt H x).source, (chartAt H x).open_source⟩ : TopologicalSpace.Opens M)) :
    ⇑(chartEquiv (I := I) (n := n) x (-Jc)).val =
      fun z ↦ -(chartEquiv (I := I) (n := n) x Jc).val z := by
  funext z
  unfold chartEquiv
  rw [almostComplexEquiv_apply, almostComplexEquiv_apply]
  exact congrFun (almostComplexCoordinates_neg _ Jc) _

end ContMDiffAlmostComplexStructure

namespace SmoothAlmostComplexStructure

variable (J : SmoothAlmostComplexStructure I M) (x : M)

/-- The almost complex structure read in the trivialization of the tangent bundle at `x`, along
the inverse of the extended chart at `x`. -/
def inChart (z : E) : E →L[ℝ] E :=
  ContinuousLinearMap.inCoordinates E (TangentSpace I) E (TangentSpace I) x
    ((extChartAt I x).symm z) x ((extChartAt I x).symm z)
      (J.toEndomorphism ((extChartAt I x).symm z))

/-- The defining formula of `inChart`: `J` at `(extChartAt I x).symm z`, written in the
coordinates of the trivialization of the tangent bundle at `x`. -/
theorem inChart_def (z : E) :
    J.inChart x z = ContinuousLinearMap.inCoordinates E (TangentSpace I) E (TangentSpace I) x
      ((extChartAt I x).symm z) x ((extChartAt I x).symm z)
        (J.toEndomorphism ((extChartAt I x).symm z)) :=
  (rfl)

/-- Reading a smooth structure in a chart agrees with every finite-regularity specialization. -/
@[simp]
theorem toContMDiff_inChart (n : ℕ∞) : (J.toContMDiff n).inChart x = J.inChart x := by
  funext z
  rw [ContMDiffAlmostComplexStructure.inChart_def, toContMDiff_toEndomorphism_apply, inChart_def]

/-- The smooth coordinate field is smooth on its full chart target. -/
theorem contDiffOn_inChart : ContDiffOn ℝ ∞ (J.inChart x) (extChartAt I x).target := by
  simpa only [toContMDiff_inChart] using (J.toContMDiff ⊤).contDiffOn_inChart x

/-- At the image of a point `y` of the chart at `x`, the almost complex structure read in the chart
is `J y` in the coordinates of the trivialization of the tangent bundle at `x`. -/
theorem inChart_extChartAt_apply {y : M} (hy : y ∈ (extChartAt I x).source) (u : E) :
    J.inChart x (extChartAt I x y) u =
      (trivializationAt E (TangentSpace I) x
        ⟨y, J y ((trivializationAt E (TangentSpace I) x).symm y u)⟩).2 := by
  have hy' : y ∈ (trivializationAt E (TangentSpace I) x).baseSet := by
    rwa [TangentBundle.trivializationAt_baseSet, ← extChartAt_source I]
  simp only [inChart, ContinuousLinearMap.inCoordinates, ContinuousLinearMap.comp_apply]
  rw [(extChartAt I x).left_inv hy,
    Trivialization.continuousLinearMapAt_apply_of_mem (R := ℝ) _ hy',
    Trivialization.symmL_apply _ hy']

/-- On the chart target, the almost complex structure read in the chart is `J` at the
corresponding point, conjugated by the derivatives of the chart and of its inverse. -/
theorem inChart_apply_eq_mfderiv {z : E} (hz : z ∈ (extChartAt I x).target) (w : E) :
    J.inChart x z w =
      mfderiv I 𝓘(ℝ, E) (extChartAt I x) ((extChartAt I x).symm z)
        (J ((extChartAt I x).symm z)
          (mfderivWithin 𝓘(ℝ, E) I (extChartAt I x).symm (Set.range I) z w)) := by
  have hz' : (extChartAt I x).symm z ∈ (chartAt H x).source := by
    rw [← extChartAt_source I]
    exact (extChartAt I x).map_target hz
  rw [inChart_def, ContinuousLinearMap.inCoordinates,
    TangentBundle.continuousLinearMapAt_trivializationAt hz',
    TangentBundle.symmL_trivializationAt hz', (extChartAt I x).right_inv hz]
  rfl

/-- At the image of a point `y` of the chart at `x`, the almost complex structure read in the chart
is `J y`, conjugated by the derivatives of the chart at `y` and of its inverse. -/
theorem inChart_extChartAt_apply_eq_mfderiv {y : M} (hy : y ∈ (extChartAt I x).source) (w : E) :
    J.inChart x (extChartAt I x y) w =
      mfderiv I 𝓘(ℝ, E) (extChartAt I x) y
        (J y (mfderivWithin 𝓘(ℝ, E) I (extChartAt I x).symm (Set.range I)
          (extChartAt I x y) w)) := by
  have hy' : y ∈ (chartAt H x).source := by rwa [← extChartAt_source I]
  rw [inChart_def, (extChartAt I x).left_inv hy, ContinuousLinearMap.inCoordinates,
    TangentBundle.continuousLinearMapAt_trivializationAt hy',
    TangentBundle.symmL_trivializationAt hy']
  rfl

/-- Read in the extended chart `φ` at `x`, a relation `du(a) = J du(b)` between derivatives at `w`
of a map `u` from a normed space becomes `d(φ ∘ u)(a) = J_φ d(φ ∘ u)(b)`, for the structure
`J_φ = J.inChart x` read in the chart. -/
theorem fderiv_extChartAt_comp_apply_eq_inChart {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {u : F → M} {w : F} (hu : MDifferentiableAt 𝓘(ℝ, F) I u w)
    (hw : u w ∈ (extChartAt I x).source) {a b : F}
    (h : mfderiv 𝓘(ℝ, F) I u w a = J (u w) (mfderiv 𝓘(ℝ, F) I u w b)) :
    fderiv ℝ (extChartAt I x ∘ u) w a =
      J.inChart x ((extChartAt I x ∘ u) w) (fderiv ℝ (extChartAt I x ∘ u) w b) := by
  have hinv := congr($(mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt' hw)
    (mfderiv 𝓘(ℝ, F) I u w b))
  rw [hu.fderiv_extChartAt_comp_apply hw, hu.fderiv_extChartAt_comp_apply hw,
    Function.comp_apply, h]
  exact (congrArg _ (congrArg _ hinv)).symm.trans
    (J.inChart_extChartAt_apply_eq_mfderiv x hw _).symm

/-- On the chart target, the derivative of the coordinate expression `f ∘ φ⁻¹` of a map `f` into a
normed space, applied after the structure `J.inChart x` read in the chart `φ` at `x`, is the
derivative of `f` applied after `J`. -/
theorem fderiv_comp_extChartAt_symm_inChart_apply {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {f : M → F} {z : E} (hz : z ∈ (extChartAt I x).target)
    (hf : DifferentiableAt ℝ (f ∘ (extChartAt I x).symm) z) (w : E) :
    fderiv ℝ (f ∘ (extChartAt I x).symm) z (J.inChart x z w) =
      mvfderiv I f ((extChartAt I x).symm z)
        (J ((extChartAt I x).symm z)
          (mfderivWithin 𝓘(ℝ, E) I (extChartAt I x).symm (Set.range I) z w)) := by
  have hy := (extChartAt I x).map_target hz
  have h := congr($(mfderiv_eq_fderiv_comp_mfderiv_extChartAt (f := f) hy
    (by rwa [(extChartAt I x).right_inv hz]))
    (J ((extChartAt I x).symm z)
      (mfderivWithin 𝓘(ℝ, E) I (extChartAt I x).symm (Set.range I) z w)))
  rw [(extChartAt I x).right_inv hz] at h
  rw [J.inChart_apply_eq_mfderiv x hz]
  -- `h` is the chain rule, up to the identifications of tangent spaces of `E` and `F`.
  exact h.symm

/-- In the chart, the almost complex structure still squares to `-1`. -/
theorem inChart_inChart {z : E} (hz : z ∈ (extChartAt I x).target) (w : E) :
    J.inChart x z (J.inChart x z w) = -w := by
  simpa only [toContMDiff_inChart] using (J.toContMDiff ⊤).inChart_inChart x hz w

/-- At the chart point, the almost complex structure read in the chart is `J x`. -/
theorem inChart_extChartAt_self : J.inChart x (extChartAt I x x) = J.toEndomorphism x := by
  simpa only [toContMDiff_inChart, toContMDiff_toEndomorphism_apply] using
    (J.toContMDiff ⊤).inChart_extChartAt_self x

/-- The almost complex structure read in the chart at `x` is differentiable at the chart point. -/
theorem differentiableWithinAt_inChart :
    DifferentiableWithinAt ℝ (J.inChart x) (Set.range I) (extChartAt I x x) := by
  have h := ((contMDiffAt_hom_bundle _).1 (J.toEndomorphism.contMDiff x)).2
  have h' := h.comp_contMDiffWithinAt_of_eq (contMDiffWithinAt_extChartAt_symm_range_self x)
    (extChartAt_to_inv x)
  exact (contMDiffWithinAt_iff_contDiffWithinAt.1 h').differentiableWithinAt (by simp)

/-- Differentiating `J² = -1` in the chart at `x`: the derivative of the almost complex structure
read in the chart anticommutes with its value at the chart point. -/
theorem fderivWithin_inChart_apply_apply (v w : E) :
    fderivWithin ℝ (J.inChart x) (Set.range I) (extChartAt I x x) v
        (J.inChart x (extChartAt I x x) w) =
      -J.inChart x (extChartAt I x x)
        (fderivWithin ℝ (J.inChart x) (Set.range I) (extChartAt I x x) v w) := by
  have hd := (J.differentiableWithinAt_inChart x).hasFDerivWithinAt
  have heq : (fun z ↦ J.inChart x z ∘L J.inChart x z) =ᶠ[𝓝[Set.range I] extChartAt I x x]
      fun _ ↦ -ContinuousLinearMap.id ℝ E := by
    filter_upwards [extChartAt_target_mem_nhdsWithin x] with z hz
    ext w
    simp [J.inChart_inChart x hz]
  have h := (I.uniqueDiffOn.uniqueDiffWithinAt (Set.mem_range_self _)).eq
    ((hd.clm_comp hd).congr_of_eventuallyEq heq.symm
      (heq.symm.eq_of_nhdsWithin (Set.mem_range_self _))) (hasFDerivWithinAt_const _ _ _)
  have hvw := congrArg (fun L ↦ L v w) h
  simp only [add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.compL_apply,
    zero_apply] at hvw
  exact eq_neg_of_add_eq_zero_right hvw

end SmoothAlmostComplexStructure

end TauCeti

end
