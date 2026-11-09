/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Complex.ClosedUpperHalfPlane
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Geometry.Manifold.ContMDiff.Atlas

/-!
# The bordered holomorphic groupoid

`TauCeti.borderedHolomorphicGroupoid` is the structure groupoid on the closed upper half-plane
whose members are the open partial homeomorphisms that are smooth up to the real boundary and
complex differentiable at the points of positive imaginary part. A charted space modelled on the
closed upper half-plane with this groupoid is a Riemann surface with boundary.

The groupoid is contained in the smooth groupoid of `closedUpperHalfPlaneModel`, so such a space
is a smooth manifold with boundary. After reading the charts in Mathlib's native half-space
coordinates through `ClosedUpperHalfPlane.euclideanHalfSpaceHomeomorph`, it is also a smooth
manifold modelled on `𝓡∂ 2`. Members send real boundary points to real boundary points.

The translation `z ↦ z + 1` and the dilation `z ↦ 2z` are members. The reflection `z ↦ -conj z`
preserves the closed upper half-plane and the real axis but is not a member, since it is
antiholomorphic. The translation `z ↦ z + I` is not even the restriction of an open partial
homeomorphism defined near `0`, since its image of a relatively open neighbourhood of `0` misses
the points of imaginary part less than one.

## Main definitions

* `TauCeti.borderedHolomorphicGroupoid`: the bordered holomorphic groupoid.
* `TauCeti.ClosedUpperHalfPlane.euclideanHalfSpaceChartedSpace`: the charts of a space modelled
  on the closed upper half-plane, read in `EuclideanHalfSpace 2`.

## Main results

* `TauCeti.mem_borderedHolomorphicGroupoid_iff`: membership is smoothness up to the boundary
  together with complex differentiability of the map and of its inverse in the interior.
* `TauCeti.borderedHolomorphicGroupoid_le_contDiffGroupoid`: members are smooth.
* `TauCeti.ClosedUpperHalfPlane.isManifold_euclideanHalfSpace`: a `C^n` manifold modelled on the
  closed upper half-plane is a `C^n` manifold modelled on `𝓡∂ 2`.
* `TauCeti.ClosedUpperHalfPlane.im_eq_zero_iff_of_mem_borderedHolomorphicGroupoid`: members
  preserve the real axis in both directions.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications **52**, 2012, Section 2.4 and Appendix C, for Riemann surfaces with
  boundary and their holomorphic atlases.
-/

public section

noncomputable section

open Set Complex Filter
open scoped Manifold ContDiff Topology ComplexConjugate

namespace TauCeti

/-- At a point of nonnegative imaginary part, the model inverse is the inverse of the inclusion. -/
theorem coe_closedUpperHalfPlaneModel_symm_of_im_nonneg {z : ℂ} (hz : 0 ≤ z.im) :
    (closedUpperHalfPlaneModel.symm z : ℂ) = z := by
  rw [closedUpperHalfPlaneModel_symm_apply, max_eq_left hz, re_add_im]

/-- The model inverse is a left inverse of the inclusion. -/
@[simp]
theorem closedUpperHalfPlaneModel_symm_coe (z : ClosedUpperHalfPlane) :
    closedUpperHalfPlaneModel.symm (z : ℂ) = z :=
  Subtype.ext (coe_closedUpperHalfPlaneModel_symm_of_im_nonneg z.property)

/-- Near a point of positive imaginary part, the model inverse is the inverse of the inclusion. -/
theorem eventually_coe_closedUpperHalfPlaneModel_symm {z : ℂ} (hz : 0 < z.im) :
    ∀ᶠ w in 𝓝 z, (closedUpperHalfPlaneModel.symm w : ℂ) = w :=
  Filter.eventually_of_mem ((isOpen_lt continuous_const continuous_im).mem_nhds hz) fun _ hw ↦
    coe_closedUpperHalfPlaneModel_symm_of_im_nonneg (le_of_lt hw)

namespace ClosedUpperHalfPlane

/-- The maps of the closed upper half-plane that, at each point of positive imaginary part of a
set, take a value of positive imaginary part and are complex differentiable in the ambient
coordinate. Requiring interior points to go to interior points makes the property stable under
composition. For open partial homeomorphisms that are smooth up to the boundary it is automatic,
see `TauCeti.mem_borderedHolomorphicGroupoid_iff`. -/
def interiorHolomorphicPregroupoid : Pregroupoid ClosedUpperHalfPlane where
  property f u := ∀ x ∈ u, 0 < (x : ℂ).im →
    0 < (f x : ℂ).im ∧
      DifferentiableAt ℂ (closedUpperHalfPlaneModel ∘ f ∘ closedUpperHalfPlaneModel.symm) x
  comp {f g u v} hf hg _ _ _ x hx hxim := by
    obtain ⟨hfx, hfd⟩ := hf x hx.1 hxim
    obtain ⟨hgx, hgd⟩ := hg (f x) hx.2 hfx
    refine ⟨hgx, ?_⟩
    have hcomp : closedUpperHalfPlaneModel ∘ (g ∘ f) ∘ closedUpperHalfPlaneModel.symm =
        (closedUpperHalfPlaneModel ∘ g ∘ closedUpperHalfPlaneModel.symm) ∘
          (closedUpperHalfPlaneModel ∘ f ∘ closedUpperHalfPlaneModel.symm) := by
      ext1 z
      simp
    rw [hcomp]
    exact DifferentiableAt.comp (x : ℂ) (by simpa using hgd) hfd
  id_mem x _ hx := ⟨hx, differentiableAt_id.congr_of_eventuallyEq
    ((eventually_coe_closedUpperHalfPlaneModel_symm hx).mono fun _ hw ↦ by simpa using hw)⟩
  locality _ h x hx hxim := by
    obtain ⟨v, -, hxv, hv⟩ := h x hx
    exact hv x ⟨hx, hxv⟩ hxim
  congr {f g u} hu hfg hf x hx hxim := by
    obtain ⟨hfx, hfd⟩ := hf x hx hxim
    refine ⟨hfg x hx ▸ hfx, hfd.congr_of_eventuallyEq ?_⟩
    have hmem : ∀ᶠ w in 𝓝 (x : ℂ), closedUpperHalfPlaneModel.symm w ∈ u :=
      closedUpperHalfPlaneModel.continuous_symm.continuousAt.preimage_mem_nhds
        (by simpa using hu.mem_nhds hx)
    exact hmem.mono fun w hw ↦ by simp [hfg _ hw]

end ClosedUpperHalfPlane

/-- The bordered holomorphic groupoid on the closed upper half-plane: open partial homeomorphisms
that are smooth up to the real boundary and complex differentiable, with complex differentiable
inverse, at the points of positive imaginary part. -/
def borderedHolomorphicGroupoid : StructureGroupoid ClosedUpperHalfPlane :=
  contDiffGroupoid ∞ closedUpperHalfPlaneModel ⊓
    ClosedUpperHalfPlane.interiorHolomorphicPregroupoid.groupoid

/-- Members of the bordered holomorphic groupoid are smooth up to the boundary. -/
theorem borderedHolomorphicGroupoid_le_contDiffGroupoid :
    borderedHolomorphicGroupoid ≤ contDiffGroupoid ∞ closedUpperHalfPlaneModel :=
  inf_le_left

/-- For a map that is smooth up to the boundary, the interior condition reduces to complex
differentiability on the interior part of the source. -/
private theorem interiorHolomorphicPregroupoid_property_iff
    {e : OpenPartialHomeomorph ClosedUpperHalfPlane ClosedUpperHalfPlane}
    (he : e ∈ contDiffGroupoid ∞ closedUpperHalfPlaneModel) :
    ClosedUpperHalfPlane.interiorHolomorphicPregroupoid.property e e.source ↔
      DifferentiableOn ℂ (closedUpperHalfPlaneModel ∘ e ∘ closedUpperHalfPlaneModel.symm)
        (closedUpperHalfPlaneModel.symm ⁻¹' e.source ∩ {z | 0 < z.im}) := by
  constructor
  · intro h z hz
    have hz' : (closedUpperHalfPlaneModel.symm z : ℂ) = z :=
      coe_closedUpperHalfPlaneModel_symm_of_im_nonneg (le_of_lt hz.2)
    have hd := (h _ hz.1 (by rw [hz']; exact hz.2)).2
    rw [hz'] at hd
    exact hd.differentiableWithinAt
  · intro h x hx hxim
    refine ⟨(ClosedUpperHalfPlane.im_pos_iff_of_mem_contDiffGroupoid he (by simp) hx).1 hxim,
      h.differentiableAt ?_⟩
    exact ((e.open_source.preimage closedUpperHalfPlaneModel.continuous_symm).inter
      (isOpen_lt continuous_const continuous_im)).mem_nhds ⟨by simpa using hx, hxim⟩

/-- An open partial homeomorphism of the closed upper half-plane belongs to the bordered
holomorphic groupoid exactly when it is smooth up to the boundary and both it and its inverse are
complex differentiable at the points of positive imaginary part. -/
theorem mem_borderedHolomorphicGroupoid_iff
    {e : OpenPartialHomeomorph ClosedUpperHalfPlane ClosedUpperHalfPlane} :
    e ∈ borderedHolomorphicGroupoid ↔ e ∈ contDiffGroupoid ∞ closedUpperHalfPlaneModel ∧
      DifferentiableOn ℂ (closedUpperHalfPlaneModel ∘ e ∘ closedUpperHalfPlaneModel.symm)
        (closedUpperHalfPlaneModel.symm ⁻¹' e.source ∩ {z | 0 < z.im}) ∧
      DifferentiableOn ℂ (closedUpperHalfPlaneModel ∘ e.symm ∘ closedUpperHalfPlaneModel.symm)
        (closedUpperHalfPlaneModel.symm ⁻¹' e.target ∩ {z | 0 < z.im}) := by
  constructor
  · rintro ⟨hc, h₁, h₂⟩
    exact ⟨hc, (interiorHolomorphicPregroupoid_property_iff hc).1 h₁,
      (interiorHolomorphicPregroupoid_property_iff ((contDiffGroupoid _ _).symm hc)).1 h₂⟩
  · rintro ⟨hc, h₁, h₂⟩
    exact ⟨hc, (interiorHolomorphicPregroupoid_property_iff hc).2 h₁,
      (interiorHolomorphicPregroupoid_property_iff ((contDiffGroupoid _ _).symm hc)).2 h₂⟩

/-- A charted space with bordered holomorphic transition maps is a smooth manifold modelled on the
closed upper half-plane. -/
instance isManifold_of_hasGroupoid_borderedHolomorphicGroupoid (M : Type*) [TopologicalSpace M]
    [ChartedSpace ClosedUpperHalfPlane M] [HasGroupoid M borderedHolomorphicGroupoid] :
    IsManifold closedUpperHalfPlaneModel ∞ M :=
  haveI := hasGroupoid_of_le ‹HasGroupoid M borderedHolomorphicGroupoid›
    borderedHolomorphicGroupoid_le_contDiffGroupoid
  IsManifold.mk' _ _ _

namespace ClosedUpperHalfPlane

/-- Members of the bordered holomorphic groupoid send real boundary points to real boundary points,
in both directions. -/
theorem im_eq_zero_iff_of_mem_borderedHolomorphicGroupoid
    {e : OpenPartialHomeomorph ClosedUpperHalfPlane ClosedUpperHalfPlane}
    (he : e ∈ borderedHolomorphicGroupoid) {z : ClosedUpperHalfPlane} (hz : z ∈ e.source) :
    (z : ℂ).im = 0 ↔ (e z : ℂ).im = 0 :=
  im_eq_zero_iff_of_mem_contDiffGroupoid (borderedHolomorphicGroupoid_le_contDiffGroupoid he)
    (by simp) hz

/-- Members of the bordered holomorphic groupoid send points of positive imaginary part to points
of positive imaginary part, in both directions. -/
theorem im_pos_iff_of_mem_borderedHolomorphicGroupoid
    {e : OpenPartialHomeomorph ClosedUpperHalfPlane ClosedUpperHalfPlane}
    (he : e ∈ borderedHolomorphicGroupoid) {z : ClosedUpperHalfPlane} (hz : z ∈ e.source) :
    0 < (z : ℂ).im ↔ 0 < (e z : ℂ).im :=
  im_pos_iff_of_mem_contDiffGroupoid (borderedHolomorphicGroupoid_le_contDiffGroupoid he)
    (by simp) hz

/-! ### Native half-space coordinates -/

/-- Conjugating a `C^n` chart change of the closed upper half-plane by the native coordinate
comparison gives a `C^n` chart change of `EuclideanHalfSpace 2`. -/
theorem symm_trans_trans_mem_contDiffGroupoid_euclideanHalfSpace {n : ℕ∞ω}
    {e : OpenPartialHomeomorph ClosedUpperHalfPlane ClosedUpperHalfPlane}
    (he : e ∈ contDiffGroupoid n closedUpperHalfPlaneModel) :
    euclideanHalfSpaceHomeomorph.toOpenPartialHomeomorph.symm ≫ₕ
        (e ≫ₕ euclideanHalfSpaceHomeomorph.toOpenPartialHomeomorph) ∈
      contDiffGroupoid n (𝓡∂ 2) := by
  set D := euclideanHalfSpaceDiffeomorph n
  have hD : ⇑D = ⇑euclideanHalfSpaceHomeomorph := funext fun z ↦ Subtype.ext (by simp [D])
  have hDs : ⇑D.symm = ⇑euclideanHalfSpaceHomeomorph.symm :=
    funext fun v ↦ Subtype.ext (by simp [D])
  have he₁ := contMDiffOn_of_mem_contDiffGroupoid he
  have he₂ := contMDiffOn_of_mem_contDiffGroupoid ((contDiffGroupoid n _).symm he)
  have hrefl : OpenPartialHomeomorph.refl (EuclideanHalfSpace 2) ∈
      IsManifold.maximalAtlas (𝓡∂ 2) n (EuclideanHalfSpace 2) :=
    StructureGroupoid.subset_maximalAtlas _ (chartedSpaceSelf_atlas.mpr rfl)
  have h := symm_trans_trans_mem_contDiffGroupoid_of_contMDiffOn hrefl hrefl
    (f := euclideanHalfSpaceHomeomorph.toOpenPartialHomeomorph.symm ≫ₕ
        (e ≫ₕ euclideanHalfSpaceHomeomorph.toOpenPartialHomeomorph)) ?_ ?_
  · simpa only [OpenPartialHomeomorph.refl_symm, OpenPartialHomeomorph.refl_trans,
      OpenPartialHomeomorph.trans_refl] using h
  · have hf : ⇑(euclideanHalfSpaceHomeomorph.toOpenPartialHomeomorph.symm ≫ₕ
        (e ≫ₕ euclideanHalfSpaceHomeomorph.toOpenPartialHomeomorph)) = D ∘ e ∘ D.symm := by
      rw [hD, hDs]
      rfl
    rw [hf]
    exact D.contMDiff.comp_contMDiffOn (he₁.comp D.symm.contMDiff.contMDiffOn fun v hv ↦ by
      simpa [hDs, mfld_simps] using hv)
  · have hf : ⇑(euclideanHalfSpaceHomeomorph.toOpenPartialHomeomorph.symm ≫ₕ
        (e ≫ₕ euclideanHalfSpaceHomeomorph.toOpenPartialHomeomorph)).symm =
          D ∘ e.symm ∘ D.symm := by
      rw [hD, hDs]
      rfl
    rw [hf]
    exact D.contMDiff.comp_contMDiffOn (he₂.comp D.symm.contMDiff.contMDiffOn fun v hv ↦ by
      simpa [hDs, mfld_simps] using hv)

/-- The charts of a space modelled on the closed upper half-plane, read in Mathlib's native
half-space coordinates `s + it ↦ (t, s)`. -/
@[expose, instance_reducible]
def euclideanHalfSpaceChartedSpace (M : Type*) [TopologicalSpace M]
    [ChartedSpace ClosedUpperHalfPlane M] : ChartedSpace (EuclideanHalfSpace 2) M where
  atlas := (· ≫ₕ euclideanHalfSpaceHomeomorph.toOpenPartialHomeomorph) ''
    atlas ClosedUpperHalfPlane M
  chartAt x := chartAt ClosedUpperHalfPlane x ≫ₕ
    euclideanHalfSpaceHomeomorph.toOpenPartialHomeomorph
  mem_chart_source x := by simp
  chart_mem_atlas x := mem_image_of_mem _ (chart_mem_atlas _ x)

/-- The preferred native chart is the preferred chart followed by the coordinate comparison. -/
theorem euclideanHalfSpaceChartedSpace_chartAt (M : Type*) [TopologicalSpace M]
    [ChartedSpace ClosedUpperHalfPlane M] (x : M) :
    (letI := euclideanHalfSpaceChartedSpace M; chartAt (EuclideanHalfSpace 2) x) =
      chartAt ClosedUpperHalfPlane x ≫ₕ euclideanHalfSpaceHomeomorph.toOpenPartialHomeomorph :=
  rfl

/-- A `C^n` manifold modelled on the closed upper half-plane is a `C^n` manifold modelled on
`𝓡∂ 2` for its charts read in native half-space coordinates. In particular, by
`TauCeti.isManifold_of_hasGroupoid_borderedHolomorphicGroupoid`, a Riemann surface with boundary
is a smooth manifold with boundary in Mathlib's sense. -/
theorem isManifold_euclideanHalfSpace {n : ℕ∞ω} (M : Type*) [TopologicalSpace M]
    [ChartedSpace ClosedUpperHalfPlane M] [IsManifold closedUpperHalfPlaneModel n M] :
    letI := euclideanHalfSpaceChartedSpace M
    IsManifold (𝓡∂ 2) n M := by
  let := euclideanHalfSpaceChartedSpace M
  refine { compatible := ?_ }
  rintro _ _ ⟨c, hc, rfl⟩ ⟨c', hc', rfl⟩
  rw [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm, OpenPartialHomeomorph.trans_assoc,
    ← OpenPartialHomeomorph.trans_assoc c.symm]
  exact symm_trans_trans_mem_contDiffGroupoid_euclideanHalfSpace
    (HasGroupoid.compatible hc hc')

/-! ### Examples -/

/-- A homeomorphism of the closed upper half-plane given in the ambient coordinate by an entire
function, with inverse also given by an entire function, belongs to the bordered holomorphic
groupoid. -/
theorem toOpenPartialHomeomorph_mem_borderedHolomorphicGroupoid
    {h : ClosedUpperHalfPlane ≃ₜ ClosedUpperHalfPlane} {F G : ℂ → ℂ}
    (hF : Differentiable ℂ F) (hG : Differentiable ℂ G)
    (hhF : ∀ z, (h z : ℂ) = F z) (hhG : ∀ z, (h.symm z : ℂ) = G z) :
    h.toOpenPartialHomeomorph ∈ borderedHolomorphicGroupoid := by
  have hcoord : ∀ {k : ClosedUpperHalfPlane → ClosedUpperHalfPlane} {K : ℂ → ℂ},
      (∀ z, (k z : ℂ) = K z) → ∀ {z : ℂ}, 0 ≤ z.im →
        (closedUpperHalfPlaneModel ∘ k ∘ closedUpperHalfPlaneModel.symm) z = K z := by
    intro k K hk z hz
    simp only [Function.comp_apply, closedUpperHalfPlaneModel_apply, hk]
    rw [coe_closedUpperHalfPlaneModel_symm_of_im_nonneg hz]
  have hsmooth : ∀ {k : ClosedUpperHalfPlane → ClosedUpperHalfPlane} {K : ℂ → ℂ},
      Differentiable ℂ K → (∀ z, (k z : ℂ) = K z) →
        ContDiffOn ℝ ∞ (closedUpperHalfPlaneModel ∘ k ∘ closedUpperHalfPlaneModel.symm)
          (closedUpperHalfPlaneModel.symm ⁻¹' univ ∩ range closedUpperHalfPlaneModel) := by
    intro k K hK hk
    refine ((hK.contDiff (n := ∞)).restrict_scalars ℝ).contDiffOn.congr fun z hz ↦ ?_
    exact hcoord hk (by simpa using hz.2)
  have hholo : ∀ {k : ClosedUpperHalfPlane → ClosedUpperHalfPlane} {K : ℂ → ℂ},
      Differentiable ℂ K → (∀ z, (k z : ℂ) = K z) →
        DifferentiableOn ℂ (closedUpperHalfPlaneModel ∘ k ∘ closedUpperHalfPlaneModel.symm)
          (closedUpperHalfPlaneModel.symm ⁻¹' univ ∩ {z | 0 < z.im}) := by
    intro k K hK hk
    exact hK.differentiableOn.congr fun z hz ↦ hcoord hk (le_of_lt hz.2)
  refine mem_borderedHolomorphicGroupoid_iff.2 ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · simpa [contDiffPregroupoid] using hsmooth hF hhF
  · simpa [contDiffPregroupoid] using hsmooth hG hhG
  · simpa using hholo hF hhF
  · simpa using hholo hG hhG

/-- Translation by one, as a homeomorphism of the closed upper half-plane. -/
def addOne : ClosedUpperHalfPlane ≃ₜ ClosedUpperHalfPlane :=
  (Homeomorph.addRight (1 : ℂ)).subtype fun z ↦ by simp

@[simp]
theorem coe_addOne (z : ClosedUpperHalfPlane) : (addOne z : ℂ) = z + 1 := by
  rw [addOne]
  rfl

@[simp]
theorem coe_addOne_symm (z : ClosedUpperHalfPlane) : (addOne.symm z : ℂ) = z - 1 := by
  have h := congrArg Subtype.val (addOne.apply_symm_apply z)
  rw [coe_addOne] at h
  rw [← h, add_sub_cancel_right]

/-- Translation by one is a bordered holomorphic chart change. -/
theorem addOne_mem_borderedHolomorphicGroupoid :
    addOne.toOpenPartialHomeomorph ∈ borderedHolomorphicGroupoid :=
  toOpenPartialHomeomorph_mem_borderedHolomorphicGroupoid (F := (· + 1)) (G := (· - 1))
    (by fun_prop) (by fun_prop) coe_addOne coe_addOne_symm

/-- Dilation by two, as a homeomorphism of the closed upper half-plane. -/
def twoMul : ClosedUpperHalfPlane ≃ₜ ClosedUpperHalfPlane :=
  (Homeomorph.mulLeft₀ (2 : ℂ) two_ne_zero).subtype fun z ↦ by simp

@[simp]
theorem coe_twoMul (z : ClosedUpperHalfPlane) : (twoMul z : ℂ) = 2 * z := by
  rw [twoMul]
  rfl

@[simp]
theorem coe_twoMul_symm (z : ClosedUpperHalfPlane) : (twoMul.symm z : ℂ) = 2⁻¹ * z := by
  rw [twoMul]
  rfl

/-- Dilation by two is a bordered holomorphic chart change. -/
theorem twoMul_mem_borderedHolomorphicGroupoid :
    twoMul.toOpenPartialHomeomorph ∈ borderedHolomorphicGroupoid :=
  toOpenPartialHomeomorph_mem_borderedHolomorphicGroupoid (F := (2 * ·)) (G := (2⁻¹ * ·))
    (by fun_prop) (by fun_prop) coe_twoMul coe_twoMul_symm

/-- The reflection `z ↦ -conj z`, as a homeomorphism of the closed upper half-plane. -/
def negConj : ClosedUpperHalfPlane ≃ₜ ClosedUpperHalfPlane :=
  (conjLIE.toHomeomorph.trans (Homeomorph.neg ℂ)).subtype fun z ↦ by simp

@[simp]
theorem coe_negConj (z : ClosedUpperHalfPlane) : (negConj z : ℂ) = -conj (z : ℂ) := by
  rw [negConj]
  rfl

/-- The map `z ↦ -conj z` is not complex differentiable anywhere. -/
private theorem not_differentiableAt_neg_conj (z : ℂ) :
    ¬ DifferentiableAt ℂ (fun w : ℂ ↦ -conj w) z := by
  intro hd
  have hreal : HasFDerivAt (fun w : ℂ ↦ -conj w) (-conjCLE.toContinuousLinearMap : ℂ →L[ℝ] ℂ) z :=
    conjCLE.toContinuousLinearMap.hasFDerivAt.neg
  have hL := hd.hasFDerivAt.restrictScalars ℝ |>.unique hreal
  have h1 := congrArg (fun L : ℂ →L[ℝ] ℂ ↦ L I) hL
  have h2 := congrArg (fun L : ℂ →L[ℝ] ℂ ↦ L 1) hL
  simp only [ContinuousLinearMap.coe_restrictScalars', FunLike.coe_neg, Pi.neg_apply,
    ContinuousLinearEquiv.coe_coe, conjCLE_apply, conj_I, neg_neg, map_one] at h1 h2
  have h3 : fderiv ℂ (fun w : ℂ ↦ -conj w) z I = I * fderiv ℂ (fun w : ℂ ↦ -conj w) z 1 := by
    rw [← smul_eq_mul, ← map_smul, smul_eq_mul, mul_one]
  rw [h1, h2] at h3
  have := congrArg Complex.im h3
  simp at this
  norm_num at this

/-- The reflection `z ↦ -conj z` preserves the closed upper half-plane and the real axis, but it
is antiholomorphic, so it is not a bordered holomorphic chart change. -/
theorem negConj_not_mem_borderedHolomorphicGroupoid :
    negConj.toOpenPartialHomeomorph ∉ borderedHolomorphicGroupoid := by
  intro hmem
  have hd := (mem_borderedHolomorphicGroupoid_iff.1 hmem).2.1
  have hat := hd.differentiableAt <|
    ((negConj.toOpenPartialHomeomorph.open_source.preimage
      closedUpperHalfPlaneModel.continuous_symm).inter
        (isOpen_lt continuous_const continuous_im)).mem_nhds
          (show (I : ℂ) ∈ _ from ⟨by simp, by simp⟩)
  refine not_differentiableAt_neg_conj I (hat.congr_of_eventuallyEq ?_)
  exact (eventually_coe_closedUpperHalfPlaneModel_symm (by simp)).mono fun w hw ↦ by
    simp [hw]

/-- The translation `z ↦ z + I` is not the restriction of any open partial homeomorphism of the
closed upper half-plane whose source contains `0`: the image of a relatively open neighbourhood
of `0` would be relatively open, but it misses the points of imaginary part less than one. -/
theorem not_exists_openPartialHomeomorph_add_I :
    ¬ ∃ e : OpenPartialHomeomorph ClosedUpperHalfPlane ClosedUpperHalfPlane,
      ofReal 0 ∈ e.source ∧ ∀ z ∈ e.source, (e z : ℂ) = z + I := by
  rintro ⟨e, h0, he⟩
  -- The path `t ↦ t I` reaches the point `e 0 = I` of the open target at `t = 1`.
  let γ : ℝ → ClosedUpperHalfPlane := fun t ↦ ⟨(max t 0 : ℝ) * I, by simp⟩
  have hγ : Continuous γ := by fun_prop
  have hγ1 : γ 1 = e (ofReal 0) := Subtype.ext (by simp [γ, he _ h0])
  have hmem : ∀ᶠ t in 𝓝[<] (1 : ℝ), γ t ∈ e.target :=
    nhdsWithin_le_nhds (hγ.continuousAt.preimage_mem_nhds
      (e.open_target.mem_nhds (hγ1 ▸ e.map_source h0)))
  obtain ⟨t, ht, htlt⟩ := (hmem.and self_mem_nhdsWithin).exists
  have hpre := he _ (e.map_target ht)
  rw [e.right_inv ht] at hpre
  have him := congrArg Complex.im hpre
  have hnn := (e.symm (γ t)).property
  simp only [γ] at hnn
  simp only [γ, mul_im, ofReal_re, I_im, mul_one, ofReal_im, I_re, mul_zero, add_zero,
    add_im] at him
  have : max t 0 < 1 := max_lt htlt one_pos
  linarith

end ClosedUpperHalfPlane

end TauCeti
