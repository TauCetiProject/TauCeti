/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Orientation.Linear
public import TauCeti.Geometry.Manifold.Complex.FundamentalClass

/-!
# The canonical local orientations of a Riemann surface in centred holomorphic charts

Let `M` be a Riemann surface with its canonical homological orientation
(`TauCeti.complexHomologicalOrientation`), and let `e` be a holomorphic chart at `x`. The centred
chart `y ↦ e y - e x`, on the source of `e`, maps `x` to the origin and no other point there, so it
acts on local homology at `x`. This file proves that it carries the canonical local orientation of
`M` at `x`, read in the source of `e` through excision, to the local orientation of `ℂ` at the
origin selected by its standard orientation `Complex.orientation`
(`TauCeti.localHomologyMap_sub_complexHomologicalOrientation`).

This is the normalization asked of an oriented chart by the computation of the local index of a
section at a transverse zero as the sign of a Jacobian determinant
(`TauCeti.VectorBundleOrientation.sectionIndex_eq_sign_det_of_hasFDerivAt`), so that computation
applies to sections of complex line bundles over Riemann surfaces read in holomorphic charts.

The proof reads the canonical local orientation in the centred chart, which is holomorphic with the
same derivative as `e`, and restricts that chart to its source. The identity-chart generator is
identified with the local orientation of `Complex.orientation` by the canonical real inner-product
comparison `Orientation.localOrientation_eq_localOrientationOfOrientedChart_refl`.
-/

public section

noncomputable section

open Module Set Topology

namespace TauCeti

/-! ### Centred holomorphic charts -/

open scoped _root_.Manifold ContDiff

variable {M : Type} [TopologicalSpace M] [T2Space M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ, ℂ) 1 M]

/-- The canonical local orientation of a Riemann surface at `x` is the one selected by
`Complex.orientation` in the centred chart `e - e x`, for a holomorphic chart `e` at `x`: the
transition from `e` is a translation. -/
private theorem complexHomologicalOrientation_eq_centred {k : ℕ∞ω} [NeZero k]
    {e : OpenPartialHomeomorph M ℂ} (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ, ℂ) k M) {x : M}
    (hx : x ∈ e.source)
    (hx₀ : x ∈ (e.trans (Homeomorph.subRight (e x)).toOpenPartialHomeomorph).source) :
    (complexHomologicalOrientation M x).val =
      ((e.trans (Homeomorph.subRight (e x)).toOpenPartialHomeomorph).localOrientationOfOrientedChart
        hx₀ Complex.orientation (n := 1) Complex.finrank_real_complex).val := by
  have hd : HasFDerivAt ((e.trans (Homeomorph.subRight (e x)).toOpenPartialHomeomorph) ∘ e.symm)
      (ContinuousLinearMap.id ℝ ℂ) (e x) := by
    refine ((hasFDerivAt_id (e x)).sub_const (e x)).congr_of_eventuallyEq ?_
    filter_upwards [e.eventually_right_inverse' hx] with y hy
    simp [hy]
  have hdet : (ContinuousLinearMap.id ℝ ℂ).det = 1 := LinearMap.det_id
  rw [complexHomologicalOrientation_apply_of_mem_maximalAtlas he hx,
    OpenPartialHomeomorph.coe_localOrientationOfOrientedChart_eq_sign_det_smul _ _ e _ hx hx₀ hd
      (hdet ▸ one_ne_zero), hdet, sign_one, SignType.coe_one, one_smul]

/-- **The canonical local orientations in a centred holomorphic chart.** For a `C^k` holomorphic
chart `e` of a Riemann surface `M` at `x`, with `k ≠ 0`, the centred chart `y ↦ e y - e x` on the
source of `e` carries the canonical local orientation of `M` at `x`, read in the source of `e`
through excision, to the local orientation of `ℂ` at the origin selected by
`Complex.orientation`. -/
theorem localHomologyMap_sub_complexHomologicalOrientation {k : ℕ∞ω} [NeZero k]
    {e : OpenPartialHomeomorph M ℂ} (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ, ℂ) k M) {x : M}
    (hx : x ∈ e.source)
    (h : (⟨fun y : e.source ↦ e y - e x, e.continuousOn.domRestrict.sub continuous_const⟩ :
      C(e.source, ℂ)) ⁻¹' {0} ⊆ {⟨x, hx⟩}) :
    localHomologyMap (ModuleCat.of ℤ (ULift.{0} ℤ))
        (⟨fun y : e.source ↦ e y - e x, e.continuousOn.domRestrict.sub continuous_const⟩ :
          C(e.source, ℂ)) (S := {⟨x, hx⟩}) (T := {0}) h 2
        ((e.open_source.isOpenEmbedding_subtypeVal.localOrientationEquiv ⟨x, hx⟩ 2).symm
          (complexHomologicalOrientation M x)).val =
      (Complex.orientation.localOrientation Complex.finrank_real_complex).val := by
  set Z := ModuleCat.of ℤ (ULift.{0} ℤ)
  -- The centred chart `e₀ = e - e x`, a chart of `M` with the same source as `e`.
  set e₀ : OpenPartialHomeomorph M ℂ := e.trans (Homeomorph.subRight (e x)).toOpenPartialHomeomorph
  have hx₀ : x ∈ e₀.source := by simpa [e₀] using hx
  have hoM := complexHomologicalOrientation_eq_centred he hx hx₀
  -- The restriction of `e₀` to the source of `e`, a chart of the subtype.
  let s : TopologicalSpace.Opens M := ⟨e.source, e.open_source⟩
  let φ : OpenPartialHomeomorph s ℂ := e₀.subtypeRestr (s := s) ⟨⟨x, hx⟩⟩
  have hxφ : (⟨x, hx⟩ : s) ∈ φ.source := by
    rw [OpenPartialHomeomorph.subtypeRestr_source]
    exact hx₀
  let ι : C(e.source, M) := ⟨Subtype.val, continuous_subtypeVal⟩
  have hι : ι ⁻¹' {x} ⊆ {⟨x, hx⟩} := fun y hy ↦ Subtype.ext hy
  -- The inclusion carries the local orientation selected in `φ` to that selected in `e₀`.
  have h₁ := OpenPartialHomeomorph.localHomologyMap_localOrientationOfOrientedChart
    Complex.orientation Complex.finrank_real_complex ι φ e₀ hxφ hx₀
    (Filter.Eventually.of_forall fun _ ↦ rfl) hι
  -- So the local orientation selected in `φ` is the canonical one, read in the source of `e`.
  have h₂ : ((e.open_source.isOpenEmbedding_subtypeVal.localOrientationEquiv ⟨x, hx⟩ 2).symm
      (complexHomologicalOrientation M x)) =
      φ.localOrientationOfOrientedChart hxφ Complex.orientation Complex.finrank_real_complex := by
    rw [Equiv.symm_apply_eq]
    apply Subtype.ext
    rw [IsOpenEmbedding.coe_localOrientationEquiv, localHomologyIsoOfIsOpenEmbedding_hom, hoM]
    exact h₁.symm
  -- The centred chart carries the local orientation selected in `φ` to the identity-chart
  -- generator of `ℂ` at the origin, which is the local orientation selected by the orientation.
  -- The value `τ x = 0` enters the morphism type and the preimage condition, so it is generalized
  -- and substituted instead of rewritten.
  set τ : C(e.source, ℂ) :=
    ⟨fun y : e.source ↦ e y - e x, e.continuousOn.domRestrict.sub continuous_const⟩
  have h₃ : ∀ {c : ℂ}, τ ⟨x, hx⟩ = c → ∀ (h' : τ ⁻¹' {c} ⊆ {⟨x, hx⟩}),
      localHomologyMap Z τ (S := {⟨x, hx⟩}) (T := {c}) h' 2
          (φ.localOrientationOfOrientedChart hxφ Complex.orientation
            Complex.finrank_real_complex).val =
        ((OpenPartialHomeomorph.refl ℂ).localOrientationOfOrientedChart (by simp)
          Complex.orientation Complex.finrank_real_complex).val := by
    rintro _ rfl h'
    exact OpenPartialHomeomorph.localHomologyMap_localOrientationOfOrientedChart
      Complex.orientation Complex.finrank_real_complex τ φ (OpenPartialHomeomorph.refl ℂ) hxφ
      (by simp) (Filter.Eventually.of_forall fun _ ↦ rfl) h'
  rw [h₂, h₃ (sub_self (e x)) h,
    Orientation.localOrientation_eq_localOrientationOfOrientedChart_refl
      Complex.orientation Complex.finrank_real_complex]

end TauCeti
