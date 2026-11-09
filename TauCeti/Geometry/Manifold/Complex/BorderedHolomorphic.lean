/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Complex.ClosedUpperHalfPlane
public import TauCeti.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# The bordered holomorphic groupoid

`TauCeti.borderedHolomorphicGroupoid` is the structure groupoid on the closed upper half-plane
whose members are the open partial homeomorphisms that are smooth up to the real boundary and
complex differentiable at the points of positive imaginary part. A charted space modelled on the
closed upper half-plane with this groupoid is a Riemann surface with boundary.

The groupoid is contained in the smooth groupoid of `closedUpperHalfPlaneModel`, so such a space
is a smooth manifold with boundary. By `ClosedUpperHalfPlane.isManifold_euclideanHalfSpace`, after
reading the charts in Mathlib's native half-space coordinates it is also a smooth manifold modelled
on `𝓡∂ 2`. Members send real boundary points to real boundary points, and points of positive
imaginary part to points of positive imaginary part, by
`ClosedUpperHalfPlane.im_eq_zero_iff_of_mem_contDiffGroupoid` and
`ClosedUpperHalfPlane.im_pos_iff_of_mem_contDiffGroupoid` applied through
`borderedHolomorphicGroupoid_le_contDiffGroupoid`.

The translation `z ↦ z + 1` and the dilation `z ↦ 2z` are members. The reflection `z ↦ -conj z`
preserves the closed upper half-plane and the real axis but is not a member, since it is
antiholomorphic. The translation `z ↦ z + I` is not even the restriction of an open partial
homeomorphism defined near `0`, since its image of a relatively open neighbourhood of `0` misses
the points of imaginary part less than one.

## Main definitions

* `TauCeti.borderedHolomorphicGroupoid`: the bordered holomorphic groupoid.
* `TauCeti.ClosedUpperHalfPlane.interiorHolomorphicPregroupoid`: the auxiliary pregroupoid
  describing the interior condition.

## Main results

* `TauCeti.mem_borderedHolomorphicGroupoid_iff`: membership is smoothness up to the boundary
  together with complex differentiability of the map and of its inverse in the interior.
* `TauCeti.borderedHolomorphicGroupoid_le_contDiffGroupoid`: members are smooth, so a charted
  space with this groupoid is a smooth manifold
  (`TauCeti.isManifold_of_hasGroupoid_borderedHolomorphicGroupoid`).
* `TauCeti.ClosedUpperHalfPlane.toOpenPartialHomeomorph_mem_borderedHolomorphicGroupoid`: a
  homeomorphism given by entire functions in both directions is a member.

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

namespace ClosedUpperHalfPlane

/-- The maps of the closed upper half-plane that, at each point of positive imaginary part of a
set, take a value of positive imaginary part and are complex differentiable in the ambient
coordinate. Requiring interior points to go to interior points makes the property stable under
composition. For open partial homeomorphisms that are smooth up to the boundary, the condition that
interior points go to interior points is automatic
(`ClosedUpperHalfPlane.im_pos_iff_of_mem_contDiffGroupoid`), so only complex differentiability
remains; see `ClosedUpperHalfPlane.interiorHolomorphicPregroupoid_property_source_iff` and
`TauCeti.mem_borderedHolomorphicGroupoid_iff`. -/
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

/-- The defining property of `interiorHolomorphicPregroupoid`. -/
theorem interiorHolomorphicPregroupoid_property_iff
    {f : ClosedUpperHalfPlane → ClosedUpperHalfPlane} {u : Set ClosedUpperHalfPlane} :
    interiorHolomorphicPregroupoid.property f u ↔ ∀ x ∈ u, 0 < (x : ℂ).im →
      0 < (f x : ℂ).im ∧
        DifferentiableAt ℂ (closedUpperHalfPlaneModel ∘ f ∘ closedUpperHalfPlaneModel.symm) x :=
  Iff.rfl

/-- For an open partial homeomorphism that is smooth up to the boundary, the interior condition
reduces to complex differentiability on the interior part of the source. -/
theorem interiorHolomorphicPregroupoid_property_source_iff
    {e : OpenPartialHomeomorph ClosedUpperHalfPlane ClosedUpperHalfPlane}
    (he : e ∈ contDiffGroupoid ∞ closedUpperHalfPlaneModel) :
    interiorHolomorphicPregroupoid.property e e.source ↔
      DifferentiableOn ℂ (closedUpperHalfPlaneModel ∘ e ∘ closedUpperHalfPlaneModel.symm)
        (closedUpperHalfPlaneModel.symm ⁻¹' e.source ∩ {z | 0 < z.im}) := by
  rw [interiorHolomorphicPregroupoid_property_iff]
  constructor
  · intro h z hz
    have hz' : (closedUpperHalfPlaneModel.symm z : ℂ) = z :=
      coe_closedUpperHalfPlaneModel_symm_of_im_nonneg (le_of_lt hz.2)
    have hd := (h _ hz.1 (by rw [hz']; exact hz.2)).2
    rw [hz'] at hd
    exact hd.differentiableWithinAt
  · intro h x hx hxim
    refine ⟨(im_pos_iff_of_mem_contDiffGroupoid he (by simp) hx).1 hxim, h.differentiableAt ?_⟩
    exact ((e.open_source.preimage closedUpperHalfPlaneModel.continuous_symm).inter
      (isOpen_lt continuous_const continuous_im)).mem_nhds ⟨by simpa using hx, hxim⟩

end ClosedUpperHalfPlane

/-- The bordered holomorphic groupoid on the closed upper half-plane: open partial homeomorphisms
that are smooth up to the real boundary and complex differentiable, with complex differentiable
inverse, at the points of positive imaginary part. -/
def borderedHolomorphicGroupoid : StructureGroupoid ClosedUpperHalfPlane :=
  contDiffGroupoid ∞ closedUpperHalfPlaneModel ⊓
    ClosedUpperHalfPlane.interiorHolomorphicPregroupoid.groupoid

/-- Membership in the infimum of two structure groupoids. This holds by `Iff.rfl`: Mathlib's `⊓`
on structure groupoids is the intersection of their members. -/
private theorem mem_inf_structureGroupoid {G G' : StructureGroupoid ClosedUpperHalfPlane}
    {e : OpenPartialHomeomorph ClosedUpperHalfPlane ClosedUpperHalfPlane} :
    e ∈ G ⊓ G' ↔ e ∈ G ∧ e ∈ G' :=
  Iff.rfl

/-- Membership in the smooth groupoid of the closed upper half-plane, read in the ambient
coordinate. This holds by `Iff.rfl`: `contDiffGroupoid` is the groupoid of
`contDiffPregroupoid`, whose property is smoothness of the coordinate expression on the model
range. -/
private theorem mem_contDiffGroupoid_closedUpperHalfPlaneModel_iff
    {e : OpenPartialHomeomorph ClosedUpperHalfPlane ClosedUpperHalfPlane} :
    e ∈ contDiffGroupoid ∞ closedUpperHalfPlaneModel ↔
      ContDiffOn ℝ ∞ (closedUpperHalfPlaneModel ∘ e ∘ closedUpperHalfPlaneModel.symm)
          (closedUpperHalfPlaneModel.symm ⁻¹' e.source ∩ range closedUpperHalfPlaneModel) ∧
        ContDiffOn ℝ ∞ (closedUpperHalfPlaneModel ∘ e.symm ∘ closedUpperHalfPlaneModel.symm)
          (closedUpperHalfPlaneModel.symm ⁻¹' e.target ∩ range closedUpperHalfPlaneModel) :=
  Iff.rfl

/-- Members of the bordered holomorphic groupoid are smooth up to the boundary. -/
theorem borderedHolomorphicGroupoid_le_contDiffGroupoid :
    borderedHolomorphicGroupoid ≤ contDiffGroupoid ∞ closedUpperHalfPlaneModel :=
  inf_le_left

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
  rw [borderedHolomorphicGroupoid, mem_inf_structureGroupoid, mem_groupoid_of_pregroupoid]
  constructor
  · rintro ⟨hc, h₁, h₂⟩
    exact ⟨hc, (ClosedUpperHalfPlane.interiorHolomorphicPregroupoid_property_source_iff hc).1 h₁,
      (ClosedUpperHalfPlane.interiorHolomorphicPregroupoid_property_source_iff
        ((contDiffGroupoid _ _).symm hc)).1 h₂⟩
  · rintro ⟨hc, h₁, h₂⟩
    exact ⟨hc, (ClosedUpperHalfPlane.interiorHolomorphicPregroupoid_property_source_iff hc).2 h₁,
      (ClosedUpperHalfPlane.interiorHolomorphicPregroupoid_property_source_iff
        ((contDiffGroupoid _ _).symm hc)).2 h₂⟩

/-- A charted space with bordered holomorphic transition maps is a smooth manifold modelled on the
closed upper half-plane. -/
instance isManifold_of_hasGroupoid_borderedHolomorphicGroupoid (M : Type*) [TopologicalSpace M]
    [ChartedSpace ClosedUpperHalfPlane M] [HasGroupoid M borderedHolomorphicGroupoid] :
    IsManifold closedUpperHalfPlaneModel ∞ M :=
  haveI := hasGroupoid_of_le ‹HasGroupoid M borderedHolomorphicGroupoid›
    borderedHolomorphicGroupoid_le_contDiffGroupoid
  IsManifold.mk' _ _ _

namespace ClosedUpperHalfPlane

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
  refine mem_borderedHolomorphicGroupoid_iff.2
    ⟨mem_contDiffGroupoid_closedUpperHalfPlaneModel_iff.2 ⟨?_, ?_⟩, ?_, ?_⟩
  · simpa using hsmooth hF hhF
  · simpa using hsmooth hG hhG
  · simpa using hholo hF hhF
  · simpa using hholo hG hhG

/-- Translation by one, as a homeomorphism of the closed upper half-plane. -/
def addOne : ClosedUpperHalfPlane ≃ₜ ClosedUpperHalfPlane :=
  (Homeomorph.addRight (1 : ℂ)).subtype fun z ↦ by simp

@[simp]
theorem coe_addOne (z : ClosedUpperHalfPlane) : (addOne z : ℂ) = z + 1 := by
  simp [addOne]

@[simp]
theorem coe_addOne_symm (z : ClosedUpperHalfPlane) : (addOne.symm z : ℂ) = z - 1 := by
  simp [addOne, Homeomorph.addRight_symm, sub_eq_add_neg]

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
  simp [twoMul]

@[simp]
theorem coe_twoMul_symm (z : ClosedUpperHalfPlane) : (twoMul.symm z : ℂ) = 2⁻¹ * z := by
  simp [twoMul]

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
  simp [negConj]

/-- The reflection `z ↦ -conj z` preserves the closed upper half-plane and the real axis, but it
is antiholomorphic, so it is not a bordered holomorphic chart change. -/
theorem negConj_notMem_borderedHolomorphicGroupoid :
    negConj.toOpenPartialHomeomorph ∉ borderedHolomorphicGroupoid := by
  intro hmem
  -- The interior condition, evaluated at the point `I`, gives differentiability there.
  have hprop := (mem_groupoid_of_pregroupoid.1 (mem_inf_structureGroupoid.1 hmem).2).1
  have hat : DifferentiableAt ℂ
      (closedUpperHalfPlaneModel ∘ negConj ∘ closedUpperHalfPlaneModel.symm) I :=
    (interiorHolomorphicPregroupoid_property_iff.1 hprop ⟨I, by simp⟩ (by simp) (by simp)).2
  refine Complex.not_differentiableAt_neg_conj I (hat.congr_of_eventuallyEq ?_)
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
  simp [γ] at him hnn
  have : max t 0 < 1 := max_lt htlt one_pos
  linarith

end ClosedUpperHalfPlane

end TauCeti
