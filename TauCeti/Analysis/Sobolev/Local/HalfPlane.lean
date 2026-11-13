/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Local.Basic
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import TauCeti.Analysis.Sobolev.Local.Locality
import TauCeti.Analysis.Sobolev.Trace.Reflection.HalfSpace

/-!
# Smooth functions on relatively open subsets of the closed upper half-plane

For an open `Ω ⊆ ℂ`, a map that is `Cᵏ` on the relatively open subset `Ω ∩ {z | 0 ≤ z.im}` of the
closed upper half-plane is in the local Sobolev class `TauCeti.MemWkpLoc p (Ω ∩ {z | 0 ≤ z.im}) k`
for every exponent, with `Lᵖ` bounds on compact sets reaching the real axis. Near a point of the
real axis the map extends to a `Cᵏ` map across the axis, by
`TauCeti.HalfSpaceExtension.exists_local_contDiff_extension_halfSpace` read in the coordinates
`(im z, re z)`, and the pieces are glued by `TauCeti.memWkpLoc_iff_locally`.

## Main declarations

* `TauCeti.exists_contDiffOn_eqOn_inter_setOf_im_nonneg`: near each point, a `Cᵏ` map on
  `Ω ∩ {z | 0 ≤ z.im}` agrees with a map that is `Cᵏ` on an open neighbourhood of the point.
* `IsOpen.measurableSet_inter_setOf_im_nonneg`: such relatively open sets are measurable.
* `ContDiffOn.memWkpLoc_inter_setOf_im_nonneg`: `Cᵏ` maps on `Ω ∩ {z | 0 ≤ z.im}` are in the
  local Sobolev class of order `k` there.
-/

public section

open Set Filter MeasureTheory

noncomputable section

namespace TauCeti

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {p : ENNReal} {k : ℕ}

/-- The real coordinates `(im z, re z)` of `ℂ`, with the normal coordinate first, as used by the
half-space extension. -/
private def imReEquiv : ℂ ≃L[ℝ] ℝ × ℝ :=
  Complex.equivRealProdCLM.trans (ContinuousLinearEquiv.prodComm ℝ ℝ ℝ)

private theorem imReEquiv_apply (z : ℂ) : imReEquiv z = (z.im, z.re) :=
  rfl

private theorem im_imReEquiv_symm (w : ℝ × ℝ) : (imReEquiv.symm w).im = w.1 := by
  obtain ⟨z, rfl⟩ := imReEquiv.surjective w
  rw [ContinuousLinearEquiv.symm_apply_apply, imReEquiv_apply]

/-- Near every point of a relatively open subset `Ω ∩ {z | 0 ≤ z.im}` of the closed upper
half-plane, a `Cᵏ` map on it agrees with a map that is `Cᵏ` on an open neighbourhood of the
point. At a point of the real axis the extension reflects across the axis. -/
theorem exists_contDiffOn_eqOn_inter_setOf_im_nonneg {f : ℂ → F} {Ω : Set ℂ}
    (hΩ : IsOpen Ω) (hf : ContDiffOn ℝ k f (Ω ∩ {z | 0 ≤ z.im})) {x : ℂ}
    (hx : x ∈ Ω ∩ {z | 0 ≤ z.im}) :
    ∃ W : Set ℂ, IsOpen W ∧ x ∈ W ∧ ∃ g : ℂ → F, ContDiffOn ℝ k g W ∧
      EqOn g f ((Ω ∩ {z | 0 ≤ z.im}) ∩ W) := by
  rcases (show 0 ≤ x.im from hx.2).lt_or_eq with hpos | hzero
  · exact ⟨Ω ∩ {z | 0 < z.im}, hΩ.inter (isOpen_lt continuous_const Complex.continuous_im),
      ⟨hx.1, hpos⟩, f, hf.mono fun z hz ↦ ⟨hz.1, show 0 ≤ z.im from le_of_lt hz.2⟩, fun _ _ ↦ rfl⟩
  · have hfe : ContDiffOn ℝ k (f ∘ imReEquiv.symm)
        (HalfSpaceExtension.upperHalfSpace ℝ ∩ imReEquiv.symm ⁻¹' Ω) := by
      refine hf.comp imReEquiv.symm.contDiff.contDiffOn fun w hw ↦ ⟨hw.2, ?_⟩
      have h1 : 0 ≤ w.1 := HalfSpaceExtension.mem_upperHalfSpace.1 hw.1
      simpa only [mem_ofPred_eq, im_imReEquiv_symm] using h1
    have hxΩ : ((0 : ℝ), x.re) ∈ imReEquiv.symm ⁻¹' Ω := by
      rw [mem_preimage, hzero, ← imReEquiv_apply, ContinuousLinearEquiv.symm_apply_apply]
      exact hx.1
    obtain ⟨g, hg, hgf⟩ := HalfSpaceExtension.exists_local_contDiff_extension_halfSpace k
      (f ∘ imReEquiv.symm) (hΩ.preimage imReEquiv.symm.continuous) hfe x.re hxΩ
    obtain ⟨T, hT, hTo, hxT⟩ := eventually_nhds_iff.1 hgf
    refine ⟨imReEquiv ⁻¹' T, hTo.preimage imReEquiv.continuous, ?_, g ∘ imReEquiv,
      (hg.comp imReEquiv.contDiff).contDiffOn, fun z hz ↦ ?_⟩
    · rw [mem_preimage, imReEquiv_apply, ← hzero]
      exact hxT
    · have h := hT _ hz.2 (by simpa only [imReEquiv_apply] using (show 0 ≤ z.im from hz.1.2))
      simpa only [Function.comp_apply, ContinuousLinearEquiv.symm_apply_apply] using h

/-- A relatively open subset `Ω ∩ {z | 0 ≤ z.im}` of the closed upper half-plane, for an open
`Ω`, is measurable. -/
theorem _root_.IsOpen.measurableSet_inter_setOf_im_nonneg {Ω : Set ℂ} (hΩ : IsOpen Ω) :
    MeasurableSet (Ω ∩ {z | 0 ≤ z.im}) :=
  hΩ.measurableSet.inter (isClosed_le continuous_const Complex.continuous_im).measurableSet

/-- A map that is `Cᵏ` on a relatively open subset `Ω ∩ {z | 0 ≤ z.im}` of the closed upper
half-plane, for an open `Ω`, is in the local Sobolev class of order `k` there, for every
exponent. The `Lᵖ` bounds reach the real axis: near a boundary point the map extends to a `Cᵏ`
map across the axis. -/
theorem _root_.ContDiffOn.memWkpLoc_inter_setOf_im_nonneg [CompleteSpace F] {f : ℂ → F}
    {Ω : Set ℂ} (hf : ContDiffOn ℝ k f (Ω ∩ {z | 0 ≤ z.im})) (hΩ : IsOpen Ω) :
    MemWkpLoc p (Ω ∩ {z | 0 ≤ z.im}) k f := by
  refine memWkpLoc_iff_locally.2 fun x hx ↦ ?_
  obtain ⟨W, hWo, hxW, g, hg, hgf⟩ := exists_contDiffOn_eqOn_inter_setOf_im_nonneg hΩ hf hx
  refine ⟨_ ∩ W, inter_mem_nhdsWithin _ (hWo.mem_nhds hxW), ?_⟩
  exact (hg.memWkpLoc (Ω := ⟨W, hWo⟩) (p := p) inter_subset_right).congr_ae
    ((ae_restrict_iff' (hΩ.measurableSet_inter_setOf_im_nonneg.inter hWo.measurableSet)).2
      (Eventually.of_forall hgf))

end TauCeti
