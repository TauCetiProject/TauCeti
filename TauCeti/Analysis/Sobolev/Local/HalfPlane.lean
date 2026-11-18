/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Local.Basic
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import TauCeti.Analysis.Complex.ReImTopology
import TauCeti.Analysis.Sobolev.Local.Locality
import TauCeti.Analysis.Sobolev.Trace.Reflection.HalfSpace
import TauCeti.MeasureTheory.Measure.Lebesgue.Complex

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
* `TauCeti.MemWkpLoc.hasWeakFDerivOn_fderiv_of_contDiffOn_inter_setOf_im_nonneg` and
  `TauCeti.MemWkpLoc.iteratedFDeriv_of_contDiffOn_inter_setOf_im_nonneg`: the classical
  derivatives of a representative that is `Cᵏ` on `Ω ∩ {0 < im}` are weak derivatives, in the local
  Sobolev classes of `Ω ∩ {0 ≤ im}` of the complementary orders, the half-plane forms of
  `TauCeti.MemWkpLoc.hasWeakFDerivOn_fderiv_of_contDiffOn` and
  `TauCeti.MemWkpLoc.iteratedFDeriv_of_contDiffOn`.
-/

public section

open Set Filter MeasureTheory TopologicalSpace

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

/-! ### Classical derivatives of representatives -/

variable {Ω : Opens ℂ} {u g : ℂ → F}

/-- **The derivative of a `C¹` representative is a weak derivative, on half-discs.** If `g` is
`C¹` on `Ω ∩ {0 < im}` and agrees almost everywhere on `Ω ∩ {0 ≤ im}` with
`u ∈ MemWkpLoc p (Ω ∩ {0 ≤ im}) (k + 1)`, then `fderiv ℝ g` is a weak derivative of `u` on
`Ω ∩ {0 < im}` and lies in `MemWkpLoc p (Ω ∩ {0 ≤ im}) k`, with `Lᵖ` bounds up to the real axis.
-/
theorem MemWkpLoc.hasWeakFDerivOn_fderiv_of_contDiffOn_inter_setOf_im_nonneg
    (hu : MemWkpLoc p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) (k + 1) u)
    (hg : ContDiffOn ℝ 1 g Ω.upperHalf)
    (hug : u =ᵐ[volume.restrict ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im})] g) :
    HasWeakFDerivOn volume Ω.upperHalf u (fderiv ℝ g) ∧
      MemWkpLoc p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) k (fderiv ℝ g) := by
  have := hu.completeSpace
  obtain ⟨D, hD, hDk⟩ := hu.exists_weakFDeriv
  rw [Opens.interior_inter_setOf_im_nonneg_eq_upperHalf] at hD
  have hsub : (Ω.upperHalf : Set ℂ) ⊆ (Ω : Set ℂ) ∩ {z | 0 ≤ z.im} := fun z hz =>
    ⟨(Opens.mem_upperHalf.1 hz).1, (Opens.mem_upperHalf.1 hz).2.le⟩
  have hug' : u =ᵐ[volume.restrict Ω.upperHalf] g := ae_restrict_of_ae_restrict_of_subset hsub hug
  have hg' : HasWeakFDerivOn volume Ω.upperHalf g (fderiv ℝ g) := hg.hasWeakFDerivOn_fderiv
  refine ⟨hg'.congr_ae hug'.symm, hDk.congr_ae ?_⟩
  have hDg := (hD.congr_ae hug').ae_eq hg'
  rw [Opens.coe_upperHalf] at hDg
  refine (ae_restrict_congr_set ?_).1 hDg
  exact Filter.EventuallyEqSet.rfl.inter (Complex.setOf_le_im_ae_eq 0).symm

/-- **Iterated derivatives of a `Cᵏ` representative, on half-discs.** If `g` is `Cᵏ` on
`Ω ∩ {0 < im}` and agrees almost everywhere on `Ω ∩ {0 ≤ im}` with
`u ∈ MemWkpLoc p (Ω ∩ {0 ≤ im}) (k + m)`, then `iteratedFDeriv ℝ k g` lies in
`MemWkpLoc p (Ω ∩ {0 ≤ im}) m`, with `Lᵖ` bounds up to the real axis. -/
theorem MemWkpLoc.iteratedFDeriv_of_contDiffOn_inter_setOf_im_nonneg {m : ℕ}
    (hu : MemWkpLoc p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) (k + m) u)
    (hg : ContDiffOn ℝ k g Ω.upperHalf)
    (hug : u =ᵐ[volume.restrict ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im})] g) :
    MemWkpLoc p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) m (iteratedFDeriv ℝ k g) := by
  induction k generalizing F with
  | zero =>
    rw [iteratedFDeriv_zero_eq_comp]
    exact (continuousMultilinearCurryFin0 ℝ ℂ F).symm.toContinuousLinearEquiv.comp_memWkpLoc_iff.2
      ((Nat.zero_add m ▸ hu).congr_ae hug)
  | succ k ih =>
    rw [Nat.add_right_comm] at hu
    obtain ⟨-, hDk⟩ := hu.hasWeakFDerivOn_fderiv_of_contDiffOn_inter_setOf_im_nonneg
      (hg.of_le (by exact_mod_cast Nat.le_add_left 1 k)) hug
    have hgk : ContDiffOn ℝ k (fderiv ℝ g) Ω.upperHalf :=
      hg.fderiv_of_isOpen Ω.upperHalf.isOpen (by push_cast; rfl)
    have h := ih hDk hgk (Filter.EventuallyEq.refl _ _)
    have heq : iteratedFDeriv ℝ (k + 1) g =
        fun z => (continuousMultilinearCurryRightEquiv' ℝ k ℂ F).symm
          (iteratedFDeriv ℝ k (fderiv ℝ g) z) := by
      ext1 z
      exact iteratedFDeriv_succ_eq_comp_right
    rw [heq]
    exact (continuousMultilinearCurryRightEquiv' ℝ k ℂ F).symm.toContinuousLinearEquiv
      |>.comp_memWkpLoc_iff.2 h

end TauCeti
