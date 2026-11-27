/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.BumpFunction.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
public import TauCeti.Analysis.Complex.ReImTopology
public import TauCeti.Analysis.Sobolev.Local.Basic
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Topology.Separation.Regular
import TauCeti.Analysis.Sobolev.Local.Locality
import TauCeti.Analysis.Sobolev.Trace.Reflection.HalfSpace
import TauCeti.MeasureTheory.Measure.Lebesgue.Complex

/-!
# Local Sobolev classes on relatively open subsets of the closed upper half-plane

For an open `Ω ⊆ ℂ`, a map that is `Cᵏ` on the relatively open subset `Ω ∩ {z | 0 ≤ z.im}` of the
closed upper half-plane is in the local Sobolev class `TauCeti.MemWkpLoc p (Ω ∩ {z | 0 ≤ z.im}) k`
for every exponent, with `Lᵖ` bounds on compact sets reaching the real axis. Near a point of the
real axis the map extends to a `Cᵏ` map across the axis, by
`TauCeti.HalfSpaceExtension.exists_local_contDiff_extension_halfSpace` read in the coordinates
`(im z, re z)`, and the pieces are glued by `TauCeti.memWkpLoc_iff_locally`.

Because the real axis is null, local `Lᵖ` membership on `Ω ∩ {z | 0 ≤ z.im}` is detected on the
upper halves `W ∩ {0 < im}` (`TopologicalSpace.Opens.upperHalf`) of the open `W` with compact
closure inside `Ω` (`TauCeti.memLpLoc_inter_setOf_im_nonneg_iff`).

## Main declarations

* `TauCeti.memLpLoc_inter_setOf_im_nonneg_iff`: local `Lᵖ` membership on `Ω ∩ {z | 0 ≤ z.im}`
  detected through upper halves of relatively compact subdomains of `Ω`.
* `TauCeti.exists_contDiffOn_eqOn_inter_setOf_im_nonneg`: near each point, a `Cᵏ` map on
  `Ω ∩ {z | 0 ≤ z.im}` agrees with a map that is `Cᵏ` on an open neighbourhood of the point.
* `TauCeti.exists_contDiffOn_eqOn_inter_setOf_fst_im_nonneg`: the same for maps on relatively open
  subsets `W ∩ {q | 0 ≤ q.1.im}` of `ℂ × E`, whenever `ℝ × (ℝ × E)` has smooth bump functions
  (for instance, for finite-dimensional `E`).
* `IsOpen.measurableSet_inter_setOf_im_nonneg`: such relatively open sets are measurable.
* `ContDiffOn.memWkpLoc_inter_setOf_im_nonneg`: `Cᵏ` maps on `Ω ∩ {z | 0 ≤ z.im}` are in the
  local Sobolev class of order `k` there.
-/

public section

open Set Filter MeasureTheory TopologicalSpace

noncomputable section

namespace TauCeti

variable {F : Type*} [NormedAddCommGroup F] {p : ENNReal}

/-- **Local `Lᵖ` on a half-disc through upper halves.** A function is locally `Lᵖ` on
`Ω ∩ {0 ≤ im}`, up to the real axis, exactly when it is `Lᵖ` on the upper half `W ∩ {0 < im}` of
every open `W` whose closure is compact and contained in `Ω`. The real axis is null, so the
compact sets reaching it see no more than these upper halves. -/
theorem memLpLoc_inter_setOf_im_nonneg_iff {Ω : Opens ℂ} {f : ℂ → F} :
    MemLpLoc p ((Ω : Set ℂ) ∩ {z : ℂ | 0 ≤ z.im}) f ↔
      ∀ W : Opens ℂ, IsCompact (closure (W : Set ℂ)) → closure (W : Set ℂ) ⊆ Ω →
        MemLp f p (volume.restrict (W.upperHalf : Set ℂ)) := by
  refine ⟨fun hf W hWc hWΩ => ?_, fun h => memLpLoc_iff.2 fun K hKU hK => ?_⟩
  · have hK : IsCompact (closure (W : Set ℂ) ∩ {z : ℂ | 0 ≤ z.im}) :=
      hWc.inter_right (isClosed_le continuous_const Complex.continuous_im)
    refine (memLpLoc_iff.1 hf _ (Set.inter_subset_inter_left _ hWΩ) hK).mono_measure
      (Measure.restrict_mono ?_ le_rfl)
    intro z hz
    obtain ⟨hzW, hz0⟩ := Opens.mem_upperHalf.1 hz
    exact ⟨subset_closure hzW, hz0.le⟩
  · obtain ⟨W, hWo, hKW, hWΩ, hWc⟩ := exists_open_between_and_isCompact_closure hK Ω.isOpen
      (hKU.trans Set.inter_subset_left)
    refine (h ⟨W, hWo⟩ hWc hWΩ).mono_measure (Measure.restrict_mono_ae ?_)
    filter_upwards [(Complex.setOf_le_im_ae_eq 0).subset] with z hz hzK
    exact Opens.mem_upperHalf.2 ⟨hKW hzK, hz (hKU hzK).2⟩

variable [NormedSpace ℝ F] {k : ℕ}

section Product

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G]
  [NormedSpace ℝ G]

variable (E) in
/-- The real coordinates `(im z, (re z, y))` of `ℂ × E`, with the normal coordinate first, as used
by the half-space extension. -/
private def imReProdEquiv : (ℂ × E) ≃L[ℝ] (ℝ × (ℝ × E)) :=
  ((Complex.equivRealProdCLM.trans (ContinuousLinearEquiv.prodComm ℝ ℝ ℝ)).prodCongr
    (ContinuousLinearEquiv.refl ℝ E)).trans (ContinuousLinearEquiv.prodAssoc ℝ ℝ ℝ E)

private theorem imReProdEquiv_apply (q : ℂ × E) :
    imReProdEquiv E q = (q.1.im, (q.1.re, q.2)) :=
  rfl

private theorem im_fst_imReProdEquiv_symm (w : ℝ × (ℝ × E)) :
    ((imReProdEquiv E).symm w).1.im = w.1 := by
  obtain ⟨q, rfl⟩ := (imReProdEquiv E).surjective w
  rw [ContinuousLinearEquiv.symm_apply_apply, imReProdEquiv_apply]

/-- Near every point of a relatively open subset `W ∩ {q | 0 ≤ q.1.im}` of `ℂ × E`, a `Cᵏ` map on
it agrees with a map that is `Cᵏ` on an open neighbourhood of the point. The only hypothesis on `E`
is that `ℝ × (ℝ × E)` has smooth bump functions, as it does for finite-dimensional `E`. At a point
with `q.1.im = 0` the extension reflects across `{q | q.1.im = 0}`. This is the form of
`TauCeti.exists_contDiffOn_eqOn_inter_setOf_im_nonneg` for maps that also depend on a point of `E`,
such as the coefficients of a Cauchy-Riemann operator in a boundary chart. -/
theorem exists_contDiffOn_eqOn_inter_setOf_fst_im_nonneg [HasContDiffBump (ℝ × (ℝ × E))]
    {g : ℂ × E → G} {W : Set (ℂ × E)} (hW : IsOpen W)
    (hg : ContDiffOn ℝ k g (W ∩ {q | 0 ≤ q.1.im})) {q₀ : ℂ × E} (hq₀ : q₀ ∈ W ∩ {q | 0 ≤ q.1.im}) :
    ∃ T : Set (ℂ × E), IsOpen T ∧ q₀ ∈ T ∧ ∃ G' : ℂ × E → G, ContDiffOn ℝ k G' T ∧
      EqOn G' g ((W ∩ {q | 0 ≤ q.1.im}) ∩ T) := by
  rcases (mem_ofPred.1 hq₀.2).lt_or_eq with hpos | hzero
  · exact ⟨W ∩ {q | 0 < q.1.im},
      hW.inter (isOpen_lt continuous_const (Complex.continuous_im.comp continuous_fst)),
      ⟨hq₀.1, hpos⟩, g, hg.mono fun q hq => ⟨hq.1, (mem_ofPred.1 hq.2).le⟩, fun _ _ => rfl⟩
  · have hge : ContDiffOn ℝ k (g ∘ (imReProdEquiv E).symm)
        (HalfSpaceExtension.upperHalfSpace (ℝ × E) ∩ (imReProdEquiv E).symm ⁻¹' W) := by
      refine hg.comp (imReProdEquiv E).symm.contDiff.contDiffOn fun w hw => ⟨hw.2, ?_⟩
      simpa only [mem_ofPred_eq, im_fst_imReProdEquiv_symm] using
        HalfSpaceExtension.mem_upperHalfSpace.1 hw.1
    have hq₀W : ((0 : ℝ), (q₀.1.re, q₀.2)) ∈ (imReProdEquiv E).symm ⁻¹' W := by
      rw [mem_preimage, hzero, ← imReProdEquiv_apply, ContinuousLinearEquiv.symm_apply_apply]
      exact hq₀.1
    obtain ⟨G', hG', hGg⟩ := HalfSpaceExtension.exists_local_contDiff_extension_halfSpace k
      (g ∘ (imReProdEquiv E).symm) (hW.preimage (imReProdEquiv E).symm.continuous) hge _ hq₀W
    obtain ⟨T, hT, hTo, hq₀T⟩ := eventually_nhds_iff.1 hGg
    refine ⟨imReProdEquiv E ⁻¹' T, hTo.preimage (imReProdEquiv E).continuous, ?_,
      G' ∘ imReProdEquiv E, (hG'.comp (imReProdEquiv E).contDiff).contDiffOn, fun q hq => ?_⟩
    · rw [mem_preimage, imReProdEquiv_apply, ← hzero]
      exact hq₀T
    · simpa only [Function.comp_apply, ContinuousLinearEquiv.symm_apply_apply] using
        hT _ hq.2 (by simpa only [imReProdEquiv_apply] using mem_ofPred.1 hq.1.2)

end Product

/-- Near every point of a relatively open subset `Ω ∩ {z | 0 ≤ z.im}` of the closed upper
half-plane, a `Cᵏ` map on it agrees with a map that is `Cᵏ` on an open neighbourhood of the
point. At a point of the real axis the extension reflects across the axis. This is the case
`E = ℝ` of `TauCeti.exists_contDiffOn_eqOn_inter_setOf_fst_im_nonneg`, applied to `f ∘ Prod.fst`
and restricted to `ℂ × {0}`. -/
theorem exists_contDiffOn_eqOn_inter_setOf_im_nonneg {f : ℂ → F} {Ω : Set ℂ}
    (hΩ : IsOpen Ω) (hf : ContDiffOn ℝ k f (Ω ∩ {z | 0 ≤ z.im})) {x : ℂ}
    (hx : x ∈ Ω ∩ {z | 0 ≤ z.im}) :
    ∃ W : Set ℂ, IsOpen W ∧ x ∈ W ∧ ∃ g : ℂ → F, ContDiffOn ℝ k g W ∧
      EqOn g f ((Ω ∩ {z | 0 ≤ z.im}) ∩ W) := by
  have hfst : ContDiffOn ℝ k (f ∘ Prod.fst) ((Ω ×ˢ (univ : Set ℝ)) ∩ {q | 0 ≤ q.1.im}) :=
    hf.comp contDiffOn_fst fun q hq => ⟨hq.1.1, hq.2⟩
  obtain ⟨T, hTo, hxT, G', hG', hGf⟩ := exists_contDiffOn_eqOn_inter_setOf_fst_im_nonneg
    (hΩ.prod isOpen_univ) hfst (q₀ := (x, 0)) ⟨⟨hx.1, mem_univ _⟩, hx.2⟩
  exact ⟨{z | (z, (0 : ℝ)) ∈ T}, hTo.preimage (continuous_id.prodMk continuous_const), hxT,
    fun z => G' (z, 0), hG'.comp (contDiff_id.prodMk contDiff_const).contDiffOn fun _ hz => hz,
    fun z hz => hGf ⟨⟨⟨hz.1.1, mem_univ _⟩, hz.1.2⟩, hz.2⟩⟩

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
