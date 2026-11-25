/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.VectorBundle.FiniteDimensional
public import TauCeti.Topology.VectorBundle.Orientation.Cover
public import TauCeti.Topology.VectorBundle.Trivialization
public import TauCeti.Topology.VectorBundle.ZeroSection
import TauCeti.LinearAlgebra.Orientation.Basis
import TauCeti.Topology.VectorBundle.Smul

/-!
# The nonzero vectors of a line bundle and its orientation double cover

Let `E → B` be a real vector bundle of rank one and `E₀` the complement of its zero section
(`TauCeti.zeroSectionCompl`). A nonzero vector `v` of a fibre orients that fibre, by the one-vector
basis `(v)`. This gives a continuous map over `B` from `E₀` to the orientation double cover of `E`
(`TauCeti.zeroSectionComplOrientation`), which carries `v ↦ -v` to the deck involution
(`TauCeti.zeroSectionComplOrientation_neg`). Two nonzero vectors have the same image exactly when
one is a positive multiple of the other (`TauCeti.zeroSectionComplOrientation_eq_iff`), so the
fibres of the map are the open half-lines of `E`, which are connected.

The map is a continuous open surjection (`TauCeti.isOpenMap_zeroSectionComplOrientation`): near
the orientation of `v`, the vector over each point whose coordinate in the preferred
trivialization is the coordinate of `v` is a continuous local section through `v`. So it is a
quotient map with connected fibres, and it identifies the connected components of `E₀` with those
of the orientation double cover
(`TauCeti.preimage_connectedComponent_zeroSectionComplOrientation`). In particular `E₀` is
connected exactly when the orientation double cover is
(`TauCeti.connectedSpace_zeroSectionCompl_iff`), and over a connected base a line bundle is
orientable exactly when the complement of its zero section is disconnected
(`TauCeti.nonempty_vectorBundleOrientation_iff_not_connectedSpace_zeroSectionCompl`).

Unlike the identification of the unit sphere bundle with the orientation double cover
(`TauCeti.sphereBundleOrientationHomeomorph`), no fibre metric is needed.

## Main results

* `TauCeti.zeroSectionComplOrientation`: the orientation map from the nonzero vectors of a line
  bundle to its orientation double cover.
* `TauCeti.isQuotientMap_zeroSectionComplOrientation`: it is a quotient map, with connected fibres
  (`TauCeti.isConnected_preimage_zeroSectionComplOrientation`).
* `TauCeti.nonempty_vectorBundleOrientation_iff_not_connectedSpace_zeroSectionCompl`: over a
  connected base, a line bundle is orientable exactly when the complement of its zero section is
  disconnected.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §12 (the orientation double cover of a vector bundle).
* John M. Lee, *Introduction to Smooth Manifolds*, second edition, Graduate Texts in
  Mathematics 218, Springer, 2013, Chapter 15, "The Orientation Covering".
-/

public section

noncomputable section

open Bundle Function Module Set Topology

namespace TauCeti

variable {B : Type*} [TopologicalSpace B] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type*} [TopologicalSpace (TotalSpace F E)] [∀ b, AddCommGroup (E b)]
  [∀ b, Module ℝ (E b)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E] [VectorBundle ℝ F E]
  (hF : finrank ℝ F = 1)

/-- In rank one a nonzero vector `v` orients its fibre: the map from the nonzero vectors of a line
bundle to its orientation double cover sending `v` to the orientation of its fibre in which `v`
is positive, that is, the orientation of the one-vector basis `(v)`. -/
def zeroSectionComplOrientation :
    C(zeroSectionCompl F E, VectorBundleOrientationCover F E (Fin 1)) where
  toFun v := ⟨(v : TotalSpace F E).proj,
    (FiniteDimensional.basisSingleton (Fin 1) ((VectorBundle.finrank_eq ℝ F E _).trans hF)
      (v : TotalSpace F E).snd (mem_zeroSectionCompl.1 v.property)).orientation⟩
  continuous_toFun :=
    VectorBundleOrientationCover.continuous_mk_basis_orientation
      ((FiberBundle.continuous_proj F E).comp continuous_subtypeVal) _ fun i ↦ by
        simp only [FiniteDimensional.basisSingleton_apply]
        exact continuous_subtypeVal

/-- The orientation map sends a nonzero vector `v` over `b` to the orientation of `E_b` given by
the basis `(v)`. -/
theorem zeroSectionComplOrientation_apply (v : zeroSectionCompl F E) :
    zeroSectionComplOrientation hF v = ⟨(v : TotalSpace F E).proj,
      (FiniteDimensional.basisSingleton (Fin 1) ((VectorBundle.finrank_eq ℝ F E _).trans hF)
        (v : TotalSpace F E).snd (mem_zeroSectionCompl.1 v.property)).orientation⟩ :=
  (rfl)

/-- The orientation given by a nonzero vector lies over the base point of the vector. -/
@[simp]
theorem proj_zeroSectionComplOrientation (v : zeroSectionCompl F E) :
    (zeroSectionComplOrientation hF v).proj = (v : TotalSpace F E).proj :=
  (rfl)

/-- The opposite vector gives the opposite orientation. -/
@[simp]
theorem zeroSectionComplOrientation_neg {b : B} {x : E b} (hx : x ≠ 0) :
    zeroSectionComplOrientation hF ⟨⟨b, -x⟩, mem_zeroSectionCompl.2 (neg_ne_zero.2 hx)⟩ =
      VectorBundleOrientationCover.deck
        (zeroSectionComplOrientation hF ⟨⟨b, x⟩, mem_zeroSectionCompl.2 hx⟩) := by
  rw [VectorBundleOrientationCover.deck_apply, zeroSectionComplOrientation_apply,
    zeroSectionComplOrientation_apply]
  exact VectorBundleOrientationCover.mk_eq_mk_iff.2 (orientation_basisSingleton_neg _ _)

/-- A positive multiple of a nonzero vector gives the same orientation. -/
@[simp]
theorem zeroSectionComplOrientation_smul {b : B} {x : E b} (hx : x ≠ 0) {c : ℝ} (hc : 0 < c) :
    zeroSectionComplOrientation hF ⟨⟨b, c • x⟩, mem_zeroSectionCompl.2 (smul_ne_zero hc.ne' hx)⟩ =
      zeroSectionComplOrientation hF ⟨⟨b, x⟩, mem_zeroSectionCompl.2 hx⟩ := by
  rw [zeroSectionComplOrientation_apply, zeroSectionComplOrientation_apply]
  exact VectorBundleOrientationCover.mk_eq_mk_iff.2 (orientation_basisSingleton_smul_of_pos _ hc _)

/-- Read in a linear trivialization `e`, the orientation given by a nonzero vector `v` is the
orientation of the one-vector basis `(e v)` of the model fibre. -/
theorem mapOrientation_orientation_zeroSectionComplOrientation (e : Trivialization F (π F E))
    [e.IsLinear ℝ] {v : zeroSectionCompl F E}
    (hv : (zeroSectionComplOrientation hF v).proj ∈ e.baseSet) :
    e.mapOrientation (Fin 1) hv (zeroSectionComplOrientation hF v).orientation =
      (FiniteDimensional.basisSingleton (Fin 1) hF (e v).2
        ((e.snd_apply_ne_zero_iff ℝ (proj_zeroSectionComplOrientation hF v ▸ hv)).2
          (mem_zeroSectionCompl.1 v.property))).orientation :=
  e.mapOrientation_orientation_basisSingleton hv _ hF _ _

/-- Every orientation of a fibre is given by a nonzero vector. -/
theorem zeroSectionComplOrientation_surjective :
    Surjective (zeroSectionComplOrientation (E := E) hF) := by
  intro p
  have : Nontrivial (E p.proj) :=
    Module.nontrivial_of_finrank_eq_succ ((VectorBundle.finrank_eq ℝ F E p.proj).trans hF)
  obtain ⟨x, hx⟩ := exists_ne (0 : E p.proj)
  have hp : (zeroSectionComplOrientation hF ⟨⟨p.proj, x⟩, mem_zeroSectionCompl.2 hx⟩).proj =
      p.proj := rfl
  rcases VectorBundleOrientationCover.eq_or_eq_deck ((Fintype.card_fin 1).trans hF.symm) hp
    with h | h
  · exact ⟨_, h⟩
  · exact ⟨_, by
      rw [zeroSectionComplOrientation_neg hF hx, h, VectorBundleOrientationCover.deck_deck]⟩

/-- **The fibres of the orientation map are the open half-lines.** Two nonzero vectors give the
same orientation exactly when the first is a positive multiple of the second. -/
theorem zeroSectionComplOrientation_eq_iff {v w : zeroSectionCompl F E} :
    zeroSectionComplOrientation hF w = zeroSectionComplOrientation hF v ↔
      ∃ c : ℝ, 0 < c ∧
        (w : TotalSpace F E) = ⟨(v : TotalSpace F E).proj, c • (v : TotalSpace F E).snd⟩ := by
  obtain ⟨⟨b, x⟩, hx⟩ := v
  refine ⟨fun h ↦ ?_, fun ⟨c, hc, h⟩ ↦ ?_⟩
  · obtain ⟨⟨b', y⟩, hy⟩ := w
    obtain rfl : b = b' := (congrArg VectorBundleOrientationCover.proj h).symm
    rw [zeroSectionComplOrientation_apply, zeroSectionComplOrientation_apply] at h
    have ho := VectorBundleOrientationCover.mk_eq_mk_iff.1 h
    have hE := (VectorBundle.finrank_eq ℝ F E b).trans hF
    set β := FiniteDimensional.basisSingleton (Fin 1) hE x (mem_zeroSectionCompl.1 hx)
    set β' := FiniteDimensional.basisSingleton (Fin 1) hE y (mem_zeroSectionCompl.1 hy)
    -- The vector `y` is `c • x` with `c = β.det β'`, positive since `(x)` and `(y)` have the
    -- same orientation.
    have hc : 0 < β.det β' := (β.orientation_eq_iff_det_pos β').1 ho.symm
    have hβ' : β' default = β.det β' • β default := by
      rw [Basis.det_apply, Matrix.det_unique, Basis.toMatrix_apply]
      simpa using (β.sum_repr (β' default)).symm
    simp only [β, β', FiniteDimensional.basisSingleton_apply] at hβ'
    exact ⟨β.det β', hc, congrArg (TotalSpace.mk b) hβ'⟩
  · obtain rfl : w = ⟨⟨b, c • x⟩, mem_zeroSectionCompl.2
        (smul_ne_zero hc.ne' (mem_zeroSectionCompl.1 hx))⟩ := Subtype.ext h
    exact zeroSectionComplOrientation_smul hF (mem_zeroSectionCompl.1 hx) hc

/-- The fibres of the orientation map are connected: the fibre through `v` is the open half-line of
the positive multiples of `v`. -/
theorem isConnected_preimage_zeroSectionComplOrientation
    (p : VectorBundleOrientationCover F E (Fin 1)) :
    IsConnected (zeroSectionComplOrientation hF ⁻¹' {p}) := by
  obtain ⟨v, rfl⟩ := zeroSectionComplOrientation_surjective hF p
  let g (c : ℝ) : TotalSpace F E :=
    TotalSpace.mk' F (v : TotalSpace F E).proj (c • (v : TotalSpace F E).snd)
  have hg : Continuous g := continuous_id.smul_totalSpace continuous_const
  have himage : ((↑) : zeroSectionCompl F E → TotalSpace F E) ''
      (zeroSectionComplOrientation hF ⁻¹' {zeroSectionComplOrientation hF v}) = g '' Ioi 0 := by
    ext z
    simp only [mem_image, mem_preimage, mem_singleton_iff, zeroSectionComplOrientation_eq_iff,
      mem_Ioi, g, TotalSpace.mk']
    refine ⟨fun ⟨w, ⟨c, hc, hw⟩, hwz⟩ ↦ ⟨c, hc, hwz ▸ hw.symm⟩, fun ⟨c, hc, hcz⟩ ↦ ?_⟩
    refine ⟨⟨z, ?_⟩, ⟨c, hc, hcz.symm⟩, rfl⟩
    rw [← hcz]
    exact mem_zeroSectionCompl.2 (smul_ne_zero hc.ne' (mem_zeroSectionCompl.1 v.property))
  refine ⟨(zeroSectionComplOrientation_surjective hF).nonempty_preimage.2 (singleton_nonempty _),
    ?_⟩
  rw [← IsInducing.subtypeVal.isPreconnected_image, himage]
  exact (isConnected_Ioi.image g hg.continuousOn).isPreconnected

/-- The orientation map from the nonzero vectors of a line bundle to its orientation double cover
is an open map. -/
theorem isOpenMap_zeroSectionComplOrientation :
    IsOpenMap (zeroSectionComplOrientation (E := E) hF) := by
  classical
  refine IsOpenMap.of_sections fun v ↦ ?_
  -- Near the orientation of `v`, the vector over each point whose coordinate in the preferred
  -- trivialization `e` at the base point of `v` is the coordinate `w` of `v` is a continuous
  -- local section through `v`. Elsewhere choose any preimage.
  set e := trivializationAt F E (v : TotalSpace F E).proj
  have hv : (v : TotalSpace F E).proj ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' _
  set w : F := (e v).2
  have hw : w ≠ 0 := (e.snd_apply_ne_zero_iff ℝ hv).2 (mem_zeroSectionCompl.1 v.property)
  let σ (p : VectorBundleOrientationCover F E (Fin 1)) : TotalSpace F E :=
    TotalSpace.mk' F p.proj (e.symm p.proj w)
  let g (p : VectorBundleOrientationCover F E (Fin 1)) : zeroSectionCompl F E :=
    if h : ∃ hσ : σ p ∈ zeroSectionCompl F E, zeroSectionComplOrientation hF ⟨σ p, hσ⟩ = p
    then ⟨σ p, h.1⟩ else surjInv (zeroSectionComplOrientation_surjective hF) p
  have hg : RightInverse g (zeroSectionComplOrientation hF) := fun p ↦ by
    by_cases h : ∃ hσ : σ p ∈ zeroSectionCompl F E, zeroSectionComplOrientation hF ⟨σ p, hσ⟩ = p
    · simpa only [g, h, ↓reduceDIte] using h.2
    · simpa only [g, h, ↓reduceDIte] using surjInv_eq _ p
  -- On the sheet of `e` through the orientation of `v`, the local section is a section: both
  -- orientations read in `e` as the orientation of the basis `(w)` of `F`.
  set o := e.mapOrientation (Fin 1) hv (zeroSectionComplOrientation hF v).orientation
  have hsheet (p) (hp : p ∈ VectorBundleOrientationCover.sheet e o) :
      ∃ hσ : σ p ∈ zeroSectionCompl F E, zeroSectionComplOrientation hF ⟨σ p, hσ⟩ = p := by
    obtain ⟨b, ob⟩ := p
    obtain ⟨hb, hbo⟩ := VectorBundleOrientationCover.mem_sheet_iff.1 hp
    have hσ : σ ⟨b, ob⟩ ∈ zeroSectionCompl F E :=
      mem_zeroSectionCompl.2 ((e.symm_apply_ne_zero_iff ℝ hb).2 hw)
    have ho : o = (FiniteDimensional.basisSingleton (Fin 1) hF w hw).orientation :=
      mapOrientation_orientation_zeroSectionComplOrientation hF e hv
    have hσo : e.mapOrientation (Fin 1) hb
        (zeroSectionComplOrientation hF ⟨σ ⟨b, ob⟩, hσ⟩).orientation =
          (FiniteDimensional.basisSingleton (Fin 1) hF w hw).orientation := by
      refine (mapOrientation_orientation_zeroSectionComplOrientation hF e
        (v := ⟨σ ⟨b, ob⟩, hσ⟩) hb).trans ?_
      simp only [σ, TotalSpace.mk', e.apply_mk_symm hb]
    refine ⟨hσ, ?_⟩
    rw [zeroSectionComplOrientation_apply]
    exact VectorBundleOrientationCover.mk_eq_mk_iff.2
      ((e.mapOrientation (Fin 1) hb).injective (hσo.trans (ho.symm.trans hbo.symm)))
  have hv₀ : zeroSectionComplOrientation hF v ∈ VectorBundleOrientationCover.sheet e o :=
    VectorBundleOrientationCover.mem_sheet_iff.2 ⟨hv, rfl⟩
  have hgσ : ∀ᶠ p in 𝓝 (zeroSectionComplOrientation hF v),
      σ p = ((g p : zeroSectionCompl F E) : TotalSpace F E) := by
    filter_upwards [(VectorBundleOrientationCover.isOpen_sheet ((Fintype.card_fin 1).trans hF.symm)
      e o).mem_nhds hv₀] with p hp
    simp only [g, hsheet p hp, ↓reduceDIte]
  have hσc : ContinuousAt σ (zeroSectionComplOrientation hF v) :=
    (e.continuousOn_symm.continuousAt (x := ((v : TotalSpace F E).proj, w))
      (prod_mem_nhds (e.open_baseSet.mem_nhds hv) Filter.univ_mem)).comp_of_eq
      (VectorBundleOrientationCover.continuous_proj.prodMk continuous_const).continuousAt rfl
  refine ⟨g, IsInducing.subtypeVal.continuousAt_iff.2 (hσc.congr hgσ), Subtype.ext ?_, hg⟩
  -- At the orientation of `v`, the local section returns `v` itself.
  rw [← hgσ.self_of_nhds]
  exact congrArg (TotalSpace.mk' F _) (e.symm_proj_apply _ hv)

/-- The orientation map from the nonzero vectors of a line bundle to its orientation double cover
is a quotient map. -/
theorem isQuotientMap_zeroSectionComplOrientation :
    IsQuotientMap (zeroSectionComplOrientation (E := E) hF) :=
  (isOpenMap_zeroSectionComplOrientation hF).isQuotientMap
    (zeroSectionComplOrientation hF).continuous (zeroSectionComplOrientation_surjective hF)

/-- **The components of the nonzero vectors of a line bundle.** The connected component of a
nonzero vector `v` consists of the nonzero vectors whose orientations lie in the connected
component of the orientation of `v` in the orientation double cover. -/
theorem preimage_connectedComponent_zeroSectionComplOrientation (v : zeroSectionCompl F E) :
    zeroSectionComplOrientation hF ⁻¹' connectedComponent (zeroSectionComplOrientation hF v) =
      connectedComponent v :=
  (isQuotientMap_zeroSectionComplOrientation hF).isCoinducing.preimage_connectedComponent
    (isConnected_preimage_zeroSectionComplOrientation hF) v

include hF in
/-- The nonzero vectors of a line bundle form a connected space exactly when its orientation
double cover is connected. -/
theorem connectedSpace_zeroSectionCompl_iff :
    ConnectedSpace (zeroSectionCompl F E) ↔
      ConnectedSpace (VectorBundleOrientationCover F E (Fin 1)) := by
  refine ⟨fun _ ↦ (zeroSectionComplOrientation_surjective hF).connectedSpace
    (zeroSectionComplOrientation hF).continuous, fun h ↦ ?_⟩
  rw [connectedSpace_iff_univ] at h ⊢
  simpa using
    (isQuotientMap_zeroSectionComplOrientation hF).isCoinducing.isConnected_preimage_of_isClosed
      (isConnected_preimage_zeroSectionComplOrientation hF) isClosed_univ h

include hF in
/-- **A line bundle is orientable exactly when the complement of its zero section is
disconnected.** Over a connected base, a real vector bundle of rank one has an orientation exactly
when its nonzero vectors do not form a connected space. -/
theorem nonempty_vectorBundleOrientation_iff_not_connectedSpace_zeroSectionCompl
    [ConnectedSpace B] :
    Nonempty (VectorBundleOrientation F E (Fin 1)) ↔ ¬ ConnectedSpace (zeroSectionCompl F E) := by
  have : FiniteDimensional ℝ F := FiniteDimensional.of_finrank_eq_succ hF
  rw [VectorBundleOrientation.nonempty_iff_not_connectedSpace
    ((Fintype.card_fin 1).trans hF.symm), connectedSpace_zeroSectionCompl_iff hF]

end TauCeti
