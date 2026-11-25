/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.VectorBundle.FiniteDimensional
public import TauCeti.Topology.VectorBundle.Orientation.Cover
public import TauCeti.Topology.VectorBundle.Orientation.PositiveSection
public import TauCeti.Topology.VectorBundle.ZeroSection
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import TauCeti.LinearAlgebra.Orientation.Basis
import TauCeti.Topology.VectorBundle.Trivialization

/-!
# The nonzero vectors of a real line bundle

Let `E → B` be a real vector bundle whose model fibre `F` is a line, and let `E₀` be the
complement of its zero section (`TauCeti.zeroSectionCompl`). A nonzero vector `v` of a fibre
`E b` is a basis of that line, so it orients the fibre. This gives a map

`E₀ → Or(E)`, `v ↦ (b, [v])`

to the orientation double cover of `E` (`TauCeti.zeroSectionComplToOrientationCover`). It is
continuous, surjective and open, and its fibres are the open half-lines `{c v | c > 0}`, which
are connected: two nonzero vectors of a line give the same orientation exactly when one is a
positive multiple of the other (`TauCeti.orientation_basisSingleton_eq_iff`). So `E₀` is, up to
connectedness, the orientation double cover, and over a connected base it is connected exactly
when the bundle is not orientable
(`TauCeti.connectedSpace_zeroSectionCompl_iff_isEmpty_vectorBundleOrientation`). For a line
bundle, being orientable is the same as having a continuous section vanishing nowhere.

When the bundle is oriented by `o` over a connected base, `E₀` has exactly two connected
components, the positive vectors `{v | [v] = o}` and the negative vectors `{v | [v] = -o}`
(`TauCeti.connectedComponent_zeroSectionCompl_eq`): the positive vectors are the preimage of the
sheet of the orientation double cover given by `o`, which is a copy of the base.

For the contact line of a contact structure, `E₀` is the symplectization, and these statements
say that the symplectization of a coorientable contact structure on a connected manifold has two
components, while that of a contact structure which is not coorientable is connected.

## Main definitions

* `TauCeti.zeroSectionComplToOrientationCover`: the orientation `[v]` of the fibre given by a
  nonzero vector `v` of a line bundle.

## Main results

* `TauCeti.continuous_zeroSectionComplToOrientationCover`,
  `TauCeti.surjective_zeroSectionComplToOrientationCover`,
  `TauCeti.isOpenMap_zeroSectionComplToOrientationCover`: the map to the orientation double cover
  is a continuous open surjection.
* `TauCeti.isConnected_preimage_zeroSectionComplToOrientationCover_singleton`: its fibres are
  connected.
* `TauCeti.connectedSpace_zeroSectionCompl_iff_isEmpty_vectorBundleOrientation`: over a connected
  base, the nonzero vectors form a connected space exactly when the line bundle is not orientable.
* `TauCeti.connectedComponent_zeroSectionCompl_eq`: over a connected base, an orientation `o`
  splits the nonzero vectors into the two connected components `[v] = o` and `[v] = -o`.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §12 (the orientation double cover of a vector bundle).
-/

public section

noncomputable section

open Bundle Module Set Topology

namespace TauCeti

variable {B : Type*} [TopologicalSpace B] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type*} [TopologicalSpace (TotalSpace F E)] [∀ b, AddCommGroup (E b)]
  [∀ b, Module ℝ (E b)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E] [VectorBundle ℝ F E]

variable (F E) in
/-- The point `(b, [v])` of the orientation double cover of a real line bundle given by a nonzero
vector `v` of the fibre over `b`: the orientation of that fibre in which the basis `(v)` is
positive. -/
def zeroSectionComplToOrientationCover (hF : finrank ℝ F = 1) (v : zeroSectionCompl F E) :
    VectorBundleOrientationCover F E (Fin 1) :=
  ⟨(v : TotalSpace F E).proj, (FiniteDimensional.basisSingleton (Fin 1)
    ((VectorBundle.finrank_eq ℝ F E _).trans hF) (v : TotalSpace F E).snd
    (mem_zeroSectionCompl.1 v.property)).orientation⟩

variable (hF : finrank ℝ F = 1)

/-- The orientation given by a nonzero vector lies over the base point of the vector. -/
@[simp]
theorem proj_zeroSectionComplToOrientationCover (v : zeroSectionCompl F E) :
    (zeroSectionComplToOrientationCover F E hF v).proj = (v : TotalSpace F E).proj :=
  (rfl)

/-- The orientation given by a nonzero vector `v` is that of the one-vector basis `(v)`. -/
theorem zeroSectionComplToOrientationCover_apply (v : zeroSectionCompl F E) :
    zeroSectionComplToOrientationCover F E hF v =
      ⟨(v : TotalSpace F E).proj, (FiniteDimensional.basisSingleton (Fin 1)
        ((VectorBundle.finrank_eq ℝ F E _).trans hF) (v : TotalSpace F E).snd
        (mem_zeroSectionCompl.1 v.property)).orientation⟩ :=
  (rfl)

/-- Two nonzero vectors give the same point of the orientation double cover exactly when they lie
over the same point and one is a positive multiple of the other. -/
theorem zeroSectionComplToOrientationCover_eq_iff {b : B} {u w : E b} (hu : u ≠ 0) (hw : w ≠ 0) :
    zeroSectionComplToOrientationCover F E hF ⟨⟨b, w⟩, mem_zeroSectionCompl.2 hw⟩ =
        zeroSectionComplToOrientationCover F E hF ⟨⟨b, u⟩, mem_zeroSectionCompl.2 hu⟩ ↔
      ∃ c : ℝ, 0 < c ∧ w = c • u := by
  rw [zeroSectionComplToOrientationCover_apply, zeroSectionComplToOrientationCover_apply,
    VectorBundleOrientationCover.mk_eq_mk_iff]
  exact orientation_basisSingleton_eq_iff ((VectorBundle.finrank_eq ℝ F E b).trans hF) hu hw

/-- The map to the orientation double cover is continuous: the one-vector bases `(v)` vary
continuously with `v`. -/
theorem continuous_zeroSectionComplToOrientationCover :
    Continuous (zeroSectionComplToOrientationCover F E hF) :=
  VectorBundleOrientationCover.continuous_mk_basis_orientation
    (FiberBundle.continuous_proj F E |>.comp continuous_subtypeVal) _
    fun _ ↦ by
      simp only [FiniteDimensional.basisSingleton_apply]
      exact continuous_subtypeVal

/-- Every orientation of a fibre is that of a nonzero vector, or of its negative. -/
theorem surjective_zeroSectionComplToOrientationCover :
    Function.Surjective (zeroSectionComplToOrientationCover F E hF) := by
  rintro ⟨b, o⟩
  -- Any nonzero vector `u` of the fibre gives the orientation `o` or `-o`; in the second case
  -- `-u` gives `o`.
  have hb := (VectorBundle.finrank_eq ℝ F E b).trans hF
  have : Nontrivial (E b) := Module.nontrivial_of_finrank_eq_succ hb
  obtain ⟨u, hu⟩ := exists_ne (0 : E b)
  rcases (FiniteDimensional.basisSingleton (Fin 1) hb u hu).orientation_eq_or_eq_neg o with h | h
  · exact ⟨⟨⟨b, u⟩, mem_zeroSectionCompl.2 hu⟩,
      (VectorBundleOrientationCover.mk_eq_mk_iff).2 h.symm⟩
  · refine ⟨⟨⟨b, -u⟩, mem_zeroSectionCompl.2 (neg_ne_zero.2 hu)⟩,
      (VectorBundleOrientationCover.mk_eq_mk_iff).2 ?_⟩
    simp only [orientation_basisSingleton_neg, ← h]

/-- A linear trivialization `e` reads the orientation of a fibre given by a nonzero vector `u` as
the orientation of the model fibre given by the coordinate vector `(e u).2`. -/
private theorem mapOrientation_basisSingleton (e : Trivialization F (π F E)) [e.IsLinear ℝ]
    {b : B} (hb : b ∈ e.baseSet) {u : E b} (hu : u ≠ 0) {w : F} (hw : w ≠ 0)
    (huw : (e ⟨b, u⟩).2 = w) :
    e.mapOrientation (Fin 1) hb (FiniteDimensional.basisSingleton (Fin 1)
        ((VectorBundle.finrank_eq ℝ F E b).trans hF) u hu).orientation =
      (FiniteDimensional.basisSingleton (Fin 1) hF w hw).orientation := by
  rw [Trivialization.mapOrientation_apply, ← Basis.orientation_map]
  exact congrArg Basis.orientation <| Basis.eq_of_apply_eq fun i ↦ by
    simp [FiniteDimensional.basisSingleton_apply, huw]

/-- **The map to the orientation double cover is open.** Near the orientation given by a nonzero
vector `v`, the vectors with constant coordinate `(e v).2` in the preferred trivialization `e`
form a continuous local section of the map through `v`. -/
theorem isOpenMap_zeroSectionComplToOrientationCover :
    IsOpenMap (zeroSectionComplToOrientationCover F E hF) := by
  refine IsOpenMap.of_nhds_le fun v W hW ↦ ?_
  set e := trivializationAt F E (v : TotalSpace F E).proj
  have h₀ : (v : TotalSpace F E).proj ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' _
  set f₀ := (e v).2
  have hf₀ : f₀ ≠ 0 := (e.snd_apply_ne_zero_iff ℝ h₀).2 (mem_zeroSectionCompl.1 v.property)
  -- The local section `σ` through `v`, defined on the sheet of the orientation of `v`.
  let σ (p : VectorBundleOrientationCover F E (Fin 1)) : TotalSpace F E :=
    ⟨p.proj, e.symm p.proj f₀⟩
  have hσc : ContinuousAt σ (zeroSectionComplToOrientationCover F E hF v) :=
    ContinuousAt.comp_of_eq (g := fun b ↦ (⟨b, e.symm b f₀⟩ : TotalSpace F E))
      ((e.continuousOn_symm.comp (continuous_id.prodMk continuous_const).continuousOn
        fun _ hb ↦ ⟨hb, mem_univ _⟩).continuousAt (e.open_baseSet.mem_nhds h₀))
      VectorBundleOrientationCover.continuous_proj.continuousAt
      (proj_zeroSectionComplToOrientationCover hF v)
  have hσv : σ (zeroSectionComplToOrientationCover F E hF v) = v := by
    -- The base point of the orientation of `v` is that of `v`, by definition.
    change (⟨(v : TotalSpace F E).proj, e.symm _ (e v).2⟩ : TotalSpace F E) = v
    rw [e.symm_proj_apply _ h₀]
  obtain ⟨U, hU, hUW⟩ := (mem_nhds_subtype _ v _).1 hW
  set o₀ := e.mapOrientation (Fin 1) h₀ (zeroSectionComplToOrientationCover F E hF v).orientation
  have hsheet : VectorBundleOrientationCover.sheet e o₀ ∈
      𝓝 (zeroSectionComplToOrientationCover F E hF v) :=
    (VectorBundleOrientationCover.isOpen_sheet_trivializationAt _ o₀).mem_nhds
      (VectorBundleOrientationCover.mem_sheet_iff.2 ⟨h₀, rfl⟩)
  filter_upwards [hsheet, hσc.preimage_mem_nhds (hσv ▸ hU)] with p hps hpU
  obtain ⟨hp, hpo⟩ := VectorBundleOrientationCover.mem_sheet_iff.1 hps
  -- On the sheet, `σ p` is a nonzero vector whose orientation is `p`.
  have hσ₀ : e.symm p.proj f₀ ≠ 0 := (e.symm_apply_ne_zero_iff ℝ hp).2 hf₀
  have hW' : (⟨σ p, mem_zeroSectionCompl.2 hσ₀⟩ : zeroSectionCompl F E) ∈ _ := hUW hpU
  obtain ⟨b, o⟩ := p
  have hfp : zeroSectionComplToOrientationCover F E hF ⟨σ ⟨b, o⟩, mem_zeroSectionCompl.2 hσ₀⟩ =
      ⟨b, o⟩ := by
    refine (VectorBundleOrientationCover.mk_eq_mk_iff).2
      ((e.mapOrientation (Fin 1) hp).injective ?_)
    rw [hpo, mapOrientation_basisSingleton hF e hp hσ₀ hf₀ (by rw [e.apply_mk_symm hp])]
    exact (mapOrientation_basisSingleton hF e h₀ _ hf₀ rfl).symm
  rwa [mem_preimage, hfp] at hW'

/-- **The fibres of the map to the orientation double cover are connected.** The nonzero vectors
giving the orientation `(b, [u])` are the positive multiples `c u`, an open half-line. -/
theorem isConnected_preimage_zeroSectionComplToOrientationCover_singleton
    (p : VectorBundleOrientationCover F E (Fin 1)) :
    IsConnected (zeroSectionComplToOrientationCover F E hF ⁻¹' {p}) := by
  obtain ⟨⟨⟨b, u⟩, hu⟩, rfl⟩ := surjective_zeroSectionComplToOrientationCover hF p
  have hu' : u ≠ 0 := mem_zeroSectionCompl.1 hu
  have : ContinuousSMul ℝ (E b) := VectorBundle.continuousSMul ℝ F E b
  -- The fibre is the image of the line under `t ↦ eᵗ u`.
  let g (t : ℝ) : zeroSectionCompl F E :=
    ⟨⟨b, Real.exp t • u⟩, mem_zeroSectionCompl.2 (smul_ne_zero (Real.exp_pos t).ne' hu')⟩
  have hg : Continuous g :=
    ((FiberBundle.continuous_totalSpaceMk F E b).comp
      (Real.continuous_exp.smul continuous_const)).subtype_mk _
  convert isConnected_range hg using 1
  ext ⟨⟨b', w⟩, hw⟩
  simp only [mem_preimage, mem_singleton_iff, mem_range]
  constructor
  · intro h
    obtain rfl : b' = b := congrArg VectorBundleOrientationCover.proj h
    obtain ⟨c, hc, rfl⟩ :=
      (zeroSectionComplToOrientationCover_eq_iff hF hu' (mem_zeroSectionCompl.1 hw)).1 h
    exact ⟨Real.log c, by simp only [g, Real.exp_log hc]⟩
  · rintro ⟨t, ht⟩
    rw [← ht]
    exact (zeroSectionComplToOrientationCover_eq_iff hF hu'
      (smul_ne_zero (Real.exp_pos t).ne' hu')).2 ⟨_, Real.exp_pos t, rfl⟩

/-- The map to the orientation double cover is a quotient map. -/
theorem isQuotientMap_zeroSectionComplToOrientationCover :
    Topology.IsQuotientMap (zeroSectionComplToOrientationCover F E hF) :=
  (isOpenMap_zeroSectionComplToOrientationCover hF).isQuotientMap
    (continuous_zeroSectionComplToOrientationCover hF)
    (surjective_zeroSectionComplToOrientationCover hF)

include hF in
/-- **The nonzero vectors of a line bundle are connected exactly when it is not orientable.** Over
a connected base, the complement of the zero section of a real line bundle is connected exactly
when the bundle admits no orientation, that is, when its orientation double cover is connected. -/
theorem connectedSpace_zeroSectionCompl_iff_isEmpty_vectorBundleOrientation [ConnectedSpace B] :
    ConnectedSpace (zeroSectionCompl F E) ↔ IsEmpty (VectorBundleOrientation F E (Fin 1)) := by
  have hι : Fintype.card (Fin 1) = finrank ℝ F := by rw [Fintype.card_fin, hF]
  have : FiniteDimensional ℝ F := Module.finite_of_finrank_eq_succ hF
  rw [← not_nonempty_iff, VectorBundleOrientation.nonempty_iff_not_connectedSpace hι, not_not]
  refine ⟨fun _ ↦ (surjective_zeroSectionComplToOrientationCover hF).connectedSpace
    (continuous_zeroSectionComplToOrientationCover hF), fun _ ↦ ?_⟩
  rw [connectedSpace_iff_univ, ← preimage_univ]
  exact (isQuotientMap_zeroSectionComplToOrientationCover hF).isCoinducing
    |>.isConnected_preimage_of_isClosed
      (isConnected_preimage_zeroSectionComplToOrientationCover_singleton hF) isClosed_univ
      isConnected_univ

include hF in
/-- **The nonzero vectors of a line bundle are connected exactly when it has no nowhere-vanishing
section.** Over a connected normal paracompact base, the complement of the zero section of a real
line bundle is connected exactly when the bundle has no continuous section vanishing nowhere. -/
theorem connectedSpace_zeroSectionCompl_iff_not_exists_continuous_section_ne_zero
    [ConnectedSpace B] [NormalSpace B] [ParacompactSpace B] :
    ConnectedSpace (zeroSectionCompl F E) ↔
      ¬ ∃ s : ∀ b, E b, Continuous (fun b ↦ TotalSpace.mk' F b (s b)) ∧ ∀ b, s b ≠ 0 := by
  have hι : Fintype.card (Fin 1) = finrank ℝ F := by rw [Fintype.card_fin, hF]
  rw [connectedSpace_zeroSectionCompl_iff_isEmpty_vectorBundleOrientation hF, ← not_nonempty_iff]
  refine not_congr ⟨fun ⟨o⟩ ↦ o.exists_continuous_section_ne_zero hι, fun ⟨s, hs, hs₀⟩ ↦
    ⟨VectorBundleOrientation.ofContinuousNonvanishingSection
      (fun b ↦ (VectorBundle.finrank_eq ℝ F E b).trans hF) hs hs₀⟩⟩

/-- **The two components of the nonzero vectors of an oriented line bundle.** Over a preconnected
base, for an orientation `o` of a real line bundle, the connected component of a nonzero vector `v`
with `[v] = o` consists of the nonzero vectors `w` with `[w] = o`. Applied to `-o`, the other
component consists of the `w` with `[w] = -o`. -/
theorem connectedComponent_zeroSectionCompl_eq [PreconnectedSpace B]
    (o : VectorBundleOrientation F E (Fin 1)) {v : zeroSectionCompl F E}
    (hv : (zeroSectionComplToOrientationCover F E hF v).orientation =
      o (zeroSectionComplToOrientationCover F E hF v).proj) :
    connectedComponent v = {w | (zeroSectionComplToOrientationCover F E hF w).orientation =
      o (zeroSectionComplToOrientationCover F E hF w).proj} := by
  have hι : Fintype.card (Fin 1) = finrank ℝ F := by rw [Fintype.card_fin, hF]
  have : ConnectedSpace B := { toNonempty := ⟨(v : TotalSpace F E).proj⟩ }
  -- In the orientation double cover, the sheet of `o` is clopen and a copy of the base.
  set P := {p : VectorBundleOrientationCover F E (Fin 1) | p.orientation = o p.proj}
  have hrange : range (o.coverSection hι) = P := by
    refine (range_subset_iff.2 fun b ↦ by
      rw [mem_ofPred_eq, VectorBundleOrientation.coverSection_apply]).antisymm
      fun p (hp : p.orientation = o p.proj) ↦ ⟨p.proj, ?_⟩
    rw [VectorBundleOrientation.coverSection_apply]
    exact (VectorBundleOrientationCover.mk_eq_mk_iff).2 hp.symm
  have hPconn : IsPreconnected P :=
    hrange ▸ (isConnected_range (o.coverSection hι).continuous).isPreconnected
  have hP : connectedComponent (zeroSectionComplToOrientationCover F E hF v) = P :=
    ((VectorBundleOrientation.isClopen_setOf_orientation_eq hι o).connectedComponent_subset
      hv).antisymm (hPconn.subset_connectedComponent hv)
  rw [← (isQuotientMap_zeroSectionComplToOrientationCover hF).isCoinducing
    |>.preimage_connectedComponent
      (isConnected_preimage_zeroSectionComplToOrientationCover_singleton hF), hP,
    preimage_ofPred_eq]

end TauCeti
