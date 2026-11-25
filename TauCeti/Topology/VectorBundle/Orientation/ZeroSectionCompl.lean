/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.PathConnected
public import TauCeti.Analysis.Convex.Orientation
public import TauCeti.Topology.VectorBundle.Orientation.Cover
public import TauCeti.Topology.VectorBundle.Trivialization
public import TauCeti.Topology.VectorBundle.ZeroSection

/-!
# The nonzero vectors of a real line bundle

Let `E → B` be a real vector bundle of rank one, a line bundle, and let `E₀ = E ∖ 0` be the
complement of its zero section (`TauCeti.zeroSectionCompl`). A nonzero vector `v` of the fibre
over `b` orients that fibre, by the one-vector basis `(v)`, so it defines a point of the
orientation double cover of `E` (`TauCeti.zeroSectionComplOrientation`). This map
`E₀ → Or(E)` is continuous, open and surjective, and its fibres are the open half-lines of
positive vectors of the oriented fibres, which are convex and hence connected. A quotient map with
connected fibres induces a bijection on connected components, so the connected components of `E₀`
are the preimages of the components of the orientation cover
(`TauCeti.preimage_connectedComponent_zeroSectionComplOrientation`).

In particular `E₀` is connected exactly when the orientation cover is
(`TauCeti.connectedSpace_zeroSectionCompl_iff`). Over a connected base the orientation cover is
connected exactly when the bundle is not orientable
(`TauCeti.VectorBundleOrientation.nonempty_iff_not_connectedSpace`), so the nonzero vectors of a
line bundle over a connected base form a connected space exactly when the bundle admits no
orientation (`TauCeti.connectedSpace_zeroSectionCompl_iff_isEmpty`). For the Möbius line bundle
over the circle, `E₀` is a single open annulus; for the trivial line bundle `B × ℝ` over a
connected base, it is `B × (ℝ ∖ 0)`, with two components.

This is the topological input for the components of the symplectization of a contact structure,
the complement of the zero section in its annihilator line.

## Main declarations

* `TauCeti.zeroSectionComplOrientation`: the orientation of the fibre through a nonzero vector,
  as a point of the orientation double cover.
* `TauCeti.isQuotientMap_zeroSectionComplOrientation`: this map is a quotient map.
* `TauCeti.isConnected_preimage_zeroSectionComplOrientation`: its fibres are connected.
* `TauCeti.preimage_connectedComponent_zeroSectionComplOrientation`: the components of `E₀` are
  the preimages of the components of the orientation cover.
* `TauCeti.connectedSpace_zeroSectionCompl_iff_isEmpty`: over a connected base, `E₀` is connected
  exactly when the line bundle is not orientable.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §12 (the orientation double cover of a vector bundle).
* John M. Lee, *Introduction to Smooth Manifolds*, second edition, Graduate Texts in
  Mathematics 218, Springer, 2013, Chapter 15, "The Orientation Covering".
-/

public section

noncomputable section

open Bundle Module Set Topology

namespace TauCeti

variable {B : Type*} [TopologicalSpace B] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type*} [TopologicalSpace (TotalSpace F E)] [∀ b, AddCommGroup (E b)]
  [∀ b, Module ℝ (E b)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E] [VectorBundle ℝ F E]

/-- The **orientation through a nonzero vector** of a real line bundle: a nonzero vector `v` over
`b` orients the fibre over `b` by the one-vector basis `(v)`, a point of the orientation double
cover. -/
def zeroSectionComplOrientation (hF : finrank ℝ F = 1) (v : zeroSectionCompl F E) :
    VectorBundleOrientationCover F E (Fin 1) :=
  ⟨v.val.proj, (FiniteDimensional.basisSingleton (Fin 1)
    ((VectorBundle.continuousLinearEquivAt ℝ F E v.val.proj).toLinearEquiv.finrank_eq.trans hF)
    v.val.snd (mem_zeroSectionCompl.1 v.prop)).orientation⟩

variable (hF : finrank ℝ F = 1)

/-- The orientation through a nonzero vector `v` over `b` is the orientation of the fibre over `b`
given by the one-vector basis `(v)`. -/
theorem zeroSectionComplOrientation_apply (v : zeroSectionCompl F E) :
    zeroSectionComplOrientation hF v =
      ⟨v.val.proj, (FiniteDimensional.basisSingleton (Fin 1)
        ((VectorBundle.continuousLinearEquivAt ℝ F E v.val.proj).toLinearEquiv.finrank_eq.trans hF)
        v.val.snd (mem_zeroSectionCompl.1 v.prop)).orientation⟩ :=
  (rfl)

/-- The orientation through a nonzero vector lies over the base point of that vector. -/
@[simp]
theorem proj_zeroSectionComplOrientation (v : zeroSectionCompl F E) :
    (zeroSectionComplOrientation hF v).proj = v.val.proj := by
  rw [zeroSectionComplOrientation_apply]

/-- A nonzero vector `w` over `b` lies over the point `⟨b, o⟩` of the orientation double cover
exactly when it is a positive vector of the oriented line `(E b, o)`: some one-vector basis with
vector `w` has orientation `o`. -/
theorem zeroSectionComplOrientation_eq_mk_iff {b : B} {w : E b} (hw : w ≠ 0)
    {o : Orientation ℝ (E b) (Fin 1)} :
    zeroSectionComplOrientation hF ⟨⟨b, w⟩, mem_zeroSectionCompl.2 hw⟩ = ⟨b, o⟩ ↔
      ∃ β : Basis (Fin 1) ℝ (E b), β default = w ∧ β.orientation = o := by
  rw [zeroSectionComplOrientation_apply, VectorBundleOrientationCover.mk_eq_mk_iff]
  refine ⟨fun h ↦ ⟨_, FiniteDimensional.basisSingleton_apply _ _ _ _ _, h⟩, ?_⟩
  rintro ⟨β, hβ, rfl⟩
  -- A basis indexed by `Fin 1` is determined by its vector.
  congr 1
  exact Basis.eq_of_apply_eq fun i ↦ by
    rw [Subsingleton.elim i default, hβ, FiniteDimensional.basisSingleton_apply]

/-- The orientation through a nonzero vector depends continuously on the vector. -/
theorem continuous_zeroSectionComplOrientation :
    Continuous (zeroSectionComplOrientation (E := E) hF) :=
  VectorBundleOrientationCover.continuous_mk_basis_orientation
    ((FiberBundle.continuous_proj F E).comp continuous_subtypeVal) _ fun _ ↦ by
      simp only [FiniteDimensional.basisSingleton_apply]
      exact continuous_subtypeVal

/-- Every orientation of every fibre of a line bundle is the orientation through some nonzero
vector. -/
theorem surjective_zeroSectionComplOrientation :
    Function.Surjective (zeroSectionComplOrientation (E := E) hF) := by
  rintro ⟨b, o⟩
  have hb := (VectorBundle.continuousLinearEquivAt ℝ F E b).toLinearEquiv.finrank_eq.trans hF
  have : FiniteDimensional ℝ (E b) := Module.finite_of_finrank_eq_succ hb
  let β := o.someBasis (by rw [hb, Fintype.card_fin])
  exact ⟨⟨⟨b, β default⟩, mem_zeroSectionCompl.2 (β.ne_zero default)⟩,
    (zeroSectionComplOrientation_eq_mk_iff hF (β.ne_zero default)).2
      ⟨β, rfl, o.someBasis_orientation _⟩⟩

/-- Read in a linear trivialization `e`, the orientation of a one-vector basis `(w)` of a fibre over
the base set of `e` is the orientation of the one-vector basis `(f)` of the model fibre, `f` being
the coordinate of `w`. -/
private theorem mapOrientation_orientation_basisSingleton (e : Trivialization F (π F E))
    [e.IsLinear ℝ] {b : B} (hb : b ∈ e.baseSet) {w : E b} (hw : w ≠ 0) {f : F} (hf : f ≠ 0)
    (hwf : (e ⟨b, w⟩).snd = f) :
    e.mapOrientation (Fin 1) hb
        (FiniteDimensional.basisSingleton (Fin 1)
          ((VectorBundle.continuousLinearEquivAt ℝ F E b).toLinearEquiv.finrank_eq.trans hF) w
          hw).orientation =
      (FiniteDimensional.basisSingleton (Fin 1) hF f hf).orientation := by
  rw [Trivialization.mapOrientation_apply, ← Basis.orientation_map]
  congr 1
  exact Basis.eq_of_apply_eq fun i ↦ by
    simp [FiniteDimensional.basisSingleton_apply, hwf]

/-- Near the orientation through a nonzero vector `v`, the orientation map has a continuous section
through `v`: in the preferred trivialization `e` at the base point of `v`, send a point of the
sheet of the orientation of `v` to the vector over its base point with the coordinate of `v`. -/
private theorem exists_continuousOn_section (v : zeroSectionCompl F E) :
    ∃ U ∈ 𝓝 (zeroSectionComplOrientation hF v), ∃ s : VectorBundleOrientationCover F E (Fin 1) →
      zeroSectionCompl F E, ContinuousOn s U ∧ s (zeroSectionComplOrientation hF v) = v ∧
        ∀ p ∈ U, zeroSectionComplOrientation hF (s p) = p := by
  classical
  have : FiniteDimensional ℝ F := Module.finite_of_finrank_eq_succ hF
  have hι : Fintype.card (Fin 1) = finrank ℝ F := by rw [hF, Fintype.card_fin]
  set e := trivializationAt F E v.val.proj
  have hv : v.val.proj ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' _
  -- The coordinate `f` of `v` in `e` is a nonzero vector of the model fibre, and the orientation
  -- of `v` reads in `e` as the orientation of `(f)`.
  set f := (e v.val).snd
  have hf : f ≠ 0 := (e.snd_apply_ne_zero_iff ℝ hv).2 (mem_zeroSectionCompl.1 v.prop)
  have hvf :=
    mapOrientation_orientation_basisSingleton hF e hv (mem_zeroSectionCompl.1 v.prop) hf rfl
  set S := VectorBundleOrientationCover.sheet e
    (FiniteDimensional.basisSingleton (Fin 1) hF f hf).orientation
  have hne {b : B} (hb : b ∈ e.baseSet) : e.symm b f ≠ 0 := (e.symm_apply_ne_zero_iff ℝ hb).2 hf
  let s (p : VectorBundleOrientationCover F E (Fin 1)) : zeroSectionCompl F E :=
    if hp : p.proj ∈ e.baseSet then ⟨⟨p.proj, e.symm p.proj f⟩, mem_zeroSectionCompl.2 (hne hp)⟩
    else v
  have hs {p : VectorBundleOrientationCover F E (Fin 1)} (hp : p.proj ∈ e.baseSet) :
      s p = ⟨⟨p.proj, e.symm p.proj f⟩, mem_zeroSectionCompl.2 (hne hp)⟩ := by
    simp only [s, hp, ↓reduceDIte]
  have hvS : zeroSectionComplOrientation hF v ∈ S := by
    rw [zeroSectionComplOrientation_apply]
    exact VectorBundleOrientationCover.mem_sheet_iff.2 ⟨hv, hvf⟩
  refine ⟨S, (VectorBundleOrientationCover.isOpen_sheet hι e _).mem_nhds hvS, s, ?_, ?_, ?_⟩
  · -- In the total space, `s` is `p ↦ e⁻¹ (p.proj, f)` on the sheet.
    rw [IsInducing.subtypeVal.continuousOn_iff]
    refine ContinuousOn.congr (f := fun p ↦ TotalSpace.mk' F p.proj (e.symm p.proj f))
      (e.continuousOn_symm.comp
        (VectorBundleOrientationCover.continuous_proj.prodMk continuous_const).continuousOn
        fun p hp ↦ ⟨(VectorBundleOrientationCover.mem_sheet_iff.1 hp).fst, mem_univ _⟩)
      fun p hp ↦ by
        rw [Function.comp_apply, hs (VectorBundleOrientationCover.mem_sheet_iff.1 hp).fst]
  · rw [zeroSectionComplOrientation_apply, hs (p := ⟨v.val.proj, _⟩) hv]
    exact Subtype.ext (TotalSpace.ext rfl (heq_of_eq (e.symm_apply_apply_mk hv v.val.snd)))
  · rintro ⟨b, o⟩ hp
    obtain ⟨hb, hbo⟩ := VectorBundleOrientationCover.mem_sheet_iff.1 hp
    rw [hs hb, zeroSectionComplOrientation_apply, VectorBundleOrientationCover.mk_eq_mk_iff]
    -- Both orientations read in `e` as the orientation of `(f)`.
    exact (e.mapOrientation (Fin 1) hb).injective <|
      (mapOrientation_orientation_basisSingleton hF e hb (hne hb) hf (by simp [hb])).trans hbo.symm

/-- The orientation through a nonzero vector is an open map: near every point it has a continuous
section through any given preimage. -/
theorem isOpenMap_zeroSectionComplOrientation :
    IsOpenMap (zeroSectionComplOrientation (E := E) hF) := by
  refine IsOpenMap.of_nhds_le fun v W hW ↦ ?_
  obtain ⟨U, hU, s, hs, hsv, hsec⟩ := exists_continuousOn_section hF v
  -- Points of `U` whose section lies in the preimage of `W` are in `W`.
  have hW' : s ⁻¹' (zeroSectionComplOrientation hF ⁻¹' W) ∈ 𝓝 (zeroSectionComplOrientation hF v) :=
    (hs.continuousAt hU).preimage_mem_nhds (by rwa [hsv])
  filter_upwards [hW', hU] with p hpW hpU
  simpa only [mem_preimage, hsec p hpU] using hpW

/-- The orientation through a nonzero vector is a quotient map onto the orientation double
cover. -/
theorem isQuotientMap_zeroSectionComplOrientation :
    IsQuotientMap (zeroSectionComplOrientation (E := E) hF) :=
  (isOpenMap_zeroSectionComplOrientation hF).isQuotientMap
    (continuous_zeroSectionComplOrientation hF) (surjective_zeroSectionComplOrientation hF)

/-- **The fibres of the orientation map are connected.** The nonzero vectors through which a
given orientation of a fibre passes form an open half-line, a connected set. -/
theorem isConnected_preimage_zeroSectionComplOrientation
    (p : VectorBundleOrientationCover F E (Fin 1)) :
    IsConnected (zeroSectionComplOrientation hF ⁻¹' {p}) := by
  obtain ⟨b, o⟩ := p
  obtain ⟨v₀, hv₀⟩ := surjective_zeroSectionComplOrientation hF ⟨b, o⟩
  refine ⟨⟨v₀, hv₀⟩, ?_⟩
  -- In the total space the fibre is the image of the convex set of positive vectors of `o`.
  set P := {w : E b | ∃ β : Basis (Fin 1) ℝ (E b), β default = w ∧ β.orientation = o}
  have himage : Subtype.val '' (zeroSectionComplOrientation hF ⁻¹' {⟨b, o⟩}) =
      TotalSpace.mk b '' P := by
    ext u
    constructor
    · rintro ⟨⟨⟨b', w⟩, hw⟩, hwo, rfl⟩
      obtain rfl : b' = b := congrArg VectorBundleOrientationCover.proj hwo
      exact ⟨w, (zeroSectionComplOrientation_eq_mk_iff hF (mem_zeroSectionCompl.1 hw)).1 hwo, rfl⟩
    · rintro ⟨w, ⟨β, hβ, hβo⟩, rfl⟩
      have hw : w ≠ 0 := hβ ▸ β.ne_zero default
      exact ⟨⟨⟨b, w⟩, mem_zeroSectionCompl.2 hw⟩,
        (zeroSectionComplOrientation_eq_mk_iff hF hw).2 ⟨β, hβ, hβo⟩, rfl⟩
  rw [← IsInducing.subtypeVal.isPreconnected_image, himage]
  -- Transport `P` to the model fibre, where it is convex.
  set L := VectorBundle.continuousLinearEquivAt ℝ F E b
  have hP : P = L.symm '' (L '' P) := (L.symm_image_image P).symm
  rw [hP, image_image]
  exact ((o.convex_setOf_exists_basis_orientation_eq.linear_image
    L.toLinearEquiv.toLinearMap).isPreconnected).image _
    ((FiberBundle.continuous_totalSpaceMk F E b).comp L.symm.continuous).continuousOn

/-- **The components of the nonzero vectors of a line bundle.** The connected component of a
nonzero vector `v` is the preimage of the connected component of the orientation through `v` in
the orientation double cover. -/
theorem preimage_connectedComponent_zeroSectionComplOrientation (v : zeroSectionCompl F E) :
    zeroSectionComplOrientation hF ⁻¹' connectedComponent (zeroSectionComplOrientation hF v) =
      connectedComponent v :=
  (isQuotientMap_zeroSectionComplOrientation hF).isCoinducing.preimage_connectedComponent
    (isConnected_preimage_zeroSectionComplOrientation hF) v

/-- The nonzero vectors of a line bundle form a connected space exactly when its orientation
double cover is connected. -/
theorem connectedSpace_zeroSectionCompl_iff (hF : finrank ℝ F = 1) :
    ConnectedSpace (zeroSectionCompl F E) ↔
      ConnectedSpace (VectorBundleOrientationCover F E (Fin 1)) := by
  refine ⟨fun _ ↦ (surjective_zeroSectionComplOrientation hF).connectedSpace
    (continuous_zeroSectionComplOrientation hF), fun h ↦ ?_⟩
  obtain ⟨p⟩ := h.toNonempty
  obtain ⟨v, -⟩ := surjective_zeroSectionComplOrientation hF p
  rw [connectedSpace_iff_connectedComponent]
  refine ⟨v, ?_⟩
  rw [← preimage_connectedComponent_zeroSectionComplOrientation hF,
    PreconnectedSpace.connectedComponent_eq_univ, preimage_univ]

/-- **The nonzero vectors of a non-orientable line bundle are connected.** Over a connected base,
the complement of the zero section of a real line bundle is connected exactly when the bundle
admits no orientation. -/
theorem connectedSpace_zeroSectionCompl_iff_isEmpty [ConnectedSpace B]
    (hF : finrank ℝ F = 1) :
    ConnectedSpace (zeroSectionCompl F E) ↔ IsEmpty (VectorBundleOrientation F E (Fin 1)) := by
  have : FiniteDimensional ℝ F := Module.finite_of_finrank_eq_succ hF
  rw [connectedSpace_zeroSectionCompl_iff hF, ← not_nonempty_iff,
    VectorBundleOrientation.nonempty_iff_not_connectedSpace (by rw [hF, Fintype.card_fin]),
    not_not]

end TauCeti
