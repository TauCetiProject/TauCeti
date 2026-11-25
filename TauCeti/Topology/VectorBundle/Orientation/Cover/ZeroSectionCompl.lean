/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.VectorBundle.FiniteDimensional
public import TauCeti.Topology.VectorBundle.Orientation.Cover
public import TauCeti.Topology.VectorBundle.ZeroSection
import TauCeti.LinearAlgebra.Orientation.Basis
import TauCeti.Topology.VectorBundle.Trivialization

/-!
# The nonzero vectors of a real line bundle and its orientation double cover

Let `E → B` be a real vector bundle of rank one, and let `E₀` be the complement of its zero
section (`TauCeti.zeroSectionCompl`). A nonzero vector `v` of a fibre `E b` is a basis `(v)` of
that line, so it determines an orientation of `E b`. This gives a map

`E₀ → B'`, `v ↦ (b, orientation of (v))`

to the orientation double cover `B'` of `E`
(`TauCeti.VectorBundleOrientationCover.ofZeroSectionCompl`). It is continuous, surjective and
open, hence a quotient map
(`TauCeti.VectorBundleOrientationCover.isQuotientMap_ofZeroSectionCompl`), and its fibres are the
open half-lines `{c • v | c > 0}` of the fibres of `E`, which are connected
(`TauCeti.VectorBundleOrientationCover.isConnected_preimage_singleton_ofZeroSectionCompl`). Openness
is checked on the sheets of the cover: over the sheet of a trivialization `e` read as the
orientation of a nonzero vector `w` of the model fibre, `p ↦ e⁻¹(p, w)` is a continuous section of
the map.

So `E₀` and `B'` have the same connected components: the preimage of the component of the image
of `v` is the component of `v`
(`TauCeti.VectorBundleOrientationCover.preimage_connectedComponent_ofZeroSectionCompl`), and `E₀` is
connected exactly when `B'` is
(`TauCeti.VectorBundleOrientationCover.connectedSpace_zeroSectionCompl_iff`). Since the cover of a
bundle over a connected base is connected exactly when the bundle is not orientable
(`TauCeti.VectorBundleOrientation.nonempty_iff_not_connectedSpace`), a real line bundle over a
connected base is orientable if and only if its nonzero vectors form a disconnected space
(`TauCeti.VectorBundleOrientation.nonempty_iff_not_connectedSpace_zeroSectionCompl`). For instance
the nonzero vectors of the Möbius line bundle over the circle form a connected space, those of the
trivial line bundle `S¹ × ℝ` do not.

## Main definitions

* `TauCeti.VectorBundleOrientationCover.ofZeroSectionCompl`: the orientation of a fibre of a line
  bundle given by a nonzero vector, as a point of the orientation double cover.

## Main results

* `TauCeti.VectorBundleOrientationCover.isQuotientMap_ofZeroSectionCompl`: this map is a quotient
  map.
* `TauCeti.VectorBundleOrientationCover.isConnected_preimage_singleton_ofZeroSectionCompl`: its
  fibres are connected.
* `TauCeti.VectorBundleOrientationCover.preimage_connectedComponent_ofZeroSectionCompl`: it
  identifies the connected components of the nonzero vectors with those of the cover.
* `TauCeti.VectorBundleOrientation.nonempty_iff_not_connectedSpace_zeroSectionCompl`: over a
  connected base, a real line bundle is orientable if and only if its nonzero vectors form a
  disconnected space.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, second edition, Graduate Texts in
  Mathematics 218, Springer, 2013, Chapter 15, "The Orientation Covering".
-/

public section

noncomputable section

open Bundle Module Set Topology

variable {B : Type*} [TopologicalSpace B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type*} [TopologicalSpace (TotalSpace F E)] [∀ b, AddCommGroup (E b)]
  [∀ b, Module ℝ (E b)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E] [VectorBundle ℝ F E]

namespace TauCeti

namespace VectorBundleOrientationCover

variable (F E) in
/-- Each fibre of a vector bundle whose model fibre is a line is a line. -/
private theorem finrank_fiber_eq_one (hF : finrank ℝ F = 1) (b : B) : finrank ℝ (E b) = 1 :=
  (VectorBundle.finrank_eq ℝ F E b).trans hF

variable (F E) in
/-- The orientation of a fibre of a real line bundle given by a nonzero vector `v`, as a point of
the orientation double cover: the base point of `v` together with the orientation of the basis
`(v)` of its fibre. -/
def ofZeroSectionCompl (hF : finrank ℝ F = 1) (v : zeroSectionCompl F E) :
    VectorBundleOrientationCover F E (Fin 1) :=
  ⟨v.val.proj, (FiniteDimensional.basisSingleton (Fin 1) (finrank_fiber_eq_one F E hF v.val.proj)
    v.val.snd (mem_zeroSectionCompl.1 v.property)).orientation⟩

variable (hF : finrank ℝ F = 1)

/-- A nonzero vector `v` of the fibre over `b` gives the orientation of the basis `(v)`. -/
@[simp]
theorem ofZeroSectionCompl_mk {b : B} {v : E b} (hv : v ≠ 0) :
    ofZeroSectionCompl F E hF ⟨⟨b, v⟩, mem_zeroSectionCompl.2 hv⟩ =
      ⟨b, (FiniteDimensional.basisSingleton (Fin 1) ((VectorBundle.finrank_eq ℝ F E b).trans hF) v
        hv).orientation⟩ :=
  (rfl)

/-- Negating a nonzero vector reverses the orientation of its fibre that it gives: the image of
`-v` is the image of `v` under the deck involution of the orientation double cover. -/
theorem ofZeroSectionCompl_mk_neg {b : B} {v : E b} (hv : v ≠ 0) :
    ofZeroSectionCompl F E hF ⟨⟨b, -v⟩, mem_zeroSectionCompl.2 (neg_ne_zero.2 hv)⟩ =
      deck (ofZeroSectionCompl F E hF ⟨⟨b, v⟩, mem_zeroSectionCompl.2 hv⟩) := by
  rw [ofZeroSectionCompl_mk hF hv, ofZeroSectionCompl_mk hF (neg_ne_zero.2 hv), deck_apply,
    orientation_basisSingleton_neg]

@[simp]
theorem proj_ofZeroSectionCompl (v : zeroSectionCompl F E) :
    (ofZeroSectionCompl F E hF v).proj = v.val.proj :=
  (rfl)

/-- The orientation of a fibre given by a nonzero vector depends continuously on the vector. -/
theorem continuous_ofZeroSectionCompl : Continuous (ofZeroSectionCompl F E hF) :=
  continuous_mk_basis_orientation ((FiberBundle.continuous_proj F E).comp continuous_subtypeVal)
    (fun v : zeroSectionCompl F E ↦ FiniteDimensional.basisSingleton (Fin 1)
      (finrank_fiber_eq_one F E hF v.val.proj) v.val.snd (mem_zeroSectionCompl.1 v.property))
    fun _ ↦ by
      simpa only [FiniteDimensional.basisSingleton_apply, Function.comp_apply] using
        continuous_subtypeVal

/-- Two nonzero vectors in the same fibre of a line bundle give the same orientation exactly when
one is a positive multiple of the other. -/
theorem ofZeroSectionCompl_mk_eq_iff {b : B} {v w : E b} (hv : v ≠ 0) (hw : w ≠ 0) :
    ofZeroSectionCompl F E hF ⟨⟨b, w⟩, mem_zeroSectionCompl.2 hw⟩ =
        ofZeroSectionCompl F E hF ⟨⟨b, v⟩, mem_zeroSectionCompl.2 hv⟩ ↔
      ∃ c : ℝ, 0 < c ∧ w = c • v := by
  have hb : finrank ℝ (E b) = 1 := finrank_fiber_eq_one F E hF b
  rw [ofZeroSectionCompl_mk hF hw, ofZeroSectionCompl_mk hF hv, mk_eq_mk_iff]
  constructor
  · intro h
    -- In a line, `w` is a nonzero multiple of `v`, and a negative multiple has the opposite
    -- orientation.
    obtain ⟨c, rfl⟩ := exists_smul_eq_of_finrank_eq_one hb hv w
    have hc : c ≠ 0 := left_ne_zero_of_smul hw
    refine ⟨c, hc.lt_or_gt.resolve_left fun hc' ↦ ?_, rfl⟩
    have hneg : c • v = (-c) • -v := by rw [smul_neg, neg_smul, neg_neg]
    have hnv : -v ≠ 0 := neg_ne_zero.2 hv
    have h' : (FiniteDimensional.basisSingleton (Fin 1) hb ((-c) • -v)
        (smul_ne_zero (neg_pos.2 hc').ne' hnv)).orientation =
        (FiniteDimensional.basisSingleton (Fin 1) hb v hv).orientation := by
      simpa only [hneg] using h
    rw [orientation_basisSingleton_smul hb (neg_pos.2 hc') hnv,
      orientation_basisSingleton_neg hb hnv] at h'
    exact Module.Ray.ne_neg_self _ h'.symm
  · rintro ⟨c, hc, rfl⟩
    exact orientation_basisSingleton_smul hb hc hv

/-- Every orientation of a fibre of a line bundle is given by a nonzero vector. -/
theorem surjective_ofZeroSectionCompl : Function.Surjective (ofZeroSectionCompl F E hF) := by
  rintro ⟨b, o⟩
  have hb : finrank ℝ (E b) = 1 := finrank_fiber_eq_one F E hF b
  have : Nontrivial (E b) := Module.nontrivial_of_finrank_eq_succ hb
  obtain ⟨v, hv⟩ := exists_ne (0 : E b)
  -- The orientation `o` is that of `(v)` or of `(-v)`.
  rcases (FiniteDimensional.basisSingleton (Fin 1) hb v hv).orientation_eq_or_eq_neg o with h | h
  · exact ⟨⟨⟨b, v⟩, mem_zeroSectionCompl.2 hv⟩, by
      rw [ofZeroSectionCompl_mk hF hv, mk_eq_mk_iff, h]⟩
  · refine ⟨⟨⟨b, -v⟩, mem_zeroSectionCompl.2 (neg_ne_zero.2 hv)⟩, ?_⟩
    rw [ofZeroSectionCompl_mk_neg hF hv, ofZeroSectionCompl_mk hF hv, deck_apply, h]

/-- The nonzero vectors giving a fixed orientation of a fibre form a connected set: the open
half-line of positive multiples of one of them. -/
theorem isConnected_preimage_singleton_ofZeroSectionCompl
    (p : VectorBundleOrientationCover F E (Fin 1)) :
    IsConnected (ofZeroSectionCompl F E hF ⁻¹' {p}) := by
  obtain ⟨⟨⟨b, v⟩, hv⟩, rfl⟩ := surjective_ofZeroSectionCompl hF p
  replace hv : v ≠ 0 := mem_zeroSectionCompl.1 hv
  -- Scalar multiplication in the fibre is continuous, read in a trivialization.
  let φ := Trivialization.continuousLinearEquivAt ℝ (trivializationAt F E b) b
    (FiberBundle.mem_baseSet_trivializationAt' b)
  have hsmul : Continuous fun c : ℝ ↦ c • v := by
    have : (fun c : ℝ ↦ c • v) = fun c ↦ φ.symm (c • φ v) := funext fun c ↦ by simp
    rw [this]
    fun_prop
  let ray : Ioi (0 : ℝ) → zeroSectionCompl F E := fun c ↦
    ⟨⟨b, (c : ℝ) • v⟩, mem_zeroSectionCompl.2 (smul_ne_zero c.property.ne' hv)⟩
  have hray : Continuous ray :=
    ((FiberBundle.totalSpaceMk_isInducing F E b).continuous.comp
      (hsmul.comp continuous_subtypeVal)).subtype_mk _
  have hpre : ofZeroSectionCompl F E hF ⁻¹'
      {ofZeroSectionCompl F E hF ⟨⟨b, v⟩, mem_zeroSectionCompl.2 hv⟩} = range ray := by
    ext ⟨⟨b', w⟩, hw⟩
    replace hw : w ≠ 0 := mem_zeroSectionCompl.1 hw
    simp only [mem_preimage, mem_singleton_iff, mem_range]
    constructor
    · intro h
      obtain rfl : b' = b := congrArg proj h
      obtain ⟨c, hc, rfl⟩ := (ofZeroSectionCompl_mk_eq_iff hF hv hw).1 h
      exact ⟨⟨c, hc⟩, rfl⟩
    · rintro ⟨c, hc⟩
      cases hc
      exact (ofZeroSectionCompl_mk_eq_iff hF hv (smul_ne_zero c.property.ne' hv)).2
        ⟨c, c.property, rfl⟩
  rw [hpre]
  have : ConnectedSpace (Ioi (0 : ℝ)) := isConnected_iff_connectedSpace.1 isConnected_Ioi
  exact isConnected_range hray

/-- Over the sheet of a linear trivialization `e` read as the orientation of a nonzero vector `w`
of the model fibre, `p ↦ e⁻¹(p, w)` is a section of `ofZeroSectionCompl`. -/
private theorem ofZeroSectionCompl_mk_symm (e : Trivialization F (π F E)) [e.IsLinear ℝ]
    {w : F} (hw : w ≠ 0) {p : VectorBundleOrientationCover F E (Fin 1)}
    (hp : p ∈ sheet e (FiniteDimensional.basisSingleton (Fin 1) hF w hw).orientation)
    (h : e.symm p.proj w ≠ 0) :
    ofZeroSectionCompl F E hF ⟨⟨p.proj, e.symm p.proj w⟩, mem_zeroSectionCompl.2 h⟩ = p := by
  obtain ⟨hpb, hpo⟩ := mem_sheet_iff.1 hp
  have hgw : (e ⟨p.proj, e.symm p.proj w⟩).2 = w := by rw [e.apply_mk_symm hpb]
  rw [ofZeroSectionCompl_mk hF h]
  refine VectorBundleOrientationCover.ext rfl
    (heq_of_eq ((e.mapOrientation (Fin 1) hpb).injective ?_))
  rw [hpo, e.mapOrientation_orientation_basisSingleton hpb _ hF h (by rw [hgw]; exact hw)]
  simp only [hgw]

/-- **Nonzero vectors orient their fibres openly.** The map sending a nonzero vector to the
orientation of its fibre that it determines is open. Over the sheet of a trivialization `e` read
as the orientation of a nonzero vector `w` of the model fibre, it has the continuous section
`p ↦ e⁻¹(p, w)`. -/
theorem isOpenMap_ofZeroSectionCompl : IsOpenMap (ofZeroSectionCompl F E hF) := by
  intro U hU
  refine isOpen_iff_mem_nhds.2 ?_
  rintro _ ⟨⟨⟨b, v⟩, hv⟩, hvU, rfl⟩
  replace hv : v ≠ 0 := mem_zeroSectionCompl.1 hv
  set e := trivializationAt F E b
  have hb : b ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' b
  have hw : (e ⟨b, v⟩).2 ≠ 0 := (e.snd_apply_ne_zero_iff ℝ (v := ⟨b, v⟩) hb).2 hv
  set w : F := (e ⟨b, v⟩).2
  set o := (FiniteDimensional.basisSingleton (Fin 1) hF w hw).orientation
  -- The section `g` of the map over the sheet of `e` read as `o`.
  let g : VectorBundleOrientationCover F E (Fin 1) → TotalSpace F E :=
    fun p ↦ ⟨p.proj, e.symm p.proj w⟩
  have hgS : ContinuousOn g (sheet e o) :=
    e.continuousOn_symm.comp (continuous_proj.prodMk continuous_const).continuousOn
      fun p hp ↦ ⟨(mem_sheet_iff.1 hp).1, mem_univ _⟩
  have hg₀ {p} (hp : p ∈ sheet e o) : e.symm p.proj w ≠ 0 :=
    (e.symm_apply_ne_zero_iff ℝ (mem_sheet_iff.1 hp).1).2 hw
  have hvS : ofZeroSectionCompl F E hF ⟨⟨b, v⟩, mem_zeroSectionCompl.2 hv⟩ ∈ sheet e o := by
    rw [ofZeroSectionCompl_mk hF hv]
    exact mem_sheet_iff.2 ⟨hb, e.mapOrientation_orientation_basisSingleton hb _ hF hv hw⟩
  have hgv : g (ofZeroSectionCompl F E hF ⟨⟨b, v⟩, mem_zeroSectionCompl.2 hv⟩) = ⟨b, v⟩ := by
    rw [ofZeroSectionCompl_mk hF hv]
    simp only [g, w, e.symm_apply_apply_mk hb]
  -- Near the image of `v`, the section lands in `U`, so the image of `U` contains the points of
  -- the sheet whose section lands in `U`.
  have hU' : IsOpen (Subtype.val '' U : Set (TotalSpace F E)) :=
    (isOpen_zeroSectionCompl F E).isOpenMap_subtypeVal U hU
  refine Filter.mem_of_superset
    ((hgS.isOpen_inter_preimage (isOpen_sheet (by simpa using hF.symm) e o) hU').mem_nhds
      ⟨hvS, by rw [mem_preimage, hgv]; exact ⟨_, hvU, rfl⟩⟩) ?_
  rintro p ⟨hpS, u, huU, hu⟩
  refine ⟨u, huU, ?_⟩
  rw [show u = ⟨g p, mem_zeroSectionCompl.2 (hg₀ hpS)⟩ from Subtype.ext hu]
  exact ofZeroSectionCompl_mk_symm hF e hw hpS (hg₀ hpS)

/-- The map sending a nonzero vector of a line bundle to the orientation of its fibre that it
determines is a quotient map. -/
theorem isQuotientMap_ofZeroSectionCompl : IsQuotientMap (ofZeroSectionCompl F E hF) :=
  (isOpenMap_ofZeroSectionCompl hF).isQuotientMap (continuous_ofZeroSectionCompl hF)
    (surjective_ofZeroSectionCompl hF)

/-- **The nonzero vectors of a line bundle and its orientation double cover have the same
connected components.** The connected component of a nonzero vector `v` is the set of nonzero
vectors whose orientation lies in the connected component of the orientation given by `v`. -/
theorem preimage_connectedComponent_ofZeroSectionCompl (v : zeroSectionCompl F E) :
    ofZeroSectionCompl F E hF ⁻¹' connectedComponent (ofZeroSectionCompl F E hF v) =
      connectedComponent v :=
  (isQuotientMap_ofZeroSectionCompl hF).isCoinducing.preimage_connectedComponent
    (isConnected_preimage_singleton_ofZeroSectionCompl hF) v

include hF in
/-- The nonzero vectors of a real line bundle form a connected space exactly when its orientation
double cover is connected. -/
theorem connectedSpace_zeroSectionCompl_iff :
    ConnectedSpace (zeroSectionCompl F E) ↔
      ConnectedSpace (VectorBundleOrientationCover F E (Fin 1)) := by
  refine ⟨fun _ ↦ (surjective_ofZeroSectionCompl hF).connectedSpace
    (continuous_ofZeroSectionCompl hF), fun h ↦ ?_⟩
  obtain ⟨p⟩ := h.toNonempty
  obtain ⟨v, -⟩ := surjective_ofZeroSectionCompl hF p
  refine connectedSpace_iff_connectedComponent.2 ⟨v, ?_⟩
  rw [← preimage_connectedComponent_ofZeroSectionCompl hF,
    PreconnectedSpace.connectedComponent_eq_univ, preimage_univ]

end VectorBundleOrientationCover

namespace VectorBundleOrientation

/-- **A line bundle over a connected base is orientable exactly when its nonzero vectors form a
disconnected space.** An orientation splits the nonzero vectors into the positive and the
negative ones, two disjoint nonempty open sets; conversely, if the nonzero vectors are
disconnected, so is the orientation double cover, and the bundle is orientable. -/
theorem nonempty_iff_not_connectedSpace_zeroSectionCompl [ConnectedSpace B]
    (hF : finrank ℝ F = 1) :
    Nonempty (VectorBundleOrientation F E (Fin 1)) ↔ ¬ ConnectedSpace (zeroSectionCompl F E) := by
  have : FiniteDimensional ℝ F := Module.finite_of_finrank_eq_succ hF
  rw [VectorBundleOrientationCover.connectedSpace_zeroSectionCompl_iff hF]
  exact nonempty_iff_not_connectedSpace (by simpa using hF.symm)

end VectorBundleOrientation

end TauCeti
