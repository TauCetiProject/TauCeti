/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Convex.Orientation
public import TauCeti.Topology.VectorBundle.Orientation.Basic
public import TauCeti.Topology.VectorBundle.Orientation.Cover
public import TauCeti.Topology.VectorBundle.Section

/-!
# Positive sections of oriented line bundles

An orientation of a real line, indexed by a type with a single element, singles out its positive
vectors: the vectors `v` such that the one-vector basis `(v)` has that orientation. They form an
open half-line, a convex set (`Orientation.convex_setOf_exists_basis_orientation_eq`).

An oriented real line bundle over a normal paracompact base therefore has a continuous section
whose value in every fibre is positive for the orientation of that fibre
(`TauCeti.VectorBundleOrientation.exists_continuous_section_basis_orientation_eq`). Near each point
the orientation reads as a constant orientation of the model fibre in the preferred
trivialization, so the section with constant coordinates a positive vector of the model fibre is
positive there; the positivity condition is convex in each fibre, so these local sections glue
along a partition of unity (`TauCeti.exists_continuous_section_forall_mem_convex_of_local`).

A positive vector is nonzero, so such a section vanishes nowhere. This is the section that kills
the Euler class of an oriented line bundle.

Conversely, orientations of the fibres of a line bundle that admit, near every point, a positive
section continuous on a neighbourhood form an orientation of the bundle
(`TauCeti.VectorBundleOrientation.ofExistsContinuousOnSection`), since continuous families of bases
give continuous maps to the orientation double cover
(`TauCeti.VectorBundleOrientationCover.continuous_mk_basis_orientation`). Together with the
positive local sections of an orientation
(`TauCeti.VectorBundleOrientation.exists_continuousOn_section_basis_orientation_eq`), this
describes the orientations of a line bundle by their positive local sections.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §9 (oriented bundles and the Euler class; a nowhere-zero section kills the
  Euler class).
-/

public section

open Bundle Module Set
open scoped Topology

namespace TauCeti.VectorBundleOrientation

variable {B : Type*} [TopologicalSpace B] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type*} [TopologicalSpace (TotalSpace F E)] [∀ b, AddCommGroup (E b)]
  [∀ b, Module ℝ (E b)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E] [VectorBundle ℝ F E]
  {ι : Type*} [Fintype ι] [DecidableEq ι] [Unique ι]

/-- **An oriented line bundle has positive local sections.** Near every point `b`, a real vector
bundle of rank one oriented by `o` has a section `s`, continuous on a neighbourhood `U` of `b`, such
that at every point `x` of `U` the one-vector basis `(s x)` has the orientation `o x`. -/
theorem exists_continuousOn_section_basis_orientation_eq (o : VectorBundleOrientation F E ι)
    (hι : Fintype.card ι = finrank ℝ F) (b : B) :
    ∃ U ∈ 𝓝 b, ∃ s : ∀ x, E x, ContinuousOn (fun x ↦ TotalSpace.mk' F x (s x)) U ∧
      ∀ x ∈ U, ∃ β : Basis ι ℝ (E x), β default = s x ∧ β.orientation = o x := by
  have : FiniteDimensional ℝ F :=
    Module.finite_of_finrank_pos (hι ▸ Fintype.card_pos)
  -- Near `b` the orientation reads as the orientation `ω` of `F` in the preferred trivialization
  -- `e` at `b`; carry a basis of `F` of orientation `ω` along `e`.
  let e := trivializationAt F E b
  have hb : b ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' b
  let β := (e.mapOrientation ι hb (o b)).someBasis hι
  refine ⟨_, Filter.inter_mem (o.eventually_mapOrientation_eq' b) (e.open_baseSet.mem_nhds hb),
    fun x ↦ e.symmL ℝ x (β default), (e.continuousOn_mk_symmL (β default)).mono inter_subset_right,
    fun y ⟨hy, hye⟩ ↦ ⟨β.map (e.linearEquivAt ℝ y hye).symm, ?_, ?_⟩⟩
  · exact (e.symmL_apply hye _).symm
  · refine ((e.mapOrientation_eq_orientation_iff hye β (o y)).1 ?_).symm
    rw [Orientation.someBasis_orientation]
    exact hy hye

/-- **An oriented line bundle has a positive section.** A real vector bundle of rank one over a
normal paracompact base, oriented by `o`, has a continuous section `s` such that, in every fibre,
the one-vector basis `(s b)` has the orientation `o b`. -/
theorem exists_continuous_section_basis_orientation_eq [NormalSpace B] [ParacompactSpace B]
    (o : VectorBundleOrientation F E ι) (hι : Fintype.card ι = finrank ℝ F) :
    ∃ s : ∀ b, E b, Continuous (fun b ↦ TotalSpace.mk' F b (s b)) ∧
      ∀ b, ∃ β : Basis ι ℝ (E b), β default = s b ∧ β.orientation = o b :=
  -- The positive vectors form a convex set in each fibre, so the positive local sections glue.
  exists_continuous_section_forall_mem_convex_of_local
    (fun b ↦ {v | ∃ β : Basis ι ℝ (E b), β default = v ∧ β.orientation = o b})
    (fun b ↦ (o b).convex_setOf_exists_basis_orientation_eq)
    (o.exists_continuousOn_section_basis_orientation_eq hι)

omit [DecidableEq ι] in
/-- **An oriented line bundle has a nowhere-vanishing section.** A real vector bundle of rank one
over a normal paracompact base that admits an orientation has a continuous section vanishing
nowhere: a positive section. -/
theorem exists_continuous_section_ne_zero [NormalSpace B] [ParacompactSpace B]
    (o : VectorBundleOrientation F E ι) (hι : Fintype.card ι = finrank ℝ F) :
    ∃ s : ∀ b, E b, Continuous (fun b ↦ TotalSpace.mk' F b (s b)) ∧ ∀ b, s b ≠ 0 := by
  classical
  obtain ⟨s, hs, hpos⟩ := o.exists_continuous_section_basis_orientation_eq hι
  refine ⟨s, hs, fun b ↦ ?_⟩
  obtain ⟨β, hβ, -⟩ := hpos b
  exact hβ ▸ β.ne_zero default

/-- **Fibre orientations with positive local sections orient a line bundle.** Let `o b` be an
orientation of every fibre of a real vector bundle of rank one. If near every point some section,
continuous on a neighbourhood, forms at every point `x` of it a one-vector basis of orientation
`o x`, then `o` is an orientation of the bundle. This is the converse of
`TauCeti.VectorBundleOrientation.exists_continuousOn_section_basis_orientation_eq`. -/
def ofExistsContinuousOnSection (o : ∀ b, Orientation ℝ (E b) ι)
    (ho : ∀ b, ∃ U ∈ 𝓝 b, ∃ s : ∀ x, E x, ContinuousOn (fun x ↦ TotalSpace.mk' F x (s x)) U ∧
      ∀ x ∈ U, ∃ β : Basis ι ℝ (E x), β default = s x ∧ β.orientation = o x) :
    VectorBundleOrientation F E ι :=
  ofContinuous o <| continuous_iff_continuousAt.2 fun b ↦ by
    obtain ⟨U, hU, s, hs, hpos⟩ := ho b
    obtain ⟨V, hVU, hV, hbV⟩ := mem_nhds_iff.1 hU
    -- On the open neighbourhood `V` of `b`, the fibre orientations are those of the bases
    -- `(s x)`, which vary continuously, so they form a continuous map to the orientation cover.
    choose β hβ hβo using fun x : V ↦ hpos x (hVU x.property)
    have hc := VectorBundleOrientationCover.continuous_mk_basis_orientation (F := F)
      continuous_subtypeVal β fun i ↦
        (continuousOn_iff_continuous_domRestrict.1 (hs.mono hVU)).congr fun x ↦ by
          rw [Set.domRestrict_apply, Unique.eq_default i, hβ]
    simp only [hβo] at hc
    exact (continuousOn_iff_continuous_domRestrict.2 hc).continuousAt (hV.mem_nhds hbV)

@[simp]
theorem coe_ofExistsContinuousOnSection (o : ∀ b, Orientation ℝ (E b) ι) (ho) :
    ⇑(ofExistsContinuousOnSection (F := F) o ho) = o :=
  coe_ofContinuous (F := F) ..

end TauCeti.VectorBundleOrientation
