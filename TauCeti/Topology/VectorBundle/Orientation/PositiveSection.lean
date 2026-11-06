/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Convex.Orientation
public import TauCeti.Topology.VectorBundle.Orientation.Basic
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

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §9 (oriented bundles and the Euler class; a nowhere-zero section kills the
  Euler class).
-/

public section

open Bundle Module Set

namespace TauCeti.VectorBundleOrientation

variable {B : Type*} [TopologicalSpace B] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type*} [TopologicalSpace (TotalSpace F E)] [∀ b, AddCommGroup (E b)]
  [∀ b, Module ℝ (E b)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E] [VectorBundle ℝ F E]
  {ι : Type*} [Fintype ι] [DecidableEq ι] [Unique ι]

/-- **An oriented line bundle has a positive section.** A real vector bundle of rank one over a
normal paracompact base, oriented by `o`, has a continuous section `s` such that, in every fibre,
the one-vector basis `(s b)` has the orientation `o b`. -/
theorem exists_continuous_section_basis_orientation_eq [NormalSpace B] [ParacompactSpace B]
    (o : VectorBundleOrientation F E ι) (hι : Fintype.card ι = finrank ℝ F) :
    ∃ s : ∀ b, E b, Continuous (fun b ↦ TotalSpace.mk' F b (s b)) ∧
      ∀ b, ∃ β : Basis ι ℝ (E b), β default = s b ∧ β.orientation = o b := by
  have : FiniteDimensional ℝ F :=
    Module.finite_of_finrank_pos (hι ▸ Fintype.card_pos)
  refine exists_continuous_section_forall_mem_convex_of_local
    (fun b ↦ {v | ∃ β : Basis ι ℝ (E b), β default = v ∧ β.orientation = o b})
    (fun b ↦ (o b).convex_setOf_exists_basis_orientation_eq) fun x₀ ↦ ?_
  -- Near `x₀` the orientation reads as the orientation `ω` of `F` in the preferred trivialization
  -- `e` at `x₀`; carry a basis of `F` of orientation `ω` along `e`.
  let e := trivializationAt F E x₀
  have hx₀ : x₀ ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' x₀
  let β := (e.mapOrientation ι hx₀ (o x₀)).someBasis hι
  refine ⟨_, Filter.inter_mem (o.eventually_mapOrientation_eq' x₀) (e.open_baseSet.mem_nhds hx₀),
    fun x ↦ e.symmL ℝ x (β default), (e.continuousOn_mk_symmL (β default)).mono inter_subset_right,
    fun y ⟨hy, hye⟩ ↦ ⟨β.map (e.linearEquivAt ℝ y hye).symm, ?_, ?_⟩⟩
  · exact (e.symmL_apply hye _).symm
  · refine ((e.mapOrientation_eq_orientation_iff hye β (o y)).1 ?_).symm
    rw [Orientation.someBasis_orientation]
    exact hy hye

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

end TauCeti.VectorBundleOrientation
