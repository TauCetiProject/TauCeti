/-
Copyright (c) 2026 Tau Ceti Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.SquareClassGroup.Real
public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.SpinorNorm.Hyperbolic
public import TauCeti.Topology.Algebra.Group.Connected
public import TauCeti.Topology.Algebra.QuadraticForm.OrthogonalGroup.Hyperbolic

/-!
# The identity component of the real hyperbolic-plane orthogonal group

The proper isometry group of the real hyperbolic plane is the topological unit group
through the hyperbolic torus. Its identity component is therefore the positive-unit
subgroup. The real Spin image is exactly this component: the general spinor-norm
calculation identifies it with the square-unit parameters, and a real unit is a square
exactly when it is positive.
-/

public section

open Set
open TauCeti.QuadraticMap

namespace TauCeti

private theorem isPreconnected_units_posSubgroup_real :
    IsPreconnected (Units.posSubgroup ℝ : Set ℝˣ) := by
  let f : Set.Ioi (0 : ℝ) → Units.posSubgroup ℝ := fun x =>
    ⟨Units.mk0 x.1 x.2.ne', (Units.mem_posSubgroup _).2 x.2⟩
  have hf : Continuous f := by
    apply continuous_induced_rng.mpr
    apply Units.continuous_iff.mpr
    constructor
    · exact continuous_subtype_val
    · apply continuous_iff_continuousAt.mpr
      intro x
      change ContinuousAt (fun y : Set.Ioi (0 : ℝ) => y.1⁻¹) x
      exact (continuousAt_inv₀ x.2.ne').comp continuous_subtype_val.continuousAt
  let hpreIoi : PreconnectedSpace (Set.Ioi (0 : ℝ)) :=
    Subtype.preconnectedSpace isPreconnected_Ioi
  have himage : f '' (Set.univ : Set (Set.Ioi (0 : ℝ))) =
      (Set.univ : Set (Units.posSubgroup ℝ)) := by
    ext u
    constructor
    · rintro ⟨x, hx, rfl⟩
      simp
    · intro hu
      let x : Set.Ioi (0 : ℝ) :=
        ⟨(((u : Units.posSubgroup ℝ) : ℝˣ) : ℝ),
          (Units.mem_posSubgroup _).1 u.2⟩
      refine ⟨x, mem_univ _, ?_⟩
      apply Subtype.ext
      simp [f, x]
  let hprePos : PreconnectedSpace (Units.posSubgroup ℝ) := by
    refine ⟨?_⟩
    have h := (@PreconnectedSpace.isPreconnected_univ (Set.Ioi (0 : ℝ)) _ hpreIoi).image
      f hf.continuousOn
    rw [himage] at h
    exact h
  exact isPreconnected_iff_preconnectedSpace.mpr hprePos

private theorem connectedComponentOfOne_units_real :
    Subgroup.connectedComponentOfOne ℝˣ = Units.posSubgroup ℝ := by
  apply le_antisymm
  · apply Subgroup.connectedComponentOfOne_le_of_isOpen
    rw [isOpen_iff_mem_nhds]
    intro u hu
    have hval : (0 : ℝ) < (u : ℝ) := (Units.mem_posSubgroup _).1 hu
    exact IsOpen.mem_nhds (isOpen_Ioi.preimage Units.continuous_val) hval
  · intro u hu
    exact isPreconnected_units_posSubgroup_real.subset_connectedComponent (by simp) hu

/-- The identity component of the real special-orthogonal hyperbolic-plane group is the
positive-unit part of its hyperbolic torus. -/
theorem connectedComponentOfOne_specialOrthogonalGroup_hyperbolicPlane :
    Subgroup.connectedComponentOfOne (specialOrthogonalGroup (hyperbolicPlane ℝ)) =
      (Units.posSubgroup ℝ).map (hyperbolicTorus ℝ) := by
  let e := hyperbolicTorusContinuousMulEquiv ℝ
  apply le_antisymm
  · intro g hg
    have hback := Subgroup.map_connectedComponentOfOne_le
      (f := e.symm.toMulEquiv.toMonoidHom) e.continuous_invFun
    have hu : e.symm g ∈ Subgroup.connectedComponentOfOne ℝˣ := by
      apply hback
      refine ⟨g, hg, ?_⟩
      exact rfl
    rw [connectedComponentOfOne_units_real] at hu
    refine ⟨e.symm g, hu, ?_⟩
    simpa [e] using e.apply_symm_apply g
  · intro g hg
    obtain ⟨u, hu, rfl⟩ := hg
    have hforward := Subgroup.map_connectedComponentOfOne_le
      (f := e.toMulEquiv.toMonoidHom) e.continuous_toFun
    rw [connectedComponentOfOne_units_real] at hforward
    apply hforward
    refine ⟨u, hu, ?_⟩
    simp [e]

/-- The real Spin image of the hyperbolic plane is the identity component of its proper
orthogonal group. -/
theorem range_spinToSpecialOrthogonal_hyperbolicPlane_real :
    (CliffordAlgebra.spinToSpecialOrthogonal (hyperbolicPlane ℝ)).range =
      Subgroup.connectedComponentOfOne (specialOrthogonalGroup (hyperbolicPlane ℝ)) := by
  rw [CliffordAlgebra.range_spinToSpecialOrthogonal_hyperbolicPlane,
    connectedComponentOfOne_specialOrthogonalGroup_hyperbolicPlane]
  ext g
  constructor
  · intro hg
    rw [Subgroup.mem_map] at hg ⊢
    obtain ⟨t, ht, rfl⟩ := hg
    exact ⟨t, (Units.isSquare_iff_pos t).mp ht, rfl⟩
  · intro hg
    rw [Subgroup.mem_map] at hg ⊢
    obtain ⟨t, ht, rfl⟩ := hg
    exact ⟨t, (Units.isSquare_iff_pos t).mpr ht, rfl⟩

end TauCeti
