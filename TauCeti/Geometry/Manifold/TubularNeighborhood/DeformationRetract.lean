/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Homotopy.Equiv
public import TauCeti.Geometry.Manifold.TubularNeighborhood.Basic

/-!
# A tube deformation retracts onto its core

Let `T : IsTubularNeighborhood f U φ` be tubular-neighbourhood data: an open, fibrewise
star-convex neighbourhood `U` of the zero section of a family of real vector spaces over `B`,
identified by the open embedding `φ : U → N` with the open tube `range φ`, and with the zero
section going to the core embedding `f : B → N`. The tube deformation retracts onto the core by
the straight-line homotopy in the fibres: the point `φ u` moves to `φ (t • u)`, where `t • u`
is `u` scaled in its fibre, as `t` runs from `1` to `0`.

This file packages that deformation. The **retraction** `T.retraction : C(range φ, B)` sends
`φ u` to the base point of `u`, and the inclusion of the core is `T.coreMap : C(B, range φ)`.
The fibrewise contraction `T.deformation` is a homotopy from `T.coreMap ∘ T.retraction` to the
identity of the tube which fixes the core at all times, so `range f` is a strong deformation
retract of `range φ` (`TauCeti.IsTubularNeighborhood.exists_deformation_range`), and the core
inclusion is a homotopy equivalence `T.homotopyEquiv : B ≃ₕ range φ`.

No bundle structure is used beyond the interface: continuity of the base projection on `U`
follows from the radial contraction at time zero, composed with `φ`, and the fact that `f` is an
embedding.

## Main definitions

* `TauCeti.IsTubularNeighborhood.retraction`: the retraction of the tube onto the base.
* `TauCeti.IsTubularNeighborhood.coreMap`: the core embedding, corestricted to the tube.
* `TauCeti.IsTubularNeighborhood.deformation`: the straight-line deformation of the tube onto
  its core, relative to the core.
* `TauCeti.IsTubularNeighborhood.homotopyEquiv`: the core inclusion as a homotopy equivalence.

## Main results

* `TauCeti.IsTubularNeighborhood.exists_deformation_range`: the core `range f` is a strong
  deformation retract of the tube `range φ`, in the subspace form of
  `Homeomorph.exists_deformation_of_image_eq`.

## References

* M. W. Hirsch, *Differential Topology*, Chapter 4, §5 and §6.
* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Theorem 6.24.
-/

public section

noncomputable section

open Set Bundle Topology
open scoped unitInterval ContinuousMap

namespace TauCeti.IsTubularNeighborhood

variable {B F N : Type*} {E : B → Type*}
  [TopologicalSpace B] [TopologicalSpace (TotalSpace F E)]
  [∀ x, AddCommGroup (E x)] [∀ x, Module ℝ (E x)] [TopologicalSpace N]
  {f : B → N} {U : Set (TotalSpace F E)} {φ : U → N}

/-- The **retraction of a tube onto its base**: the point `φ u` of the tube goes to the base
point of `u`. -/
def retraction (T : IsTubularNeighborhood f U φ) : C(range φ, B) where
  toFun w := (T.isOpenEmbedding.isEmbedding.toHomeomorph.symm w : TotalSpace F E).proj
  continuous_toFun := T.continuous_proj.comp
    T.isOpenEmbedding.isEmbedding.toHomeomorph.symm.continuous

/-- The retraction sends `φ u` to the base point of `u`. -/
@[simp]
theorem retraction_apply_mk (T : IsTubularNeighborhood f U φ) (u : U) :
    T.retraction ⟨φ u, mem_range_self u⟩ = (u : TotalSpace F E).proj := by
  simp only [retraction, ContinuousMap.coe_mk, Topology.IsEmbedding.toHomeomorph_symm_apply]

/-- The retraction is a left inverse of the core embedding. -/
@[simp]
theorem retraction_apply_f (T : IsTubularNeighborhood f U φ) (x : B) :
    T.retraction ⟨f x, T.f_mem_range x⟩ = x := by
  simpa only [T.map_zeroSection, zeroSection_proj] using T.retraction_apply_mk ⟨_, T.zero_mem x⟩

/-- The core embedding `f`, as a map into the tube. -/
def coreMap (T : IsTubularNeighborhood f U φ) : C(B, range φ) where
  toFun x := ⟨f x, T.f_mem_range x⟩
  continuous_toFun := T.isEmbedding_f.continuous.subtype_mk _

/-- The core map is `f`. -/
@[simp]
theorem coe_coreMap_apply (T : IsTubularNeighborhood f U φ) (x : B) :
    (T.coreMap x : N) = f x :=
  (rfl)

/-- The retraction is a left inverse of the core map. -/
@[simp]
theorem retraction_coreMap (T : IsTubularNeighborhood f U φ) (x : B) :
    T.retraction (T.coreMap x) = x :=
  T.retraction_apply_f x

/-- The range of the core map consists of the points of the tube on the core. -/
theorem range_coreMap (T : IsTubularNeighborhood f U φ) :
    range T.coreMap = {w : range φ | (w : N) ∈ range f} :=
  Set.range_codRestrict T.f_mem_range

/-- The retraction undoes the core map. -/
@[simp]
theorem retraction_comp_coreMap (T : IsTubularNeighborhood f U φ) :
    T.retraction.comp T.coreMap = ContinuousMap.id B :=
  ContinuousMap.ext T.retraction_coreMap

/-- The deformation of the tube at time `t`, in tubular coordinates: the tubular chart of the
radial contraction of `u` by `t`. -/
private def deformationFun (T : IsTubularNeighborhood f U φ) (p : I × range φ) : range φ :=
  ⟨φ (T.radialContraction ⟨p.1, T.isOpenEmbedding.isEmbedding.toHomeomorph.symm p.2⟩),
    mem_range_self _⟩

private theorem deformationFun_apply_mk (T : IsTubularNeighborhood f U φ) (t : I) (u : U) :
    T.deformationFun (t, ⟨φ u, mem_range_self u⟩) =
      ⟨φ (T.radialContraction ⟨t, u⟩), mem_range_self _⟩ := by
  simp only [deformationFun, Topology.IsEmbedding.toHomeomorph_symm_apply]

private theorem deformationFun_apply_f (T : IsTubularNeighborhood f U φ) (t : I) (x : B) :
    T.deformationFun (t, ⟨f x, T.f_mem_range x⟩) = ⟨f x, T.f_mem_range x⟩ := by
  have hu : T.radialContraction ⟨t, ⟨_, T.zero_mem x⟩⟩ = ⟨_, T.zero_mem x⟩ :=
    Subtype.ext (by simp [zeroSection])
  have := T.deformationFun_apply_mk t ⟨_, T.zero_mem x⟩
  simp only [hu, T.map_zeroSection] at this
  exact this

/-- **The straight-line deformation of a tube onto its core.** At time `t` the point `φ u` of the
tube moves to `φ (t • u)`, with `u` scaled in its fibre. At time `0` this is the core map after the
retraction, at time `1` it is the identity, and it fixes every point of the core throughout. -/
def deformation (T : IsTubularNeighborhood f U φ) :
    (T.coreMap.comp T.retraction).HomotopyRel (ContinuousMap.id (range φ)) (range T.coreMap) where
  toFun := T.deformationFun
  continuous_toFun := by
    refine Continuous.subtype_mk (T.isOpenEmbedding.continuous.comp
      (T.continuous_radialContraction.comp ?_)) _
    exact continuous_fst.prodMk
      (T.isOpenEmbedding.isEmbedding.toHomeomorph.symm.continuous.comp continuous_snd)
  map_zero_left := by
    rintro ⟨_, u, rfl⟩
    rw [deformationFun_apply_mk]
    apply Subtype.ext
    simp [T.map_zeroSection]
  map_one_left := by
    rintro ⟨_, u, rfl⟩
    rw [deformationFun_apply_mk]
    simp
  prop' := by
    rintro t _ ⟨x, rfl⟩
    simp only [ContinuousMap.coe_mk, ContinuousMap.comp_apply, coreMap, ContinuousMap.coe_mk,
      deformationFun_apply_f, retraction_apply_f]

/-- The deformation moves `φ u` along `φ` of the fibrewise scalings of `u`. -/
@[simp]
theorem deformation_apply_mk (T : IsTubularNeighborhood f U φ) (t : I) (u : U) :
    (T.deformation (t, ⟨φ u, mem_range_self u⟩) : N) = φ (T.radialContraction ⟨t, u⟩) :=
  congrArg Subtype.val (T.deformationFun_apply_mk t u)

/-- **The core inclusion of a tube is a homotopy equivalence**, with homotopy inverse the
retraction. -/
def homotopyEquiv (T : IsTubularNeighborhood f U φ) : B ≃ₕ range φ where
  toFun := T.coreMap
  invFun := T.retraction
  left_inv := T.retraction_comp_coreMap ▸ .refl _
  right_inv := ⟨T.deformation.toHomotopy⟩

/-- The homotopy equivalence is the core map. -/
@[simp]
theorem homotopyEquiv_apply (T : IsTubularNeighborhood f U φ) (x : B) :
    T.homotopyEquiv x = T.coreMap x :=
  (rfl)

/-- The homotopy inverse is the retraction. -/
@[simp]
theorem homotopyEquiv_symm_apply (T : IsTubularNeighborhood f U φ) (w : range φ) :
    T.homotopyEquiv.symm w = T.retraction w :=
  (rfl)

/-- **The core of a tube is a strong deformation retract of the tube**, stated for the subspaces
`range f ⊆ range φ` of `N`. -/
theorem exists_deformation_range (T : IsTubularNeighborhood f U φ) :
    ∃ r : C(range φ, range f), (∀ b, r (ContinuousMap.inclusion T.range_f_subset b) = b) ∧
      Nonempty (((ContinuousMap.inclusion T.range_f_subset).comp r).HomotopyRel
        (ContinuousMap.id (range φ)) {w | (w : N) ∈ range f}) := by
  let r : C(range φ, range f) :=
    ⟨fun w ↦ ⟨f (T.retraction w), mem_range_self _⟩,
      (T.isEmbedding_f.continuous.comp T.retraction.continuous).subtype_mk _⟩
  have hr (w : range φ) : ContinuousMap.inclusion T.range_f_subset (r w) =
      T.coreMap (T.retraction w) :=
    rfl
  refine ⟨r, ?_, ⟨?_⟩⟩
  · rintro ⟨_, x, rfl⟩
    exact Subtype.ext (congrArg f (T.retraction_apply_f x))
  · have hcomp : (ContinuousMap.inclusion T.range_f_subset).comp r =
        T.coreMap.comp T.retraction :=
      ContinuousMap.ext hr
    rw [hcomp, ← T.range_coreMap]
    exact T.deformation

end TauCeti.IsTubularNeighborhood
