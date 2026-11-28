/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- `Valued` supplies the valuation topology on `K`, `Matrix m m K`, and `GL m K`.
public import Mathlib.Topology.Algebra.Valued.ValuationTopology
-- `Matrix.GeneralLinearGroup` topology and `Continuous.generalLinearGroup_map`.
public import Mathlib.Topology.Algebra.Group.Matrix
-- `TauCeti.mem_map_iwahoriOne_iff` characterizes membership in `I₁` by entry valuations.
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.UpperTriangular.Iwahori.Valuation

import Mathlib.Topology.Algebra.Valued.ValuedField
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Map

/-!
# Topology of pro-`p` Iwahori subgroups of `GL_m` over a valued field

Let `K` be a valued field with valuation `v : Valuation K Γ₀` and valuation subring `𝒪`, and let
`m` be a finite linearly ordered index type. This file characterizes membership in the image
`I₁ ⊆ GL_m(K)` of `TauCeti.iwahoriOne m 𝒪` directly in terms of `Valued.v`, and establishes its
openness and compactness:

* `TauCeti.mem_map_iwahoriOne_iff_valued`: membership in `I₁` expressed via `Valued.v`.
* `TauCeti.isOpen_map_iwahoriOne`: `I₁` is an open (hence closed) subgroup of `GL_m(K)`.
* `TauCeti.isCompact_map_iwahoriOne`: when `𝒪` is compact, `I₁` is compact in `GL_m(K)`.
-/

public section

namespace TauCeti

open Matrix

variable {K : Type*} [Field K] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
variable {m : Type*} [Fintype m] [LinearOrder m]

/-- Membership in the image of the pro-`p` Iwahori subgroup `iwahoriOne m 𝒪` inside `GL m K`,
expressed directly in terms of `Valued.v`. -/
theorem mem_map_iwahoriOne_iff_valued {g : GL m K} :
    g ∈ (iwahoriOne m (Valued.v (R := K)).valuationSubring).map
        (GeneralLinearGroup.map (algebraMap _ K)) ↔
      (∀ i j, Valued.v (g i j) ≤ 1) ∧ (∀ ⦃i j⦄, j < i → Valued.v (g i j) < 1) ∧
        ∀ i, Valued.v (g i i - 1) < 1 := by
  have heq := Valuation.isEquiv_valuation_valuationSubring (Valued.v (R := K))
  simp only [mem_map_iwahoriOne_iff, heq.le_one_iff_le_one.symm, heq.lt_one_iff_lt_one.symm]

/-- The pro-`p` Iwahori subgroup `I₁` is an open subgroup of `GL m K`. -/
theorem isOpen_map_iwahoriOne :
    IsOpen ((iwahoriOne m (Valued.v (R := K)).valuationSubring).map
      (GeneralLinearGroup.map (algebraMap _ K)) : Set (GL m K)) := by
  have hopen_le : IsOpen {x : K | Valued.v x ≤ (1 : Γ₀)} := Valued.isOpen_integer K
  have hopen_lt : IsOpen {x : K | Valued.v x < (1 : Γ₀)} := by
    have hball : IsOpen {x : K | (Valued.v (R := K)).restrict x < 1} := Valued.isOpen_ball K 1
    simpa [Valuation.restrict_lt_iff] using hball
  have hset : ((iwahoriOne m (Valued.v (R := K)).valuationSubring).map
        (GeneralLinearGroup.map (algebraMap _ K)) : Set (GL m K)) =
      (⋂ i : m, ⋂ j : m, {g : GL m K | Valued.v (g i j) ≤ 1}) ∩
      (⋂ i : m, ⋂ j : m, ⋂ (_ : j < i), {g : GL m K | Valued.v (g i j) < 1}) ∩
      (⋂ i : m, {g : GL m K | Valued.v (g i i - 1) < 1}) := by
    ext g
    simp only [SetLike.mem_coe, mem_map_iwahoriOne_iff_valued, Set.mem_inter_iff, Set.mem_iInter,
      Set.mem_ofPred_eq, and_assoc]
  rw [hset]
  have hcont (i j : m) : Continuous fun g : GL m K ↦ (g : Matrix m m K) i j := by fun_prop
  refine (IsOpen.inter ?_ ?_).inter ?_
  · exact isOpen_iInter_of_finite fun i ↦ isOpen_iInter_of_finite fun j ↦
      hopen_le.preimage (hcont i j)
  · exact isOpen_iInter_of_finite fun i ↦ isOpen_iInter_of_finite fun j ↦
      isOpen_iInter_of_finite fun _ ↦ hopen_lt.preimage (hcont i j)
  · exact isOpen_iInter_of_finite fun i ↦
      hopen_lt.preimage ((hcont i i).sub continuous_const)

/-- When the valuation subring of `K` is compact, the pro-`p` Iwahori subgroup `I₁` is compact in
`GL m K`. -/
theorem isCompact_map_iwahoriOne [CompactSpace (Valued.v (R := K)).valuationSubring] :
    IsCompact ((iwahoriOne m (Valued.v (R := K)).valuationSubring).map
      (GeneralLinearGroup.map (algebraMap _ K)) : Set (GL m K)) := by
  let A := (Valued.v (R := K)).valuationSubring
  have : IsTopologicalRing A := Subring.instIsTopologicalRing A.toSubring
  have : CompactSpace (Matrix m m A) := Pi.compactSpace
  have : CompactSpace (GL m A) := Units.isClosedEmbedding_embedProduct.compactSpace
  let f := GeneralLinearGroup.map (n := m) (algebraMap A K)
  have hf_cont : Continuous f := Continuous.generalLinearGroup_map continuous_subtypeVal
  have hf_inj : Function.Injective f := GeneralLinearGroup.map_injective Subtype.val_injective
  have hpre : (iwahoriOne m A : Set (GL m A)) =
      f ⁻¹' (((iwahoriOne m A).map f : Subgroup _) : Set _) := by
    rw [Subgroup.coe_map, Set.preimage_image_eq _ hf_inj]
  have hclosed_I1 : IsClosed (iwahoriOne m A : Set (GL m A)) := by
    rw [hpre]
    exact (((iwahoriOne m A).map f).isClosed_of_isOpen isOpen_map_iwahoriOne).preimage hf_cont
  simpa [Subgroup.coe_map] using hclosed_I1.isCompact.image hf_cont

end TauCeti
