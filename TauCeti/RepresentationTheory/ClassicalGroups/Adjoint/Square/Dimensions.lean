/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeromie Beasley
-/
module

public import TauCeti.RepresentationTheory.ClassicalGroups.Adjoint.Square.Parity
import TauCeti.Algebra.Lie.GeneralLinear.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Dimensions of the two adjoint images in the tensor square

For size `n ≥ 3` nonzero in the scalar field, each image has dimension `n ^ 2 - 1`.
The two images are disjoint when `2 ≠ 0`, so their sum has twice that dimension.
In size three the separate images are octets and their sum has dimension sixteen.
-/

public section
namespace TauCeti.AdjointSquare

section Dimensions

variable (K : Type*) [Field K] (n : ℕ) [NeZero (n : K)]

/-- Swapping factors has opposite signs on the two images, so their intersection vanishes
when `2 ≠ 0`. -/
theorem disjoint_range_alternatingEmbeddingMap_symmetricEmbeddingMap [NeZero (2 : K)] :
    Disjoint (LinearMap.range (alternatingEmbeddingMap K n).toLinearMap)
      (LinearMap.range (symmetricEmbeddingMap K n).toLinearMap) := by
  rw [disjoint_iff_inf_le]
  intro x hx
  obtain ⟨hxAlt, hxSymm⟩ := Submodule.mem_inf.mp hx
  obtain ⟨u, hu⟩ := LinearMap.mem_range.mp hxAlt
  obtain ⟨v, hv⟩ := LinearMap.mem_range.mp hxSymm
  have ha := comm_alternatingEmbeddingMap u
  have hs := comm_symmetricEmbeddingMap v
  rw [Representation.IntertwiningMap.toLinearMap_apply] at hu hv
  rw [hu] at ha
  rw [hv] at hs
  have hneg : -x = x := ha.symm.trans hs
  have htwo : (2 : K) • x = 0 := by
    rw [two_smul]
    exact (congrArg (fun z => z + x) hneg.symm).trans (neg_add_cancel x)
  exact (smul_eq_zero.mp htwo).resolve_left (NeZero.ne (2 : K))

/-- The alternating image has the same dimension as the adjoint when the size is at least three. -/
theorem finrank_range_alternatingEmbeddingMap (hn : 3 ≤ n) :
    Module.finrank K (LinearMap.range (alternatingEmbeddingMap K n).toLinearMap) = n ^ 2 - 1 := by
  rw [LinearMap.finrank_range_of_inj (alternatingEmbeddingMap_injective K n hn)]
  simp [TauCeti.finrank_sl]

/-- The symmetric image has the same dimension as the adjoint when the size is at least three. -/
theorem finrank_range_symmetricEmbeddingMap (hn : 3 ≤ n) :
    Module.finrank K (LinearMap.range (symmetricEmbeddingMap K n).toLinearMap) = n ^ 2 - 1 := by
  rw [LinearMap.finrank_range_of_inj (symmetricEmbeddingMap_injective K n hn)]
  simp [TauCeti.finrank_sl]

/-- The sum of the two disjoint adjoint images has twice the dimension of the adjoint. -/
theorem finrank_range_alternatingEmbeddingMap_sup_range_symmetricEmbeddingMap [NeZero (2 : K)]
    (hn : 3 ≤ n) :
    Module.finrank K
      ↥(LinearMap.range (alternatingEmbeddingMap K n).toLinearMap ⊔
        LinearMap.range (symmetricEmbeddingMap K n).toLinearMap) = 2 * (n ^ 2 - 1) := by
  have h := Submodule.finrank_sup_add_finrank_inf_eq
    (LinearMap.range (alternatingEmbeddingMap K n).toLinearMap)
    (LinearMap.range (symmetricEmbeddingMap K n).toLinearMap)
  rw [(disjoint_range_alternatingEmbeddingMap_symmetricEmbeddingMap K n).eq_bot, finrank_bot,
    add_zero, finrank_range_alternatingEmbeddingMap K n hn,
    finrank_range_symmetricEmbeddingMap K n hn] at h
  simpa only [two_mul] using h

end Dimensions

section Octets

variable (K : Type*) [Field K] [NeZero (3 : K)]

/-- The alternating image in size three has dimension eight. -/
theorem finrank_range_alternatingEmbeddingMap_three :
    Module.finrank K (LinearMap.range (alternatingEmbeddingMap K 3).toLinearMap) = 8 :=
  finrank_range_alternatingEmbeddingMap K 3 le_rfl

/-- The symmetric image in size three has dimension eight. -/
theorem finrank_range_symmetricEmbeddingMap_three :
    Module.finrank K (LinearMap.range (symmetricEmbeddingMap K 3).toLinearMap) = 8 :=
  finrank_range_symmetricEmbeddingMap K 3 le_rfl

/-- The two octets span a sixteen-dimensional subspace when `2 ≠ 0`. -/
theorem finrank_range_alternatingEmbeddingMap_sup_range_symmetricEmbeddingMap_three
    [NeZero (2 : K)] :
    Module.finrank K
      ↥(LinearMap.range (alternatingEmbeddingMap K 3).toLinearMap ⊔
        LinearMap.range (symmetricEmbeddingMap K 3).toLinearMap) = 16 :=
  finrank_range_alternatingEmbeddingMap_sup_range_symmetricEmbeddingMap K 3 le_rfl

end Octets

end TauCeti.AdjointSquare
