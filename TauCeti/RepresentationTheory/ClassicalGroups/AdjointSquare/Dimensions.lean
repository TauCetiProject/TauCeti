/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeromie Beasley
-/
module

public import TauCeti.RepresentationTheory.ClassicalGroups.AdjointSquare.Parity
import TauCeti.Algebra.Lie.GeneralLinear.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Two disjoint eight-dimensional images in the adjoint square

The two injective intertwiners have images of dimension eight. When `2 ≠ 0`, their
opposite flip signs force these images to be disjoint, so together they span a
sixteen-dimensional subspace of the tensor square of `sl₃`.
-/

public section
namespace TauCeti.AdjointSquare

variable (K : Type*) [Field K] [NeZero (3 : K)]

/-- Swapping factors has opposite signs on the two images, so their intersection vanishes
when `2 ≠ 0`. -/
theorem disjoint_range_alternatingEmbeddingMap_symmetricEmbeddingMap [NeZero (2 : K)] :
    Disjoint (LinearMap.range (alternatingEmbeddingMap (K := K)).toLinearMap)
      (LinearMap.range (symmetricEmbeddingMap (K := K)).toLinearMap) := by
  rw [disjoint_iff_inf_le]
  intro x hx
  obtain ⟨u, hu⟩ := hx.1
  obtain ⟨v, hv⟩ := hx.2
  have ha := comm_alternatingEmbeddingMap (K := K) u
  have hs := comm_symmetricEmbeddingMap (K := K) v
  -- `IntertwiningMap.coe_toLinearMap` is `rfl`, so `rw` sees no coercion to rewrite.
  change alternatingEmbeddingMap (K := K) u = x at hu
  change symmetricEmbeddingMap (K := K) v = x at hv
  rw [hu] at ha
  rw [hv] at hs
  have hneg : -x = x := ha.symm.trans hs
  have htwo : (2 : K) • x = 0 := by
    rw [two_smul]
    exact (congrArg (fun z => z + x) hneg.symm).trans (neg_add_cancel x)
  exact (smul_eq_zero.mp htwo).resolve_left (NeZero.ne (2 : K))

/-- The alternating copy of the adjoint has dimension eight. -/
theorem finrank_range_alternatingEmbeddingMap :
    Module.finrank K (LinearMap.range (alternatingEmbeddingMap (K := K)).toLinearMap) = 8 := by
  rw [LinearMap.finrank_range_of_inj (alternatingEmbeddingMap_injective (K := K))]
  simp [TauCeti.finrank_sl]

/-- The symmetric copy of the adjoint has dimension eight. -/
theorem finrank_range_symmetricEmbeddingMap :
    Module.finrank K (LinearMap.range (symmetricEmbeddingMap (K := K)).toLinearMap) = 8 := by
  rw [LinearMap.finrank_range_of_inj (symmetricEmbeddingMap_injective (K := K))]
  simp [TauCeti.finrank_sl]

/-- The span of the two disjoint octet images has dimension sixteen when `2 ≠ 0`. -/
theorem finrank_range_alternatingEmbeddingMap_sup_range_symmetricEmbeddingMap [NeZero (2 : K)] :
    Module.finrank K
      ↥(LinearMap.range (alternatingEmbeddingMap (K := K)).toLinearMap ⊔
        LinearMap.range (symmetricEmbeddingMap (K := K)).toLinearMap) = 16 := by
  have h := Submodule.finrank_sup_add_finrank_inf_eq
    (LinearMap.range (alternatingEmbeddingMap (K := K)).toLinearMap)
    (LinearMap.range (symmetricEmbeddingMap (K := K)).toLinearMap)
  rw [(disjoint_range_alternatingEmbeddingMap_symmetricEmbeddingMap K).eq_bot, finrank_bot,
    add_zero, finrank_range_alternatingEmbeddingMap K, finrank_range_symmetricEmbeddingMap K] at h
  exact h

end TauCeti.AdjointSquare
