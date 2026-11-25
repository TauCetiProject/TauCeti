/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.LocallyConvex.SeparatingDual
public import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition

/-!
# Commutativity of the continuous endomorphism algebra

For a vector space with separating continuous dual, the algebra of continuous endomorphisms
is commutative exactly in dimensions zero and one. In every higher dimension two rank-one
operators with the same defining functional already fail to commute. This applies in
particular to bounded operators on real and complex normed spaces.
-/

public section

namespace ContinuousLinearMap

variable {𝕜 E : Type*} [Field 𝕜] [TopologicalSpace 𝕜] [IsTopologicalRing 𝕜]
  [AddCommGroup E] [TopologicalSpace E] [Module 𝕜 E] [ContinuousSMul 𝕜 E] [SeparatingDual 𝕜 E]

/-- In dimension greater than one there are noncommuting rank-one endomorphisms
of the form `z ↦ f z • x` and `z ↦ f z • y` for the same continuous functional `f`. -/
theorem exists_not_commute_smulRight (h : 1 < Module.rank 𝕜 E) :
    ∃ (f : StrongDual 𝕜 E) (x y : E), ¬ Commute (f.smulRight x) (f.smulRight y) := by
  have := rank_pos_iff_nontrivial.mp (zero_lt_one.trans h)
  obtain ⟨x, hx⟩ := exists_ne (0 : E)
  obtain ⟨f, hf⟩ := SeparatingDual.exists_eq_one (R := 𝕜) hx
  -- If all these operators commuted, evaluating their products at x would give y = f(y) • x.
  by_contra! hc
  apply h.not_ge
  refine rank_le_one_iff.mpr ⟨x, fun y ↦ ⟨f y, ?_⟩⟩
  simpa [hf] using DFunLike.congr_fun (hc f x y).eq x

/-- The continuous endomorphisms of a space with separating dual commute exactly when its
dimension is at most one. Cardinal rank includes infinite-dimensional spaces in the criterion. -/
theorem isMulCommutative_iff_rank_le_one :
    IsMulCommutative (E →L[𝕜] E) ↔ Module.rank 𝕜 E ≤ 1 := by
  constructor
  · intro hc
    by_contra! h
    obtain ⟨f, x, y, hxy⟩ := exists_not_commute_smulRight h
    exact hxy (isMulCommutative_iff.mp hc _ _)
  · intro h
    obtain ⟨x, hx⟩ := rank_le_one_iff.mp h
    refine IsMulCommutative.of_comm fun S T ↦ ext fun y ↦ ?_
    obtain ⟨a, ha⟩ := hx (S x)
    obtain ⟨b, hb⟩ := hx (T x)
    obtain ⟨c, rfl⟩ := hx y
    simp [← ha, ← hb, smul_smul, mul_comm]

end ContinuousLinearMap
