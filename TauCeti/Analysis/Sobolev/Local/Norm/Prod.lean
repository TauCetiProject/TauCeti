/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Local.Norm

/-!
# The local Sobolev norm of a pair

Pairing two Sobolev maps lets one apply composition estimates to a function of both maps.
The product carries its usual maximum norm at order zero.
-/

public section

open scoped ENNReal

namespace TauCeti

/-- The extended Sobolev norm of a pair is at most the sum of the component norms. -/
theorem eLpNormWkp_prodMk_le {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace F] [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    {p : ℝ≥0∞} (hp : 1 ≤ p) {U : Set ℂ} {k : ℕ} {u : ℂ → F} {v : ℂ → G} :
    eLpNormWkp p U k (fun z ↦ (u z, v z)) ≤ eLpNormWkp p U k u + eLpNormWkp p U k v := by
  let a := ContinuousLinearMap.inl ℝ F G
  let b := ContinuousLinearMap.inr ℝ F G
  have h : (fun z ↦ (u z, v z)) = (a ∘ u) + (b ∘ v) := by
    ext z <;> simp [a, b]
  rw [h]
  exact (eLpNormWkp_add_le hp).trans (add_le_add
    (eLpNormWkp_clm_comp_le_of_norm_le_one a (ContinuousLinearMap.norm_inl_le_one ℝ F G))
    (eLpNormWkp_clm_comp_le_of_norm_le_one b (ContinuousLinearMap.norm_inr_le_one ℝ F G)))

end TauCeti
