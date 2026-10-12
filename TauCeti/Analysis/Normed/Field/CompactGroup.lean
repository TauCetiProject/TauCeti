/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Topology.Algebra.Constructions

import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Analysis.Normed.Group.Continuity

/-!
# Continuous homomorphisms from a compact group into the units of a normed division ring

A continuous homomorphism `f` from a compact group into the units of a normed division ring takes
values of norm `1`: the norms `‖f (g ^ n)‖ = ‖f g‖ ^ n` stay bounded for all `n : ℤ`, which forces
`‖f g‖ = 1`.  For `𝕜 = ℂ` this says that a continuous character of a compact group is unitary.
-/

public section

namespace ContinuousMonoidHom

variable {G 𝕜 : Type*} [Group G] [TopologicalSpace G] [CompactSpace G] [NormedDivisionRing 𝕜]

/-- **A continuous homomorphism from a compact group into the units of a normed division ring takes
values of norm `1`.** -/
theorem norm_apply_eq_one_of_compactSpace (f : G →ₜ* 𝕜ˣ) (g : G) : ‖(f g : 𝕜)‖ = 1 := by
  obtain ⟨B, hB⟩ := (isCompact_range
    (continuous_norm.comp (Units.continuous_val.comp f.continuous))).bddAbove
  have hle (g : G) : ‖(f g : 𝕜)‖ ≤ 1 := by
    by_contra! h
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt B h
    have hgn : ‖(f (g ^ n) : 𝕜)‖ ≤ B := hB ⟨g ^ n, rfl⟩
    rw [map_pow, Units.val_pow_eq_pow_val, norm_pow] at hgn
    exact hn.not_ge hgn
  refine (hle g).antisymm ?_
  have hinv := hle g⁻¹
  rw [map_inv, Units.val_inv_eq_inv_val, norm_inv] at hinv
  exact (inv_le_one₀ (norm_pos_iff.mpr (f g).ne_zero)).mp hinv

end ContinuousMonoidHom
