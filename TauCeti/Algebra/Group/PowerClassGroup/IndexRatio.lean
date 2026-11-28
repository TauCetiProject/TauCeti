/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Data.Rat.Init
public import Mathlib.GroupTheory.Index
public import Mathlib.LinearAlgebra.Quotient.Basic

import TauCeti.GroupTheory.Index.CokerKerRatio

/-!
# Power-subgroup index from rational cokernel-to-kernel ratios

For the `n`-th power homomorphism `powMonoidHom n : G →* G` on a commutative group `G`, this
bridges the additive cokernel-to-kernel ratio of `n : Module.End ℤ (Additive G)` (such as the
Herbrand quotient or Tate index) to the multiplicative index `[G : G^n] = t * #G[n]`.

## Main results

* `TauCeti.CommGroup.index_range_powMonoidHom_eq_of_cokerKer_ratio`: the specialization of
  `MonoidHom.index_range_eq_of_div_natCard_ker_eq` to `powMonoidHom n : G →* G` and the additive
  endomorphism `n : Module.End ℤ (Additive G)`.

## Provenance

Adapted from grh-lean (https://github.com/lsernau/grh-lean at commit
`72fead102f663d5c7a407964a13dc0cf9d977207`, Apache 2.0, Copyright 2026 Anthropic, PBC), file
`src/Lib/ClassField/Global/ExistenceTheorem.lean` (`New.index_range_pow_eq`), decoupled from
`New.cokerKerIndex`.
-/

@[expose] public section

namespace TauCeti

/-- For a commutative group `G` and `n : ℕ`, if the rational cokernel-to-kernel ratio of
multiplication by `n` on `Additive G` equals a nonzero natural number `t`, then the `n`-th powers
have finite index `t * #G[n]` in `G`. -/
theorem CommGroup.index_range_powMonoidHom_eq_of_cokerKer_ratio {G : Type*} [CommGroup G]
    (n : ℕ) {t : ℕ} (ht : t ≠ 0)
    (h : (Nat.card (Additive G ⧸ (n : Module.End ℤ (Additive G)).range) : ℚ) /
      Nat.card (n : Module.End ℤ (Additive G)).ker = t) :
    let f := (powMonoidHom n : G →* G)
    f.range.index ≠ 0 ∧ f.range.index = t * Nat.card f.ker := by
  intro f
  have hker : Nat.card (n : Module.End ℤ (Additive G)).ker = Nat.card f.ker := by
    refine Nat.card_congr (Equiv.subtypeEquiv Additive.toMul fun x ↦ ?_)
    simp [f, powMonoidHom_apply, ← toMul_nsmul]
  have hrange : Nat.card (Additive G ⧸ (n : Module.End ℤ (Additive G)).range) = f.range.index := by
    rw [Subgroup.index]
    refine Nat.card_congr (Quotient.congr Additive.toMul fun a b ↦ ?_)
    simp only [Submodule.quotientRel_def, QuotientGroup.leftRel_apply, LinearMap.mem_range,
      MonoidHom.mem_range, f, natCast_apply_eq_smul, powMonoidHom_apply]
    constructor <;> rintro ⟨c, hc⟩
    · refine ⟨(Additive.toMul c)⁻¹, ?_⟩
      have h := congrArg (fun x ↦ (Additive.toMul x)⁻¹) hc
      simpa [← toMul_nsmul, inv_pow, mul_comm, div_eq_mul_inv] using h
    · refine ⟨-Additive.ofMul c, ?_⟩
      have h := congrArg (fun x ↦ -Additive.ofMul x) hc
      simpa [← ofMul_pow, smul_neg, sub_eq_add_neg, add_comm] using h
  rw [hrange, hker] at h
  exact MonoidHom.index_range_eq_of_div_natCard_ker_eq f ht h

end TauCeti
