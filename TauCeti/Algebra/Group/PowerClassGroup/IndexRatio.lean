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

import Mathlib.Data.Rat.Cast.Defs

/-!
# Power-subgroup index from rational cokernel-to-kernel ratios

When the rational cokernel-to-kernel ratio `[H : range f] / #ker f` of a group homomorphism
`f : G →* H` equals a nonzero natural number `t`, both the index `[H : range f]` and the kernel
order `#ker f` are nonzero (hence finite), and `[H : range f] = t * #ker f`. For the `n`-th power
homomorphism `powMonoidHom n : G →* G` on a commutative group `G`, this bridges the additive
cokernel-to-kernel ratio of `n : Module.End ℤ (Additive G)` (such as the Herbrand quotient or Tate
index) to the multiplicative index `[G : G^n] = t * #G[n]`.

## Main results

* `MonoidHom.index_range_eq_of_div_natCard_ker_eq` and
  `AddMonoidHom.index_range_eq_of_div_natCard_ker_eq`: if `(f.range.index : ℚ) / Nat.card f.ker = t`
  with `t ≠ 0`, then `f.range.index ≠ 0` and `f.range.index = t * Nat.card f.ker`.
* `CommGroup.index_range_powMonoidHom_eq_of_cokerKer_ratio`: the specialization to
  `powMonoidHom n : G →* G` and the additive endomorphism `n : Module.End ℤ (Additive G)`.

## Provenance

Adapted from grh-lean (https://github.com/lsernau/grh-lean at commit
`72fead102f663d5c7a407964a13dc0cf9d977207`, Apache 2.0, Copyright 2026 Anthropic, PBC), file
`src/Lib/ClassField/Global/ExistenceTheorem.lean` (`New.index_range_pow_eq`), generalized to
arbitrary group homomorphisms with an additive counterpart and decoupled from `New.cokerKerIndex`.
-/

@[expose] public section

namespace TauCeti

/-- If the rational ratio `[H : range f] / #ker f` of a group homomorphism `f : G →* H` equals a
nonzero natural number `t`, then `range f` has finite index `t * #ker f` in `H`. -/
@[to_additive AddMonoidHom.index_range_eq_of_div_natCard_ker_eq
  /-- If the rational ratio `[H : range f] / #ker f` of an additive group homomorphism
  `f : G →+ H` equals a nonzero natural number `t`, then `range f` has finite index `t * #ker f` in
  `H`. -/]
theorem MonoidHom.index_range_eq_of_div_natCard_ker_eq {G H : Type*} [Group G] [Group H]
    (f : G →* H) {t : ℕ} (ht : t ≠ 0) (h : (f.range.index : ℚ) / Nat.card f.ker = t) :
    f.range.index ≠ 0 ∧ f.range.index = t * Nat.card f.ker := by
  have hne : (f.range.index : ℚ) / Nat.card f.ker ≠ 0 := by
    rw [h]
    exact Nat.cast_ne_zero.mpr ht
  obtain ⟨hidx, hker⟩ := div_ne_zero_iff.mp hne
  exact ⟨Nat.cast_ne_zero.mp hidx, by exact_mod_cast (div_eq_iff hker).mp h⟩

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
  have hrange : Nat.card (Additive G ⧸ (n : Module.End ℤ (Additive G)).range) = f.range.index := rfl
  have hker : Nat.card (n : Module.End ℤ (Additive G)).ker = Nat.card f.ker := rfl
  rw [hrange, hker] at h
  exact MonoidHom.index_range_eq_of_div_natCard_ker_eq f ht h

end TauCeti
