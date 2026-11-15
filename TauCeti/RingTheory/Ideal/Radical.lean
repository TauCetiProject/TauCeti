/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Finiteness.Ideal
public import Mathlib.RingTheory.Ideal.Operations

/-!
# Radicals of finitely generated subideals

The radical of an ideal `I` of a commutative semiring is the directed supremum of the radicals of
the finitely generated ideals contained in `I`: if `x ^ n ∈ I` then `x` already lies in the
radical of the principal ideal `(x ^ n) ≤ I`. In particular a radical ideal is the directed
supremum of the radicals of its finitely generated subideals. This reduces statements about
quotients by radical ideals that pass to directed unions to the radicals of finitely generated
ideals, for instance the vanishing of `Tor` of radical quotients of perfect rings. We also record
that a finitely generated ideal lies in the radical of `J` iff some positive power lies in `J`.

## Main results

* `Ideal.directed_radical_fg`: the radicals of the finitely generated subideals of `I` form a
  directed family.
* `Ideal.iSup_radical_fg`: their supremum is the radical of `I`.
* `Ideal.le_radical_iff_exists_pos_pow_le`: a finitely generated ideal lies in `J.radical` iff
  some positive power lies in `J`.
-/

public section

namespace Ideal

variable {R : Type*} [CommSemiring R]

/-- The radicals of the finitely generated subideals of an ideal `I` form a directed family. -/
theorem directed_radical_fg (I : Ideal R) :
    Directed (· ≤ ·) fun N : {N : Ideal R // N.FG ∧ N ≤ I} ↦ N.1.radical := fun N₁ N₂ ↦
  ⟨⟨N₁.1 ⊔ N₂.1, Submodule.FG.sup N₁.2.1 N₂.2.1, sup_le N₁.2.2 N₂.2.2⟩,
    radical_mono le_sup_left, radical_mono le_sup_right⟩

/-- The radical of an ideal `I` is the supremum of the radicals of the finitely generated ideals
contained in `I`. -/
theorem iSup_radical_fg (I : Ideal R) :
    ⨆ N : {N : Ideal R // N.FG ∧ N ≤ I}, N.1.radical = I.radical := by
  refine le_antisymm (iSup_le fun N ↦ radical_mono N.2.2) fun x ⟨n, hx⟩ ↦ ?_
  refine Submodule.mem_iSup_of_mem (⟨span {x ^ n}, Submodule.fg_span_singleton _,
    (span_singleton_le_iff_mem I).2 hx⟩ : {N : Ideal R // N.FG ∧ N ≤ I}) ⟨n, ?_⟩
  exact mem_span_singleton_self _

/-- A finitely generated ideal `I` lies in the radical of `J` if and only if `I ^ k ≤ J` for some
positive integer `k`. -/
theorem le_radical_iff_exists_pos_pow_le {I J : Ideal R} (hI : I.FG) :
    I ≤ J.radical ↔ ∃ k > 0, I ^ k ≤ J := by
  refine ⟨fun h ↦ ?_, fun ⟨k, _, hk⟩ x hx ↦ ⟨k, hk (pow_mem_pow hx k)⟩⟩
  obtain ⟨k, hk⟩ := exists_pow_le_of_le_radical_of_fg h hI
  rcases Nat.eq_zero_or_pos k with rfl | hkpos
  · exact ⟨1, Nat.one_pos, le_top.trans (by simpa [pow_zero, one_eq_top] using hk)⟩
  · exact ⟨k, hkpos, hk⟩

end Ideal

end
