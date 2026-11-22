/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Finiteness.Ideal

/-!
# Radicals of finitely generated subideals

The radical of an ideal `I` of a commutative semiring is the directed supremum of the radicals of
the finitely generated ideals contained in `I`: if `x ^ n ∈ I` then `x` already lies in the
radical of the principal ideal `(x ^ n) ≤ I`. In particular a radical ideal is the directed
supremum of the radicals of its finitely generated subideals. This reduces statements about
quotients by radical ideals that pass to directed unions to the radicals of finitely generated
ideals, for instance the vanishing of `Tor` of radical quotients of perfect rings.

A finitely generated ideal lies in the radical of `K` precisely when one of its positive
powers lies in `K`. Thus this power containment depends only on the radical of the
finitely generated ideal.

## Main results

* `Ideal.directed_radical_fg`: the radicals of the finitely generated subideals of `I` form a
  directed family.
* `Ideal.iSup_radical_fg`: their supremum is the radical of `I`.
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

/-- A finitely generated ideal lies in the radical of `K` if and only if some positive
power of it lies in `K`. -/
theorem le_radical_iff_exists_pow_le_of_fg {I K : Ideal R} (hI : I.FG) :
    I ≤ K.radical ↔ ∃ n : ℕ, 0 < n ∧ I ^ n ≤ K := by
  constructor
  · intro h
    obtain ⟨n, hn⟩ := exists_pow_le_of_le_radical_of_fg h hI
    exact ⟨n + 1, Nat.succ_pos n, (pow_le_pow_right (Nat.le_succ n)).trans hn⟩
  · rintro ⟨n, -, hn⟩ x hx
    exact ⟨n, hn (pow_mem_pow hx n)⟩

/-- If two finitely generated ideals have the same radical, one has a positive power
contained in `K` if and only if the other does. -/
theorem exists_pow_le_iff_of_radical_eq {I J K : Ideal R}
    (hI : I.FG) (hJ : J.FG) (h : I.radical = J.radical) :
    (∃ n : ℕ, 0 < n ∧ I ^ n ≤ K) ↔ ∃ n : ℕ, 0 < n ∧ J ^ n ≤ K := by
  rw [← le_radical_iff_exists_pow_le_of_fg hI, ← le_radical_iff_exists_pow_le_of_fg hJ,
    ← radical_le_radical_iff (I := I), ← radical_le_radical_iff (I := J), h]

end Ideal

end
