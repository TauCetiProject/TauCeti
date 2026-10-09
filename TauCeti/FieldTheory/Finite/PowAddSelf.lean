/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.GroupTheory.Index

/-!
# The fibres of `b ↦ b ^ q + b` over a field with `q²` elements

Let `K` be a finite field with `q²` elements, where `q = p ^ n` is a power of the
characteristic. The map `T b = b ^ q + b` is additive, and it is the trace from `K` to its
subfield with `q` elements, although that subfield plays no role in the statement here. Every
`c` with `c ^ q = c` has exactly `q` preimages under `T`.

The kernel of `T` consists of roots of `X ^ q + X`, and its image of roots of `X ^ q - X`, since
`(b ^ q + b) ^ q = b ^ (q²) + b ^ q = b + b ^ q`. So both have at most `q` elements. Their
product is `|K| = q²`, so both have exactly `q` elements. The image is then the whole root set
of `X ^ q - X` in `K`, and each fibre over it is a coset of the kernel.

This is the count behind the order `q³` of the translation group of the Hermitian function
field: for `a ∈ K`, the element `c = a ^ (q + 1)` satisfies `c ^ q = c`.

## Main results

* `TauCeti.FiniteField.natCard_pow_add_self_eq`: `#{b | b ^ q + b = c} = q` whenever
  `c ^ q = c`.
-/

public section

open Finset Polynomial

namespace TauCeti

namespace FiniteField

variable {K : Type*} [Field K] {p n : ℕ} [ExpChar K p]

/-- In a field with `q²` elements, `q = p ^ n` a power of the exponential characteristic, every
`c` with `c ^ q = c` is of the form `b ^ q + b` for exactly `q` elements `b`. -/
theorem natCard_pow_add_self_eq [Finite K] (hK : Nat.card K = (p ^ n) ^ 2) {c : K}
    (hc : c ^ p ^ n = c) : Nat.card {b : K // b ^ p ^ n + b = c} = p ^ n := by
  classical
  have := Fintype.ofFinite K
  rw [Nat.card_eq_fintype_card] at hK
  set q := p ^ n with hqdef
  -- A field has at least two elements, so `q > 1`.
  have hq : 1 < q := by
    have := Fintype.one_lt_card (α := K)
    rw [hK] at this
    by_contra hle
    interval_cases q <;> simp at this
  -- The additive map `T b = b ^ q + b`.
  let T : K →+ K :=
    { toFun b := b ^ q + b
      map_zero' := by simp [show q ≠ 0 by omega]
      map_add' u v := by simp only [hqdef, add_pow_expChar_pow]; ring }
  have hT (b : K) : T b = b ^ q + b := rfl
  have hpow (b : K) : b ^ q ^ 2 = b := by rw [← hK]; exact FiniteField.pow_card b
  -- Kernel and image of `T` lie in the root sets of `X ^ q + X` and `X ^ q - X`.
  have hX1 : (X ^ q + X : K[X]).natDegree = q := by
    rw [natDegree_add_eq_left_of_degree_lt] <;> simp [hq]
  have hX2 : (X ^ q - X : K[X]).natDegree = q := by
    rw [natDegree_sub_eq_left_of_natDegree_lt] <;> simp [hq]
  have hker : #({b | T b = 0} : Finset K) ≤ q := by
    refine (card_le_degree_of_subset_roots fun b hb ↦ ?_).trans hX1.le
    have hb : T b = 0 := (Finset.mem_filter.mp hb).2
    rw [mem_roots (ne_zero_of_natDegree_gt (hX1 ▸ hq))]
    simpa [hT] using hb
  have himage_sub : (Finset.univ.image T) ⊆ ({c | c ^ q = c} : Finset K) := by
    intro c hc
    obtain ⟨b, -, rfl⟩ := Finset.mem_image.mp hc
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hT, hqdef, add_pow_expChar_pow]
    rw [← pow_mul, ← sq, hpow, add_comm]
  have hfix : #({c | c ^ q = c} : Finset K) ≤ q := by
    refine (card_le_degree_of_subset_roots fun c hc ↦ ?_).trans hX2.le
    have hc : c ^ q = c := (Finset.mem_filter.mp hc).2
    rw [mem_roots (ne_zero_of_natDegree_gt (hX2 ▸ hq))]
    simp [hc]
  -- `|ker T| · |im T| = q²`, so both have exactly `q` elements.
  have hmul : Nat.card T.ker * Nat.card T.range = q ^ 2 := by
    rw [AddSubgroup.card_ker_mul_card_range, Nat.card_eq_fintype_card, hK]
  have hkerc : Nat.card T.ker = #({b | T b = 0} : Finset K) := by
    rw [Nat.card_eq_fintype_card, ← Fintype.card_coe]
    exact Fintype.card_congr (Equiv.subtypeEquivRight fun b ↦ by simp [AddMonoidHom.mem_ker])
  have hrangec : Nat.card T.range = #(Finset.univ.image T) := by
    rw [Nat.card_eq_fintype_card, ← Fintype.card_coe]
    exact Fintype.card_congr (Equiv.subtypeEquivRight fun c ↦ by simp [AddMonoidHom.mem_range])
  have hkerq : #({b | T b = 0} : Finset K) = q := by
    have := (Finset.card_le_card himage_sub).trans hfix
    rw [hkerc, hrangec] at hmul
    nlinarith
  have himage : (Finset.univ.image T) = ({c | c ^ q = c} : Finset K) := by
    refine Finset.eq_of_subset_of_card_le himage_sub (hfix.trans ?_)
    rw [hkerc, hrangec, hkerq] at hmul
    nlinarith
  -- Each fibre over the image has the size of the kernel.
  have hcmem : c ∈ Set.range T := by
    have : c ∈ Finset.univ.image T := by simp [himage, hc]
    simpa using this
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  exact (AddMonoidHom.card_fiber_eq_of_mem_range T hcmem ⟨0, map_zero T⟩).trans hkerq

end FiniteField

end TauCeti
