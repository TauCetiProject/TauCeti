/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.Coxeter.FixedPoints
public import TauCeti.LinearAlgebra.RootSystem.Inversions.Length

/-!
# Orbits of a Coxeter element on the roots

Let `w` be an element of the Weyl group of a finite root system which fixes no nonzero vector of
the weight space, such as a Coxeter element. Along the orbit `j, w j, w² j, …` of a root, the sum
of the roots over a period is fixed by `w`, so it vanishes, and so does the sum of their heights.
Hence every orbit contains positive and negative roots, so it passes from a positive root to a
negative one: within `orderOf w` steps it meets the inversion set of `w`, the positive roots that
`w` sends to negative roots. Counting the pairs (inversion, number of steps) bounds the number of
roots by `orderOf w` times the number of inversions.

For a Coxeter element `c`, a product of the `r` simple reflections, the inversion set has at most
`r` elements, so a finite crystallographic root system has at most `r * orderOf c` roots. Combined
with the invariant degrees this is the inequality `|Φ| ≤ r h` in the proof of the formula
`|Φ| = r h` for the Coxeter number `h`.

## Main results

* `TauCeti.exists_lt_orderOf_weylGroupToPerm_pow_mem_inversions`: if `w` fixes no nonzero vector,
  every root reaches an inversion of `w` within `orderOf w` steps of its `w`-orbit.
* `TauCeti.natCard_le_orderOf_mul_ncard_inversions`: if `w` fixes no nonzero vector, the number of
  roots is at most `orderOf w` times the number of inversions of `w`.
* `TauCeti.natCard_le_orderOf_wordProd_mul_length`: a finite crystallographic reduced root system
  has at most `r * orderOf c` roots, for a Coxeter element `c` spelled by a word of `r` letters.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Ch. V, §6, no. 2.
* J. E. Humphreys, *Reflection Groups and Coxeter Groups*, Cambridge University Press (1990),
  § 3.18.
-/

public section

namespace TauCeti

open RootPairing

variable {ι R M N : Type*} [CommRing R] [CharZero R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] {P : RootPairing ι R M N} [Finite ι] [P.IsRootSystem]
  (b : P.Base)

/-- Along the orbit of a root under a Weyl-group element fixing no nonzero vector, the heights over
a period add up to zero: the sum of the roots over a period is a fixed vector. -/
private theorem sum_range_height_weylGroupToPerm_pow_eq_zero {w : P.weylGroup}
    (hw : ∀ y : M, w • y = y → y = 0) (j : ι) :
    ∑ k ∈ Finset.range (orderOf w), b.height (P.weylGroupToPerm (w ^ k) j) = 0 := by
  have := P.finite_weylGroup
  obtain ⟨n, hn⟩ := Nat.exists_eq_add_one_of_ne_zero (orderOf_pos w).ne'
  -- The sum of the roots over a period is fixed by `w`, hence zero.
  have hfix : ∑ k ∈ Finset.range (orderOf w), (w ^ k) • P.root j = 0 := by
    refine hw _ ?_
    rw [Finset.smul_sum, hn, Finset.sum_range_succ, Finset.sum_range_succ']
    simp only [← mul_smul, ← pow_succ', ← hn, pow_orderOf_eq_one, pow_zero]
  have hheight := congrArg (heightLinearMap P b) hfix
  simp only [map_sum, P.weylGroup_apply_root, heightLinearMap_root, map_zero] at hheight
  exact_mod_cast hheight

/-- **Every orbit of a fixed-point-free Weyl-group element meets its inversion set.** If `w` fixes
no nonzero vector, then for every root `j` some `w ^ k j` with `k < orderOf w` is a positive root
that `w` sends to a negative root. -/
theorem exists_lt_orderOf_weylGroupToPerm_pow_mem_inversions {w : P.weylGroup}
    (hw : ∀ y : M, w • y = y → y = 0) (j : ι) :
    ∃ k < orderOf w, P.weylGroupToPerm (w ^ k) j ∈ inversions P b w := by
  have := P.finite_weylGroup
  have hpos := orderOf_pos w
  set a : ℕ → ι := fun k ↦ P.weylGroupToPerm (w ^ k) j with ha
  have hmod (k : ℕ) : a (k % orderOf w) = a k := by simp only [ha, pow_mod_orderOf]
  have hsucc (k : ℕ) : a (k + 1) = P.weylGroupToPerm w (a k) := by
    simp only [ha, pow_succ', map_mul, Equiv.Perm.mul_apply]
  have hper (k : ℕ) : a (k + orderOf w) = a k := by
    simp only [ha, pow_add, pow_orderOf_eq_one, mul_one]
  by_contra! hno
  replace hno : ∀ k < orderOf w, a k ∉ inversions P b w := hno
  -- Positivity propagates along the orbit, since no step goes from positive to negative.
  have hstep (k : ℕ) (hk : b.IsPos (a k)) : b.IsPos (a (k + 1)) := by
    have := hno (k % orderOf w) (Nat.mod_lt _ hpos)
    rw [mem_inversions, hmod] at this
    rw [hsucc]
    by_contra h
    exact this ⟨hk, h⟩
  have hsum := sum_range_height_weylGroupToPerm_pow_eq_zero b hw j
  by_cases hex : ∃ p, b.IsPos (a p)
  · -- Then every root of the orbit is positive, and the heights add up to a positive number.
    obtain ⟨p, hp⟩ := hex
    have hall (t : ℕ) : b.IsPos (a (p % orderOf w + t)) := by
      induction t with
      | zero => rwa [add_zero, hmod]
      | succ t ih => exact hstep _ ih
    refine (Finset.sum_pos (fun k _ ↦ ?_) (Finset.nonempty_range_iff.mpr hpos.ne')).ne' hsum
    have hidx : p % orderOf w + (k + orderOf w - p % orderOf w) = k + orderOf w := by
      have := Nat.mod_lt p hpos
      omega
    have hk := hall (k + orderOf w - p % orderOf w)
    rw [hidx, hper] at hk
    exact one_le_height_of_mem_posRoots P b ((mem_posRoots P b _).2 hk)
  · -- Otherwise every root of the orbit is negative, and the heights add up to a negative number.
    push Not at hex
    exact (Finset.sum_neg
      (fun k _ ↦ height_neg_of_mem_negRoots P b ((mem_negRoots P b _).2 (hex k)))
      (Finset.nonempty_range_iff.mpr hpos.ne')).ne hsum

/-- **A fixed-point-free Weyl-group element has at most `orderOf w` roots per inversion.** If `w`
fixes no nonzero vector, then the number of roots is at most `orderOf w` times the number of
positive roots that `w` sends to negative roots. -/
theorem natCard_le_orderOf_mul_ncard_inversions {w : P.weylGroup}
    (hw : ∀ y : M, w • y = y → y = 0) :
    Nat.card ι ≤ orderOf w * (inversions P b w).ncard := by
  choose k hk hkinv using exists_lt_orderOf_weylGroupToPerm_pow_mem_inversions b hw
  let F : ι → Fin (orderOf w) × inversions P b w := fun j ↦ (⟨k j, hk j⟩, ⟨_, hkinv j⟩)
  have hF : Function.Injective F := fun j j' hjj' ↦ by
    simp only [F, Prod.mk.injEq, Fin.mk.injEq, Subtype.mk.injEq] at hjj'
    rw [← hjj'.1] at hjj'
    exact (P.weylGroupToPerm (w ^ k j)).injective hjj'.2
  rw [← Nat.card_coe_set_eq, ← Nat.card_fin (orderOf w), ← Nat.card_prod]
  exact Nat.card_le_card_of_injective F hF

variable [IsDomain R] [P.IsCrystallographic] [P.IsReduced]

/-- **A root system has at most `r * orderOf c` roots, for a Coxeter element `c`.** For a base of
a finite reduced crystallographic root system, a word using every simple reflection exactly once
spells an element `c` such that the number of roots is at most `orderOf c` times the length of the
word. -/
theorem natCard_le_orderOf_wordProd_mul_length {l : List b.support} (hl : l.Nodup)
    (hl' : ∀ i, i ∈ l) :
    Nat.card ι ≤ orderOf (wordProd P b l) * l.length :=
  (natCard_le_orderOf_mul_ncard_inversions b fun _ hy ↦
    (wordProd_smul_eq_self_iff_eq_zero b hl hl').mp hy).trans
    (Nat.mul_le_mul_left _ (ncard_inversions_wordProd_le_length P b l))

end TauCeti
