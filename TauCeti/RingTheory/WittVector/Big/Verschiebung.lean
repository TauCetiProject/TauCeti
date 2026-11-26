/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.WittVector.Big.Basic

import Mathlib.Algebra.Module.Torsion.Free
import Mathlib.Algebra.MvPolynomial.Counit
import Mathlib.RingTheory.MvPolynomial.Basic

/-!
# The big Witt Verschiebung

For a truncation set `S` and a natural number `n`, the Verschiebung
`V_n : W_{S/n}(R) → W_S(R)` moves the coordinate of index `e` to index `n * e` and puts zeros
at the indices not divisible by `n`: `(V_n x)_{n e} = x_e`. It is additive, although it is not
multiplicative, and on ghost components it is given by
`w_m(V_n x) = n * w_{m/n}(x)` when `n ∣ m` and `w_m(V_n x) = 0` otherwise.

Additivity is proved by comparing ghost components over an integral polynomial ring, where the
ghost map is injective, and specialising along the coordinatewise map induced by
`MvPolynomial.counit`; the ghost formula itself is the divisor-sum identity
`ghostPolynomial_ite_dvd`, valid over every semiring.

## Main definitions

* `TauCeti.BigWittVector.verschiebung n`: the additive Verschiebung
  `W_{S/n}(R) →+ W_S(R)`.

## Main results

* `TauCeti.BigWitt.ghostPolynomial_ite_dvd`: the ghost components of a coordinate sequence
  spread out along the multiples of `n`.
* `TauCeti.BigWittVector.coeff_verschiebung`: the coordinates of `V_n x`.
* `TauCeti.BigWittVector.ghostMap_verschiebung_mul` and
  `TauCeti.BigWittVector.ghostMap_verschiebung_of_not_dvd`: the ghost components of `V_n x`.
* `TauCeti.BigWittVector.verschiebung_map` and `TauCeti.BigWittVector.restrict_verschiebung`:
  the Verschiebung commutes with coefficient maps and with restriction.
* `TauCeti.BigWittVector.verschiebung_one` and
  `TauCeti.BigWittVector.verschiebung_verschiebung`: `V_1` is the identity and
  `V_a V_b = V_{a b}`.
* `TauCeti.BigWittVector.verschiebung_injective`: every Verschiebung is injective.

## References

* L. Hesselholt, *The big de Rham–Witt complex*, Acta Math. 214 (2015), §1, Lemma 1.5.
-/

public section

noncomputable section

namespace TauCeti

open Finset

namespace BigWitt

variable {R : Type*} [Semiring R]

/-- **Ghost components of a spread-out sequence.** Moving the coordinate of index `e` to index
`n * e` and putting zeros at the indices not divisible by `n` multiplies the ghost components by
`n` and spreads them out the same way:
`w_m(x') = n * w_{m/n}(x)` if `n ∣ m` and `w_m(x') = 0` otherwise. -/
theorem ghostPolynomial_ite_dvd (n m : ℕ) (x : ℕ → R) :
    ghostPolynomial m (fun k ↦ if n ∣ k then x (k / n) else 0) =
      if n ∣ m then n * ghostPolynomial (m / n) x else 0 := by
  rcases eq_or_ne m 0 with rfl | hm
  · simp
  -- a term indexed by a divisor `d` of `m` not divisible by `n` is `d * 0 ^ (m / d) = 0`
  have hzero : ∀ d ∈ m.divisors, ¬n ∣ d →
      (d : R) * (if n ∣ d then x (d / n) else 0) ^ (m / d) = 0 := fun d hd hnd ↦ by
    rw [ite_eq_right hnd,
      zero_pow (Nat.div_pos (Nat.divisor_le hd) (Nat.pos_of_mem_divisors hd)).ne', mul_zero]
  rw [ghostPolynomial_eq_sum]
  split_ifs with hnm
  · -- the divisors of `n * k` divisible by `n` are the `n * e` with `e ∣ k`
    obtain ⟨k, rfl⟩ := hnm
    have hn : 0 < n := Nat.pos_of_ne_zero (left_ne_zero_of_mul hm)
    have hk : k ≠ 0 := right_ne_zero_of_mul hm
    rw [Nat.mul_div_cancel_left k hn, ghostPolynomial_eq_sum, mul_sum,
      ← sum_subset (s₁ := k.divisors.map ⟨(n * ·), mul_right_injective₀ hn.ne'⟩), sum_map]
    · refine sum_congr rfl fun e _ ↦ ?_
      simp only [Function.Embedding.coeFn_mk, dvd_mul_right, ite_true,
        Nat.mul_div_cancel_left e hn, Nat.mul_div_mul_left k e hn, Nat.cast_mul, mul_assoc]
    · intro d hd
      obtain ⟨e, he, rfl⟩ := mem_map.1 hd
      exact Nat.mem_divisors.2 ⟨mul_dvd_mul_left n (Nat.dvd_of_mem_divisors he), hm⟩
    · intro d hd hdmap
      refine hzero d hd fun ⟨e, he⟩ ↦ hdmap (mem_map.2 ⟨e, Nat.mem_divisors.2 ⟨?_, hk⟩, he.symm⟩)
      exact (Nat.mul_dvd_mul_iff_left hn).1 (he ▸ Nat.dvd_of_mem_divisors hd)
  · exact sum_eq_zero fun d hd ↦ hzero d hd fun hnd ↦ hnm (hnd.trans (Nat.dvd_of_mem_divisors hd))

end BigWitt

namespace BigWittVector

open BigWitt _root_.MvPolynomial Function

variable {S T : TruncationSet} {R R' : Type*} [CommRing R] [CommRing R']

/-- The Verschiebung on coordinates, before additivity is available. -/
private def verschiebungFun (n : ℕ) (x : BigWittVector (S / n) R) : BigWittVector S R where
  coeff m := if n ∣ m then x.coeff (m / n) else 0
  coeff_eq_zero_of_notMem m hm := by
    split_ifs with h
    · exact x.coeff_eq_zero_of_notMem _ (by rwa [TruncationSet.mem_div, Nat.mul_div_cancel' h])
    · rfl

private theorem coeff_verschiebungFun (n : ℕ) (x : BigWittVector (S / n) R) (m : ℕ) :
    (verschiebungFun n x).coeff m = if n ∣ m then x.coeff (m / n) else 0 :=
  rfl

private theorem verschiebungFun_map (n : ℕ) (f : R →+* R') (x : BigWittVector (S / n) R) :
    verschiebungFun n (map f x) = map f (verschiebungFun n x) := by
  ext m
  simp only [coeff_verschiebungFun, coeff_map]
  split_ifs <;> simp

private theorem ghostPolynomial_verschiebungFun (n : ℕ) (x : BigWittVector (S / n) R) (m : ℕ) :
    ghostPolynomial m (verschiebungFun n x).coeff =
      if n ∣ m then n * ghostPolynomial (m / n) x.coeff else 0 :=
  ghostPolynomial_ite_dvd n m x.coeff

private theorem verschiebungFun_add (n : ℕ) (x y : BigWittVector (S / n) R) :
    verschiebungFun n (x + y) = verschiebungFun n x + verschiebungFun n y := by
  -- lift `x` and `y` to the integral polynomial ring `ℤ[X_r : r ∈ R]`
  obtain ⟨x, rfl⟩ := map_surjective (S := S / n) (counit R) (counit_surjective R) x
  obtain ⟨y, rfl⟩ := map_surjective (S := S / n) (counit R) (counit_surjective R) y
  rw [← map_add, verschiebungFun_map, verschiebungFun_map, verschiebungFun_map, ← map_add]
  congr 1
  -- over `ℤ[X_r : r ∈ R]` the ghost map is injective
  refine ghostMap_injective (fun _ _ hp ↦ .of_ne_zero (Nat.cast_ne_zero.2 hp.ne_zero)) ?_
  rw [map_add]
  funext m
  simp only [Pi.add_apply, ghostMap_apply, ghostPolynomial_verschiebungFun]
  split_ifs with h
  · have hadd := congrFun (map_add ghostMap x y) ⟨m / n, TruncationSet.div_mem_div m.property h⟩
    simp only [Pi.add_apply, ghostMap_apply] at hadd
    rw [hadd, mul_add]
  · rw [add_zero]

/-- The big Witt Verschiebung `V_n : W_{S/n}(R) →+ W_S(R)`, given on coordinates by
`(V_n x)_{n e} = x_e` and `(V_n x)_m = 0` when `n ∤ m`. -/
def verschiebung (n : ℕ) : BigWittVector (S / n) R →+ BigWittVector S R where
  toFun := verschiebungFun n
  map_zero' := ext fun m ↦ by simp [coeff_verschiebungFun]
  map_add' := verschiebungFun_add n

/-- The coordinates of the Verschiebung. -/
theorem coeff_verschiebung (n : ℕ) (x : BigWittVector (S / n) R) (m : ℕ) :
    (verschiebung n x).coeff m = if n ∣ m then x.coeff (m / n) else 0 :=
  (rfl)

/-- The Verschiebung moves the coordinate of index `e` to index `n * e`. -/
@[simp]
theorem coeff_verschiebung_mul (n : ℕ) (x : BigWittVector (S / n) R) (e : ℕ) :
    (verschiebung n x).coeff (n * e) = x.coeff e := by
  rcases eq_or_ne n 0 with rfl | hn
  · rw [zero_mul, coeff_eq_zero_of_notMem _ 0 S.zero_notMem,
      coeff_eq_zero_of_notMem _ e (by simp)]
  · rw [coeff_verschiebung, ite_eq_left (dvd_mul_right n e),
      Nat.mul_div_cancel_left e (Nat.pos_of_ne_zero hn)]

/-- The coordinates of the Verschiebung at indices not divisible by `n` vanish. -/
@[simp]
theorem coeff_verschiebung_of_not_dvd (n : ℕ) (x : BigWittVector (S / n) R) {m : ℕ}
    (h : ¬n ∣ m) : (verschiebung n x).coeff m = 0 := by
  rw [coeff_verschiebung, ite_eq_right h]

/-- The ghost components of the Verschiebung at multiples of `n`:
`w_{n k}(V_n x) = n * w_k(x)`. -/
@[simp]
theorem ghostMap_verschiebung_mul (n : ℕ) (x : BigWittVector (S / n) R) (k : S / n) :
    ghostMap (verschiebung n x) ⟨n * k, TruncationSet.mem_div.mp k.property⟩ =
      n * ghostMap x k := by
  have hn : 0 < n := Nat.pos_of_mul_pos_right (S.pos_of_mem (TruncationSet.mem_div.mp k.property))
  rw [ghostMap_apply, ghostMap_apply]
  refine (ghostPolynomial_verschiebungFun n x _).trans ?_
  rw [ite_eq_left (dvd_mul_right n k), Nat.mul_div_cancel_left _ hn]

/-- The ghost components of the Verschiebung vanish at indices not divisible by `n`. -/
@[simp]
theorem ghostMap_verschiebung_of_not_dvd (n : ℕ) (x : BigWittVector (S / n) R) {m : S}
    (h : ¬n ∣ m) : ghostMap (verschiebung n x) m = 0 := by
  rw [ghostMap_apply]
  exact (ghostPolynomial_verschiebungFun n x m).trans (ite_eq_right h)

/-- The Verschiebung commutes with coefficient homomorphisms. -/
@[simp]
theorem verschiebung_map (n : ℕ) (f : R →+* R') (x : BigWittVector (S / n) R) :
    verschiebung n (map f x) = map f (verschiebung n x) :=
  verschiebungFun_map n f x

/-- The Verschiebung commutes with restriction to smaller truncation sets. -/
theorem restrict_verschiebung (n : ℕ) (h : T ≤ S) (x : BigWittVector (S / n) R) :
    restrict h (verschiebung n x) =
      verschiebung n (restrict (TruncationSet.div_le_div h n) x) := by
  ext m
  by_cases hm : m ∈ T
  · rw [coeff_restrict_of_mem h _ hm, coeff_verschiebung, coeff_verschiebung]
    split_ifs with hd
    · rw [coeff_restrict_of_mem _ _ (TruncationSet.div_mem_div hm hd)]
    · rfl
  · rw [coeff_eq_zero_of_notMem _ m hm, coeff_eq_zero_of_notMem _ m hm]

/-- The Verschiebung at index one is the identity, with its source presented as `S / 1`. -/
@[simp]
theorem verschiebung_one (x : BigWittVector (S / 1) R) :
    verschiebung 1 x = restrict (TruncationSet.div_one S).ge x := by
  ext m
  by_cases hm : m ∈ S
  · rw [coeff_restrict_of_mem _ _ hm, coeff_verschiebung, ite_eq_left (one_dvd m), Nat.div_one]
  · rw [coeff_eq_zero_of_notMem _ m hm, coeff_eq_zero_of_notMem _ m hm]

/-- Successive Verschiebung maps multiply their indices: `V_a V_b = V_{a b}`, with the source of
`V_a V_b` presented as `S / a / b`. -/
theorem verschiebung_verschiebung (a b : ℕ) (x : BigWittVector (S / a / b) R) :
    verschiebung a (verschiebung b x) =
      verschiebung (a * b) (restrict (TruncationSet.div_div S a b).ge x) := by
  ext m
  by_cases hm : m ∈ S
  swap
  · rw [coeff_eq_zero_of_notMem _ m hm, coeff_eq_zero_of_notMem _ m hm]
  rw [coeff_verschiebung, coeff_verschiebung, coeff_verschiebung]
  by_cases ha : a ∣ m
  · rw [ite_eq_left ha, Nat.div_div_eq_div_mul]
    by_cases hab : a * b ∣ m
    · rw [ite_eq_left ((Nat.dvd_div_iff_mul_dvd ha).2 hab), ite_eq_left hab,
        coeff_restrict_of_mem _ _ (TruncationSet.div_mem_div hm hab)]
    · rw [ite_eq_right (mt (Nat.dvd_div_iff_mul_dvd ha).1 hab), ite_eq_right hab]
  · rw [ite_eq_right ha, ite_eq_right fun hab ↦ ha ((dvd_mul_right a b).trans hab)]

/-- The Verschiebung at index zero is zero, because its source truncation set is empty. -/
@[simp]
theorem verschiebung_zero (x : BigWittVector (S / 0) R) : verschiebung 0 x = 0 := by
  ext m
  rw [coeff_verschiebung, coeff_eq_zero_of_notMem _ _ (by simp)]
  simp

/-- Every Verschiebung is injective. -/
theorem verschiebung_injective (n : ℕ) :
    Injective (verschiebung n : BigWittVector (S / n) R → BigWittVector S R) := fun x y h ↦
  ext fun e ↦ by rw [← coeff_verschiebung_mul n x e, ← coeff_verschiebung_mul n y e, h]

end BigWittVector

end TauCeti
