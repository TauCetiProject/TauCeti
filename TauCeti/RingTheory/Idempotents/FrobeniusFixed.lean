/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.ZMod.Basic
public import TauCeti.Algebra.CharP.Frobenius.Fixed
public import TauCeti.Algebra.CharP.ZModCast
public import TauCeti.RingTheory.Idempotents.Combination
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic.LinearCombination

/-!
# The idempotent decomposition of a Frobenius-fixed element

Let `R` be a commutative ring of prime characteristic `p` and let `x : R` satisfy `x ^ p = x`.
Over a connected base such an `x` is one of the `p` scalars `i ∈ 𝔽_p`, but in general `x` is a
locally constant `𝔽_p`-valued function on `Spec R`: there are unique orthogonal idempotents
`(e_i)_{i ∈ 𝔽_p}` summing to one with `x = ∑ i e_i`, and `e_i` cuts out the clopen locus where
`x = i`. They are given by the explicit formula

`e_i = 1 - (x - i) ^ (p - 1)`,

and conversely `∑ i e_i` is fixed by the `p`-power map for every complete family of orthogonal
idempotents indexed by `𝔽_p`. So the Frobenius-fixed subring of `R` is in bijection with such
families. Perfectness of `R` plays no role.

This is the description of the fixed scalars `R^{φ = 1}` of a Frobenius module over a possibly
disconnected base: a fixed scalar is a locally constant function rather than an element of the
diagonal copy of `𝔽_p`. On `𝔽_p × 𝔽_p`, for instance, `x = (0, 1)` has the two nonzero idempotents
`(1, 0)` and `(0, 1)`, and it is not a scalar.

## Main definitions

* `TauCeti.frobeniusFixedIdempotent p x i`: the element `1 - (x - i) ^ (p - 1)`.
* `TauCeti.frobeniusFixedIdempotentEquiv`: the bijection between the elements of `R` fixed by the
  `p`-power map and the complete families of orthogonal idempotents indexed by `ZMod p`.

## Main results

* `TauCeti.completeOrthogonalIdempotents_frobeniusFixedIdempotent`: for `x ^ p = x`, the
  `frobeniusFixedIdempotent p x i` form a complete family of orthogonal idempotents, and
  `TauCeti.sum_zmodCast_mul_frobeniusFixedIdempotent` says that `x = ∑ i, i * e_i`.
* `TauCeti.frobeniusFixedIdempotent_sum_zmodCast_mul`: uniqueness, every complete family of
  orthogonal idempotents `f` is the family attached to `∑ i, i * f i`.
* `TauCeti.sum_zmodCast_mul_pow_char`: conversely, `∑ i, i * f i` is fixed by the `p`-power map.
* `TauCeti.map_frobeniusFixedIdempotent`: ring homomorphisms, such as restriction to a clopen
  piece of `Spec R`, carry the decomposition of `x` to that of its image.
* `TauCeti.pow_char_eq_self_iff_mem_range_zmodCast` and
  `TauCeti.natCard_frobeniusFixedSubring_one`: when `R` has no idempotents besides `0` and `1`,
  the solutions of `x ^ p = x` are exactly the `p` elements of the image of `ZMod p`.

## References

* K. S. Kedlaya and R. Liu, *Relative p-adic Hodge theory: foundations*, Astérisque 371 (2015),
  Lemmas 3.1.3 and 3.1.4.
-/

public section

namespace TauCeti

section Def

variable {R : Type*} [CommRing R] (p : ℕ) (x : R) (i : ZMod p)

/-- The element `1 - (x - i) ^ (p - 1)` attached to `x` and a residue `i ∈ 𝔽_p`. When
`x ^ p = x` in characteristic `p`, these are the unique complete orthogonal idempotents with
`x = ∑ i, i * e_i`, and `e_i` is the indicator of the locus where `x = i`
(`TauCeti.completeOrthogonalIdempotents_frobeniusFixedIdempotent`). -/
def frobeniusFixedIdempotent : R :=
  1 - (x - (i.cast : R)) ^ (p - 1)

theorem frobeniusFixedIdempotent_def :
    frobeniusFixedIdempotent p x i = 1 - (x - (i.cast : R)) ^ (p - 1) :=
  (rfl)

/-- A ring homomorphism carries the idempotents attached to `x` to those attached to its image.
Restriction to a clopen piece of `Spec R` is the case of the projection `R → R ⧸ (1 - e)`. -/
@[simp]
theorem map_frobeniusFixedIdempotent {S F : Type*} [CommRing S] [FunLike F R S]
    [RingHomClass F R S] (f : F) :
    f (frobeniusFixedIdempotent p x i) = frobeniusFixedIdempotent p (f x) i := by
  simp only [frobeniusFixedIdempotent_def, map_sub, map_one, map_pow, map_zmodCast]

end Def

variable {R : Type*} [CommRing R] (p : ℕ) [hp : Fact p.Prime] [CharP R p]

variable {p} {x : R}

/-- For `x ^ p = x`, the element `x` acts on `frobeniusFixedIdempotent p x i` as the scalar `i`. -/
theorem mul_frobeniusFixedIdempotent (hx : x ^ p = x) (i : ZMod p) :
    x * frobeniusFixedIdempotent p x i = (i.cast : R) * frobeniusFixedIdempotent p x i := by
  -- The one real step: `(x - i) * (x - i) ^ (p - 1) = (x - i) ^ p = x - i`.
  have h : (x - (i.cast : R)) * (x - (i.cast : R)) ^ (p - 1) = x - (i.cast : R) := by
    rw [← pow_succ', Nat.sub_add_cancel hp.out.one_le, sub_zmodCast_pow_char hx]
  rw [frobeniusFixedIdempotent_def]
  linear_combination -h

/-- For `x ^ p = x`, each `frobeniusFixedIdempotent p x i` is idempotent. -/
theorem isIdempotentElem_frobeniusFixedIdempotent (hx : x ^ p = x) (i : ZMod p) :
    IsIdempotentElem (frobeniusFixedIdempotent p x i) := by
  -- With `y = x - i` and `y ^ p = y`: `y ^ (2p - 2) = y ^ p * y ^ (p - 2) = y ^ (p - 1)`.
  have := hp.out.two_le
  refine IsIdempotentElem.one_sub ?_
  rw [IsIdempotentElem, ← pow_add, show p - 1 + (p - 1) = p + (p - 2) by omega, pow_add,
    sub_zmodCast_pow_char hx, ← pow_succ', show p - 2 + 1 = p - 1 by omega]

/-- For `x ^ p = x`, the `frobeniusFixedIdempotent p x i` form a complete family of orthogonal
idempotents indexed by `ZMod p`. -/
theorem completeOrthogonalIdempotents_frobeniusFixedIdempotent (hx : x ^ p = x) :
    CompleteOrthogonalIdempotents (frobeniusFixedIdempotent p x) := by
  refine .of_prod_one_sub ⟨isIdempotentElem_frobeniusFixedIdempotent hx, fun i j hij ↦ ?_⟩ ?_
  · -- `x` acts on the product by both `i` and `j`, and `i - j` is a unit.
    have hunit : IsUnit ((i.cast : R) - (j.cast : R)) := by
      rw [← ZMod.cast_sub']
      exact (isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr hij)).map (ZMod.castHom dvd_rfl R)
    refine (hunit.mul_right_eq_zero).mp ?_
    linear_combination frobeniusFixedIdempotent p x i * mul_frobeniusFixedIdempotent hx j -
      frobeniusFixedIdempotent p x j * mul_frobeniusFixedIdempotent hx i
  · simp_rw [frobeniusFixedIdempotent_def, sub_sub_cancel]
    rw [Finset.prod_pow, prod_sub_zmodCast, hx, sub_self,
      zero_pow (Nat.sub_ne_zero_of_lt hp.out.one_lt)]

/-- For `x ^ p = x`, the element `x` is the combination `∑ i, i * e_i` of its idempotents. -/
theorem sum_zmodCast_mul_frobeniusFixedIdempotent (hx : x ^ p = x) :
    ∑ i : ZMod p, (i.cast : R) * frobeniusFixedIdempotent p x i = x := by
  simp_rw [← mul_frobeniusFixedIdempotent hx, ← Finset.mul_sum,
    (completeOrthogonalIdempotents_frobeniusFixedIdempotent hx).complete, mul_one]

/-- Uniqueness of the decomposition: a complete family of orthogonal idempotents `f` indexed by
`ZMod p` is the family of idempotents attached to `∑ i, i * f i`. -/
theorem frobeniusFixedIdempotent_sum_zmodCast_mul {f : ZMod p → R}
    (hf : CompleteOrthogonalIdempotents f) :
    frobeniusFixedIdempotent p (∑ i : ZMod p, (i.cast : R) * f i) = f := by
  funext i
  rw [frobeniusFixedIdempotent_def, ← hf.sum_sub_mul, hf.sum_mul_pow]
  simp_rw [← ZMod.cast_sub', ← ZMod.cast_pow']
  rw [← hf.complete, ← Finset.sum_sub_distrib, Finset.sum_eq_single i
    (fun j _ hji ↦ by simp [ZMod.pow_card_sub_one_eq_one (sub_ne_zero.mpr hji)]) (by simp)]
  simp [zero_pow (Nat.sub_ne_zero_of_lt hp.out.one_lt)]

/-- Every combination `∑ i, i * f i` of a complete family of orthogonal idempotents indexed by
`ZMod p` is fixed by the `p`-power map. -/
theorem sum_zmodCast_mul_pow_char {f : ZMod p → R} (hf : CompleteOrthogonalIdempotents f) :
    (∑ i : ZMod p, (i.cast : R) * f i) ^ p = ∑ i : ZMod p, (i.cast : R) * f i := by
  simp_rw [hf.sum_mul_pow, zmodCast_pow_char]

variable (R p) in
/-- The elements of `R` fixed by the `p`-power map correspond to the complete families of
orthogonal idempotents indexed by `ZMod p`: a fixed element `x` goes to its idempotents
`frobeniusFixedIdempotent p x`, and a family `f` goes to `∑ i, i * f i`. -/
def frobeniusFixedIdempotentEquiv :
    frobeniusFixedSubring R p 1 ≃ {f : ZMod p → R // CompleteOrthogonalIdempotents f} where
  toFun x := ⟨frobeniusFixedIdempotent p (x : R),
    completeOrthogonalIdempotents_frobeniusFixedIdempotent
      (mem_frobeniusFixedSubring_one.mp x.property)⟩
  invFun f := ⟨∑ i : ZMod p, (i.cast : R) * f.val i,
    mem_frobeniusFixedSubring_one.mpr (sum_zmodCast_mul_pow_char f.property)⟩
  left_inv x := Subtype.ext <| sum_zmodCast_mul_frobeniusFixedIdempotent
    (mem_frobeniusFixedSubring_one.mp x.property)
  right_inv f := Subtype.ext <| frobeniusFixedIdempotent_sum_zmodCast_mul f.property

@[simp]
theorem coe_frobeniusFixedIdempotentEquiv_apply (x : frobeniusFixedSubring R p 1) :
    (frobeniusFixedIdempotentEquiv R p x : ZMod p → R) = frobeniusFixedIdempotent p (x : R) :=
  (rfl)

@[simp]
theorem coe_frobeniusFixedIdempotentEquiv_symm_apply
    (f : {f : ZMod p → R // CompleteOrthogonalIdempotents f}) :
    ((frobeniusFixedIdempotentEquiv R p).symm f : R) = ∑ i : ZMod p, (i.cast : R) * f.val i :=
  (rfl)

/-- If `R` has no idempotents other than `0` and `1`, for instance if `Spec R` is connected, the
solutions of `x ^ p = x` are exactly the images of the residues `i ∈ ZMod p`. -/
theorem pow_char_eq_self_iff_mem_range_zmodCast
    (hR : ∀ e : R, IsIdempotentElem e → e = 0 ∨ e = 1) :
    x ^ p = x ↔ x ∈ Set.range (ZMod.cast : ZMod p → R) := by
  refine ⟨fun hx ↦ ?_, ?_⟩
  · have := CharP.nontrivial_of_char_ne_one (R := R) hp.out.ne_one
    have he := completeOrthogonalIdempotents_frobeniusFixedIdempotent hx
    -- Some `e_i` is nonzero, since they sum to `1 ≠ 0`; it is then `1`, and `x` acts on it by `i`.
    obtain ⟨i, hi⟩ : ∃ i, frobeniusFixedIdempotent p x i ≠ 0 := by
      by_contra! h
      have : (1 : R) = 0 := by rw [← he.complete, Finset.sum_eq_zero fun i _ ↦ h i]
      exact one_ne_zero this
    have h1 := (hR _ (he.idem i)).resolve_left hi
    exact ⟨i, by simpa [h1] using (mul_frobeniusFixedIdempotent hx i).symm⟩
  · rintro ⟨i, rfl⟩
    exact zmodCast_pow_char i

/-- If `R` has no idempotents other than `0` and `1`, exactly `p` elements of `R` are fixed by the
`p`-power map. -/
theorem natCard_frobeniusFixedSubring_one (hR : ∀ e : R, IsIdempotentElem e → e = 0 ∨ e = 1) :
    Nat.card (frobeniusFixedSubring R p 1) = p := by
  have hset : (frobeniusFixedSubring R p 1 : Set R) = Set.range (ZMod.cast : ZMod p → R) := by
    ext x
    rw [SetLike.mem_coe, mem_frobeniusFixedSubring_one, pow_char_eq_self_iff_mem_range_zmodCast hR]
  have hinj : Function.Injective (ZMod.cast : ZMod p → R) :=
    fun a b hab ↦ ZMod.castHom_injective R (by simpa using hab)
  rw [← SetLike.coe_sort_coe, hset, Nat.card_range_of_injective hinj, Nat.card_zmod]

end TauCeti
