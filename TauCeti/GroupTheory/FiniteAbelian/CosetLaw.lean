/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Analysis.Normed.Ring.Finite
import Mathlib.RingTheory.IntegralDomain

/-!
# Character sums and coset laws

A finite set whose coset counts approximate prescribed shares has character sums close to
its size times the corresponding Fourier coefficients. For a profile with one weight at the
identity and a constant weight off the identity, these coefficients are explicit. In particular,
shares in ratio `4 : 3` give the weight `1 / (3 * |G| + 1)` at every nontrivial character of `G`.

The character-sum comparison is the estimate in Levent Alpöge's formalization,
`UpperTheory.Comparison₂.tops_sum` (`PrimitiveCosets/TopsSum.lean`).
-/

public section

open scoped BigOperators

namespace MonoidHom

/-- The error in the character sum on a finite set is bounded by the sum of the absolute
errors of its fibre counts. No normalization of the prescribed shares is needed. -/
theorem norm_sum_comp_sub_card_mul_sum_le {α Q : Type*} [Group Q] [Fintype Q] [DecidableEq Q]
    (χ : Q →* ℂ) (S : Finset α) (p : α → Q) (ν : Q → ℝ) :
    ‖(∑ a ∈ S, χ (p a)) - (S.card : ℂ) * ∑ q, (ν q : ℂ) * χ q‖ ≤
      ∑ q, |((S.filter fun a ↦ p a = q).card : ℝ) - ν q * S.card| := by
  have hfiber : (∑ a ∈ S, χ (p a)) =
      ∑ q : Q, ((S.filter fun a ↦ p a = q).card : ℂ) * χ q := by
    rw [← S.sum_fiberwise p (fun a ↦ χ (p a))]
    refine Finset.sum_congr rfl fun q _ ↦ ?_
    rw [← nsmul_eq_mul, ← Finset.sum_const]
    exact Finset.sum_congr rfl fun a ha ↦ congrArg χ (Finset.mem_filter.mp ha).2
  rw [hfiber, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun q _ ↦ ?_)
  rw [← mul_assoc, mul_comm (S.card : ℂ) (ν q : ℂ), ← sub_mul, norm_mul,
    (χ.isOfFinOrder (isOfFinOrder_of_finite q)).norm_eq_one, mul_one]
  norm_cast

/-- If the count in each coset of `H` differs from its prescribed share of `S` by at most
`η * |S|`, then each quotient character sum differs from its predicted value by at most
`[G : H] * η * |S|`. A character on `G` trivial on `H` can be descended by `QuotientGroup.lift`.
-/
theorem norm_sum_character_sub_coset_law_le {G : Type*} [Group G] {H : Subgroup G} [H.Normal]
    [Fintype (G ⧸ H)] [DecidableEq (G ⧸ H)]
    (χ : G ⧸ H →* ℂ) (S : Finset G) (ν : G ⧸ H → ℝ) (η : ℝ)
    (hν : ∀ q, |((S.filter fun g ↦ (QuotientGroup.mk' H) g = q).card : ℝ) - ν q * S.card| ≤
      η * S.card) :
    ‖(∑ g ∈ S, χ ((QuotientGroup.mk' H) g)) - (S.card : ℂ) * ∑ q, (ν q : ℂ) * χ q‖ ≤
      Fintype.card (G ⧸ H) * η * S.card := by
  refine (χ.norm_sum_comp_sub_card_mul_sum_le S (QuotientGroup.mk' H) ν).trans ?_
  refine (Finset.sum_le_sum (s := Finset.univ) fun q _ ↦ hν q).trans_eq ?_
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_assoc]

/-- Real shares invariant under inversion give a real character coefficient for the transform
with kernel `χ`, without any assumption of nonnegativity or total mass. -/
theorem im_sum_mul_apply_eq_zero_of_inv {Q : Type*} [Group Q] [Fintype Q]
    (χ : Q →* ℂ) (ν : Q → ℝ) (hν : ∀ q, ν q⁻¹ = ν q) :
    (∑ q, (ν q : ℂ) * χ q).im = 0 := by
  apply Complex.conj_eq_iff_im.mp
  rw [map_sum]
  have hinv (q : Q) : starRingEnd ℂ (χ q) = χ q⁻¹ := by
    rw [map_inv, Complex.inv_eq_conj (χ.isOfFinOrder (isOfFinOrder_of_finite q)).norm_eq_one]
  simpa only [map_mul, Complex.conj_ofReal, hinv, Equiv.inv_apply, hν] using
    Equiv.sum_comp (Equiv.inv Q) (fun q ↦ (ν q : ℂ) * χ q)

open scoped Classical in
/-- For a profile with share proportional to `1` at the identity and to `b` elsewhere,
the normalized coefficient at the trivial character is `1`. At any nontrivial character
it is `(1 - b) / (1 + (|Q| - 1) * b)`. -/
theorem sum_normalized_twoLevel_mul_apply {Q : Type*} [Group Q] [Fintype Q]
    (χ : Q →* ℂ) (b : ℝ) (hb : 1 + ((Fintype.card Q : ℝ) - 1) * b ≠ 0) :
    ∑ q : Q, (((if q = 1 then 1 else b) / (1 + ((Fintype.card Q : ℝ) - 1) * b) : ℝ) : ℂ) *
      χ q = if χ = 1 then 1 else ((1 - b) / (1 + ((Fintype.card Q : ℝ) - 1) * b) : ℝ) := by
  classical
  have hsplit (q : Q) :
      (if q = 1 then 1 else (b : ℂ)) * χ q = b * χ q + if q = 1 then 1 - (b : ℂ) else 0 := by
    split_ifs with h <;> simp [h]
  simp only [Complex.ofReal_div, Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_one,
    Complex.ofReal_mul, Complex.ofReal_natCast, apply_ite Complex.ofReal]
  simp_rw [div_mul_eq_mul_div, hsplit, div_eq_mul_inv]
  -- Apply character orthogonality to the constant part of the profile.
  rw [← Finset.sum_mul, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_ite_eq',
    ite_eq_left (Finset.mem_univ _), sum_hom_units]
  simp only [← div_eq_mul_inv]
  by_cases h : χ = 1
  · simp only [ite_eq_left h]
    rw [div_eq_iff (by exact_mod_cast hb)]
    ring
  · simp [h]

end MonoidHom
