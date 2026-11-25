/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Divisor.Index
public import TauCeti.FieldTheory.FunctionField.Elliptic.Basic
public import TauCeti.FieldTheory.FunctionField.Gonality.Basic
-- Proof-only: genus, exact constants and degree-one divisors of the pointless conic.
import TauCeti.FieldTheory.FunctionField.Consequences.Conic
-- Proof-only: a divisor of degree one makes the constant field exact.
import TauCeti.FieldTheory.FunctionField.Divisor.ConstantField

/-!
# Gonality in genus zero and one

The *index* of an algebraic function field `F / k`, the least positive degree of a divisor
(`TauCeti.index`), divides the gonality, since the gonality is the degree of a divisor. In genus
zero and one, over an exact constant field (`IsIntegrallyClosedIn k F`), this divisibility, with
Riemann–Roch, determines the gonality.

* In genus zero, over an exact constant field, a canonical divisor has degree `-2`, so the index
  divides two. Index one means a divisor of degree one, hence a rational field and gonality one;
  otherwise the anticanonical divisor, of degree two and `ℓ = 3`, gives gonality two. So the
  gonality is the index.
* In genus one, over an exact constant field, every divisor `D` of positive degree has
  `ℓ(D) = deg D`. A pencil therefore exists exactly in the degrees at least two that are multiples
  of the index, and the gonality is `max 2 (index k F)`. An elliptic function field (genus one,
  index one) has gonality two, while a genus-one field of index three, such as Selmer's cubic
  `3x³ + 4y³ + 5z³ = 0` over `ℚ`, has gonality three.

The function field of the conic `x² + y² + 1 = 0` over a field without a solution to
`a² + b² + 1 = 0`, such as `ℝ`, has index two and gonality two.

## Main results

* `TauCeti.index_dvd_gonality`, `TauCeti.index_dvd_two_mul_genus_sub_two`: the index divides the
  gonality and, over an exact constant field, the canonical degree.
* `TauCeti.gonality_of_genus_eq_zero`: in genus zero, over an exact constant field, the gonality
  is the index.
* `TauCeti.gonality_of_genus_eq_one`: in genus one, over an exact constant field, the gonality is
  `max 2 (index k F)`; `TauCeti.IsEllipticFunctionField.gonality_eq_two`: an elliptic function
  field has gonality two.
* `TauCeti.index_eq_two_of_sq_add_sq_add_one_eq_zero`,
  `TauCeti.gonality_eq_two_of_sq_add_sq_add_one_eq_zero`: the pointless conic has index two and
  gonality two.

## References

* B. Poonen, *Gonality of modular curves in characteristic `p`*, Math. Res. Lett. 14 (2007),
  Appendix A.
* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Remark 1.6.4 and Theorem 1.5.17.
-/

public section

open scoped IntermediateField

namespace TauCeti

open AlgebraicGeometry

variable {k F : Type*} [Field k] [Field F] [Algebra k F]

/-- **The index divides the gonality**: the gonality is the degree of a divisor. No exactness of
the constant field is needed. -/
theorem index_dvd_gonality (hF : IsFunctionField k F) : index k F ∣ gonality k F := by
  obtain ⟨D, -, hD, -⟩ := exists_nonneg_and_degree_eq_gonality_and_two_le_dim hF
  have := index_dvd_degree hF D
  rw [hD] at this
  exact_mod_cast this

/-- The index of a function field is at most its gonality. -/
theorem index_le_gonality (hF : IsFunctionField k F) : index k F ≤ gonality k F :=
  Nat.le_of_dvd (gonality_pos hF) (index_dvd_gonality hF)

/-- The rational function field `k(t)` has index one. -/
@[simp]
theorem index_ratFunc : index k (RatFunc k) = 1 :=
  Nat.dvd_one.mp (gonality_ratFunc (k := k) ▸ index_dvd_gonality (IsFunctionField.ratFunc k))

/-- **The index divides the canonical degree `2g - 2`**, over an exact constant field. -/
theorem index_dvd_two_mul_genus_sub_two (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) : (index k F : ℤ) ∣ 2 * genus k F - 2 := by
  obtain ⟨W, hW⟩ := exists_isRiemannRochDivisor hF hex
  exact hW.degree_eq hF hex ▸ index_dvd_degree hF W

/-- **A genus-zero function field has index one or two**: the index divides the canonical degree
`-2`. -/
theorem index_dvd_two_of_genus_eq_zero (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) (hg : genus k F = 0) : index k F ∣ 2 := by
  have := index_dvd_two_mul_genus_sub_two hF hex
  rw [hg, Nat.cast_zero, mul_zero, zero_sub, Int.dvd_neg] at this
  exact_mod_cast this

/-- **In genus zero the gonality is the index**, over an exact constant field: it is one when a
divisor of degree one exists, the field then being rational, and two otherwise, the
anticanonical divisor having degree two and `ℓ = 3`. -/
theorem gonality_of_genus_eq_zero (hF : IsFunctionField k F) (hex : IsIntegrallyClosedIn k F)
    (hg : genus k F = 0) : gonality k F = index k F := by
  obtain ⟨B, -, hB, hBdim⟩ := exists_degree_eq_two_and_three_le_dim_of_genus_eq_zero hF hex hg
  have hle : gonality k F ≤ 2 := by
    have := gonality_le_degree hF hex (D := B) (by omega)
    omega
  have hdvd := index_dvd_gonality hF
  have hidx := Nat.le_of_dvd two_pos (index_dvd_two_of_genus_eq_zero hF hex hg)
  have := index_pos hF
  have := gonality_pos hF
  by_cases h1 : index k F = 1
  · obtain ⟨e⟩ := nonempty_algEquiv_ratFunc_of_genus_eq_zero_of_divisor_degree_eq_one hF hg
      (index_eq_one_iff.mp h1)
    rw [h1, gonality_eq_one_iff]
    exact ⟨e⟩
  · interval_cases gonality k F
    · exact absurd (Nat.dvd_one.mp hdvd) h1
    · omega

/-- **In genus one the gonality is `max 2 (index k F)`**, over an exact constant field: every
divisor of positive degree has `ℓ(D) = deg D`, so a pencil exists exactly in the degrees at least
two that the index divides. -/
theorem gonality_of_genus_eq_one (hF : IsFunctionField k F) (hex : IsIntegrallyClosedIn k F)
    (hg : genus k F = 1) : gonality k F = max 2 (index k F) := by
  refine le_antisymm ?_
    (max_le (two_le_gonality_of_genus_ne_zero hF (by omega)) (index_le_gonality hF))
  obtain ⟨D, hD⟩ := exists_degree_eq_index hF
  have hpos := index_pos hF
  by_cases h1 : index k F = 1
  · have hdeg : Divisor.degree ((2 : ℤ) • D) = 2 := by
      rw [Divisor.degree_zsmul, hD, h1]
      norm_num
    have hdim := Divisor.dim_eq_degree_of_genus_eq_one hF hex hg (D := (2 : ℤ) • D) (by omega)
    have := gonality_le_degree hF hex (D := (2 : ℤ) • D) (by omega)
    omega
  · have hdim := Divisor.dim_eq_degree_of_genus_eq_one hF hex hg (D := D) (by omega)
    have := gonality_le_degree hF hex (D := D) (by omega)
    omega

/-- **An elliptic function field has gonality two**: it has genus one and a divisor of degree
one, hence index one, and the divisor of degree one makes the constant field exact. -/
theorem IsEllipticFunctionField.gonality_eq_two (hF : IsFunctionField k F)
    (he : IsEllipticFunctionField k F) : gonality k F = 2 := by
  rw [gonality_of_genus_eq_one hF
    (isIntegrallyClosedIn_of_exists_divisor_degree_eq_one he.exists_divisor_degree_eq_one)
    he.genus_eq_one, index_eq_one_iff.mpr he.exists_divisor_degree_eq_one]
  rfl

/-! ### The pointless conic -/

section Conic

variable [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]

/-- **The pointless conic has index two**: if `a² + b² + 1 = 0` has no solution in `k`, the
function field of `x² + y² + 1 = 0` has genus zero, so its index divides two, and it has no
divisor of degree one. -/
theorem index_eq_two_of_sq_add_sq_add_one_eq_zero (hk : ∀ a b : k, a ^ 2 + b ^ 2 + 1 ≠ 0)
    {y : F} (hgen : (RatFunc k)⟮y⟯ = ⊤)
    (hy : algebraMap (RatFunc k) F RatFunc.X ^ 2 + y ^ 2 + 1 = 0) : index k F = 2 := by
  have h2 : (2 : k) ≠ 0 := fun h ↦ hk 1 0 (by linear_combination h)
  have hdvd := index_dvd_two_of_genus_eq_zero
    (isFunctionField_of_sq_add_sq_add_one_eq_zero hgen hy)
    (isIntegrallyClosedIn_of_sq_add_sq_add_one_eq_zero h2 hgen hy)
    (genus_eq_zero_of_sq_add_sq_add_one_eq_zero h2 hgen hy)
  have h1 : index k F ≠ 1 := fun h ↦
    not_exists_divisor_degree_eq_one_of_sq_add_sq_add_one_eq_zero hk hgen hy
      (index_eq_one_iff.mp h)
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
  · exact absurd h h1
  · exact h

/-- **The pointless conic has gonality two**: if `a² + b² + 1 = 0` has no solution in `k`, as
over `ℝ`, the function field of `x² + y² + 1 = 0` has gonality two, since in genus zero the
gonality is the index. -/
theorem gonality_eq_two_of_sq_add_sq_add_one_eq_zero (hk : ∀ a b : k, a ^ 2 + b ^ 2 + 1 ≠ 0)
    {y : F} (hgen : (RatFunc k)⟮y⟯ = ⊤)
    (hy : algebraMap (RatFunc k) F RatFunc.X ^ 2 + y ^ 2 + 1 = 0) : gonality k F = 2 := by
  have h2 : (2 : k) ≠ 0 := fun h ↦ hk 1 0 (by linear_combination h)
  rw [gonality_of_genus_eq_zero (isFunctionField_of_sq_add_sq_add_one_eq_zero hgen hy)
    (isIntegrallyClosedIn_of_sq_add_sq_add_one_eq_zero h2 hgen hy)
    (genus_eq_zero_of_sq_add_sq_add_one_eq_zero h2 hgen hy),
    index_eq_two_of_sq_add_sq_add_one_eq_zero hk hgen hy]

end Conic

end TauCeti
