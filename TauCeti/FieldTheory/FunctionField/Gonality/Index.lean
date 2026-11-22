/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Elliptic.Basic
public import TauCeti.FieldTheory.FunctionField.Gonality.Basic
-- Proof-only: genus, exact constants and degree-one divisors of the pointless conic.
import TauCeti.FieldTheory.FunctionField.Consequences.Conic
-- Proof-only: a divisor of degree one makes the constant field exact.
import TauCeti.FieldTheory.FunctionField.Divisor.ConstantField

/-!
# The index of a function field, and gonality in genus zero and one

The *index* of an algebraic function field `F / k` is the least positive degree of a divisor.
The degrees of divisors form a subgroup of `ℤ`, and for a function field this subgroup is
nonzero (every place has positive degree), so the index is its positive generator: a degree
occurs exactly when the index divides it. A rational place, or an algebraically closed constant
field, gives index one; in genus at least two, index one need not produce a rational place.

Since the gonality is the degree of a divisor, the index divides it. In genus zero and one this
divisibility, with Riemann–Roch, determines the gonality.

* In genus zero a canonical divisor has degree `-2`, so the index divides two. Index one means a
  divisor of degree one, hence a rational field and gonality one; otherwise the anticanonical
  divisor, of degree two and `ℓ = 3`, gives gonality two. So the gonality is the index.
* In genus one every divisor `D` of positive degree has `ℓ(D) = deg D`. A pencil therefore exists
  exactly in the degrees at least two that are multiples of the index, and the gonality is
  `max 2 (index k F)`. An elliptic function field (genus one, index one) has gonality two, while a
  genus-one field of index three, such as Selmer's cubic `3x³ + 4y³ + 5z³ = 0` over `ℚ`, has
  gonality three.

The function field of the conic `x² + y² + 1 = 0` over a field without a solution to
`a² + b² + 1 = 0`, such as `ℝ`, has index two and gonality two.

## Main definitions

* `TauCeti.index`: the least positive degree of a divisor of `F / k`.

## Main results

* `TauCeti.Divisor.range_degree`: the degrees of divisors are the multiples of the index.
* `TauCeti.index_dvd_iff_exists_degree_eq`, `TauCeti.index_dvd_degree`: an integer is the degree
  of a divisor exactly when the index divides it.
* `TauCeti.index_eq_one_iff`: index one means a divisor of degree one;
  `TauCeti.Place.index_eq_one_of_degree_eq_one` and `TauCeti.index_eq_one_of_isAlgClosed` are the
  two standard sources.
* `TauCeti.index_dvd_gonality`, `TauCeti.index_dvd_two_mul_genus_sub_two`: the index divides the
  gonality and the canonical degree.
* `TauCeti.gonality_of_genus_eq_zero`: in genus zero the gonality is the index.
* `TauCeti.gonality_of_genus_eq_one`: in genus one the gonality is `max 2 (index k F)`;
  `TauCeti.IsEllipticFunctionField.gonality_eq_two`: an elliptic function field has gonality two.
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

/-- The **index** of `F / k`: the least positive degree of a divisor.

For an algebraic function field the degrees of divisors are exactly the multiples of the index
(`TauCeti.Divisor.range_degree`), so the index is the positive generator of the image of the
degree map. It is one when a rational place exists. Outside the function-field setting the set
of positive degrees can be empty, and the index is then the junk value zero. -/
noncomputable def index (k F : Type*) [Field k] [Field F] [Algebra k F] : ℕ :=
  sInf {n : ℕ | 0 < n ∧ ∃ D : Divisor k F, Divisor.degree D = n}

/-- **The index is at most every positive divisor degree.** -/
theorem index_le_of_degree_eq {D : Divisor k F} {n : ℕ} (hn : 0 < n)
    (hD : Divisor.degree D = n) : index k F ≤ n :=
  Nat.sInf_le ⟨hn, D, hD⟩

/-- A divisor of positive degree makes the index positive and attained. -/
private theorem index_mem_of_degree_pos {D : Divisor k F} (hD : 0 < Divisor.degree D) :
    0 < index k F ∧ ∃ D : Divisor k F, Divisor.degree D = index k F :=
  Nat.sInf_mem (s := {n : ℕ | 0 < n ∧ ∃ D : Divisor k F, Divisor.degree D = n})
    ⟨(Divisor.degree D).toNat, by omega, D, by omega⟩

/-- A function field has a divisor of positive degree: the divisor of any place. -/
private theorem exists_degree_pos (hF : IsFunctionField k F) :
    ∃ D : Divisor k F, 0 < Divisor.degree D := by
  obtain ⟨P⟩ := Place.nonempty hF
  refine ⟨WeilDivisor.ofPoint P, ?_⟩
  have := P.one_le_degree_of_isFunctionField hF
  rw [Divisor.degree_ofPoint]
  omega

/-- **The index of a function field is positive.** -/
theorem index_pos (hF : IsFunctionField k F) : 0 < index k F :=
  (index_mem_of_degree_pos (exists_degree_pos hF).choose_spec).1

/-- **The index of a function field is attained** by the degree of some divisor. -/
theorem exists_degree_eq_index (hF : IsFunctionField k F) :
    ∃ D : Divisor k F, Divisor.degree D = index k F :=
  (index_mem_of_degree_pos (exists_degree_pos hF).choose_spec).2

/-- **The index divides the degree of every divisor**: the remainder of `deg D` modulo the index
is the degree of a divisor, so by minimality of the index it is zero. -/
theorem index_dvd_degree (hF : IsFunctionField k F) (D : Divisor k F) :
    (index k F : ℤ) ∣ Divisor.degree D := by
  obtain ⟨D₀, hD₀⟩ := exists_degree_eq_index hF
  have hpos := index_pos hF
  have hr : Divisor.degree (D - (Divisor.degree D / index k F) • D₀) =
      Divisor.degree D % index k F := by
    rw [Divisor.degree_sub, Divisor.degree_zsmul, hD₀, Int.emod_def]
    ring
  have h0 : 0 ≤ Divisor.degree D % index k F := Int.emod_nonneg _ (by omega)
  have hlt : Divisor.degree D % index k F < index k F := Int.emod_lt_of_pos _ (by omega)
  refine Int.dvd_of_emod_eq_zero (by_contra fun hne ↦ ?_)
  have := index_le_of_degree_eq (n := (Divisor.degree D % index k F).toNat) (by omega)
    (by rw [hr]; omega)
  omega

/-- **The degrees of divisors are the multiples of the index**: an integer is the degree of a
divisor of a function field exactly when the index divides it. -/
theorem index_dvd_iff_exists_degree_eq (hF : IsFunctionField k F) {d : ℤ} :
    (index k F : ℤ) ∣ d ↔ ∃ D : Divisor k F, Divisor.degree D = d := by
  refine ⟨fun ⟨m, hm⟩ ↦ ?_, fun ⟨D, hD⟩ ↦ hD ▸ index_dvd_degree hF D⟩
  obtain ⟨D₀, hD₀⟩ := exists_degree_eq_index hF
  exact ⟨m • D₀, by rw [Divisor.degree_zsmul, hD₀, hm, mul_comm]⟩

/-- **The index generates the degrees**: the image of the degree map on divisors of a function
field is the subgroup of multiples of the index. -/
theorem Divisor.range_degree (hF : IsFunctionField k F) :
    (Divisor.degree (k := k) (F := F)).range = AddSubgroup.zmultiples (index k F : ℤ) := by
  ext d
  rw [AddMonoidHom.mem_range, Int.mem_zmultiples_iff, index_dvd_iff_exists_degree_eq hF]

/-- The index of a function field divides the degree of every place. -/
theorem Place.index_dvd_degree (hF : IsFunctionField k F) (P : Place k F) :
    index k F ∣ P.degree := by
  have := TauCeti.index_dvd_degree hF (WeilDivisor.ofPoint P)
  rw [Divisor.degree_ofPoint] at this
  exact_mod_cast this

/-- **Index one means a divisor of degree one.** No hypothesis on `F` is needed: index one makes
the defining set nonempty, and a divisor of degree one bounds the index by one. -/
theorem index_eq_one_iff : index k F = 1 ↔ ∃ D : Divisor k F, Divisor.degree D = 1 := by
  refine ⟨fun h ↦ ?_, fun ⟨D, hD⟩ ↦ ?_⟩
  · have hne : {n : ℕ | 0 < n ∧ ∃ D : Divisor k F, Divisor.degree D = n}.Nonempty :=
      Nat.nonempty_of_pos_sInf (h ▸ Nat.one_pos : 0 < index k F)
    obtain ⟨-, D, hD⟩ : index k F ∈ _ := Nat.sInf_mem hne
    exact ⟨D, by rw [hD, h, Nat.cast_one]⟩
  · have := (index_mem_of_degree_pos (D := D) (by omega)).1
    have := index_le_of_degree_eq Nat.one_pos (by rw [hD, Nat.cast_one])
    omega

/-- **A rational place gives index one.** The converse fails in genus at least two. -/
theorem Place.index_eq_one_of_degree_eq_one {P : Place k F} (hP : P.degree = 1) :
    index k F = 1 :=
  index_eq_one_iff.mpr ⟨WeilDivisor.ofPoint P, by rw [Divisor.degree_ofPoint, hP, Nat.cast_one]⟩

/-- **Over an algebraically closed constant field the index is one**, since every place is
rational. -/
theorem index_eq_one_of_isAlgClosed [IsAlgClosed k] (hF : IsFunctionField k F) :
    index k F = 1 := by
  obtain ⟨P⟩ := Place.nonempty hF
  exact Place.index_eq_one_of_degree_eq_one
    (P.degree_eq_one_of_isAlgClosed_of_isFunctionField hF)

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
