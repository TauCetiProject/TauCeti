/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Polynomial.Laurent.Basic
public import TauCeti.KnotTheory.PDCode.Circle
public import TauCeti.KnotTheory.PDCode.Oriented.ClaspInsertion
public import TauCeti.KnotTheory.PDCode.Oriented.Reidemeister.Circle
public import TauCeti.KnotTheory.PDCode.Oriented.Reidemeister.Two.Basic
public import TauCeti.KnotTheory.PDCode.Oriented.Reidemeister.Two.Circles
public import TauCeti.KnotTheory.PDCode.Oriented.Reidemeister.One
public import TauCeti.KnotTheory.PDCode.Oriented.Reidemeister.Three
public import TauCeti.KnotTheory.PDCode.Trefoil

/-!
# The Jones polynomial of an oriented PD-code

Lickorish defines the Jones polynomial of an oriented link diagram `D` from its Kauffman bracket:
`V(D)` is the writhe-normalized bracket `(-A)^(-3 w(D)) ⟨D⟩` rewritten in `t^(1/2) = A⁻²`. It is a
Laurent polynomial in `t^(1/2)` with integer coefficients. This file defines it for oriented
PD-codes, as `TauCeti.OrientedPDCode.jonesPolynomial`, with the generator `T` of `ℤ[T;T⁻¹]`
standing for `t^(1/2)`.

The substitution is possible because every power of `A` in the normalized bracket is even. Crossing
by crossing, a positive crossing contributes `A * (-A⁻³) = -t^(1/2)` to a state that smooths it by
`A` and `A⁻¹ * (-A⁻³) = -t` to one that smooths it by `A⁻¹`. A negative crossing contributes `-t⁻¹`
and `-t^(-1/2)` instead. The loop value `-(A² + A⁻²)` becomes `-(t^(1/2) + t^(-1/2))`. So the Jones
polynomial is the state sum `TauCeti.OrientedPDCode.jonesPolynomial` with these weights, and
evaluating it at `t^(1/2) = A⁻²` recovers the normalized bracket over every commutative ring
(`TauCeti.OrientedPDCode.eval₂_jonesPolynomial`). The substitution `T ↦ T⁻²` is injective on
`ℤ[T;T⁻¹]`, so two codes have the same Jones polynomial exactly when they have the same normalized
bracket (`TauCeti.OrientedPDCode.jonesPolynomial_eq_jonesPolynomial_iff`). Every invariance property
of the normalized bracket is therefore one of the Jones polynomial.

In particular the Jones polynomial is unchanged by the first Reidemeister move, by clasp
insertion, which along a common face is the second Reidemeister move, by the second-move clasps
involving crossing-free circles, and by the third Reidemeister move. These are the local moves
behind its invariance for oriented links (Lickorish, Theorem 3.5).
Reversing the orientation of every component leaves the Jones polynomial unchanged, and
mirroring substitutes `t⁻¹` for `t`. The unknot has Jones polynomial `1`, and the right-handed
trefoil has `t + t³ - t⁴`.

## Main definitions

* `TauCeti.OrientedPDCode.jonesStateWeight`: the weight of a state in the Jones state sum.
* `TauCeti.OrientedPDCode.jonesPolynomial`: the Jones polynomial of an oriented PD-code.

## Main results

* `TauCeti.OrientedPDCode.eval₂_jonesPolynomial`: at `t^(1/2) = A⁻²` the Jones polynomial is
  the writhe-normalized Kauffman bracket.
* `TauCeti.OrientedPDCode.jonesPolynomial_eq_jonesPolynomial_iff`: two codes have the same Jones
  polynomial exactly when they have the same normalized bracket.
* `TauCeti.OrientedPDCode.jonesPolynomial_reidemeisterOne`,
  `TauCeti.OrientedPDCode.jonesPolynomial_insertClasp` and
  `TauCeti.OrientedPDCode.jonesPolynomial_reidemeisterThree`: invariance under the first
  Reidemeister move, under clasp insertion and under the third Reidemeister move.
* `TauCeti.OrientedPDCode.jonesPolynomial_mirror`, `TauCeti.OrientedPDCode.jonesPolynomial_reverse`
  and `TauCeti.OrientedPDCode.jonesPolynomial_relabel`: behaviour under reflection, reversal and
  relabelling.
* `TauCeti.OrientedPDCode.jonesPolynomial_eq_pow`: a code with no crossings and `c` circles has
  Jones polynomial `(-(t^(1/2) + t^(-1/2))) ^ (c - 1)`, and
  `TauCeti.OrientedPDCode.jonesPolynomial_unknot`: the unknot has Jones polynomial `1`.
* `TauCeti.jonesPolynomial_rightHandedTrefoilPDCode`: the right-handed trefoil has Jones polynomial
  `t + t³ - t⁴`.

## References

* W. B. R. Lickorish, *An Introduction to Knot Theory*, Springer GTM 175 (1997), Chapter 3,
  Theorem 3.5 and Definition 3.6.
* V. F. R. Jones, *A polynomial invariant for knots via von Neumann algebras*, Bull. Amer. Math.
  Soc. 12 (1985), 103-111.
-/

public section

namespace TauCeti

open LaurentPolynomial TemperleyLieb

namespace OrientedPDCode

variable {n : ℕ}

/-- The weight of a state `s` in the Jones state sum, a signed power of `t^(1/2) = T`: each
positive crossing contributes `-t^(1/2)` when `s` smooths it by `A` and `-t` when by `A⁻¹`, and
each negative crossing contributes `-t⁻¹` and `-t^(-1/2)` respectively. These are the factors
`A^(±1) * (-A³)^(-ε)` of the writhe-normalized bracket at a crossing of sign `ε`, rewritten in
`t^(1/2) = A⁻²`. -/
noncomputable def jonesStateWeight (D : OrientedPDCode n) (s : Fin n → Bool) : ℤ[T;T⁻¹] :=
  ∏ i, -T (if D.crossingSign i = 1 then bif s i then 1 else 2 else bif s i then -2 else -1)

/-- The defining product of the Jones weight of a state. -/
theorem jonesStateWeight_def (D : OrientedPDCode n) (s : Fin n → Bool) :
    D.jonesStateWeight s =
      ∏ i, -T (if D.crossingSign i = 1 then bif s i then 1 else 2 else bif s i then -2 else -1) :=
  (rfl)

/-- **The Jones polynomial** of an oriented PD-code, as a Laurent polynomial in `t^(1/2) = T`
with integer coefficients: the sum over all states of the Jones weight of the state times the loop
value `-(t^(1/2) + t^(-1/2))` raised to one less than the number of circles of the smoothed
diagram. It is Lickorish's `V(D)`, the writhe-normalized Kauffman bracket at `t^(1/2) = A⁻²`
(`TauCeti.OrientedPDCode.eval₂_jonesPolynomial`). As for the bracket, the exponent is truncated
subtraction, so the empty code has Jones polynomial `1`. -/
noncomputable def jonesPolynomial (D : OrientedPDCode n) : ℤ[T;T⁻¹] :=
  ∑ s : Fin n → Bool, D.jonesStateWeight s * (-(T 1 + T (-1))) ^ (D.stateLoopCount s - 1)

/-- The defining state-sum equation of the Jones polynomial. -/
theorem jonesPolynomial_def (D : OrientedPDCode n) :
    D.jonesPolynomial =
      ∑ s : Fin n → Bool, D.jonesStateWeight s * (-(T 1 + T (-1))) ^ (D.stateLoopCount s - 1) :=
  (rfl)

section Evaluation

variable {R : Type*} [CommRing R]

/-- At `t^(1/2) = A⁻²`, the Jones loop value is the Kauffman loop value. -/
private theorem eval₂_jonesLoop (a : Rˣ) :
    eval₂ (Int.castRingHom R) (a⁻¹ ^ 2) (-(T 1 + T (-1)) : ℤ[T;T⁻¹]) = jonesDelta a := by
  simp [jonesDelta_def, add_comm]

/-- At `t^(1/2) = A⁻²`, the Jones weight of a crossing of sign `ε` smoothed by `c` is its factor
`A^(±1) * (-A³)^(-ε)` in the normalized bracket. -/
private theorem neg_zpow_jonesExponent (a : Rˣ) {ε : ℤ} (hε : ε = 1 ∨ ε = -1) (c : Bool) :
    -(a⁻¹ ^ 2) ^ (if ε = 1 then bif c then 1 else 2 else bif c then -2 else -1 : ℤ) =
      (-a ^ 3) ^ (-ε) * bif c then a else a⁻¹ := by
  rcases hε with rfl | rfl <;> cases c <;> simp [zpow_neg, neg_mul] <;> group

/-- At `t^(1/2) = A⁻²`, the Jones weight of a state is its Kauffman weight times the writhe
correction. -/
private theorem eval₂_jonesStateWeight (D : OrientedPDCode n) (a : Rˣ)
    (s : Fin n → Bool) :
    eval₂ (Int.castRingHom R) (a⁻¹ ^ 2) (D.jonesStateWeight s) =
      (((-a ^ 3) ^ (-D.writhe) : Rˣ) : R) * (PDCode.stateWeight s a : R) := by
  -- the writhe correction is the product of the corrections `(-a ^ 3) ^ (-ε)` at the crossings
  have hwrithe : (-a ^ 3) ^ (-D.writhe) = ∏ i, (-a ^ 3) ^ (-D.crossingSign i) := by
    simpa [writhe_def, ← ofAdd_sum] using map_prod (zpowersHom Rˣ (-a ^ 3))
      (fun i ↦ Multiplicative.ofAdd (-D.crossingSign i)) Finset.univ
  rw [jonesStateWeight_def, map_prod, ← Units.val_mul, hwrithe, PDCode.stateWeight_def,
    ← Finset.prod_mul_distrib, Units.coe_prod]
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  rw [← neg_zpow_jonesExponent a (D.crossingSign_eq_one_or_neg_one i), map_neg, eval₂_T,
    Units.val_neg]

/-- **The Jones polynomial is the normalized Kauffman bracket at `t^(1/2) = A⁻²`.** Evaluating
`TauCeti.OrientedPDCode.jonesPolynomial` at the square of `a⁻¹` gives the writhe-normalized bracket
at `a`, over every commutative ring. This is Lickorish's definition of the Jones polynomial. -/
theorem eval₂_jonesPolynomial (D : OrientedPDCode n) (a : Rˣ) :
    eval₂ (Int.castRingHom R) (a⁻¹ ^ 2) D.jonesPolynomial = D.normalizedKauffmanBracket a := by
  rw [jonesPolynomial_def, normalizedKauffmanBracket_def, PDCode.kauffmanBracket_def,
    map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  rw [map_mul, map_pow, eval₂_jonesStateWeight, eval₂_jonesLoop, mul_assoc]

end Evaluation

section Injectivity

/-- **The Jones polynomial carries exactly the information of the normalized bracket**: two
oriented PD-codes have the same Jones polynomial exactly when they have the same writhe-normalized
Kauffman bracket over `ℤ[A, A⁻¹]`. Every invariance statement for the normalized bracket is
therefore one for the Jones polynomial. -/
theorem jonesPolynomial_eq_jonesPolynomial_iff {m : ℕ} (D : OrientedPDCode n)
    (D' : OrientedPDCode m) :
    D.jonesPolynomial = D'.jonesPolynomial ↔
      D.normalizedKauffmanBracket (isUnit_T (R := ℤ) 1).unit =
        D'.normalizedKauffmanBracket (isUnit_T (R := ℤ) 1).unit := by
  refine ⟨fun h ↦ ?_, fun h ↦ eval₂_C_inv_pow_injective two_ne_zero ?_⟩
  · rw [← eval₂_jonesPolynomial, ← eval₂_jonesPolynomial, h]
  · rw [← Subsingleton.elim (Int.castRingHom ℤ[T;T⁻¹]) C, eval₂_jonesPolynomial,
      eval₂_jonesPolynomial, h]

/-- **The first Reidemeister move leaves the Jones polynomial unchanged.** -/
@[simp]
theorem jonesPolynomial_reidemeisterOne (D : OrientedPDCode n) (h : Fin (4 * n)) (b : Bool) :
    (D.reidemeisterOne h b).jonesPolynomial = D.jonesPolynomial :=
  (jonesPolynomial_eq_jonesPolynomial_iff _ _).2 <|
    normalizedKauffmanBracket_reidemeisterOne (R := ℤ[T;T⁻¹]) D h b _

/-- The Jones polynomial is invariant under the first Reidemeister move on an isolated
circle, including a circle in an otherwise empty diagram. -/
@[simp] theorem jonesPolynomial_adjoinKink (D : OrientedPDCode n) (o b : Bool) :
    (D.adjoinKink o b).jonesPolynomial = (D.adjoinCircle o).jonesPolynomial :=
  (jonesPolynomial_eq_jonesPolynomial_iff _ _).2 (normalizedKauffmanBracket_adjoinKink D o b _)

/-- **Clasp insertion leaves the Jones polynomial unchanged.** Along a common face of the two arcs
this is the second Reidemeister move. -/
@[simp]
theorem jonesPolynomial_insertClasp (D : OrientedPDCode n) (p q : Fin (4 * n)) (b : Bool)
    (hqp : q ≠ p) (hqe : q ≠ D.edgePair.val p) :
    (D.insertClasp p q b hqp hqe).jonesPolynomial = D.jonesPolynomial :=
  (jonesPolynomial_eq_jonesPolynomial_iff _ _).2 <|
    normalizedKauffmanBracket_insertClasp (R := ℤ[T;T⁻¹]) D p q b hqp hqe _

/-- The Jones polynomial is invariant under the circle-and-arc second Reidemeister move. -/
@[simp] theorem jonesPolynomial_insertCircleClasp (D : OrientedPDCode n)
    (p : Fin (4 * n)) (o b : Bool) :
    (D.insertCircleClasp p o b).jonesPolynomial = (D.adjoinCircle o).jonesPolynomial :=
  (jonesPolynomial_eq_jonesPolynomial_iff _ _).2
    (D.normalizedKauffmanBracket_insertCircleClasp p o b _)

/-- The Jones polynomial is unchanged by the two-circle second Reidemeister move. -/
@[simp] theorem jonesPolynomial_adjoinTwoCircleClasp (D : OrientedPDCode n)
    (o₁ o₂ b : Bool) :
    (D.adjoinTwoCircleClasp o₁ o₂ b).jonesPolynomial =
      ((D.adjoinCircle o₁).adjoinCircle o₂).jonesPolynomial :=
  (jonesPolynomial_eq_jonesPolynomial_iff _ _).2
    (D.normalizedKauffmanBracket_adjoinTwoCircleClasp o₁ o₂ b _)

/-- **The third Reidemeister move leaves the Jones polynomial unchanged**, for every surrounding
diagram and all six height orders of the three strands. -/
@[simp]
theorem jonesPolynomial_reidemeisterThree (D : OrientedPDCode n) (c : Fin 3 ↪ Fin n)
    (h : D.HasReidemeisterThreeTriangle c) :
    (D.reidemeisterThree c).jonesPolynomial = D.jonesPolynomial :=
  (jonesPolynomial_eq_jonesPolynomial_iff _ _).2 <|
    normalizedKauffmanBracket_reidemeisterThree (R := ℤ[T;T⁻¹]) D c h _

/-- Adjoining a crossing-free circle to a nonempty oriented diagram multiplies its Jones polynomial
by the loop value `-(t^(1/2) + t^(-1/2))`. -/
@[simp]
theorem jonesPolynomial_adjoinCircle (D : OrientedPDCode n) (orientation : Bool)
    (h : 0 < D.toPDCode.componentCount) :
    (OrientedPDCode.adjoinCircle D orientation).jonesPolynomial =
      -(T 1 + T (-1)) * D.jonesPolynomial := by
  refine eval₂_C_inv_pow_injective two_ne_zero ?_
  rw [← Subsingleton.elim (Int.castRingHom ℤ[T;T⁻¹]) C, map_mul, eval₂_jonesPolynomial,
    eval₂_jonesPolynomial, eval₂_jonesLoop, normalizedKauffmanBracket_adjoinCircle D orientation h]

end Injectivity

/-- **Reflection substitutes `t⁻¹` for `t`** in the Jones polynomial. -/
@[simp]
theorem jonesPolynomial_mirror (D : OrientedPDCode n) :
    D.mirror.jonesPolynomial = invert D.jonesPolynomial := by
  rw [jonesPolynomial_def, jonesPolynomial_def, map_sum]
  refine Fintype.sum_bijective (fun s i ↦ !(s i))
    (Function.Involutive.bijective fun s ↦ by funext i; simp) _ _ fun s ↦ ?_
  simp only [mirror_toPDCode, PDCode.stateLoopCount_mirror, map_mul, map_pow, map_neg, map_add,
    invert_T, neg_neg, jonesStateWeight_def, map_prod, crossingSign_mirror, add_comm (T (-1))]
  congr 1
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  rcases D.crossingSign_eq_one_or_neg_one i with h | h <;> cases s i <;> simp [h]

/-- Reversing the orientation of every component leaves the Jones polynomial unchanged. -/
@[simp]
theorem jonesPolynomial_reverse (D : OrientedPDCode n) :
    D.reverse.jonesPolynomial = D.jonesPolynomial := by
  simp [jonesPolynomial_def, jonesStateWeight_def]

/-- The Jones polynomial depends on an oriented PD-code only through its relabelling class. -/
@[simp]
theorem jonesPolynomial_relabel {m : ℕ} (D : OrientedPDCode n)
    (half : Fin (4 * n) ≃ Fin (4 * m)) (cross : Fin n ≃ Fin m) :
    (D.relabel half cross).jonesPolynomial = D.jonesPolynomial := by
  let e := Equiv.piCongrLeft (fun _ : Fin n ↦ Bool) cross.symm
  have he : (fun s : Fin m → Bool ↦ s ∘ cross) = e := by
    funext s i
    simp [e, Equiv.piCongrLeft_apply]
  refine Fintype.sum_bijective (fun s ↦ s ∘ cross) (he ▸ e.bijective) _ _ fun s ↦ ?_
  rw [relabel_toPDCode, PDCode.stateLoopCount_relabel, jonesStateWeight_def,
    jonesStateWeight_def, ← Equiv.prod_comp cross]
  simp

/-- A code with no crossings and `c` crossing-free circles has Jones polynomial
`(-(t^(1/2) + t^(-1/2))) ^ (c - 1)`, the counterpart of
`TauCeti.PDCode.kauffmanBracket_eq_jonesDelta_pow`. -/
theorem jonesPolynomial_eq_pow (D : OrientedPDCode 0) :
    D.jonesPolynomial = (-(T 1 + T (-1))) ^ (D.crossinglessComponentCount - 1) := by
  rw [jonesPolynomial_def, Fintype.sum_unique]
  simp [jonesStateWeight_def]

/-- **The unknot has Jones polynomial `1`.** -/
@[simp]
theorem jonesPolynomial_unknot (orientation : Bool) : (unknot orientation).jonesPolynomial = 1 := by
  rw [jonesPolynomial_eq_pow, ← crossinglessComponents_card, crossinglessComponents_unknot]
  simp

/-- An isolated kink in an otherwise empty diagram has Jones polynomial one, for either
orientation and either crossing sign. -/
-- Evaluate this special case before the general `jonesPolynomial_adjoinKink` rewrite.
@[simp 1100] theorem jonesPolynomial_adjoinKink_empty (o b : Bool) :
    (empty.adjoinKink o b).jonesPolynomial = 1 := by
  rw [jonesPolynomial_adjoinKink, jonesPolynomial_eq_pow]
  simp [← crossinglessComponents_card]

end OrientedPDCode

/-- **The Jones polynomial of the right-handed trefoil** is `t + t³ - t⁴`, written in
`t^(1/2) = T`. This pins the convention: Lickorish's `V(D)` with `t^(1/2) = A⁻²`. -/
@[simp]
theorem jonesPolynomial_rightHandedTrefoilPDCode :
    rightHandedTrefoilPDCode.jonesPolynomial = T 2 + T 6 - T 8 := by
  refine eval₂_C_inv_pow_injective two_ne_zero ?_
  rw [← Subsingleton.elim (Int.castRingHom ℤ[T;T⁻¹]) C, OrientedPDCode.eval₂_jonesPolynomial,
    normalizedKauffmanBracket_rightHandedTrefoilPDCode]
  simp only [map_add, map_sub, eval₂_T, zpow_ofNat, ← pow_mul, Units.val_pow_eq_pow_val]

end TauCeti
