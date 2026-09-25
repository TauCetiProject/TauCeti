/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Data.Nat.Choose
public import TauCeti.FieldTheory.SquareClassGroup.Basic
public import TauCeti.LinearAlgebra.QuadraticForm.Diagonal.Basic
public import TauCeti.LinearAlgebra.QuadraticForm.Hyperbolic
public import TauCeti.LinearAlgebra.QuadraticForm.RegularFormClass.TensorProduct

/-!
# The discriminant and the signed discriminant of a regular quadratic form

Over a field in which two is invertible, a regular quadratic form is diagonalizable, and the
product of the weights of a diagonalization is well defined modulo squares. That square class is
the **discriminant** `d(q)`; correcting it by the sign `(-1)^{m(m-1)/2}` in rank `m` gives the
**signed discriminant** `d±(q)`, the variant that vanishes on a hyperbolic plane and is unchanged
by adding one.

Both invariants are defined on `TauCeti.RegularFormClass`, the carrier of isometry classes of
regular forms, so they are invariants of a form up to isometry by construction. Well-definedness
is a Gram-determinant computation: the Gram matrix of a diagonal presentation in the standard
basis is the diagonal matrix of its weights, and an isometry of the coordinate spaces changes that
matrix by a congruence, hence changes its determinant — the product of the weights — by the square
of a unit.

The sign is recorded as `m.choose 2` rather than as the truncated quotient `m * (m - 1) / 2`; the
two agree by `Nat.choose_two_right`, and only the parity matters, because the square-class group
is killed by two.

## Main definitions

* `TauCeti.RegularFormClass.discr` and `TauCeti.RegularFormClass.discrHom`: the discriminant of an
  isometry class, and its packaging as an additive homomorphism for the orthogonal sum.
* `TauCeti.RegularFormClass.signedDiscr`: the signed discriminant.

## Main results

* `TauCeti.squareClass_prod_eq_of_equivalent`: isometric diagonal presentations have weight
  products in the same square class.
* `TauCeti.equivalent_presentedForm_hyperbolicPlane_of_squareClass_prod_eq_neg_one`: a binary
  presentation whose weight product has square class `[-1]` presents a hyperbolic plane.
* `TauCeti.RegularFormClass.discr_add` and `TauCeti.RegularFormClass.discr_mul`: the discriminant
  of an orthogonal sum is the sum of the discriminants, and the discriminant of a tensor product
  of classes of ranks `m` and `n` is `d(q)^n d(r)^m`.
* `TauCeti.RegularFormClass.signedDiscr_add` and `TauCeti.RegularFormClass.signedDiscr_mul`: the
  signed discriminant of an orthogonal sum picks up the sign `(-1)^{mn}`, and that of a tensor
  product is `(-1)^{mn(mn-1)/2} d(q)^n d(r)^m`.
* `TauCeti.RegularFormClass.discr_mk_rankOne_mul` and
  `TauCeti.RegularFormClass.signedDiscr_mk_rankOne_mul`: scaling by `a` adds
  `m • squareClass a` to the (signed) discriminant of a class of rank `m`.
* `TauCeti.RegularFormClass.eq_one_of_rank_eq_one_of_discr_eq_zero`: a rank-one class of trivial
  discriminant is `⟨1⟩`.
* `TauCeti.RegularFormClass.mk_rankOne_mul_self`: scaling twice by the same unit is the identity,
  `⟨a⟩ ⊗ ⟨a⟩ ≅ ⟨1⟩`.
* `TauCeti.RegularFormClass.exists_eq_mk_neg_neg_mul`: a rank-three class with trivial
  discriminant has a presentation `⟨-a, -b, ab⟩`.
* `TauCeti.RegularFormClass.signedDiscr_mk_rankOne`: `d±⟨a⟩ = squareClass a`.
* `TauCeti.RegularFormClass.discr_hyperbolicClass` and
  `TauCeti.RegularFormClass.signedDiscr_hyperbolicClass`: the discriminant of a hyperbolic plane
  is the class of `-1`, and its signed discriminant is trivial.
* `TauCeti.RegularFormClass.signedDiscr_add_hyperbolicClass`: adding a hyperbolic plane leaves the
  signed discriminant unchanged.
* `TauCeti.RegularFormClass.eq_hyperbolicClass_of_rank_eq_two_of_discr_eq_neg_one`: a binary
  class of discriminant `[-1]` is the hyperbolic class.

## References

* T. Y. Lam, *Introduction to Quadratic Forms over Fields* (2005), Chapter II, §2.
* O. T. O'Meara, *Introduction to Quadratic Forms* (1973), §58.
-/

public section

open QuadraticMap QuadraticForm

namespace TauCeti

universe u v

variable {K : Type u} [Field K] [Invertible (2 : K)]

/-! ### The discriminant of a diagonal presentation -/

/-- Isometric diagonal presentations have weight products in the same square class, which is what
makes the discriminant an invariant of an isometry class. -/
theorem squareClass_prod_eq_of_equivalent {p q : RegularFormPresentation K}
    (h : (presentedForm p).Equivalent (presentedForm q)) :
    squareClass (∏ i, p.2 i) = squareClass (∏ i, q.2 i) := by
  obtain ⟨n, w⟩ := p
  obtain ⟨m, v⟩ := q
  obtain rfl : n = m := fst_eq_of_presentedForm_equivalent h
  rw [presentedForm_eq_weightedSumSquares, presentedForm_eq_weightedSumSquares] at h
  exact (squareClass_eq_iff_isSquare_mul _ _).mpr (isSquare_prod_mul_prod_of_equivalent h)

/-- A binary regular-form presentation whose weight product has square class `[-1]` presents a
hyperbolic plane. -/
theorem equivalent_presentedForm_hyperbolicPlane_of_squareClass_prod_eq_neg_one
    (w : Fin 2 → Kˣ) (h : squareClass (w 0 * w 1) = squareClass (-1 : Kˣ)) :
    (presentedForm ⟨2, w⟩).Equivalent (hyperbolicPlane K) := by
  have hdisc : IsSquare (w 0 * w 1 * ((1 : Kˣ) * (-1))) := by
    rw [← squareClass_eq_iff_isSquare_mul]
    simpa only [one_mul] using h
  rw [presentedForm_eq_weightedSumSquares_coe]
  have hweights : (fun i ↦ (w i : K)) = ![(w 0 : K), (w 1 : K)] := by
    ext i
    fin_cases i <;> rfl
  rw [hweights]
  exact equivalent_weightedSumSquares_hyperbolicPlane_of_isSquare hdisc

namespace RegularFormClass

/-! ### The discriminant -/

/-- **The discriminant of an isometry class of regular quadratic forms**: the product of the
weights of any diagonalization of the form, taken modulo squares. -/
def discr : RegularFormClass K → SquareClassGroup K :=
  Quotient.lift (fun p => squareClass (∏ i, p.2 i)) fun _ _ h =>
    squareClass_prod_eq_of_equivalent h

/-- The discriminant of the class of a presentation is the square class of its weight product. -/
@[simp]
theorem discr_mk (p : RegularFormPresentation K) :
    discr (Quotient.mk (regularFormSetoid K) p) = squareClass (∏ i, p.2 i) :=
  (rfl)

/-- The rank-zero class has trivial discriminant, its weight product being empty. -/
@[simp]
theorem discr_zero : discr (0 : RegularFormClass K) = 0 := by
  rw [RegularFormClass.zero_def, discr_mk]
  simp

/-- **The discriminant of an orthogonal sum is the sum of the discriminants**:
`d(q ⊥ r) = d(q) + d(r)` in the additively written square-class group. -/
@[simp]
theorem discr_add (x y : RegularFormClass K) : discr (x + y) = discr x + discr y := by
  refine Quotient.inductionOn₂ x y fun p q => ?_
  rw [RegularFormClass.mk_add_mk, discr_mk, discr_mk, discr_mk, ← squareClass_mul,
    RegularFormPresentation.prod_append]

/-- The discriminant as an additive homomorphism for the orthogonal sum. -/
def discrHom : RegularFormClass K →+ SquareClassGroup K where
  toFun := discr
  map_zero' := discr_zero
  map_add' := discr_add

@[simp]
theorem discrHom_apply (x : RegularFormClass K) : discrHom x = discr x :=
  (rfl)

/-- The multiplicative unit `⟨1⟩` has trivial discriminant. -/
@[simp]
theorem discr_one : discr (1 : RegularFormClass K) = 0 := by
  rw [RegularFormClass.one_def, discr_mk]
  simp

/-- **The discriminant of a tensor product**: `d(q ⊗ r) = n • d(q) + m • d(r)` for `q` of
rank `m` and `r` of rank `n`, in the additively written square-class group. -/
@[simp]
theorem discr_mul (x y : RegularFormClass K) :
    discr (x * y) = rank y • discr x + rank x • discr y := by
  refine Quotient.inductionOn₂ x y fun p q => ?_
  rw [RegularFormClass.mk_mul_mk, discr_mk, discr_mk, discr_mk, rank_mk, rank_mk,
    ← squareClass_pow, ← squareClass_pow, ← squareClass_mul,
    RegularFormPresentation.prod_tmul]

/-- **Scaling by a unit**: `d(⟨a⟩ ⊗ q) = m • squareClass a + d(q)` for `q` of rank `m`,
where scaling by `a` is multiplication by the rank-one class `⟨a⟩`. -/
theorem discr_mk_rankOne_mul (a : Kˣ) (x : RegularFormClass K) :
    discr (Quotient.mk (regularFormSetoid K) ⟨1, fun _ => a⟩ * x) =
      rank x • squareClass a + discr x := by
  rw [discr_mul, rank_mk, one_nsmul, discr_mk, Fin.prod_univ_one]

/-- A class of rank one and trivial discriminant is the class `⟨1⟩`: in rank one the discriminant
is a complete invariant. -/
theorem eq_one_of_rank_eq_one_of_discr_eq_zero {x : RegularFormClass K}
    (hr : x.rank = 1) (hd : discr x = 0) : x = 1 := by
  induction x using Quotient.inductionOn with
  | h p =>
    obtain ⟨n, w⟩ := p
    rw [rank_mk] at hr
    subst hr
    rw [discr_mk, Fin.prod_univ_one, squareClass_eq_zero_iff] at hd
    obtain ⟨t, ht⟩ := hd
    dsimp only at ht
    rw [← mk_rankOne_one, mk_eq_mk_iff, presentedForm_eq_weightedSumSquares_coe,
      presentedForm_eq_weightedSumSquares_coe]
    refine ⟨QuadraticForm.isometryEquivWeightedSumSquaresWeightedSumSquares (fun _ => t) ?_⟩
    intro i
    fin_cases i
    simp [ht, pow_two]

/-- **Scaling by a unit is an involution up to isometry**: `⟨a⟩ ⊗ ⟨a⟩ ≅ ⟨a²⟩ ≅ ⟨1⟩`. -/
@[simp 1100]
theorem mk_rankOne_mul_self (a : Kˣ) :
    Quotient.mk (regularFormSetoid K) ⟨1, fun _ => a⟩ *
      Quotient.mk (regularFormSetoid K) ⟨1, fun _ => a⟩ = 1 := by
  refine eq_one_of_rank_eq_one_of_discr_eq_zero (by simp) ?_
  rw [discr_mk_rankOne_mul, rank_mk, discr_mk, Fin.prod_univ_one, one_nsmul, ← two_nsmul,
    ZModModule.char_nsmul_eq_zero 2]

/-- **A ternary form of trivial discriminant is a pure quaternion norm form**: a class of rank
three and trivial discriminant is the class of `⟨-a, -b, ab⟩` for some units `a` and `b`. -/
theorem exists_eq_mk_neg_neg_mul {x : RegularFormClass K} (hr : x.rank = 3) (hd : discr x = 0) :
    ∃ a b : Kˣ, x = Quotient.mk (regularFormSetoid K) ⟨3, ![-a, -b, a * b]⟩ := by
  induction x using Quotient.inductionOn with
  | h p =>
    obtain ⟨n, w⟩ := p
    rw [rank_mk] at hr
    subst hr
    rw [discr_mk, squareClass_eq_zero_iff, Fin.prod_univ_three] at hd
    obtain ⟨t, ht⟩ := hd
    refine ⟨-w 0, -w 1, ?_⟩
    rw [mk_eq_mk_iff, presentedForm_eq_weightedSumSquares_coe,
      presentedForm_eq_weightedSumSquares_coe]
    refine ⟨QuadraticForm.isometryEquivWeightedSumSquaresWeightedSumSquares
      ![1, 1, t * (w 0 * w 1)⁻¹] ?_⟩
    intro i
    fin_cases i
    · simp
    · simp
    · have ht' : (w 0 : K) * w 1 * w 2 = t * t := by simpa using congrArg Units.val ht
      simp only [Fin.isValue, neg_neg, mul_neg, neg_mul, Fin.reduceFinMk, Matrix.cons_val,
        Units.val_mul, mul_inv_rev, Units.val_inv_eq_inv_val]
      field_simp
      linear_combination -ht'

/-! ### The signed discriminant -/

/-- **The signed discriminant** `d±(q) = m.choose 2 • squareClass (-1) + d(q)` of a class of
rank `m`, in the additively written square-class group. The exponent is recorded as `m.choose 2`,
which equals `m * (m - 1) / 2` by `Nat.choose_two_right`. -/
def signedDiscr (x : RegularFormClass K) : SquareClassGroup K :=
  (rank x).choose 2 • squareClass (-1 : Kˣ) + discr x

/-- The signed discriminant is the discriminant corrected by the sign of its rank. This is the
only conversion between the two invariants that later arguments need. -/
theorem signedDiscr_eq_sign_add_discr (x : RegularFormClass K) :
    signedDiscr x = (rank x).choose 2 • squareClass (-1 : Kˣ) + discr x :=
  (rfl)

/-- The signed discriminant of the class of a presentation. -/
@[simp]
theorem signedDiscr_mk (p : RegularFormPresentation K) :
    signedDiscr (Quotient.mk (regularFormSetoid K) p) =
      p.1.choose 2 • squareClass (-1 : Kˣ) + squareClass (∏ i, p.2 i) := by
  rw [signedDiscr_eq_sign_add_discr, rank_mk, discr_mk]

/-- In rank at most one the signed discriminant is the discriminant. -/
theorem signedDiscr_eq_discr_of_rank_le_one {x : RegularFormClass K} (hx : rank x ≤ 1) :
    signedDiscr x = discr x := by
  rw [signedDiscr_eq_sign_add_discr, Nat.choose_eq_zero_of_lt (by omega), zero_nsmul]
  abel

/-- The rank-zero class has trivial signed discriminant. -/
@[simp]
theorem signedDiscr_zero : signedDiscr (0 : RegularFormClass K) = 0 := by
  rw [signedDiscr_eq_discr_of_rank_le_one (by rw [rank_zero]; omega), discr_zero]

/-- The multiplicative unit `⟨1⟩` has trivial signed discriminant: in rank one the signed
discriminant agrees with the discriminant. -/
@[simp]
theorem signedDiscr_one : signedDiscr (1 : RegularFormClass K) = 0 := by
  rw [signedDiscr_eq_discr_of_rank_le_one rank_one.le, discr_one]

/-- **The signed discriminant of a rank-one class** `⟨a⟩` is the class of `a`. -/
theorem signedDiscr_mk_rankOne (a : Kˣ) :
    signedDiscr (Quotient.mk (regularFormSetoid K) ⟨1, fun _ => a⟩) = squareClass a := by
  rw [signedDiscr_eq_discr_of_rank_le_one (by rw [rank_mk]), discr_mk, Fin.prod_univ_one]

/-- **The signed discriminant of an orthogonal sum**:
`d±(q ⊥ r) = mn • squareClass (-1) + d±(q) + d±(r)` for `q` of rank `m` and `r` of rank
`n`, in the additively written square-class group. The cross term is what the unsigned
discriminant misses. -/
@[simp]
theorem signedDiscr_add (x y : RegularFormClass K) :
    signedDiscr (x + y) =
      (rank x * rank y) • squareClass (-1 : Kˣ) + signedDiscr x + signedDiscr y := by
  rw [signedDiscr_eq_sign_add_discr, signedDiscr_eq_sign_add_discr,
    signedDiscr_eq_sign_add_discr, discr_add, rank_add, Nat.add_choose_two, add_nsmul, add_nsmul]
  abel

/-- **The signed discriminant of a tensor product**:
`d±(q ⊗ r) = (mn).choose 2 • squareClass (-1) + n • d(q) + m • d(r)` for `q` of rank `m`
and `r` of rank `n`, in the additively written square-class group. -/
@[simp]
theorem signedDiscr_mul (x y : RegularFormClass K) :
    signedDiscr (x * y) =
      (rank x * rank y).choose 2 • squareClass (-1 : Kˣ) +
        (rank y • discr x + rank x • discr y) := by
  rw [signedDiscr_eq_sign_add_discr, discr_mul, rank_mul]

/-- **Scaling by a unit**: `d±(⟨a⟩ ⊗ q) = m • squareClass a + d±(q)` for `q` of rank
`m`, where scaling by `a` is multiplication by the rank-one class `⟨a⟩`. -/
theorem signedDiscr_mk_rankOne_mul (a : Kˣ) (x : RegularFormClass K) :
    signedDiscr (Quotient.mk (regularFormSetoid K) ⟨1, fun _ => a⟩ * x) =
      rank x • squareClass a + signedDiscr x := by
  rw [signedDiscr_mul, rank_mk, one_mul, one_nsmul, discr_mk, Fin.prod_univ_one,
    signedDiscr_eq_sign_add_discr]
  abel

end RegularFormClass

/-! ### Regular forms and the standard examples -/

/-- The discriminant of a regular form is computed by any of its diagonalizations. -/
theorem discr_formClass {V : Type v} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (Q : QuadraticForm K V) (hQ : Q.Nondegenerate) (p : RegularFormPresentation K)
    (hp : Q.Equivalent (presentedForm p)) :
    RegularFormClass.discr (formClass Q hQ) = squareClass (∏ i, p.2 i) := by
  rw [formClass_mk Q hQ p hp, RegularFormClass.discr_mk]

/-- The signed discriminant of a regular form is computed by any of its diagonalizations. -/
theorem signedDiscr_formClass {V : Type v} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (Q : QuadraticForm K V) (hQ : Q.Nondegenerate)
    (p : RegularFormPresentation K) (hp : Q.Equivalent (presentedForm p)) :
    RegularFormClass.signedDiscr (formClass Q hQ) =
      p.1.choose 2 • squareClass (-1 : Kˣ) + squareClass (∏ i, p.2 i) := by
  rw [formClass_mk Q hQ p hp, RegularFormClass.signedDiscr_mk]

/-- The discriminant of the hyperbolic class is the class of `-1`. -/
@[simp]
theorem RegularFormClass.discr_hyperbolicClass :
    RegularFormClass.discr (hyperbolicClass K) = squareClass (-1 : Kˣ) := by
  rw [← formClass_hyperbolicPlane,
    discr_formClass _ _ (⟨2, ![1, -1]⟩ : RegularFormPresentation K)
      (by rw [presentedForm_one_neg_one]; exact QuadraticMap.Equivalent.refl _)]
  simp [Fin.prod_univ_two]

/-- A class of rank two whose discriminant is the class of `-1` is the hyperbolic class: in rank
two the discriminant is a complete invariant of hyperbolicity. -/
theorem RegularFormClass.eq_hyperbolicClass_of_rank_eq_two_of_discr_eq_neg_one
    {x : RegularFormClass K}
    (hrank : RegularFormClass.rank x = 2)
    (hdiscr : RegularFormClass.discr x = squareClass (-1 : Kˣ)) : x = hyperbolicClass K := by
  induction x using Quotient.inductionOn with
  | h p =>
    obtain ⟨n, w⟩ := p
    rw [RegularFormClass.rank_mk] at hrank
    subst hrank
    rw [RegularFormClass.discr_mk, Fin.prod_univ_two] at hdiscr
    rw [hyperbolicClass_def, RegularFormClass.mk_eq_mk_iff]
    refine (equivalent_presentedForm_hyperbolicPlane_of_squareClass_prod_eq_neg_one w hdiscr).trans
      (equivalent_presentedForm_hyperbolicPlane_of_squareClass_prod_eq_neg_one
        ![1, -1] (by simp)).symm

/-- **The signed discriminant of the hyperbolic class is trivial.** The unsigned discriminant is
the class of `-1`, which is nontrivial precisely when `-1` is not a square. -/
@[simp]
theorem RegularFormClass.signedDiscr_hyperbolicClass :
    RegularFormClass.signedDiscr (hyperbolicClass K) = 0 := by
  rw [RegularFormClass.signedDiscr_eq_sign_add_discr, RegularFormClass.discr_hyperbolicClass,
    rank_hyperbolicClass, Nat.choose_self, one_nsmul, ← squareClass_mul]
  simp

/-- **Adding a hyperbolic plane leaves the signed discriminant unchanged.** The cross term of
`TauCeti.RegularFormClass.signedDiscr_add` is an even multiple of the class of `-1`, so it
vanishes. The unsigned discriminant instead picks up the class of `-1` each time. -/
theorem RegularFormClass.signedDiscr_add_hyperbolicClass (x : RegularFormClass K) :
    RegularFormClass.signedDiscr (x + hyperbolicClass K) = RegularFormClass.signedDiscr x := by
  rw [RegularFormClass.signedDiscr_add, RegularFormClass.signedDiscr_hyperbolicClass,
    rank_hyperbolicClass]
  have hcross : (RegularFormClass.rank x * 2) • squareClass (-1 : Kˣ) = 0 := by
    calc
      _ = 2 • (RegularFormClass.rank x • squareClass (-1 : Kˣ)) :=
        mul_nsmul _ _ _
      _ = 0 := ZModModule.char_nsmul_eq_zero 2
        (RegularFormClass.rank x • squareClass (-1 : Kˣ) : SquareClassGroup K)
  rw [hcross]
  abel

end TauCeti
