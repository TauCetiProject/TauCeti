/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Bigraded.Stabilization

/-!
# The conjugation symmetry of bigraded Poincaré series

Knot Floer homology and grid homology satisfy the conjugation symmetry
`HFK_m(K, a) ≅ HFK_(m - 2a)(K, -a)`: the bidegree `(Maslov, Alexander)` is acted on by the
involution `(m, a) ↦ (m - 2a, -a)` of `ℤ × ℤ`. This file records that involution as an additive
automorphism and its action on bigraded Poincaré series `TauCeti.Bigraded.Series`, so that the
symmetry can be stated as an equality of series.

The involution is additive, so its action on series is an algebra automorphism: it is compatible
with tensor products. It sends the stabilization factor `W`, with generators in bidegrees `(0, 0)`
and `(-1, -1)`, to `W` shifted by `(1, 1)`, and it turns the Alexander-graded Euler characteristic
`t ↦ χ(t)` into `t ↦ χ(t⁻¹)`, because `m - 2a` and `m` have the same parity.

## Main definitions

* `TauCeti.Bigraded.conjugationEquiv`: the involution `(m, a) ↦ (m - 2a, -a)` of bidegrees.
* `TauCeti.Bigraded.conjugate`: its action on bigraded Poincaré series.

## Main results

* `TauCeti.Bigraded.coeff_conjugate`: the coefficient of the conjugate series in bidegree
  `(m, a)` is the coefficient of the original series in bidegree `(m - 2a, -a)`.
* `TauCeti.Bigraded.conjugate_W`: conjugating `W` shifts it by `(1, 1)`.
* `TauCeti.Bigraded.euler_conjugate`: conjugation inverts the Alexander variable of the Euler
  characteristic.

## References

* P. Ozsváth, Z. Szabó, *Holomorphic disks and knot invariants*, Adv. Math. 186 (2004),
  Proposition 3.10, for the conjugation symmetry of knot Floer homology.
* P. Ozsváth, A. Stipsicz, Z. Szabó, *Grid Homology for Knots and Links*, AMS Mathematical Surveys
  and Monographs 208, 2015, Section 7.1, for its grid form.
-/

public section

namespace TauCeti

namespace Bigraded

open AddMonoidAlgebra LaurentPolynomial

/-- The conjugation symmetry of bidegrees `(Maslov, Alexander)`: `(m, a) ↦ (m - 2a, -a)`. It is an
additive involution of `ℤ × ℤ`. -/
def conjugationEquiv : ℤ × ℤ ≃+ ℤ × ℤ where
  toFun g := (g.1 - 2 * g.2, -g.2)
  invFun g := (g.1 - 2 * g.2, -g.2)
  left_inv g := Prod.ext (by simp) (by simp)
  right_inv g := Prod.ext (by simp) (by simp)
  map_add' g h := Prod.ext (by simp only [Prod.fst_add, Prod.snd_add]; ring)
    (by simp only [Prod.snd_add, neg_add])

/-- The conjugation symmetry sends `(m, a)` to `(m - 2a, -a)`. -/
@[simp]
theorem conjugationEquiv_apply (g : ℤ × ℤ) : conjugationEquiv g = (g.1 - 2 * g.2, -g.2) :=
  (rfl)

/-- The conjugation symmetry of bidegrees is its own inverse. -/
@[simp]
theorem conjugationEquiv_symm : conjugationEquiv.symm = conjugationEquiv :=
  (rfl)

/-- The conjugation symmetry of bidegrees is an involution. -/
theorem conjugationEquiv_conjugationEquiv (g : ℤ × ℤ) :
    conjugationEquiv (conjugationEquiv g) = g :=
  conjugationEquiv.symm_apply_apply g

/-- The conjugate of a bigraded Poincaré series: the series of the bigraded vector space whose
piece in bidegree `(m - 2a, -a)` is the piece of the original space in bidegree `(m, a)`. It is
an algebra automorphism, so it is compatible with tensor products. -/
noncomputable def conjugate : Series ≃ₐ[ℕ] Series :=
  domCongr ℕ ℕ conjugationEquiv

/-- The coefficient of the conjugate series in bidegree `(m, a)` is the coefficient of the
original series in bidegree `(m - 2a, -a)`. -/
@[simp]
theorem coeff_conjugate (P : Series) (g : ℤ × ℤ) :
    (conjugate P).coeff g = P.coeff (conjugationEquiv g) := by
  rw [conjugate, coeff_domCongr, conjugationEquiv_symm]

/-- Conjugation moves a series concentrated in one bidegree to the conjugate bidegree. -/
@[simp]
theorem conjugate_single (g : ℤ × ℤ) (r : ℕ) :
    conjugate (single g r) = single (conjugationEquiv g) r :=
  domCongr_single _ _ _

/-- Conjugation of series is its own inverse. -/
@[simp]
theorem conjugate_symm : conjugate.symm = conjugate := by
  rw [conjugate, domCongr_symm, conjugationEquiv_symm]

/-- Conjugation of series is an involution. -/
@[simp]
theorem conjugate_conjugate (P : Series) : conjugate (conjugate P) = P := by
  conv_lhs => rw [← conjugate_symm]
  exact conjugate.symm_apply_apply P

/-- Conjugation preserves the total dimension. -/
@[simp]
theorem totalDim_conjugate (P : Series) : totalDim (conjugate P) = totalDim P := by
  induction P using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add P Q hP hQ => rw [map_add, map_add, map_add, hP, hQ]
  | single g r => rw [conjugate_single, totalDim_single, totalDim_single]

/-- Conjugating the stabilization factor `W` shifts it by `(1, 1)`: its generators in bidegrees
`(0, 0)` and `(-1, -1)` go to bidegrees `(0, 0)` and `(1, 1)`. -/
theorem conjugate_W : conjugate W = single (1, 1) 1 * W := by
  have hW (g : ℤ × ℤ) : W.coeff g = (single (0 : ℤ × ℤ) 1 : Series).coeff g +
      (single (0 : ℤ × ℤ) 1 : Series).coeff (g + (1, 1)) := by
    simpa [one_def] using coeff_mul_W 1 g
  refine AddMonoidAlgebra.coeff_injective (Finsupp.ext fun g => ?_)
  obtain ⟨m, a⟩ := g
  rw [coeff_conjugate, coeff_mul_W, hW]
  simp only [conjugationEquiv_apply, coeff_single, Finsupp.single_apply, Prod.ext_iff,
    Prod.fst_add, Prod.snd_add, Prod.fst_zero, Prod.snd_zero]
  split_ifs <;> omega

/-- Conjugating `W ^ k` shifts it by `(k, k)`. -/
theorem conjugate_W_pow (k : ℕ) : conjugate (W ^ k) = single ((k : ℤ), (k : ℤ)) 1 * W ^ k := by
  rw [map_pow, conjugate_W, mul_pow, single_pow, one_pow]
  congr 2
  ext <;> simp

/-- Conjugation inverts the Alexander variable of the Euler characteristic: a class of bidegree
`(m, a)` contributes `(-1)^m T^a`, and its conjugate `(-1)^(m - 2a) T^(-a) = (-1)^m T^(-a)`. -/
@[simp]
theorem euler_conjugate (P : Series) : euler (conjugate P) = invert (euler P) := by
  induction P using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add P Q hP hQ => simp only [map_add, hP, hQ]
  | single g r =>
    obtain ⟨m, a⟩ := g
    have hinv : invert (single a ((m.negOnePow : ℤˣ) : ℤ)) =
        single (-a) ((m.negOnePow : ℤˣ) : ℤ) :=
      domCongr_single _ _ _
    rw [conjugate_single, conjugationEquiv_apply, euler_single, euler_single, map_mul,
      map_natCast, hinv, Int.negOnePow_sub, Int.negOnePow_two_mul, mul_one]

end Bigraded

end TauCeti
