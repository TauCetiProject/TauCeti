/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.PolynomialLaw.Coeff
public import TauCeti.RingTheory.PolynomialLaw.Power
public import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import TauCeti.RingTheory.TensorProduct.Maps

/-!
# Determinants in the sense of Chenevier

For a commutative ring `A` and an associative unital `A`-algebra `R`, possibly noncommutative, a
`d`-dimensional `A`-valued *determinant* on `R` is a polynomial law `D : R → A`, homogeneous of
degree `d`, which preserves `1` and products after every commutative scalar extension. The
motivating example is `det ∘ ρ` for an algebra map `ρ : R → Mₙ(A)`. Over rings in which `d!` is
not invertible, determinants keep more information than their traces: over `𝔽_p`, the `p`-th
powers of two different algebra maps `R → 𝔽_p` are different `p`-dimensional determinants whose
traces both vanish.

The characteristic polynomial of `D` at `x ∈ R` is `χ(x, X) = D(X − x) ∈ A[X]`, computed after
scalar extension to the polynomial ring `A[X]`. Writing
`χ(x, X) = ∑ᵢ (-1)ⁱ Λᵢ(x) X^(d - i)`, the coefficient `Λᵢ(x)` is the coefficient of `sⁱ t^(d - i)`
in `D(s x + t)`; the first one, `Λ₁`, is the trace of `D`, an `A`-linear map. The coefficients
are defined through the coefficients of the polynomial law, so they make sense over commutative
semirings, as does the definition of a determinant, while the characteristic polynomial needs the
subtraction of a ring.

## Main declarations

* `TauCeti.Determinant A R d`: `d`-dimensional `A`-valued determinants on `R`, with their value
  `D x` (the ground map of the law), multiplicative and homogeneous of degree `d`.
* `TauCeti.Determinant.toMonoidHom`, `TauCeti.Determinant.isUnit_apply`: a determinant is a
  monoid map `R →* A`, so it sends units to units.
* `TauCeti.Determinant.toFun_eq_one_of_dim_zero`: a determinant of dimension zero is constantly
  `1`, and there is exactly one.
* `TauCeti.Determinant.charCoeff`: the characteristic coefficients `Λᵢ`, with
  `TauCeti.Determinant.toFun_tmul_add_tmul_one` computing `D(s x + t)` from them.
* `TauCeti.Determinant.trace`: the trace `Λ₁` as an `A`-linear map, with `D.trace 1 = d`.
* `TauCeti.Determinant.charpoly`: the characteristic polynomial, monic of degree `d`, with
  `χ(x, 0) = (-1)ᵈ D x` and `χ(1, X) = (X - 1)ᵈ`.
* `TauCeti.Determinant.algHomPow`: the `d`-th power of an algebra map `R →ₐ[A] A`, a
  `d`-dimensional determinant with characteristic polynomial `(X - φ x)ᵈ`.

## References

* [G. Chenevier, *The p-adic analytic space of pseudocharacters of a profinite group and
  pseudorepresentations over arbitrary rings*, §1.5 and §1.10](https://arxiv.org/abs/0809.0415)
-/

public section

noncomputable section

universe u

open TensorProduct Polynomial

namespace TauCeti

/-- A `d`-dimensional `A`-valued determinant on the `A`-algebra `R` (Chenevier): a polynomial law
`R → A`, homogeneous of degree `d`, which preserves `1` and products after every commutative
scalar extension. Two determinants are equal when their laws are, after every scalar extension,
not merely when their values on `R` agree. -/
@[ext]
structure Determinant (A : Type u) [CommSemiring A] (R : Type*) [Semiring R] [Algebra A R]
    (d : ℕ) where
  /-- The underlying polynomial law `R → A`. -/
  toLaw : R →ₚₗ[A] A
  /-- The law is homogeneous of degree `d` after every scalar extension. -/
  isHomogeneousOfDegree : toLaw.IsHomogeneousOfDegree d
  /-- The law preserves `1` and products after every scalar extension. -/
  isMultiplicative : toLaw.IsMultiplicative

namespace Determinant

section CommSemiring

variable {A : Type u} [CommSemiring A] {R : Type*} [Semiring R] [Algebra A R] {d : ℕ}
  (D : Determinant A R d)

/-- The value `D x ∈ A` of a determinant at `x ∈ R`, the ground map of its polynomial law. It
does not determine `D` in general. -/
@[coe]
def ground : R → A := D.toLaw.ground

instance : CoeFun (Determinant A R d) fun _ ↦ R → A := ⟨ground⟩

@[simp]
theorem ground_toLaw : D.toLaw.ground = ⇑D :=
  (rfl)

/-- A determinant sends `1` to `1`. -/
@[simp]
theorem map_one : D 1 = 1 :=
  D.isMultiplicative.ground_one

/-- A determinant is multiplicative. -/
@[simp]
theorem map_mul (x y : R) : D (x * y) = D x * D y :=
  D.isMultiplicative.ground_mul x y

/-- A `d`-dimensional determinant is homogeneous of degree `d`. -/
@[simp]
theorem map_smul (a : A) (x : R) : D (a • x) = a ^ d * D x :=
  D.isHomogeneousOfDegree.ground_smul a x

/-- A `d`-dimensional determinant sends the scalar `a` to `a ^ d`. -/
theorem map_algebraMap (a : A) : D (algebraMap A R a) = a ^ d := by
  rw [Algebra.algebraMap_eq_smul_one, map_smul, map_one, mul_one]

/-- A determinant as a monoid map `R →* A`. -/
def toMonoidHom : R →* A where
  toFun := D
  map_one' := D.map_one
  map_mul' := D.map_mul

@[simp]
theorem coe_toMonoidHom : ⇑D.toMonoidHom = D :=
  (rfl)

/-- A determinant sends units to units. -/
theorem isUnit_apply {x : R} (hx : IsUnit x) : IsUnit (D x) :=
  hx.map D.toMonoidHom

/-- A determinant of dimension zero is constantly `1`, after every scalar extension. -/
theorem toFun_eq_one_of_dim_zero (D : Determinant A R 0) (S : Type*) [CommSemiring S]
    [Algebra A S] (x : S ⊗[A] R) : D.toLaw.toFun S x = 1 := by
  have h := D.isHomogeneousOfDegree.toFun_smul (0 : S) x
  rw [pow_zero, one_smul, zero_smul, ← zero_smul S (1 : S ⊗[A] R),
    D.isHomogeneousOfDegree.toFun_smul, pow_zero, one_smul, D.isMultiplicative.toFun_one] at h
  exact h.symm

/-- There is exactly one determinant of dimension zero, the constant law `1`. -/
instance : Unique (Determinant A R 0) where
  default :=
    { toLaw :=
        { toFun' _ _ _ _ := 1
          isCompat' φ := funext fun _ ↦
            _root_.map_one (Algebra.TensorProduct.map φ (AlgHom.id A A)) }
      isHomogeneousOfDegree :=
        PolynomialLaw.isHomogeneousOfDegree_iff.mpr fun _ _ _ _ _ ↦ by rw [pow_zero, one_smul]
      isMultiplicative :=
        { toFun'_one _ _ _ := rfl
          toFun'_mul _ _ := (mul_one 1).symm } }
  uniq D := by
    ext S _ _ x
    rw [PolynomialLaw.toFun'_eq_toFun, toFun_eq_one_of_dim_zero]

/-- The `i`-th characteristic coefficient `Λᵢ(x)` of a `d`-dimensional determinant: the
coefficient of `sⁱ t^(d - i)` in `D(s x + t)`, so that the characteristic polynomial is
`∑ᵢ (-1)ⁱ Λᵢ(x) X^(d - i)` (`charpoly_eq_sum`). It is `1` for `i = 0`, `D x` for `i = d`, and
`0` for `i > d`. -/
def charCoeff (i : ℕ) (x : R) : A :=
  PolynomialLaw.coeff A A (Option.elim' x fun _ : Unit ↦ 1) D.toLaw
    ((Finsupp.single () (d - i)).optionElim i)

/-- The characteristic coefficients vanish above the dimension. -/
theorem charCoeff_eq_zero {i : ℕ} (hi : d < i) (x : R) : D.charCoeff i x = 0 :=
  D.isHomogeneousOfDegree.coeff_eq_zero _ <| by
    simp [Nat.sub_eq_zero_of_le hi.le, hi.ne']

/-- After scalar extension to any commutative `A`-algebra `S`,
`D(s ⊗ x + t ⊗ 1) = ∑ᵢ sⁱ t^(d - i) Λᵢ(x)`. -/
theorem toFun_tmul_add_tmul_one {S : Type*} [CommSemiring S] [Algebra A S] (s t : S) (x : R) :
    D.toLaw.toFun S (s ⊗ₜ x + t ⊗ₜ 1) =
      ∑ i ∈ Finset.range (d + 1), (s ^ i * t ^ (d - i)) ⊗ₜ D.charCoeff i x := by
  classical
  let K : ℕ → Option Unit →₀ ℕ := fun i ↦ (Finsupp.single () (d - i)).optionElim i
  have hK : Set.InjOn K (Finset.range (d + 1)) := fun i _ j _ h ↦ by
    simpa [K] using DFunLike.congr_fun h none
  have hsupp : (PolynomialLaw.coeff A A (Option.elim' x fun _ : Unit ↦ 1) D.toLaw).support ⊆
      (Finset.range (d + 1)).image K := by
    intro k hk
    have hdeg : k none + k (some ()) = d := by
      by_contra h
      exact Finsupp.mem_support_iff.mp hk
        (D.isHomogeneousOfDegree.coeff_eq_zero _ (by simpa [Fintype.sum_option] using h))
    refine Finset.mem_image.mpr ⟨k none, Finset.mem_range.mpr (by omega), ?_⟩
    ext o
    rcases o with _ | ⟨⟨⟩⟩ <;> simp [K, ← hdeg]
  have hsum : ∑ o : Option Unit, Option.elim' s (fun _ ↦ t) o ⊗ₜ[A]
      Option.elim' x (fun _ ↦ (1 : R)) o = s ⊗ₜ x + t ⊗ₜ 1 := by
    simp [Fintype.sum_option]
  rw [← hsum, PolynomialLaw.toFun_sum_tmul_eq_coeff_sum,
    Finsupp.sum_of_support_subset _ hsupp _ (fun _ _ ↦ tmul_zero _ _), Finset.sum_image hK]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  simp [K, Fintype.prod_option, charCoeff]

/-- The characteristic coefficient `Λ₀` is `1`. -/
theorem charCoeff_zero (x : R) : D.charCoeff 0 x = 1 := by
  have h := D.toFun_tmul_add_tmul_one (0 : A) 1 x
  rw [zero_tmul, zero_add, ← Algebra.TensorProduct.one_def, D.isMultiplicative.toFun_one,
    Finset.sum_range_succ'] at h
  simp only [pow_succ, mul_zero, zero_tmul, Finset.sum_const_zero, pow_zero, one_pow,
    mul_one, zero_add] at h
  simpa [Algebra.TensorProduct.one_def] using (congrArg (TensorProduct.lid A A) h).symm

/-- The top characteristic coefficient `Λ_d` is the determinant itself. -/
theorem charCoeff_dim (x : R) : D.charCoeff d x = D x := by
  have h := D.toFun_tmul_add_tmul_one (1 : A) 0 x
  rw [zero_tmul, add_zero, ← PolynomialLaw.toFun'_eq_toFun, ← PolynomialLaw.one_tmul_ground_apply',
    Finset.sum_range_succ, Finset.sum_eq_zero fun i hi ↦ by
      rw [zero_pow (by simp at hi; omega), mul_zero, zero_tmul]] at h
  simpa using (congrArg (TensorProduct.lid A A) h).symm

/-- The characteristic coefficients of `1` are the binomial coefficients. -/
theorem charCoeff_one_eq_choose (i : ℕ) : D.charCoeff i 1 = d.choose i := by
  rcases lt_or_ge d i with hi | hi
  · rw [D.charCoeff_eq_zero hi, Nat.choose_eq_zero_of_lt hi, Nat.cast_zero]
  have h := D.toFun_tmul_add_tmul_one (X : A[X]) 1 1
  rw [← add_tmul, ← mul_one (X + 1 : A[X]), ← smul_eq_mul, ← smul_tmul',
    D.isHomogeneousOfDegree.toFun_smul, ← Algebra.TensorProduct.one_def,
    D.isMultiplicative.toFun_one, Algebra.TensorProduct.one_def, smul_tmul', smul_eq_mul,
    mul_one] at h
  have h' := congrArg (fun p ↦ (Algebra.TensorProduct.rid A A A[X] p).coeff i) h
  simp only [map_sum, Algebra.TensorProduct.rid_tmul, one_pow, mul_one, finsetSum_coeff,
    smul_eq_C_mul, coeff_C_mul, coeff_X_pow, mul_ite, mul_zero, Finset.sum_ite_eq,
    Finset.mem_range, one_smul, coeff_X_add_one_pow] at h'
  rw [ite_eq_left (by omega)] at h'
  exact h'.symm

/-- The trace of a determinant, its first characteristic coefficient `Λ₁`, as an `A`-linear map.
It is `0` for a determinant of dimension zero. -/
def trace : R →ₗ[A] A where
  toFun := D.charCoeff 1
  map_add' x y := PolynomialLaw.coeff_optionElim_add_of_exponent_one x y _ _ _
  map_smul' a x := by simpa [charCoeff] using PolynomialLaw.coeff_optionElim_smul 1 a x _ D.toLaw _

/-- The trace is the first characteristic coefficient. -/
theorem trace_apply (x : R) : D.trace x = D.charCoeff 1 x :=
  (rfl)

/-- The trace of `1` is the dimension. -/
@[simp]
theorem trace_one : D.trace 1 = d := by
  rw [trace_apply, charCoeff_one_eq_choose, Nat.choose_one_right]

/-- A determinant of dimension zero has trace zero. -/
theorem trace_eq_zero_of_dim_zero (D : Determinant A R 0) : D.trace = 0 :=
  LinearMap.ext fun x ↦ D.charCoeff_eq_zero zero_lt_one x

end CommSemiring

section CommRing

variable {A : Type u} [CommRing A] {R : Type*} [Ring R] [Algebra A R] {d : ℕ}
  (D : Determinant A R d)

/-- The characteristic polynomial `χ(x, X) = D(X − x) ∈ A[X]` of a determinant at `x ∈ R`,
computed after scalar extension to the polynomial ring `A[X]`. -/
def charpoly (x : R) : A[X] :=
  Algebra.TensorProduct.rid A A A[X] (D.toLaw.toFun' A[X] (X ⊗ₜ 1 - 1 ⊗ₜ x))

/-- The characteristic polynomial in terms of the characteristic coefficients:
`χ(x, X) = ∑ᵢ (-1)ⁱ Λᵢ(x) X^(d - i)`. -/
theorem charpoly_eq_sum (x : R) :
    D.charpoly x = ∑ i ∈ Finset.range (d + 1), C ((-1) ^ i * D.charCoeff i x) * X ^ (d - i) := by
  have hx : (X : A[X]) ⊗ₜ[A] (1 : R) - 1 ⊗ₜ x = (-1 : A[X]) ⊗ₜ x + X ⊗ₜ 1 := by
    rw [neg_tmul, sub_eq_neg_add]
  rw [charpoly, hx, PolynomialLaw.toFun'_eq_toFun, toFun_tmul_add_tmul_one, map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Algebra.TensorProduct.rid_tmul, smul_eq_C_mul, C_mul, C_pow, C_neg, C_1]
  ring

/-- The coefficient of `X ^ j` in the characteristic polynomial is `(-1)^(d - j) Λ_(d - j)(x)`
for `j ≤ d`, and `0` above the dimension. -/
theorem coeff_charpoly (x : R) (j : ℕ) :
    (D.charpoly x).coeff j = if j ≤ d then (-1) ^ (d - j) * D.charCoeff (d - j) x else 0 := by
  rw [charpoly_eq_sum, finsetSum_coeff]
  simp only [coeff_C_mul_X_pow]
  split_ifs with hj
  · rw [Finset.sum_eq_single_of_mem (d - j) (Finset.mem_range.mpr (by omega)) fun i hi' hi ↦
      ite_eq_right (by simp at hi'; omega), ite_eq_left (by omega)]
  · exact Finset.sum_eq_zero fun i hi ↦ ite_eq_right (by simp at hi; omega)

/-- The characteristic polynomial has degree at most the dimension. -/
theorem charpoly_natDegree_le (x : R) : (D.charpoly x).natDegree ≤ d :=
  natDegree_le_iff_coeff_eq_zero.mpr fun j hj ↦ by rw [coeff_charpoly, ite_eq_right (by omega)]

/-- The coefficient of `X ^ d` in the characteristic polynomial is `1`. -/
theorem coeff_charpoly_dim (x : R) : (D.charpoly x).coeff d = 1 := by
  rw [coeff_charpoly, ite_eq_left le_rfl, Nat.sub_self, pow_zero, one_mul, charCoeff_zero]

/-- The characteristic polynomial is monic. -/
theorem charpoly_monic (x : R) : (D.charpoly x).Monic :=
  monic_of_natDegree_le_of_coeff_eq_one d (D.charpoly_natDegree_le x) (D.coeff_charpoly_dim x)

/-- Over a nontrivial ring, the characteristic polynomial has degree exactly the dimension. -/
@[simp]
theorem charpoly_natDegree_eq_dim [Nontrivial A] (x : R) : (D.charpoly x).natDegree = d :=
  natDegree_eq_of_le_of_coeff_ne_zero (D.charpoly_natDegree_le x)
    (by rw [coeff_charpoly_dim]; exact one_ne_zero)

/-- The constant term of the characteristic polynomial is `(-1) ^ d D x`. -/
theorem eval_zero_charpoly (x : R) : (D.charpoly x).eval 0 = (-1) ^ d * D x := by
  rw [← coeff_zero_eq_eval_zero, coeff_charpoly, ite_eq_left (Nat.zero_le d), Nat.sub_zero,
    charCoeff_dim]

/-- In positive dimension, the trace is minus the coefficient of `X ^ (d - 1)` in the
characteristic polynomial. -/
theorem trace_eq_neg_charpoly_coeff (hd : 0 < d) (x : R) :
    D.trace x = -(D.charpoly x).coeff (d - 1) := by
  rw [coeff_charpoly, ite_eq_left (Nat.sub_le d 1), Nat.sub_sub_self hd, pow_one, neg_one_mul,
    neg_neg, trace_apply]

/-- The characteristic polynomial of `1` is `(X - 1) ^ d`. -/
@[simp]
theorem charpoly_one : D.charpoly 1 = (X - 1) ^ d := by
  have h : (X : A[X]) ⊗ₜ[A] (1 : R) - 1 ⊗ₜ 1 = (X - 1 : A[X]) • (1 : A[X] ⊗[A] R) := by
    rw [Algebra.TensorProduct.one_def, smul_tmul', smul_eq_mul, mul_one, sub_tmul]
  rw [charpoly, h, D.isHomogeneousOfDegree.toFun'_smul, PolynomialLaw.toFun'_eq_toFun,
    D.isMultiplicative.toFun_one, Algebra.TensorProduct.one_def, smul_tmul', smul_eq_mul, mul_one,
    Algebra.TensorProduct.rid_tmul, one_smul]

end CommRing

section AlgHomPow

variable {A : Type u} [CommSemiring A] {R : Type*} [Semiring R] [Algebra A R]

/-- The `d`-th power `x ↦ φ(x) ^ d` of an `A`-algebra map `φ : R →ₐ[A] A`, a `d`-dimensional
determinant. -/
def algHomPow (φ : R →ₐ[A] A) (d : ℕ) : Determinant A R d where
  toLaw := (PolynomialLaw.power A A d).comp φ.toLinearMap.toPolynomialLaw
  isHomogeneousOfDegree := by
    simpa using (PolynomialLaw.isHomogeneousOfDegree_power d).comp
      φ.toLinearMap.isHomogeneousOfDegree_toPolynomialLaw
  isMultiplicative :=
    (PolynomialLaw.isMultiplicative_power A A d).comp φ.isMultiplicative_toPolynomialLaw

/-- After scalar extension to `S`, the law of `algHomPow φ d` is the `d`-th power of
`φ` extended to `S`. -/
theorem algHomPow_toFun' (φ : R →ₐ[A] A) (d : ℕ) (S : Type u) [CommSemiring S] [Algebra A S]
    (x : S ⊗[A] R) :
    (algHomPow φ d).toLaw.toFun' S x = Algebra.TensorProduct.map (AlgHom.id A S) φ x ^ d := by
  rw [algHomPow, PolynomialLaw.comp_toFun', Function.comp_apply, PolynomialLaw.power_toFun',
    LinearMap.toPolynomialLaw_toFun', LinearMap.baseChange_eq_lTensor,
    AlgHom.lTensor_toLinearMap_apply]

/-- The value of `algHomPow φ d` at `x` is `φ x ^ d`. -/
@[simp]
theorem algHomPow_apply (φ : R →ₐ[A] A) (d : ℕ) (x : R) : algHomPow φ d x = φ x ^ d := by
  simp [← ground_toLaw, PolynomialLaw.ground_apply, algHomPow_toFun']

end AlgHomPow

section AlgHomPowCharpoly

variable {A : Type u} [CommRing A] {R : Type*} [Ring R] [Algebra A R]

/-- The characteristic polynomial of `algHomPow φ d` at `x` is `(X - φ x) ^ d`. -/
@[simp]
theorem charpoly_algHomPow (φ : R →ₐ[A] A) (d : ℕ) (x : R) :
    (algHomPow φ d).charpoly x = (X - C (φ x)) ^ d := by
  simp [charpoly, algHomPow_toFun', Algebra.TensorProduct.rid_tmul, smul_eq_C_mul]

/-- The trace of `algHomPow φ d` at `x` is `d * φ x`. -/
@[simp]
theorem trace_algHomPow (φ : R →ₐ[A] A) (d : ℕ) (x : R) :
    (algHomPow φ d).trace x = d * φ x := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · rw [trace_eq_zero_of_dim_zero, LinearMap.zero_apply, Nat.cast_zero, zero_mul]
  rw [trace_eq_neg_charpoly_coeff _ hd, charpoly_algHomPow, sub_eq_add_neg, ← C_neg,
    coeff_X_add_C_pow, Nat.sub_sub_self hd, pow_one, Nat.choose_symm hd,
    Nat.choose_one_right]
  ring

end AlgHomPowCharpoly

end Determinant

end TauCeti
