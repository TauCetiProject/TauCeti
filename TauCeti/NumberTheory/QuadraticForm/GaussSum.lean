/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
public import Mathlib.LinearAlgebra.Matrix.Symmetric
public import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
public import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import TauCeti.Data.Matrix.DotProduct
import TauCeti.Data.ZMod.MulCastHom.Sum
import TauCeti.InformationTheory.Coding.CharacterSum
import TauCeti.NumberTheory.LegendreSymbol.QuadraticChar.Quadric

/-!
# Gauss sums of quadratic forms in even rank

Let `A` be a symmetric matrix indexed by a type with `2k` elements. This file evaluates the Gauss
sum of the quadratic form `x ↦ xᵀ A x` in two settings, both in terms of the quadratic character of
the signed determinant `(-1)^k det A`.

Over a finite field `F` of odd characteristic with `q` elements, for `det A ≠ 0` and a primitive
additive character `ψ` of `F`,

`∑_x ψ(xᵀ A x) = χ((-1)^k det A) q^k`,

where `χ` is the quadratic character of `F`. Group the terms by the value `c = xᵀ A x`. For
`k > 0` the number of solutions of `xᵀ A x = c` is `q^{2k-1} + χ((-1)^k det A) q^{k-1} ν(c)`, with
`ν(0) = q - 1` and `ν(c) = -1` otherwise
(`Matrix.IsSymm.card_dotProduct_mulVec_eq_of_card_eq_two_mul_add_two`), and `ψ` sums to zero over
`F`.

For an integer matrix `A`, an odd modulus `a` prime to `det A`, and `e(t) = exp (2πi t)`,

`∑_{x ∈ (ℤ/a)^{2k}} e(xᵀ A x / a) = ((-1)^k det A / a) a^k`,

with the Jacobi symbol on the right. The sign of the classical quadratic Gauss sum never enters.
The proof reduces to prime moduli in two steps.

* **Coprime moduli.** If `u n + v m = 1`, then `1 / (m n) = u / m + v / n`, and the Chinese
  remainder theorem splits the sum modulo `m n` into the sums of `u A` modulo `m` and of `v A`
  modulo `n`. Since `det (u A) = u^{2k} det A`, this does not change the Jacobi symbols.
* **Removing a square.** If `N = p² M` with `p` odd and prime to `det A`, the sum modulo `N` is
  `p^{2k}` times the sum modulo `M`. Translating `x` by `c z` with `c = p M` changes `xᵀ A x` by
  `2c (A x) ⬝ᵥ z`, because `c² ≡ 0 (mod N)`; averaging over `z` kills every `x` with `c x ≠ 0`,
  since `c x = 0` exactly when `x ≡ 0 (mod p)` and `2A` is invertible modulo `p`. The surviving
  `x` are the multiples `p w` of the classes `w ∈ ℤ/pM`, and on them
  `e(p² wᵀ A w / N) = e(wᵀ A w / M)`.

At a prime `p` the sum is the Gauss sum over the field `ZMod p` with the standard character.

Since `2` is invertible modulo an odd `a`, the integral quadratic form `x ↦ xᵀ B x / 2` of an even
symmetric matrix `B` is `x ↦ xᵀ A x` modulo `a` for an integer matrix `A ≡ B / 2`, so the second
evaluation covers the Gauss sums of integral quadratic forms that are unimodular modulo `a`. These
are the sums that arise when theta series of even lattices are transformed under `Γ₀(N)`.

## Main statements

* `Matrix.IsSymm.sum_addChar_dotProduct_mulVec_of_card_eq_two_mul`: the Gauss sum of a
  nondegenerate quadratic form of even rank over a finite field of odd characteristic.
* `Matrix.sum_stdAddChar_dotProduct_mulVec_mul`: the Gauss sums modulo coprime `m` and `n`
  multiply.
* `Matrix.IsSymm.sum_stdAddChar_dotProduct_mulVec_of_eq_sq_mul`: the Gauss sum modulo `p² M` is
  `p^{#ι}` times the Gauss sum modulo `M`.
* `Matrix.IsSymm.sum_stdAddChar_dotProduct_mulVec_eq_jacobiSym`: the evaluation modulo an odd
  `a` prime to `det A`.

## References

* R. Lidl and H. Niederreiter, *Finite Fields*, Encyclopedia of Mathematics and its Applications
  20, Cambridge University Press (1997), Chapter 6, §2.
* B. Schoeneberg, *Elliptic Modular Functions*, Springer (1974), Chapter IX.
-/

public section

open Finset ZMod

namespace Matrix

/-! ### Over a finite field -/

section FiniteField

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {ι : Type*} [Fintype ι] [DecidableEq ι]
  {A : Matrix ι ι F}

/-- **The Gauss sum of a nondegenerate quadratic form of even rank** over a finite field `F` of
odd characteristic with `q` elements: if `A` is a symmetric matrix with `det A ≠ 0` indexed by a
type with `2k` elements and `ψ` is a primitive additive character of `F`, then
`∑_x ψ(xᵀ A x) = χ((-1)^k det A) q^k`, where `χ` is the quadratic character of `F`. -/
theorem IsSymm.sum_addChar_dotProduct_mulVec_of_card_eq_two_mul (hA : A.IsSymm)
    (hF : ringChar F ≠ 2) (hdet : A.det ≠ 0) {k : ℕ} (hι : Fintype.card ι = 2 * k) {R : Type*}
    [CommRing R] [IsDomain R] {ψ : AddChar F R} (hψ : ψ.IsPrimitive) :
    ∑ x : ι → F, ψ (x ⬝ᵥ A *ᵥ x) =
      quadraticChar F ((-1) ^ k * A.det) * (Fintype.card F : R) ^ k := by
  rcases k with _ | m
  · have : IsEmpty ι := Fintype.card_eq_zero_iff.mp hι
    simp [Matrix.det_isEmpty]
  have hsum : ∑ c, ψ c = 0 := by simpa using AddChar.sum_mulShift 1 hψ
  rw [← Fintype.sum_fiberwise (fun x : ι → F ↦ x ⬝ᵥ A *ᵥ x)]
  have hfib (c : F) : ∑ x : {x : ι → F // x ⬝ᵥ A *ᵥ x = c}, ψ (x.1 ⬝ᵥ A *ᵥ x.1) =
      ((#{x : ι → F | x ⬝ᵥ A *ᵥ x = c} : ℤ) : R) * ψ c := by
    rw [Finset.sum_congr rfl fun x _ ↦ congrArg ψ x.2, Finset.sum_const, Finset.card_univ,
      Fintype.card_subtype, nsmul_eq_mul, Int.cast_natCast]
  simp only [hfib, hA.card_dotProduct_mulVec_eq_of_card_eq_two_mul_add_two hF hdet
    (hι.trans (by ring)), Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_natCast]
  have hite (c : F) : ((if c = 0 then (Fintype.card F : ℤ) - 1 else -1 : ℤ) : R) =
      (if c = 0 then (Fintype.card F : R) else 0) - 1 := by
    split_ifs <;> simp
  simp only [hite, add_mul, mul_assoc, sum_add_distrib, ← mul_sum, sub_mul, one_mul, ite_mul,
    zero_mul, sum_sub_distrib, sum_ite_eq', mem_univ, ite_true, AddChar.map_zero_eq_one, hsum]
  ring

end FiniteField

/-! ### Modulo an odd integer -/

section ZMod

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- The form of the reduction of an integer matrix, at the reduction of an integer vector, is the
reduction of the integer value of the form: `RingHom.map_dotProduct_mulVec` for the cast. -/
private theorem intCast_dotProduct_mulVec (R : Type*) [CommRing R] (A : Matrix ι ι ℤ)
    (v : ι → ℤ) :
    (fun i ↦ (v i : R)) ⬝ᵥ A.map (Int.cast : ℤ → R) *ᵥ (fun i ↦ (v i : R)) =
      ((v ⬝ᵥ A *ᵥ v : ℤ) : R) :=
  ((Int.castRingHom R).map_dotProduct_mulVec A v v).symm

variable {A : Matrix ι ι ℤ}

/-- **Averaging over translates.** If `c ∈ ZMod N` has `c * c = 0` and `2c A x = 0` forces
`c • x = 0`, then only the classes `x` with `c • x = 0` contribute to the Gauss sum modulo `N`.
Translating by `c • z` changes `xᵀ A x` by `(2c A x) ⬝ᵥ z`, and the sum over `z` of this character
vanishes unless `2c A x = 0`, that is unless `c • x = 0`. -/
private theorem IsSymm.sum_stdAddChar_eq_sum_ite_smul_eq_zero (hA : A.IsSymm) {N : ℕ} [NeZero N]
    {c : ZMod N} (hc2 : c * c = 0)
    (hcond : ∀ x : ι → ZMod N, (2 * c) • (A.map (Int.cast : ℤ → ZMod N) *ᵥ x) = 0 → c • x = 0) :
    ∑ x : ι → ZMod N, stdAddChar (x ⬝ᵥ A.map (Int.cast : ℤ → ZMod N) *ᵥ x) =
      ∑ x : ι → ZMod N,
        if c • x = 0 then stdAddChar (x ⬝ᵥ A.map (Int.cast : ℤ → ZMod N) *ᵥ x) else 0 := by
  set A' := A.map (Int.cast : ℤ → ZMod N)
  have hexp (x z : ι → ZMod N) : (x + c • z) ⬝ᵥ A' *ᵥ (x + c • z) =
      x ⬝ᵥ A' *ᵥ x + ((2 * c) • (A' *ᵥ x)) ⬝ᵥ z := by
    have hsymm : z ⬝ᵥ A' *ᵥ x = x ⬝ᵥ A' *ᵥ z := by
      rw [dotProduct_mulVec, ← mulVec_transpose, (hA.map _).eq, dotProduct_comm]
    simp only [mulVec_add, mulVec_smul, add_dotProduct, dotProduct_add, smul_dotProduct,
      dotProduct_smul, smul_eq_mul, hsymm]
    rw [dotProduct_comm (A' *ᵥ x) z, hsymm]
    linear_combination (z ⬝ᵥ A' *ᵥ z) * hc2
  have hcond' (x : ι → ZMod N) : (2 * c) • (A' *ᵥ x) = 0 ↔ c • x = 0 :=
    ⟨hcond x, fun h ↦ by rw [mul_smul, ← mulVec_smul, h, mulVec_zero, smul_zero]⟩
  refine mul_left_cancel₀ (pow_ne_zero (Fintype.card ι) (Nat.cast_ne_zero.2 (NeZero.ne N))) ?_
  calc (N : ℂ) ^ Fintype.card ι * ∑ x : ι → ZMod N, stdAddChar (x ⬝ᵥ A' *ᵥ x)
      = ∑ z : ι → ZMod N, ∑ x : ι → ZMod N,
          stdAddChar ((x + c • z) ⬝ᵥ A' *ᵥ (x + c • z)) := by
        rw [Finset.sum_congr rfl fun z _ ↦ Fintype.sum_equiv (Equiv.addRight (c • z))
          (fun x ↦ stdAddChar ((x + c • z) ⬝ᵥ A' *ᵥ (x + c • z)))
          (fun x ↦ stdAddChar (x ⬝ᵥ A' *ᵥ x)) fun x ↦ rfl, sum_const, card_univ,
          Fintype.card_pi, prod_const, card_univ, ZMod.card, nsmul_eq_mul]
        push_cast
        ring
    _ = ∑ x : ι → ZMod N, stdAddChar (x ⬝ᵥ A' *ᵥ x) *
          ∑ z : ι → ZMod N, stdAddChar (((2 * c) • (A' *ᵥ x)) ⬝ᵥ z) := by
        simp_rw [hexp, AddChar.map_add_eq_mul, mul_sum]
        exact sum_comm
    _ = (N : ℂ) ^ Fintype.card ι *
          ∑ x : ι → ZMod N, if c • x = 0 then stdAddChar (x ⬝ᵥ A' *ᵥ x) else 0 := by
        simp_rw [AddChar.sum_apply_dotProduct (isPrimitive_stdAddChar N), ZMod.card, hcond',
          mul_sum, mul_ite, mul_zero]
        exact sum_congr rfl fun x _ ↦ by split_ifs <;> ring

/-- **Removing a square from the modulus.** Let `A` be a symmetric integer matrix, `p` an odd
natural number prime to `det A`, and `N = p ^ 2 * M`. With `e(t) = exp (2πi t)`, the Gauss sum
`∑_{x ∈ (ℤ/N)^ι} e(xᵀ A x / N)` is `p ^ #ι` times the Gauss sum `∑_{y ∈ (ℤ/M)^ι} e(yᵀ A y / M)`. -/
theorem IsSymm.sum_stdAddChar_dotProduct_mulVec_of_eq_sq_mul (hA : A.IsSymm) {N M p : ℕ}
    [NeZero N] [NeZero M] (hN : N = p ^ 2 * M) (hodd : Odd p) (hdet : IsCoprime A.det p) :
    ∑ x : ι → ZMod N, stdAddChar (x ⬝ᵥ A.map (Int.cast : ℤ → ZMod N) *ᵥ x) =
      (p : ℂ) ^ Fintype.card ι *
        ∑ y : ι → ZMod M, stdAddChar (y ⬝ᵥ A.map (Int.cast : ℤ → ZMod M) *ᵥ y) := by
  have hp : p ≠ 0 := by rintro rfl; exact absurd hodd (by decide)
  have : NeZero (p * M) := ⟨mul_ne_zero hp (NeZero.ne M)⟩
  have hpM : p * M * p = N := by rw [hN]; ring
  have hc2 : ((p * M : ℕ) : ZMod N) * ((p * M : ℕ) : ZMod N) = 0 := by
    rw [← Nat.cast_mul, show p * M * (p * M) = N * M by rw [hN]; ring, Nat.cast_mul,
      ZMod.natCast_self, zero_mul]
  -- `2 A` is invertible modulo `p`, and `p * M` kills exactly the classes vanishing modulo `p`.
  have hcond (x : ι → ZMod N) :
      (2 * ((p * M : ℕ) : ZMod N)) • (A.map (Int.cast : ℤ → ZMod N) *ᵥ x) = 0 →
        ((p * M : ℕ) : ZMod N) • x = 0 := by
    set φ := castHom (Dvd.intro_left (p * M) hpM) (ZMod p)
    have hker (y : ι → ZMod N) : ((p * M : ℕ) : ZMod N) • y = 0 ↔ φ ∘ y = 0 := by
      simp only [funext_iff, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, Function.comp_apply,
        ZMod.natCast_mul_eq_zero_iff p hpM (NeZero.ne (p * M)), φ]
    have hAp : (A.map (Int.cast : ℤ → ZMod N)).map φ = A.map (Int.cast : ℤ → ZMod p) := by
      rw [Matrix.map_map]
      exact congrArg A.map (funext fun j ↦ map_intCast φ j)
    have hunit : IsUnit (A.map (Int.cast : ℤ → ZMod p)).det := by
      rw [show (A.map (Int.cast : ℤ → ZMod p)).det = (A.det : ZMod p) from
        ((Int.castRingHom (ZMod p)).map_det A).symm]
      obtain ⟨u, v, huv⟩ := hdet
      refine IsUnit.of_mul_eq_one_right (u : ZMod p) ?_
      simpa using congrArg (Int.cast : ℤ → ZMod p) huv
    have h2 : IsUnit (2 : ZMod p) := by
      simpa using (ZMod.unitOfCoprime 2 (Nat.coprime_two_left.2 hodd)).isUnit
    intro h
    rw [mul_comm, mul_smul, hker, ← mulVec_smul] at h
    rw [hker]
    have h2x : φ ∘ ((2 : ZMod N) • x) = (2 : ZMod p) • (φ ∘ x) :=
      funext fun j ↦ by simp [map_ofNat]
    have h' : A.map (Int.cast : ℤ → ZMod p) *ᵥ ((2 : ZMod p) • (φ ∘ x)) = 0 := by
      ext i
      simpa only [Function.comp_apply, Pi.zero_apply, φ.map_mulVec, hAp, h2x] using congrFun h i
    have h'' := (mulVec_injective_of_isUnit ((isUnit_iff_isUnit_det _).2 hunit))
      (h'.trans (mulVec_zero _).symm)
    exact (h2.smul_left_cancel).1 (h''.trans (smul_zero _).symm)
  rw [hA.sum_stdAddChar_eq_sum_ite_smul_eq_zero hc2 hcond,
    ZMod.sum_ite_natCast_smul_eq_zero p hpM]
  -- On the multiples of `p`, the character of `ZMod N` is the character of `ZMod M`.
  have hval (w : ι → ZMod (p * M)) :
      stdAddChar ((fun i ↦ ZMod.mulCastHom p hpM (w i)) ⬝ᵥ A.map (Int.cast : ℤ → ZMod N) *ᵥ
        fun i ↦ ZMod.mulCastHom p hpM (w i)) =
      stdAddChar ((fun i ↦ castHom (Dvd.intro_left p rfl) (ZMod M) (w i)) ⬝ᵥ
        A.map (Int.cast : ℤ → ZMod M) *ᵥ
          fun i ↦ castHom (Dvd.intro_left p rfl) (ZMod M) (w i)) := by
    obtain ⟨v, rfl⟩ : ∃ v : ι → ℤ, (fun i ↦ (v i : ZMod (p * M))) = w :=
      ⟨fun i ↦ ((w i).cast : ℤ), funext fun i ↦ ZMod.intCast_zmod_cast _⟩
    have hmul (j : ℤ) : ZMod.mulCastHom p hpM (j : ZMod (p * M)) = ((p * j : ℤ) : ZMod N) := by
      rw [ZMod.mulCastHom_intCast]
      push_cast
      ring
    simp only [hmul, map_intCast]
    rw [intCast_dotProduct_mulVec, intCast_dotProduct_mulVec, stdAddChar_coe, stdAddChar_coe]
    have hsq : (fun i ↦ (p : ℤ) * v i) ⬝ᵥ A *ᵥ (fun i ↦ (p : ℤ) * v i) =
        (p : ℤ) ^ 2 * (v ⬝ᵥ A *ᵥ v) := by
      have hpv : (fun i ↦ (p : ℤ) * v i) = (p : ℤ) • v := funext fun _ ↦ (smul_eq_mul _ _).symm
      rw [hpv, mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]
      ring
    have hp' : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hp
    have hM' : (M : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne M)
    rw [hsq, hN]
    push_cast
    field_simp
  simp_rw [hval]
  have h := ZMod.sum_comp_castHom (ι := ι) (m := p) (n := p * M) M rfl
    fun y : ι → ZMod M ↦ stdAddChar (y ⬝ᵥ A.map (Int.cast : ℤ → ZMod M) *ᵥ y)
  rw [nsmul_eq_mul] at h
  push_cast at h
  exact h

/-- **Coprime moduli.** For natural numbers `m`, `n` and integers `u`, `v` with `u n + v m = 1`, the
Gauss sum `∑_{x ∈ (ℤ/mn)^ι} e(xᵀ A x / (m n))`, with `e(t) = exp (2πi t)`, is the product of the
Gauss sums of `u A` modulo `m` and of `v A` modulo `n`. -/
theorem sum_stdAddChar_dotProduct_mulVec_mul (A : Matrix ι ι ℤ) {m n : ℕ} [NeZero m]
    [NeZero n] {u v : ℤ} (huv : u * n + v * m = 1) :
    ∑ x : ι → ZMod (m * n), stdAddChar (x ⬝ᵥ A.map (Int.cast : ℤ → ZMod (m * n)) *ᵥ x) =
      (∑ y : ι → ZMod m, stdAddChar (y ⬝ᵥ (u • A).map (Int.cast : ℤ → ZMod m) *ᵥ y)) *
        ∑ z : ι → ZMod n, stdAddChar (z ⬝ᵥ (v • A).map (Int.cast : ℤ → ZMod n) *ᵥ z) := by
  have hmn : m.Coprime n := Nat.isCoprime_iff_coprime.1 ⟨v, u, by linear_combination huv⟩
  let e : (ι → ZMod (m * n)) ≃ (ι → ZMod m) × (ι → ZMod n) :=
    (Equiv.piCongrRight fun _ ↦ (chineseRemainder hmn).toEquiv).trans
      (Equiv.arrowProdEquivProdArrow ι _ _)
  rw [sum_mul_sum, ← Fintype.sum_prod_type']
  refine Fintype.sum_equiv e _ _ fun x ↦ ?_
  obtain ⟨w, rfl⟩ : ∃ w : ι → ℤ, (fun i ↦ (w i : ZMod (m * n))) = x :=
    ⟨fun i ↦ ((x i).cast : ℤ), funext fun i ↦ ZMod.intCast_zmod_cast _⟩
  have he : e (fun i ↦ (w i : ZMod (m * n))) =
      ((fun i ↦ (w i : ZMod m)), (fun i ↦ (w i : ZMod n))) := by
    ext i <;> simp [e, Equiv.arrowProdEquivProdArrow, map_intCast]
  rw [he]
  simp only
  rw [intCast_dotProduct_mulVec, intCast_dotProduct_mulVec, intCast_dotProduct_mulVec,
    stdAddChar_coe, stdAddChar_coe, stdAddChar_coe, ← Complex.exp_add]
  congr 1
  simp only [smul_mulVec, dotProduct_smul, smul_eq_mul, Int.cast_mul]
  have hm : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne m)
  have hn : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne n)
  have huv' : (u : ℂ) * n + v * m = 1 := by exact_mod_cast huv
  push_cast
  field_simp
  linear_combination (-((w ⬝ᵥ A *ᵥ w : ℤ) : ℂ)) * huv'

/-- **The Gauss sum of a quadratic form modulo an odd integer.** Let `A` be a symmetric integer
matrix indexed by a type with `2k` elements, and `a` an odd modulus prime to `det A`. With
`e(t) = exp (2πi t)`,
`∑_{x ∈ (ℤ/a)^ι} e(xᵀ A x / a) = ((-1)^k det A / a) a^k`, with the Jacobi symbol `(· / a)`. -/
theorem IsSymm.sum_stdAddChar_dotProduct_mulVec_eq_jacobiSym (hA : A.IsSymm) {k : ℕ}
    (hι : Fintype.card ι = 2 * k) {a : ℕ} [NeZero a] (ha : Odd a) (hdet : IsCoprime A.det a) :
    ∑ x : ι → ZMod a, stdAddChar (x ⬝ᵥ A.map (Int.cast : ℤ → ZMod a) *ᵥ x) =
      jacobiSym ((-1) ^ k * A.det) a * (a : ℂ) ^ k := by
  -- Induct over prime powers and coprime products, for all matrices at once: the coprime step
  -- replaces `A` by multiples `u • A` and `v • A`.
  suffices h : ∀ a : ℕ, ∀ A : Matrix ι ι ℤ, A.IsSymm → Odd a → IsCoprime A.det a →
      ∀ [NeZero a], ∑ x : ι → ZMod a, stdAddChar (x ⬝ᵥ A.map (Int.cast : ℤ → ZMod a) *ᵥ x) =
        jacobiSym ((-1) ^ k * A.det) a * (a : ℂ) ^ k from h a A hA ha hdet
  intro a
  induction a using Nat.recOnPrimeCoprime with
  | zero => intro A _ h0; exact absurd h0 (by decide)
  | prime_pow p e hp =>
    intro A hA
    have : Fact p.Prime := ⟨hp⟩
    -- Prime powers: the exponents `0` and `1` directly, then down by two with the reduction lemma.
    induction e using Nat.twoStepInduction with
    | zero =>
      rw [pow_zero]
      intro _ _ _
      have hx (x : ι → ZMod 1) : x = 0 := Subsingleton.elim x 0
      simp [hx, jacobiSym.one_right]
    | one =>
      rw [pow_one]
      intro hodd hdet _
      have hF : ringChar (ZMod p) ≠ 2 := by
        rw [ZMod.ringChar_zmod_n]
        rintro rfl
        exact absurd hodd (by decide)
      have hdet' : (A.map (Int.cast : ℤ → ZMod p)).det = (A.det : ZMod p) :=
        ((Int.castRingHom (ZMod p)).map_det A).symm
      have hne : (A.map (Int.cast : ℤ → ZMod p)).det ≠ 0 := by
        rw [hdet', Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
        intro h
        have hu := hdet.isUnit_of_dvd' h dvd_rfl
        rw [Int.isUnit_iff_natAbs_eq, Int.natAbs_natCast] at hu
        exact hp.one_lt.ne' hu
      rw [(hA.map _).sum_addChar_dotProduct_mulVec_of_card_eq_two_mul hF hne hι
        (isPrimitive_stdAddChar p), ZMod.card, hdet', ← jacobiSym.legendreSym.to_jacobiSym]
      simp [legendreSym]
    | more e ih₀ _ =>
      intro hodd hdet _
      have hp0 : p ≠ 0 := hp.ne_zero
      have : NeZero (p ^ e) := ⟨pow_ne_zero e hp0⟩
      have hoddp : Odd p := (Nat.odd_pow_iff (by omega)).1 hodd
      push_cast at hdet
      have hdetp : IsCoprime A.det p := (IsCoprime.pow_right_iff (by omega)).1 hdet
      have hgcd' : ((-1) ^ k * A.det).gcd p = 1 :=
        Int.isCoprime_iff_gcd_eq_one.1 ((isCoprime_one_left.neg_left.pow_left).mul_left hdetp)
      rw [hA.sum_stdAddChar_dotProduct_mulVec_of_eq_sq_mul (M := p ^ e) (p := p) (by ring) hoddp
          hdetp,
        ih₀ hoddp.pow (by exact_mod_cast hdetp.pow_right), hι, jacobiSym.pow_right,
        jacobiSym.pow_right, pow_add, jacobiSym.sq_one hgcd']
      push_cast
      ring
  | coprime a b ha hb hab iha ihb =>
    intro A hA hodd hdet _
    have : NeZero a := ⟨by omega⟩
    have : NeZero b := ⟨by omega⟩
    obtain ⟨u, v, huv⟩ : IsCoprime (b : ℤ) (a : ℤ) := Nat.isCoprime_iff_coprime.2 hab.symm
    rw [sum_stdAddChar_dotProduct_mulVec_mul A huv]
    push_cast at hdet
    have hua : IsCoprime u a := ⟨b, v, by linear_combination huv⟩
    have hvb : IsCoprime v b := ⟨a, u, by linear_combination huv⟩
    have hca : IsCoprime (u • A).det a := by
      rw [det_smul]
      exact hua.pow_left.mul_left hdet.of_mul_right_left
    have hcb : IsCoprime (v • A).det b := by
      rw [det_smul]
      exact hvb.pow_left.mul_left hdet.of_mul_right_right
    rw [iha (u • A) (hA.smul u) (Nat.odd_mul.1 hodd).1 hca,
      ihb (v • A) (hA.smul v) (Nat.odd_mul.1 hodd).2 hcb, det_smul, det_smul, hι]
    have hJ (w : ℤ) (c : ℕ) (hw : IsCoprime w c) :
        jacobiSym ((-1) ^ k * (w ^ (2 * k) * A.det)) c = jacobiSym ((-1) ^ k * A.det) c := by
      rw [show (-1) ^ k * (w ^ (2 * k) * A.det) = (w ^ k) ^ 2 * ((-1) ^ k * A.det) by ring,
        jacobiSym.mul_left, jacobiSym.sq_one' (Int.isCoprime_iff_gcd_eq_one.1 hw.pow_left),
        one_mul]
    rw [hJ u a hua, hJ v b hvb, jacobiSym.mul_right]
    push_cast
    ring

end ZMod

end Matrix
