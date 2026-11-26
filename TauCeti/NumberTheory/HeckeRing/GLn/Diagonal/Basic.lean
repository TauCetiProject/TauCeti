/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Diagonal.Basic

/-!
# Natural diagonal elements of `GL_n(ℚ)`

The diagonal matrix `diag(a₁,...,aₙ)` with positive natural number entries, as an element of
`GL_n(ℚ)`. These elements name the double cosets of the arithmetic Hecke triple
(`TauCeti.NumberTheory.HeckeRing.GLn.Diagonal.Cosets`). Over `n = 2`, `diag(d, 1)` is also the
rational form of the matrix that defines the level-raising operator on modular forms
(`TauCeti.map_natDiagGL_d_one_eq_scaleGL`). This file keeps only the definition and its
elementary matrix-level API (multiplicativity, determinant, commutation, scalar constants), so that
both uses can import it without the Hecke ring.

Ported from the AINTLIB `LeanModularForms` project
([`LeanModularForms/HeckeRIngs/GLn/DiagonalCosets.lean`](https://github.com/CBirkbeck/AINTLIB),
Chris Birkbeck).

## Main definitions

* `HeckeRing.GLn.natDiagGL`: the diagonal matrix `diag(a₁,...,aₙ)` as an element of `GL_n(ℚ)`,
  with the identity as junk value when some entry is zero.
* `HeckeRing.GLn.intPowDiagGL`: the `p`-power diagonal matrix `diag(p ^ e₁, …, p ^ eₙ)` in
  `GL_n(ℚ)` for integer exponents `e : Fin n → ℤ`, with the identity as junk value at `p = 0`.

## Main results

* `HeckeRing.GLn.natDiagGL_coe`: for positive entries, the underlying matrix is
  `Matrix.diagonal (fun i ↦ (a i : ℚ))`.
* `HeckeRing.GLn.natDiagGL_of_not_pos`: otherwise `natDiagGL` is the identity.
* `HeckeRing.GLn.natDiagGL_mul`, `HeckeRing.GLn.natDiagGL_comm`: multiplicativity in the entries,
  and commutation of any two natural diagonals.
* `HeckeRing.GLn.natDiagGL_const_eq_scalar`, `HeckeRing.GLn.natDiagGL_const_mem_normalizer`: a
  constant natural diagonal is scalar when positive, and normalizes every subgroup unconditionally.
* `HeckeRing.GLn.intPowDiagGL_coe`, `HeckeRing.GLn.intPowDiagGL_add`,
  `HeckeRing.GLn.intPowDiagGL_neg`, `HeckeRing.GLn.intPowDiagGL_mem_glpos`,
  `HeckeRing.GLn.intPowDiagGL_natCast`: matrix coercion, group homomorphism properties, positive
  determinant, and agreement with `natDiagGL` on natural exponents.
-/

public section

open Matrix

namespace HeckeRing.GLn

variable (n : ℕ)

/-- The diagonal `GL_n(ℚ)` element `diag(a₁,...,aₙ)` with positive natural number entries.
Returns `1` (the identity matrix) when the positivity condition `∀ i, 0 < a i` fails;
this is a junk value that simplifies the API by avoiding an explicit positivity argument.
Only positivity is needed for a meaningful value — a positive tuple that is not a
divisibility chain still names its genuine diagonal coset. -/
noncomputable def natDiagGL (a : Fin n → ℕ) : GL (Fin n) ℚ :=
  if h : ∀ i, 0 < a i then
    TauCeti.diagGL fun i ↦ Units.mk0 (a i : ℚ) (by exact_mod_cast (h i).ne')
  else 1

@[simp] lemma natDiagGL_coe (a : Fin n → ℕ) (ha : ∀ i, 0 < a i) :
    (↑(natDiagGL n a) : Matrix (Fin n) (Fin n) ℚ) =
    Matrix.diagonal (fun i ↦ (a i : ℚ)) := by
  rw [natDiagGL, dite_eq_left ha, TauCeti.diagGL_coe]
  simp

/-- The junk branch of `natDiagGL`: without positivity the value is the identity. -/
@[simp] lemma natDiagGL_of_not_pos {a : Fin n → ℕ} (ha : ¬ ∀ i, 0 < a i) :
    natDiagGL n a = 1 :=
  dite_eq_right ha


/-- **The integral witness of `natDiagGL`.** `natDiagGL n a` is the entrywise cast of the
integral diagonal matrix with entries `a`.

`natDiagGL_coe` gives the same matrix as a `ℚ`-valued diagonal; this states it in the form the
integral-witness API asks for, so that `mapGL_mul_coe_eq_intMatrix` and its relatives can be
applied to a product with `natDiagGL` in the middle without re-deriving the cast each time. -/
lemma natDiagGL_coe_eq_map_intCast (a : Fin n → ℕ) (ha : ∀ i, 0 < a i) :
    (↑(natDiagGL n a) : Matrix (Fin n) (Fin n) ℚ) =
      (Matrix.diagonal (fun i ↦ (a i : ℤ))).map (Int.cast : ℤ → ℚ) := by
  rw [natDiagGL_coe n a ha, Matrix.diagonal_map (by simp)]
  norm_num

/-- Positivity is preserved by pointwise products. -/
private lemma pi_mul_pos {a b : Fin n → ℕ} (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i) :
    ∀ i, 0 < (a * b) i :=
  fun i ↦ Nat.mul_pos (ha i) (hb i)

/-- The diagonal element is multiplicative in its tuple of entries. -/
@[simp]
lemma natDiagGL_mul (a b : Fin n → ℕ) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i) :
    natDiagGL n a * natDiagGL n b = natDiagGL n (a * b) := by
  apply Units.ext
  simp [natDiagGL_coe n a ha, natDiagGL_coe n b hb,
    natDiagGL_coe n (a * b) (pi_mul_pos n ha hb), Matrix.diagonal_mul_diagonal,
    Pi.mul_apply, Nat.cast_mul]

/-- The determinant of `natDiagGL n a` is positive, with no positivity hypothesis on `a`: when an
entry is not positive the value is the identity, of determinant `1`. -/
lemma natDiagGL_det_pos (a : Fin n → ℕ) :
    0 < (↑(natDiagGL n a) : Matrix (Fin n) (Fin n) ℚ).det := by
  by_cases ha : ∀ i, 0 < a i
  · rw [natDiagGL_coe n a ha, det_diagonal]
    exact Finset.prod_pos (fun i _ ↦ by positivity [ha i])
  · rw [natDiagGL_of_not_pos n ha]
    simp

lemma natDiagGL_det (a : Fin n → ℕ) (ha : ∀ i, 0 < a i) :
    (↑(natDiagGL n a) : Matrix (Fin n) (Fin n) ℚ).det = ∏ i, (a i : ℚ) := by
  rw [natDiagGL_coe n a ha, Matrix.det_diagonal]

/-- **Natural diagonal matrices commute**, with no positivity hypothesis: on the positive branch
this is `natDiagGL_mul` and `mul_comm` of the entry tuples, and when either tuple fails positivity
that factor is the junk value `1`, which commutes with everything. -/
lemma natDiagGL_comm (a b : Fin n → ℕ) :
    natDiagGL n a * natDiagGL n b = natDiagGL n b * natDiagGL n a := by
  by_cases ha : ∀ i, 0 < a i
  · by_cases hb : ∀ i, 0 < b i
    · rw [natDiagGL_mul n a b ha hb, natDiagGL_mul n b a hb ha, mul_comm a b]
    · rw [natDiagGL_of_not_pos n hb, one_mul, mul_one]
  · rw [natDiagGL_of_not_pos n ha, one_mul, mul_one]

/-- A positive constant natural diagonal is the corresponding scalar matrix. -/
lemma natDiagGL_const_eq_scalar {c : ℕ} (hc : 0 < c) :
    natDiagGL n (fun _ ↦ c) =
      Matrix.GeneralLinearGroup.scalar (Fin n)
        (Units.mk0 (c : ℚ) (by exact_mod_cast hc.ne')) := by
  apply Units.ext
  ext i j
  simp only [natDiagGL_coe n _ fun _ ↦ hc, Matrix.GeneralLinearGroup.coe_scalar,
    Matrix.scalar_apply, Matrix.diagonal_apply, Units.val_mk0]

/-- A constant diagonal matrix is a scalar, hence commutes with everything — unconditionally
in the constant, since `c = 0` sends `natDiagGL` to its junk value `1`. -/
lemma natDiagGL_const_comm (c : ℕ) (g : GL (Fin n) ℚ) :
    natDiagGL n (fun _ ↦ c) * g = g * natDiagGL n (fun _ ↦ c) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  -- at rank zero `GL (Fin 0) ℚ` is trivial
  · exact Subsingleton.elim _ _
  rcases Nat.eq_zero_or_pos c with rfl | hc
  · rw [natDiagGL_of_not_pos n (not_forall.mpr ⟨⟨0, hn⟩, by simp⟩), one_mul, mul_one]
  · rw [natDiagGL_const_eq_scalar n hc]
    exact Matrix.GeneralLinearGroup.scalar_commute _ _

/-- A constant natural diagonal normalizes every subgroup of `GLₙ(ℚ)`: it is central. -/
lemma natDiagGL_const_mem_normalizer (c : ℕ) (Γ : Subgroup (GL (Fin n) ℚ)) :
    natDiagGL n (fun _ ↦ c) ∈ Subgroup.normalizer Γ :=
  Subgroup.center_le_normalizer _
    (Subgroup.mem_center_iff.mpr fun g ↦ (natDiagGL_const_comm n c g).symm)

@[simp] lemma natDiagGL_one : natDiagGL n (fun _ ↦ 1) = 1 := by
  ext1
  rw [natDiagGL_coe n _ (fun _ ↦ Nat.one_pos)]
  simp

/-- The all-zeros tuple sends `natDiagGL` to its fallback value `1` in every rank `n`. -/
@[simp] lemma natDiagGL_const_zero : natDiagGL n (fun _ ↦ 0) = 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact Subsingleton.elim _ _
  · exact natDiagGL_of_not_pos n fun h ↦ Nat.lt_irrefl 0 (h ⟨0, hn⟩)

section IntPowDiag

/-- The `p`-power diagonal matrix `diag(p ^ e₁, …, p ^ eₙ) ∈ GL_n(ℚ)` with integer exponents
`e : Fin n → ℤ` for `p ≠ 0`, taking the junk value `1` at `p = 0` to match `natDiagGL`. -/
noncomputable def intPowDiagGL (p : ℕ) (e : Fin n → ℤ) : GL (Fin n) ℚ :=
  if hp : p = 0 then 1
  else TauCeti.diagGL fun i ↦ Units.mk0 (p : ℚ) (Nat.cast_ne_zero.mpr hp) ^ e i

/-- Formula for `intPowDiagGL` when `0 < p`. -/
theorem intPowDiagGL_of_pos {p : ℕ} (hp : 0 < p) (e : Fin n → ℤ) :
    intPowDiagGL n p e =
      TauCeti.diagGL fun i ↦ Units.mk0 (p : ℚ) (Nat.cast_ne_zero.mpr hp.ne') ^ e i :=
  dite_eq_right hp.ne'

/-- Matrix coercion of `intPowDiagGL` for `0 < p`. -/
@[simp]
theorem intPowDiagGL_coe {p : ℕ} (hp : 0 < p) (e : Fin n → ℤ) :
    (↑(intPowDiagGL n p e) : Matrix (Fin n) (Fin n) ℚ) =
      Matrix.diagonal fun i ↦ (p : ℚ) ^ e i := by
  rw [intPowDiagGL_of_pos n hp, TauCeti.diagGL_coe]; congr 1; funext i
  rw [Units.val_zpow_eq_zpow_val, Units.val_mk0]

/-- `intPowDiagGL` at the zero exponent vector is `1`. -/
@[simp]
theorem intPowDiagGL_zero (p : ℕ) : intPowDiagGL n p 0 = 1 := by
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · simp [intPowDiagGL]
  · exact Units.ext (by simp [intPowDiagGL_coe n hp])

/-- `intPowDiagGL` converts addition of exponent vectors into matrix multiplication. -/
@[simp]
theorem intPowDiagGL_add (p : ℕ) (e f : Fin n → ℤ) :
    intPowDiagGL n p (e + f) = intPowDiagGL n p e * intPowDiagGL n p f := by
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · simp [intPowDiagGL]
  · exact Units.ext (by
      simp [intPowDiagGL_coe n hp, zpow_add₀ (Nat.cast_ne_zero.mpr hp.ne' : (p : ℚ) ≠ 0)])

/-- `intPowDiagGL` converts negation of exponent vectors into group inversion. -/
@[simp]
theorem intPowDiagGL_neg (p : ℕ) (e : Fin n → ℤ) :
    intPowDiagGL n p (-e) = (intPowDiagGL n p e)⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [← intPowDiagGL_add, neg_add_cancel, intPowDiagGL_zero])

/-- Every `p`-power diagonal matrix `intPowDiagGL n p e` has positive rational determinant. -/
theorem intPowDiagGL_mem_glpos (p : ℕ) (e : Fin n → ℤ) :
    intPowDiagGL n p e ∈ Matrix.GLPos (Fin n) ℚ := by
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · simp [intPowDiagGL]
  · rw [Matrix.mem_glpos, Matrix.GeneralLinearGroup.val_det_apply, intPowDiagGL_coe n hp,
      Matrix.det_diagonal]
    exact Finset.prod_pos fun i _ ↦ zpow_pos (Nat.cast_pos.mpr hp) (e i)

/-- On natural exponents, `intPowDiagGL` agrees with `natDiagGL` of `i ↦ p ^ e i`. -/
theorem intPowDiagGL_natCast (p : ℕ) (e : Fin n → ℕ) :
    intPowDiagGL n p (fun i ↦ (e i : ℤ)) = natDiagGL n (fun i ↦ p ^ e i) := by
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · simp only [intPowDiagGL, ↓reduceDIte]
    by_cases he : ∀ i, e i = 0
    · have hpp : (fun i ↦ (0 : ℕ) ^ e i) = fun _ ↦ 1 := funext fun i ↦ by simp [he i]
      rw [hpp, natDiagGL_one]
    · obtain ⟨i, hi⟩ := not_forall.mp he
      exact (natDiagGL_of_not_pos n fun h ↦ absurd (h i)
        (by simp [Nat.zero_pow (Nat.pos_of_ne_zero hi)])).symm
  · exact Units.ext (by
      simp [intPowDiagGL_coe n hp, natDiagGL_coe n _ (fun i ↦ pow_pos hp (e i))])

/-- At the constant exponent `-1`, `intPowDiagGL` is the inverse of `diag(p, …, p)`. -/
theorem intPowDiagGL_const_neg_one (p : ℕ) :
    intPowDiagGL n p (fun _ ↦ -1) = (natDiagGL n (fun _ ↦ p))⁻¹ := by
  have hneg : (fun _ : Fin n ↦ (-1 : ℤ)) = -(fun _ ↦ ((1 : ℕ) : ℤ)) := funext fun _ ↦ by simp
  rw [hneg, intPowDiagGL_neg, intPowDiagGL_natCast]
  exact congrArg Inv.inv (congrArg (natDiagGL n) (funext fun _ ↦ pow_one p))

/-- Multiplying `intPowDiagGL n p e` by `diag(p ^ k, …, p ^ k)` shifts every exponent by `k`. -/
theorem intPowDiagGL_mul_natDiagGL_const (p : ℕ) (e : Fin n → ℤ) (k : ℕ) :
    intPowDiagGL n p e * natDiagGL n (fun _ ↦ p ^ k) =
      intPowDiagGL n p (fun i ↦ e i + (k : ℤ)) := by
  rw [← intPowDiagGL_natCast n p (fun _ ↦ k), ← intPowDiagGL_add, Pi.add_def]

end IntPowDiag

end HeckeRing.GLn
