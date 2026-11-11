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

## Main results

* `HeckeRing.GLn.natDiagGL_coe`: for positive entries, the underlying matrix is
  `Matrix.diagonal (fun i ↦ (a i : ℚ))`.
* `HeckeRing.GLn.natDiagGL_of_not_pos`: otherwise `natDiagGL` is the identity.
* `HeckeRing.GLn.natDiagGL_mul`, `HeckeRing.GLn.natDiagGL_comm`: multiplicativity in the entries,
  and commutation of any two natural diagonals.
* `HeckeRing.GLn.natDiagGL_const_eq_scalar`, `HeckeRing.GLn.natDiagGL_const_mem_normalizer`: a
  constant natural diagonal is scalar when positive, and normalizes every subgroup unconditionally.
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

lemma natDiagGL_det_pos (a : Fin n → ℕ) (ha : ∀ i, 0 < a i) :
    0 < (↑(natDiagGL n a) : Matrix (Fin n) (Fin n) ℚ).det := by
  rw [natDiagGL_coe n a ha, det_diagonal]
  exact Finset.prod_pos (fun i _ ↦ by positivity [ha i])

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

end HeckeRing.GLn
