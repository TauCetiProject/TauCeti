/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Transpose
public import TauCeti.NumberTheory.HeckeRing.Commutativity
public import TauCeti.NumberTheory.HeckeRing.GLn.Diagonal.Basic
public import TauCeti.NumberTheory.Padics.GeneralLinearGroup.Integral

import TauCeti.Data.Int.Shift
import TauCeti.GroupTheory.Commensurable
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.DoubleCoset
import TauCeti.NumberTheory.Padics.Basic
import TauCeti.NumberTheory.Padics.PadicIntegers
import TauCeti.NumberTheory.Padics.RingHoms
import TauCeti.NumberTheory.Padics.SmithNormalForm

/-!
# Integral and rational `p`-adic `GL_n` Hecke rings

For a prime `p`, let `TauCeti.GLPadicInt (Fin n) p` be the integral subgroup `GL_n(ℤ_p)` inside
`GL_n(ℚ_p)` and let `TauCeti.padicIntEntries (Fin n) p` be the submonoid `M_n(ℤ_p) ∩ GL_n(ℚ_p)`
of invertible `p`-adic matrices with integral `p`-adic entries (both defined in
`TauCeti.NumberTheory.Padics.GeneralLinearGroup.Integral`). Following Rhodes–Shemanske (1998, §3.1)
and [Rhodes–Shemanske][rhodes1999] §2, this file establishes:

1. Using the `p`-adic Smith normal form (`Matrix.exists_padic_smith_normal_form` and
   `Matrix.padic_smith_normal_form_unique`, whereby every nonsingular matrix in `M_n(ℤ_p)` is
   `GL_n(ℤ_p)`-equivalent to `diag(p ^ e₁, …, p ^ eₙ)` for a unique monotone tuple
   `e : Fin n → ℕ`), every matrix in `padicIntEntries (Fin n) p` is `GL_n(ℤ_p)`-equivalent to
   `diag(p ^ e₁, …, p ^ eₙ)` for a unique monotone tuple `e : Fin n → ℕ`, and every matrix in
   `GL_n(ℚ_p)` is `GL_n(ℤ_p)`-equivalent to `diag(p ^ e₁, …, p ^ eₙ)` for a unique monotone tuple
   `e : Fin n → ℤ`.
2. Invariance of `GL_n(ℤ_p)` double cosets under negation (`doubleCoset_neg_GLPadicInt`) and under
   left or right scaling by diagonal `ℤ_pˣ`-matrices (`doubleCoset_diagGL_units_mul_GLPadicInt`,
   `doubleCoset_mul_diagGL_units_GLPadicInt`).
3. Commensurability of `GL_n(ℤ_p)` under all of `GL_n(ℚ_p)` (`commensurator_GLPadicInt_eq_top`),
   yielding the integral and rational `p`-adic Hecke rings `PadicIntegralHeckeRing n p` and
   `PadicRationalHeckeRing n p`, their commutativity via matrix transposition, and their monotone
   exponent double-coset parametrizations (including the rank-`1` bijections with `ℕ` and `ℤ`).

## Main definitions

* `HeckeRing.GLn.padicNatPowDiagGL`, `HeckeRing.GLn.padicIntPowDiagGL`: diagonal `p`-power matrices
  in `GL_n(ℚ_p)` with `ℕ`- and `ℤ`-exponents.
* `HeckeRing.GLn.PadicIntegralHeckeRing`, `HeckeRing.GLn.PadicRationalHeckeRing`: the `ℤ`-Hecke
  rings of `(GL_n(ℤ_p), M_n(ℤ_p) ∩ GL_n(ℚ_p))` and `(GL_n(ℤ_p), GL_n(ℚ_p))`.
* `HeckeRing.GLn.padicNatPowDiagCosetEquiv`, `HeckeRing.GLn.padicIntPowDiagCosetEquiv`: bijections
  between monotone exponent tuples and `p`-adic Hecke double cosets.

## References

* J. A. Rhodes and T. R. Shemanske, *Bruhat–Tits buildings and Hecke operators*, 12 June 1998
  author manuscript, §3.1.
* [J. A. Rhodes and T. R. Shemanske,
  *Rationality theorems for Hecke operators on GL_n*][rhodes1999], §2.
* [G. Shimura, *Introduction to the arithmetic theory of automorphic functions*][shimura1971], §3.2.
-/

public section

open Matrix Subgroup Subgroup.Commensurable DoubleCoset TauCeti
open scoped Pointwise HeckeCosetModule

namespace HeckeRing.GLn

variable (n p : ℕ) [Fact p.Prime]

section DoubleCosetInvariance

/-- Every `GL_n(ℤ_p)` double coset is invariant under negation `g ↦ -g`. -/
@[simp]
theorem doubleCoset_neg_GLPadicInt (g : GL (Fin n) ℚ_[p]) :
    doubleCoset (-g) (GLPadicInt (Fin n) p) (GLPadicInt (Fin n) p) =
      doubleCoset g (GLPadicInt (Fin n) p) (GLPadicInt (Fin n) p) :=
  DoubleCoset.doubleCoset_neg_of_neg_one_mem_left (GLPadicInt.neg_one_mem (Fin n) p) g

private theorem diagGL_units_mem_GLPadicInt (u : Fin n → ℤ_[p]ˣ) :
    TauCeti.diagGL (fun i ↦ Units.map (PadicInt.Coe.ringHom (p := p) : ℤ_[p] →* ℚ_[p]) (u i)) ∈
      GLPadicInt (Fin n) p :=
  TauCeti.map_diagGL (PadicInt.Coe.ringHom (p := p)) u ▸ GLPadicInt.map_mem (TauCeti.diagGL u)

/-- Left multiplication by a diagonal matrix of `ℤ_pˣ`-units preserves `GL_n(ℤ_p)` double cosets. -/
@[simp]
theorem doubleCoset_diagGL_units_mul_GLPadicInt (u : Fin n → ℤ_[p]ˣ) (g : GL (Fin n) ℚ_[p]) :
    doubleCoset
        (TauCeti.diagGL
          (fun i ↦ Units.map (PadicInt.Coe.ringHom (p := p) : ℤ_[p] →* ℚ_[p]) (u i)) * g)
        (GLPadicInt (Fin n) p) (GLPadicInt (Fin n) p) =
      doubleCoset g (GLPadicInt (Fin n) p) (GLPadicInt (Fin n) p) :=
  (DoubleCoset.doubleCoset_eq_of_mem (DoubleCoset.mem_doubleCoset.mpr
    ⟨_, (GLPadicInt (Fin n) p).inv_mem (diagGL_units_mem_GLPadicInt n p u), 1, one_mem _,
      by rw [inv_mul_cancel_left, mul_one]⟩)).symm

/-- Right multiplication by a diagonal matrix of `ℤ_pˣ`-units preserves `GL_n(ℤ_p)` double
cosets. -/
@[simp]
theorem doubleCoset_mul_diagGL_units_GLPadicInt (g : GL (Fin n) ℚ_[p]) (u : Fin n → ℤ_[p]ˣ) :
    doubleCoset
        (g * TauCeti.diagGL
          (fun i ↦ Units.map (PadicInt.Coe.ringHom (p := p) : ℤ_[p] →* ℚ_[p]) (u i)))
        (GLPadicInt (Fin n) p) (GLPadicInt (Fin n) p) =
      doubleCoset g (GLPadicInt (Fin n) p) (GLPadicInt (Fin n) p) :=
  (DoubleCoset.doubleCoset_eq_of_mem (DoubleCoset.mem_doubleCoset.mpr
    ⟨1, one_mem _, _, (GLPadicInt (Fin n) p).inv_mem (diagGL_units_mem_GLPadicInt n p u),
      by rw [one_mul, mul_inv_cancel_right]⟩)).symm

end DoubleCosetInvariance

section PadicDiagonal

/-- The `p`-adic diagonal matrix `diag(p ^ e₁, …, p ^ eₙ) ∈ GL_n(ℚ_p)` for `e : Fin n → ℕ`. -/
noncomputable def padicNatPowDiagGL (e : Fin n → ℕ) : GL (Fin n) ℚ_[p] :=
  castGLPadic (Fin n) p (natDiagGL n fun i ↦ p ^ e i)

/-- Defining equation for `padicNatPowDiagGL`. -/
theorem padicNatPowDiagGL_def (e : Fin n → ℕ) :
    padicNatPowDiagGL n p e = castGLPadic (Fin n) p (natDiagGL n fun i ↦ p ^ e i) := (rfl)

/-- The `p`-adic diagonal matrix `diag(p ^ e₁, …, p ^ eₙ) ∈ GL_n(ℚ_p)` for `e : Fin n → ℤ`. -/
noncomputable def padicIntPowDiagGL (e : Fin n → ℤ) : GL (Fin n) ℚ_[p] :=
  castGLPadic (Fin n) p (intPowDiagGL n p e)

/-- Defining equation for `padicIntPowDiagGL`. -/
theorem padicIntPowDiagGL_def (e : Fin n → ℤ) :
    padicIntPowDiagGL n p e = castGLPadic (Fin n) p (intPowDiagGL n p e) := (rfl)

/-- Matrix coercion of `padicNatPowDiagGL`. -/
@[simp]
theorem padicNatPowDiagGL_coe (e : Fin n → ℕ) :
    (↑(padicNatPowDiagGL n p e) : Matrix (Fin n) (Fin n) ℚ_[p]) =
      Matrix.diagonal fun i ↦ (p : ℚ_[p]) ^ e i := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  rw [padicNatPowDiagGL_def, castGLPadic_coe, natDiagGL_coe n _ fun i ↦ pow_pos hp (e i)]
  ext i j; by_cases hij : i = j <;> simp [hij]

/-- Matrix coercion of `padicIntPowDiagGL`. -/
@[simp]
theorem padicIntPowDiagGL_coe (e : Fin n → ℤ) :
    (↑(padicIntPowDiagGL n p e) : Matrix (Fin n) (Fin n) ℚ_[p]) =
      Matrix.diagonal fun i ↦ (p : ℚ_[p]) ^ e i := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  rw [padicIntPowDiagGL_def, castGLPadic_coe, intPowDiagGL_coe n hp]
  ext i j; by_cases hij : i = j <;> simp [hij]

/-- On natural exponents, `padicIntPowDiagGL` agrees with `padicNatPowDiagGL`. -/
@[simp]
theorem padicIntPowDiagGL_natCast (e : Fin n → ℕ) :
    padicIntPowDiagGL n p (fun i ↦ (e i : ℤ)) = padicNatPowDiagGL n p e := by
  rw [padicIntPowDiagGL_def, intPowDiagGL_natCast, padicNatPowDiagGL_def]

/-- `padicNatPowDiagGL` at `0` is `1`. -/
@[simp]
theorem padicNatPowDiagGL_zero : padicNatPowDiagGL n p 0 = 1 := by
  rw [padicNatPowDiagGL_def, show (fun i : Fin n ↦ p ^ (0 : Fin n → ℕ) i) = fun _ ↦ 1 from
    funext fun _ ↦ pow_zero p, natDiagGL_one, map_one]

/-- `padicIntPowDiagGL` at `0` is `1`. -/
@[simp]
theorem padicIntPowDiagGL_zero : padicIntPowDiagGL n p 0 = 1 := by
  rw [padicIntPowDiagGL_def, intPowDiagGL_zero, map_one]

/-- `padicIntPowDiagGL` converts addition of exponent tuples into matrix multiplication. -/
@[simp]
theorem padicIntPowDiagGL_add (e f : Fin n → ℤ) :
    padicIntPowDiagGL n p (e + f) = padicIntPowDiagGL n p e * padicIntPowDiagGL n p f := by
  simp only [padicIntPowDiagGL_def, intPowDiagGL_add, map_mul]

/-- `padicNatPowDiagGL` converts addition of exponent tuples into matrix multiplication. -/
@[simp]
theorem padicNatPowDiagGL_add (e f : Fin n → ℕ) :
    padicNatPowDiagGL n p (e + f) = padicNatPowDiagGL n p e * padicNatPowDiagGL n p f := by
  rw [← padicIntPowDiagGL_natCast, ← padicIntPowDiagGL_natCast, ← padicIntPowDiagGL_natCast,
    ← padicIntPowDiagGL_add]
  exact congrArg (padicIntPowDiagGL n p) (funext fun i ↦ Nat.cast_add (e i) (f i))

/-- `padicIntPowDiagGL` converts negation of exponent tuples into group inversion. -/
@[simp]
theorem padicIntPowDiagGL_neg (e : Fin n → ℤ) :
    padicIntPowDiagGL n p (-e) = (padicIntPowDiagGL n p e)⁻¹ := by
  simp only [padicIntPowDiagGL_def, intPowDiagGL_neg, map_inv]

/-- Negative constant exponent tuple `fun _ ↦ -(k : ℤ)` gives the inverse of
`padicNatPowDiagGL n p (fun _ ↦ k)`. -/
theorem padicIntPowDiagGL_const_neg (k : ℕ) :
    padicIntPowDiagGL n p (fun _ ↦ -(k : ℤ)) = (padicNatPowDiagGL n p (fun _ ↦ k))⁻¹ := by
  rw [← Pi.neg_def, padicIntPowDiagGL_neg, padicIntPowDiagGL_natCast]

/-- Scalar `p`-adic diagonal matrices `padicIntPowDiagGL n p (fun _ ↦ k)` are central in
`GL_n(ℚ_p)`. -/
theorem padicIntPowDiagGL_const_comm (k : ℤ) (g : GL (Fin n) ℚ_[p]) :
    padicIntPowDiagGL n p (fun _ ↦ k) * g = g * padicIntPowDiagGL n p (fun _ ↦ k) :=
  Units.ext (by ext i j; simp [padicIntPowDiagGL_coe, Matrix.diagonal_mul, Matrix.mul_diagonal,
    mul_comm])

/-- Scalar `p`-adic diagonal matrices `padicNatPowDiagGL n p (fun _ ↦ k)` are central in
`GL_n(ℚ_p)`. -/
theorem padicNatPowDiagGL_const_comm (k : ℕ) (g : GL (Fin n) ℚ_[p]) :
    padicNatPowDiagGL n p (fun _ ↦ k) * g = g * padicNatPowDiagGL n p (fun _ ↦ k) := by
  rw [← padicIntPowDiagGL_natCast]; exact padicIntPowDiagGL_const_comm n p k g

/-- Every central `p`-power diagonal matrix `padicIntPowDiagGL n p (fun _ ↦ k)` normalizes
`GL_n(ℤ_p)`. -/
theorem padicIntPowDiagGL_const_mem_normalizer (k : ℤ) :
    padicIntPowDiagGL n p (fun _ ↦ k) ∈
      Subgroup.normalizer (GLPadicInt (Fin n) p : Set (GL (Fin n) ℚ_[p])) :=
  Subgroup.mem_normalizer_iff.mpr fun h ↦ by
    rw [padicIntPowDiagGL_const_comm n p k h, mul_inv_cancel_right]

/-- Every `padicNatPowDiagGL n p e` has `ℤ_p`-entries. -/
theorem padicNatPowDiagGL_mem_padicIntEntries (e : Fin n → ℕ) :
    padicNatPowDiagGL n p e ∈ padicIntEntries (Fin n) p :=
  (mem_padicIntEntries_iff (Fin n) p).mpr ⟨Matrix.diagonal fun i ↦ (p : ℤ_[p]) ^ e i, by
    rw [padicNatPowDiagGL_coe]; ext i j; by_cases hij : i = j <;> simp [hij]⟩

/-- The underlying `ℤ_p`-matrix of `padicNatPowDiagGL n p e` is `diag(p ^ e₁, …, p ^ eₙ)`. -/
@[simp]
theorem padicIntMatrix_padicNatPowDiagGL (e : Fin n → ℕ) :
    padicIntMatrix (Fin n) p
        ⟨padicNatPowDiagGL n p e, padicNatPowDiagGL_mem_padicIntEntries n p e⟩ =
      Matrix.diagonal fun i ↦ (p : ℤ_[p]) ^ e i := by
  rw [padicIntMatrix_eq_iff, padicNatPowDiagGL_coe]
  ext i j; by_cases hij : i = j <;> simp [hij]

/-- Entrywise coercion of `diag(p ^ e₁, …, p ^ eₙ)` from `M_n(ℤ_p)` to `M_n(ℚ_p)` is the matrix of
`padicNatPowDiagGL n p e`. -/
theorem map_diagonal_padicInt_pow (e : Fin n → ℕ) :
    (Matrix.diagonal fun i ↦ (p : ℤ_[p]) ^ e i).map (PadicInt.Coe.ringHom (p := p)) =
      (↑(padicNatPowDiagGL n p e) : Matrix (Fin n) (Fin n) ℚ_[p]) := by
  rw [← padicIntMatrix_padicNatPowDiagGL n p e, map_padicIntMatrix]

end PadicDiagonal

section PadicDoubleCosets

/-- Every `g ∈ padicIntEntries (Fin n) p` lies in the `GL_n(ℤ_p)` double coset of
`padicNatPowDiagGL n p e` for a monotone tuple `e : Fin n → ℕ`. -/
theorem exists_padicNatPowDiagGL_mem_doubleCoset {g : GL (Fin n) ℚ_[p]}
    (hg : g ∈ padicIntEntries (Fin n) p) :
    ∃ e : Fin n → ℕ, Monotone e ∧
      g ∈ doubleCoset (padicNatPowDiagGL n p e)
        (GLPadicInt (Fin n) p) (GLPadicInt (Fin n) p) := by
  obtain ⟨U₁, U₂, e, he, hU⟩ := Matrix.exists_padic_smith_normal_form n p
    (padicIntMatrix (Fin n) p ⟨g, hg⟩) (det_padicIntMatrix_ne_zero (Fin n) p ⟨g, hg⟩)
  refine ⟨e, he, DoubleCoset.mem_doubleCoset.mpr
    ⟨GeneralLinearGroup.map (PadicInt.Coe.ringHom (p := p)) U₁⁻¹, GLPadicInt.map_mem _,
     GeneralLinearGroup.map (PadicInt.Coe.ringHom (p := p)) U₂⁻¹, GLPadicInt.map_mem _, ?_⟩⟩
  have hmap := congrArg (Matrix.map · (PadicInt.Coe.ringHom (p := p))) hU
  simp only [Matrix.map_mul, map_padicIntMatrix, map_diagonal_padicInt_pow] at hmap
  have hgl : GeneralLinearGroup.map (PadicInt.Coe.ringHom (p := p)) U₁ * g *
      GeneralLinearGroup.map (PadicInt.Coe.ringHom (p := p)) U₂ = padicNatPowDiagGL n p e :=
    Units.ext (by simpa only [Units.val_mul, GLPadicInt.map_coe] using hmap)
  rw [← hgl]; simp [mul_assoc]

/-- Distinct monotone tuples `e₁, e₂ : Fin n → ℕ` define disjoint `GL_n(ℤ_p)` double cosets. -/
theorem eq_of_padicNatPowDiagGL_mem_doubleCoset {e₁ e₂ : Fin n → ℕ}
    (he₁ : Monotone e₁) (he₂ : Monotone e₂)
    (h : padicNatPowDiagGL n p e₂ ∈
      doubleCoset (padicNatPowDiagGL n p e₁) (GLPadicInt (Fin n) p) (GLPadicInt (Fin n) p)) :
    e₁ = e₂ := by
  obtain ⟨u₁, hu₁, u₂, hu₂, hu⟩ := DoubleCoset.mem_doubleCoset.mp h
  obtain ⟨U₁, rfl⟩ := GLPadicInt.mem_iff_exists_map.mp hu₁
  obtain ⟨U₂, rfl⟩ := GLPadicInt.mem_iff_exists_map.mp hu₂
  apply Matrix.padic_smith_normal_form_unique n p he₁ he₂ U₁ U₂
  apply Matrix.map_injective (f := PadicInt.Coe.ringHom (p := p)) Subtype.val_injective
  simpa only [Matrix.map_mul, map_diagonal_padicInt_pow, Units.val_mul, GLPadicInt.map_coe] using
    congrArg Units.val hu.symm

/-- **Clearing denominators in `GL_n(ℚ_p)`**: for every `g ∈ GL_n(ℚ_p)` there exists `k : ℕ` such
that `padicNatPowDiagGL n p (fun _ ↦ k) * g` has `ℤ_p`-entries. -/
theorem exists_padicNatPowDiagGL_const_mul_mem_padicIntEntries (g : GL (Fin n) ℚ_[p]) :
    ∃ k : ℕ, padicNatPowDiagGL n p (fun _ ↦ k) * g ∈ padicIntEntries (Fin n) p := by
  let M : ℕ := Finset.univ.sup fun ij : Fin n × Fin n ↦
    (-((↑g : Matrix (Fin n) (Fin n) ℚ_[p]) ij.1 ij.2).valuation).toNat
  refine ⟨M, (mem_padicIntEntries_iff_norm_le_one (Fin n) p).mpr fun i j ↦ ?_⟩
  rw [Units.val_mul, padicNatPowDiagGL_coe, Matrix.diagonal_mul]
  set x := (↑g : Matrix (Fin n) (Fin n) ℚ_[p]) i j
  by_cases hx : x = 0
  · simp [hx]
  · rw [Padic.norm_le_one_iff_val_nonneg, ← zpow_natCast (p : ℚ_[p]) M,
      Padic.valuation_p_zpow_mul _ hx]
    have hle : (-x.valuation).toNat ≤ M := Finset.le_sup (f := fun ij : Fin n × Fin n ↦
      (-((↑g : Matrix (Fin n) (Fin n) ℚ_[p]) ij.1 ij.2).valuation).toNat) (Finset.mem_univ (i, j))
    omega

/-- Every `g ∈ GL_n(ℚ_p)` lies in the `GL_n(ℤ_p)` double coset of `padicIntPowDiagGL n p e` for a
monotone tuple `e : Fin n → ℤ`. -/
theorem exists_padicIntPowDiagGL_mem_doubleCoset (g : GL (Fin n) ℚ_[p]) :
    ∃ e : Fin n → ℤ, Monotone e ∧
      g ∈ doubleCoset (padicIntPowDiagGL n p e) (GLPadicInt (Fin n) p) (GLPadicInt (Fin n) p) := by
  obtain ⟨k, hk⟩ := exists_padicNatPowDiagGL_const_mul_mem_padicIntEntries n p g
  obtain ⟨e', he', hcos⟩ := exists_padicNatPowDiagGL_mem_doubleCoset n p hk
  obtain ⟨u₁, hu₁, u₂, hu₂, hmul⟩ := DoubleCoset.mem_doubleCoset.mp hcos
  refine ⟨fun i ↦ (e' i : ℤ) - k, fun i j hij ↦ sub_le_sub_right (Nat.cast_le.mpr (he' hij)) _,
    DoubleCoset.mem_doubleCoset.mpr ⟨u₁, hu₁, u₂, hu₂, ?_⟩⟩
  have hsub : (fun i : Fin n ↦ (e' i : ℤ) - k) = (fun _ ↦ -(k : ℤ)) + fun i ↦ (e' i : ℤ) :=
    funext fun i ↦ sub_eq_neg_add _ _
  rw [hsub, padicIntPowDiagGL_add, padicIntPowDiagGL_const_neg, padicIntPowDiagGL_natCast]
  apply mul_left_cancel (a := padicNatPowDiagGL n p (fun _ ↦ k))
  rw [hmul, ← mul_assoc, ← mul_assoc, padicNatPowDiagGL_const_comm n p k u₁]
  simp only [mul_assoc, mul_inv_cancel_left]

/-- Distinct monotone tuples `e₁, e₂ : Fin n → ℤ` define disjoint `GL_n(ℤ_p)` double cosets. -/
theorem eq_of_padicIntPowDiagGL_mem_doubleCoset {e₁ e₂ : Fin n → ℤ}
    (he₁ : Monotone e₁) (he₂ : Monotone e₂)
    (h : padicIntPowDiagGL n p e₂ ∈
      doubleCoset (padicIntPowDiagGL n p e₁) (GLPadicInt (Fin n) p) (GLPadicInt (Fin n) p)) :
    e₁ = e₂ := by
  obtain ⟨M, f, hf⟩ := TauCeti.exists_natCast_eq_add_natCast (Sum.elim e₁ e₂)
  let f₁ : Fin n → ℕ := f ∘ Sum.inl
  let f₂ : Fin n → ℕ := f ∘ Sum.inr
  have hf₁ : ∀ i, (f₁ i : ℤ) = e₁ i + M := fun i ↦ hf (Sum.inl i)
  have hf₂ : ∀ i, (f₂ i : ℤ) = e₂ i + M := fun i ↦ hf (Sum.inr i)
  obtain ⟨u₁, hu₁, u₂, hu₂, hmul⟩ := DoubleCoset.mem_doubleCoset.mp h
  have hshift : padicNatPowDiagGL n p f₂ ∈
      doubleCoset (padicNatPowDiagGL n p f₁) (GLPadicInt (Fin n) p) (GLPadicInt (Fin n) p) := by
    refine DoubleCoset.mem_doubleCoset.mpr ⟨u₁, hu₁, u₂, hu₂, ?_⟩
    rw [← padicIntPowDiagGL_natCast, ← padicIntPowDiagGL_natCast,
      show (fun i ↦ (f₂ i : ℤ)) = (fun _ ↦ (M : ℤ)) + e₂ from
        funext fun i ↦ by rw [hf₂, Pi.add_apply, add_comm],
      show (fun i ↦ (f₁ i : ℤ)) = (fun _ ↦ (M : ℤ)) + e₁ from
        funext fun i ↦ by rw [hf₁, Pi.add_apply, add_comm],
      padicIntPowDiagGL_add, padicIntPowDiagGL_add, hmul]
    simp only [← mul_assoc, padicIntPowDiagGL_const_comm n p M u₁]
  have hfeq := eq_of_padicNatPowDiagGL_mem_doubleCoset n p
    (fun i j hij ↦ by rw [← Int.ofNat_le, hf₁, hf₁]; linarith [he₁ hij])
    (fun i j hij ↦ by rw [← Int.ofNat_le, hf₂, hf₂]; linarith [he₂ hij]) hshift
  funext i; have := congrArg (fun g : Fin n → ℕ ↦ (g i : ℤ)) hfeq; linarith [hf₁ i, hf₂ i]

end PadicDoubleCosets

section Commensurator

/-- Conjugating an element of the congruence kernel `ker(GL_n(ℤ_p) → GL_n(ℤ/p^M ℤ))` by
`padicIntPowDiagGL n p e` stays in `padicIntEntries (Fin n) p` once `M` bounds all `|e i - e j|`.
-/
private theorem conj_padicIntPowDiagGL_mem_padicIntEntries {e : Fin n → ℤ} {M : ℕ}
    (hM : ∀ i j, e j - e i ≤ M) (u : GL (Fin n) ℤ_[p])
    (hu : u ∈ (Matrix.GeneralLinearGroup.map (PadicInt.toZModPow (p := p) M)).ker) :
    (padicIntPowDiagGL n p e)⁻¹ *
        GeneralLinearGroup.map (PadicInt.Coe.ringHom (p := p)) u * padicIntPowDiagGL n p e ∈
      padicIntEntries (Fin n) p := by
  rw [mem_padicIntEntries_iff_norm_le_one]
  intro i j
  have hval : (↑((padicIntPowDiagGL n p e)⁻¹ *
        GeneralLinearGroup.map (PadicInt.Coe.ringHom (p := p)) u * padicIntPowDiagGL n p e) :
      Matrix (Fin n) (Fin n) ℚ_[p]) i j =
      (p : ℚ_[p]) ^ (-e i) * ((↑u : Matrix (Fin n) (Fin n) ℤ_[p]) i j : ℚ_[p]) *
        (p : ℚ_[p]) ^ e j := by
    simp only [← padicIntPowDiagGL_neg, Units.val_mul, padicIntPowDiagGL_coe, GLPadicInt.map_coe,
      Pi.neg_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.map_apply,
      PadicInt.Coe.ringHom_apply]
  rw [hval]
  by_cases hij : i = j
  · subst hij
    rw [mul_right_comm, ← zpow_add₀ (NeZero.ne (p : ℚ_[p])), neg_add_cancel, zpow_zero, one_mul]
    exact ((↑u : Matrix (Fin n) (Fin n) ℤ_[p]) i i).property
  · have hker : PadicInt.toZModPow M ((↑u : Matrix (Fin n) (Fin n) ℤ_[p]) i j) = 0 := by
      have h1 := congrArg (fun x : GL (Fin n) (ZMod (p ^ M)) ↦
        (↑x : Matrix (Fin n) (Fin n) (ZMod (p ^ M))) i j) (MonoidHom.mem_ker.mp hu)
      simpa [Matrix.one_apply, hij] using h1
    obtain ⟨c, hc⟩ := (PadicInt.toZModPow_eq_zero_iff_dvd M _).mp hker
    have hcast : ((↑u : Matrix (Fin n) (Fin n) ℤ_[p]) i j : ℚ_[p]) =
        (p : ℚ_[p]) ^ (M : ℤ) * (c : ℚ_[p]) := by rw [hc, zpow_natCast]; push_cast; rfl
    rw [hcast, ← mul_assoc, mul_right_comm _ (c : ℚ_[p]),
      ← zpow_add₀ (NeZero.ne (p : ℚ_[p])), ← zpow_add₀ (NeZero.ne (p : ℚ_[p]))]
    let E : ℕ := (-e i + (M : ℤ) + e j).toNat
    have hE : -e i + (M : ℤ) + e j = (E : ℤ) :=
      (Int.toNat_of_nonneg (by have := hM j i; omega)).symm
    rw [hE, show (p : ℚ_[p]) ^ (E : ℤ) * (c : ℚ_[p]) = (((p : ℤ_[p]) ^ E * c : ℤ_[p]) : ℚ_[p])
      by rw [zpow_natCast]; push_cast; rfl]
    exact ((p : ℤ_[p]) ^ E * c).property

private theorem congruence_ker_le_conj_padicIntPowDiagGL {e : Fin n → ℤ} {M : ℕ}
    (hM : ∀ i j, e j - e i ≤ M) :
    (Matrix.GeneralLinearGroup.map (PadicInt.toZModPow (p := p) M) :
      GL (Fin n) ℤ_[p] →* GL (Fin n) (ZMod (p ^ M))).ker.map
        (GeneralLinearGroup.map (PadicInt.Coe.ringHom (p := p))) ≤
      MulAut.conj (padicIntPowDiagGL n p e) • GLPadicInt (Fin n) p := by
  set φ : GL (Fin n) ℤ_[p] →* GL (Fin n) (ZMod (p ^ M)) :=
    Matrix.GeneralLinearGroup.map (PadicInt.toZModPow (p := p) M)
  set g := padicIntPowDiagGL n p e
  rintro x ⟨u, hu, rfl⟩
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, MulAut.smul_def, MulAut.conj_inv_apply,
    GLPadicInt.mem_iff_mem_padicIntEntries_and_inv]
  refine ⟨conj_padicIntPowDiagGL_mem_padicIntEntries n p hM u hu, ?_⟩
  have hinv : (g⁻¹ * GeneralLinearGroup.map (PadicInt.Coe.ringHom (p := p)) u * g)⁻¹ =
      g⁻¹ * GeneralLinearGroup.map (PadicInt.Coe.ringHom (p := p)) u⁻¹ * g := by
    rw [_root_.mul_inv_rev, _root_.mul_inv_rev, inv_inv, ← map_inv, mul_assoc]
  rw [hinv]
  exact conj_padicIntPowDiagGL_mem_padicIntEntries n p hM u⁻¹ (φ.ker.inv_mem hu)

/-- Every `padicIntPowDiagGL n p e` belongs to the commensurator of `GL_n(ℤ_p)`. -/
theorem padicIntPowDiagGL_mem_commensurator_GLPadicInt (e : Fin n → ℤ) :
    padicIntPowDiagGL n p e ∈ commensurator (GLPadicInt (Fin n) p) := by
  rw [commensurator_mem_iff]
  set H := GLPadicInt (Fin n) p
  let M : ℕ := 2 * Finset.univ.sup fun i ↦ (e i).natAbs
  have hM : ∀ i j, e j - e i ≤ M := fun i j ↦ by
    have hi := Finset.le_sup (f := fun k : Fin n ↦ (e k).natAbs) (Finset.mem_univ i)
    have hj := Finset.le_sup (f := fun k : Fin n ↦ (e k).natAbs) (Finset.mem_univ j)
    omega
  have : NeZero (p ^ M) := NeZero.pow
  set φ : GL (Fin n) ℤ_[p] →* GL (Fin n) (ZMod (p ^ M)) :=
    Matrix.GeneralLinearGroup.map (PadicInt.toZModPow (p := p) M)
  set K := φ.ker.map (GeneralLinearGroup.map (PadicInt.Coe.ringHom (p := p)))
  have hK_rel : K.relIndex H ≠ 0 := by
    have hH : H = Subgroup.map (GeneralLinearGroup.map (PadicInt.Coe.ringHom (p := p))) ⊤ := by
      rw [← MonoidHom.range_eq_map]; exact GLPadicInt.eq_range (Fin n) p
    rw [hH, Subgroup.relIndex_map_map_of_injective _ _ (GLPadicInt.map_injective (Fin n) p),
      Subgroup.relIndex_top_right]
    exact (Subgroup.finiteIndex_ker φ).index_ne_zero
  set g := padicIntPowDiagGL n p e
  have hK_le_gH : K ≤ MulAut.conj g • H := congruence_ker_le_conj_padicIntPowDiagGL n p hM
  have hK_le_ginvH : K ≤ MulAut.conj g⁻¹ • H := by
    rw [show g⁻¹ = padicIntPowDiagGL n p (-e) from (padicIntPowDiagGL_neg n p e).symm]
    exact congruence_ker_le_conj_padicIntPowDiagGL n p fun i j ↦ by
      simpa [sub_eq_add_neg, add_comm] using hM j i
  have hHg : H.relIndex (MulAut.conj g • H) ≠ 0 := by
    rw [(Subgroup.relIndex_pointwise_smul (MulAut.conj g⁻¹) H (MulAut.conj g • H)).symm,
      smul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul]
    exact ne_zero_of_dvd_ne_zero hK_rel (Subgroup.relIndex_dvd_of_le_left H hK_le_ginvH)
  exact ⟨Subgroup.isFiniteRelIndex_iff_relIndex_ne_zero.mpr
      (ne_zero_of_dvd_ne_zero hK_rel (Subgroup.relIndex_dvd_of_le_left H hK_le_gH)),
    Subgroup.isFiniteRelIndex_iff_relIndex_ne_zero.mpr hHg⟩

/-- **The commensurator of `GL_n(ℤ_p)` in `GL_n(ℚ_p)` is the whole group `GL_n(ℚ_p)`.** -/
theorem commensurator_GLPadicInt_eq_top : commensurator (GLPadicInt (Fin n) p) = ⊤ := by
  rw [Subgroup.eq_top_iff']
  intro g
  obtain ⟨e, -, hcos⟩ := exists_padicIntPowDiagGL_mem_doubleCoset n p g
  obtain ⟨u₁, hu₁, u₂, hu₂, rfl⟩ := DoubleCoset.mem_doubleCoset.mp hcos
  exact (commensurator (GLPadicInt (Fin n) p)).mul_mem
    ((commensurator (GLPadicInt (Fin n) p)).mul_mem
      (Subgroup.Commensurable.le_commensurator (GLPadicInt (Fin n) p) hu₁)
      (padicIntPowDiagGL_mem_commensurator_GLPadicInt n p e))
    (Subgroup.Commensurable.le_commensurator (GLPadicInt (Fin n) p) hu₂)

/-- The integral `p`-adic Hecke triple `(M_n(ℤ_p) ∩ GL_n(ℚ_p), GL_n(ℤ_p))`. -/
instance instIsHeckeTriplePadicIntEntries :
    IsHeckeTriple (padicIntEntries (Fin n) p) (GLPadicInt (Fin n) p) (GLPadicInt (Fin n) p) :=
  IsHeckeTriple.of_diagonal (GLPadicInt.le_padicIntEntries (Fin n) p)
    (fun _ _ ↦ by rw [Subgroup.mem_toSubmonoid, commensurator_GLPadicInt_eq_top]; trivial)

/-- The rational `p`-adic Hecke triple `(GL_n(ℚ_p), GL_n(ℤ_p))`. -/
instance instIsHeckeTriplePadicTop :
    IsHeckeTriple (⊤ : Submonoid (GL (Fin n) ℚ_[p]))
      (GLPadicInt (Fin n) p) (GLPadicInt (Fin n) p) :=
  IsHeckeTriple.of_diagonal le_top
    (fun _ _ ↦ by rw [Subgroup.mem_toSubmonoid, commensurator_GLPadicInt_eq_top]; trivial)

end Commensurator

section HeckeRingsAndCosets

/-- **The integral `p`-adic Hecke ring** of `(GL_n(ℤ_p), M_n(ℤ_p) ∩ GL_n(ℚ_p))` over `ℤ`. -/
abbrev PadicIntegralHeckeRing : Type :=
  𝕋 (padicIntEntries (Fin n) p) (GLPadicInt (Fin n) p) ℤ

/-- **The rational (spherical) `p`-adic Hecke ring** of `(GL_n(ℤ_p), GL_n(ℚ_p))` over `ℤ`. -/
abbrev PadicRationalHeckeRing : Type :=
  𝕋 (⊤ : Submonoid (GL (Fin n) ℚ_[p])) (GLPadicInt (Fin n) p) ℤ

/-- The `GL_n(ℤ_p)` double coset of `padicNatPowDiagGL n p e` in `padicIntEntries (Fin n) p`. -/
noncomputable def padicNatPowDiagCoset (e : Fin n → ℕ) :
    HeckeCoset (padicIntEntries (Fin n) p) (GLPadicInt (Fin n) p) (GLPadicInt (Fin n) p) :=
  HeckeCoset.mk (GLPadicInt (Fin n) p) (GLPadicInt (Fin n) p)
    ⟨padicNatPowDiagGL n p e, padicNatPowDiagGL_mem_padicIntEntries n p e⟩

/-- Defining equation for `padicNatPowDiagCoset`. -/
theorem padicNatPowDiagCoset_def (e : Fin n → ℕ) :
    padicNatPowDiagCoset n p e =
      HeckeCoset.mk (GLPadicInt (Fin n) p) (GLPadicInt (Fin n) p)
        ⟨padicNatPowDiagGL n p e, padicNatPowDiagGL_mem_padicIntEntries n p e⟩ := (rfl)

/-- At `0`, `padicNatPowDiagCoset` is the identity coset `1`. -/
@[simp]
theorem padicNatPowDiagCoset_zero : padicNatPowDiagCoset n p 0 = 1 := by
  rw [padicNatPowDiagCoset_def, HeckeCoset.one_def]
  exact HeckeCoset.mk_congr_val (padicNatPowDiagGL_zero n p)

/-- The basis element `[GL_n(ℤ_p) · diag(p ^ e) · GL_n(ℤ_p)]` in `PadicIntegralHeckeRing n p`. -/
noncomputable def padicNatPowDiagElem (e : Fin n → ℕ) : PadicIntegralHeckeRing n p :=
  HeckeCosetModule.single ℤ (padicNatPowDiagCoset n p e) 1

/-- Defining equation for `padicNatPowDiagElem`. -/
theorem padicNatPowDiagElem_def (e : Fin n → ℕ) :
    padicNatPowDiagElem n p e = HeckeCosetModule.single ℤ (padicNatPowDiagCoset n p e) 1 := (rfl)

/-- At `0`, `padicNatPowDiagElem` is `1`. -/
@[simp]
theorem padicNatPowDiagElem_zero : padicNatPowDiagElem n p 0 = 1 := by
  rw [padicNatPowDiagElem_def, padicNatPowDiagCoset_zero, HeckeCosetModule.one_def]

/-- Bijection between monotone tuples `e : Fin n → ℕ` and double cosets of
`(padicIntEntries (Fin n) p, GLPadicInt (Fin n) p)`. -/
noncomputable def padicNatPowDiagCosetEquiv :
    {e : Fin n → ℕ // Monotone e} ≃
      HeckeCoset (padicIntEntries (Fin n) p) (GLPadicInt (Fin n) p) (GLPadicInt (Fin n) p) :=
  Equiv.ofBijective (fun e ↦ padicNatPowDiagCoset n p e.val) ⟨by
    rintro ⟨e₁, he₁⟩ ⟨e₂, he₂⟩ h
    have hset := congrArg HeckeCoset.toSet h
    simp only [padicNatPowDiagCoset_def, HeckeCoset.toSet_mk] at hset
    exact Subtype.ext (eq_of_padicNatPowDiagGL_mem_doubleCoset n p he₂ he₁
      (hset ▸ DoubleCoset.mem_doubleCoset_self _ _ _)).symm,
    fun D ↦ by
      obtain ⟨e, he, hmem⟩ := exists_padicNatPowDiagGL_mem_doubleCoset n p D.rep.property
      exact ⟨⟨e, he⟩, ((HeckeCoset.mk_eq_mk_of_mem hmem).symm).trans (HeckeCoset.mk_rep D)⟩⟩

/-- `padicNatPowDiagCosetEquiv` sends a monotone tuple `e` to `padicNatPowDiagCoset n p e`. -/
@[simp]
theorem padicNatPowDiagCosetEquiv_apply (e : {e : Fin n → ℕ // Monotone e}) :
    padicNatPowDiagCosetEquiv n p e = padicNatPowDiagCoset n p e.val := (rfl)

/-- The `GL_n(ℤ_p)` double coset of `padicIntPowDiagGL n p e` in `GL_n(ℚ_p)`. -/
noncomputable def padicIntPowDiagCoset (e : Fin n → ℤ) :
    HeckeCoset (⊤ : Submonoid (GL (Fin n) ℚ_[p])) (GLPadicInt (Fin n) p) (GLPadicInt (Fin n) p) :=
  HeckeCoset.mk (GLPadicInt (Fin n) p) (GLPadicInt (Fin n) p) ⟨padicIntPowDiagGL n p e, trivial⟩

/-- Defining equation for `padicIntPowDiagCoset`. -/
theorem padicIntPowDiagCoset_def (e : Fin n → ℤ) :
    padicIntPowDiagCoset n p e =
      HeckeCoset.mk (GLPadicInt (Fin n) p) (GLPadicInt (Fin n) p)
        ⟨padicIntPowDiagGL n p e, trivial⟩ := (rfl)

/-- At `0`, `padicIntPowDiagCoset` is the identity coset `1`. -/
@[simp]
theorem padicIntPowDiagCoset_zero : padicIntPowDiagCoset n p 0 = 1 := by
  rw [padicIntPowDiagCoset_def, HeckeCoset.one_def]
  exact HeckeCoset.mk_congr_val (padicIntPowDiagGL_zero n p)

/-- The basis element `[GL_n(ℤ_p) · diag(p ^ e) · GL_n(ℤ_p)]` in `PadicRationalHeckeRing n p`. -/
noncomputable def padicIntPowDiagElem (e : Fin n → ℤ) : PadicRationalHeckeRing n p :=
  HeckeCosetModule.single ℤ (padicIntPowDiagCoset n p e) 1

/-- Defining equation for `padicIntPowDiagElem`. -/
theorem padicIntPowDiagElem_def (e : Fin n → ℤ) :
    padicIntPowDiagElem n p e = HeckeCosetModule.single ℤ (padicIntPowDiagCoset n p e) 1 := (rfl)

/-- At `0`, `padicIntPowDiagElem` is `1`. -/
@[simp]
theorem padicIntPowDiagElem_zero : padicIntPowDiagElem n p 0 = 1 := by
  rw [padicIntPowDiagElem_def, padicIntPowDiagCoset_zero, HeckeCosetModule.one_def]

/-- Bijection between monotone tuples `e : Fin n → ℤ` and double cosets of
`(⊤, GLPadicInt (Fin n) p)` in `GL_n(ℚ_p)`. -/
noncomputable def padicIntPowDiagCosetEquiv :
    {e : Fin n → ℤ // Monotone e} ≃
      HeckeCoset (⊤ : Submonoid (GL (Fin n) ℚ_[p]))
        (GLPadicInt (Fin n) p) (GLPadicInt (Fin n) p) :=
  Equiv.ofBijective (fun e ↦ padicIntPowDiagCoset n p e.val) ⟨by
    rintro ⟨e₁, he₁⟩ ⟨e₂, he₂⟩ h
    have hset := congrArg HeckeCoset.toSet h
    simp only [padicIntPowDiagCoset_def, HeckeCoset.toSet_mk] at hset
    exact Subtype.ext (eq_of_padicIntPowDiagGL_mem_doubleCoset n p he₂ he₁
      (hset ▸ DoubleCoset.mem_doubleCoset_self _ _ _)).symm,
    fun D ↦ by
      obtain ⟨e, he, hmem⟩ :=
        exists_padicIntPowDiagGL_mem_doubleCoset n p (D.rep : GL (Fin n) ℚ_[p])
      exact ⟨⟨e, he⟩, ((HeckeCoset.mk_eq_mk_of_mem hmem).symm).trans (HeckeCoset.mk_rep D)⟩⟩

/-- `padicIntPowDiagCosetEquiv` sends a monotone tuple `e` to `padicIntPowDiagCoset n p e`. -/
@[simp]
theorem padicIntPowDiagCosetEquiv_apply (e : {e : Fin n → ℤ // Monotone e}) :
    padicIntPowDiagCosetEquiv n p e = padicIntPowDiagCoset n p e.val := (rfl)

/-- **Rank-`1` integral `p`-adic cosets**: in rank `n = 1`, the double cosets of
`(M_1(ℤ_p) ∩ GL_1(ℚ_p), GL_1(ℤ_p))` biject canonically with `ℕ` via
`k ↦ [GL_1(ℤ_p) · p ^ k · GL_1(ℤ_p)]`. -/
noncomputable def padicIntegralCosetEquivNat :
    ℕ ≃ HeckeCoset (padicIntEntries (Fin 1) p) (GLPadicInt (Fin 1) p) (GLPadicInt (Fin 1) p) :=
  (Equiv.mk (fun k : ℕ ↦ (⟨fun _ ↦ k, monotone_const⟩ : {e : Fin 1 → ℕ // Monotone e}))
    (fun e ↦ e.val 0) (fun _ ↦ rfl)
    (fun e ↦ Subtype.ext (funext fun i ↦ congrArg e.val (Subsingleton.elim 0 i)))).trans
    (padicNatPowDiagCosetEquiv 1 p)

/-- `padicIntegralCosetEquivNat` sends `k : ℕ` to `padicNatPowDiagCoset 1 p (fun _ ↦ k)`. -/
@[simp]
theorem padicIntegralCosetEquivNat_apply (k : ℕ) :
    padicIntegralCosetEquivNat p k = padicNatPowDiagCoset 1 p (fun _ ↦ k) := (rfl)

/-- **Rank-`1` rational `p`-adic cosets**: in rank `n = 1`, the double cosets of
`(GL_1(ℚ_p), GL_1(ℤ_p))` biject canonically with `ℤ` via `k ↦ [GL_1(ℤ_p) · p ^ k · GL_1(ℤ_p)]`. -/
noncomputable def padicRationalCosetEquivInt :
    ℤ ≃ HeckeCoset (⊤ : Submonoid (GL (Fin 1) ℚ_[p]))
      (GLPadicInt (Fin 1) p) (GLPadicInt (Fin 1) p) :=
  (Equiv.mk (fun k : ℤ ↦ (⟨fun _ ↦ k, monotone_const⟩ : {e : Fin 1 → ℤ // Monotone e}))
    (fun e ↦ e.val 0) (fun _ ↦ rfl)
    (fun e ↦ Subtype.ext (funext fun i ↦ congrArg e.val (Subsingleton.elim 0 i)))).trans
    (padicIntPowDiagCosetEquiv 1 p)

/-- `padicRationalCosetEquivInt` sends `k : ℤ` to `padicIntPowDiagCoset 1 p (fun _ ↦ k)`. -/
@[simp]
theorem padicRationalCosetEquivInt_apply (k : ℤ) :
    padicRationalCosetEquivInt p k = padicIntPowDiagCoset 1 p (fun _ ↦ k) := (rfl)

end HeckeRingsAndCosets

section Commutativity

private theorem transposeMulEquiv_mem_GLPadicInt {g : GL (Fin n) ℚ_[p]}
    (hg : g ∈ GLPadicInt (Fin n) p) :
    (Matrix.GeneralLinearGroup.transposeMulEquiv (Fin n) g).unop ∈ GLPadicInt (Fin n) p := by
  obtain ⟨u, rfl⟩ := GLPadicInt.mem_iff_exists_map.mp hg
  exact GLPadicInt.mem_iff_exists_map.mpr
    ⟨(Matrix.GeneralLinearGroup.transposeMulEquiv (Fin n) u).unop, Units.ext (by ext i j; simp)⟩

private theorem transposeMulEquiv_mem_padicIntEntries {g : GL (Fin n) ℚ_[p]}
    (hg : g ∈ padicIntEntries (Fin n) p) :
    (Matrix.GeneralLinearGroup.transposeMulEquiv (Fin n) g).unop ∈ padicIntEntries (Fin n) p := by
  obtain ⟨A, hA⟩ := (mem_padicIntEntries_iff (Fin n) p).mp hg
  exact (mem_padicIntEntries_iff (Fin n) p).mpr
    ⟨Aᵀ, by rw [Matrix.GeneralLinearGroup.coe_unop_transposeMulEquiv, hA, Matrix.transpose_map]⟩

/-- Transposition as an anti-involution of `(padicIntEntries (Fin n) p, GLPadicInt (Fin n) p)`. -/
noncomputable def padicIntegralTransposeAntiInvolution :
    _root_.HeckeAntiInvolution (padicIntEntries (Fin n) p) (GLPadicInt (Fin n) p) :=
  _root_.HeckeAntiInvolution.ofAmbient
    (Matrix.GeneralLinearGroup.transposeMulEquiv (R := ℚ_[p]) (Fin n)).toMonoidHom
    Matrix.GeneralLinearGroup.transposeMulEquiv_transposeMulEquiv
    (fun _ hg ↦ transposeMulEquiv_mem_GLPadicInt n p hg)
    (fun _ hg ↦ transposeMulEquiv_mem_padicIntEntries n p hg)

/-- Transposition as an anti-involution of `(⊤, GLPadicInt (Fin n) p)` in `GL_n(ℚ_p)`. -/
noncomputable def padicRationalTransposeAntiInvolution :
    _root_.HeckeAntiInvolution (⊤ : Submonoid (GL (Fin n) ℚ_[p])) (GLPadicInt (Fin n) p) :=
  _root_.HeckeAntiInvolution.ofAmbient
    (Matrix.GeneralLinearGroup.transposeMulEquiv (R := ℚ_[p]) (Fin n)).toMonoidHom
    Matrix.GeneralLinearGroup.transposeMulEquiv_transposeMulEquiv
    (fun _ hg ↦ transposeMulEquiv_mem_GLPadicInt n p hg)
    (fun _ _ ↦ trivial)

/-- The integral `p`-adic anti-involution acts as matrix transposition. -/
@[simp]
theorem padicIntegralTransposeAntiInvolution_bar {x : GL (Fin n) ℚ_[p]}
    (hx : x ∈ padicIntEntries (Fin n) p) :
    (padicIntegralTransposeAntiInvolution n p).bar x hx =
      (Matrix.GeneralLinearGroup.transposeMulEquiv (Fin n) x).unop :=
  _root_.HeckeAntiInvolution.ofAmbient_bar _ _ _ _ x hx

/-- The rational `p`-adic anti-involution acts as matrix transposition. -/
@[simp]
theorem padicRationalTransposeAntiInvolution_bar {x : GL (Fin n) ℚ_[p]}
    (hx : x ∈ (⊤ : Submonoid (GL (Fin n) ℚ_[p]))) :
    (padicRationalTransposeAntiInvolution n p).bar x hx =
      (Matrix.GeneralLinearGroup.transposeMulEquiv (Fin n) x).unop :=
  _root_.HeckeAntiInvolution.ofAmbient_bar _ _ _ _ x hx

/-- Transposition fixes every integral `p`-adic Hecke double coset. -/
@[simp]
theorem padicIntegralTransposeAntiInvolution_onHeckeCoset_eq_self
    (D : HeckeCoset (padicIntEntries (Fin n) p) (GLPadicInt (Fin n) p) (GLPadicInt (Fin n) p)) :
    (padicIntegralTransposeAntiInvolution n p).onHeckeCoset D = D := by
  obtain ⟨⟨e, -⟩, rfl⟩ := (padicNatPowDiagCosetEquiv n p).surjective D
  rw [padicNatPowDiagCosetEquiv_apply, padicNatPowDiagCoset_def,
    (padicIntegralTransposeAntiInvolution n p).onHeckeCoset_mk]
  exact congrArg (HeckeCoset.mk (GLPadicInt (Fin n) p) (GLPadicInt (Fin n) p))
    (Subtype.ext ((padicIntegralTransposeAntiInvolution_bar n p _).trans
      (Units.ext (by simp [padicNatPowDiagGL_coe]))))

/-- Transposition fixes every rational `p`-adic Hecke double coset. -/
@[simp]
theorem padicRationalTransposeAntiInvolution_onHeckeCoset_eq_self
    (D : HeckeCoset (⊤ : Submonoid (GL (Fin n) ℚ_[p]))
      (GLPadicInt (Fin n) p) (GLPadicInt (Fin n) p)) :
    (padicRationalTransposeAntiInvolution n p).onHeckeCoset D = D := by
  obtain ⟨⟨e, -⟩, rfl⟩ := (padicIntPowDiagCosetEquiv n p).surjective D
  rw [padicIntPowDiagCosetEquiv_apply, padicIntPowDiagCoset_def,
    (padicRationalTransposeAntiInvolution n p).onHeckeCoset_mk]
  exact congrArg (HeckeCoset.mk (GLPadicInt (Fin n) p) (GLPadicInt (Fin n) p))
    (Subtype.ext ((padicRationalTransposeAntiInvolution_bar n p _).trans
      (Units.ext (by simp [padicIntPowDiagGL_coe]))))

/-- Multiplication in `𝕋 (padicIntEntries (Fin n) p) (GLPadicInt (Fin n) p) R` is commutative over
any commutative semiring `R`. -/
theorem mul_comm_padicIntegralHeckeRing (R : Type*) [CommSemiring R]
    (f g : 𝕋 (padicIntEntries (Fin n) p) (GLPadicInt (Fin n) p) R) : f * g = g * f :=
  HeckeCosetModule.mul_comm_of_antiInvolution R (padicIntegralTransposeAntiInvolution n p)
    (padicIntegralTransposeAntiInvolution_onHeckeCoset_eq_self n p) f g

/-- Commutativity of `𝕋 (padicIntEntries (Fin n) p) (GLPadicInt (Fin n) p) R` over any commutative
semiring `R`. -/
@[instance_reducible]
noncomputable def commSemiringPadicIntegralHeckeRing (R : Type*) [CommSemiring R] :
    CommSemiring (𝕋 (padicIntEntries (Fin n) p) (GLPadicInt (Fin n) p) R) :=
  HeckeCosetModule.commSemiringOfAntiInvolution R (padicIntegralTransposeAntiInvolution n p)
    (padicIntegralTransposeAntiInvolution_onHeckeCoset_eq_self n p)

/-- Commutativity of `𝕋 (padicIntEntries (Fin n) p) (GLPadicInt (Fin n) p) R` over any commutative
ring `R`, extending the ambient `Ring` instance without a `Mul` diamond. -/
-- `@[expose]` keeps `toRing` definitionally equal to the ambient `Ring` instance when activated
-- as a local instance in downstream modules (e.g. `Padic/RationalComparison.lean`).
@[expose, instance_reducible]
noncomputable def commRingPadicIntegralHeckeRing (R : Type*) [CommRing R] :
    CommRing (𝕋 (padicIntEntries (Fin n) p) (GLPadicInt (Fin n) p) R) :=
  { (inferInstance : Ring (𝕋 (padicIntEntries (Fin n) p) (GLPadicInt (Fin n) p) R)) with
    mul_comm := mul_comm_padicIntegralHeckeRing n p R }

/-- Multiplication in `𝕋 ⊤ (GLPadicInt (Fin n) p) R` is commutative over any commutative semiring
`R`. -/
theorem mul_comm_padicRationalHeckeRing (R : Type*) [CommSemiring R]
    (f g : 𝕋 (⊤ : Submonoid (GL (Fin n) ℚ_[p])) (GLPadicInt (Fin n) p) R) : f * g = g * f :=
  HeckeCosetModule.mul_comm_of_antiInvolution R (padicRationalTransposeAntiInvolution n p)
    (padicRationalTransposeAntiInvolution_onHeckeCoset_eq_self n p) f g

/-- Commutativity of `𝕋 ⊤ (GLPadicInt (Fin n) p) R` over any commutative semiring `R`. -/
@[instance_reducible]
noncomputable def commSemiringPadicRationalHeckeRing (R : Type*) [CommSemiring R] :
    CommSemiring (𝕋 (⊤ : Submonoid (GL (Fin n) ℚ_[p])) (GLPadicInt (Fin n) p) R) :=
  HeckeCosetModule.commSemiringOfAntiInvolution R (padicRationalTransposeAntiInvolution n p)
    (padicRationalTransposeAntiInvolution_onHeckeCoset_eq_self n p)

/-- Commutativity of `𝕋 ⊤ (GLPadicInt (Fin n) p) R` over any commutative ring `R`, extending the
ambient `Ring` instance without a `Mul` diamond. -/
-- See `commRingPadicIntegralHeckeRing` for `@[expose]`.
@[expose, instance_reducible]
noncomputable def commRingPadicRationalHeckeRing (R : Type*) [CommRing R] :
    CommRing (𝕋 (⊤ : Submonoid (GL (Fin n) ℚ_[p])) (GLPadicInt (Fin n) p) R) :=
  { (inferInstance : Ring (𝕋 (⊤ : Submonoid (GL (Fin n) ℚ_[p])) (GLPadicInt (Fin n) p) R)) with
    mul_comm := mul_comm_padicRationalHeckeRing n p R }

end Commutativity

end HeckeRing.GLn

end
