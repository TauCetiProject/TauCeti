/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.HeckeRing.GLn.Diagonal.Basic
public import TauCeti.NumberTheory.HeckeRing.GLn.Padic

import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Cartan.DiscreteValuationRing

/-!
# Double-coset classification for the local `p`-adic `GL_n` Hecke rings

For a prime `p`, let `TauCeti.GLPadicInt (Fin n) p` be the integral subgroup `GL_n(ℤ_p)` inside
`GL_n(ℚ_p)` and let `HeckeRing.GLn.padicIntEntries (Fin n) p` be the submonoid
`M_n(ℤ_p) ∩ GL_n(ℚ_p)` of invertible `p`-adic matrices with integral `p`-adic entries (defined in
`TauCeti.NumberTheory.HeckeRing.GLn.Padic`). Following Rhodes–Shemanske (1998, §3.1) and
[Rhodes–Shemanske][rhodes1999] §2, this file establishes:

1. Specializing the discrete-valuation-ring Cartan decomposition
   (`TauCeti.exists_monotone_mem_doubleCoset_diagGL_zpow` and
   `TauCeti.eq_of_monotone_of_mem_doubleCoset_diagGL_zpow` in
   `TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Cartan.DiscreteValuationRing`) to `ℤ_[p]` and
   `ℚ_[p]`, every matrix in `GL_n(ℚ_p)` is `GL_n(ℤ_p)`-equivalent to `diag(p ^ e₁, …, p ^ eₙ)` for a
   unique monotone tuple `e : Fin n → ℤ`, and every matrix in `padicIntEntries (Fin n) p` has
   nonnegative Cartan exponents, giving a unique monotone tuple `e : Fin n → ℕ`.
2. The resulting monotone exponent double-coset parametrizations (`padicNatPowDiagCosetEquiv`,
   `padicIntPowDiagCosetEquiv`) for `PadicIntegralHeckeRing n p` and `PadicRationalHeckeRing n p`,
   together with the rank-`1` bijections with `ℕ` and `ℤ` (`padicIntegralCosetEquivNat`,
   `padicRationalCosetEquivInt`).

## Main definitions

* `HeckeRing.GLn.padicNatPowDiagGL`, `HeckeRing.GLn.padicIntPowDiagGL`: diagonal `p`-power matrices
  in `GL_n(ℚ_p)` with `ℕ`- and `ℤ`-exponents.
* `HeckeRing.GLn.padicNatPowDiagCoset`, `HeckeRing.GLn.padicNatPowDiagElem`,
  `HeckeRing.GLn.padicIntPowDiagCoset`, `HeckeRing.GLn.padicIntPowDiagElem`: diagonal double cosets
  and basis elements in the integral and rational local Hecke rings.
* `HeckeRing.GLn.padicNatPowDiagCosetEquiv`, `HeckeRing.GLn.padicIntPowDiagCosetEquiv`: bijections
  between monotone exponent tuples and `p`-adic Hecke double cosets.
* `HeckeRing.GLn.padicIntegralCosetEquivNat`, `HeckeRing.GLn.padicRationalCosetEquivInt`: the
  rank-`1` double-coset bijections with `ℕ` and `ℤ`.

## References

* J. A. Rhodes and T. R. Shemanske, *Bruhat–Tits buildings and Hecke operators*, 12 June 1998
  author manuscript, §3.1.
* [J. A. Rhodes and T. R. Shemanske,
  *Rationality theorems for Hecke operators on GL_n*][rhodes1999], §2.
* [G. Shimura, *Introduction to the arithmetic theory of automorphic functions*][shimura1971], §3.2.
-/

public section

open Matrix Subgroup DoubleCoset TauCeti
open scoped Pointwise HeckeCosetModule

namespace HeckeRing.GLn

variable (n p : ℕ) [Fact p.Prime]

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
  have hzero : (fun i : Fin n ↦ p ^ (0 : Fin n → ℕ) i) = fun _ ↦ 1 :=
    funext fun _ ↦ pow_zero p
  rw [padicNatPowDiagGL_def, hzero, natDiagGL_one, map_one]

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

/-- Every `padicNatPowDiagGL n p e` has `ℤ_p`-entries. -/
theorem padicNatPowDiagGL_mem_padicIntEntries (e : Fin n → ℕ) :
    padicNatPowDiagGL n p e ∈ padicIntEntries (Fin n) p :=
  castGLPadic_mem_padicIntEntries_of_exists_int_matrix
    ⟨Matrix.diagonal fun i ↦ (p : ℤ) ^ e i, by
      rw [natDiagGL_coe n _ fun i ↦ pow_pos (Fact.out : p.Prime).pos (e i)]
      ext i j; by_cases hij : i = j <;> simp [hij]⟩

/-- The underlying `ℤ_p`-matrix of `padicNatPowDiagGL n p e` is `diag(p ^ e₁, …, p ^ eₙ)`. -/
@[simp]
theorem padicIntMatrix_padicNatPowDiagGL (e : Fin n → ℕ) :
    padicIntMatrix (Fin n) p
        ⟨padicNatPowDiagGL n p e, padicNatPowDiagGL_mem_padicIntEntries n p e⟩ =
      Matrix.diagonal fun i ↦ (p : ℤ_[p]) ^ e i := by
  rw [padicIntMatrix_eq_iff, padicNatPowDiagGL_coe]
  ext i j; by_cases hij : i = j <;> simp [hij]

end PadicDiagonal

section PadicDoubleCosets

private lemma range_map_algebraMap_padicInt_eq :
    (GeneralLinearGroup.map (n := Fin n) (algebraMap ℤ_[p] ℚ_[p])).range =
      GLPadicInt (Fin n) p := by
  have halg : algebraMap ℤ_[p] ℚ_[p] = PadicInt.Coe.ringHom (p := p) := RingHom.ext fun _ ↦ rfl
  ext g
  rw [halg, MonoidHom.mem_range, GLPadicInt.mem_iff_exists_map]

private lemma diagGL_p_zpow_eq (e : Fin n → ℤ) :
    (TauCeti.diagGL fun i ↦
        Units.mk0 (p : ℚ_[p]) (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero) ^ e i) =
      padicIntPowDiagGL n p e :=
  Units.ext (by simp [padicIntPowDiagGL_coe])

/-- Every `g ∈ GL_n(ℚ_p)` lies in the `GL_n(ℤ_p)` double coset of `padicIntPowDiagGL n p e` for a
monotone tuple `e : Fin n → ℤ`. -/
theorem exists_padicIntPowDiagGL_mem_doubleCoset (g : GL (Fin n) ℚ_[p]) :
    ∃ e : Fin n → ℤ, Monotone e ∧
      g ∈ doubleCoset (padicIntPowDiagGL n p e) (GLPadicInt (Fin n) p) (GLPadicInt (Fin n) p) := by
  let π : ℚ_[p]ˣ := Units.mk0 (p : ℚ_[p]) (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)
  obtain ⟨e, he, hg⟩ := TauCeti.exists_monotone_mem_doubleCoset_diagGL_zpow
    (PadicInt.irreducible_p (p := p)) (π := π) (by simp [π]) g
  rw [range_map_algebraMap_padicInt_eq, diagGL_p_zpow_eq] at hg
  exact ⟨e, he, hg⟩

/-- Distinct monotone tuples `e₁, e₂ : Fin n → ℤ` define disjoint `GL_n(ℤ_p)` double cosets. -/
theorem eq_of_padicIntPowDiagGL_mem_doubleCoset {e₁ e₂ : Fin n → ℤ}
    (he₁ : Monotone e₁) (he₂ : Monotone e₂)
    (h : padicIntPowDiagGL n p e₂ ∈
      doubleCoset (padicIntPowDiagGL n p e₁) (GLPadicInt (Fin n) p) (GLPadicInt (Fin n) p)) :
    e₁ = e₂ := by
  let π : ℚ_[p]ˣ := Units.mk0 (p : ℚ_[p]) (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)
  refine TauCeti.eq_of_monotone_of_mem_doubleCoset_diagGL_zpow
    (PadicInt.irreducible_p (p := p)) (π := π) (by simp [π]) he₁ he₂
    (g := padicIntPowDiagGL n p e₂) ?_ ?_
  · rw [range_map_algebraMap_padicInt_eq, diagGL_p_zpow_eq]; exact h
  · rw [range_map_algebraMap_padicInt_eq, diagGL_p_zpow_eq]
    exact DoubleCoset.mem_doubleCoset_self _ _ _

/-- Every `g ∈ padicIntEntries (Fin n) p` lies in the `GL_n(ℤ_p)` double coset of
`padicNatPowDiagGL n p e` for a monotone tuple `e : Fin n → ℕ`. -/
theorem exists_padicNatPowDiagGL_mem_doubleCoset {g : GL (Fin n) ℚ_[p]}
    (hg : g ∈ padicIntEntries (Fin n) p) :
    ∃ e : Fin n → ℕ, Monotone e ∧
      g ∈ doubleCoset (padicNatPowDiagGL n p e)
        (GLPadicInt (Fin n) p) (GLPadicInt (Fin n) p) := by
  obtain ⟨a, ha, hcos⟩ := exists_padicIntPowDiagGL_mem_doubleCoset n p g
  obtain ⟨u₁, hu₁, u₂, hu₂, hmul⟩ := DoubleCoset.mem_doubleCoset.mp hcos
  have hdiag_mem : padicIntPowDiagGL n p a ∈ padicIntEntries (Fin n) p := by
    have heq : padicIntPowDiagGL n p a = u₁⁻¹ * g * u₂⁻¹ := by rw [hmul]; simp [mul_assoc]
    rw [heq]
    exact (padicIntEntries (Fin n) p).mul_mem
      ((padicIntEntries (Fin n) p).mul_mem
        (glPadicInt_le_padicIntEntries ((GLPadicInt (Fin n) p).inv_mem hu₁)) hg)
      (glPadicInt_le_padicIntEntries ((GLPadicInt (Fin n) p).inv_mem hu₂))
  have hnonneg (i : Fin n) : 0 ≤ a i := by
    have hnorm := mem_padicIntEntries_iff_norm_le_one.mp hdiag_mem i i
    rw [padicIntPowDiagGL_coe, Matrix.diagonal_apply_eq, norm_zpow, Padic.norm_p,
      _root_.inv_zpow'] at hnorm
    exact neg_nonpos.mp
      ((zpow_le_one_iff_right₀ (Nat.one_lt_cast.mpr (Fact.out : p.Prime).one_lt)).mp hnorm)
  have ha_eq : (fun i ↦ ((a i).toNat : ℤ)) = a :=
    funext fun i ↦ Int.toNat_of_nonneg (hnonneg i)
  refine ⟨fun i ↦ (a i).toNat, fun _ _ hij ↦ Int.toNat_le_toNat (ha hij), ?_⟩
  rwa [← padicIntPowDiagGL_natCast, ha_eq]

/-- Distinct monotone tuples `e₁, e₂ : Fin n → ℕ` define disjoint `GL_n(ℤ_p)` double cosets. -/
theorem eq_of_padicNatPowDiagGL_mem_doubleCoset {e₁ e₂ : Fin n → ℕ}
    (he₁ : Monotone e₁) (he₂ : Monotone e₂)
    (h : padicNatPowDiagGL n p e₂ ∈
      doubleCoset (padicNatPowDiagGL n p e₁) (GLPadicInt (Fin n) p) (GLPadicInt (Fin n) p)) :
    e₁ = e₂ := by
  rw [← padicIntPowDiagGL_natCast, ← padicIntPowDiagGL_natCast] at h
  have heq := eq_of_padicIntPowDiagGL_mem_doubleCoset n p
    (fun _ _ hij ↦ Int.ofNat_le.mpr (he₁ hij))
    (fun _ _ hij ↦ Int.ofNat_le.mpr (he₂ hij)) h
  exact funext fun i ↦ Int.ofNat.inj (congrFun heq i)

end PadicDoubleCosets

section CosetParametrizations

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

end CosetParametrizations

end HeckeRing.GLn

end
