/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Padics.RingHoms
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Transpose
public import TauCeti.NumberTheory.HeckeRing.Commutativity
public import TauCeti.NumberTheory.HeckeRing.GLn.PolynomialRing.Localization

import TauCeti.Data.Int.Shift
import TauCeti.GroupTheory.Commensurable
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Map
import TauCeti.NumberTheory.Padics.Basic
import TauCeti.NumberTheory.Padics.PadicIntegers
import TauCeti.NumberTheory.Padics.RingHoms
import TauCeti.NumberTheory.Padics.SmithNormalForm

/-!
# Integral and rational `p`-adic `GL_n` Hecke rings

For a prime `p`, let `GLnZp n p` be the image of `GL_n(ℤ_p)` inside `GL_n(ℚ_p)` and let
`padicIntEntries n p` be the submonoid `M_n(ℤ_p) ∩ GL_n(ℚ_p)` of invertible `p`-adic matrices
with integral `p`-adic entries. Following Rhodes–Shemanske (1998, §3.1) and
[Rhodes–Shemanske][rhodes1999] §2, this file establishes:

1. Using the `p`-adic Smith normal form (`Matrix.exists_padic_smith_normal_form` and
   `Matrix.padic_smith_normal_form_unique`, whereby every nonsingular matrix in `M_n(ℤ_p)` is
   `GL_n(ℤ_p)`-equivalent to `diag(p ^ e₁, …, p ^ eₙ)` for a unique monotone tuple
   `e : Fin n → ℕ`), every matrix in `padicIntEntries n p` is `GL_n(ℤ_p)`-equivalent to
   `diag(p ^ e₁, …, p ^ eₙ)` for a unique monotone tuple `e : Fin n → ℕ`, and every matrix in
   `GL_n(ℚ_p)` is `GL_n(ℤ_p)`-equivalent to `diag(p ^ e₁, …, p ^ eₙ)` for a unique monotone tuple
   `e : Fin n → ℤ`.
2. Invariance of `GL_n(ℤ_p)` double cosets under negation (`doubleCoset_neg_GLnZp`) and under left
   or right scaling by diagonal `ℤ_pˣ`-matrices (`doubleCoset_diagGL_units_mul_GLnZp`,
   `doubleCoset_mul_diagGL_units_GLnZp`).
3. Commensurability of `GL_n(ℤ_p)` under all of `GL_n(ℚ_p)` (`commensurator_GLnZp_eq_top`), yielding
   the integral and rational `p`-adic Hecke rings `PadicIntegralHeckeRing n p` and
   `PadicRationalHeckeRing n p`, their commutativity via matrix transposition, and their monotone
   exponent double-coset parametrizations (including the rank-`1` bijections with `ℕ` and `ℤ`).

## Main definitions

* `HeckeRing.GLn.GLnZp`: `GL_n(ℤ_p)` embedded as a subgroup of `GL_n(ℚ_p)`.
* `HeckeRing.GLn.padicIntEntries`: the submonoid `M_n(ℤ_p) ∩ GL_n(ℚ_p)`.
* `HeckeRing.GLn.castGLPadic`: the injective group homomorphism `GL_n(ℚ) →* GL_n(ℚ_p)`.
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

open Matrix Subgroup Subgroup.Commensurable DoubleCoset
open scoped Pointwise HeckeCosetModule

namespace HeckeRing.GLn

variable (n p : ℕ) [Fact p.Prime]

section Embedding

/-- The canonical entrywise embedding `GL_n(ℤ_p) →* GL_n(ℚ_p)`. -/
noncomputable def mapGLPadicInt : GL (Fin n) ℤ_[p] →* GL (Fin n) ℚ_[p] :=
  Matrix.GeneralLinearGroup.map (PadicInt.Coe.ringHom (p := p))

/-- Defining equation for `mapGLPadicInt`. -/
theorem mapGLPadicInt_def :
    mapGLPadicInt n p = Matrix.GeneralLinearGroup.map (PadicInt.Coe.ringHom (p := p)) := (rfl)

/-- Matrix coercion of `mapGLPadicInt`. -/
@[simp]
theorem mapGLPadicInt_coe (u : GL (Fin n) ℤ_[p]) :
    (↑(mapGLPadicInt n p u) : Matrix (Fin n) (Fin n) ℚ_[p]) =
      (↑u : Matrix (Fin n) (Fin n) ℤ_[p]).map (PadicInt.Coe.ringHom (p := p)) := by
  ext i j; simp [mapGLPadicInt]

/-- `mapGLPadicInt` is injective because `ℤ_p ↪ ℚ_p` is injective. -/
theorem mapGLPadicInt_injective : Function.Injective (mapGLPadicInt n p) :=
  Matrix.GeneralLinearGroup.map_injective PadicInt.coe_ringHom_injective

/-- `GL_n(ℤ_p)` as a subgroup of `GL_n(ℚ_p)`, defined as the range of `mapGLPadicInt`. -/
noncomputable def GLnZp : Subgroup (GL (Fin n) ℚ_[p]) :=
  (mapGLPadicInt n p).range

/-- Defining equation for `GLnZp`. -/
theorem GLnZp_def : GLnZp n p = (mapGLPadicInt n p).range := (rfl)

/-- Canonical membership of `mapGLPadicInt n p u` in `GLnZp n p`. -/
theorem mapGLPadicInt_mem_GLnZp (u : GL (Fin n) ℤ_[p]) :
    mapGLPadicInt n p u ∈ GLnZp n p := ⟨u, rfl⟩

/-- Membership in `GLnZp n p` characterised by a `GL_n(ℤ_p)` witness. -/
@[simp]
theorem mem_GLnZp_iff {g : GL (Fin n) ℚ_[p]} :
    g ∈ GLnZp n p ↔ ∃ u : GL (Fin n) ℤ_[p], mapGLPadicInt n p u = g :=
  Iff.rfl

/-- `-1` belongs to `GL_n(ℤ_p)` in every rank `n`. -/
theorem neg_one_mem_GLnZp : (-1 : GL (Fin n) ℚ_[p]) ∈ GLnZp n p :=
  ⟨-1, Units.ext (by ext i j; by_cases hij : i = j <;> simp [hij])⟩

/-- Every `GL_n(ℤ_p)` double coset is invariant under negation `g ↦ -g`. -/
@[simp]
theorem doubleCoset_neg_GLnZp (g : GL (Fin n) ℚ_[p]) :
    doubleCoset (-g) (GLnZp n p) (GLnZp n p) = doubleCoset g (GLnZp n p) (GLnZp n p) :=
  DoubleCoset.doubleCoset_neg_of_neg_one_mem_left (neg_one_mem_GLnZp n p) g

/-- Every diagonal matrix of `ℤ_pˣ`-units embeds into `GLnZp n p`. -/
theorem map_diagGL_units_mem_GLnZp (u : Fin n → ℤ_[p]ˣ) :
    mapGLPadicInt n p (TauCeti.diagGL u) ∈ GLnZp n p :=
  mapGLPadicInt_mem_GLnZp n p _

/-- Left multiplication by a diagonal matrix of `ℤ_pˣ`-units preserves `GL_n(ℤ_p)` double cosets. -/
@[simp]
theorem doubleCoset_diagGL_units_mul_GLnZp (u : Fin n → ℤ_[p]ˣ) (g : GL (Fin n) ℚ_[p]) :
    doubleCoset (mapGLPadicInt n p (TauCeti.diagGL u) * g) (GLnZp n p) (GLnZp n p) =
      doubleCoset g (GLnZp n p) (GLnZp n p) :=
  (DoubleCoset.doubleCoset_eq_of_mem (DoubleCoset.mem_doubleCoset.mpr
    ⟨_, (GLnZp n p).inv_mem (map_diagGL_units_mem_GLnZp n p u), 1, one_mem _, by simp⟩)).symm

/-- Right multiplication by a diagonal matrix of `ℤ_pˣ`-units preserves `GL_n(ℤ_p)` double
cosets. -/
@[simp]
theorem doubleCoset_mul_diagGL_units_GLnZp (g : GL (Fin n) ℚ_[p]) (u : Fin n → ℤ_[p]ˣ) :
    doubleCoset (g * mapGLPadicInt n p (TauCeti.diagGL u)) (GLnZp n p) (GLnZp n p) =
      doubleCoset g (GLnZp n p) (GLnZp n p) :=
  (DoubleCoset.doubleCoset_eq_of_mem (DoubleCoset.mem_doubleCoset.mpr
    ⟨1, one_mem _, _, (GLnZp n p).inv_mem (map_diagGL_units_mem_GLnZp n p u), by simp⟩)).symm

/-- The canonical entrywise group homomorphism `GL_n(ℚ) →* GL_n(ℚ_p)`. -/
noncomputable def castGLPadic : GL (Fin n) ℚ →* GL (Fin n) ℚ_[p] :=
  Matrix.GeneralLinearGroup.map (Rat.castHom ℚ_[p])

/-- Defining equation for `castGLPadic`. -/
theorem castGLPadic_def :
    castGLPadic n p = Matrix.GeneralLinearGroup.map (Rat.castHom ℚ_[p]) := (rfl)

/-- Matrix coercion of `castGLPadic`. -/
@[simp]
theorem castGLPadic_coe (g : GL (Fin n) ℚ) :
    (↑(castGLPadic n p g) : Matrix (Fin n) (Fin n) ℚ_[p]) =
      (↑g : Matrix (Fin n) (Fin n) ℚ).map (Rat.castHom ℚ_[p]) := by
  ext i j; simp [castGLPadic]

/-- `castGLPadic` is injective because `ℚ ↪ ℚ_p` is injective. -/
theorem castGLPadic_injective : Function.Injective (castGLPadic n p) :=
  Matrix.GeneralLinearGroup.map_injective (Rat.castHom ℚ_[p]).injective

/-- `castGLPadic` maps `GL_n(ℤ)` into `GL_n(ℤ_p)`. -/
theorem castGLPadic_mem_GLnZp_of_mem_GLnZ {g : GL (Fin n) ℚ} (hg : g ∈ GLnZ n) :
    castGLPadic n p g ∈ GLnZp n p := by
  obtain ⟨γ, rfl⟩ := (mem_GLnZ_iff n).mp hg
  refine ⟨Matrix.GeneralLinearGroup.map (Int.castRingHom ℤ_[p]) γ, Units.ext ?_⟩
  ext i j; simp [castGLPadic, mapGLPadicInt]

/-- `castGLPadic` maps `SL_n(ℤ)` into `GL_n(ℤ_p)`. -/
theorem castGLPadic_mem_GLnZp_of_mem_SLnZ {g : GL (Fin n) ℚ} (hg : g ∈ SLnZ n) :
    castGLPadic n p g ∈ GLnZp n p :=
  castGLPadic_mem_GLnZp_of_mem_GLnZ n p (SLnZ_le_GLnZ n hg)

end Embedding

section PadicIntEntries

/-- Predicate asserting that `g ∈ GL_n(ℚ_p)` has entries in `ℤ_p`. -/
def HasPadicIntEntries (g : GL (Fin n) ℚ_[p]) : Prop :=
  ∃ A : Matrix (Fin n) (Fin n) ℤ_[p],
    (↑g : Matrix (Fin n) (Fin n) ℚ_[p]) = A.map (PadicInt.Coe.ringHom (p := p))

/-- Defining equivalence for `HasPadicIntEntries`. -/
theorem hasPadicIntEntries_def {g : GL (Fin n) ℚ_[p]} :
    HasPadicIntEntries n p g ↔
      ∃ A : Matrix (Fin n) (Fin n) ℤ_[p],
        (↑g : Matrix (Fin n) (Fin n) ℚ_[p]) = A.map (PadicInt.Coe.ringHom (p := p)) := Iff.rfl

/-- `g ∈ GL_n(ℚ_p)` has `ℤ_p`-entries if and only if every matrix entry has `p`-adic norm `≤ 1`. -/
theorem hasPadicIntEntries_iff_norm_le_one {g : GL (Fin n) ℚ_[p]} :
    HasPadicIntEntries n p g ↔ ∀ i j, ‖(↑g : Matrix (Fin n) (Fin n) ℚ_[p]) i j‖ ≤ 1 := by
  constructor
  · rintro ⟨A, hA⟩ i j
    rw [hA, Matrix.map_apply]
    exact (A i j).property
  · intro h
    exact ⟨Matrix.of fun i j ↦ ⟨(↑g : Matrix (Fin n) (Fin n) ℚ_[p]) i j, h i j⟩,
      by ext i j; rfl⟩

/-- The submonoid `M_n(ℤ_p) ∩ GL_n(ℚ_p)` of invertible matrices over `ℚ_p` with `ℤ_p`-entries. -/
def padicIntEntries : Submonoid (GL (Fin n) ℚ_[p]) where
  carrier := {g | HasPadicIntEntries n p g}
  one_mem' := ⟨1, (Matrix.map_one (PadicInt.Coe.ringHom (p := p)) (map_zero _) (map_one _)).symm⟩
  mul_mem' := by
    rintro g h ⟨A, hA⟩ ⟨B, hB⟩
    exact ⟨A * B, by simp [hA, hB]⟩

/-- Membership in `padicIntEntries n p` unfolds to `HasPadicIntEntries n p`. -/
@[simp]
theorem mem_padicIntEntries_iff {g : GL (Fin n) ℚ_[p]} :
    g ∈ padicIntEntries n p ↔ HasPadicIntEntries n p g := Iff.rfl

/-- Every element of `GL_n(ℤ_p)` lies in `padicIntEntries n p`. -/
theorem GLnZp_le_padicIntEntries : (GLnZp n p).toSubmonoid ≤ padicIntEntries n p := by
  rintro g ⟨u, rfl⟩
  exact ⟨↑u, mapGLPadicInt_coe n p u⟩

/-- An element `g ∈ GL_n(ℚ_p)` belongs to `GL_n(ℤ_p)` if and only if both `g` and `g⁻¹` have
`ℤ_p`-entries. -/
theorem mem_GLnZp_iff_mem_padicIntEntries_and_inv {g : GL (Fin n) ℚ_[p]} :
    g ∈ GLnZp n p ↔ g ∈ padicIntEntries n p ∧ g⁻¹ ∈ padicIntEntries n p := by
  constructor
  · intro hg
    exact ⟨GLnZp_le_padicIntEntries n p hg, GLnZp_le_padicIntEntries n p ((GLnZp n p).inv_mem hg)⟩
  · rintro ⟨⟨A, hA⟩, ⟨B, hB⟩⟩
    have hAB : A * B = 1 := Matrix.map_injective PadicInt.coe_ringHom_injective (by
      simp [Matrix.map_one _ (map_zero _) (map_one _), ← hA, ← hB])
    have hBA : B * A = 1 := Matrix.map_injective PadicInt.coe_ringHom_injective (by
      simp [Matrix.map_one _ (map_zero _) (map_one _), ← hA, ← hB])
    exact ⟨⟨A, B, hAB, hBA⟩, Units.ext hA.symm⟩

private noncomputable def padicIntMatrixFun (g : padicIntEntries n p) :
    Matrix (Fin n) (Fin n) ℤ_[p] :=
  Classical.choose g.property

private theorem map_padicIntMatrixFun (g : padicIntEntries n p) :
    (padicIntMatrixFun n p g).map (PadicInt.Coe.ringHom (p := p)) =
      (↑(g : GL (Fin n) ℚ_[p]) : Matrix (Fin n) (Fin n) ℚ_[p]) :=
  (Classical.choose_spec g.property).symm

/-- The `ℤ_p`-matrix underlying an element of `padicIntEntries n p`, packaged as a monoid
homomorphism. -/
noncomputable def padicIntMatrix : padicIntEntries n p →* Matrix (Fin n) (Fin n) ℤ_[p] where
  toFun := padicIntMatrixFun n p
  map_one' := Matrix.map_injective PadicInt.coe_ringHom_injective (by
    simp [map_padicIntMatrixFun, Matrix.map_one _ (map_zero _) (map_one _)])
  map_mul' g h := Matrix.map_injective PadicInt.coe_ringHom_injective (by
    simp [map_padicIntMatrixFun])

/-- Casting `padicIntMatrix n p g` to `ℚ_p` recovers the matrix of `g`. -/
@[simp]
theorem map_padicIntMatrix (g : padicIntEntries n p) :
    (padicIntMatrix n p g).map (PadicInt.Coe.ringHom (p := p)) =
      (↑(g : GL (Fin n) ℚ_[p]) : Matrix (Fin n) (Fin n) ℚ_[p]) :=
  map_padicIntMatrixFun n p g

/-- `padicIntMatrix n p g = A` if and only if `A` casts to the matrix of `g`. -/
theorem padicIntMatrix_eq_iff {g : padicIntEntries n p} {A : Matrix (Fin n) (Fin n) ℤ_[p]} :
    padicIntMatrix n p g = A ↔
      (↑(g : GL (Fin n) ℚ_[p]) : Matrix (Fin n) (Fin n) ℚ_[p]) =
        A.map (PadicInt.Coe.ringHom (p := p)) :=
  ⟨fun h ↦ h ▸ (map_padicIntMatrix n p g).symm,
    fun h ↦ Matrix.map_injective PadicInt.coe_ringHom_injective
      ((map_padicIntMatrix n p g).trans h)⟩

/-- The `ℤ_p`-matrix of an invertible element has nonzero determinant. -/
theorem det_padicIntMatrix_ne_zero (g : padicIntEntries n p) :
    (padicIntMatrix n p g).det ≠ 0 := by
  intro h0
  have hdet := (g : GL (Fin n) ℚ_[p]).det_ne_zero
  rw [← map_padicIntMatrix n p g, ← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero]
    at hdet
  exact hdet rfl

/-- `castGLPadic` sends `intEntries n` into `padicIntEntries n p`. -/
theorem castGLPadic_mem_padicIntEntries_of_mem_intEntries {g : GL (Fin n) ℚ}
    (hg : g ∈ intEntries n) : castGLPadic n p g ∈ padicIntEntries n p := by
  obtain ⟨A, hA⟩ := (hasIntEntries_iff n).mp ((mem_intEntries n).mp hg)
  refine ⟨A.map (Int.castRingHom ℤ_[p]), ?_⟩
  rw [castGLPadic_coe, hA]
  ext i j; simp

/-- `castGLPadic` sends `posDetInt n` into `padicIntEntries n p`. -/
theorem castGLPadic_mem_padicIntEntries_of_mem_posDetInt {g : GL (Fin n) ℚ}
    (hg : g ∈ posDetInt n) : castGLPadic n p g ∈ padicIntEntries n p :=
  castGLPadic_mem_padicIntEntries_of_mem_intEntries n p
    ((mem_intEntries n).mpr ((mem_posDetInt_iff n).mp hg).1)

end PadicIntEntries

section PadicDiagonal

/-- The `p`-adic diagonal matrix `diag(p ^ e₁, …, p ^ eₙ) ∈ GL_n(ℚ_p)` for `e : Fin n → ℕ`. -/
noncomputable def padicNatPowDiagGL (e : Fin n → ℕ) : GL (Fin n) ℚ_[p] :=
  castGLPadic n p (natDiagGL n (primePowDiag n p e))

/-- Defining equation for `padicNatPowDiagGL`. -/
theorem padicNatPowDiagGL_def (e : Fin n → ℕ) :
    padicNatPowDiagGL n p e = castGLPadic n p (natDiagGL n (primePowDiag n p e)) := (rfl)

/-- The `p`-adic diagonal matrix `diag(p ^ e₁, …, p ^ eₙ) ∈ GL_n(ℚ_p)` for `e : Fin n → ℤ`. -/
noncomputable def padicIntPowDiagGL (e : Fin n → ℤ) : GL (Fin n) ℚ_[p] :=
  castGLPadic n p (intPowDiagGL n p e)

/-- Defining equation for `padicIntPowDiagGL`. -/
theorem padicIntPowDiagGL_def (e : Fin n → ℤ) :
    padicIntPowDiagGL n p e = castGLPadic n p (intPowDiagGL n p e) := (rfl)

/-- Matrix coercion of `padicNatPowDiagGL`. -/
@[simp]
theorem padicNatPowDiagGL_coe (e : Fin n → ℕ) :
    (↑(padicNatPowDiagGL n p e) : Matrix (Fin n) (Fin n) ℚ_[p]) =
      Matrix.diagonal fun i ↦ (p : ℚ_[p]) ^ e i := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  rw [padicNatPowDiagGL_def, castGLPadic_coe, natDiagGL_coe n _ (primePowDiag_pos n p hp e)]
  ext i j; by_cases hij : i = j <;> simp [hij, primePowDiag_apply]

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
  have h0 : primePowDiag n p 0 = fun _ ↦ 1 := funext fun i ↦ by simp [primePowDiag_apply]
  rw [padicNatPowDiagGL_def, h0, natDiagGL_one, map_one]

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
    padicIntPowDiagGL n p (fun _ ↦ k) * g = g * padicIntPowDiagGL n p (fun _ ↦ k) := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, padicIntPowDiagGL_coe]
  ext i j
  simp [Matrix.diagonal_mul, Matrix.mul_diagonal, mul_comm]

/-- Scalar `p`-adic diagonal matrices `padicNatPowDiagGL n p (fun _ ↦ k)` are central in
`GL_n(ℚ_p)`. -/
theorem padicNatPowDiagGL_const_comm (k : ℕ) (g : GL (Fin n) ℚ_[p]) :
    padicNatPowDiagGL n p (fun _ ↦ k) * g = g * padicNatPowDiagGL n p (fun _ ↦ k) := by
  rw [← padicIntPowDiagGL_natCast]
  exact padicIntPowDiagGL_const_comm n p k g

/-- Every central `p`-power diagonal matrix `padicIntPowDiagGL n p (fun _ ↦ k)` normalizes
`GL_n(ℤ_p)`. -/
theorem padicIntPowDiagGL_const_mem_normalizer (k : ℤ) :
    padicIntPowDiagGL n p (fun _ ↦ k) ∈
      Subgroup.normalizer (GLnZp n p : Set (GL (Fin n) ℚ_[p])) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  rw [padicIntPowDiagGL_const_comm n p k h, mul_inv_cancel_right]

/-- Every `padicNatPowDiagGL n p e` has `ℤ_p`-entries. -/
theorem padicNatPowDiagGL_mem_padicIntEntries (e : Fin n → ℕ) :
    padicNatPowDiagGL n p e ∈ padicIntEntries n p :=
  castGLPadic_mem_padicIntEntries_of_mem_posDetInt n p (natDiagGL_mem_posDetInt n _)

/-- The underlying `ℤ_p`-matrix of `padicNatPowDiagGL n p e` is `diag(p ^ e₁, …, p ^ eₙ)`. -/
@[simp]
theorem padicIntMatrix_padicNatPowDiagGL (e : Fin n → ℕ) :
    padicIntMatrix n p ⟨padicNatPowDiagGL n p e, padicNatPowDiagGL_mem_padicIntEntries n p e⟩ =
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

/-- Every `g ∈ padicIntEntries n p` lies in the `GL_n(ℤ_p)` double coset of
`padicNatPowDiagGL n p e` for a monotone tuple `e : Fin n → ℕ`. -/
theorem exists_padicNatPowDiagGL_mem_doubleCoset {g : GL (Fin n) ℚ_[p]}
    (hg : g ∈ padicIntEntries n p) :
    ∃ e : Fin n → ℕ, Monotone e ∧
      g ∈ doubleCoset (padicNatPowDiagGL n p e) (GLnZp n p) (GLnZp n p) := by
  obtain ⟨U₁, U₂, e, he, hU⟩ := Matrix.exists_padic_smith_normal_form n p
    (padicIntMatrix n p ⟨g, hg⟩) (det_padicIntMatrix_ne_zero n p ⟨g, hg⟩)
  refine ⟨e, he, DoubleCoset.mem_doubleCoset.mpr
    ⟨mapGLPadicInt n p U₁⁻¹, mapGLPadicInt_mem_GLnZp n p _,
     mapGLPadicInt n p U₂⁻¹, mapGLPadicInt_mem_GLnZp n p _, ?_⟩⟩
  have hmap := congrArg (Matrix.map · (PadicInt.Coe.ringHom (p := p))) hU
  simp only [Matrix.map_mul, map_padicIntMatrix, map_diagonal_padicInt_pow] at hmap
  have hgl : mapGLPadicInt n p U₁ * g * mapGLPadicInt n p U₂ = padicNatPowDiagGL n p e :=
    Units.ext (by simpa only [Units.val_mul, mapGLPadicInt_coe] using hmap)
  rw [← hgl]; simp [mul_assoc]

/-- Distinct monotone tuples `e₁, e₂ : Fin n → ℕ` define disjoint `GL_n(ℤ_p)` double cosets. -/
theorem eq_of_padicNatPowDiagGL_mem_doubleCoset {e₁ e₂ : Fin n → ℕ}
    (he₁ : Monotone e₁) (he₂ : Monotone e₂)
    (h : padicNatPowDiagGL n p e₂ ∈
      doubleCoset (padicNatPowDiagGL n p e₁) (GLnZp n p) (GLnZp n p)) :
    e₁ = e₂ := by
  obtain ⟨u₁, ⟨U₁, rfl⟩, u₂, ⟨U₂, rfl⟩, hu⟩ := DoubleCoset.mem_doubleCoset.mp h
  apply Matrix.padic_smith_normal_form_unique n p he₁ he₂ U₁ U₂
  apply Matrix.map_injective PadicInt.coe_ringHom_injective
  simpa only [Matrix.map_mul, map_diagonal_padicInt_pow, Units.val_mul, mapGLPadicInt_coe] using
    congrArg Units.val hu.symm

/-- **Clearing denominators in `GL_n(ℚ_p)`**: for every `g ∈ GL_n(ℚ_p)` there exists `k : ℕ` such
that `padicNatPowDiagGL n p (fun _ ↦ k) * g` has `ℤ_p`-entries. -/
theorem exists_padicNatPowDiagGL_const_mul_mem_padicIntEntries (g : GL (Fin n) ℚ_[p]) :
    ∃ k : ℕ, padicNatPowDiagGL n p (fun _ ↦ k) * g ∈ padicIntEntries n p := by
  let M : ℕ := Finset.univ.sup fun ij : Fin n × Fin n ↦
    (-((↑g : Matrix (Fin n) (Fin n) ℚ_[p]) ij.1 ij.2).valuation).toNat
  refine ⟨M, (hasPadicIntEntries_iff_norm_le_one n p).mpr fun i j ↦ ?_⟩
  rw [Units.val_mul, padicNatPowDiagGL_coe, Matrix.diagonal_mul]
  set x := (↑g : Matrix (Fin n) (Fin n) ℚ_[p]) i j
  by_cases hx : x = 0
  · simp [hx]
  · rw [Padic.norm_le_one_iff_val_nonneg, ← zpow_natCast (p : ℚ_[p]) M,
      Padic.valuation_p_zpow_mul _ hx]
    have hle : (-x.valuation).toNat ≤ M :=
      Finset.le_sup (f := fun ij : Fin n × Fin n ↦
        (-((↑g : Matrix (Fin n) (Fin n) ℚ_[p]) ij.1 ij.2).valuation).toNat)
        (Finset.mem_univ (i, j))
    omega

/-- Every `g ∈ GL_n(ℚ_p)` lies in the `GL_n(ℤ_p)` double coset of `padicIntPowDiagGL n p e` for a
monotone tuple `e : Fin n → ℤ`. -/
theorem exists_padicIntPowDiagGL_mem_doubleCoset (g : GL (Fin n) ℚ_[p]) :
    ∃ e : Fin n → ℤ, Monotone e ∧
      g ∈ doubleCoset (padicIntPowDiagGL n p e) (GLnZp n p) (GLnZp n p) := by
  obtain ⟨k, hk⟩ := exists_padicNatPowDiagGL_const_mul_mem_padicIntEntries n p g
  obtain ⟨e', he', hcos⟩ := exists_padicNatPowDiagGL_mem_doubleCoset n p hk
  obtain ⟨u₁, hu₁, u₂, hu₂, hmul⟩ := DoubleCoset.mem_doubleCoset.mp hcos
  refine ⟨fun i ↦ (e' i : ℤ) - k, fun i j hij ↦ sub_le_sub_right (Nat.cast_le.mpr (he' hij)) _,
    DoubleCoset.mem_doubleCoset.mpr ⟨u₁, hu₁, u₂, hu₂, ?_⟩⟩
  have hsub : (fun i : Fin n ↦ (e' i : ℤ) - k) =
      (fun _ ↦ -(k : ℤ)) + (fun i ↦ (e' i : ℤ)) := funext fun i ↦ sub_eq_neg_add _ _
  calc g = (padicNatPowDiagGL n p (fun _ ↦ k))⁻¹ *
        (padicNatPowDiagGL n p (fun _ ↦ k) * g) := by simp
    _ = (padicNatPowDiagGL n p (fun _ ↦ k))⁻¹ *
        (u₁ * padicNatPowDiagGL n p e' * u₂) := by rw [hmul]
    _ = u₁ * ((padicNatPowDiagGL n p (fun _ ↦ k))⁻¹ * padicNatPowDiagGL n p e') * u₂ := by
        simp only [← mul_assoc]
        congr 1; congr 1
        rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, padicNatPowDiagGL_const_comm n p k u₁,
          mul_inv_cancel_right]
    _ = u₁ * padicIntPowDiagGL n p (fun i ↦ (e' i : ℤ) - k) * u₂ := by
        rw [hsub, padicIntPowDiagGL_add, padicIntPowDiagGL_const_neg, padicIntPowDiagGL_natCast]

/-- Distinct monotone tuples `e₁, e₂ : Fin n → ℤ` define disjoint `GL_n(ℤ_p)` double cosets. -/
theorem eq_of_padicIntPowDiagGL_mem_doubleCoset {e₁ e₂ : Fin n → ℤ}
    (he₁ : Monotone e₁) (he₂ : Monotone e₂)
    (h : padicIntPowDiagGL n p e₂ ∈
      doubleCoset (padicIntPowDiagGL n p e₁) (GLnZp n p) (GLnZp n p)) :
    e₁ = e₂ := by
  obtain ⟨M, f, hf⟩ := TauCeti.exists_natCast_eq_add_natCast (Sum.elim e₁ e₂)
  let f₁ : Fin n → ℕ := f ∘ Sum.inl
  let f₂ : Fin n → ℕ := f ∘ Sum.inr
  have hf₁_eq : ∀ i, (f₁ i : ℤ) = e₁ i + M := fun i ↦ hf (Sum.inl i)
  have hf₂_eq : ∀ i, (f₂ i : ℤ) = e₂ i + M := fun i ↦ hf (Sum.inr i)
  have hf₁_mono : Monotone f₁ := fun i j hij ↦ by
    rw [← Int.ofNat_le, hf₁_eq, hf₁_eq]; linarith [he₁ hij]
  have hf₂_mono : Monotone f₂ := fun i j hij ↦ by
    rw [← Int.ofNat_le, hf₂_eq, hf₂_eq]; linarith [he₂ hij]
  obtain ⟨u₁, hu₁, u₂, hu₂, hmul⟩ := DoubleCoset.mem_doubleCoset.mp h
  have hshift : padicNatPowDiagGL n p f₂ ∈
      doubleCoset (padicNatPowDiagGL n p f₁) (GLnZp n p) (GLnZp n p) := by
    refine DoubleCoset.mem_doubleCoset.mpr ⟨u₁, hu₁, u₂, hu₂, ?_⟩
    have hf₁_fun : (fun i ↦ (f₁ i : ℤ)) = (fun _ ↦ (M : ℤ)) + e₁ :=
      funext fun i ↦ by rw [hf₁_eq, Pi.add_apply, add_comm]
    have hf₂_fun : (fun i ↦ (f₂ i : ℤ)) = (fun _ ↦ (M : ℤ)) + e₂ :=
      funext fun i ↦ by rw [hf₂_eq, Pi.add_apply, add_comm]
    rw [← padicIntPowDiagGL_natCast, ← padicIntPowDiagGL_natCast, hf₂_fun, hf₁_fun,
      padicIntPowDiagGL_add, padicIntPowDiagGL_add, hmul]
    simp only [← mul_assoc, padicIntPowDiagGL_const_comm n p M u₁]
  have hfeq := eq_of_padicNatPowDiagGL_mem_doubleCoset n p hf₁_mono hf₂_mono hshift
  funext i
  have := congrArg (fun f : Fin n → ℕ ↦ (f i : ℤ)) hfeq
  linarith [hf₁_eq i, hf₂_eq i]

end PadicDoubleCosets

section Commensurator

/-- Conjugating an element of the congruence kernel `ker(GL_n(ℤ_p) → GL_n(ℤ/p^M ℤ))` by
`padicIntPowDiagGL n p e` stays in `padicIntEntries n p` once `M` bounds all `|e i - e j|`. -/
private theorem conj_padicIntPowDiagGL_mem_padicIntEntries {e : Fin n → ℤ} {M : ℕ}
    (hM : ∀ i j, e j - e i ≤ M) (u : GL (Fin n) ℤ_[p])
    (hu : u ∈ (Matrix.GeneralLinearGroup.map (PadicInt.toZModPow (p := p) M)).ker) :
    (padicIntPowDiagGL n p e)⁻¹ * mapGLPadicInt n p u * padicIntPowDiagGL n p e ∈
      padicIntEntries n p := by
  rw [mem_padicIntEntries_iff, hasPadicIntEntries_iff_norm_le_one]
  intro i j
  have hmat : (↑((padicIntPowDiagGL n p e)⁻¹ * mapGLPadicInt n p u * padicIntPowDiagGL n p e) :
      Matrix (Fin n) (Fin n) ℚ_[p]) =
      (Matrix.diagonal fun k ↦ (p : ℚ_[p]) ^ (-e k)) *
        (↑u : Matrix (Fin n) (Fin n) ℤ_[p]).map (PadicInt.Coe.ringHom (p := p)) *
        Matrix.diagonal fun k ↦ (p : ℚ_[p]) ^ e k := by
    simp only [← padicIntPowDiagGL_neg, Units.val_mul, padicIntPowDiagGL_coe,
      mapGLPadicInt_coe, Pi.neg_apply]
  have hval : (↑((padicIntPowDiagGL n p e)⁻¹ * mapGLPadicInt n p u * padicIntPowDiagGL n p e) :
      Matrix (Fin n) (Fin n) ℚ_[p]) i j =
      (p : ℚ_[p]) ^ (-e i) * ((↑u : Matrix (Fin n) (Fin n) ℤ_[p]) i j : ℚ_[p]) *
        (p : ℚ_[p]) ^ e j := by
    have hfun := congr_fun (congr_fun hmat i) j
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.map_apply,
      PadicInt.Coe.ringHom_apply] at hfun
    exact hfun
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
        (p : ℚ_[p]) ^ (M : ℤ) * (c : ℚ_[p]) := by
      rw [hc, zpow_natCast]; push_cast; rfl
    rw [hcast, ← mul_assoc, mul_right_comm _ (c : ℚ_[p]),
      ← zpow_add₀ (NeZero.ne (p : ℚ_[p])), ← zpow_add₀ (NeZero.ne (p : ℚ_[p]))]
    let E : ℕ := (-e i + (M : ℤ) + e j).toNat
    have hE : -e i + (M : ℤ) + e j = (E : ℤ) :=
      (Int.toNat_of_nonneg (by have := hM j i; omega)).symm
    have hzp : (p : ℚ_[p]) ^ (E : ℤ) * (c : ℚ_[p]) = (((p : ℤ_[p]) ^ E * c : ℤ_[p]) : ℚ_[p]) := by
      rw [zpow_natCast]; push_cast; rfl
    rw [hE, hzp]
    exact ((p : ℤ_[p]) ^ E * c).property

private theorem congruence_ker_le_conj_padicIntPowDiagGL {e : Fin n → ℤ} {M : ℕ}
    (hM : ∀ i j, e j - e i ≤ M) :
    (Matrix.GeneralLinearGroup.map (PadicInt.toZModPow (p := p) M) :
      GL (Fin n) ℤ_[p] →* GL (Fin n) (ZMod (p ^ M))).ker.map (mapGLPadicInt n p) ≤
      MulAut.conj (padicIntPowDiagGL n p e) • GLnZp n p := by
  set φ : GL (Fin n) ℤ_[p] →* GL (Fin n) (ZMod (p ^ M)) :=
    Matrix.GeneralLinearGroup.map (PadicInt.toZModPow (p := p) M)
  set g := padicIntPowDiagGL n p e
  rintro x ⟨u, hu, rfl⟩
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, MulAut.smul_def, MulAut.conj_inv_apply,
    mem_GLnZp_iff_mem_padicIntEntries_and_inv]
  refine ⟨conj_padicIntPowDiagGL_mem_padicIntEntries n p hM u hu, ?_⟩
  have hinv : (g⁻¹ * mapGLPadicInt n p u * g)⁻¹ = g⁻¹ * mapGLPadicInt n p u⁻¹ * g := by
    rw [_root_.mul_inv_rev, _root_.mul_inv_rev, inv_inv, ← map_inv, mul_assoc]
  rw [hinv]
  exact conj_padicIntPowDiagGL_mem_padicIntEntries n p hM u⁻¹ (φ.ker.inv_mem hu)

/-- Every `padicIntPowDiagGL n p e` belongs to the commensurator of `GL_n(ℤ_p)`. -/
theorem padicIntPowDiagGL_mem_commensurator_GLnZp (e : Fin n → ℤ) :
    padicIntPowDiagGL n p e ∈ commensurator (GLnZp n p) := by
  rw [commensurator_mem_iff]
  set H := GLnZp n p
  let M : ℕ := 2 * Finset.univ.sup fun i ↦ (e i).natAbs
  have hM : ∀ i j, e j - e i ≤ M := fun i j ↦ by
    have hi := Finset.le_sup (f := fun k : Fin n ↦ (e k).natAbs) (Finset.mem_univ i)
    have hj := Finset.le_sup (f := fun k : Fin n ↦ (e k).natAbs) (Finset.mem_univ j)
    omega
  have hM' : ∀ i j, (-e) j - (-e) i ≤ M := fun i j ↦ by
    simpa [sub_eq_add_neg, add_comm] using hM j i
  have : NeZero (p ^ M) := NeZero.pow
  set φ : GL (Fin n) ℤ_[p] →* GL (Fin n) (ZMod (p ^ M)) :=
    Matrix.GeneralLinearGroup.map (PadicInt.toZModPow (p := p) M)
  set K := φ.ker.map (mapGLPadicInt n p)
  have hK_rel : K.relIndex H ≠ 0 := by
    have hH : H = Subgroup.map (mapGLPadicInt n p) ⊤ := by
      simp [H, GLnZp_def, MonoidHom.range_eq_map]
    rw [hH, Subgroup.relIndex_map_map_of_injective _ _ (mapGLPadicInt_injective n p),
      Subgroup.relIndex_top_right]
    exact (Subgroup.finiteIndex_ker φ).index_ne_zero
  set g := padicIntPowDiagGL n p e
  have hK_le_gH : K ≤ MulAut.conj g • H := congruence_ker_le_conj_padicIntPowDiagGL n p hM
  have hK_le_ginvH : K ≤ MulAut.conj g⁻¹ • H := by
    have hginv : g⁻¹ = padicIntPowDiagGL n p (-e) := (padicIntPowDiagGL_neg n p e).symm
    rw [hginv]
    exact congruence_ker_le_conj_padicIntPowDiagGL n p hM'
  have hgH : (MulAut.conj g • H).relIndex H ≠ 0 :=
    ne_zero_of_dvd_ne_zero hK_rel (Subgroup.relIndex_dvd_of_le_left H hK_le_gH)
  have hHg : H.relIndex (MulAut.conj g • H) ≠ 0 := by
    have h1 : MulAut.conj g⁻¹ • (MulAut.conj g • H) = H := by
      rw [smul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul]
    rw [(Subgroup.relIndex_pointwise_smul (MulAut.conj g⁻¹) H
      (MulAut.conj g • H)).symm.trans (by rw [h1])]
    exact ne_zero_of_dvd_ne_zero hK_rel (Subgroup.relIndex_dvd_of_le_left H hK_le_ginvH)
  exact ⟨Subgroup.isFiniteRelIndex_iff_relIndex_ne_zero.mpr hgH,
    Subgroup.isFiniteRelIndex_iff_relIndex_ne_zero.mpr hHg⟩

/-- **The commensurator of `GL_n(ℤ_p)` in `GL_n(ℚ_p)` is the whole group `GL_n(ℚ_p)`.** -/
theorem commensurator_GLnZp_eq_top : commensurator (GLnZp n p) = ⊤ := by
  rw [Subgroup.eq_top_iff']
  intro g
  obtain ⟨e, -, hcos⟩ := exists_padicIntPowDiagGL_mem_doubleCoset n p g
  obtain ⟨u₁, hu₁, u₂, hu₂, rfl⟩ := DoubleCoset.mem_doubleCoset.mp hcos
  exact (commensurator (GLnZp n p)).mul_mem
    ((commensurator (GLnZp n p)).mul_mem
      (Subgroup.Commensurable.le_commensurator (GLnZp n p) hu₁)
      (padicIntPowDiagGL_mem_commensurator_GLnZp n p e))
    (Subgroup.Commensurable.le_commensurator (GLnZp n p) hu₂)

/-- The integral `p`-adic Hecke triple `(M_n(ℤ_p) ∩ GL_n(ℚ_p), GL_n(ℤ_p))`. -/
instance instIsHeckeTriplePadicIntEntries :
    IsHeckeTriple (padicIntEntries n p) (GLnZp n p) (GLnZp n p) :=
  IsHeckeTriple.of_diagonal (GLnZp_le_padicIntEntries n p)
    (fun _ _ ↦ by rw [Subgroup.mem_toSubmonoid, commensurator_GLnZp_eq_top]; trivial)

/-- The rational `p`-adic Hecke triple `(GL_n(ℚ_p), GL_n(ℤ_p))`. -/
instance instIsHeckeTriplePadicTop :
    IsHeckeTriple (⊤ : Submonoid (GL (Fin n) ℚ_[p])) (GLnZp n p) (GLnZp n p) :=
  IsHeckeTriple.of_diagonal le_top
    (fun _ _ ↦ by rw [Subgroup.mem_toSubmonoid, commensurator_GLnZp_eq_top]; trivial)

end Commensurator

section HeckeRingsAndCosets

/-- **The integral `p`-adic Hecke ring** of `(GL_n(ℤ_p), M_n(ℤ_p) ∩ GL_n(ℚ_p))` over `ℤ`. -/
abbrev PadicIntegralHeckeRing : Type :=
  𝕋 (padicIntEntries n p) (GLnZp n p) ℤ

/-- **The rational (spherical) `p`-adic Hecke ring** of `(GL_n(ℤ_p), GL_n(ℚ_p))` over `ℤ`. -/
abbrev PadicRationalHeckeRing : Type :=
  𝕋 (⊤ : Submonoid (GL (Fin n) ℚ_[p])) (GLnZp n p) ℤ

/-- The `GL_n(ℤ_p)` double coset of `padicNatPowDiagGL n p e` in `padicIntEntries n p`. -/
noncomputable def padicNatPowDiagCoset (e : Fin n → ℕ) :
    HeckeCoset (padicIntEntries n p) (GLnZp n p) (GLnZp n p) :=
  HeckeCoset.mk (GLnZp n p) (GLnZp n p)
    ⟨padicNatPowDiagGL n p e, padicNatPowDiagGL_mem_padicIntEntries n p e⟩

/-- Defining equation for `padicNatPowDiagCoset`. -/
theorem padicNatPowDiagCoset_def (e : Fin n → ℕ) :
    padicNatPowDiagCoset n p e =
      HeckeCoset.mk (GLnZp n p) (GLnZp n p)
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
`(padicIntEntries n p, GLnZp n p)`. -/
noncomputable def padicNatPowDiagCosetEquiv :
    {e : Fin n → ℕ // Monotone e} ≃ HeckeCoset (padicIntEntries n p) (GLnZp n p) (GLnZp n p) :=
  Equiv.ofBijective (fun e ↦ padicNatPowDiagCoset n p e.val) ⟨by
    rintro ⟨e₁, he₁⟩ ⟨e₂, he₂⟩ h
    apply Subtype.ext
    have hset := congrArg HeckeCoset.toSet h
    dsimp only at hset
    rw [padicNatPowDiagCoset_def, padicNatPowDiagCoset_def,
      HeckeCoset.toSet_mk, HeckeCoset.toSet_mk] at hset
    exact (eq_of_padicNatPowDiagGL_mem_doubleCoset n p he₂ he₁
      (hset ▸ DoubleCoset.mem_doubleCoset_self _ _ _)).symm,
    fun D ↦ by
      obtain ⟨e, he, hmem⟩ := exists_padicNatPowDiagGL_mem_doubleCoset n p D.rep.property
      refine ⟨⟨e, he⟩, ?_⟩
      dsimp only
      rw [padicNatPowDiagCoset_def]
      exact ((HeckeCoset.mk_eq_mk_of_mem hmem).symm).trans (HeckeCoset.mk_rep D)⟩

/-- `padicNatPowDiagCosetEquiv` sends a monotone tuple `e` to `padicNatPowDiagCoset n p e`. -/
@[simp]
theorem padicNatPowDiagCosetEquiv_apply (e : {e : Fin n → ℕ // Monotone e}) :
    padicNatPowDiagCosetEquiv n p e = padicNatPowDiagCoset n p e.val := (rfl)

/-- The `GL_n(ℤ_p)` double coset of `padicIntPowDiagGL n p e` in `GL_n(ℚ_p)`. -/
noncomputable def padicIntPowDiagCoset (e : Fin n → ℤ) :
    HeckeCoset (⊤ : Submonoid (GL (Fin n) ℚ_[p])) (GLnZp n p) (GLnZp n p) :=
  HeckeCoset.mk (GLnZp n p) (GLnZp n p) ⟨padicIntPowDiagGL n p e, trivial⟩

/-- Defining equation for `padicIntPowDiagCoset`. -/
theorem padicIntPowDiagCoset_def (e : Fin n → ℤ) :
    padicIntPowDiagCoset n p e =
      HeckeCoset.mk (GLnZp n p) (GLnZp n p) ⟨padicIntPowDiagGL n p e, trivial⟩ := (rfl)

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
`(⊤, GLnZp n p)` in `GL_n(ℚ_p)`. -/
noncomputable def padicIntPowDiagCosetEquiv :
    {e : Fin n → ℤ // Monotone e} ≃
      HeckeCoset (⊤ : Submonoid (GL (Fin n) ℚ_[p])) (GLnZp n p) (GLnZp n p) :=
  Equiv.ofBijective (fun e ↦ padicIntPowDiagCoset n p e.val) ⟨by
    rintro ⟨e₁, he₁⟩ ⟨e₂, he₂⟩ h
    apply Subtype.ext
    have hset := congrArg HeckeCoset.toSet h
    dsimp only at hset
    rw [padicIntPowDiagCoset_def, padicIntPowDiagCoset_def,
      HeckeCoset.toSet_mk, HeckeCoset.toSet_mk] at hset
    exact (eq_of_padicIntPowDiagGL_mem_doubleCoset n p he₂ he₁
      (hset ▸ DoubleCoset.mem_doubleCoset_self _ _ _)).symm,
    fun D ↦ by
      obtain ⟨e, he, hmem⟩ :=
        exists_padicIntPowDiagGL_mem_doubleCoset n p (D.rep : GL (Fin n) ℚ_[p])
      refine ⟨⟨e, he⟩, ?_⟩
      dsimp only
      rw [padicIntPowDiagCoset_def]
      exact ((HeckeCoset.mk_eq_mk_of_mem hmem).symm).trans (HeckeCoset.mk_rep D)⟩

/-- `padicIntPowDiagCosetEquiv` sends a monotone tuple `e` to `padicIntPowDiagCoset n p e`. -/
@[simp]
theorem padicIntPowDiagCosetEquiv_apply (e : {e : Fin n → ℤ // Monotone e}) :
    padicIntPowDiagCosetEquiv n p e = padicIntPowDiagCoset n p e.val := (rfl)

/-- **Rank-`1` integral `p`-adic cosets**: in rank `n = 1`, the double cosets of
`(M_1(ℤ_p) ∩ GL_1(ℚ_p), GL_1(ℤ_p))` biject canonically with `ℕ` via
`k ↦ [GL_1(ℤ_p) · p ^ k · GL_1(ℤ_p)]`. -/
noncomputable def padicIntegralCosetEquivNat :
    ℕ ≃ HeckeCoset (padicIntEntries 1 p) (GLnZp 1 p) (GLnZp 1 p) :=
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
    ℤ ≃ HeckeCoset (⊤ : Submonoid (GL (Fin 1) ℚ_[p])) (GLnZp 1 p) (GLnZp 1 p) :=
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

private theorem transposeMulEquiv_mem_GLnZp {g : GL (Fin n) ℚ_[p]} (hg : g ∈ GLnZp n p) :
    (Matrix.GeneralLinearGroup.transposeMulEquiv (Fin n) g).unop ∈ GLnZp n p := by
  obtain ⟨u, rfl⟩ := (mem_GLnZp_iff n p).mp hg
  refine ⟨(Matrix.GeneralLinearGroup.transposeMulEquiv (Fin n) u).unop, Units.ext ?_⟩
  ext i j; simp [mapGLPadicInt]

private theorem transposeMulEquiv_mem_padicIntEntries {g : GL (Fin n) ℚ_[p]}
    (hg : g ∈ padicIntEntries n p) :
    (Matrix.GeneralLinearGroup.transposeMulEquiv (Fin n) g).unop ∈ padicIntEntries n p := by
  obtain ⟨A, hA⟩ := hg
  refine ⟨Aᵀ, ?_⟩
  rw [Matrix.GeneralLinearGroup.coe_unop_transposeMulEquiv, hA, Matrix.transpose_map]

/-- Transposition as an anti-involution of `(padicIntEntries n p, GLnZp n p)`. -/
noncomputable def padicIntegralTransposeAntiInvolution :
    _root_.HeckeAntiInvolution (padicIntEntries n p) (GLnZp n p) :=
  _root_.HeckeAntiInvolution.ofAmbient
    (Matrix.GeneralLinearGroup.transposeMulEquiv (R := ℚ_[p]) (Fin n)).toMonoidHom
    Matrix.GeneralLinearGroup.transposeMulEquiv_transposeMulEquiv
    (fun _ hg ↦ transposeMulEquiv_mem_GLnZp n p hg)
    (fun _ hg ↦ transposeMulEquiv_mem_padicIntEntries n p hg)

/-- Transposition as an anti-involution of `(⊤, GLnZp n p)` in `GL_n(ℚ_p)`. -/
noncomputable def padicRationalTransposeAntiInvolution :
    _root_.HeckeAntiInvolution (⊤ : Submonoid (GL (Fin n) ℚ_[p])) (GLnZp n p) :=
  _root_.HeckeAntiInvolution.ofAmbient
    (Matrix.GeneralLinearGroup.transposeMulEquiv (R := ℚ_[p]) (Fin n)).toMonoidHom
    Matrix.GeneralLinearGroup.transposeMulEquiv_transposeMulEquiv
    (fun _ hg ↦ transposeMulEquiv_mem_GLnZp n p hg)
    (fun _ _ ↦ trivial)

/-- The integral `p`-adic anti-involution acts as matrix transposition. -/
@[simp]
theorem padicIntegralTransposeAntiInvolution_bar {x : GL (Fin n) ℚ_[p]}
    (hx : x ∈ padicIntEntries n p) :
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
    (D : HeckeCoset (padicIntEntries n p) (GLnZp n p) (GLnZp n p)) :
    (padicIntegralTransposeAntiInvolution n p).onHeckeCoset D = D := by
  obtain ⟨⟨e, -⟩, rfl⟩ := (padicNatPowDiagCosetEquiv n p).surjective D
  rw [padicNatPowDiagCosetEquiv_apply, padicNatPowDiagCoset_def,
    (padicIntegralTransposeAntiInvolution n p).onHeckeCoset_mk]
  exact congrArg (HeckeCoset.mk (GLnZp n p) (GLnZp n p))
    (Subtype.ext ((padicIntegralTransposeAntiInvolution_bar n p _).trans
      (Units.ext (by simp [padicNatPowDiagGL_coe]))))

/-- Transposition fixes every rational `p`-adic Hecke double coset. -/
@[simp]
theorem padicRationalTransposeAntiInvolution_onHeckeCoset_eq_self
    (D : HeckeCoset (⊤ : Submonoid (GL (Fin n) ℚ_[p])) (GLnZp n p) (GLnZp n p)) :
    (padicRationalTransposeAntiInvolution n p).onHeckeCoset D = D := by
  obtain ⟨⟨e, -⟩, rfl⟩ := (padicIntPowDiagCosetEquiv n p).surjective D
  rw [padicIntPowDiagCosetEquiv_apply, padicIntPowDiagCoset_def,
    (padicRationalTransposeAntiInvolution n p).onHeckeCoset_mk]
  exact congrArg (HeckeCoset.mk (GLnZp n p) (GLnZp n p))
    (Subtype.ext ((padicRationalTransposeAntiInvolution_bar n p _).trans
      (Units.ext (by simp [padicIntPowDiagGL_coe]))))

/-- Multiplication in `𝕋 (padicIntEntries n p) (GLnZp n p) R` is commutative over any commutative
semiring `R`. -/
theorem mul_comm_padicIntegralHeckeRing (R : Type*) [CommSemiring R]
    (f g : 𝕋 (padicIntEntries n p) (GLnZp n p) R) : f * g = g * f :=
  HeckeCosetModule.mul_comm_of_antiInvolution R (padicIntegralTransposeAntiInvolution n p)
    (padicIntegralTransposeAntiInvolution_onHeckeCoset_eq_self n p) f g

/-- Commutativity of `𝕋 (padicIntEntries n p) (GLnZp n p) R` over any commutative semiring `R`. -/
@[instance_reducible]
noncomputable def commSemiringPadicIntegralHeckeRing (R : Type*) [CommSemiring R] :
    CommSemiring (𝕋 (padicIntEntries n p) (GLnZp n p) R) :=
  HeckeCosetModule.commSemiringOfAntiInvolution R (padicIntegralTransposeAntiInvolution n p)
    (padicIntegralTransposeAntiInvolution_onHeckeCoset_eq_self n p)

/-- Commutativity of `𝕋 (padicIntEntries n p) (GLnZp n p) R` over any commutative ring `R`,
extending the ambient `Ring` instance without a `Mul` diamond. -/
-- `@[expose]` keeps `toRing` definitionally equal to the ambient `Ring` instance when activated
-- as a local instance in downstream modules (e.g. `Padic/RationalComparison.lean`).
@[expose, instance_reducible]
noncomputable def commRingPadicIntegralHeckeRing (R : Type*) [CommRing R] :
    CommRing (𝕋 (padicIntEntries n p) (GLnZp n p) R) :=
  { (inferInstance : Ring (𝕋 (padicIntEntries n p) (GLnZp n p) R)) with
    mul_comm := mul_comm_padicIntegralHeckeRing n p R }

/-- Multiplication in `𝕋 ⊤ (GLnZp n p) R` is commutative over any commutative semiring `R`. -/
theorem mul_comm_padicRationalHeckeRing (R : Type*) [CommSemiring R]
    (f g : 𝕋 (⊤ : Submonoid (GL (Fin n) ℚ_[p])) (GLnZp n p) R) : f * g = g * f :=
  HeckeCosetModule.mul_comm_of_antiInvolution R (padicRationalTransposeAntiInvolution n p)
    (padicRationalTransposeAntiInvolution_onHeckeCoset_eq_self n p) f g

/-- Commutativity of `𝕋 ⊤ (GLnZp n p) R` over any commutative semiring `R`. -/
@[instance_reducible]
noncomputable def commSemiringPadicRationalHeckeRing (R : Type*) [CommSemiring R] :
    CommSemiring (𝕋 (⊤ : Submonoid (GL (Fin n) ℚ_[p])) (GLnZp n p) R) :=
  HeckeCosetModule.commSemiringOfAntiInvolution R (padicRationalTransposeAntiInvolution n p)
    (padicRationalTransposeAntiInvolution_onHeckeCoset_eq_self n p)

/-- Commutativity of `𝕋 ⊤ (GLnZp n p) R` over any commutative ring `R`, extending the ambient
`Ring` instance without a `Mul` diamond. -/
-- See `commRingPadicIntegralHeckeRing` for `@[expose]`.
@[expose, instance_reducible]
noncomputable def commRingPadicRationalHeckeRing (R : Type*) [CommRing R] :
    CommRing (𝕋 (⊤ : Submonoid (GL (Fin n) ℚ_[p])) (GLnZp n p) R) :=
  { (inferInstance : Ring (𝕋 (⊤ : Submonoid (GL (Fin n) ℚ_[p])) (GLnZp n p) R)) with
    mul_comm := mul_comm_padicRationalHeckeRing n p R }

end Commutativity

end HeckeRing.GLn

end
