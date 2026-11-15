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

import TauCeti.LinearAlgebra.Matrix.InvariantFactor
import TauCeti.LinearAlgebra.Matrix.SmithNormalForm.Basic
import TauCeti.NumberTheory.Padics.PadicIntegers
import TauCeti.NumberTheory.Padics.RingHoms

/-!
# Integral and rational `p`-adic `GL_n` Hecke rings and `p`-adic Smith normal form

For a prime `p`, let `GLnZp n p` be the image of `GL_n(ℤ_p)` inside `GL_n(ℚ_p)` and let
`padicIntEntries n p` be the submonoid `M_n(ℤ_p) ∩ GL_n(ℚ_p)` of invertible `p`-adic matrices
with integral `p`-adic entries. Following [Rhodes–Shemanske][rhodes1998] §3.1 and
[Rhodes–Shemanske][rhodes1999] §2, this file establishes:

1. The `p`-adic Smith normal form (`exists_padic_smith_normal_form` and
   `padic_smith_normal_form_unique`): every invertible matrix in `M_n(ℤ_p)` is
   `GL_n(ℤ_p)`-equivalent to `diag(p ^ e₁, …, p ^ eₙ)` for a unique monotone tuple `e : Fin n → ℕ`,
   and every matrix in `GL_n(ℚ_p)` is `GL_n(ℤ_p)`-equivalent to `diag(p ^ e₁, …, p ^ eₙ)` for a
   unique monotone tuple `e : Fin n → ℤ`.
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

* [J. A. Rhodes and T. R. Shemanske, *Lattices and Hecke operators over local fields*][rhodes1998],
  §3.1.
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

private theorem coeRingHom_injective : Function.Injective (PadicInt.Coe.ringHom (p := p)) :=
  fun _ _ h ↦ Subtype.ext h

/-- The canonical entrywise embedding `GL_n(ℤ_p) →* GL_n(ℚ_p)`. -/
noncomputable def mapGLPadicInt : GL (Fin n) ℤ_[p] →* GL (Fin n) ℚ_[p] :=
  Matrix.GeneralLinearGroup.map (PadicInt.Coe.ringHom (p := p))

/-- Matrix coercion of `mapGLPadicInt`. -/
@[simp]
theorem mapGLPadicInt_coe (u : GL (Fin n) ℤ_[p]) :
    (↑(mapGLPadicInt n p u) : Matrix (Fin n) (Fin n) ℚ_[p]) =
      (↑u : Matrix (Fin n) (Fin n) ℤ_[p]).map (PadicInt.Coe.ringHom (p := p)) := by
  ext i j; simp [mapGLPadicInt]

/-- `mapGLPadicInt` is injective because `ℤ_p ↪ ℚ_p` is injective. -/
theorem mapGLPadicInt_injective : Function.Injective (mapGLPadicInt n p) := by
  intro u v huv
  apply Units.ext
  exact Matrix.map_injective (coeRingHom_injective p) (by
    simpa only [mapGLPadicInt_coe] using congrArg Units.val huv)

/-- `GL_n(ℤ_p)` as a subgroup of `GL_n(ℚ_p)`, defined as the range of `mapGLPadicInt`. -/
noncomputable def GLnZp : Subgroup (GL (Fin n) ℚ_[p]) :=
  (mapGLPadicInt n p).range

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

/-- Matrix coercion of `castGLPadic`. -/
@[simp]
theorem castGLPadic_coe (g : GL (Fin n) ℚ) :
    (↑(castGLPadic n p g) : Matrix (Fin n) (Fin n) ℚ_[p]) =
      (↑g : Matrix (Fin n) (Fin n) ℚ).map (Rat.castHom ℚ_[p]) := by
  ext i j; simp [castGLPadic]

/-- `castGLPadic` is injective because `ℚ ↪ ℚ_p` is injective. -/
theorem castGLPadic_injective : Function.Injective (castGLPadic n p) := by
  intro g h gh
  apply Units.ext
  exact Matrix.map_injective (Rat.castHom ℚ_[p]).injective (by
    simpa only [castGLPadic_coe] using congrArg Units.val gh)

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
    exact (A i j).2
  · intro h
    exact ⟨Matrix.of fun i j ↦ ⟨(↑g : Matrix (Fin n) (Fin n) ℚ_[p]) i j, h i j⟩,
      by ext i j; rfl⟩

/-- The submonoid `M_n(ℤ_p) ∩ GL_n(ℚ_p)` of invertible matrices over `ℚ_p` with `ℤ_p`-entries. -/
def padicIntEntries : Submonoid (GL (Fin n) ℚ_[p]) where
  carrier := {g | HasPadicIntEntries n p g}
  one_mem' := ⟨1, by ext i j; simp [Matrix.one_apply]⟩
  mul_mem' := by
    rintro g h ⟨A, hA⟩ ⟨B, hB⟩
    refine ⟨A * B, ?_⟩
    rw [Units.val_mul, hA, hB, ← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply,
      ← map_mul, RingHom.mapMatrix_apply]

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
    have h1 : (1 : Matrix (Fin n) (Fin n) ℤ_[p]).map (PadicInt.Coe.ringHom (p := p)) = 1 := by
      ext i j; simp [Matrix.one_apply]
    have hAB : A * B = 1 := Matrix.map_injective (coeRingHom_injective p) (by
      have := congrArg Units.val (mul_inv_cancel g)
      rw [Units.val_mul, hA, hB, Units.val_one, ← h1, ← RingHom.mapMatrix_apply,
        ← RingHom.mapMatrix_apply, ← map_mul, RingHom.mapMatrix_apply] at this
      exact this)
    have hBA : B * A = 1 := Matrix.map_injective (coeRingHom_injective p) (by
      have := congrArg Units.val (inv_mul_cancel g)
      rw [Units.val_mul, hA, hB, Units.val_one, ← h1, ← RingHom.mapMatrix_apply,
        ← RingHom.mapMatrix_apply, ← map_mul, RingHom.mapMatrix_apply] at this
      exact this)
    exact ⟨⟨A, B, hAB, hBA⟩, Units.ext hA.symm⟩

private noncomputable def padicIntMatrixFun (g : padicIntEntries n p) :
    Matrix (Fin n) (Fin n) ℤ_[p] :=
  Classical.choose g.2

private theorem map_padicIntMatrixFun (g : padicIntEntries n p) :
    (padicIntMatrixFun n p g).map (PadicInt.Coe.ringHom (p := p)) =
      (↑(g : GL (Fin n) ℚ_[p]) : Matrix (Fin n) (Fin n) ℚ_[p]) :=
  (Classical.choose_spec g.2).symm

/-- The `ℤ_p`-matrix underlying an element of `padicIntEntries n p`, packaged as a monoid
homomorphism. -/
noncomputable def padicIntMatrix : padicIntEntries n p →* Matrix (Fin n) (Fin n) ℤ_[p] where
  toFun := padicIntMatrixFun n p
  map_one' := Matrix.map_injective (coeRingHom_injective p) (by
    dsimp only; rw [map_padicIntMatrixFun]; ext i j; simp [Matrix.one_apply])
  map_mul' g h := Matrix.map_injective (coeRingHom_injective p) (by
    dsimp only
    rw [map_padicIntMatrixFun, Submonoid.coe_mul, Units.val_mul,
      ← map_padicIntMatrixFun n p g, ← map_padicIntMatrixFun n p h]
    ext i j; simp [Matrix.mul_apply, Matrix.map_apply])

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
    fun h ↦ Matrix.map_injective (coeRingHom_injective p)
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
  rw [padicNatPowDiagGL, castGLPadic_coe, natDiagGL_coe n _ (primePowDiag_pos n p hp e)]
  ext i j; by_cases hij : i = j <;> simp [hij, primePowDiag_apply]

/-- Matrix coercion of `padicIntPowDiagGL`. -/
@[simp]
theorem padicIntPowDiagGL_coe (e : Fin n → ℤ) :
    (↑(padicIntPowDiagGL n p e) : Matrix (Fin n) (Fin n) ℚ_[p]) =
      Matrix.diagonal fun i ↦ (p : ℚ_[p]) ^ e i := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  rw [padicIntPowDiagGL, castGLPadic_coe, intPowDiagGL_coe n hp]
  ext i j; by_cases hij : i = j <;> simp [hij]

/-- On natural exponents, `padicIntPowDiagGL` agrees with `padicNatPowDiagGL`. -/
@[simp]
theorem padicIntPowDiagGL_natCast (e : Fin n → ℕ) :
    padicIntPowDiagGL n p (fun i ↦ (e i : ℤ)) = padicNatPowDiagGL n p e := by
  rw [padicIntPowDiagGL, intPowDiagGL_natCast, padicNatPowDiagGL]

/-- `padicNatPowDiagGL` at `0` is `1`. -/
@[simp]
theorem padicNatPowDiagGL_zero : padicNatPowDiagGL n p 0 = 1 := by
  have h0 : primePowDiag n p 0 = fun _ ↦ 1 := funext fun i ↦ by simp [primePowDiag_apply]
  rw [padicNatPowDiagGL, h0, natDiagGL_one, map_one]

/-- `padicIntPowDiagGL` at `0` is `1`. -/
@[simp]
theorem padicIntPowDiagGL_zero : padicIntPowDiagGL n p 0 = 1 := by
  rw [padicIntPowDiagGL, intPowDiagGL_zero, map_one]

/-- `padicIntPowDiagGL` converts addition of exponent tuples into matrix multiplication. -/
@[simp]
theorem padicIntPowDiagGL_add (e f : Fin n → ℤ) :
    padicIntPowDiagGL n p (e + f) = padicIntPowDiagGL n p e * padicIntPowDiagGL n p f := by
  rw [padicIntPowDiagGL, intPowDiagGL_add, map_mul]; rfl

/-- `padicIntPowDiagGL` converts negation of exponent tuples into group inversion. -/
@[simp]
theorem padicIntPowDiagGL_neg (e : Fin n → ℤ) :
    padicIntPowDiagGL n p (-e) = (padicIntPowDiagGL n p e)⁻¹ := by
  rw [padicIntPowDiagGL, intPowDiagGL_neg, map_inv]; rfl

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

end PadicDiagonal

section PadicSmithNormalForm

/-- **`p`-adic Smith normal form (existence)**: every matrix `A ∈ M_n(ℤ_p)` with `det A ≠ 0` is
`GL_n(ℤ_p)`-equivalent to `diag(p ^ e₁, …, p ^ eₙ)` for a monotone tuple `e : Fin n → ℕ`. -/
theorem exists_padic_smith_normal_form (A : Matrix (Fin n) (Fin n) ℤ_[p]) (hA : A.det ≠ 0) :
    ∃ (U₁ U₂ : GL (Fin n) ℤ_[p]) (e : Fin n → ℕ),
      Monotone e ∧
        (↑U₁ : Matrix (Fin n) (Fin n) ℤ_[p]) * A * (↑U₂ : Matrix (Fin n) (Fin n) ℤ_[p]) =
          Matrix.diagonal fun i ↦ (p : ℤ_[p]) ^ e i := by
  obtain ⟨L, Q, s, hL, hQ, hs_dvd, hLAQ⟩ :=
    Matrix.exists_smith_normal_form_of_isDiscreteValuationRing A
  have hs_ne : ∀ i, s i ≠ 0 := by
    intro i hi
    have hdet : (Matrix.diagonal s).det = 0 := by
      rw [Matrix.det_diagonal]; exact Finset.prod_eq_zero (Finset.mem_univ i) hi
    rw [← hLAQ, Matrix.det_mul, Matrix.det_mul] at hdet
    exact mul_ne_zero (mul_ne_zero hL.ne_zero hA) hQ.ne_zero hdet
  let u : Fin n → ℤ_[p]ˣ := fun i ↦ PadicInt.unitCoeff (hs_ne i)
  let e : Fin n → ℕ := fun i ↦ (s i).valuation
  have he_mono : Monotone e := by
    intro i j hij
    obtain ⟨c, hc⟩ := hs_dvd hij
    rw [← pow_dvd_pow_iff (PadicInt.irreducible_p (p := p)).ne_zero
      (PadicInt.irreducible_p (p := p)).not_isUnit]
    refine ⟨↑(u i) * c * ↑((u j)⁻¹), ?_⟩
    calc (p : ℤ_[p]) ^ e j
        = ↑((u j)⁻¹) * (↑(u j) * (p : ℤ_[p]) ^ e j) := by
          rw [← mul_assoc, Units.inv_mul, one_mul]
      _ = ↑((u j)⁻¹) * s j := by rw [← PadicInt.unitCoeff_spec (hs_ne j)]
      _ = ↑((u j)⁻¹) * (↑(u i) * (p : ℤ_[p]) ^ e i * c) := by
          rw [hc, PadicInt.unitCoeff_spec (hs_ne i)]
      _ = (p : ℤ_[p]) ^ e i * (↑(u i) * c * ↑((u j)⁻¹)) := by ring
  let UL : GL (Fin n) ℤ_[p] := Matrix.nonsingInvUnit L hL
  let UD : GL (Fin n) ℤ_[p] := TauCeti.diagGL fun i ↦ (u i)⁻¹
  let UQ : GL (Fin n) ℤ_[p] := Matrix.nonsingInvUnit Q hQ * UD
  refine ⟨UL, UQ, e, he_mono, ?_⟩
  have hUL : (↑UL : Matrix (Fin n) (Fin n) ℤ_[p]) = L := rfl
  have hUQ : (↑UQ : Matrix (Fin n) (Fin n) ℤ_[p]) = Q * (↑UD : Matrix (Fin n) (Fin n) ℤ_[p]) :=
    Units.val_mul _ _
  rw [hUL, hUQ, ← Matrix.mul_assoc, hLAQ, TauCeti.diagGL_coe, Matrix.diagonal_mul_diagonal]
  congr 1; funext i
  rw [PadicInt.unitCoeff_spec (hs_ne i), mul_right_comm, Units.mul_inv, one_mul]

/-- **`p`-adic Smith normal form (uniqueness)**: the monotone `p`-power exponent tuple of a matrix
in `M_n(ℤ_p)` is uniquely determined by its `GL_n(ℤ_p)` double coset. -/
theorem padic_smith_normal_form_unique {e₁ e₂ : Fin n → ℕ} (he₁ : Monotone e₁) (he₂ : Monotone e₂)
    (U₁ U₂ : GL (Fin n) ℤ_[p])
    (h : (↑U₁ : Matrix (Fin n) (Fin n) ℤ_[p]) * (Matrix.diagonal fun i ↦ (p : ℤ_[p]) ^ e₁ i) *
        (↑U₂ : Matrix (Fin n) (Fin n) ℤ_[p]) = Matrix.diagonal fun i ↦ (p : ℤ_[p]) ^ e₂ i) :
    e₁ = e₂ := by
  let d₁ : Fin n → ℤ_[p] := fun i ↦ (p : ℤ_[p]) ^ e₁ i
  let d₂ : Fin n → ℤ_[p] := fun i ↦ (p : ℤ_[p]) ^ e₂ i
  have hc₁ : ∀ ⦃i j : Fin n⦄, i ≤ j → d₁ i ∣ d₁ j := fun _ _ hij ↦ pow_dvd_pow _ (he₁ hij)
  have hc₂ : ∀ ⦃i j : Fin n⦄, i ≤ j → d₂ i ∣ d₂ j := fun _ _ hij ↦ pow_dvd_pow _ (he₂ hij)
  have hU₁ : IsUnit (↑U₁ : Matrix (Fin n) (Fin n) ℤ_[p]).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp U₁.isUnit
  have hU₂ : IsUnit (↑U₂ : Matrix (Fin n) (Fin n) ℤ_[p]).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp U₂.isUnit
  have h1 : IsUnit (1 : Matrix (Fin n) (Fin n) ℤ_[p]).det := by
    rw [Matrix.det_one]; exact isUnit_one
  have hid : (1 : Matrix (Fin n) (Fin n) ℤ_[p]) * Matrix.diagonal d₁ * 1 = Matrix.diagonal d₁ := by
    rw [Matrix.one_mul, Matrix.mul_one]
  have hp_dvd := fun {a b : ℕ} ↦ pow_dvd_pow_iff (n := a) (m := b)
    (PadicInt.irreducible_p (p := p)).ne_zero (PadicInt.irreducible_p (p := p)).not_isUnit
  have hsum : ∀ (k : ℕ) (hk : k ≤ n),
      ∑ j : Fin k, e₁ (Fin.castLE hk j) = ∑ j : Fin k, e₂ (Fin.castLE hk j) := by
    intro k hk
    have hdvd₁ : (∏ j : Fin k, d₁ (Fin.castLE hk j)) ∣ ∏ j : Fin k, d₂ (Fin.castLE hk j) :=
      Matrix.dvd_prod_of_mul_mul_eq_diagonal h hk fun f g ↦
        Matrix.prod_dvd_det_submatrix_of_mul_mul_eq_diagonal h1 h1 hc₁ hid hk f g
    have hdvd₂ : (∏ j : Fin k, d₂ (Fin.castLE hk j)) ∣ ∏ j : Fin k, d₁ (Fin.castLE hk j) := by
      rw [← Matrix.det_submatrix_diagonal d₁ (Fin.castLE_injective hk)]
      exact Matrix.prod_dvd_det_submatrix_of_mul_mul_eq_diagonal hU₁ hU₂ hc₂ h hk _ _
    simp only [d₁, d₂, Finset.prod_pow_eq_pow_sum] at hdvd₁ hdvd₂
    exact le_antisymm (hp_dvd.mp hdvd₁) (hp_dvd.mp hdvd₂)
  funext ⟨i, hi⟩
  have hs₁ := hsum (i + 1) hi
  have hs₀ := hsum i (Nat.le_of_lt hi)
  rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc] at hs₁
  have hcast₁ : (∑ x : Fin i, e₁ (Fin.castLE hi x.castSucc)) =
      ∑ j : Fin i, e₁ (Fin.castLE (Nat.le_of_lt hi) j) := rfl
  have hcast₂ : (∑ x : Fin i, e₂ (Fin.castLE hi x.castSucc)) =
      ∑ j : Fin i, e₂ (Fin.castLE (Nat.le_of_lt hi) j) := rfl
  rw [hcast₁, hcast₂, hs₀] at hs₁
  exact add_left_cancel hs₁

/-- Every `g ∈ padicIntEntries n p` lies in the `GL_n(ℤ_p)` double coset of
`padicNatPowDiagGL n p e` for a monotone tuple `e : Fin n → ℕ`. -/
theorem exists_padicNatPowDiagGL_mem_doubleCoset {g : GL (Fin n) ℚ_[p]}
    (hg : g ∈ padicIntEntries n p) :
    ∃ e : Fin n → ℕ, Monotone e ∧
      g ∈ doubleCoset (padicNatPowDiagGL n p e) (GLnZp n p) (GLnZp n p) := by
  let A := padicIntMatrix n p ⟨g, hg⟩
  obtain ⟨U₁, U₂, e, he, hU⟩ := exists_padic_smith_normal_form n p A
    (det_padicIntMatrix_ne_zero n p ⟨g, hg⟩)
  refine ⟨e, he, DoubleCoset.mem_doubleCoset.mpr
    ⟨mapGLPadicInt n p U₁⁻¹, mapGLPadicInt_mem_GLnZp n p _,
     mapGLPadicInt n p U₂⁻¹, mapGLPadicInt_mem_GLnZp n p _, ?_⟩⟩
  apply Units.ext
  have hmap := congrArg (Matrix.map · (PadicInt.Coe.ringHom (p := p))) hU
  rw [← RingHom.mapMatrix_apply, map_mul, map_mul, RingHom.mapMatrix_apply,
    RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, map_padicIntMatrix] at hmap
  have hdiag : (Matrix.diagonal fun i ↦ (p : ℤ_[p]) ^ e i).map (PadicInt.Coe.ringHom (p := p)) =
      (↑(padicNatPowDiagGL n p e) : Matrix _ _ ℚ_[p]) := by
    rw [padicNatPowDiagGL_coe]; ext i j; by_cases hij : i = j <;> simp [hij]
  rw [hdiag] at hmap
  have hgl : mapGLPadicInt n p U₁ * g * mapGLPadicInt n p U₂ = padicNatPowDiagGL n p e :=
    Units.ext (by simpa only [Units.val_mul, mapGLPadicInt_coe] using hmap)
  rw [← hgl]; simp [mul_assoc]

/-- Distinct monotone tuples `e₁, e₂ : Fin n → ℕ` define disjoint `GL_n(ℤ_p)` double cosets. -/
theorem padicNatPowDiagGL_eq_of_mem_doubleCoset {e₁ e₂ : Fin n → ℕ}
    (he₁ : Monotone e₁) (he₂ : Monotone e₂)
    (h : padicNatPowDiagGL n p e₂ ∈
      doubleCoset (padicNatPowDiagGL n p e₁) (GLnZp n p) (GLnZp n p)) :
    e₁ = e₂ := by
  obtain ⟨u₁, ⟨U₁, rfl⟩, u₂, ⟨U₂, rfl⟩, hu⟩ := DoubleCoset.mem_doubleCoset.mp h
  apply padic_smith_normal_form_unique n p he₁ he₂ U₁ U₂
  apply Matrix.map_injective (coeRingHom_injective p)
  have hval := congrArg Units.val hu.symm
  simp only [Units.val_mul, mapGLPadicInt_coe] at hval
  have hdiag₁ : (↑(padicNatPowDiagGL n p e₁) : Matrix _ _ ℚ_[p]) =
      (Matrix.diagonal fun i ↦ (p : ℤ_[p]) ^ e₁ i).map (PadicInt.Coe.ringHom (p := p)) := by
    rw [padicNatPowDiagGL_coe]; ext i j; by_cases hij : i = j <;> simp [hij]
  have hdiag₂ : (↑(padicNatPowDiagGL n p e₂) : Matrix _ _ ℚ_[p]) =
      (Matrix.diagonal fun i ↦ (p : ℤ_[p]) ^ e₂ i).map (PadicInt.Coe.ringHom (p := p)) := by
    rw [padicNatPowDiagGL_coe]; ext i j; by_cases hij : i = j <;> simp [hij]
  rw [hdiag₁, hdiag₂, ← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply,
    ← RingHom.mapMatrix_apply, ← map_mul, ← map_mul] at hval
  exact hval

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
  have hcomm : padicNatPowDiagGL n p (fun _ ↦ k) * u₁ =
      u₁ * padicNatPowDiagGL n p (fun _ ↦ k) := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, padicNatPowDiagGL_coe]
    ext i j
    simp [Matrix.diagonal_mul, Matrix.mul_diagonal, mul_comm]
  have hsub : (fun i : Fin n ↦ (e' i : ℤ) - k) =
      (fun _ ↦ -(k : ℤ)) + (fun i ↦ (e' i : ℤ)) := funext fun i ↦ sub_eq_neg_add _ _
  have hneg : padicIntPowDiagGL n p (fun _ ↦ -(k : ℤ)) =
      (padicNatPowDiagGL n p (fun _ ↦ k))⁻¹ := by
    rw [show (fun _ : Fin n ↦ -(k : ℤ)) = -(fun _ ↦ (k : ℤ)) from rfl,
      padicIntPowDiagGL_neg, padicIntPowDiagGL_natCast]
  calc g = (padicNatPowDiagGL n p (fun _ ↦ k))⁻¹ *
        (padicNatPowDiagGL n p (fun _ ↦ k) * g) := by simp
    _ = (padicNatPowDiagGL n p (fun _ ↦ k))⁻¹ *
        (u₁ * padicNatPowDiagGL n p e' * u₂) := by rw [hmul]
    _ = u₁ * ((padicNatPowDiagGL n p (fun _ ↦ k))⁻¹ * padicNatPowDiagGL n p e') * u₂ := by
        simp only [← mul_assoc]
        congr 1; congr 1
        rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, hcomm, mul_inv_cancel_right]
    _ = u₁ * padicIntPowDiagGL n p (fun i ↦ (e' i : ℤ) - k) * u₂ := by
        rw [hsub, padicIntPowDiagGL_add, hneg, padicIntPowDiagGL_natCast]

/-- Distinct monotone tuples `e₁, e₂ : Fin n → ℤ` define disjoint `GL_n(ℤ_p)` double cosets. -/
theorem padicIntPowDiagGL_eq_of_mem_doubleCoset {e₁ e₂ : Fin n → ℤ}
    (he₁ : Monotone e₁) (he₂ : Monotone e₂)
    (h : padicIntPowDiagGL n p e₂ ∈
      doubleCoset (padicIntPowDiagGL n p e₁) (GLnZp n p) (GLnZp n p)) :
    e₁ = e₂ := by
  let M : ℕ := Finset.univ.sup fun i ↦ max (-e₁ i).toNat (-e₂ i).toNat
  let f₁ : Fin n → ℕ := fun i ↦ (e₁ i + M).toNat
  let f₂ : Fin n → ℕ := fun i ↦ (e₂ i + M).toNat
  have hf₁_eq : ∀ i, (f₁ i : ℤ) = e₁ i + M := fun i ↦ by
    have : (-e₁ i).toNat ≤ M := le_trans (le_max_left _ _)
      (Finset.le_sup (f := fun i ↦ max (-e₁ i).toNat (-e₂ i).toNat) (Finset.mem_univ i))
    exact Int.toNat_of_nonneg (by omega)
  have hf₂_eq : ∀ i, (f₂ i : ℤ) = e₂ i + M := fun i ↦ by
    have : (-e₂ i).toNat ≤ M := le_trans (le_max_right _ _)
      (Finset.le_sup (f := fun i ↦ max (-e₁ i).toNat (-e₂ i).toNat) (Finset.mem_univ i))
    exact Int.toNat_of_nonneg (by omega)
  have hf₁_mono : Monotone f₁ := fun i j hij ↦ by
    rw [← Int.ofNat_le, hf₁_eq, hf₁_eq]; linarith [he₁ hij]
  have hf₂_mono : Monotone f₂ := fun i j hij ↦ by
    rw [← Int.ofNat_le, hf₂_eq, hf₂_eq]; linarith [he₂ hij]
  obtain ⟨u₁, hu₁, u₂, hu₂, hmul⟩ := DoubleCoset.mem_doubleCoset.mp h
  have hcomm : padicIntPowDiagGL n p (fun _ ↦ (M : ℤ)) * u₁ =
      u₁ * padicIntPowDiagGL n p (fun _ ↦ (M : ℤ)) := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, padicIntPowDiagGL_coe]
    ext i j
    simp [Matrix.diagonal_mul, Matrix.mul_diagonal, mul_comm]
  have hshift : padicNatPowDiagGL n p f₂ ∈
      doubleCoset (padicNatPowDiagGL n p f₁) (GLnZp n p) (GLnZp n p) := by
    refine DoubleCoset.mem_doubleCoset.mpr ⟨u₁, hu₁, u₂, hu₂, ?_⟩
    rw [← padicIntPowDiagGL_natCast, ← padicIntPowDiagGL_natCast,
      show (fun i ↦ (f₂ i : ℤ)) = (fun _ ↦ (M : ℤ)) + e₂ from funext fun i ↦ by
        rw [hf₂_eq, Pi.add_apply, add_comm],
      show (fun i ↦ (f₁ i : ℤ)) = (fun _ ↦ (M : ℤ)) + e₁ from funext fun i ↦ by
        rw [hf₁_eq, Pi.add_apply, add_comm],
      padicIntPowDiagGL_add, padicIntPowDiagGL_add, hmul]
    simp only [← mul_assoc, hcomm]
  have hfeq := padicNatPowDiagGL_eq_of_mem_doubleCoset n p hf₁_mono hf₂_mono hshift
  funext i
  have := congrArg (fun f : Fin n → ℕ ↦ (f i : ℤ)) hfeq
  linarith [hf₁_eq i, hf₂_eq i]

end PadicSmithNormalForm

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
    rw [← padicIntPowDiagGL_neg, Units.val_mul, Units.val_mul,
      padicIntPowDiagGL_coe, padicIntPowDiagGL_coe, mapGLPadicInt_coe]
    rfl
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
    exact ((↑u : Matrix (Fin n) (Fin n) ℤ_[p]) i i).2
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
    exact ((p : ℤ_[p]) ^ E * c).2

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
    have hH : H = Subgroup.map (mapGLPadicInt n p) ⊤ := by simp [H, GLnZp, MonoidHom.range_eq_map]
    rw [hH, Subgroup.relIndex_map_map_of_injective _ _ (mapGLPadicInt_injective n p),
      Subgroup.relIndex_top_right]
    exact (Subgroup.finiteIndex_ker φ).index_ne_zero
  set g := padicIntPowDiagGL n p e
  have hK_le_gH : K ≤ MulAut.conj g • H := congruence_ker_le_conj_padicIntPowDiagGL n p hM
  have hK_le_ginvH : K ≤ MulAut.conj g⁻¹ • H := by
    rw [show g⁻¹ = padicIntPowDiagGL n p (-e) by simp [g]]
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

private theorem mem_commensurator_of_mem {G : Type*} [Group G] {H : Subgroup G} {u : G}
    (hu : u ∈ H) : u ∈ commensurator H := by
  rw [commensurator_mem_iff]
  have hconj : MulAut.conj u • H = H := by
    ext x
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, MulAut.smul_def, MulAut.conj_inv_apply]
    exact ⟨fun hx ↦ by simpa [mul_assoc] using H.mul_mem hu (H.mul_mem hx (H.inv_mem hu)),
      fun hx ↦ by simpa [mul_assoc] using H.mul_mem (H.inv_mem hu) (H.mul_mem hx hu)⟩
  rw [hconj]

/-- **The commensurator of `GL_n(ℤ_p)` in `GL_n(ℚ_p)` is the whole group `GL_n(ℚ_p)`.** -/
theorem commensurator_GLnZp_eq_top : commensurator (GLnZp n p) = ⊤ := by
  rw [Subgroup.eq_top_iff']
  intro g
  obtain ⟨e, -, hcos⟩ := exists_padicIntPowDiagGL_mem_doubleCoset n p g
  obtain ⟨u₁, hu₁, u₂, hu₂, rfl⟩ := DoubleCoset.mem_doubleCoset.mp hcos
  exact (commensurator (GLnZp n p)).mul_mem
    ((commensurator (GLnZp n p)).mul_mem (mem_commensurator_of_mem hu₁)
      (padicIntPowDiagGL_mem_commensurator_GLnZp n p e))
    (mem_commensurator_of_mem hu₂)

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
  Equiv.ofBijective (fun e ↦ padicNatPowDiagCoset n p e.1) ⟨by
    rintro ⟨e₁, he₁⟩ ⟨e₂, he₂⟩ h
    apply Subtype.ext
    have hset := congrArg HeckeCoset.toSet h
    dsimp only at hset
    rw [padicNatPowDiagCoset_def, padicNatPowDiagCoset_def,
      HeckeCoset.toSet_mk, HeckeCoset.toSet_mk] at hset
    exact (padicNatPowDiagGL_eq_of_mem_doubleCoset n p he₂ he₁
      (hset ▸ DoubleCoset.mem_doubleCoset_self _ _ _)).symm,
    fun D ↦ by
      obtain ⟨e, he, hmem⟩ := exists_padicNatPowDiagGL_mem_doubleCoset n p D.rep.2
      refine ⟨⟨e, he⟩, ?_⟩
      dsimp only
      rw [padicNatPowDiagCoset_def]
      exact ((HeckeCoset.mk_eq_mk_of_mem hmem).symm).trans (HeckeCoset.mk_rep D)⟩

/-- `padicNatPowDiagCosetEquiv` sends a monotone tuple `e` to `padicNatPowDiagCoset n p e`. -/
@[simp]
theorem padicNatPowDiagCosetEquiv_apply (e : {e : Fin n → ℕ // Monotone e}) :
    padicNatPowDiagCosetEquiv n p e = padicNatPowDiagCoset n p e.1 := (rfl)

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
  Equiv.ofBijective (fun e ↦ padicIntPowDiagCoset n p e.1) ⟨by
    rintro ⟨e₁, he₁⟩ ⟨e₂, he₂⟩ h
    apply Subtype.ext
    have hset := congrArg HeckeCoset.toSet h
    dsimp only at hset
    rw [padicIntPowDiagCoset_def, padicIntPowDiagCoset_def,
      HeckeCoset.toSet_mk, HeckeCoset.toSet_mk] at hset
    exact (padicIntPowDiagGL_eq_of_mem_doubleCoset n p he₂ he₁
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
    padicIntPowDiagCosetEquiv n p e = padicIntPowDiagCoset n p e.1 := (rfl)

/-- **Rank-`1` integral `p`-adic cosets**: in rank `n = 1`, the double cosets of
`(M_1(ℤ_p) ∩ GL_1(ℚ_p), GL_1(ℤ_p))` biject canonically with `ℕ` via
`k ↦ [GL_1(ℤ_p) · p ^ k · GL_1(ℤ_p)]`. -/
noncomputable def padicIntegralCosetEquivNat :
    ℕ ≃ HeckeCoset (padicIntEntries 1 p) (GLnZp 1 p) (GLnZp 1 p) :=
  (Equiv.mk (fun k : ℕ ↦ (⟨fun _ ↦ k, monotone_const⟩ : {e : Fin 1 → ℕ // Monotone e}))
    (fun e ↦ e.1 0) (fun _ ↦ rfl)
    (fun e ↦ Subtype.ext (funext fun i ↦ congrArg e.1 (Subsingleton.elim 0 i)))).trans
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
    (fun e ↦ e.1 0) (fun _ ↦ rfl)
    (fun e ↦ Subtype.ext (funext fun i ↦ congrArg e.1 (Subsingleton.elim 0 i)))).trans
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
  change (padicIntegralTransposeAntiInvolution n p).onHeckeCoset (padicNatPowDiagCoset n p e) = _
  rw [padicNatPowDiagCoset_def, (padicIntegralTransposeAntiInvolution n p).onHeckeCoset_mk]
  exact congrArg (HeckeCoset.mk (GLnZp n p) (GLnZp n p))
    (Subtype.ext ((padicIntegralTransposeAntiInvolution_bar n p _).trans
      (Units.ext (by simp [padicNatPowDiagGL_coe]))))

/-- Transposition fixes every rational `p`-adic Hecke double coset. -/
@[simp]
theorem padicRationalTransposeAntiInvolution_onHeckeCoset_eq_self
    (D : HeckeCoset (⊤ : Submonoid (GL (Fin n) ℚ_[p])) (GLnZp n p) (GLnZp n p)) :
    (padicRationalTransposeAntiInvolution n p).onHeckeCoset D = D := by
  obtain ⟨⟨e, -⟩, rfl⟩ := (padicIntPowDiagCosetEquiv n p).surjective D
  change (padicRationalTransposeAntiInvolution n p).onHeckeCoset (padicIntPowDiagCoset n p e) = _
  rw [padicIntPowDiagCoset_def, (padicRationalTransposeAntiInvolution n p).onHeckeCoset_mk]
  exact congrArg (HeckeCoset.mk (GLnZp n p) (GLnZp n p))
    (Subtype.ext ((padicRationalTransposeAntiInvolution_bar n p _).trans
      (Units.ext (by simp [padicIntPowDiagGL_coe]))))

/-- Multiplication in `𝕋 (padicIntEntries n p) (GLnZp n p) R` is commutative over any commutative
semiring `R`. -/
theorem mul_comm_padicIntegralHecke (R : Type*) [CommSemiring R]
    (f g : 𝕋 (padicIntEntries n p) (GLnZp n p) R) : f * g = g * f :=
  HeckeCosetModule.mul_comm_of_antiInvolution R (padicIntegralTransposeAntiInvolution n p)
    (padicIntegralTransposeAntiInvolution_onHeckeCoset_eq_self n p) f g

/-- Commutativity of `𝕋 (padicIntEntries n p) (GLnZp n p) R` over any commutative semiring `R`. -/
@[instance_reducible]
noncomputable def commSemiringPadicIntegralHecke (R : Type*) [CommSemiring R] :
    CommSemiring (𝕋 (padicIntEntries n p) (GLnZp n p) R) :=
  { HeckeCosetModule.instSemiringHeckeRing R with
    mul_comm := mul_comm_padicIntegralHecke n p R }

/-- Commutativity of `PadicIntegralHeckeRing n p`, extending its `Ring` instance without a `Mul`
diamond. -/
@[expose, instance_reducible]
noncomputable def commRingPadicIntegralHeckeRing : CommRing (PadicIntegralHeckeRing n p) :=
  { (inferInstance : Ring (PadicIntegralHeckeRing n p)) with
    mul_comm := mul_comm_padicIntegralHecke n p ℤ }

/-- Multiplication in `𝕋 ⊤ (GLnZp n p) R` is commutative over any commutative semiring `R`. -/
theorem mul_comm_padicRationalHecke (R : Type*) [CommSemiring R]
    (f g : 𝕋 (⊤ : Submonoid (GL (Fin n) ℚ_[p])) (GLnZp n p) R) : f * g = g * f :=
  HeckeCosetModule.mul_comm_of_antiInvolution R (padicRationalTransposeAntiInvolution n p)
    (padicRationalTransposeAntiInvolution_onHeckeCoset_eq_self n p) f g

/-- Commutativity of `𝕋 ⊤ (GLnZp n p) R` over any commutative semiring `R`. -/
@[instance_reducible]
noncomputable def commSemiringPadicRationalHecke (R : Type*) [CommSemiring R] :
    CommSemiring (𝕋 (⊤ : Submonoid (GL (Fin n) ℚ_[p])) (GLnZp n p) R) :=
  { HeckeCosetModule.instSemiringHeckeRing R with
    mul_comm := mul_comm_padicRationalHecke n p R }

/-- Commutativity of `PadicRationalHeckeRing n p`, extending its `Ring` instance without a `Mul`
diamond. -/
@[expose, instance_reducible]
noncomputable def commRingPadicRationalHeckeRing : CommRing (PadicRationalHeckeRing n p) :=
  { (inferInstance : Ring (PadicRationalHeckeRing n p)) with
    mul_comm := mul_comm_padicRationalHecke n p ℤ }

end Commutativity

end HeckeRing.GLn

end
