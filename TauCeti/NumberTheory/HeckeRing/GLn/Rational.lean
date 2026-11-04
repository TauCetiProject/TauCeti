/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Diagonal.Basic
public import TauCeti.NumberTheory.HeckeRing.GLn.TransposeAntiInvolution
public import TauCeti.NumberTheory.HeckeRing.Map.SubgroupExtension

import Mathlib.Algebra.Ring.Int.Units
import Mathlib.Tactic.Group
import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Basic

/-!
# Rational and full `GL_n` Hecke rings and the global comparison chain

Following Proposition 3.16 of [Shimura][shimura1971] and §2 of [Rhodes–Shemanske][rhodes1999], this
file constructs the rational Hecke triples `(SL_n(ℤ), GL_n^+(ℚ))` and `(GL_n(ℤ), GL_n(ℚ))` inside
`GL_n(ℚ)`, proves their commutativity, and establishes the global comparison chain

`IntegralHeckeRing n ↪ RationalHeckeRing n ≃+* FullHeckeRing n`

(over `ℤ`, and more generally over any coefficient semiring `R`).

Every element of `GL_n(ℚ)` clears denominators under multiplication by a positive scalar matrix
`diag(c, …, c)` (`exists_pos_natDiagGL_mul_mem_intEntries`). Together with Shimura's Lemma 3.10
(`mem_commensurator_of_hasIntEntries`), this forces `commensurator (SL_n(ℤ)) = ⊤` and, by finite
index of `SL_n(ℤ)` in `GL_n(ℤ)`, `commensurator (GL_n(ℤ)) = ⊤`. Enlarging the submonoid from
`posDetInt n` to `GL_n^+(ℚ)` gives the injective ring homomorphism `integralToRationalRingHom`,
while applying `HeckeCosetModule.mapSubgroupRingEquiv` to `SL_n(ℤ) = GL_n(ℤ) ⊓ GL_n^+(ℚ)` gives the
ring isomorphism `rationalToFullRingEquiv`. To verify the stabilizer coset condition on `GL_n^+(ℚ)`,
one clears denominators and puts the resulting integral matrix in Smith normal form `γ₁ · D · γ₂`
(`γ₁, γ₂ ∈ SL_n(ℤ)`), so conjugating `diag(-1, 1, …, 1)` by `γ₁` produces a determinant-`-1` element
of `GL_n(ℤ) ∩ g · GL_n(ℤ) · g⁻¹`.

The file also records how negation `-I_n` interacts with double cosets in the two groups: `-I_n`
always lies in `GL_n(ℤ)` (`doubleCoset_neg_GLnZ`), whereas `-I_n ∈ SL_n(ℤ)` and
`-g ∈ SL_n(ℤ) g SL_n(ℤ)` hold if and only if `n` is even (`neg_one_mem_SLnZ_iff`,
`neg_mem_doubleCoset_SLnZ_iff`).

## Main definitions

* `HeckeRing.GLn.GLnZ`: `GL_n(ℤ)` embedded as a subgroup of `GL_n(ℚ)` via
  `Matrix.GeneralLinearGroup.map (Int.castRingHom ℚ)`.
* `HeckeRing.GLn.RationalHeckeRing`, `HeckeRing.GLn.FullHeckeRing`: the Hecke rings of
  `(SL_n(ℤ), GL_n^+(ℚ))` and `(GL_n(ℤ), GL_n(ℚ))` over `ℤ`.
* `HeckeRing.GLn.integralToRationalRingHom`, `HeckeRing.GLn.integralToRational`: the injective
  embedding `𝕋 (posDetInt n) (SLnZ n) R →+* 𝕋 (GLPos (Fin n) ℚ).toSubmonoid (SLnZ n) R`.
* `HeckeRing.GLn.rationalToFullRingEquiv`, `HeckeRing.GLn.rationalToFullEquiv`: the ring isomorphism
  `𝕋 (GLPos (Fin n) ℚ).toSubmonoid (SLnZ n) R ≃+* 𝕋 ⊤ (GLnZ n) R`.
* `HeckeRing.GLn.commSemiringRationalHeckeRing`, `HeckeRing.GLn.commRingRationalHeckeRing`,
  `HeckeRing.GLn.commSemiringFullHeckeRing`, `HeckeRing.GLn.commRingFullHeckeRing`: commutativity of
  both rational Hecke rings.

## Main results

* `HeckeRing.GLn.SLnZ_eq_GLnZ_inf_glpos`: `SL_n(ℤ) = GL_n(ℤ) ⊓ GL_n^+(ℚ)`.
* `HeckeRing.GLn.neg_one_mem_SLnZ_iff`, `HeckeRing.GLn.neg_mem_doubleCoset_SLnZ_iff`,
  `HeckeRing.GLn.doubleCoset_neg_GLnZ`: parity behavior of `-I_n` on double cosets.
* `HeckeRing.GLn.exists_pos_natDiagGL_mul_mem_intEntries`,
  `HeckeRing.GLn.exists_pos_natDiagGL_mul_mem_posDetInt`: clearing denominators by a positive scalar
  matrix.
* `HeckeRing.GLn.commensurator_SLnZ_eq_top`, `HeckeRing.GLn.commensurator_GLnZ_eq_top`: both
  arithmetic subgroups have commensurator all of `GL_n(ℚ)`.

## References

* [G. Shimura, *Introduction to the arithmetic theory of automorphic functions*][shimura1971],
  Proposition 3.16.
* [J. A. Rhodes and T. R. Shemanske,
  *Rationality theorems for Hecke operators on GL_n*][rhodes1999], §2.
-/

public section

open Matrix Subgroup.Commensurable DoubleCoset Matrix.SpecialLinearGroup
open scoped Pointwise HeckeCosetModule

namespace HeckeRing.GLn

variable (n : ℕ)

section GLnZ

/-- `GL_n(ℤ)` as a subgroup of `GL_n(ℚ)`, embedded entrywise via
`Matrix.GeneralLinearGroup.map (Int.castRingHom ℚ)`. -/
noncomputable def GLnZ : Subgroup (GL (Fin n) ℚ) :=
  (Matrix.GeneralLinearGroup.map (Int.castRingHom ℚ) :
    GL (Fin n) ℤ →* GL (Fin n) ℚ).range

/-- Canonical membership of an integral invertible matrix in `GLnZ n`. -/
theorem map_intCast_mem_GLnZ (γ : GL (Fin n) ℤ) :
    Matrix.GeneralLinearGroup.map (Int.castRingHom ℚ) γ ∈ GLnZ n :=
  ⟨γ, rfl⟩

/-- Membership in `GLnZ n` characterised by an integral `GL_n(ℤ)` witness. -/
@[simp]
theorem mem_GLnZ_iff {g : GL (Fin n) ℚ} :
    g ∈ GLnZ n ↔
      ∃ γ : GL (Fin n) ℤ, Matrix.GeneralLinearGroup.map (Int.castRingHom ℚ) γ = g := by
  rw [GLnZ, MonoidHom.mem_range]

/-- Every element of `GL_n(ℤ)` has integer matrix entries. -/
theorem hasIntEntries_of_mem_GLnZ {g : GL (Fin n) ℚ} (hg : g ∈ GLnZ n) :
    HasIntEntries n g := by
  obtain ⟨γ, rfl⟩ := (mem_GLnZ_iff n).mp hg
  refine (hasIntEntries_iff n).mpr ⟨(γ : Matrix (Fin n) (Fin n) ℤ), ?_⟩
  ext i j
  simp [Matrix.GeneralLinearGroup.map_apply]

/-- `GL_n(ℤ)` lies in the integral-entry submonoid `intEntries n`. -/
theorem GLnZ_le_intEntries : (GLnZ n).toSubmonoid ≤ intEntries n :=
  fun _ hg ↦ (mem_intEntries n).mpr (hasIntEntries_of_mem_GLnZ n hg)

/-- Every element of `GL_n(ℤ)` has rational determinant `1` or `-1`. -/
theorem det_eq_one_or_neg_one_of_mem_GLnZ {g : GL (Fin n) ℚ} (hg : g ∈ GLnZ n) :
    (↑g : Matrix (Fin n) (Fin n) ℚ).det = 1 ∨
      (↑g : Matrix (Fin n) (Fin n) ℚ).det = -1 := by
  obtain ⟨γ, rfl⟩ := (mem_GLnZ_iff n).mp hg
  have hdet :
      ((Matrix.GeneralLinearGroup.map (Int.castRingHom ℚ) γ : GL (Fin n) ℚ) :
          Matrix (Fin n) (Fin n) ℚ).det =
        ((Matrix.GeneralLinearGroup.det γ : ℤˣ) : ℤ) := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.map_det]
    rfl
  rw [hdet]
  rcases Int.units_eq_one_or (Matrix.GeneralLinearGroup.det γ) with h | h <;> simp [h]

/-- Entrywise and determinant characterization of `GL_n(ℤ)` inside `GL_n(ℚ)`: an invertible rational
matrix belongs to `GL_n(ℤ)` if and only if it has integer entries and determinant `±1`. -/
theorem mem_GLnZ_iff_hasIntEntries_and_det {g : GL (Fin n) ℚ} :
    g ∈ GLnZ n ↔
      HasIntEntries n g ∧
        ((↑g : Matrix (Fin n) (Fin n) ℚ).det = 1 ∨
          (↑g : Matrix (Fin n) (Fin n) ℚ).det = -1) := by
  refine ⟨fun hg ↦ ⟨hasIntEntries_of_mem_GLnZ n hg, det_eq_one_or_neg_one_of_mem_GLnZ n hg⟩, ?_⟩
  rintro ⟨hint, hdet⟩
  obtain ⟨A, hA⟩ := (hasIntEntries_iff n).mp hint
  have hAdet_cast : (A.det : ℚ) = (↑g : Matrix (Fin n) (Fin n) ℚ).det := by
    rw [hA]
    simpa [RingHom.mapMatrix_apply] using RingHom.map_det (Int.castRingHom ℚ) A
  have hAunit : IsUnit A.det := by
    rcases hdet with h1 | h1
    · have hA1 : A.det = 1 := by exact_mod_cast hAdet_cast.trans h1
      exact hA1 ▸ isUnit_one
    · have hA1 : A.det = -1 := by exact_mod_cast hAdet_cast.trans h1
      exact hA1 ▸ IsUnit.neg isUnit_one
  refine (mem_GLnZ_iff n).mpr ⟨Matrix.nonsingInvUnit A hAunit, Units.ext ?_⟩
  ext i j
  simpa [Matrix.GeneralLinearGroup.map_apply, Matrix.nonsingInvUnit] using
    (congrFun (congrFun hA i) j).symm

/-- `SL_n(ℤ)` is the positive-determinant part of `GL_n(ℤ)`: `SL_n(ℤ) = GL_n(ℤ) ⊓ GL_n^+(ℚ)`. -/
theorem SLnZ_eq_GLnZ_inf_glpos :
    SLnZ n = GLnZ n ⊓ Matrix.GLPos (Fin n) ℚ := by
  ext g
  rw [Subgroup.mem_inf]
  constructor
  · intro hg
    refine ⟨?_, SLnZ_le_glpos n hg⟩
    obtain ⟨σ, rfl⟩ := (mem_SLnZ_iff n).mp hg
    refine (mem_GLnZ_iff n).mpr ⟨σ.toGL, Units.ext ?_⟩
    rw [mapGL_coe_matrix]
    ext i j
    simp [algebraMap_int_eq, Matrix.GeneralLinearGroup.map_apply]
  · rintro ⟨hgZ, hgPos⟩
    rw [Matrix.mem_glpos, Matrix.GeneralLinearGroup.val_det_apply] at hgPos
    have hdet1 : (↑g : Matrix (Fin n) (Fin n) ℚ).det = 1 := by
      rcases det_eq_one_or_neg_one_of_mem_GLnZ n hgZ with h1 | h1
      · exact h1
      · linarith
    obtain ⟨A, hA⟩ := (hasIntEntries_iff n).mp (hasIntEntries_of_mem_GLnZ n hgZ)
    have hAdet : A.det = 1 := by
      have hcast : (A.det : ℚ) = (↑g : Matrix (Fin n) (Fin n) ℚ).det := by
        rw [hA]
        simpa [RingHom.mapMatrix_apply] using RingHom.map_det (Int.castRingHom ℚ) A
      exact_mod_cast hcast.trans hdet1
    let σ : SpecialLinearGroup (Fin n) ℤ := ⟨A, hAdet⟩
    refine (mem_SLnZ_iff n).mpr ⟨σ, Units.ext ?_⟩
    rw [hA, mapGL_coe_matrix, algebraMap_int_eq, map_apply_coe, RingHom.mapMatrix_apply]
    simp [σ]

/-- `SL_n(ℤ)` is a subgroup of `GL_n(ℤ)`. -/
theorem SLnZ_le_GLnZ : SLnZ n ≤ GLnZ n :=
  SLnZ_eq_GLnZ_inf_glpos n ▸ inf_le_left

end GLnZ

section ParityAndSign

/-- `-I_n` belongs to `GL_n(ℤ)` in every rank `n`. -/
theorem neg_one_mem_GLnZ : (-1 : GL (Fin n) ℚ) ∈ GLnZ n := by
  refine (mem_GLnZ_iff n).mpr ⟨-1, Units.ext ?_⟩
  ext i j
  rcases eq_or_ne i j with rfl | hij
  · simp [Matrix.GeneralLinearGroup.map_apply]
  · simp [Matrix.GeneralLinearGroup.map_apply, hij]

/-- Whenever `-I_n` belongs to the left subgroup `H₁`, negating a matrix leaves its
`(H₁, H₂)`-double coset unchanged. -/
theorem doubleCoset_neg_of_neg_one_mem_left {H₁ H₂ : Subgroup (GL (Fin n) ℚ)}
    (hneg : (-1 : GL (Fin n) ℚ) ∈ H₁) (g : GL (Fin n) ℚ) :
    doubleCoset (-g) H₁ H₂ = doubleCoset g H₁ H₂ :=
  (doubleCoset_eq_of_mem (mem_doubleCoset.mpr ⟨-1, hneg, 1, H₂.one_mem, by simp⟩)).symm

/-- Negating a matrix leaves its `GL_n(ℤ)`-double coset unchanged (`Rhodes–Shemanske`, §2). -/
@[simp]
theorem doubleCoset_neg_GLnZ (g : GL (Fin n) ℚ) :
    doubleCoset (-g) (GLnZ n) (GLnZ n) = doubleCoset g (GLnZ n) (GLnZ n) :=
  doubleCoset_neg_of_neg_one_mem_left n (neg_one_mem_GLnZ n) g

/-- `-I_n` belongs to `SL_n(ℤ)` if and only if `n` is even. -/
theorem neg_one_mem_SLnZ_iff : (-1 : GL (Fin n) ℚ) ∈ SLnZ n ↔ Even n := by
  constructor
  · intro h
    have hdet := det_eq_one_of_mem_SLnZ n h
    have hneg : ((-1 : GL (Fin n) ℚ) : Matrix (Fin n) (Fin n) ℚ) = (-1 : ℚ) • 1 := by
      ext i j
      simp
    rw [hneg, Matrix.det_smul, Fintype.card_fin, Matrix.det_one, mul_one] at hdet
    exact (neg_one_pow_eq_one_iff_even (by norm_num : (-1 : ℚ) ≠ 1)).mp hdet
  · intro hn
    have : Fact (Even (Fintype.card (Fin n))) := ⟨by simpa using hn⟩
    exact (mem_SLnZ_iff n).mpr ⟨-1, mapGL_neg_one⟩

/-- `-g` lies in the `SL_n(ℤ)`-double coset of `g ∈ GL_n(ℚ)` if and only if `n` is even
(`Rhodes–Shemanske`, §2). -/
theorem neg_mem_doubleCoset_SLnZ_iff (g : GL (Fin n) ℚ) :
    -g ∈ doubleCoset g (SLnZ n) (SLnZ n) ↔ Even n := by
  constructor
  · intro hmem
    have hdet := det_eq_of_mem_doubleCoset_SLnZ n hmem
    have hneg : ((-g : GL (Fin n) ℚ) : Matrix (Fin n) (Fin n) ℚ) =
        (-1 : ℚ) • (↑g : Matrix (Fin n) (Fin n) ℚ) := by
      ext i j
      simp
    rw [hneg, Matrix.det_smul, Fintype.card_fin] at hdet
    have hpow : (-1 : ℚ) ^ n = 1 :=
      mul_right_cancel₀ g.det_ne_zero (hdet.trans (one_mul _).symm)
    exact (neg_one_pow_eq_one_iff_even (by norm_num : (-1 : ℚ) ≠ 1)).mp hpow
  · intro hn
    rw [← doubleCoset_neg_of_neg_one_mem_left n ((neg_one_mem_SLnZ_iff n).mpr hn) g]
    exact mem_doubleCoset_self _ _ _

/-- In even rank `n`, negating a matrix leaves its `SL_n(ℤ)`-double coset unchanged. -/
theorem doubleCoset_neg_SLnZ_of_even (hn : Even n) (g : GL (Fin n) ℚ) :
    doubleCoset (-g) (SLnZ n) (SLnZ n) = doubleCoset g (SLnZ n) (SLnZ n) :=
  doubleCoset_neg_of_neg_one_mem_left n ((neg_one_mem_SLnZ_iff n).mpr hn) g

/-- The diagonal sign-flip matrix `diag(-1, 1, …, 1) ∈ GL_n(ℤ)` in positive rank `n`. -/
noncomputable def signFlipGL [NeZero n] : GL (Fin n) ℚ :=
  TauCeti.diagGL fun i : Fin n ↦ if i = 0 then (-1 : ℚˣ) else 1

/-- `signFlipGL` belongs to `GL_n(ℤ)`. -/
theorem signFlipGL_mem_GLnZ [NeZero n] : signFlipGL n ∈ GLnZ n := by
  refine (mem_GLnZ_iff n).mpr
    ⟨TauCeti.diagGL fun i : Fin n ↦ if i = 0 then (-1 : ℤˣ) else 1, ?_⟩
  rw [TauCeti.map_diagGL, signFlipGL]
  congr 1
  funext i
  split_ifs <;> rfl

/-- `signFlipGL` is an involution. -/
@[simp]
theorem signFlipGL_mul_self [NeZero n] : signFlipGL n * signFlipGL n = 1 := by
  rw [signFlipGL, ← map_mul]
  convert map_one TauCeti.diagGL
  funext i
  simp only [Pi.mul_apply, Pi.one_apply]
  split_ifs <;> simp

/-- `signFlipGL` equals its own inverse. -/
@[simp]
theorem signFlipGL_inv [NeZero n] : (signFlipGL n)⁻¹ = signFlipGL n :=
  inv_eq_of_mul_eq_one_right (signFlipGL_mul_self n)

/-- `signFlipGL` has determinant `-1`. -/
@[simp]
theorem det_signFlipGL [NeZero n] :
    (↑(signFlipGL n) : Matrix (Fin n) (Fin n) ℚ).det = -1 := by
  rw [← Matrix.GeneralLinearGroup.val_det_apply, signFlipGL, TauCeti.det_diagGL,
    Finset.prod_eq_single (0 : Fin n)]
  · simp
  · intro i _ hi
    rw [ite_eq_right hi]
  · intro h
    exact absurd (Finset.mem_univ (0 : Fin n)) h

/-- `signFlipGL` commutes with every diagonal matrix in `GL_n(ℚ)`. -/
theorem signFlipGL_comm_diagGL [NeZero n] (t : Fin n → ℚˣ) :
    signFlipGL n * TauCeti.diagGL t = TauCeti.diagGL t * signFlipGL n :=
  ((Commute.all _ t).map TauCeti.diagGL).eq

/-- `signFlipGL` commutes with every natural diagonal matrix `natDiagGL n a`. -/
theorem signFlipGL_comm_natDiagGL [NeZero n] (a : Fin n → ℕ) :
    signFlipGL n * natDiagGL n a = natDiagGL n a * signFlipGL n := by
  by_cases ha : ∀ i, 0 < a i
  · apply Units.ext
    simp only [Units.val_mul, natDiagGL_coe n a ha, signFlipGL, TauCeti.diagGL_coe,
      Matrix.diagonal_mul_diagonal]
    exact congrArg Matrix.diagonal (funext fun _ ↦ mul_comm _ _)
  · rw [natDiagGL_of_not_pos n ha, mul_one, one_mul]

end ParityAndSign

section Commensurator

/-- **Clearing denominators in `GL_n(ℚ)`**: for every `g ∈ GL_n(ℚ)` there is a positive natural `c`
such that `diag(c, …, c) * g` has integer entries. -/
theorem exists_pos_natDiagGL_mul_mem_intEntries (g : GL (Fin n) ℚ) :
    ∃ c : ℕ, 0 < c ∧ natDiagGL n (fun _ ↦ c) * g ∈ intEntries n := by
  let c : ℕ := ∏ i : Fin n, ∏ j : Fin n, ((g : Matrix (Fin n) (Fin n) ℚ) i j).den
  have hc : 0 < c :=
    Finset.prod_pos fun _ _ ↦ Finset.prod_pos fun _ _ ↦ Rat.den_pos _
  refine ⟨c, hc, (mem_intEntries n).mpr ((hasIntEntries_iff n).mpr ?_)⟩
  refine ⟨Matrix.of fun i j ↦
      ((g : Matrix (Fin n) (Fin n) ℚ) i j).num *
        ↑(c / ((g : Matrix (Fin n) (Fin n) ℚ) i j).den), ?_⟩
  ext i j
  have hdvd : ((g : Matrix (Fin n) (Fin n) ℚ) i j).den ∣ c :=
    dvd_trans
      (Finset.dvd_prod_of_mem (fun j' ↦ ((g : Matrix (Fin n) (Fin n) ℚ) i j').den)
        (Finset.mem_univ j))
      (Finset.dvd_prod_of_mem (fun i' ↦ ∏ j' : Fin n, ((g : Matrix (Fin n) (Fin n) ℚ) i' j').den)
        (Finset.mem_univ i))
  have hmul : (c : ℚ) =
      (((g : Matrix (Fin n) (Fin n) ℚ) i j).den : ℚ) *
        ((c / ((g : Matrix (Fin n) (Fin n) ℚ) i j).den : ℕ) : ℚ) := by
    exact_mod_cast (Nat.mul_div_cancel' hdvd).symm
  simp only [Units.val_mul, natDiagGL_coe n _ fun _ ↦ hc, Matrix.diagonal_mul,
    Matrix.map_apply, Matrix.of_apply, Int.cast_mul, Int.cast_natCast]
  calc (c : ℚ) * (g : Matrix (Fin n) (Fin n) ℚ) i j
      = ((c / ((g : Matrix (Fin n) (Fin n) ℚ) i j).den : ℕ) : ℚ) *
          ((g : Matrix (Fin n) (Fin n) ℚ) i j *
            (((g : Matrix (Fin n) (Fin n) ℚ) i j).den : ℚ)) := by
          rw [hmul]
          ring
    _ = (((g : Matrix (Fin n) (Fin n) ℚ) i j).num : ℚ) *
          ((c / ((g : Matrix (Fin n) (Fin n) ℚ) i j).den : ℕ) : ℚ) := by
          rw [Rat.mul_den_eq_num, mul_comm]

/-- **Clearing denominators in `GL_n^+(ℚ)`**: for every `g ∈ GL_n^+(ℚ)` there is a positive natural
`c` such that `diag(c, …, c) * g` lies in Shimura's integral submonoid `posDetInt n`. -/
theorem exists_pos_natDiagGL_mul_mem_posDetInt {g : GL (Fin n) ℚ}
    (hg : g ∈ Matrix.GLPos (Fin n) ℚ) :
    ∃ c : ℕ, 0 < c ∧ natDiagGL n (fun _ ↦ c) * g ∈ posDetInt n := by
  obtain ⟨c, hc, hint⟩ := exists_pos_natDiagGL_mul_mem_intEntries n g
  have hc_pos : natDiagGL n (fun _ ↦ c) ∈ Matrix.GLPos (Fin n) ℚ :=
    posDetInt_le_glpos n (natDiagGL_mem_posDetInt n _)
  have hprod_pos : natDiagGL n (fun _ ↦ c) * g ∈ Matrix.GLPos (Fin n) ℚ :=
    (Matrix.GLPos (Fin n) ℚ).mul_mem hc_pos hg
  rw [Matrix.mem_glpos, Matrix.GeneralLinearGroup.val_det_apply] at hprod_pos
  exact ⟨c, hc, (mem_posDetInt_iff n).mpr ⟨(mem_intEntries n).mp hint, hprod_pos⟩⟩

/-- **The commensurator of `SL_n(ℤ)` in `GL_n(ℚ)` is the whole group.** -/
theorem commensurator_SLnZ_eq_top : commensurator (SLnZ n) = ⊤ := by
  -- Clearing denominators writes `g = (diag(c, …, c))⁻¹ * h` with both factors in `intEntries n`,
  -- each of which commensurates `SL_n(ℤ)` by Shimura's Lemma 3.10.
  rw [Subgroup.eq_top_iff']
  intro g
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have : Subsingleton (GL (Fin 0) ℚ) := inferInstance
    exact Subsingleton.elim g 1 ▸ (commensurator (SLnZ 0)).one_mem
  · have : NeZero n := ⟨hn.ne'⟩
    obtain ⟨c, -, hcg⟩ := exists_pos_natDiagGL_mul_mem_intEntries n g
    have hc_comm : natDiagGL n (fun _ ↦ c) ∈ commensurator (SLnZ n) :=
      mem_commensurator_of_hasIntEntries n (hasIntEntries_natDiagGL n _)
    have hcg_comm : natDiagGL n (fun _ ↦ c) * g ∈ commensurator (SLnZ n) :=
      mem_commensurator_of_hasIntEntries n ((mem_intEntries n).mp hcg)
    simpa using
      (commensurator (SLnZ n)).mul_mem ((commensurator (SLnZ n)).inv_mem hc_comm) hcg_comm

/-- `SL_n(ℤ)` has finite index (at most `2`) inside `GL_n(ℤ)`. -/
instance finiteIndex_SLnZ_subgroupOf_GLnZ : ((SLnZ n).subgroupOf (GLnZ n)).FiniteIndex := by
  have hinj : Function.Injective
      (fun q : GLnZ n ⧸ (SLnZ n).subgroupOf (GLnZ n) ↦
        decide (0 < ((q.out : GL (Fin n) ℚ) : Matrix (Fin n) (Fin n) ℚ).det)) := by
    intro q₁ q₂ hdec
    have hiff : 0 < ((q₁.out : GL (Fin n) ℚ) : Matrix (Fin n) (Fin n) ℚ).det ↔
        0 < ((q₂.out : GL (Fin n) ℚ) : Matrix (Fin n) (Fin n) ℚ).det :=
      decide_eq_decide.mp hdec
    have hdet_eq : ((q₁.out : GL (Fin n) ℚ) : Matrix (Fin n) (Fin n) ℚ).det =
        ((q₂.out : GL (Fin n) ℚ) : Matrix (Fin n) (Fin n) ℚ).det := by
      rcases det_eq_one_or_neg_one_of_mem_GLnZ n q₁.out.2 with h1 | h1 <;>
        rcases det_eq_one_or_neg_one_of_mem_GLnZ n q₂.out.2 with h2 | h2
      · exact h1.trans h2.symm
      · exfalso; have := hiff.mp (by linarith); linarith
      · exfalso; have := hiff.mpr (by linarith); linarith
      · exact h1.trans h2.symm
    have hprod_pos : ((q₁.out : GL (Fin n) ℚ)⁻¹ * (q₂.out : GL (Fin n) ℚ)) ∈
        Matrix.GLPos (Fin n) ℚ := by
      rw [Matrix.mem_glpos, map_mul, map_inv, Units.val_mul, Units.val_inv_eq_inv_val,
        Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply,
        ← hdet_eq]
      rcases det_eq_one_or_neg_one_of_mem_GLnZ n q₁.out.2 with h1 | h1 <;> simp [h1]
    have hprod_SL : (q₁.out : GL (Fin n) ℚ)⁻¹ * (q₂.out : GL (Fin n) ℚ) ∈ SLnZ n :=
      (Subgroup.ext_iff.mp (SLnZ_eq_GLnZ_inf_glpos n) _).mpr
        (Subgroup.mem_inf.mpr ⟨(GLnZ n).mul_mem ((GLnZ n).inv_mem q₁.out.2) q₂.out.2, hprod_pos⟩)
    have hmk : (QuotientGroup.mk q₁.out : GLnZ n ⧸ (SLnZ n).subgroupOf (GLnZ n)) =
        QuotientGroup.mk q₂.out :=
      QuotientGroup.eq.mpr (Subgroup.mem_subgroupOf.mpr hprod_SL)
    simpa only [QuotientGroup.out_eq'] using hmk
  have : Finite (GLnZ n ⧸ (SLnZ n).subgroupOf (GLnZ n)) := Finite.of_injective _ hinj
  exact Subgroup.finiteIndex_of_finite_quotient

/-- `GL_n(ℤ)` and `SL_n(ℤ)` are commensurable in `GL_n(ℚ)`. -/
theorem commensurable_GLnZ_SLnZ : Subgroup.Commensurable (GLnZ n) (SLnZ n) :=
  ⟨Subgroup.isFiniteRelIndex_iff_relIndex_ne_zero.mpr
      (by rw [Subgroup.relIndex_eq_one.mpr (SLnZ_le_GLnZ n)]; exact one_ne_zero),
    Subgroup.isFiniteRelIndex_iff_relIndex_ne_zero.mpr Subgroup.FiniteIndex.index_ne_zero⟩

/-- **The commensurator of `GL_n(ℤ)` in `GL_n(ℚ)` is the whole group.** -/
theorem commensurator_GLnZ_eq_top : commensurator (GLnZ n) = ⊤ :=
  (commensurable_GLnZ_SLnZ n).eq.trans (commensurator_SLnZ_eq_top n)

/-- The positive-determinant rational Hecke triple `(SL_n(ℤ), GL_n^+(ℚ))`. -/
instance instIsHeckeTripleGLPosSLnZ :
    IsHeckeTriple (Matrix.GLPos (Fin n) ℚ).toSubmonoid (SLnZ n) (SLnZ n) :=
  IsHeckeTriple.of_diagonal (SLnZ_le_glpos n)
    (by rw [commensurator_SLnZ_eq_top]; exact le_top)

/-- The full rational Hecke triple `(GL_n(ℤ), GL_n(ℚ))`. -/
instance instIsHeckeTripleTopGLnZ :
    IsHeckeTriple (⊤ : Submonoid (GL (Fin n) ℚ)) (GLnZ n) (GLnZ n) :=
  IsHeckeTriple.of_diagonal le_top
    (by rw [commensurator_GLnZ_eq_top]; exact le_top)

/-- The positive-determinant rational Hecke ring `H(SL_n(ℤ), GL_n^+(ℚ))` over `ℤ`. -/
abbrev RationalHeckeRing := 𝕋 (Matrix.GLPos (Fin n) ℚ).toSubmonoid (SLnZ n) ℤ

/-- The full rational Hecke ring `H(GL_n(ℤ), GL_n(ℚ))` over `ℤ`. -/
abbrev FullHeckeRing := 𝕋 (⊤ : Submonoid (GL (Fin n) ℚ)) (GLnZ n) ℤ

end Commensurator

section Comparison

/-- **Integral-to-rational Hecke ring embedding** (`Shimura` Proposition 3.16 /
`Rhodes–Shemanske` §2): enlarging `posDetInt n` to `GL_n^+(ℚ)` embeds `𝕋 (posDetInt n) (SLnZ n) R`
injectively into `𝕋 (GLPos (Fin n) ℚ).toSubmonoid (SLnZ n) R` over any coefficient semiring `R`. -/
noncomputable def integralToRationalRingHom [NeZero n] (R : Type*) [Semiring R] :
    𝕋 (posDetInt n) (SLnZ n) R →+* 𝕋 (Matrix.GLPos (Fin n) ℚ).toSubmonoid (SLnZ n) R :=
  HeckeCosetModule.mapSubmonoidRingHom R (posDetInt_le_glpos n)

/-- The integral-to-rational embedding over `ℤ`. -/
noncomputable abbrev integralToRational [NeZero n] :
    IntegralHeckeRing n →+* RationalHeckeRing n :=
  integralToRationalRingHom n ℤ

/-- `integralToRationalRingHom` maps a basis element to the corresponding rational basis element. -/
@[simp]
theorem integralToRationalRingHom_single [NeZero n] (R : Type*) [Semiring R]
    (D : HeckeCoset (posDetInt n) (SLnZ n) (SLnZ n)) (b : R) :
    integralToRationalRingHom n R (HeckeCosetModule.single R D b) =
      HeckeCosetModule.single R (D.map (posDetInt_le_glpos n) le_rfl le_rfl) b :=
  HeckeCosetModule.mapSubmonoidRingHom_single R (posDetInt_le_glpos n) D b

/-- `integralToRationalRingHom` is injective over any coefficient semiring `R`. -/
theorem integralToRationalRingHom_injective [NeZero n] (R : Type*) [Semiring R] :
    Function.Injective (integralToRationalRingHom n R) :=
  HeckeCosetModule.mapSubmonoidRingHom_injective R (posDetInt_le_glpos n)

/-- `integralToRational` is injective. -/
theorem integralToRational_injective [NeZero n] :
    Function.Injective (integralToRational n) :=
  integralToRationalRingHom_injective n ℤ

/-- Image of a diagonal Hecke operator `diagElem a` under `integralToRational`. -/
theorem integralToRational_diagElem [NeZero n] (a : Fin n → ℕ) :
    integralToRational n (diagElem a) =
      HeckeCosetModule.single ℤ
        (HeckeCoset.mk (SLnZ n) (SLnZ n)
          ⟨natDiagGL n a, posDetInt_le_glpos n (natDiagGL_mem_posDetInt n a)⟩) 1 := by
  rw [diagElem_def, integralToRationalRingHom_single, diagCoset_def, HeckeCoset.map_mk]
  rfl

/-- Every `g ∈ GL_n(ℚ)` can be translated on the left into `GL_n^+(ℚ)` by an element of
`GL_n(ℤ)`. -/
theorem exists_mem_GLnZ_mul_mem_glpos (g : GL (Fin n) ℚ) :
    ∃ u ∈ GLnZ n, u * g ∈ Matrix.GLPos (Fin n) ℚ := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have : Subsingleton (GL (Fin 0) ℚ) := inferInstance
    exact ⟨1, (GLnZ 0).one_mem, Subsingleton.elim (1 * g) 1 ▸ (Matrix.GLPos (Fin 0) ℚ).one_mem⟩
  · have : NeZero n := ⟨hn.ne'⟩
    rcases lt_or_gt_of_ne g.det_ne_zero with hneg | hpos
    · refine ⟨signFlipGL n, signFlipGL_mem_GLnZ n, ?_⟩
      rw [Matrix.mem_glpos, Matrix.GeneralLinearGroup.val_det_apply, Units.val_mul,
        Matrix.det_mul, det_signFlipGL]
      linarith
    · refine ⟨1, (GLnZ n).one_mem, ?_⟩
      rw [one_mul, Matrix.mem_glpos, Matrix.GeneralLinearGroup.val_det_apply]
      exact hpos

/-- For every `g ∈ GL_n^+(ℚ)` in positive rank `n`, clearing denominators and putting
`diag(c, …, c) * g = γ₁ * diag(a) * γ₂` in Smith normal form produces `s₁, s₂ ∈ GL_n(ℤ)` with
`det s₁ = -1` and `s₁ * g = g * s₂` (`Rhodes–Shemanske`, §2). -/
private lemma exists_mem_GLnZ_det_neg_one_mul_eq_mul [NeZero n] {g : GL (Fin n) ℚ}
    (hg : g ∈ Matrix.GLPos (Fin n) ℚ) :
    ∃ s₁ ∈ GLnZ n, ∃ s₂ ∈ GLnZ n,
      (↑s₁ : Matrix (Fin n) (Fin n) ℚ).det = -1 ∧ s₁ * g = g * s₂ := by
  obtain ⟨c, -, hcg⟩ := exists_pos_natDiagGL_mul_mem_posDetInt n hg
  obtain ⟨a, -, -, hD⟩ :=
    exists_diagonal_representative (HeckeCoset.mk (SLnZ n) (SLnZ n) ⟨_, hcg⟩)
  have hmem : natDiagGL n (fun _ ↦ c) * g ∈ doubleCoset (natDiagGL n a) (SLnZ n) (SLnZ n) := by
    have hset := congrArg HeckeCoset.toSet hD
    rw [HeckeCoset.toSet_mk, diagCoset_toSet] at hset
    exact hset ▸ mem_doubleCoset_self _ _ _
  obtain ⟨γ₁, hγ₁, γ₂, hγ₂, hsnf⟩ := mem_doubleCoset.mp hmem
  refine ⟨γ₁ * signFlipGL n * γ₁⁻¹,
    (GLnZ n).mul_mem ((GLnZ n).mul_mem (SLnZ_le_GLnZ n hγ₁) (signFlipGL_mem_GLnZ n))
      ((GLnZ n).inv_mem (SLnZ_le_GLnZ n hγ₁)),
    γ₂⁻¹ * signFlipGL n * γ₂,
    (GLnZ n).mul_mem ((GLnZ n).mul_mem ((GLnZ n).inv_mem (SLnZ_le_GLnZ n hγ₂))
      (signFlipGL_mem_GLnZ n)) (SLnZ_le_GLnZ n hγ₂), ?_, ?_⟩
  · simp only [Units.val_mul, Matrix.det_mul, det_signFlipGL,
      det_eq_one_of_mem_SLnZ n hγ₁, det_eq_one_of_mem_SLnZ n ((SLnZ n).inv_mem hγ₁)]
    ring
  · apply mul_left_cancel (a := natDiagGL n (fun _ ↦ c))
    calc natDiagGL n (fun _ ↦ c) * ((γ₁ * signFlipGL n * γ₁⁻¹) * g)
        = (γ₁ * signFlipGL n * γ₁⁻¹) * (natDiagGL n (fun _ ↦ c) * g) := by
            rw [← mul_assoc, natDiagGL_const_comm n c, mul_assoc]
      _ = γ₁ * (signFlipGL n * natDiagGL n a) * γ₂ := by rw [hsnf]; group
      _ = γ₁ * (natDiagGL n a * signFlipGL n) * γ₂ := by rw [signFlipGL_comm_natDiagGL]
      _ = (natDiagGL n (fun _ ↦ c) * g) * (γ₂⁻¹ * signFlipGL n * γ₂) := by rw [hsnf]; group
      _ = natDiagGL n (fun _ ↦ c) * (g * (γ₂⁻¹ * signFlipGL n * γ₂)) := mul_assoc _ _ _

/-- **Stabilizer coset condition for `(SL_n(ℤ), GL_n(ℤ))` along `GL_n^+(ℚ)`.** For every
`g ∈ GL_n^+(ℚ)`, `SL_n(ℤ)` meets every left coset of `GL_n(ℤ) ∩ g · GL_n(ℤ) · g⁻¹` in `GL_n(ℤ)`. -/
theorem exists_mem_SLnZ_inv_mul_mem_conj_GLnZ {g : GL (Fin n) ℚ}
    (hg : g ∈ Matrix.GLPos (Fin n) ℚ) {u : GL (Fin n) ℚ} (hu : u ∈ GLnZ n) :
    ∃ x ∈ SLnZ n, x⁻¹ * u ∈ ConjAct.toConjAct g • GLnZ n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have : Subsingleton (GL (Fin 0) ℚ) := inferInstance
    exact ⟨1, (SLnZ 0).one_mem,
      Subsingleton.elim ((1 : GL (Fin 0) ℚ)⁻¹ * u) 1 ▸
        (ConjAct.toConjAct g • GLnZ 0).one_mem⟩
  have : NeZero n := ⟨hn.ne'⟩
  rcases det_eq_one_or_neg_one_of_mem_GLnZ n hu with hu1 | hu1
  · have huSL : u ∈ SLnZ n :=
      (Subgroup.ext_iff.mp (SLnZ_eq_GLnZ_inf_glpos n) _).mpr
        (Subgroup.mem_inf.mpr ⟨hu, by
          rw [Matrix.mem_glpos, Matrix.GeneralLinearGroup.val_det_apply, hu1]; norm_num⟩)
    exact ⟨u, huSL, by rw [inv_mul_cancel]; exact Subgroup.one_mem _⟩
  · obtain ⟨s₁, hs₁_GLnZ, s₂, hs₂_GLnZ, hs₁_det, hintertwine⟩ :=
      exists_mem_GLnZ_det_neg_one_mul_eq_mul n hg
    have hx_SL : u * s₁⁻¹ ∈ SLnZ n :=
      (Subgroup.ext_iff.mp (SLnZ_eq_GLnZ_inf_glpos n) _).mpr
        (Subgroup.mem_inf.mpr ⟨(GLnZ n).mul_mem hu ((GLnZ n).inv_mem hs₁_GLnZ), by
          rw [Matrix.mem_glpos, map_mul, map_inv, Units.val_mul, Units.val_inv_eq_inv_val,
            Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply,
            hu1, hs₁_det]
          norm_num⟩)
    refine ⟨u * s₁⁻¹, hx_SL, ?_⟩
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ConjAct.smul_def, ConjAct.ofConjAct_inv,
      ConjAct.ofConjAct_toConjAct, inv_inv]
    have hconj : g⁻¹ * ((u * s₁⁻¹)⁻¹ * u) * g = s₂ := by
      have hsimp : (u * s₁⁻¹)⁻¹ * u = s₁ := by group
      rw [hsimp, mul_assoc, hintertwine, inv_mul_cancel_left]
    exact hconj ▸ hs₂_GLnZ

/-- **Double-coset equivalence** `SL_n(ℤ) \ GL_n^+(ℚ) / SL_n(ℤ) ≃ GL_n(ℤ) \ GL_n(ℚ) / GL_n(ℤ)`
(`Rhodes–Shemanske`, §2). -/
noncomputable def rationalToFullCosetEquiv :
    HeckeCoset (Matrix.GLPos (Fin n) ℚ).toSubmonoid (SLnZ n) (SLnZ n) ≃
      HeckeCoset (⊤ : Submonoid (GL (Fin n) ℚ)) (GLnZ n) (GLnZ n) :=
  HeckeCoset.mapEquivOfInf (SLnZ_eq_GLnZ_inf_glpos n) le_top le_rfl
    (fun δ' ↦ exists_mem_GLnZ_mul_mem_glpos n (δ' : GL (Fin n) ℚ))
    (fun g _ hu ↦ exists_mem_SLnZ_inv_mul_mem_conj_GLnZ n g.2 hu)

/-- **Rational-to-full Hecke ring isomorphism** (`Shimura` Proposition 3.16 /
`Rhodes–Shemanske` §2): `H_R(SL_n(ℤ), GL_n^+(ℚ)) ≃+* H_R(GL_n(ℤ), GL_n(ℚ))` over any coefficient
semiring `R`. -/
noncomputable def rationalToFullRingEquiv (R : Type*) [Semiring R] :
    𝕋 (Matrix.GLPos (Fin n) ℚ).toSubmonoid (SLnZ n) R ≃+*
      𝕋 (⊤ : Submonoid (GL (Fin n) ℚ)) (GLnZ n) R :=
  HeckeCosetModule.mapSubgroupRingEquiv R (SLnZ_eq_GLnZ_inf_glpos n) le_top le_rfl
    (fun δ' ↦ exists_mem_GLnZ_mul_mem_glpos n (δ' : GL (Fin n) ℚ))
    (fun g _ hu ↦ exists_mem_SLnZ_inv_mul_mem_conj_GLnZ n g.2 hu)

/-- The rational-to-full Hecke ring isomorphism over `ℤ`. -/
noncomputable abbrev rationalToFullEquiv :
    RationalHeckeRing n ≃+* FullHeckeRing n :=
  rationalToFullRingEquiv n ℤ

/-- `rationalToFullRingEquiv` sends each basis element to the corresponding `GL_n(ℤ)`-coset basis
element. -/
@[simp]
theorem rationalToFullRingEquiv_single (R : Type*) [Semiring R]
    (D : HeckeCoset (Matrix.GLPos (Fin n) ℚ).toSubmonoid (SLnZ n) (SLnZ n)) (b : R) :
    rationalToFullRingEquiv n R (HeckeCosetModule.single R D b) =
      HeckeCosetModule.single R (D.map le_top (SLnZ_le_GLnZ n) (SLnZ_le_GLnZ n)) b :=
  HeckeCosetModule.mapSubgroupRingEquiv_single R (SLnZ_eq_GLnZ_inf_glpos n) le_top le_rfl _ _ D b

/-- Composite embedding `H_R(SL_n(ℤ), M_n^+(ℤ)) ↪ H_R(GL_n(ℤ), GL_n(ℚ))` of the integral Hecke ring
into the full rational Hecke ring. -/
noncomputable def integralToFullRingHom [NeZero n] (R : Type*) [Semiring R] :
    𝕋 (posDetInt n) (SLnZ n) R →+* 𝕋 (⊤ : Submonoid (GL (Fin n) ℚ)) (GLnZ n) R :=
  (rationalToFullRingEquiv n R).toRingHom.comp (integralToRationalRingHom n R)

/-- `integralToFullRingHom` is injective over any coefficient semiring `R`. -/
theorem integralToFullRingHom_injective [NeZero n] (R : Type*) [Semiring R] :
    Function.Injective (integralToFullRingHom n R) :=
  (rationalToFullRingEquiv n R).injective.comp (integralToRationalRingHom_injective n R)

end Comparison

section Commutativity

/-- Transposition preserves `GL_n^+(ℚ)`. -/
theorem transposeMulEquiv_mem_glpos {g : GL (Fin n) ℚ} (hg : g ∈ Matrix.GLPos (Fin n) ℚ) :
    (Matrix.GeneralLinearGroup.transposeMulEquiv (Fin n) g).unop ∈ Matrix.GLPos (Fin n) ℚ := by
  rw [Matrix.mem_glpos, Matrix.GeneralLinearGroup.val_det_apply] at hg ⊢
  rwa [Matrix.GeneralLinearGroup.coe_unop_transposeMulEquiv, Matrix.det_transpose]

/-- Transposition as an anti-involution of the rational Hecke datum `(GL_n^+(ℚ), SL_n(ℤ))`. -/
noncomputable def transposeRationalAntiInvolution :
    HeckeAntiInvolution (Matrix.GLPos (Fin n) ℚ).toSubmonoid (SLnZ n) :=
  HeckeAntiInvolution.ofAmbient
    (Matrix.GeneralLinearGroup.transposeMulEquiv (R := ℚ) (Fin n)).toMonoidHom
    Matrix.GeneralLinearGroup.transposeMulEquiv_transposeMulEquiv
    (fun _ hg ↦ transposeMulEquiv_mem_SLnZ n hg)
    (fun _ hg ↦ transposeMulEquiv_mem_glpos n hg)

/-- `transposeRationalAntiInvolution` acts on `GL_n^+(ℚ)` by matrix transposition. -/
@[simp]
theorem transposeRationalAntiInvolution_bar {x : GL (Fin n) ℚ}
    (hx : x ∈ (Matrix.GLPos (Fin n) ℚ).toSubmonoid) :
    (transposeRationalAntiInvolution n).bar x hx =
      (Matrix.GeneralLinearGroup.transposeMulEquiv (Fin n) x).unop :=
  HeckeAntiInvolution.ofAmbient_bar _ _ _ _ x hx

/-- Transposition fixes every double coset in `SL_n(ℤ) \ GL_n^+(ℚ) / SL_n(ℤ)`. -/
@[simp]
theorem transposeRationalAntiInvolution_onHeckeCoset_eq_self
    (D : HeckeCoset (Matrix.GLPos (Fin n) ℚ).toSubmonoid (SLnZ n) (SLnZ n)) :
    (transposeRationalAntiInvolution n).onHeckeCoset D = D := by
  -- Clearing denominators by a central scalar `diag(c, …, c)` reduces to the integral
  -- Smith-normal-form theorem `transposeAntiInvolution_onHeckeCoset_eq_self`, after which
  -- `diag(c, …, c)` cancels.
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · induction D using HeckeCoset.induction with | h g =>
    rw [(transposeRationalAntiInvolution 0).onHeckeCoset_mk]
    have : Subsingleton (GL (Fin 0) ℚ) := inferInstance
    exact congrArg (HeckeCoset.mk _ _) (Subtype.ext (Subsingleton.elim _ _))
  have : NeZero n := ⟨hn.ne'⟩
  induction D using HeckeCoset.induction with | h g =>
  rw [(transposeRationalAntiInvolution n).onHeckeCoset_mk]
  obtain ⟨c, hc, hcg⟩ := exists_pos_natDiagGL_mul_mem_posDetInt n g.2
  have hbar_int := (transposeAntiInvolution n).bar_mem_doubleCoset_self
    (transposeAntiInvolution_onHeckeCoset_eq_self n) ⟨natDiagGL n (fun _ ↦ c) * g, hcg⟩
  rw [transposeAntiInvolution_bar] at hbar_int
  obtain ⟨γ₁, hγ₁, γ₂, hγ₂, hEq⟩ := mem_doubleCoset.mp hbar_int
  have hbar_cg :
      (Matrix.GeneralLinearGroup.transposeMulEquiv (Fin n)
          (natDiagGL n (fun _ ↦ c) * (g : GL (Fin n) ℚ))).unop =
        natDiagGL n (fun _ ↦ c) *
          (Matrix.GeneralLinearGroup.transposeMulEquiv (Fin n) (g : GL (Fin n) ℚ)).unop := by
    rw [map_mul, MulOpposite.unop_mul, transposeMulEquiv_natDiagGL, ← natDiagGL_const_comm]
  refine HeckeCoset.mk_eq_mk_of_mem (mem_doubleCoset.mpr ⟨γ₁, hγ₁, γ₂, hγ₂, ?_⟩)
  dsimp only
  rw [transposeRationalAntiInvolution_bar]
  apply mul_left_cancel (a := natDiagGL n (fun _ ↦ c))
  calc natDiagGL n (fun _ ↦ c) *
        (Matrix.GeneralLinearGroup.transposeMulEquiv (Fin n) (g : GL (Fin n) ℚ)).unop
      = (Matrix.GeneralLinearGroup.transposeMulEquiv (Fin n)
          (natDiagGL n (fun _ ↦ c) * (g : GL (Fin n) ℚ))).unop := hbar_cg.symm
    _ = γ₁ * (natDiagGL n (fun _ ↦ c) * (g : GL (Fin n) ℚ)) * γ₂ := hEq
    _ = natDiagGL n (fun _ ↦ c) * (γ₁ * (g : GL (Fin n) ℚ) * γ₂) := by
        rw [← mul_assoc γ₁, ← natDiagGL_const_comm n c γ₁]
        group

/-- The positive-determinant rational Hecke ring is commutative over any commutative semiring
`R`. -/
@[instance_reducible]
noncomputable def commSemiringRationalHeckeRing (R : Type*) [CommSemiring R] :
    CommSemiring (𝕋 (Matrix.GLPos (Fin n) ℚ).toSubmonoid (SLnZ n) R) :=
  HeckeCosetModule.commSemiringOfAntiInvolution R (transposeRationalAntiInvolution n)
    (transposeRationalAntiInvolution_onHeckeCoset_eq_self n)

/-- The positive-determinant rational Hecke ring is a commutative ring over any commutative ring
`R`, extending the ambient `Ring` instance. -/
@[instance_reducible]
noncomputable def commRingRationalHeckeRing (R : Type*) [CommRing R] :
    CommRing (𝕋 (Matrix.GLPos (Fin n) ℚ).toSubmonoid (SLnZ n) R) :=
  { (inferInstance : Ring (𝕋 (Matrix.GLPos (Fin n) ℚ).toSubmonoid (SLnZ n) R)) with
    mul_comm := HeckeCosetModule.mul_comm_of_antiInvolution R (transposeRationalAntiInvolution n)
      (transposeRationalAntiInvolution_onHeckeCoset_eq_self n) }

/-- Multiplication in the full rational Hecke ring `H_R(GL_n(ℤ), GL_n(ℚ))` is commutative over any
commutative semiring `R`. -/
theorem mul_comm_fullHeckeRing (R : Type*) [CommSemiring R]
    (f g : 𝕋 (⊤ : Submonoid (GL (Fin n) ℚ)) (GLnZ n) R) : f * g = g * f := by
  apply (rationalToFullRingEquiv n R).symm.injective
  rw [map_mul, map_mul]
  exact HeckeCosetModule.mul_comm_of_antiInvolution R (transposeRationalAntiInvolution n)
    (transposeRationalAntiInvolution_onHeckeCoset_eq_self n) _ _

/-- The full rational Hecke ring `H_R(GL_n(ℤ), GL_n(ℚ))` is a commutative semiring over any
commutative semiring `R`. -/
@[instance_reducible]
noncomputable def commSemiringFullHeckeRing (R : Type*) [CommSemiring R] :
    CommSemiring (𝕋 (⊤ : Submonoid (GL (Fin n) ℚ)) (GLnZ n) R) :=
  { HeckeCosetModule.instSemiringHeckeRing R with
    mul_comm := mul_comm_fullHeckeRing n R }

/-- The full rational Hecke ring `H_R(GL_n(ℤ), GL_n(ℚ))` is a commutative ring over any commutative
ring `R`, extending the ambient `Ring` instance. -/
@[instance_reducible]
noncomputable def commRingFullHeckeRing (R : Type*) [CommRing R] :
    CommRing (𝕋 (⊤ : Submonoid (GL (Fin n) ℚ)) (GLnZ n) R) :=
  { (inferInstance : Ring (𝕋 (⊤ : Submonoid (GL (Fin n) ℚ)) (GLnZ n) R)) with
    mul_comm := mul_comm_fullHeckeRing n R }

end Commutativity

end HeckeRing.GLn
