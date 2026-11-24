/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.HeckeRing.GLn.PrimeDecomposition
public import TauCeti.NumberTheory.HeckeRing.GLn.Rational

import TauCeti.Data.Int.Shift
import TauCeti.LinearAlgebra.Matrix.Divisibility

/-!
# The `p`-primary and `p`-local rational `GL_n` Hecke triples

For a prime `p`, the `p`-primary integral submonoid `pPrimaryPosDetInt n p` consists of matrices in
Shimura's `posDetInt n` whose determinant is a power of `p`, and the `p`-local positive-determinant
subgroup `pLocalPosGL n p` consists of matrices in `GL_n^+(ℚ)` that clear into
`pPrimaryPosDetInt n p` under a scalar power of `p`.

This module keeps these rational-matrix constructions and the identification of the `p`-primary
Hecke ring `𝕋 (pPrimaryPosDetInt n p) (SLnZ n) ℤ` with Shimura's `p`-local subring
`pLocalSubring n p` purely global, downstream of `PrimeDecomposition` and `Rational`, with no
`p`-adic completion dependency.

## Main definitions

* `HeckeRing.GLn.pPrimaryPosDetInt`: the `p`-primary integral submonoid of `GL_n(ℚ)`.
* `HeckeRing.GLn.pLocalPosGL`: the `p`-local positive-determinant subgroup of `GL_n(ℚ)`.
* `HeckeRing.GLn.pPrimaryToPLocalRingEquiv`: the ring isomorphism
  `𝕋 (pPrimaryPosDetInt n p) (SLnZ n) ℤ ≃+* pLocalSubring n p`.

## Main results

* `HeckeRing.GLn.exists_primePowDiag_mem_doubleCoset`: every matrix in `pPrimaryPosDetInt n p` lies
  in the `SL_n(ℤ)` double coset of `natDiagGL n (primePowDiag n p e)` for a monotone tuple `e`.
* `HeckeRing.GLn.intPowDiagGL_mem_pLocalPosGL`: every `intPowDiagGL n p e` lies in
  `pLocalPosGL n p`.
* `HeckeRing.GLn.instIsHeckeTriplePPrimaryPosDetInt`, `HeckeRing.GLn.instIsHeckeTriplePLocalPosGL`:
  Hecke-triple instances for `(pPrimaryPosDetInt n p, SL_n(ℤ))` and `(pLocalPosGL n p, SL_n(ℤ))`.
* `HeckeRing.GLn.range_mapSubmonoidRingHom_pPrimaryPosDetInt`: the image of
  `𝕋 (pPrimaryPosDetInt n p) (SLnZ n) ℤ` in `IntegralHeckeRing n` is `pLocalSubring n p`.

## References

* [G. Shimura, *Introduction to the arithmetic theory of automorphic functions*][shimura1971], §3.2.
* J. A. Rhodes and T. R. Shemanske, *Bruhat–Tits buildings and Hecke operators*, 12 June 1998
  author manuscript, §§3.1–3.2.
* [J. A. Rhodes and T. R. Shemanske,
  *Rationality theorems for Hecke operators on GL_n*][rhodes1999], §2.
-/

public section

open Matrix Subgroup DoubleCoset
open scoped Pointwise HeckeCosetModule

namespace HeckeRing.GLn

variable (n p : ℕ) [Fact p.Prime]

section PPrimaryAndPLocalGroups

omit [Fact p.Prime] in
/-- The `p`-primary integral submonoid of `GL_n(ℚ)`: matrices in Shimura's `posDetInt n` whose
determinant is a power of `p`. -/
noncomputable def pPrimaryPosDetInt : Submonoid (GL (Fin n) ℚ) where
  carrier := {g | g ∈ posDetInt n ∧ ∃ m : ℕ, (↑g : Matrix (Fin n) (Fin n) ℚ).det = (p : ℚ) ^ m}
  one_mem' := ⟨(posDetInt n).one_mem, 0, by simp⟩
  mul_mem' := by
    rintro g₁ g₂ ⟨hg₁, m₁, hm₁⟩ ⟨hg₂, m₂, hm₂⟩
    exact ⟨(posDetInt n).mul_mem hg₁ hg₂, m₁ + m₂,
      by rw [Units.val_mul, Matrix.det_mul, hm₁, hm₂, ← pow_add]⟩

omit [Fact p.Prime] in
/-- Membership characterization for `pPrimaryPosDetInt`. -/
@[simp]
theorem mem_pPrimaryPosDetInt_iff {g : GL (Fin n) ℚ} :
    g ∈ pPrimaryPosDetInt n p ↔
      g ∈ posDetInt n ∧ ∃ m : ℕ, (↑g : Matrix (Fin n) (Fin n) ℚ).det = (p : ℚ) ^ m := Iff.rfl

omit [Fact p.Prime] in
/-- `pPrimaryPosDetInt n p` is contained in `posDetInt n`. -/
theorem pPrimaryPosDetInt_le_posDetInt : pPrimaryPosDetInt n p ≤ posDetInt n :=
  fun _ hg ↦ hg.1

omit [Fact p.Prime] in
/-- `SL_n(ℤ)` is contained in `pPrimaryPosDetInt n p` (`m = 0`). -/
theorem SLnZ_le_pPrimaryPosDetInt : (SLnZ n).toSubmonoid ≤ pPrimaryPosDetInt n p :=
  fun _ hg ↦ ⟨SLnZ_le_posDetInt n hg, 0, by rw [det_eq_one_of_mem_SLnZ n hg, pow_zero]⟩

omit [Fact p.Prime] in
/-- Every `p`-power diagonal matrix `natDiagGL n (primePowDiag n p e)` lies in
`pPrimaryPosDetInt n p`. -/
theorem natDiagGL_primePowDiag_mem_pPrimaryPosDetInt (e : Fin n → ℕ) :
    natDiagGL n (primePowDiag n p e) ∈ pPrimaryPosDetInt n p := by
  refine ⟨natDiagGL_mem_posDetInt n _, ?_⟩
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · by_cases he : ∀ i, 0 < primePowDiag n 0 e i
    · refine ⟨0, ?_⟩
      rw [natDiagGL_det n _ he, pow_zero]
      refine Finset.prod_eq_one fun i _ ↦ ?_
      have hi := he i
      rw [primePowDiag_apply] at hi ⊢
      rcases Nat.eq_zero_or_pos (e i) with h0 | hpos
      · simp [h0]
      · simp [Nat.zero_pow hpos] at hi
    · exact ⟨0, by rw [natDiagGL_of_not_pos n he]; simp⟩
  · refine ⟨∑ i, e i, ?_⟩
    rw [natDiagGL_det n _ (primePowDiag_pos n p hp e)]
    simpa [primePowDiag_apply] using Finset.prod_pow_eq_pow_sum Finset.univ e (p : ℚ)

/-- Every `g ∈ pPrimaryPosDetInt n p` lies in the `SL_n(ℤ)` double coset of
`natDiagGL n (primePowDiag n p e)` for a monotone tuple `e : Fin n → ℕ`. -/
theorem exists_primePowDiag_mem_doubleCoset {g : GL (Fin n) ℚ} (hg : g ∈ pPrimaryPosDetInt n p) :
    ∃ e : Fin n → ℕ, Monotone e ∧
      g ∈ doubleCoset (natDiagGL n (primePowDiag n p e)) (SLnZ n) (SLnZ n) := by
  obtain ⟨hg_pos, m, hm⟩ := hg
  let D : HeckeCoset (posDetInt n) (SLnZ n) (SLnZ n) := HeckeCoset.mk _ _ ⟨g, hg_pos⟩
  obtain ⟨a, ha_pos, ha_dvd, hD⟩ := exists_diagonal_representative D
  have hmem : g ∈ doubleCoset (natDiagGL n a) (SLnZ n) (SLnZ n) := by
    have := congrArg HeckeCoset.toSet hD
    rw [HeckeCoset.toSet_mk, diagCoset_toSet] at this
    exact this ▸ DoubleCoset.mem_doubleCoset_self _ _ _
  have hprod : ∏ i, a i = p ^ m := by
    have hdet := (det_eq_of_mem_doubleCoset_SLnZ n hmem).symm.trans hm
    rw [natDiagGL_det n a ha_pos] at hdet
    exact_mod_cast hdet
  have ha_pow : ∀ i, ∃ k ≤ m, a i = p ^ k := fun i ↦
    (Nat.dvd_prime_pow (Fact.out : p.Prime)).mp
      (hprod ▸ Finset.dvd_prod_of_mem a (Finset.mem_univ i))
  choose e _ he using ha_pow
  have ha_eq : a = primePowDiag n p e :=
    funext fun i ↦ (he i).trans (primePowDiag_apply n p e i).symm
  have he_mono : Monotone e := fun i j hij ↦ by
    have hd : p ^ e i ∣ p ^ e j := he i ▸ he j ▸ isDvdChain_iff.mp ha_dvd hij
    exact (Nat.pow_dvd_pow_iff_le_right (Fact.out : p.Prime).one_lt).mp hd
  exact ⟨e, he_mono, ha_eq ▸ hmem⟩

private theorem exists_int_matrix_natDiagGL_mul_inv {g : GL (Fin n) ℚ} {k m : ℕ}
    {A : Matrix (Fin n) (Fin n) ℤ}
    (hA : (↑(natDiagGL n (fun _ ↦ p ^ k) * g) : Matrix (Fin n) (Fin n) ℚ) =
      A.map (Int.cast : ℤ → ℚ))
    (hm : (↑(natDiagGL n (fun _ ↦ p ^ k) * g) : Matrix (Fin n) (Fin n) ℚ).det = (p : ℚ) ^ m) :
    ∃ B : Matrix (Fin n) (Fin n) ℤ,
      B * A = (p : ℤ) ^ (m + k) • 1 ∧
        (↑(natDiagGL n (fun _ ↦ p ^ m) * g⁻¹) : Matrix (Fin n) (Fin n) ℚ) =
          B.map (Int.cast : ℤ → ℚ) := by
  have hp_pos : 0 < p := (Fact.out : p.Prime).pos
  let B : Matrix (Fin n) (Fin n) ℤ := (p : ℤ) ^ k • A.adjugate
  have hAm : A.det = (p : ℤ) ^ m := by
    exact_mod_cast (show (A.det : ℚ) = (p : ℚ) ^ m by rw [Int.cast_det, ← hA, hm])
  have hBA : B * A = (p : ℤ) ^ (m + k) • 1 := by
    rw [Matrix.smul_mul, Matrix.adjugate_mul, hAm, smul_smul, ← pow_add, add_comm]
  refine ⟨B, hBA, ?_⟩
  have hpk_ne : (p : ℚ) ^ k ≠ 0 := pow_ne_zero k (Nat.cast_ne_zero.mpr hp_pos.ne')
  have hmulQ : B.map (Int.cast : ℤ → ℚ) * ((p : ℚ) ^ k • (↑g : Matrix (Fin n) (Fin n) ℚ)) =
      (p : ℚ) ^ k • (↑(natDiagGL n (fun _ ↦ p ^ m)) : Matrix (Fin n) (Fin n) ℚ) := by
    have hdiag_smul : (↑(natDiagGL n (fun _ ↦ p ^ k) * g) : Matrix (Fin n) (Fin n) ℚ) =
        (p : ℚ) ^ k • (↑g : Matrix (Fin n) (Fin n) ℚ) := by
      rw [Units.val_mul, natDiagGL_coe n _ fun _ ↦ pow_pos hp_pos k]
      ext i j; simp [Matrix.diagonal_mul]
    rw [← hdiag_smul, hA]
    have hmap := congrArg (Matrix.map · (Int.castRingHom ℚ)) hBA
    rw [Matrix.map_mul] at hmap; simp only [Int.coe_castRingHom] at hmap
    rw [hmap, natDiagGL_coe n _ fun _ ↦ pow_pos hp_pos m]
    ext i j
    simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.diagonal_apply,
      smul_eq_mul]
    by_cases hij : i = j <;> simp [hij, pow_add, mul_comm]
  rw [Matrix.mul_smul] at hmulQ
  have hBg : B.map (Int.cast : ℤ → ℚ) * (↑g : Matrix (Fin n) (Fin n) ℚ) =
      (↑(natDiagGL n (fun _ ↦ p ^ m)) : Matrix (Fin n) (Fin n) ℚ) := by
    ext i j; exact mul_left_cancel₀ hpk_ne (congr_fun (congr_fun hmulQ i) j)
  have hg_inv : (↑g : Matrix (Fin n) (Fin n) ℚ) * (↑(g⁻¹) : Matrix (Fin n) (Fin n) ℚ) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  rw [Units.val_mul, ← hBg, Matrix.mul_assoc, hg_inv, Matrix.mul_one]

private theorem inv_mem_pLocalPosGL_aux {g : GL (Fin n) ℚ} (hg : g ∈ Matrix.GLPos (Fin n) ℚ)
    {k : ℕ} (hkg : natDiagGL n (fun _ ↦ p ^ k) * g ∈ pPrimaryPosDetInt n p) :
    ∃ k' : ℕ, natDiagGL n (fun _ ↦ p ^ k') * g⁻¹ ∈ pPrimaryPosDetInt n p := by
  obtain ⟨hg_pos, m, hm⟩ := hkg
  obtain ⟨A, hA⟩ := (hasIntEntries_iff n).mp ((mem_posDetInt_iff n).mp hg_pos).1
  obtain ⟨B, hBA, hBmat⟩ := exists_int_matrix_natDiagGL_mul_inv n p hA hm
  have hdet_pos : 0 < (↑(natDiagGL n (fun _ ↦ p ^ m) * g⁻¹) : Matrix (Fin n) (Fin n) ℚ).det := by
    have hmem := (Matrix.GLPos (Fin n) ℚ).mul_mem
      (posDetInt_le_glpos n (natDiagGL_mem_posDetInt n (fun _ ↦ p ^ m)))
      ((Matrix.GLPos (Fin n) ℚ).inv_mem hg)
    rwa [Matrix.mem_glpos, Matrix.GeneralLinearGroup.val_det_apply] at hmem
  have hBdet_Q :
      (B.det : ℚ) = (↑(natDiagGL n (fun _ ↦ p ^ m) * g⁻¹) : Matrix (Fin n) (Fin n) ℚ).det := by
    rw [hBmat, Int.cast_det]
  have hBdet_pos : 0 < B.det := by exact_mod_cast hBdet_Q ▸ hdet_pos
  have hdvd : B.det.natAbs ∣ p ^ ((m + k) * n) := by
    have hdvdZ : B.det ∣ (p : ℤ) ^ ((m + k) * n) := by
      simpa [Fintype.card_fin, pow_mul] using Matrix.det_dvd_pow_card_of_mul_eq_smul_one hBA
    simpa [Int.natAbs_pow, Int.natAbs_natCast] using Int.natAbs_dvd_natAbs.mpr hdvdZ
  obtain ⟨r, -, hr⟩ := (Nat.dvd_prime_pow (Fact.out : p.Prime)).mp hdvd
  refine ⟨m, ⟨(mem_posDetInt_iff n).mpr ⟨(hasIntEntries_iff n).mpr ⟨B, hBmat⟩, hdet_pos⟩, r, ?_⟩⟩
  rw [← hBdet_Q, show B.det = (p : ℤ) ^ r from by
    rw [← Int.natAbs_of_nonneg hBdet_pos.le, hr, Nat.cast_pow]]
  simp

/-- The `p`-local positive-determinant subgroup of `GL_n(ℚ)`: elements of `GL_n^+(ℚ)` whose
entries clear to `pPrimaryPosDetInt n p` under a scalar power of `p`. -/
noncomputable def pLocalPosGL : Subgroup (GL (Fin n) ℚ) where
  carrier := {g | g ∈ Matrix.GLPos (Fin n) ℚ ∧
    ∃ k : ℕ, natDiagGL n (fun _ ↦ p ^ k) * g ∈ pPrimaryPosDetInt n p}
  one_mem' := ⟨(Matrix.GLPos (Fin n) ℚ).one_mem, 0, by simp [pow_zero, natDiagGL_one]⟩
  mul_mem' := by
    rintro g₁ g₂ ⟨hg₁, k₁, hk₁⟩ ⟨hg₂, k₂, hk₂⟩
    refine ⟨(Matrix.GLPos (Fin n) ℚ).mul_mem hg₁ hg₂, k₁ + k₂, ?_⟩
    have hp_pos : 0 < p := (Fact.out : p.Prime).pos
    have hpow : (fun _ : Fin n ↦ p ^ (k₁ + k₂)) =
        (fun _ : Fin n ↦ p ^ k₁) * (fun _ : Fin n ↦ p ^ k₂) :=
      funext fun _ ↦ pow_add p k₁ k₂
    have hmul : natDiagGL n (fun _ ↦ p ^ (k₁ + k₂)) * (g₁ * g₂) =
        (natDiagGL n (fun _ ↦ p ^ k₁) * g₁) * (natDiagGL n (fun _ ↦ p ^ k₂) * g₂) := by
      rw [hpow, ← natDiagGL_mul n _ _ (fun _ ↦ pow_pos hp_pos k₁) (fun _ ↦ pow_pos hp_pos k₂),
        mul_assoc, ← mul_assoc (natDiagGL n (fun _ ↦ p ^ k₂)),
        natDiagGL_const_comm n (p ^ k₂) g₁, mul_assoc, mul_assoc]
    rw [hmul]
    exact (pPrimaryPosDetInt n p).mul_mem hk₁ hk₂
  inv_mem' := fun ⟨hg, k, hk⟩ ↦
    ⟨(Matrix.GLPos (Fin n) ℚ).inv_mem hg, inv_mem_pLocalPosGL_aux n p hg hk⟩

/-- Membership characterization for `pLocalPosGL`. -/
@[simp]
theorem mem_pLocalPosGL_iff {g : GL (Fin n) ℚ} :
    g ∈ pLocalPosGL n p ↔ g ∈ Matrix.GLPos (Fin n) ℚ ∧
      ∃ k : ℕ, natDiagGL n (fun _ ↦ p ^ k) * g ∈ pPrimaryPosDetInt n p := Iff.rfl

/-- `pLocalPosGL n p` is contained in `GL_n^+(ℚ)`. -/
theorem pLocalPosGL_le_glpos : pLocalPosGL n p ≤ Matrix.GLPos (Fin n) ℚ :=
  fun _ hg ↦ hg.1

/-- `pPrimaryPosDetInt n p` is contained in `pLocalPosGL n p`. -/
theorem pPrimaryPosDetInt_le_pLocalPosGL :
    pPrimaryPosDetInt n p ≤ (pLocalPosGL n p).toSubmonoid :=
  fun g hg ↦ ⟨posDetInt_le_glpos n hg.1, 0, by rw [pow_zero, natDiagGL_one, one_mul]; exact hg⟩

/-- `SL_n(ℤ)` is contained in `pLocalPosGL n p`. -/
theorem SLnZ_le_pLocalPosGL : SLnZ n ≤ pLocalPosGL n p :=
  fun _ hg ↦ pPrimaryPosDetInt_le_pLocalPosGL n p (SLnZ_le_pPrimaryPosDetInt n p hg)

/-- Every `intPowDiagGL n p e` belongs to `pLocalPosGL n p`. -/
theorem intPowDiagGL_mem_pLocalPosGL (e : Fin n → ℤ) :
    intPowDiagGL n p e ∈ pLocalPosGL n p := by
  refine ⟨intPowDiagGL_mem_glpos n p e, ?_⟩
  obtain ⟨k, f, hf⟩ := TauCeti.exists_natCast_eq_add_natCast e
  have hf_fun : (fun i ↦ e i + (k : ℤ)) = fun i ↦ (f i : ℤ) := funext fun i ↦ (hf i).symm
  have hpp : (fun i ↦ p ^ f i) = primePowDiag n p f :=
    funext fun i ↦ (primePowDiag_apply n p f i).symm
  refine ⟨k, ?_⟩
  rw [natDiagGL_const_comm n (p ^ k), intPowDiagGL_mul_natDiagGL_const, hf_fun,
    intPowDiagGL_natCast, hpp]
  exact natDiagGL_primePowDiag_mem_pPrimaryPosDetInt n p f

omit [Fact p.Prime] in
/-- The `p`-primary integral Hecke triple `(pPrimaryPosDetInt n p, SL_n(ℤ))`. -/
instance instIsHeckeTriplePPrimaryPosDetInt :
    IsHeckeTriple (pPrimaryPosDetInt n p) (SLnZ n) (SLnZ n) :=
  IsHeckeTriple.of_diagonal (SLnZ_le_pPrimaryPosDetInt n p)
    (by rw [commensurator_SLnZ_eq_top]; exact le_top)

/-- The `p`-local rational Hecke triple `(pLocalPosGL n p, SL_n(ℤ))`. -/
instance instIsHeckeTriplePLocalPosGL :
    IsHeckeTriple (pLocalPosGL n p).toSubmonoid (SLnZ n) (SLnZ n) :=
  IsHeckeTriple.of_diagonal (SLnZ_le_pLocalPosGL n p)
    (by rw [commensurator_SLnZ_eq_top]; exact le_top)

end PPrimaryAndPLocalGroups

section PPrimaryToPLocal

/-- The image of `𝕋 (pPrimaryPosDetInt n p) (SLnZ n) ℤ` inside `IntegralHeckeRing n` is precisely
Shimura's `p`-local subring `pLocalSubring n p`. -/
theorem range_mapSubmonoidRingHom_pPrimaryPosDetInt :
    (HeckeCosetModule.mapSubmonoidRingHom (H := SLnZ n) ℤ
        (pPrimaryPosDetInt_le_posDetInt n p)).range =
      pLocalSubring n p := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨f, rfl⟩
    induction f using HeckeCosetModule.induction_linear with
    | h0 => rw [map_zero]; exact (pLocalSubring n p).zero_mem
    | hadd x y ihx ihy => rw [map_add]; exact (pLocalSubring n p).add_mem ihx ihy
    | hsingle D c =>
      rw [HeckeCosetModule.mapSubmonoidRingHom_single, ← HeckeCosetModule.smul_single_one ℤ _ c]
      refine (pLocalSubring n p).zsmul_mem ?_ c
      obtain ⟨e, he, hmem⟩ := exists_primePowDiag_mem_doubleCoset n p D.rep.property
      have hmap : HeckeCosetModule.single ℤ
          (D.map (pPrimaryPosDetInt_le_posDetInt n p) le_rfl le_rfl) 1 =
          diagElem (primePowDiag n p e) := by
        rw [diagElem_def]
        refine congrArg (HeckeCosetModule.single ℤ · 1) ?_
        conv_lhs => rw [← HeckeCoset.mk_rep D, HeckeCoset.map_mk]
        rw [diagCoset_def]
        exact HeckeCoset.mk_eq_mk_of_mem hmem
      rw [hmap]
      exact diagElem_primePowDiag_mem_pLocalSubring n p e he
  · rw [pLocalSubring_le_iff]
    intro e _
    let D₀ : HeckeCoset (pPrimaryPosDetInt n p) (SLnZ n) (SLnZ n) :=
      HeckeCoset.mk _ _
        ⟨natDiagGL n (primePowDiag n p e), natDiagGL_primePowDiag_mem_pPrimaryPosDetInt n p e⟩
    refine ⟨HeckeCosetModule.single ℤ D₀ 1, ?_⟩
    rw [HeckeCosetModule.mapSubmonoidRingHom_single, diagElem_def, diagCoset_def]
    exact congrArg (HeckeCosetModule.single ℤ · 1) (HeckeCoset.map_mk _ _ _ _)

/-- Ring isomorphism between `𝕋 (pPrimaryPosDetInt n p) (SLnZ n) ℤ` and `pLocalSubring n p`. -/
noncomputable def pPrimaryToPLocalRingEquiv :
    𝕋 (pPrimaryPosDetInt n p) (SLnZ n) ℤ ≃+* pLocalSubring n p :=
  HeckeCosetModule.mapSubmonoidSubringEquiv (pPrimaryPosDetInt_le_posDetInt n p)
    (range_mapSubmonoidRingHom_pPrimaryPosDetInt n p)

/-- Coercion of `pPrimaryToPLocalRingEquiv` to `IntegralHeckeRing n`. -/
@[simp]
theorem pPrimaryToPLocalRingEquiv_coe (f : 𝕋 (pPrimaryPosDetInt n p) (SLnZ n) ℤ) :
    (pPrimaryToPLocalRingEquiv n p f : IntegralHeckeRing n) =
      HeckeCosetModule.mapSubmonoidRingHom (H := SLnZ n) ℤ
        (pPrimaryPosDetInt_le_posDetInt n p) f :=
  HeckeCosetModule.coe_mapSubmonoidSubringEquiv_apply _ _ f

/-- `pPrimaryToPLocalRingEquiv` sends the `p`-primary double coset of
`natDiagGL n (primePowDiag n p e)` to `diagElem (primePowDiag n p e)` in `pLocalSubring n p`. -/
@[simp]
theorem pPrimaryToPLocalRingEquiv_single_primePowDiag (e : Fin n → ℕ) (he : Monotone e) :
    pPrimaryToPLocalRingEquiv n p (HeckeCosetModule.single ℤ
        (HeckeCoset.mk (SLnZ n) (SLnZ n)
          ⟨natDiagGL n (primePowDiag n p e),
            natDiagGL_primePowDiag_mem_pPrimaryPosDetInt n p e⟩) 1) =
      ⟨diagElem (primePowDiag n p e), diagElem_primePowDiag_mem_pLocalSubring n p e he⟩ := by
  apply Subtype.ext
  rw [pPrimaryToPLocalRingEquiv_coe]
  dsimp only
  rw [HeckeCosetModule.mapSubmonoidRingHom_single, diagElem_def, diagCoset_def]
  exact congrArg (HeckeCosetModule.single ℤ · 1) (HeckeCoset.map_mk _ _ _ _)

end PPrimaryToPLocal

end HeckeRing.GLn
