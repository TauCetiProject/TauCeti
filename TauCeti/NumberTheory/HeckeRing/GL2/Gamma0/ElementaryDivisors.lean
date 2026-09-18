/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.HeckeRing.GL2.Gamma0.BadPrimeCoset

import TauCeti.Data.ZMod.Units
import TauCeti.NumberTheory.HeckeRing.GL2.Gamma0.CoprimeRepresentative

/-!
# `Γ₀(N)` double cosets are determined by their elementary divisors

Two elements of `Δ₀(N)` whose integral matrices have the same determinant and the same common
divisors of entries lie in the same `Γ₀(N)`-double coset. No hypothesis relating the
determinant to the level is needed; this is the form of Shimura's Proposition 3.32 in which the
double coset is read off the matrix, and it extends the coprime-determinant case
`HeckeRing.GL2.doubleCoset_SLnZ_inter_Delta0_eq_doubleCoset_Gamma0_map`.

A **primitive** witness — one no prime divides entrywise — of determinant `m` lies in the double
coset of `diag(1, m)`. Split `m = b * c` with `b = gcd (m, N ^ m)` collecting the primes shared
with the level, so that `c` is coprime to `N`. The two-sided clearing
`exists_gamma0_mul_mul_coprime_upperLeft` moves the witness inside its double coset until its
upper-left entry is coprime to `c` as well as to `N`, hence to `m`, and then Shimura's 3.33
(`mem_doubleCoset_natDiagGL_of_intWitness`) applies. In general, dividing out the gcd `d` of the
entries leaves a primitive witness; `d` is coprime to the level and central, so it can be put
back on both sides.

## Main results

* `HeckeRing.GL2.mem_doubleCoset_natDiagGL_of_primitive`: a primitive witness of determinant `m`
  lies in `Γ₀(N) diag(1, m) Γ₀(N)`.
* `HeckeRing.GL2.mem_doubleCoset_of_det_eq_of_dvd_iff`: elements of `Δ₀(N)` with equal
  determinants and equal common divisors of entries share a `Γ₀(N)`-double coset.

## References

* [G. Shimura, *Introduction to the arithmetic theory of automorphic functions*][shimura1971],
  Propositions 3.32 and 3.33.
-/

public section

open Matrix Matrix.SpecialLinearGroup CongruenceSubgroup HeckeRing.GLn

open scoped MatrixGroups

namespace HeckeRing.GL2

variable (N : ℕ)

/-- **Dividing out the shared part leaves a cofactor coprime to the level.** For `m ≠ 0`, the
quotient of `m` by `gcd (m, N ^ m)` is coprime to `N`.

The exponent `m` is deliberately crude: it only has to dominate the exponent each prime carries
in `m`, and `Nat.factorization_lt` says `m` itself does. A caller splitting a determinant has
`m` to hand and nothing sharper, so a tighter exponent would only move the work. -/
private lemma coprime_div_gcd_pow {N m : ℕ} (hN : N ≠ 0) (hm : m ≠ 0) :
    Nat.Coprime (m / Nat.gcd m (N ^ m)) N := by
  have hbm : Nat.gcd m (N ^ m) ∣ m := Nat.gcd_dvd_left _ _
  have hb0 : Nat.gcd m (N ^ m) ≠ 0 := fun h ↦ hm (Nat.eq_zero_of_gcd_eq_zero_left h)
  have hc0 : m / Nat.gcd m (N ^ m) ≠ 0 :=
    Nat.div_ne_zero_iff.mpr ⟨hb0, Nat.le_of_dvd (Nat.pos_of_ne_zero hm) hbm⟩
  by_contra hnc
  obtain ⟨p, hp, hpc, hpN⟩ := Nat.Prime.not_coprime_iff_dvd.mp hnc
  -- `p` carries at most `m` in `m` and at least `m` in `N ^ m`, so the gcd absorbs all of it
  have hle : m.factorization p ≤ (N ^ m).factorization p := by
    rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
    exact le_trans (Nat.factorization_lt p hm).le
      (Nat.le_mul_of_pos_right _ (hp.factorization_pos_of_dvd hN hpN))
  have hzero : (m / Nat.gcd m (N ^ m)).factorization p = 0 := by
    rw [Nat.factorization_div hbm, Finsupp.tsub_apply,
      Nat.factorization_gcd hm (pow_ne_zero m hN), Finsupp.inf_apply, min_eq_left hle,
      Nat.sub_self]
  exact absurd (hp.factorization_pos_of_dvd hc0 hpc) (by omega)

/-- **Coprimality passes to a product along a split.** If `m = b * c` with `b` dividing a power
of `N`, then anything coprime to both `N` and `c` is coprime to `m`. This is how a determinant
is proved coprime to an upper-left entry after being split into its `N`-part and the rest. -/
private lemma gcd_eq_one_of_eq_mul_of_dvd_pow {x : ℤ} {N m b c : ℕ} (hbc : m = b * c)
    (hb : b ∣ N ^ m) (hxN : Int.gcd x N = 1) (hxc : Int.gcd x c = 1) : Int.gcd x m = 1 := by
  have hm : (m : ℤ) = (b : ℤ) * (c : ℤ) := by exact_mod_cast hbc
  rw [hm]
  exact Int.isCoprime_iff_gcd_eq_one.mp
    (((Int.isCoprime_iff_gcd_eq_one.mpr hxN).pow_right (n := m)).of_isCoprime_of_dvd_right
        (by exact_mod_cast hb) |>.mul_right (Int.isCoprime_iff_gcd_eq_one.mpr hxc))

/-- **A primitive witness lies in the double coset of `diag(1, m)`.** Let `x ∈ GL₂(ℚ)` have an
integral matrix `A` with `N ∣ A 1 0`, upper-left entry coprime to `N`, determinant `m`, and no
prime dividing all four entries. Then `x ∈ Γ₀(N) diag(1, m) Γ₀(N)`. -/
-- Splitting `m = b * c` with `b = gcd (m, N ^ m)` isolates the primes `m` shares with the level
-- in `b` and leaves `c` coprime to `N`. The split is uniform in `m`: the degenerate values
-- `b = 1` and `b = m` are closed by the same appeal to `gcd_eq_one_of_eq_mul_of_dvd_pow`.
theorem mem_doubleCoset_natDiagGL_of_primitive [NeZero N] (m : ℕ) (x : GL (Fin 2) ℚ)
    (A : Matrix (Fin 2) (Fin 2) ℤ)
    (hA : (x : Matrix (Fin 2) (Fin 2) ℚ) = A.map (Int.cast : ℤ → ℚ))
    (hAN : (N : ℤ) ∣ A 1 0) (hAco : Int.gcd (A 0 0) N = 1)
    (hdet : (x : Matrix (Fin 2) (Fin 2) ℚ).det = (m : ℚ))
    (hprim : ∀ p : ℕ, p.Prime → ¬((p : ℤ) ∣ A 0 0 ∧ (p : ℤ) ∣ A 0 1 ∧ (p : ℤ) ∣ A 1 0 ∧
      (p : ℤ) ∣ A 1 1)) :
    x ∈ DoubleCoset.doubleCoset (natDiagGL 2 ![1, m])
      ((Gamma0 N).map (mapGL ℚ)) ((Gamma0 N).map (mapGL ℚ)) := by
  have hm_pos : 0 < m := by
    have hne := Matrix.GeneralLinearGroup.det_ne_zero x
    rw [hdet] at hne
    exact Nat.pos_of_ne_zero (by exact_mod_cast hne)
  have hbc : m = Nat.gcd m (N ^ m) * (m / Nat.gcd m (N ^ m)) :=
    (Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)).symm
  have hc_pos : 0 < m / Nat.gcd m (N ^ m) := by
    refine Nat.div_pos (Nat.le_of_dvd hm_pos (Nat.gcd_dvd_left _ _)) (Nat.pos_of_ne_zero ?_)
    exact fun h ↦ hm_pos.ne' (Nat.eq_zero_of_gcd_eq_zero_left h)
  obtain ⟨γL, γR, A', hA', hA'N, hA'Nco, hA'c⟩ :=
    exists_gamma0_mul_mul_coprime_upperLeft N x A hA hAN hAco _ hc_pos
      (coprime_div_gcd_pow (NeZero.ne N) hm_pos.ne') fun p hp _ ↦ hprim p hp
  have hdc : ((γL : GL (Fin 2) ℚ) * x * (γR : GL (Fin 2) ℚ)) ∈
      DoubleCoset.doubleCoset x ((Gamma0 N).map (mapGL ℚ)) ((Gamma0 N).map (mapGL ℚ)) :=
    DoubleCoset.mem_doubleCoset.mpr ⟨γL, γL.2, γR, γR.2, rfl⟩
  have hy := mem_doubleCoset_natDiagGL_of_intWitness N m _ A' hA' hA'N
    ((det_eq_of_mem_doubleCoset_of_le_SLnZ 2 (Gamma0_map_le_SLnZ N) (Gamma0_map_le_SLnZ N)
      hdc).trans hdet)
    (gcd_eq_one_of_eq_mul_of_dvd_pow hbc (Nat.gcd_dvd_right _ _) hA'Nco hA'c)
  rw [← DoubleCoset.doubleCoset_eq_of_mem hy, DoubleCoset.doubleCoset_eq_of_mem hdc]
  exact DoubleCoset.mem_doubleCoset_self _ _ _

/-- **Elements of `Δ₀(N)` with the same elementary divisors share a `Γ₀(N)`-double coset.** If
`α, β ∈ Δ₀(N)` have integral matrices `A, B` of equal determinant, and an integer divides all
entries of `A` exactly when it divides all entries of `B`, then `β ∈ Γ₀(N) α Γ₀(N)`. -/
theorem mem_doubleCoset_of_det_eq_of_dvd_iff [NeZero N] {α β : GL (Fin 2) ℚ}
    (hα : α ∈ Delta0 N) (hβ : β ∈ Delta0 N) {A B : Matrix (Fin 2) (Fin 2) ℤ}
    (hA : (α : Matrix (Fin 2) (Fin 2) ℚ) = A.map (Int.cast : ℤ → ℚ))
    (hB : (β : Matrix (Fin 2) (Fin 2) ℚ) = B.map (Int.cast : ℤ → ℚ)) (hdet : B.det = A.det)
    (hdvd : ∀ e : ℤ, (∀ i j, e ∣ A i j) ↔ ∀ i j, e ∣ B i j) :
    β ∈ DoubleCoset.doubleCoset α ((Gamma0 N).map (mapGL ℚ)) ((Gamma0 N).map (mapGL ℚ)) := by
  obtain ⟨A₁, hA₁, hαdet, hAN, hAunit⟩ := (mem_Delta0_iff N).mp hα
  obtain rfl : A = A₁ := Matrix.map_injective Int.cast_injective (hA.symm.trans hA₁)
  obtain ⟨B₁, hB₁, -, hBN, hBunit⟩ := (mem_Delta0_iff N).mp hβ
  obtain rfl : B = B₁ := Matrix.map_injective Int.cast_injective (hB.symm.trans hB₁)
  have hAco : Int.gcd (A 0 0) N = 1 := Int.isUnit_intCast_iff_gcd_eq_one.mp hAunit
  have hA_det_pos : 0 < A.det := by
    rw [← Int.cast_pos (R := ℚ), Int.cast_det, ← hA]
    exact hαdet
  -- divide both witnesses by the gcd `d` of the entries of `A`, which divides those of `B` too
  set d : ℕ := Nat.gcd (Nat.gcd (A 0 0).natAbs (A 0 1).natAbs)
    (Nat.gcd (A 1 0).natAbs (A 1 1).natAbs) with hd_def
  obtain ⟨A₀, hA₀_eq, hA₀_det_pos, hA₀N, hA₀co, hA₀_prim⟩ :=
    exists_primitive_content_quotient N A hA_det_pos hAN hAco d hd_def
  choose B₀ hB₀_eq using (hdvd d).mp fun i j ↦ ⟨A₀ i j, hA₀_eq i j⟩
  have hA_fac : A.det = (d : ℤ) ^ 2 * A₀.det := by
    simp only [Matrix.det_fin_two, hA₀_eq]
    ring
  have hB_fac : B.det = (d : ℤ) ^ 2 * Matrix.det (Matrix.of B₀) := by
    simp only [Matrix.det_fin_two, Matrix.of_apply, hB₀_eq]
    ring
  have hd_ne : (d : ℤ) ≠ 0 := by
    rintro hd
    rw [hA_fac, hd] at hA_det_pos
    simp at hA_det_pos
  have hdet₀ : Matrix.det (Matrix.of B₀) = A₀.det :=
    mul_left_cancel₀ (pow_ne_zero 2 hd_ne) (hB_fac.symm.trans (hdet.trans hA_fac))
  -- `d` divides the upper-left entry of `A`, so it is coprime to the level
  have hdN : IsCoprime (d : ℤ) N := by
    have h := Int.isCoprime_iff_gcd_eq_one.mpr hAco
    rw [hA₀_eq] at h
    exact h.of_mul_left_left
  have hB₀N : (N : ℤ) ∣ Matrix.of B₀ 1 0 :=
    hdN.symm.dvd_of_dvd_mul_left (hB₀_eq 1 0 ▸ hBN)
  have hB₀co : Int.gcd (Matrix.of B₀ 0 0) N = 1 := by
    have h := Int.isCoprime_iff_gcd_eq_one.mpr (Int.isUnit_intCast_iff_gcd_eq_one.mp hBunit)
    rw [hB₀_eq] at h
    exact Int.isCoprime_iff_gcd_eq_one.mp h.of_mul_left_right
  -- a prime dividing `B₀` entrywise would give a common divisor of `B`, hence of `A`, beyond `d`
  have hB₀_prim : ∀ p : ℕ, p.Prime → ¬((p : ℤ) ∣ Matrix.of B₀ 0 0 ∧
      (p : ℤ) ∣ Matrix.of B₀ 0 1 ∧ (p : ℤ) ∣ Matrix.of B₀ 1 0 ∧ (p : ℤ) ∣ Matrix.of B₀ 1 1) := by
    rintro p hp ⟨h00, h01, h10, h11⟩
    have hpB : ∀ i j, (d : ℤ) * p ∣ B i j := fun i j ↦ by
      rw [hB₀_eq]
      refine mul_dvd_mul_left _ ?_
      fin_cases i <;> fin_cases j
      exacts [h00, h01, h10, h11]
    have hpA : ∀ i j, (p : ℤ) ∣ A₀ i j := fun i j ↦
      (mul_dvd_mul_iff_left hd_ne).mp (hA₀_eq i j ▸ (hdvd _).mpr hpB i j)
    exact hA₀_prim p hp ⟨hpA 0 0, hpA 0 1, hpA 1 0, hpA 1 1⟩
  -- both primitive quotients lie in the double coset of `diag(1, m₀)`
  obtain ⟨m₀, hm₀⟩ : ∃ m₀ : ℕ, A₀.det = (m₀ : ℤ) :=
    ⟨A₀.det.natAbs, (Int.natAbs_of_nonneg hA₀_det_pos.le).symm⟩
  have hA₀_ne : (A₀.map (Int.cast : ℤ → ℚ)).det ≠ 0 := by
    rw [← Int.cast_det]
    exact_mod_cast hA₀_det_pos.ne'
  have hB₀_ne : ((Matrix.of B₀).map (Int.cast : ℤ → ℚ)).det ≠ 0 := by
    rw [← Int.cast_det, hdet₀]
    exact_mod_cast hA₀_det_pos.ne'
  set x₀ : GL (Fin 2) ℚ := Matrix.GeneralLinearGroup.mkOfDetNeZero _ hA₀_ne
  set y₀ : GL (Fin 2) ℚ := Matrix.GeneralLinearGroup.mkOfDetNeZero _ hB₀_ne
  have hx₀ := mem_doubleCoset_natDiagGL_of_primitive N m₀ x₀ A₀
    (Matrix.GeneralLinearGroup.val_mkOfDetNeZero _ _) hA₀N hA₀co
    (by rw [Matrix.GeneralLinearGroup.val_mkOfDetNeZero, ← Int.cast_det, hm₀]; norm_cast)
    hA₀_prim
  have hy₀ := mem_doubleCoset_natDiagGL_of_primitive N m₀ y₀ (Matrix.of B₀)
    (Matrix.GeneralLinearGroup.val_mkOfDetNeZero _ _) hB₀N hB₀co
    (by rw [Matrix.GeneralLinearGroup.val_mkOfDetNeZero, ← Int.cast_det, hdet₀, hm₀]; norm_cast)
    hB₀_prim
  rw [← DoubleCoset.doubleCoset_eq_of_mem hx₀] at hy₀
  obtain ⟨γ₁, hγ₁, γ₂, hγ₂, hy⟩ := DoubleCoset.mem_doubleCoset.mp hy₀
  -- put the central scalar `d` back on both sides
  have hαx : (α : Matrix (Fin 2) (Fin 2) ℚ) = (d : ℚ) • (x₀ : Matrix (Fin 2) (Fin 2) ℚ) := by
    rw [hA, Matrix.GeneralLinearGroup.val_mkOfDetNeZero]
    ext i j
    simp [hA₀_eq]
  have hβy : (β : Matrix (Fin 2) (Fin 2) ℚ) = (d : ℚ) • (y₀ : Matrix (Fin 2) (Fin 2) ℚ) := by
    rw [hB, Matrix.GeneralLinearGroup.val_mkOfDetNeZero]
    ext i j
    simp [hB₀_eq]
  refine DoubleCoset.mem_doubleCoset.mpr ⟨γ₁, hγ₁, γ₂, hγ₂, Units.ext ?_⟩
  rw [Units.val_mul, Units.val_mul, hαx, hβy, hy, Units.val_mul, Units.val_mul,
    Matrix.mul_smul, Matrix.smul_mul]

end HeckeRing.GL2
