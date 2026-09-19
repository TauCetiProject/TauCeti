/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.HeckeRing.GL2.Gamma0.DoubleCoset
public import TauCeti.NumberTheory.ModularForms.AtkinLehner.Matrix

import TauCeti.Data.ZMod.Units
import TauCeti.LinearAlgebra.Matrix.Divisibility
import TauCeti.NumberTheory.HeckeRing.GL2.Gamma0.ElementaryDivisors

/-!
# Atkin–Lehner matrices and the `Γ₀(N)` double cosets

An Atkin–Lehner matrix `W` for a divisor `Q` of `N`, read in `GL(2, ℚ)`, normalizes the image of
`Γ₀(N)`. This file shows that conjugation by `W` moreover fixes every double coset
`Γ₀(N) α Γ₀(N)` with `α ∈ Δ₀(N)` of determinant coprime to `Q`:

`W⁻¹ α W ∈ Γ₀(N) α Γ₀(N)`.

Writing `W = !![Q a, b; N c, Q d]` and `α = !![p, q; N r, s]`, the conjugate is the integral
matrix `B` with `W B = α W`. Its lower-left entry is divisible by `N`, and its upper-left entry
is congruent to `s` modulo `Q` and to `p` modulo `N / Q`, hence a unit modulo `N` (`s` is a unit
modulo `Q` because `det α ≡ p s` is); so `W⁻¹ α W ∈ Δ₀(N)`. It has the determinant of `α`, and
the same common divisors of entries (a common divisor of either matrix is coprime to `Q`, and
`Q • B = adj W · α · W`), so the two lie in the same `Γ₀(N)`-double coset
(`HeckeRing.GL2.mem_doubleCoset_of_det_eq_of_dvd_iff`). No coprimality with `N / Q` is needed, so
this covers the `U_p` double cosets at the primes `p ∣ N / Q`.

These are the two hypotheses under which the slash by `W` commutes with the Hecke operator of
`Γ₀(N) α Γ₀(N)` (`HeckeRing.GL2.heckeSlashSum_slash_of_mem_normalizer`).

## Main results

* `TauCeti.IsAtkinLehnerMatrix.mem_normalizer_map_mapGL`: `W` normalizes the image of `Γ₀(N)` in
  `GL(2, ℚ)`.
* `TauCeti.IsAtkinLehnerMatrix.inv_mul_mul_mem_doubleCoset`: for `α ∈ Δ₀(N)` of determinant
  coprime to `Q`, `W⁻¹ α W ∈ Γ₀(N) α Γ₀(N)`.

## References

* [G. Shimura, *Introduction to the arithmetic theory of automorphic functions*][shimura1971],
  Proposition 3.32.
* A. O. L. Atkin and J. Lehner, *Hecke operators on `Γ₀(m)`*, Math. Ann. 185 (1970), 134–160.
-/

public section

open Matrix Matrix.SpecialLinearGroup CongruenceSubgroup HeckeRing.GL2 HeckeRing.GLn

open scoped MatrixGroups

namespace TauCeti

variable {N Q : ℕ} {M : Matrix (Fin 2) (Fin 2) ℤ} {w : GL (Fin 2) ℚ}

/-- An integral identity `M X = Y M` between `2 × 2` matrices, read in `GL (Fin 2) ℚ`. -/
private lemma mul_eq_mul_of_intMatrix {X Y : GL (Fin 2) ℚ} {A B : Matrix (Fin 2) (Fin 2) ℤ}
    (hw : (w : Matrix (Fin 2) (Fin 2) ℚ) = M.map (Int.cast : ℤ → ℚ))
    (hX : (X : Matrix (Fin 2) (Fin 2) ℚ) = A.map (Int.cast : ℤ → ℚ))
    (hY : (Y : Matrix (Fin 2) (Fin 2) ℚ) = B.map (Int.cast : ℤ → ℚ)) (h : M * A = B * M) :
    w * X = Y * w := by
  ext1
  rw [Units.val_mul, Units.val_mul, hw, hX, hY, ← Matrix.map_mul_intCast,
    ← Matrix.map_mul_intCast, h]

/-- If `W B = A W` for integral matrices lifting `w` and `α`, then `w⁻¹ α w` lifts `B`. -/
private lemma val_inv_mul_mul_eq_of_mul_eq_mul {α : GL (Fin 2) ℚ} {A B : Matrix (Fin 2) (Fin 2) ℤ}
    (hw : (w : Matrix (Fin 2) (Fin 2) ℚ) = M.map (Int.cast : ℤ → ℚ))
    (hA : (α : Matrix (Fin 2) (Fin 2) ℚ) = A.map (Int.cast : ℤ → ℚ)) (h : M * B = A * M)
    (hB : (B.map (Int.cast : ℤ → ℚ)).det ≠ 0) :
    ((w⁻¹ * α * w : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) = B.map (Int.cast : ℤ → ℚ) := by
  have hB' := mul_eq_mul_of_intMatrix hw (Matrix.GeneralLinearGroup.val_mkOfDetNeZero _ hB) hA h
  rw [mul_assoc, ← hB', inv_mul_cancel_left, Matrix.GeneralLinearGroup.val_mkOfDetNeZero]

/-- **An Atkin–Lehner matrix normalizes `Γ₀(N)` in `GL(2, ℚ)`.** -/
theorem IsAtkinLehnerMatrix.mem_normalizer_map_mapGL (hQN : Q ∣ N)
    (h : IsAtkinLehnerMatrix N Q M)
    (hw : (w : Matrix (Fin 2) (Fin 2) ℚ) = M.map (Int.cast : ℤ → ℚ)) :
    w ∈ Subgroup.normalizer
      (((Gamma0 N).map (mapGL ℚ) : Subgroup (GL (Fin 2) ℚ)) : Set (GL (Fin 2) ℚ)) := by
  have hQ : Q ≠ 0 := by
    intro hQ
    apply Matrix.GeneralLinearGroup.det_ne_zero w
    rw [hw, ← Int.cast_det, h.det_eq, hQ]
    norm_num
  refine Subgroup.mem_normalizer_iff.mpr fun x ↦ ⟨?_, fun hx ↦ ?_⟩
  · rintro ⟨γ, hγ, rfl⟩
    obtain ⟨δ, hδ, hmul⟩ := h.exists_mem_Gamma0_mul_eq_mul_left hQ hQN hγ
    refine ⟨δ, hδ, ?_⟩
    rw [eq_mul_inv_iff_mul_eq]
    exact (mul_eq_mul_of_intMatrix hw (mapGL_coe_matrix γ) (mapGL_coe_matrix δ) hmul).symm
  · obtain ⟨δ, hδ, hδx⟩ := hx
    obtain ⟨γ, hγ, hmul⟩ := h.exists_mem_Gamma0_mul_eq_mul_right hQ hQN hδ
    refine ⟨γ, hγ, ?_⟩
    have hw' := mul_eq_mul_of_intMatrix hw (mapGL_coe_matrix γ) (mapGL_coe_matrix δ) hmul.symm
    rw [hδx, inv_mul_cancel_right] at hw'
    exact mul_left_cancel hw'

/-- The integral conjugate `W⁻¹ α W` of `α = !![p, q; Q m r, s]` by `W = !![Q a, b; Q m c, Q d]`,
for `N = Q m`. It satisfies `W B = α W` whenever `Q a d - m b c = 1`. -/
private def atkinLehnerConj (Q m a b c d p q r s : ℤ) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![Q * d * (p * a + q * m * c) - b * m * (Q * r * a + s * c),
    d * (p * b + Q * q * d) - b * (m * r * b + s * d);
    Q * m * (a * (Q * r * a + s * c) - c * (p * a + q * m * c)),
    Q * a * (m * r * b + s * d) - m * c * (p * b + Q * q * d)]

private lemma mul_atkinLehnerConj {Q m a b c d p q r s : ℤ}
    (hred : Q * (a * d) - m * (b * c) = 1) :
    !![Q * a, b; Q * m * c, Q * d] * atkinLehnerConj Q m a b c d p q r s =
      !![p, q; Q * m * r, s] * !![Q * a, b; Q * m * c, Q * d] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [atkinLehnerConj, Matrix.mul_apply, Fin.sum_univ_two]
  · linear_combination (Q * (a * p + c * m * q)) * hred
  · linear_combination (Q * d * q + b * p) * hred
  · linear_combination (Q * m * (Q * a * r + c * s)) * hred
  · linear_combination (Q * (b * m * r + d * s)) * hred

/-- The upper-left entry of the conjugate is a unit modulo `N = Q m` as soon as `p` is and `s`
is a unit modulo `Q`: it is `s` modulo `Q` and `p` modulo `m`. -/
private lemma isCoprime_atkinLehnerConj_zero_zero {Q m a b c d p q r s : ℤ}
    (hred : Q * (a * d) - m * (b * c) = 1) (hp : IsCoprime p (Q * m)) (hs : IsCoprime s Q) :
    IsCoprime (atkinLehnerConj Q m a b c d p q r s 0 0) (Q * m) := by
  have hQ : atkinLehnerConj Q m a b c d p q r s 0 0 =
      s + Q * (d * p * a + d * q * m * c - b * m * r * a - s * a * d) := by
    simp only [atkinLehnerConj, of_apply, cons_val', cons_val_zero, empty_val',
      cons_val_fin_one]
    linear_combination s * hred
  have hm : atkinLehnerConj Q m a b c d p q r s 0 0 =
      p + m * (p * b * c + Q * d * q * c - b * Q * r * a - b * s * c) := by
    simp only [atkinLehnerConj, of_apply, cons_val', cons_val_zero, empty_val',
      cons_val_fin_one]
    linear_combination p * hred
  refine IsCoprime.mul_right ?_ ?_
  · rw [hQ]
    exact hs.add_mul_left_left _
  · rw [hm]
    exact (hp.of_mul_right_right).add_mul_left_left _

/-- **Conjugation by an Atkin–Lehner matrix fixes a `Γ₀(N)` double coset of determinant coprime
to `Q`.** If `W` is an Atkin–Lehner matrix for `Q ∣ N` and `α ∈ Δ₀(N)` has an integral matrix `A`
with determinant coprime to `Q`, then `W⁻¹ α W` lies in the double coset `Γ₀(N) α Γ₀(N)`. -/
theorem IsAtkinLehnerMatrix.inv_mul_mul_mem_doubleCoset [NeZero N] (hQN : Q ∣ N)
    (h : IsAtkinLehnerMatrix N Q M)
    (hw : (w : Matrix (Fin 2) (Fin 2) ℚ) = M.map (Int.cast : ℤ → ℚ)) {α : GL (Fin 2) ℚ}
    (hα : α ∈ Delta0 N) {A : Matrix (Fin 2) (Fin 2) ℤ}
    (hA : (α : Matrix (Fin 2) (Fin 2) ℚ) = A.map (Int.cast : ℤ → ℚ)) (hAdet : Int.gcd A.det Q = 1) :
    w⁻¹ * α * w ∈ DoubleCoset.doubleCoset α ((Gamma0 N).map (mapGL ℚ))
      ((Gamma0 N).map (mapGL ℚ)) := by
  have hQ : Q ≠ 0 := by
    intro hQ
    obtain ⟨m, hm⟩ := hQN
    apply NeZero.ne N
    simpa [hQ] using hm
  obtain ⟨A₁, hA₁, hdet_pos, ⟨r, hr⟩, hAunit⟩ := (mem_Delta0_iff N).mp hα
  obtain rfl : A = A₁ := Matrix.map_injective Int.cast_injective (hA.symm.trans hA₁)
  have hsQ : IsCoprime (A 1 1) (Q : ℤ) := Int.isCoprime_iff_gcd_eq_one.mpr
    (gcd_apply_one_one_eq_one Q A (hr ▸ (Int.natCast_dvd_natCast.mpr hQN).mul_right r) hAdet)
  obtain ⟨m, hm⟩ := hQN
  obtain ⟨a, b, c, d, rfl, hred⟩ := h.exists_entries hQ hm
  have hN : (N : ℤ) = (Q : ℤ) * m := by exact_mod_cast congrArg (Nat.cast : ℕ → ℤ) hm
  have hQ' : (Q : ℤ) ≠ 0 := Nat.cast_ne_zero.mpr hQ
  set W : Matrix (Fin 2) (Fin 2) ℤ := !![(Q : ℤ) * a, b; (Q : ℤ) * m * c, (Q : ℤ) * d] with hW
  have hAeq : A = !![A 0 0, A 0 1; (Q : ℤ) * m * r, A 1 1] := by
    rw [← hN, ← hr]
    exact Matrix.eta_fin_two A
  set B := atkinLehnerConj Q m a b c d (A 0 0) (A 0 1) r (A 1 1) with hB
  have hWB : W * B = A * W := by
    rw [hW, hB, mul_atkinLehnerConj hred, ← hAeq]
  -- the conjugate `β = W⁻¹ α W` is the integral matrix `B`
  set β : GL (Fin 2) ℚ := w⁻¹ * α * w
  have hdetB : B.det = A.det := by
    have hdetB := congrArg Matrix.det hWB
    rw [Matrix.det_mul, Matrix.det_mul, h.det_eq, mul_comm] at hdetB
    exact mul_right_cancel₀ hQ' hdetB
  have hBunit : (B.map (Int.cast : ℤ → ℚ)).det ≠ 0 := by
    rw [← Int.cast_det, hdetB, Int.cast_det, ← hA]
    exact hdet_pos.ne'
  have hβB : (β : Matrix (Fin 2) (Fin 2) ℚ) = B.map (Int.cast : ℤ → ℚ) :=
    val_inv_mul_mul_eq_of_mul_eq_mul hw hA hWB hBunit
  -- coprimality of the diagonal entries of `A` with the level
  have hApos : 0 < A.det := by
    rw [← Int.cast_pos (R := ℚ), Int.cast_det, ← hA]
    exact hdet_pos
  have hpN : IsCoprime (A 0 0) ((Q : ℤ) * m) := by
    rw [← hN]
    exact Int.isCoprime_iff_gcd_eq_one.mpr (Int.isUnit_intCast_iff_gcd_eq_one.mp hAunit)
  have hB00 : IsCoprime (B 0 0) ((Q : ℤ) * m) :=
    isCoprime_atkinLehnerConj_zero_zero hred hpN hsQ
  -- `β ∈ Δ₀(N)`
  have hβΔ : β ∈ Delta0 N := by
    refine (mem_Delta0_iff N).mpr ⟨B, hβB, ?_, ?_, ?_⟩
    · rw [hβB, ← Int.cast_det, hdetB]
      exact_mod_cast hApos
    · rw [hN, hB]
      simp only [atkinLehnerConj, of_apply, cons_val', cons_val_zero, cons_val_one, empty_val',
        cons_val_fin_one]
      exact dvd_mul_right _ _
    · exact Int.isUnit_intCast_iff_gcd_eq_one.mpr (Int.isCoprime_iff_gcd_eq_one.mp (hN ▸ hB00))
  -- a common divisor of either matrix divides its upper-left entry, so is coprime to `det W = Q`
  have hcopQ : ∀ e x : ℤ, IsCoprime x ((Q : ℤ) * m) → e ∣ x → IsCoprime e W.det :=
    fun e x hx hex ↦ h.det_eq ▸ (hx.of_isCoprime_of_dvd_left hex).of_mul_right_left
  have hdvd : ∀ e : ℤ, (∀ i j, e ∣ A i j) ↔ ∀ i j, e ∣ B i j := fun e ↦
    ⟨fun he ↦ (forall_dvd_apply_iff_of_mul_eq_mul hWB (hcopQ e _ hpN (he 0 0))).mp he,
      fun he ↦ (forall_dvd_apply_iff_of_mul_eq_mul hWB (hcopQ e _ hB00 (he 0 0))).mpr he⟩
  exact mem_doubleCoset_of_det_eq_of_dvd_iff N hα hβΔ hA hβB hdetB hdvd

end TauCeti
