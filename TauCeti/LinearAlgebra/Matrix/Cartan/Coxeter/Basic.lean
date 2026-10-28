/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Cartan.Basic
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Expand
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots

/-!
# Coxeter elements of Cartan matrices: the matrix layer

In the basis of simple roots, the simple reflection `sᵢ` acts by `sᵢ αⱼ = αⱼ - A j i • αᵢ`, where
`A` is the Cartan matrix in Mathlib's convention `b.cartanMatrix i j = ⟨αᵢ, αⱼ^∨⟩`. The Coxeter
element is `c = s₁ s₂ ⋯ sᵣ`.

The characteristic polynomial of a Coxeter element of an exceptional type is a product of at most
two distinct cyclotomic polynomials, so it is identified without computing a determinant:

* `charpoly_eq_cyclotomic`: an annihilating `Φₐ` of degree equal to the dimension is the
  characteristic polynomial (`Φₐ` is irreducible over `ℚ`, so it is the minimal polynomial).
* `charpoly_eq_cyclotomic_mul`: if `Φₐ Φ_b` (`a ≠ b`) annihilates `M`, neither factor does alone,
  and the degrees add up to the dimension, then `Φₐ Φ_b` is the characteristic polynomial.

Both reduce to kernel checks on integer matrices. The explicit forms of `Φ₆`, `Φ₁₂`, `Φ₁₈`, `Φ₃₀`
are proved from `cyclotomic` itself.
-/

@[expose] public section

open Matrix Polynomial

namespace TauCeti.Coxeter

/-- The simple reflection `sᵢ` in the simple-root basis: `sᵢ αⱼ = αⱼ - A j i • αᵢ`. -/
def reflMatrix {κ : Type*} [DecidableEq κ] (A : Matrix κ κ ℤ) (i : κ) : Matrix κ κ ℤ :=
  Matrix.of fun k j => (if k = j then 1 else 0) - (if k = i then A j i else 0)

/-- The Coxeter element `s₁ s₂ ⋯ sₙ` of a Cartan matrix, in the simple-root basis. -/
def coxeterElement {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) : Matrix (Fin n) (Fin n) ℤ :=
  ((List.finRange n).map (reflMatrix A)).prod

/-! ### Explicit cyclotomic polynomials -/

theorem cyclotomic_six_int : cyclotomic 6 ℤ = X ^ 2 - X + 1 := by
  have h := cyclotomic_expand_eq_cyclotomic_mul (p := 3) (n := 2) Nat.prime_three (by decide) ℤ
  rw [cyclotomic_two] at h
  apply mul_right_cancel₀ (cyclotomic_ne_zero 2 ℤ)
  rw [show (6 : ℕ) = 2 * 3 from rfl, cyclotomic_two, ← h]
  simp only [map_add, expand_X, map_one]
  ring

theorem cyclotomic_twelve_int : cyclotomic 12 ℤ = X ^ 4 - X ^ 2 + 1 := by
  rw [show (12 : ℕ) = 6 * 2 from rfl,
    ← cyclotomic_expand_eq_cyclotomic Nat.prime_two (by decide), cyclotomic_six_int]
  simp only [map_add, map_sub, map_pow, expand_X, map_one]
  ring

theorem cyclotomic_eighteen_int : cyclotomic 18 ℤ = X ^ 6 - X ^ 3 + 1 := by
  rw [show (18 : ℕ) = 6 * 3 from rfl,
    ← cyclotomic_expand_eq_cyclotomic Nat.prime_three (by decide), cyclotomic_six_int]
  simp only [map_add, map_sub, map_pow, expand_X, map_one]
  ring

theorem cyclotomic_thirty_int :
    cyclotomic 30 ℤ = X ^ 8 + X ^ 7 - X ^ 5 - X ^ 4 - X ^ 3 + X + 1 := by
  have h := cyclotomic_expand_eq_cyclotomic_mul (p := 5) (n := 6) Nat.prime_five (by decide) ℤ
  apply mul_right_cancel₀ (cyclotomic_ne_zero 6 ℤ)
  rw [show (30 : ℕ) = 6 * 5 from rfl, ← h, cyclotomic_six_int]
  simp only [map_add, map_sub, map_pow, expand_X, map_one]
  ring

/-! ### Characteristic polynomials from annihilating cyclotomic polynomials -/

variable {n : ℕ}

/-- Evaluating an integer polynomial at an integer matrix commutes with casting to `ℚ`. -/
theorem aeval_map_rat (M : Matrix (Fin n) (Fin n) ℤ) (p : ℤ[X]) :
    aeval (M.map (Int.castRingHom ℚ)) (p.map (Int.castRingHom ℚ)) =
      (aeval M p).map (Int.castRingHom ℚ) := by
  rw [aeval_def, aeval_def, eval₂_map]
  change _ = (Int.castRingHom ℚ).mapMatrix (eval₂ _ M p)
  rw [hom_eval₂]
  congr 1
  exact RingHom.ext_int _ _

theorem aeval_map_rat_cyclotomic (M : Matrix (Fin n) (Fin n) ℤ) (a : ℕ) :
    aeval (M.map (Int.castRingHom ℚ)) (cyclotomic a ℚ) =
      (aeval M (cyclotomic a ℤ)).map (Int.castRingHom ℚ) := by
  rw [← aeval_map_rat, map_cyclotomic]

theorem aeval_map_rat_eq_zero_iff (M : Matrix (Fin n) (Fin n) ℤ) (a : ℕ) :
    aeval (M.map (Int.castRingHom ℚ)) (cyclotomic a ℚ) = 0 ↔ aeval M (cyclotomic a ℤ) = 0 := by
  rw [aeval_map_rat_cyclotomic, ← Matrix.map_zero (Int.castRingHom ℚ) (map_zero _)]
  exact (Matrix.map_injective (Int.castRingHom ℚ).injective_int).eq_iff

/-- Pull a characteristic polynomial identity back from `ℚ` to `ℤ`. -/
theorem charpoly_eq_of_map_rat {M : Matrix (Fin n) (Fin n) ℤ} {p : ℤ[X]}
    (h : (M.map (Int.castRingHom ℚ)).charpoly = p.map (Int.castRingHom ℚ)) : M.charpoly = p := by
  apply Polynomial.map_injective (Int.castRingHom ℚ) (Int.castRingHom ℚ).injective_int
  rw [← charpoly_map, h]

/-- If `Φₐ` annihilates `M` and has degree the dimension, it is the characteristic polynomial. -/
theorem charpoly_eq_cyclotomic (M : Matrix (Fin n) (Fin n) ℤ) {a : ℕ} (ha : 0 < a)
    (hdeg : a.totient = n) (hann : aeval M (cyclotomic a ℤ) = 0) :
    M.charpoly = cyclotomic a ℤ := by
  apply charpoly_eq_of_map_rat
  rw [map_cyclotomic]
  set Mq := M.map (Int.castRingHom ℚ)
  have : Nonempty (Fin n) := ⟨⟨0, hdeg ▸ Nat.totient_pos.2 ha⟩⟩
  have hq : minpoly ℚ Mq = cyclotomic a ℚ :=
    (minpoly.eq_of_irreducible_of_monic (cyclotomic.irreducible_rat ha)
      ((aeval_map_rat_eq_zero_iff M a).2 hann) (cyclotomic.monic a ℚ)).symm
  refine eq_of_monic_of_dvd_of_natDegree_le (cyclotomic.monic a ℚ) (charpoly_monic _)
    (hq ▸ minpoly_dvd_charpoly _) ?_
  rw [charpoly_natDegree_eq_dim, natDegree_cyclotomic, Fintype.card_fin, hdeg]

/-- If `Φₐ Φ_b` (`a ≠ b`) annihilates `M`, neither factor annihilates it alone, and the degrees
add up to the dimension, then `Φₐ Φ_b` is the characteristic polynomial of `M`. -/
theorem charpoly_eq_cyclotomic_mul (M : Matrix (Fin n) (Fin n) ℤ) {a b : ℕ} (ha : 0 < a)
    (hb : 0 < b) (hab : a ≠ b) (hdeg : a.totient + b.totient = n)
    (hann : aeval M (cyclotomic a ℤ * cyclotomic b ℤ) = 0)
    (hna : aeval M (cyclotomic a ℤ) ≠ 0) (hnb : aeval M (cyclotomic b ℤ) ≠ 0) :
    M.charpoly = cyclotomic a ℤ * cyclotomic b ℤ := by
  apply charpoly_eq_of_map_rat
  rw [Polynomial.map_mul, map_cyclotomic, map_cyclotomic]
  set Mq := M.map (Int.castRingHom ℚ)
  have hann' : aeval Mq (cyclotomic a ℚ * cyclotomic b ℚ) = 0 := by
    rw [← map_cyclotomic a (Int.castRingHom ℚ), ← map_cyclotomic b (Int.castRingHom ℚ),
      ← Polynomial.map_mul, aeval_map_rat, hann, Matrix.map_zero _ (map_zero _)]
  have hq : minpoly ℚ Mq ∣ cyclotomic a ℚ * cyclotomic b ℚ := minpoly.dvd_iff.2 hann'
  have hA : cyclotomic a ℚ ∣ minpoly ℚ Mq := by
    by_contra h
    have hcop := ((cyclotomic.irreducible_rat ha).coprime_iff_not_dvd.2 h).symm
    exact hnb ((aeval_map_rat_eq_zero_iff M b).1 (minpoly.dvd_iff.1 (hcop.dvd_of_dvd_mul_left hq)))
  have hB : cyclotomic b ℚ ∣ minpoly ℚ Mq := by
    by_contra h
    have hcop := ((cyclotomic.irreducible_rat hb).coprime_iff_not_dvd.2 h).symm
    rw [mul_comm] at hq
    exact hna ((aeval_map_rat_eq_zero_iff M a).1 (minpoly.dvd_iff.1 (hcop.dvd_of_dvd_mul_left hq)))
  have hmon := (cyclotomic.monic a ℚ).mul (cyclotomic.monic b ℚ)
  refine eq_of_monic_of_dvd_of_natDegree_le hmon (charpoly_monic _)
    (((cyclotomic.isCoprime_rat hab).mul_dvd hA hB).trans (minpoly_dvd_charpoly _)) ?_
  rw [charpoly_natDegree_eq_dim, natDegree_mul (cyclotomic_ne_zero a ℚ) (cyclotomic_ne_zero b ℚ),
    natDegree_cyclotomic, natDegree_cyclotomic, Fintype.card_fin, hdeg]

end TauCeti.Coxeter

end
