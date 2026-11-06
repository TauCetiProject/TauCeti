/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
public import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import TauCeti.RingTheory.Polynomial.Cyclotomic.ComplexRoots

/-!
# Integer matrices whose characteristic polynomial is cyclotomic

A cyclotomic polynomial is irreducible over `ℚ`. So if `Φₐ` annihilates an integer matrix and has
degree the dimension, it is the characteristic polynomial. The same holds for a product `Φₐ Φ_b` of
two distinct cyclotomic polynomials, provided neither factor annihilates the matrix alone and the
degrees add up to the dimension. No determinant is computed. Once the characteristic polynomial is
known, the complex eigenvalues are the corresponding primitive roots of unity, written as
`exp (2πi e / h)` with `e` coprime to `h`.

## Main results

* `Matrix.charpoly_eq_cyclotomic`: an annihilating `Φₐ` of degree the dimension is the
  characteristic polynomial.
* `Matrix.charpoly_eq_cyclotomic_mul`: if `Φₐ Φ_b` (`a ≠ b`) annihilates `M`, neither factor does
  alone, and the degrees add up to the dimension, then `Φₐ Φ_b` is the characteristic polynomial.
* `Matrix.mem_roots_charpoly_of_charpoly_eq_cyclotomic` and
  `Matrix.nodup_roots_charpoly_of_charpoly_eq_cyclotomic`: the complex eigenvalues of a matrix with
  characteristic polynomial `Φ_h` are `exp (2πi e / h)` for `e < h` coprime to `h`, each once.
* `Matrix.mem_roots_charpoly_of_charpoly_eq_cyclotomic_mul` and
  `Matrix.nodup_roots_charpoly_of_charpoly_eq_cyclotomic_mul`: the same for `Φₐ Φ_b`.
-/

public section

open Polynomial

namespace Matrix

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- An integer polynomial annihilates an integer matrix exactly when its cast to `ℚ` annihilates the
cast of the matrix. -/
theorem aeval_map_rat_eq_zero_iff (M : Matrix κ κ ℤ) (p : ℤ[X]) :
    aeval (M.map (Int.castRingHom ℚ)) (p.map (Int.castRingHom ℚ)) = 0 ↔ aeval M p = 0 := by
  have h := map_aeval_eq_aeval_map (φ := Int.castRingHom ℚ) (ψ := (Int.castRingHom ℚ).mapMatrix)
    (RingHom.ext_int _ _) p M
  rw [RingHom.mapMatrix_apply, RingHom.mapMatrix_apply] at h
  rw [← h, ← Matrix.map_zero (Int.castRingHom ℚ) (map_zero _)]
  exact (Matrix.map_injective (Int.castRingHom ℚ).injective_int).eq_iff

/-- A cyclotomic polynomial annihilates an integer matrix exactly when it annihilates its cast to
`ℚ`. -/
theorem aeval_map_rat_cyclotomic_eq_zero_iff (M : Matrix κ κ ℤ) (a : ℕ) :
    aeval (M.map (Int.castRingHom ℚ)) (cyclotomic a ℚ) = 0 ↔ aeval M (cyclotomic a ℤ) = 0 := by
  rw [← map_cyclotomic a (Int.castRingHom ℚ), aeval_map_rat_eq_zero_iff]

/-- A characteristic polynomial identity over `ℤ` can be checked after casting to `ℚ`. -/
theorem charpoly_eq_of_map_rat {M : Matrix κ κ ℤ} {p : ℤ[X]}
    (h : (M.map (Int.castRingHom ℚ)).charpoly = p.map (Int.castRingHom ℚ)) : M.charpoly = p := by
  apply Polynomial.map_injective (Int.castRingHom ℚ) (Int.castRingHom ℚ).injective_int
  rw [← charpoly_map, h]

/-- If `Φₐ` annihilates `M` and has degree the dimension, it is the characteristic polynomial. -/
theorem charpoly_eq_cyclotomic {M : Matrix κ κ ℤ} {a : ℕ} (ha : 0 < a)
    (hdeg : a.totient = Fintype.card κ) (hann : aeval M (cyclotomic a ℤ) = 0) :
    M.charpoly = cyclotomic a ℤ := by
  apply charpoly_eq_of_map_rat
  rw [map_cyclotomic]
  set Mq := M.map (Int.castRingHom ℚ)
  have : Nonempty κ := Fintype.card_pos_iff.1 (hdeg ▸ Nat.totient_pos.2 ha)
  have hq : minpoly ℚ Mq = cyclotomic a ℚ :=
    (minpoly.eq_of_irreducible_of_monic (cyclotomic.irreducible_rat ha)
      ((aeval_map_rat_cyclotomic_eq_zero_iff M a).2 hann) (cyclotomic.monic a ℚ)).symm
  refine eq_of_monic_of_dvd_of_natDegree_le (cyclotomic.monic a ℚ) (charpoly_monic _)
    (hq ▸ minpoly_dvd_charpoly _) ?_
  rw [charpoly_natDegree_eq_dim, natDegree_cyclotomic, hdeg]

/-- If the minimal polynomial of `M` divides `Φₐ q` and `q` does not annihilate `M`, then `Φₐ`
divides the minimal polynomial, since `Φₐ` is irreducible over `ℚ`. -/
private theorem cyclotomic_dvd_minpoly {M : Matrix κ κ ℚ} {a : ℕ} (ha : 0 < a) {q : ℚ[X]}
    (hq : minpoly ℚ M ∣ cyclotomic a ℚ * q) (hn : aeval M q ≠ 0) :
    cyclotomic a ℚ ∣ minpoly ℚ M := by
  by_contra h
  have hcop := ((cyclotomic.irreducible_rat ha).coprime_iff_not_dvd.2 h).symm
  exact hn (minpoly.dvd_iff.1 (hcop.dvd_of_dvd_mul_left hq))

/-- If `Φₐ Φ_b` (`a ≠ b`) annihilates `M`, neither factor annihilates it alone, and the degrees
add up to the dimension, then `Φₐ Φ_b` is the characteristic polynomial of `M`. -/
theorem charpoly_eq_cyclotomic_mul {M : Matrix κ κ ℤ} {a b : ℕ} (ha : 0 < a)
    (hb : 0 < b) (hab : a ≠ b) (hdeg : a.totient + b.totient = Fintype.card κ)
    (hann : aeval M (cyclotomic a ℤ * cyclotomic b ℤ) = 0)
    (hna : aeval M (cyclotomic a ℤ) ≠ 0) (hnb : aeval M (cyclotomic b ℤ) ≠ 0) :
    M.charpoly = cyclotomic a ℤ * cyclotomic b ℤ := by
  apply charpoly_eq_of_map_rat
  rw [Polynomial.map_mul, map_cyclotomic, map_cyclotomic]
  set Mq := M.map (Int.castRingHom ℚ)
  have hann' : aeval Mq (cyclotomic a ℚ * cyclotomic b ℚ) = 0 := by
    rw [← map_cyclotomic a (Int.castRingHom ℚ), ← map_cyclotomic b (Int.castRingHom ℚ),
      ← Polynomial.map_mul]
    exact (aeval_map_rat_eq_zero_iff M _).2 hann
  have hq : minpoly ℚ Mq ∣ cyclotomic a ℚ * cyclotomic b ℚ := minpoly.dvd_iff.2 hann'
  have hA : cyclotomic a ℚ ∣ minpoly ℚ Mq :=
    cyclotomic_dvd_minpoly ha hq (mt (aeval_map_rat_cyclotomic_eq_zero_iff M b).1 hnb)
  have hB : cyclotomic b ℚ ∣ minpoly ℚ Mq :=
    cyclotomic_dvd_minpoly hb (hq.trans (mul_comm _ _).dvd)
      (mt (aeval_map_rat_cyclotomic_eq_zero_iff M a).1 hna)
  have hmon := (cyclotomic.monic a ℚ).mul (cyclotomic.monic b ℚ)
  refine eq_of_monic_of_dvd_of_natDegree_le hmon (charpoly_monic _)
    (((cyclotomic.isCoprime_rat hab).mul_dvd hA hB).trans (minpoly_dvd_charpoly _)) ?_
  rw [charpoly_natDegree_eq_dim, natDegree_mul (cyclotomic_ne_zero a ℚ) (cyclotomic_ne_zero b ℚ),
    natDegree_cyclotomic, natDegree_cyclotomic, hdeg]

/-- The complex eigenvalues of an integer matrix with characteristic polynomial `Φ_h` are the
`exp (2πi e / h)` for `e < h` coprime to `h`. -/
theorem mem_roots_charpoly_of_charpoly_eq_cyclotomic {M : Matrix κ κ ℤ} {h : ℕ} (hh : h ≠ 0)
    (hM : M.charpoly = cyclotomic h ℤ) (ζ : ℂ) :
    ζ ∈ (M.map (Int.castRingHom ℂ)).charpoly.roots ↔
      ∃ e ∈ (List.range h).filter (Nat.Coprime · h),
        Complex.exp (2 * Real.pi * Complex.I * (e / h)) = ζ := by
  rw [charpoly_map, hM, map_cyclotomic, mem_roots_cyclotomic_complex_iff hh]

/-- The complex eigenvalues of an integer matrix with characteristic polynomial `Φ_h` are simple. -/
theorem nodup_roots_charpoly_of_charpoly_eq_cyclotomic {M : Matrix κ κ ℤ} {h : ℕ} (hh : h ≠ 0)
    (hM : M.charpoly = cyclotomic h ℤ) :
    (M.map (Int.castRingHom ℂ)).charpoly.roots.Nodup := by
  have : NeZero (h : ℂ) := ⟨Nat.cast_ne_zero.2 hh⟩
  rw [charpoly_map, hM, map_cyclotomic]
  exact roots_cyclotomic_nodup

/-- The complex eigenvalues of an integer matrix with characteristic polynomial `Φₐ Φ_b` are the
`exp (2πi e / a)` for `e < a` coprime to `a`, and the `exp (2πi e / b)` for `e < b` coprime
to `b`. -/
theorem mem_roots_charpoly_of_charpoly_eq_cyclotomic_mul {M : Matrix κ κ ℤ} {a b : ℕ} (ha : a ≠ 0)
    (hb : b ≠ 0) (hM : M.charpoly = cyclotomic a ℤ * cyclotomic b ℤ) (ζ : ℂ) :
    ζ ∈ (M.map (Int.castRingHom ℂ)).charpoly.roots ↔
      (∃ e ∈ (List.range a).filter (Nat.Coprime · a),
        Complex.exp (2 * Real.pi * Complex.I * (e / a)) = ζ) ∨
      ∃ e ∈ (List.range b).filter (Nat.Coprime · b),
        Complex.exp (2 * Real.pi * Complex.I * (e / b)) = ζ := by
  have hMa : (M.map (Int.castRingHom ℂ)).charpoly = cyclotomic a ℂ * cyclotomic b ℂ := by
    rw [charpoly_map, hM, Polynomial.map_mul, map_cyclotomic, map_cyclotomic]
  rw [hMa, roots_mul (mul_ne_zero (cyclotomic_ne_zero a ℂ) (cyclotomic_ne_zero b ℂ)),
    Multiset.mem_add, mem_roots_cyclotomic_complex_iff ha, mem_roots_cyclotomic_complex_iff hb]

/-- The complex eigenvalues of an integer matrix with characteristic polynomial `Φₐ Φ_b`, `a ≠ b`,
are simple: two distinct cyclotomic factors have disjoint roots. -/
theorem nodup_roots_charpoly_of_charpoly_eq_cyclotomic_mul {M : Matrix κ κ ℤ} {a b : ℕ} (ha : a ≠ 0)
    (hb : b ≠ 0) (hab : a ≠ b) (hM : M.charpoly = cyclotomic a ℤ * cyclotomic b ℤ) :
    (M.map (Int.castRingHom ℂ)).charpoly.roots.Nodup := by
  have : NeZero (a : ℂ) := ⟨Nat.cast_ne_zero.2 ha⟩
  have : NeZero (b : ℂ) := ⟨Nat.cast_ne_zero.2 hb⟩
  rw [charpoly_map, hM, Polynomial.map_mul, map_cyclotomic, map_cyclotomic,
    roots_mul (mul_ne_zero (cyclotomic_ne_zero a ℂ) (cyclotomic_ne_zero b ℂ)),
    Multiset.nodup_add]
  refine ⟨roots_cyclotomic_nodup, roots_cyclotomic_nodup, Multiset.disjoint_left.2 ?_⟩
  intro ζ h1 h2
  rw [cyclotomic.roots_eq_primitiveRoots_val, Finset.mem_val,
    mem_primitiveRoots (Nat.pos_of_ne_zero ha)] at h1
  rw [cyclotomic.roots_eq_primitiveRoots_val, Finset.mem_val,
    mem_primitiveRoots (Nat.pos_of_ne_zero hb)] at h2
  exact hab (h1.unique h2)

end Matrix

end
