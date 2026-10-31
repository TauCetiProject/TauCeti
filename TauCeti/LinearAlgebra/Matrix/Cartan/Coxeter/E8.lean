/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.Cartan.Coxeter.Basic
public import Mathlib.RingTheory.RootsOfUnity.Complex

/-!
# The Coxeter element of type `E₈`: order 30 and characteristic polynomial `Φ₃₀`

For `A = CartanMatrix.E 8` (Bourbaki numbering). See
`TauCeti.LinearAlgebra.Matrix.Cartan.Coxeter.Basic` for the conventions.

## Main results

* `orderOf_coxE8`: the Coxeter element `c = s₁ ⋯ s₈` has order `30`, the Coxeter number of `E₈`.
* `charpoly_coxE8`: the characteristic polynomial of `c` is `cyclotomic 30 ℤ`.
* `mem_roots_charpoly_coxE8_iff`, `nodup_roots_charpoly_coxE8`: the eigenvalues of `c` over `ℂ` are
  `exp (2πi e / 30)` for the exponents `e ∈ {1, 7, 11, 13, 17, 19, 23, 29}`, each once.
-/

@[expose] public section

open Matrix Polynomial

namespace TauCeti.Coxeter

/-- The Coxeter element `s₁ s₂ ⋯ s₈` of type `E₈`, in the simple-root basis. -/
def coxE8 : Matrix (Fin 8) (Fin 8) ℤ := coxeterElement (CartanMatrix.E 8)

/-- The exponents of `E₈`. -/
def e8Exponents : List ℕ := [1, 7, 11, 13, 17, 19, 23, 29]

theorem reflMatrix_E8_mul_self (i : Fin 8) :
    reflMatrix (CartanMatrix.E 8) i * reflMatrix (CartanMatrix.E 8) i = 1 := by
  revert i; decide +kernel

/-- **The Coxeter number of `E₈` is 30**: the Coxeter element has order exactly `30`. -/
theorem orderOf_coxE8 : orderOf coxE8 = 30 :=
  (orderOf_eq_iff (by norm_num)).2 ⟨by decide +kernel, by decide +kernel⟩

theorem aeval_coxE8_cyclotomic : aeval coxE8 (cyclotomic 30 ℤ) = 0 := by
  rw [cyclotomic_thirty_int]
  simp only [map_add, map_sub, map_pow, aeval_X, map_one]
  decide +kernel

/-- **The characteristic polynomial of the `E₈` Coxeter element is `Φ₃₀`.** -/
theorem charpoly_coxE8 : coxE8.charpoly = cyclotomic 30 ℤ :=
  charpoly_eq_cyclotomic _ (by norm_num) (by decide) aeval_coxE8_cyclotomic

theorem charpoly_map_coxE8_complex :
    (coxE8.map (Int.castRingHom ℂ)).charpoly = cyclotomic 30 ℂ := by
  rw [charpoly_map, charpoly_coxE8, map_cyclotomic]

theorem e8Exponents_eq_filter : e8Exponents = (List.range 30).filter (Nat.Coprime · 30) := by
  decide

/-- **Eigenvalues of the `E₈` Coxeter element**: the complex eigenvalues are exactly
`exp (2πi e / 30)` for the exponents `e` of `E₈`. -/
theorem mem_roots_charpoly_coxE8_iff (ζ : ℂ) :
    ζ ∈ (coxE8.map (Int.castRingHom ℂ)).charpoly.roots ↔
      ∃ e ∈ e8Exponents, Complex.exp (2 * Real.pi * Complex.I * (e / 30)) = ζ := by
  rw [charpoly_map_coxE8_complex, cyclotomic.roots_eq_primitiveRoots_val, Finset.mem_val,
    mem_primitiveRoots (by norm_num), Complex.isPrimitiveRoot_iff ζ 30 (by norm_num),
    e8Exponents_eq_filter]
  simp only [List.mem_filter, List.mem_range, decide_eq_true_eq, Nat.cast_ofNat]
  constructor
  · rintro ⟨i, hi, hc, h⟩; exact ⟨i, ⟨hi, hc⟩, h⟩
  · rintro ⟨i, ⟨hi, hc⟩, h⟩; exact ⟨i, hi, hc, h⟩

/-- Each eigenvalue of the `E₈` Coxeter element occurs with multiplicity one. -/
theorem nodup_roots_charpoly_coxE8 :
    (coxE8.map (Int.castRingHom ℂ)).charpoly.roots.Nodup := by
  rw [charpoly_map_coxE8_complex]
  exact roots_cyclotomic_nodup

end TauCeti.Coxeter

end
