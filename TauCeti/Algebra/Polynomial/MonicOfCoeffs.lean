/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.OfFn
public import Mathlib.Algebra.Polynomial.Monic
public import Mathlib.Data.Fintype.Pi

/-!
# Monic polynomials with prescribed lower coefficients

A monic polynomial of degree `d` is `X ^ d + ∑_{i < d} c_i X ^ i` for a unique vector
`c : Fin d → R` of lower coefficients. This file names that polynomial
(`Polynomial.monicOfCoeffs c = X ^ d + Polynomial.ofFn d c`, with Mathlib's `Polynomial.ofFn`)
and, over a finite semiring, collects the monic polynomials of degree `d` into a finset with
`(card R) ^ d` elements. Sums over the monic polynomials of a given degree, such as the
coefficients of the `L`-series of a function on `𝔽_q[X]`, are sums over this finset.

## Main definitions

* `Polynomial.monicOfCoeffs c`: the monic polynomial `X ^ d + ∑_{i < d} c_i X ^ i`.
* `Polynomial.monicsOfDegree R d`: the finset of monic polynomials of degree `d` over a finite
  semiring `R`.

## Main results

* `Polynomial.monic_monicOfCoeffs`, `Polynomial.natDegree_monicOfCoeffs`,
  `Polynomial.coeff_monicOfCoeffs_of_lt`: `monicOfCoeffs c` is monic of degree `d` with lower
  coefficients `c`.
* `Polynomial.monicOfCoeffs_injective`, `Polynomial.exists_monicOfCoeffs_eq`: every monic
  polynomial of degree `d` is `monicOfCoeffs c` for exactly one `c`.
* `Polynomial.mem_monicsOfDegree`, `Polynomial.card_monicsOfDegree`: `monicsOfDegree R d` consists
  of the monic polynomials of degree `d`, and it has `(card R) ^ d` elements.
-/

public section

open Finset

namespace Polynomial

variable {R : Type*} [Semiring R] [DecidableEq R]

/-- The monic polynomial `X ^ d + ∑_{i < d} c_i X ^ i` with lower coefficients `c`. -/
noncomputable def monicOfCoeffs {d : ℕ} (c : Fin d → R) : R[X] :=
  X ^ d + ofFn d c

/-- The monic polynomial of degree `0` is `1`. -/
@[simp]
theorem monicOfCoeffs_of_isEmpty (c : Fin 0 → R) : monicOfCoeffs c = 1 := by
  simp [monicOfCoeffs]

theorem monic_monicOfCoeffs {d : ℕ} (c : Fin d → R) : (monicOfCoeffs c).Monic :=
  monic_X_pow_add (ofFn_degree_lt c)

@[simp]
theorem natDegree_monicOfCoeffs [Nontrivial R] {d : ℕ} (c : Fin d → R) :
    (monicOfCoeffs c).natDegree = d := by
  rw [monicOfCoeffs, natDegree_add_eq_left_of_degree_lt] <;>
    simp [ofFn_degree_lt c]

theorem coeff_monicOfCoeffs_of_lt {d i : ℕ} (c : Fin d → R) (hi : i < d) :
    (monicOfCoeffs c).coeff i = c ⟨i, hi⟩ := by
  simp [monicOfCoeffs, coeff_X_pow, hi.ne, ofFn_coeff_eq_val_of_lt c hi]

theorem monicOfCoeffs_injective (d : ℕ) : Function.Injective (monicOfCoeffs (R := R) (d := d)) :=
  fun c c' h ↦ funext fun i ↦ by
    rw [← coeff_monicOfCoeffs_of_lt c i.isLt, h, coeff_monicOfCoeffs_of_lt]

/-- Every monic polynomial `g` is `monicOfCoeffs` of its lower coefficients. -/
theorem exists_monicOfCoeffs_eq {g : R[X]} (hg : g.Monic) :
    ∃ c : Fin g.natDegree → R, monicOfCoeffs c = g := by
  refine ⟨fun i ↦ g.coeff i, ?_⟩
  ext i
  rw [monicOfCoeffs, coeff_add, coeff_X_pow]
  rcases lt_trichotomy i g.natDegree with hi | rfl | hi
  · simp [hi.ne, ofFn_coeff_eq_val_of_lt _ hi]
  · simp [ofFn_coeff_eq_zero_of_ge _ le_rfl, hg.coeff_natDegree]
  · simp [hi.ne', ofFn_coeff_eq_zero_of_ge _ hi.le, coeff_eq_zero_of_natDegree_lt hi]

variable (R) [Fintype R]

/-- The finset of monic polynomials of degree `d` over a finite semiring `R`, the image of
`monicOfCoeffs` on `Fin d → R`. -/
noncomputable def monicsOfDegree (d : ℕ) : Finset R[X] :=
  univ.image (monicOfCoeffs (R := R) (d := d))

variable {R}

theorem mem_monicsOfDegree [Nontrivial R] {d : ℕ} {g : R[X]} :
    g ∈ monicsOfDegree R d ↔ g.Monic ∧ g.natDegree = d := by
  constructor
  · rintro hg
    obtain ⟨c, -, rfl⟩ := mem_image.1 hg
    exact ⟨monic_monicOfCoeffs c, natDegree_monicOfCoeffs c⟩
  · rintro ⟨hg, rfl⟩
    obtain ⟨c, hc⟩ := exists_monicOfCoeffs_eq hg
    exact mem_image.2 ⟨c, mem_univ _, hc⟩

/-- There are `(card R) ^ d` monic polynomials of degree `d` over a finite semiring `R`. -/
theorem card_monicsOfDegree (d : ℕ) : #(monicsOfDegree R d) = Fintype.card R ^ d := by
  rw [monicsOfDegree, card_image_of_injective _ (monicOfCoeffs_injective d), card_univ,
    Fintype.card_fun, Fintype.card_fin]

/-- A sum over the monic polynomials of degree `d` is a sum over their lower coefficients. -/
theorem sum_monicsOfDegree {M : Type*} [AddCommMonoid M] (f : R[X] → M) (d : ℕ) :
    ∑ g ∈ monicsOfDegree R d, f g = ∑ c : Fin d → R, f (monicOfCoeffs c) :=
  sum_image fun _ _ _ _ h ↦ monicOfCoeffs_injective d h

end Polynomial
