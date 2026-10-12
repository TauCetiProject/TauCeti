/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
public import TauCeti.RingTheory.Etale.AdjoinRoot

/-!
# Cyclotomic polynomials over a ring in which `n` is invertible

Over a field, Mathlib characterises the roots of the cyclotomic polynomial `Φ_n` as the primitive
`n`th roots of unity (`Polynomial.isRoot_cyclotomic_iff`). This file proves the analogue over an
arbitrary commutative ring `R` in which `n` is invertible, where "primitive" has to be read
pointwise on `Spec R`.

Write `X ^ n - 1 = Φ_n * Ψ_n` with `Ψ_n = ∏_{d ∣ n, d < n} Φ_d`
(Mathlib's `Polynomial.eq_cyclotomic_iff`). When `n` is a unit, `X ^ n - 1` is separable,
so `Φ_n` is separable and coprime to `Ψ_n`. Consequently, for `ζ ∈ R`, the following are
equivalent:

* `Φ_n(ζ) = 0`;
* `ζ ^ n = 1` and `ζ ^ d - 1` is a unit for every proper divisor `d` of `n`
  (`Polynomial.isRoot_cyclotomic_iff_isUnit_pow_sub_one`);
* `ζ ^ n = 1` and the image of `ζ` in `R ⧸ p` is a primitive `n`th root of unity for every prime
  ideal `p` (`Polynomial.isRoot_cyclotomic_iff_forall_isPrimitiveRoot`).

The condition `ζ ^ n = 1` cannot be dropped from the last item: over `ℚ[ε]/(ε²)` the element
`1 + ε` is a primitive first root of unity modulo the only prime ideal, but is not a root of
`Φ_1 = X - 1`.

Finally, `R[X]/(Φ_n)` is finite and free over `R`, of rank `φ(n)` when `R` is nontrivial
(`Polynomial.finrank_adjoinRoot_cyclotomic`), and it is étale over `R` when `n` is a unit
(`Polynomial.etale_adjoinRoot_cyclotomic`).
-/

public section

open Finset

namespace Polynomial

variable {R : Type*} [CommRing R] {n : ℕ}

/-- If `n` is invertible in `R`, then the cyclotomic polynomial `Φ_n` is separable over `R`. -/
theorem separable_cyclotomic_of_isUnit (hn : IsUnit (n : R)) : (cyclotomic n R).Separable := by
  have h := separable_X_pow_sub_C_unit (1 : Rˣ) hn
  rw [Units.val_one, C_1] at h
  exact h.of_dvd (cyclotomic.dvd_X_pow_sub_one n R)

/-- If `n` is invertible in `R`, then `Φ_n` is coprime to the product of the `Φ_d` over the
proper divisors `d` of `n`. -/
theorem isCoprime_cyclotomic_prod_properDivisors (hn : IsUnit (n : R)) :
    IsCoprime (cyclotomic n R) (∏ d ∈ n.properDivisors, cyclotomic d R) := by
  rcases eq_or_ne n 0 with rfl | hn₀
  · simpa using isCoprime_one_left
  have h := separable_X_pow_sub_C_unit (1 : Rˣ) hn
  rw [Units.val_one, C_1,
    ← (eq_cyclotomic_iff (Nat.pos_of_ne_zero hn₀) (cyclotomic n R)).mp rfl] at h
  exact h.isCoprime

/-- An `n`th root of unity `ζ` for which every `ζ ^ d - 1`, with `d` a proper divisor of `n`, is
a unit is a root of the cyclotomic polynomial `Φ_n`. -/
theorem isRoot_cyclotomic_of_isUnit_pow_sub_one (hn : n ≠ 0) {ζ : R} (h₁ : ζ ^ n = 1)
    (h : ∀ d ∈ n.properDivisors, IsUnit (ζ ^ d - 1)) : (cyclotomic n R).IsRoot ζ := by
  have hu : IsUnit ((∏ d ∈ n.properDivisors, cyclotomic d R).eval ζ) := by
    rw [eval_prod, IsUnit.prod_iff]
    intro d hd
    refine isUnit_of_dvd_unit ?_ (h d hd)
    simpa using eval_dvd (x := ζ) (cyclotomic.dvd_X_pow_sub_one d R)
  have h₀ := congr(eval ζ $((eq_cyclotomic_iff (Nat.pos_of_ne_zero hn) (cyclotomic n R)).mp rfl))
  exact hu.mul_left_eq_zero.mp (by simpa [h₁] using h₀)

/-- **Roots of `Φ_n` when `n` is invertible.** If `n` is a unit in `R`, then `ζ` is a root of
`Φ_n` if and only if `ζ ^ n = 1` and `ζ ^ d - 1` is a unit for every proper divisor `d` of
`n`. -/
theorem isRoot_cyclotomic_iff_isUnit_pow_sub_one (hn : IsUnit (n : R)) {ζ : R} :
    (cyclotomic n R).IsRoot ζ ↔ ζ ^ n = 1 ∧ ∀ d ∈ n.properDivisors, IsUnit (ζ ^ d - 1) := by
  nontriviality R
  have hn₀ : n ≠ 0 := by
    rintro rfl
    simp at hn
  refine ⟨fun hζ ↦ ⟨?_, fun d hd ↦ ?_⟩, fun h ↦ isRoot_cyclotomic_of_isUnit_pow_sub_one hn₀ h.1 h.2⟩
  · have h₀ :=
      congr(eval ζ $((eq_cyclotomic_iff (Nat.pos_of_ne_zero hn₀) (cyclotomic n R)).mp rfl))
    simpa [hζ.eq_zero, sub_eq_zero] using h₀.symm
  · -- `Ψ_n(ζ)` is a unit by coprimality, and `ζ ^ d - 1` divides it.
    obtain ⟨a, b, hab⟩ := isCoprime_cyclotomic_prod_properDivisors hn
    have hu : IsUnit ((∏ d ∈ n.properDivisors, cyclotomic d R).eval ζ) := by
      refine IsUnit.of_mul_eq_one_right (b.eval ζ) ?_
      simpa [hζ.eq_zero] using congr(eval ζ $hab)
    refine isUnit_of_dvd_unit ?_ hu
    have hd' := Nat.mem_properDivisors.mp hd
    simpa using eval_dvd (x := ζ)
      (X_pow_sub_one_dvd_prod_cyclotomic R (Nat.pos_of_ne_zero hn₀) hd'.1 hd'.2.ne)

/-- **Roots of `Φ_n` are the fibrewise primitive roots of unity.** If `n` is a unit in `R`, then
`ζ` is a root of `Φ_n` if and only if `ζ ^ n = 1` and the image of `ζ` in `R ⧸ p` is a primitive
`n`th root of unity for every prime ideal `p` of `R`. -/
theorem isRoot_cyclotomic_iff_forall_isPrimitiveRoot (hn : IsUnit (n : R)) {ζ : R} :
    (cyclotomic n R).IsRoot ζ ↔
      ζ ^ n = 1 ∧ ∀ p : Ideal R, p.IsPrime → IsPrimitiveRoot (Ideal.Quotient.mk p ζ) n := by
  rw [isRoot_cyclotomic_iff_isUnit_pow_sub_one hn]
  refine and_congr_right fun h₁ ↦ ⟨fun h p hp ↦ ?_, fun h d hd ↦ ?_⟩
  · have : NeZero (n : R ⧸ p) := ⟨by simpa using (hn.map (Ideal.Quotient.mk p)).ne_zero⟩
    refine isRoot_cyclotomic_iff.mp ?_
    rw [← map_cyclotomic n (Ideal.Quotient.mk p)]
    exact IsRoot.map ((isRoot_cyclotomic_iff_isUnit_pow_sub_one hn).mpr ⟨h₁, h⟩)
  · -- Otherwise `ζ ^ d = 1` modulo some maximal ideal, contradicting primitivity there.
    by_contra hu
    obtain ⟨m, hm, hmem⟩ := exists_max_ideal_of_mem_nonunits hu
    have hd' := Nat.mem_properDivisors.mp hd
    have hdvd := ((h m hm.isPrime).pow_eq_one_iff_dvd d).mp
      (by simpa [sub_eq_zero] using Ideal.Quotient.eq_zero_iff_mem.mpr hmem)
    exact absurd (Nat.le_of_dvd (Nat.pos_of_mem_properDivisors hd) hdvd) (not_le.mpr hd'.2)

instance : Module.Free R (AdjoinRoot (cyclotomic n R)) :=
  (cyclotomic.monic n R).free_adjoinRoot

instance : Module.Finite R (AdjoinRoot (cyclotomic n R)) :=
  (cyclotomic.monic n R).finite_adjoinRoot

/-- `R[X]/(Φ_n)` has rank `φ(n)` over a nontrivial ring `R`. -/
theorem finrank_adjoinRoot_cyclotomic [Nontrivial R] :
    Module.finrank R (AdjoinRoot (cyclotomic n R)) = n.totient := by
  rw [(AdjoinRoot.powerBasis' (cyclotomic.monic n R)).finrank, AdjoinRoot.powerBasis'_dim,
    natDegree_cyclotomic]

/-- If `n` is invertible in `R`, then `R[X]/(Φ_n)` is étale over `R`. -/
theorem etale_adjoinRoot_cyclotomic (hn : IsUnit (n : R)) :
    Algebra.Etale R (AdjoinRoot (cyclotomic n R)) :=
  have := (cyclotomic.monic n R).isStandardEtale_adjoinRoot (separable_cyclotomic_of_isUnit hn)
  inferInstance

end Polynomial
