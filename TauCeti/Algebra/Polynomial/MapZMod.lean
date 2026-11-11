/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Data.ZMod.Basic
public import Mathlib.RingTheory.Ideal.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.RingTheory.PrincipalIdealDomain

/-!
# Reduction of integer polynomials modulo `n`

An integer polynomial reduces to zero in `(ZMod n)[X]` exactly when `n` divides every one of its
coefficients, that is, when the constant `n` divides it in `ℤ[X]`. Consequently two integer
polynomials with the same reduction modulo `n` differ by `n` times an integer polynomial, and if
the reduction of `Φ` divides the reduction of `G` then `G = Φ Q + n D` for integer polynomials
`Q` and `D`. Conversely, for a prime `p`, if `Φ` reduces to an irreducible polynomial and `Φ(x)`
and `G(x)` lie in a proper ideal containing `p`, then the reduction of `Φ` divides the reduction
of `G`.

## Main results

* `Polynomial.map_intCastRingHom_zmod_eq_zero_iff`: `G.map (Int.castRingHom (ZMod n)) = 0`
  exactly when `(n : ℤ[X]) ∣ G`.
* `Polynomial.exists_C_mul_eq_sub_of_map_zmod_eq`: polynomials with the same reduction modulo
  `n` differ by `C n * D`.
* `Polynomial.exists_eq_mul_add_C_mul_of_map_zmod_dvd`: if `Φ mod n` divides `G mod n`, then
  `G = Φ * Q + C n * D`.
* `Polynomial.map_zmod_dvd_map_of_aeval_mem`: if `Φ mod p` is irreducible and `Φ(x)`, `G(x)` lie
  in a proper ideal containing the prime `p`, then `Φ mod p` divides `G mod p`.
-/

public section

namespace Polynomial

variable {n : ℕ}

/-- An integer polynomial reduces to zero modulo `n` exactly when `n` divides it, that is, when
`n` divides each of its coefficients. -/
@[simp]
theorem map_intCastRingHom_zmod_eq_zero_iff (G : ℤ[X]) :
    G.map (Int.castRingHom (ZMod n)) = 0 ↔ (n : ℤ[X]) ∣ G := by
  rw [← C_eq_natCast, C_dvd_iff_dvd_coeff, Polynomial.ext_iff]
  simp only [coeff_map, coeff_zero, eq_intCast, ZMod.intCast_zmod_eq_zero_iff_dvd]

/-- Two integer polynomials with the same reduction modulo `n` differ by `n` times an integer
polynomial. -/
theorem exists_C_mul_eq_sub_of_map_zmod_eq {G G' : ℤ[X]}
    (h : G.map (Int.castRingHom (ZMod n)) = G'.map (Int.castRingHom (ZMod n))) :
    ∃ D : ℤ[X], C (n : ℤ) * D = G - G' := by
  obtain ⟨D, hD⟩ := (map_intCastRingHom_zmod_eq_zero_iff (n := n) (G - G')).mp (by
    rw [Polynomial.map_sub, h, sub_self])
  exact ⟨D, by rw [C_eq_natCast, hD]⟩

/-- If the reduction of `Φ` modulo `n` divides the reduction of `G`, then `G = Φ Q + n D` for
integer polynomials `Q` and `D`. -/
theorem exists_eq_mul_add_C_mul_of_map_zmod_dvd {Φ G : ℤ[X]}
    (h : Φ.map (Int.castRingHom (ZMod n)) ∣ G.map (Int.castRingHom (ZMod n))) :
    ∃ Q D : ℤ[X], G = Φ * Q + C (n : ℤ) * D := by
  obtain ⟨q, hq⟩ := h
  obtain ⟨Q, rfl⟩ := Polynomial.map_surjective (Int.castRingHom (ZMod n)) ZMod.intCast_surjective q
  obtain ⟨D, hD⟩ := exists_C_mul_eq_sub_of_map_zmod_eq (n := n) (G := G) (G' := Φ * Q) (by
    rw [Polynomial.map_mul, hq])
  exact ⟨Q, D, eq_add_of_sub_eq' hD.symm⟩

/-- Let `p` be a prime, let `x` be an element of a ring `A`, and let `P` be a proper (left)
ideal of `A` containing `p`. If `Φ` reduces modulo `p` to an irreducible polynomial and both
`Φ(x)` and `G(x)` lie in `P`, then the reduction of `Φ` divides the reduction of `G`. -/
theorem map_zmod_dvd_map_of_aeval_mem {A : Type*} [Ring A] {p : ℕ} [Fact p.Prime] (x : A)
    {P : Ideal A} (hP : P ≠ ⊤) (hp : (p : A) ∈ P) {Φ G : ℤ[X]}
    (hirr : Irreducible (Φ.map (Int.castRingHom (ZMod p))))
    (hΦ : aeval x Φ ∈ P) (hG : aeval x G ∈ P) :
    Φ.map (Int.castRingHom (ZMod p)) ∣ G.map (Int.castRingHom (ZMod p)) := by
  by_contra hndvd
  obtain ⟨a, b, hab⟩ := hirr.coprime_iff_not_dvd.mpr hndvd
  obtain ⟨A₁, rfl⟩ := map_surjective (Int.castRingHom (ZMod p)) ZMod.intCast_surjective a
  obtain ⟨B, rfl⟩ := map_surjective (Int.castRingHom (ZMod p)) ZMod.intCast_surjective b
  obtain ⟨D, hD⟩ := exists_C_mul_eq_sub_of_map_zmod_eq (n := p) (G := A₁ * Φ + B * G) (G' := 1)
    (by simp [hab])
  refine hP (P.eq_top_iff_one.2 ?_)
  rw [← map_one (aeval (R := ℤ) x), ← sub_sub_cancel (A₁ * Φ + B * G) 1, ← hD]
  simp only [map_sub, map_add, map_mul, map_natCast]
  refine P.sub_mem (P.add_mem (P.mul_mem_left _ hΦ) (P.mul_mem_left _ hG)) ?_
  rw [Nat.cast_comm]
  exact P.mul_mem_left _ hp

end Polynomial
