/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Polynomial.UniversalFactorizationRing
public import TauCeti.RingTheory.MvPolynomial.Symmetric.Alternant
public import TauCeti.RingTheory.Polynomial.Vieta

import Mathlib.Algebra.Prime.Lemmas
import TauCeti.RingTheory.MvPolynomial.IrreducibleQuadratic
import TauCeti.RingTheory.MvPolynomial.Symmetric.Alternant.Divisibility
import TauCeti.RingTheory.Polynomial.Resultant.Discriminant

/-!
# Primality of the generic monic discriminant

Let `R` be a commutative ring. A monic polynomial of degree `m` over `R` has `m` free lower
coefficients, represented universally by `Polynomial.freeMonic R m` over `MvPolynomial (Fin m) R`.
Via Vieta's formulas and the fundamental theorem of symmetric polynomials, `MvPolynomial (Fin m) R`
embeds `R`-algebraically onto the symmetric polynomials in `m` root variables, sending
`(Polynomial.freeMonic R m).discr` to the square `δ ^ 2` of the Vandermonde product
`δ = ∏_{i < j} (X i - X j)`.

Over any integral domain `R` with `2 ≤ m`, each root difference `X i - X j` (`i ≠ j`) generates a
prime ideal in `MvPolynomial (Fin m) R`, and any symmetric polynomial divisible by one root
difference is divisible by `δ`. Contracting the prime ideal `(X 1 - X 0)` along
`MvPolynomial.vietaAlgHom` shows that `(Polynomial.freeMonic R m).discr` is prime if and only if
`(2 : R) ≠ 0` (`Polynomial.prime_discr_freeMonic_iff`), and is a square when `(2 : R) = 0`
(`Polynomial.isSquare_discr_freeMonic_of_two_eq_zero`), without any unique factorization assumption
on `R`.

## Main results

* `MvPolynomial.vietaAlgHom_discr_freeMonic`: `MvPolynomial.vietaAlgHom` sends
  `(Polynomial.freeMonic R m).discr` to the square of the Vandermonde alternant.
* `Polynomial.isSquare_discr_freeMonic_of_two_eq_zero`,
  `Polynomial.prime_discr_freeMonic`, `Polynomial.prime_discr_freeMonic_iff`: squareness when
  `2 = 0` and integral-domain primality of `(Polynomial.freeMonic R m).discr` when `2 ≤ m`.

## References

* S. Lang, *Algebra*, Revised Third Edition, GTM 211, Springer (2002), Chapter IV, §8.
* I. M. Gelfand, M. M. Kapranov, A. V. Zelevinsky, *Discriminants, Resultants, and
  Multidimensional Determinants*, Birkhäuser (1994), Chapter 12, §1.B.
-/

public section

open Finset MvPolynomial Polynomial

namespace Polynomial

section FreeMonicPrime

/-- Applying `MvPolynomial.vietaAlgHom` to `(Polynomial.freeMonic R m).discr` yields the square of
the Vandermonde alternant `TauCeti.alternant (Fin m) R (fun j ↦ (j : ℕ))`. -/
theorem _root_.MvPolynomial.vietaAlgHom_discr_freeMonic (R : Type*) [CommRing R] (m : ℕ) :
    vietaAlgHom R m (freeMonic R m).discr =
      TauCeti.alternant (Fin m) R (fun j ↦ (j : ℕ)) ^ 2 := by
  have h := congrArg Polynomial.discr (map_vietaAlgHom_freeMonic R m)
  rw [(monic_freeMonic R m).discr_map, discr_prod_X_sub_C_eq_sq] at h
  have h' : vietaAlgHom R m (freeMonic R m).discr =
      (∏ i : Fin m, ∏ j ∈ Ioi i, (MvPolynomial.X i - MvPolynomial.X j :
        MvPolynomial (Fin m) R)) ^ 2 := by
    simpa only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] using h
  exact h'.trans (TauCeti.alternant_fin_val_sq m).symm

/-- When `(2 : R) = 0`, the discriminant of `Polynomial.freeMonic R m` is a square in
`MvPolynomial (Fin m) R`. -/
theorem isSquare_discr_freeMonic_of_two_eq_zero {R : Type*} [CommRing R] (h2 : (2 : R) = 0)
    (m : ℕ) : IsSquare (freeMonic R m).discr := by
  -- When `2 = 0`, `-1 = 1`, so the Vandermonde alternant is invariant under every permutation of
  -- the roots and descends along `vietaAlgHom` to a square root of the discriminant.
  obtain ⟨s, hs⟩ := mem_range_vietaAlgHom_iff.mpr
    (TauCeti.isSymmetric_alternant_of_two_eq_zero h2 (fun j : Fin m ↦ (j : ℕ)))
  refine ⟨s, vietaAlgHom_injective R m ?_⟩
  rw [vietaAlgHom_discr_freeMonic, map_mul, ← sq, hs]

private theorem X_sub_X_dvd_sub_rename_swap {R : Type*} [CommRing R] {m : ℕ}
    (i₀ i₁ : Fin m) (p : MvPolynomial (Fin m) R) :
    MvPolynomial.X i₁ - MvPolynomial.X i₀ ∣ p - rename (Equiv.swap i₀ i₁) p := by
  induction p using MvPolynomial.induction_on with
  | C r =>
    simp
  | add p q hp hq =>
    have hadd : (p + q) - rename (Equiv.swap i₀ i₁) (p + q) =
        (p - rename (Equiv.swap i₀ i₁) p) + (q - rename (Equiv.swap i₀ i₁) q) := by
      rw [map_add]; ring
    rw [hadd]
    exact dvd_add hp hq
  | mul_X p k hp =>
    have hmul : (p * MvPolynomial.X k) - rename (Equiv.swap i₀ i₁) (p * MvPolynomial.X k) =
        (p - rename (Equiv.swap i₀ i₁) p) * MvPolynomial.X k +
          rename (Equiv.swap i₀ i₁) p *
            (MvPolynomial.X k - MvPolynomial.X (Equiv.swap i₀ i₁ k)) := by
      rw [map_mul, rename_X]; ring
    rw [hmul]
    refine dvd_add (dvd_mul_of_dvd_left hp _) (dvd_mul_of_dvd_right ?_ _)
    by_cases hk0 : k = i₀
    · subst hk0; rw [Equiv.swap_apply_left]; exact ⟨-1, by ring⟩
    · by_cases hk1 : k = i₁
      · subst hk1; rw [Equiv.swap_apply_right]
      · rw [Equiv.swap_apply_of_ne_of_ne hk0 hk1, sub_self]; exact dvd_zero _

private theorem discr_freeMonic_dvd_of_X_sub_X_dvd {R : Type*} [CommRing R] [IsDomain R]
    (h2 : (2 : R) ≠ 0) {m : ℕ} {i₀ i₁ : Fin m} (h01 : i₀ ≠ i₁)
    {f : MvPolynomial (Fin m) R}
    (hdvd : MvPolynomial.X i₁ - MvPolynomial.X i₀ ∣ vietaAlgHom R m f) :
    (freeMonic R m).discr ∣ f := by
  -- Step 1: Factor out the antisymmetric quotient `h` with `vietaAlgHom R m f = δ * h`.
  let δ : MvPolynomial (Fin m) R := TauCeti.alternant (Fin m) R (fun j ↦ (j : ℕ))
  have hδ0 : δ ≠ 0 := TauCeti.alternant_ne_zero_of_injective Fin.val_injective
  obtain ⟨h, hh⟩ := TauCeti.alternant_fin_val_dvd_of_isSymmetric
    (isSymmetric_vietaAlgHom f) h01.symm hdvd
  have hanti : ∀ e : Equiv.Perm (Fin m), rename (R := R) e h = e.sign • h := by
    intro e
    have hf := isSymmetric_vietaAlgHom f e
    rw [hh, map_mul, TauCeti.rename_alternant] at hf
    have hf' : δ * rename (R := R) e h = δ * (e.sign • h) := by
      calc δ * rename (R := R) e h
        _ = (e.sign ^ 2) • (δ * rename (R := R) e h) := by
            rw [Int.units_sq, one_smul]
        _ = e.sign • ((e.sign • δ) * rename (R := R) e h) := by
            rw [sq, mul_smul, smul_mul_assoc]
        _ = e.sign • (δ * h) := by rw [hf]
        _ = δ * (e.sign • h) := by rw [mul_smul_comm]
    exact mul_left_cancel₀ hδ0 hf'
  -- Step 2: Antisymmetry under `swap i₀ i₁` gives `X i₁ - X i₀ ∣ 2 * h`, hence `∣ h`.
  have hswap : rename (R := R) (Equiv.swap i₀ i₁) h = -h := by
    rw [hanti (Equiv.swap i₀ i₁), Equiv.Perm.sign_swap h01, Units.smul_def, Units.val_neg,
      Units.val_one, neg_one_smul]
  have hdvd2h : MvPolynomial.X i₁ - MvPolynomial.X i₀ ∣ (2 : MvPolynomial (Fin m) R) * h := by
    have heq : h - rename (R := R) (Equiv.swap i₀ i₁) h = 2 * h := by
      rw [hswap]; ring
    rw [← heq]
    exact X_sub_X_dvd_sub_rename_swap i₀ i₁ h
  have hnot2 : ¬ (MvPolynomial.X i₁ - MvPolynomial.X i₀ ∣ (2 : MvPolynomial (Fin m) R)) := by
    intro hd
    have hev := _root_.map_dvd (MvPolynomial.eval (R := R) (fun _ ↦ 0)) hd
    simp only [map_sub, MvPolynomial.eval_X, sub_self, map_ofNat, zero_dvd_iff] at hev
    exact h2 hev
  have hdvdh : MvPolynomial.X i₁ - MvPolynomial.X i₀ ∣ h :=
    ((prime_X_sub_X h01.symm).dvd_or_dvd hdvd2h).resolve_left hnot2
  -- Step 3: Permutations leave `h` associated to itself, so `δ ∣ h` and `δ ^ 2` divides `f`.
  have hass_h : ∀ e : Equiv.Perm (Fin m), Associated (rename (R := R) e h) h := by
    intro e
    rcases Int.units_eq_one_or e.sign with hs | hs
    · simp [hanti e, hs]
    · simp [hanti e, hs, (Associated.refl h).neg_left]
  obtain ⟨k, hk⟩ := TauCeti.alternant_fin_val_dvd_of_associated_rename hass_h h01.symm hdvdh
  have hfk : vietaAlgHom R m f = δ ^ 2 * k := by
    rw [hh, hk, sq]; ring
  have hk_symm : k.IsSymmetric := by
    intro e
    have hf := isSymmetric_vietaAlgHom f e
    rw [hfk, map_mul, ← vietaAlgHom_discr_freeMonic,
      isSymmetric_vietaAlgHom (freeMonic R m).discr e, vietaAlgHom_discr_freeMonic] at hf
    exact mul_left_cancel₀ (pow_ne_zero 2 hδ0) hf
  obtain ⟨k', hk'⟩ := mem_range_vietaAlgHom_iff.mpr hk_symm
  refine ⟨k', vietaAlgHom_injective R m ?_⟩
  rw [map_mul, vietaAlgHom_discr_freeMonic, hk', hfk]

/-- **Primality of the generic monic discriminant.** Over any integral domain `R` in which
`2 ≠ 0`, the discriminant of `Polynomial.freeMonic R m` is prime in `MvPolynomial (Fin m) R` for
every `m ≥ 2`. -/
theorem prime_discr_freeMonic {R : Type*} [CommRing R] [IsDomain R]
    (h2 : (2 : R) ≠ 0) {m : ℕ} (hm : 2 ≤ m) :
    Prime (freeMonic R m).discr := by
  let i₀ : Fin m := ⟨0, by omega⟩
  let i₁ : Fin m := ⟨1, by omega⟩
  have h01 : i₀ < i₁ := Fin.mk_lt_mk.mpr (by omega)
  have hdvd_vand : MvPolynomial.X i₁ - MvPolynomial.X i₀ ∣
      TauCeti.alternant (Fin m) R (fun j ↦ (j : ℕ)) := by
    rw [TauCeti.alternant_fin_val_eq_vandermonde]
    exact dvd_trans
      (Finset.dvd_prod_of_mem (fun j ↦ MvPolynomial.X j - MvPolynomial.X i₀) (mem_Ioi.mpr h01))
      (Finset.dvd_prod_of_mem
        (fun i ↦ ∏ j ∈ Ioi i, (MvPolynomial.X j - MvPolynomial.X i)) (mem_univ i₀))
  refine ⟨?_, fun hu ↦ ?_, fun f g hfg ↦ ?_⟩
  · intro h0
    have hsq0 : TauCeti.alternant (Fin m) R (fun j ↦ (j : ℕ)) ^ 2 = 0 := by
      rw [← vietaAlgHom_discr_freeMonic, h0, map_zero]
    exact pow_ne_zero 2 (TauCeti.alternant_ne_zero_of_injective Fin.val_injective) hsq0
  · have hu' : IsUnit (TauCeti.alternant (Fin m) R (fun j ↦ (j : ℕ)) ^ 2) := by
      rw [← vietaAlgHom_discr_freeMonic]
      exact hu.map (vietaAlgHom R m)
    have hv_unit : IsUnit (TauCeti.alternant (Fin m) R (fun j ↦ (j : ℕ))) :=
      (isUnit_pow_iff (by decide : 2 ≠ 0)).mp hu'
    exact (prime_X_sub_X h01.ne').not_isUnit (isUnit_of_dvd_unit hdvd_vand hv_unit)
  · have hprod : MvPolynomial.X i₁ - MvPolynomial.X i₀ ∣
        vietaAlgHom R m f * vietaAlgHom R m g := by
      have hmap := _root_.map_dvd (vietaAlgHom R m) hfg
      rw [vietaAlgHom_discr_freeMonic, map_mul] at hmap
      exact dvd_trans (dvd_trans hdvd_vand (dvd_pow_self _ (by decide))) hmap
    rcases (prime_X_sub_X h01.ne').dvd_or_dvd hprod with hf | hg
    · exact Or.inl (discr_freeMonic_dvd_of_X_sub_X_dvd h2 h01.ne hf)
    · exact Or.inr (discr_freeMonic_dvd_of_X_sub_X_dvd h2 h01.ne hg)

/-- Over an integral domain `R` and for `m ≥ 2`, the discriminant of `Polynomial.freeMonic R m`
is prime if and only if `(2 : R) ≠ 0`. -/
theorem prime_discr_freeMonic_iff {R : Type*} [CommRing R] [IsDomain R] {m : ℕ} (hm : 2 ≤ m) :
    Prime (freeMonic R m).discr ↔ (2 : R) ≠ 0 :=
  ⟨fun hp h2 ↦ (isSquare_discr_freeMonic_of_two_eq_zero h2 m).not_prime hp,
    fun h2 ↦ prime_discr_freeMonic h2 hm⟩

end FreeMonicPrime

end Polynomial
